import $file.lexer, lexer._
import $file.parser, parser._

var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}


implicit def string_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
}

// this allows us to write things like
// i"iadd" and l"Label"


// environments 
type Env = Map[String, Int]


def compile_op(op: String) = op match {
  case "+" => i"iadd"
  case "-" => i"isub"
  case "*" => i"imul"
  case "/" => i"idiv"
  case "%" => i"irem"
}

// arithmetic expression compilation
def compile_aexp(a: AExp, env : Env) : String = a match {
  case Num(i) => i"ldc $i"
  case Var(s) => i"iload ${env(s)} \t\t; $s"
  case Aop(op, a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ compile_op(op)
}

// boolean expression compilation
//  - the jump-label is for where to jump if the condition is not true
def compile_bexp(b: BExp, env : Env, jmp: String) : String = b match {
  case True => ""
  case False => i"goto $jmp"
  case Bop("==", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp"
  case Bop("!=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp"
  case Bop("<", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp"
  case Bop(">", a1, a2) => 
    compile_aexp(a2, env) ++ compile_aexp(a1, env) ++ i"if_icmpge $jmp"
  case Bop("<=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpgt $jmp"
  case Bop(">=", a1, a2) => 
    compile_aexp(a2, env) ++ compile_aexp(a1, env) ++ i"if_icmpgt $jmp"  
  case And(b1, b2) =>
    compile_bexp(b1, env, jmp) ++ compile_bexp(b2, env, jmp)
  case Or(b1, b2) =>{
        val or_else = Fresh("Or_else")
        val or_end = Fresh("Or_end")

        compile_bexp(b1, env, or_else) ++ i"goto $or_end" ++
        l"$or_else" ++ compile_bexp(b2, env, jmp) ++ l"$or_end"
  }
}


def stringfy(a: AExp) : String = a match {
    case Str(s) => s
    case Var(s) => s
  }

// statement compilation
def compile_stmt(s: Stmt, env: Env) : (String, Env) = s match {
  case Skip => ("", env)
  case Assign(x, a) => {
    val index = env.getOrElse(x, env.keys.size)
    (compile_aexp(a, env) ++ i"istore $index \t\t; $x", env + (x -> index))
  } 
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     i"goto $if_end" ++
     l"$if_else" ++
     instrs2 ++
     l"$if_end", env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (l"$loop_begin" ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }
  case WriteVar(x) => 
    (i"iload ${env(x)} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/write(I)V", env)
  case WriteStr(x) => 
    (i"""ldc "$x"""" ++ 
     i"invokestatic XXX/XXX/writes(Ljava/lang/String;)V", env)
  case Read(x) => {
   val index = env.getOrElse(x, env.keys.size) 
   (i"invokestatic XXX/XXX/read()I" ++ 
    i"istore $index \t\t; $x", env + (x -> index))
  }
  case ForLoop(x, y, u, bl) => {
      val adding = Assign(stringfy(x) , Aop("+", x , Num(1)))
      val (instrs1, env1) = compile_stmt(Assign(stringfy(x) ,y), env)
      val (instrs2, env2) = compile_stmt(While((Bop("<=", x, u)) , bl ++ List(adding)), env1)
      (instrs1 ++ instrs2 ,env2)
  }
}

// compilation of a block (i.e. list of instructions)
def compile_block(bl: Block, env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}


val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public static write(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/println(I)V 
    return 
.end method


.method public static writes(Ljava/lang/String;)V
    .limit stack 2
    .limit locals 1
    getstatic java/lang/System/out Ljava/io/PrintStream;
    aload 0
    invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
    return
.end method


.method public static read()I 
    .limit locals 10 
    .limit stack 10

    ldc 0 
    istore 1  ; this will hold our final integer 
Label1: 
    getstatic java/lang/System/in Ljava/io/InputStream;
    invokevirtual java/io/InputStream/read()I 
    istore 2 
    iload 2 
    ldc 13   ; the newline delimiter 
    isub 
    ifeq Label2 
    iload 2 
    ldc 32   ; the space delimiter 
    isub 
    ifeq Label2

    iload 2 
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48 
    isub 
    ldc 10 
    iload 1 
    imul 
    iadd 
    istore 1 
    goto Label1 
Label2: 
    ; when we come here we have our integer computed in local variable 1 
    iload 1 
    ireturn 
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS

"""

val ending = """
; COMPILED CODE ENDS
   return

.end method
"""


// main compilation function for blocks
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions ++ ending).replaceAllLiterally("XXX", class_name)
}




val fibonacci = 
  """
write "Fib: ";
read n;
minus1 := 1;
minus2 := 0;
while n > 0 do {
temp := minus2 ;
minus2 := minus1 + minus2 ;
minus1 := temp;
n := n - 1
};
write " Result : ";
write minus2 ;
write "\n"
"""


val factors = 
"""n := 20;
      f := 2;
      while (f < n / 2 + 1) do {
        if ((n / f) * f == n) then  { write(f) } else { skip };
        f := f + 1
      }"""


@main
def fib_test() = 
  println(compile(Stmts.parse_all(tokenise(fibonacci)).head, "fib"))


@main
def factor_test() = 
  println(compile(Stmts.parse_all(tokenise(factors)).head, "factor"))



def run(bl: Block, class_name: String) = {
    val code = compile(bl, class_name)
    os.write.over(os.pwd / s"$class_name.j", code)
    os.proc("java", "-jar", "jasmin.jar", s"$class_name.j").call()
    os.proc("java", s"$class_name/$class_name").call(stdout = os.Inherit, stdin = os.Inherit)
}

@main
def fib_test2() =
  run(Stmts.parse_all(tokenise(fibonacci)).head, "fib")

@main
def factor_test2() =
  run(Stmts.parse_all(tokenise(factors)).head, "factor")


val forloop = 
"""
      for i := 2 upto 4 do {
        write i
      }
"""



@main
def for_test() =
   println(compile(Stmts.parse_all(tokenise(forloop)).head, "for"))

  @main
def for_test2() =
  run(Stmts.parse_all(tokenise(forloop)).head, "for")



  val forloop2 =
  """
    for i := 1 upto 10 do {
      for i := 1 upto 10 do {
        write i
      }
    }
  """

  @main
  def for2_test() =
    println(compile(Stmts.parse_all(tokenise(forloop2)).head, "for2"))

  @main
  def for2_test2() =
  run(Stmts.parse_all(tokenise(forloop2)).head, "for2")


  val and = 
"""
      f := 2;
      i := 1;
      while (f < 4) && i < 2 do {
        write i;
        i := i + 1;
        f := f + 1;
      }
"""

  @main
  def and_test() =
    println(compile(Stmts.parse_all(tokenise(and)).head, "and"))

  @main
  def and_test2() =
  run(Stmts.parse_all(tokenise(and)).head, "and")

    val or = 
"""
    f := 2;
    i := 1;
    while f < 4 || f < 3 do {
        write i;
        i := i + 1;
        f := f + 1;
    }
"""

  @main
  def or_test() =
    println(compile(Stmts.parse_all(tokenise(or)).head, "or"))

  @main
  def or_test2() =
  run(Stmts.parse_all(tokenise(or)).head, "or")