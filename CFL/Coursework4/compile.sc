// A Small Compiler for the WHILE Language
// (it does not use a parser nor lexer)
//
// cal with 
//
//   amm compile.sc test
//   amm compile.sc test2


import scala.io.StdIn.readInt
import scala.language.implicitConversions
import scala.language.reflectiveCalls

abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CFUN(f: Char => Boolean) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class OPTIONAL(r : Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class PLUS(r1: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp  
                // records for extracting strings or tokens
  

abstract class Token 
case object T_SEMI extends Token
case object T_LPAREN extends Token
case object T_RPAREN extends Token
case class T_ID(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_KWD(s: String) extends Token
case class T_STR(s: String) extends Token
case class T_COM(s: String) extends Token
case class T_SYM(s: String) extends Token

// values  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
case class Ntmes(vs: List[Val]) extends Val
   
// some convenience for typing in regular expressions

def CHAR(c: Char) = CFUN(_ == c)
def RANGE(l: List[Char]) = CFUN(l.contains(_))

def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case OPTIONAL(_) => true
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case PLUS(r) => nullable(r)
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case STAR(_) => true
  case CFUN(f) => false
  case RECD(_, r1) => nullable(r1)
}

def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CFUN(f) => if (f(c)) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case PLUS(r1) => SEQ(der(c, r1), STAR(r1))
  case NTIMES(r, i) => if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i-1))
  case OPTIONAL(r) => der(c,r)
  case RECD(_, r1) => der(c, r1)
}


// extracts a string from a value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Ntmes(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}


// extracts an environment from a value;
// used for tokenising a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Ntmes(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}



// The injection and mkeps part of the lexer
//===========================================

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case OPTIONAL(r) => Empty
  case PLUS(r) => Stars(Nil)
  case NTIMES(r, n) => if (n == 0) Ntmes(Nil) else Ntmes(List.fill(n)(mkeps(r)))
  // case RANGE(cs) => Empty
  case RECD(x, r) => Rec(x, mkeps(r))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (CFUN(f), Empty) => Chr(c)  
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), v) => inj(r,c,v)
  case (NTIMES(r,n), Sequ(v1, Ntmes(vs))) => Ntmes(inj(r, c, v1)::vs)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))

def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = 
  env(lex_simp(r, s.toList))


// The Lexing Rules for the WHILE Language


def Range2(s : List[Char]) : Rexp = s match {
  case Nil => ZERO
  case c::Nil => CHAR(c)
  case c::s => ALT(CHAR(c), Range2(s))
}
def RANGE2(s: String) = Range2(s.toList)

def PLUS2(r: Rexp) = r ~ r.%

val LET = RANGE2("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
val SYM = LET | "_" | "." | ">" |  "<" | "=" | ":" | ";" | "," | "\\"
val DIGIT = RANGE2("0123456789")
val ID = LET ~  ("_" | LET | DIGIT).% 
val DIGIT2 = RANGE2("123456789")
val NUM = "0" | DIGIT2 ~ DIGIT.%
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "upto" | "for" | "true" | "false"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "=" | "-" | "+" | "*" | "!=" | "<" | ">" | "==" | "+=" | ":=" | "&&" | "||" | "/" | "%"
val WHITESPACE = PLUS2(" " | "\n" | "\t" | "\r")
val RPAREN: Rexp = "}" |  ")" 
val LPAREN: Rexp = "{" | "("
val STRING: Rexp = "\"" ~ (SYM | DIGIT | WHITESPACE).% ~ "\""
val COMMENT: Rexp = "//" ~ (SYM | " " | DIGIT).% ~ "\r\n"


val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("w" $ WHITESPACE) |
                  ("c" $ COMMENT)).%


val token : PartialFunction[(String, String), Token] = {
  case ("s", _) => T_SEMI
  case ("p", "{") => T_LPAREN
  case ("p", "(") => T_LPAREN
  case ("p", ")") => T_LPAREN
  case ("p", "}") => T_RPAREN
  case ("i", s) => T_ID(s)
  case ("o", s) => T_OP(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("k", s) => T_KWD(s)
  case ("sym", s) => T_SYM(s)
  case ("str", s) => T_STR(StringContext treatEscapes(s.substring(1, s.length - 1)))
}

// by using collect we filter out all unwanted tokens
def tokenise(s: String) : List[Token] = 
  lexing_simp(WHILE_REGS, s).collect(token)

case class ~[+A, +B](x: A, y: B)

// constraint for the input
type IsSeq[A] = A => Seq[_]


abstract class Parser[I : IsSeq, T]{
  def parse(in: I): Set[(T, I)]

  def parse_all(in: I) : Set[T] =
    for ((hd, tl) <- parse(in); 
        if tl.isEmpty) yield hd
}

// parser combinators

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}



case class TokenParser(s: String) extends Parser[List[Token], String] {
  def parse(tk: List[Token]) = tk match {
    case T_KWD(x)::rest => if (x == s) Set((s, rest)) else Set()
    case T_OP(x)::rest => if (x == s) Set((s, rest)) else Set()
    case T_SYM(x)::rest => if (x == s) Set((s, rest)) else Set()
    case T_SEMI::rest => Set((";", rest))
    case T_LPAREN::rest => Set(("(", rest))
    case T_RPAREN::rest => Set((")", rest))
    case _ => Set()
  }
}

case object StrParser extends Parser[List[Token], String] {
  def parse(tk: List[Token]) = tk match {
    case T_STR(x)::rest => Set((x, rest))
    case _ => Set()
  }
}

case object IdParser extends Parser[List[Token], String] {
  def parse(tk: List[Token]) = tk match {
    case T_ID(x)::rest => Set((x, rest))
    case _ => Set()
  }
}


case object NumParser extends Parser[List[Token], Int] {
  def parse(tk: List[Token]) = tk match {
    case T_NUM(x)::rest =>  Set((x, rest))
    case _ => Set()
  }
}


implicit def parser_interpolation(sc: StringContext) = new {
    def p(args: Any*) = TokenParser(sc.s(args:_*))
}    

implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Read(s: String) extends Stmt
case class WriteVar(s: String) extends Stmt
case class WriteStr(s: String) extends Stmt
case class ForLoop(a1: AExp, a2: AExp , bl: Block) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp


// arithmetic expressions
lazy val AExp: Parser[List[Token], AExp] = 
  (Te ~ p"+" ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("+", x, z) } ||
  (Te ~ p"-" ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("-", x, z) } || Te
lazy val Te: Parser[List[Token], AExp] = 
  (Fa ~ p"*" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("*", x, z) } ||
  (Fa ~ p"/" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("/", x, z) } || 
  (Fa ~ p"%" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("%", x, z) } || Fa  
lazy val Fa: Parser[List[Token], AExp] = 
   (p"(" ~ AExp ~ p")").map{ case _ ~ y ~ _ => y } || 
   IdParser.map(Var) || 
   NumParser.map(Num) 


// boolean expressions with some simple nesting
lazy val BExp: Parser[List[Token], BExp] = 
   (AExp ~ p"==" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ p"!=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } ||
   (AExp ~ p">=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z) } || 
   (AExp ~ p"<=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z) } ||  
   (AExp ~ p"<" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ p">" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">", x, z) } ||
   (p"(" ~ BExp ~ p")" ~ p"&&" ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => And(y, v) } ||
   (p"(" ~ BExp ~ p")" ~ p"||" ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => Or(y, v) } ||
   (p"true".map[BExp]{ _ => True }) || 
   (p"false".map[BExp]{ _ => False }) ||
   (p"(" ~ BExp ~ p")").map[BExp]{ case _ ~ x ~ _ => x }


lazy val Stmt: Parser[List[Token], Stmt] =
  ((p"skip".map[Stmt]{_ => Skip }) ||
   (IdParser ~ p":=" ~ AExp).map[Stmt]{ case x ~ _ ~ z => Assign(x, z) } ||
   (p"write" ~ IdParser).map[Stmt]{ case _ ~ y => WriteVar(y) } ||
   (p"write" ~ StrParser).map[Stmt]{ case _ ~ y => WriteStr(y) } ||
   (p"read" ~ IdParser).map[Stmt]{ case _ ~ y => Read(y) } ||
   (p"write"~ p"(" ~ StrParser ~ p")").map[Stmt]{ case _ ~ _ ~ y ~ _ => WriteStr(y) } ||
   (p"write" ~ p"(" ~ IdParser ~ p")").map[Stmt]{ case _ ~ _ ~ y ~ _ => WriteVar(y) } ||
   (p"read" ~ p"(" ~ IdParser ~ p")").map[Stmt]{ case _ ~ _ ~ y ~ _ => Read(y) } ||
   (p"if" ~ BExp ~ p"then" ~ Block ~ p"else" ~ Block)
     .map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
   (p"while" ~ BExp ~ p"do" ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ w => While(y, w) } ||
   (p"for" ~ IdParser ~ p":=" ~ AExp ~ p"upto" ~ AExp ~ p"do" ~ Block)
   .map[Stmt]{ case _ ~ _ ~ _ ~ y ~ _ ~ u ~ _ ~ w => For(y, u, w)})     


// statements
lazy val Stmts: Parser[List[Token], Block] =
  (Stmt ~ p";" ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[Token], Block] =
  ((p"{" ~ Stmts ~ p"}").map{ case _ ~ y ~ _ => y } || 
  (p"(" ~ Stmts ~ p")").map{ case _ ~ y ~ _ => y } ||
   (Stmt.map(s => List(s))))


var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}


implicit def sring_inters(sc: StringContext) = new {
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

