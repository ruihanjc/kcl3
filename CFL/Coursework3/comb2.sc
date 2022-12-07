// Parser Combinators:
// Simple Version for WHILE-language
//====================================
//
// with some added convenience for
// map-parsers and grammar rules
//
// call with
//
//    amm comb2.sc


// more convenience for the map parsers later on;
// it allows writing nested patterns as
// case x ~ y ~ z => ...

import scala.io.StdIn.readInt

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
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "to" | "for" | "true" | "false"
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

// the following string interpolation allows us to write 
// TokenParser(_some_string_) more conveniently as 
//
// p"<_some_string_>" 
implicit def parser_interpolation(sc: StringContext) = new {
    def p(args: Any*) = TokenParser(sc.s(args:_*))
}    

// more convenient syntax for parser combinators
implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}


// the abstract syntax trees for the WHILE language
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

// a single statement 
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
   (p"while" ~ BExp ~ p"do" ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ w => While(y, w) })   


// statements
lazy val Stmts: Parser[List[Token], Block] =
  (Stmt ~ p";" ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[Token], Block] =
  ((p"{" ~ Stmts ~ p"}").map{ case _ ~ y ~ _ => y } || 
  (p"(" ~ Stmts ~ p")").map{ case _ ~ y ~ _ => y } ||
   (Stmt.map(s => List(s))))


// Examples
@arg(doc = "parser tree test")
@main
def parser_test() = {
  println("Parser tree test")
  Stmt.parse_all(tokenise("if (a < b) then skip else a := a * b + 1"))
}


// an interpreter for the WHILE language

type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env) : Int = a match {
  case Num(i) => i
  case Var(s) => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
}

def eval_bexp(b: BExp, env: Env) : Boolean = b match {
  case True => true
  case False => false
  case Bop("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bop("!=", a1, a2) => (eval_aexp(a1, env) != eval_aexp(a2, env))
  case Bop("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  case Bop(">=", a1, a2) => eval_aexp(a1, env) >= eval_aexp(a2, env)
  case Bop(">", a1, a2) => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bop("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)
  case And(b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Or(b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
}

def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env) 
  case While(b, bl) => 
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case WriteStr(x) => { print(x) ; env }  
  case WriteVar(x) => { print(env(x)) ; env }  
  case Read(x) => env + (x -> readInt()) 
}

def eval_bl(bl: Block, env: Env) : Env = bl match {
  case Nil => env
  case s::bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block) : Env = eval_bl(bl, Map())


val tree = """ if (a < b) then skip else a := a * b + 1"""

@arg(doc = "Parse tree test")
@main
def parseTreeTest() = {
  println("Parse Tree")
  println(Stmts.parse_all(tokenise(tree)))
}

val fib =  
   """
      write "Fib: ";
      read n;
      minus1 := 1;
      minus2 := 0;
      while n > 0 do {
      temp := minus2;
      minus2 := minus1 + minus2;
      minus1 := temp;
      n := n - 1
      };
      write "Result: ";
      write minus2 ;
      write "\n"
   """


@arg(doc = "Fibonacci test")
@main
def fibTest() = {
  println(eval(Stmts.parse_all(tokenise(fib)).head))
}
val t = System.nanoTime
val three = 
   """
      start := 200;
      x := start;
      y := start;
      z := start;
      while 0 < x do {
      while 0 < y do {
      while 0 < z do { z := z - 1 };
      z := start;
      y := y - 1
      };
      y := start;
      x := x - 1
      }
    """

@arg(doc = "three_nested_loops test")
@main
def threeTest() = {
  println("Three Nested Loop")
  println(eval(Stmts.parse_all(tokenise(three)).head)) 
  println("The time needed is:" + (System.nanoTime - t) / 1e9d + "seconds")
}


val factors =  
   """n := 12;
      f := 2;
      while (f < n / 2 + 1) do {
        if ((n / f) * f == n) then  { write(f) } else { skip };
        f := f + 1
      }"""


@arg(doc = "Factors test")
@main
def factorTest() = {
  println("Factors")
  println(eval(Stmts.parse_all(tokenise(factors)).head))
}



// prints out prime numbers from 2 to 100
val primes =  
   """
  end := 100;
  n := 2;
  while (n < end) do {
  f := 2;
  tmp := 0;
  while ((f < n / 2 + 1) && (tmp == 0)) do {
  if ((n / f) * f == n) then { tmp := 1 } else { skip };
  f := f + 1
  };
  if (tmp == 0) then { write(n); write("\n") } else { skip };
  n := n + 1
  }
  """

@arg(doc = "Primes test")
@main
def primeTest() = {
  println("Primes")
  println(eval(Stmts.parse_all(tokenise(primes)).head))
}


val collatz =
  """
    // wewew
    bnd := 1;
    while bnd < 101 do {
      write bnd;
      write ": ";
      n := bnd;
      cnt := 0;
      while n > 1 do {
        write n;
        write ",";
        if n % 2 == 0
        then n := n / 2
        else n := 3 * n+1;
        cnt := cnt + 1
      };
      write " => ";
      write cnt;
      write "\n";
      bnd := bnd + 1
    }
  """

@arg(doc = "Collatz test")
@main
def collatzTest() = {
  println("Collatz")
  //println(tokenise(collatz))
  println(eval(Stmts.parse_all(tokenise(collatz)).head))
}


// runs with amm2 and amm3
