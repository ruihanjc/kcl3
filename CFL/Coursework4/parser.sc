import $file.lexer, lexer._

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
    case T_SEMI::rest => Set()
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
case class ForLoop (s: AExp, n: AExp, n1: AExp, bl: Block) extends Stmt


case class Var(s: String) extends AExp
case class Str(s: String) extends AExp
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
   NumParser.map(Num) ||
   StrParser.map(Str)


// boolean expressions with some simple nesting
lazy val BExp: Parser[List[Token], BExp] =
  (Rel ~ p"&&" ~ BExp).map[BExp]{ case y ~ _ ~ v => And(y, v) } ||
  (Rel ~ p"||" ~ BExp).map[BExp]{ case y ~ _ ~ v => Or(y, v) } || Rel
lazy val Rel: Parser[List[Token], BExp] = 
   (AExp ~ p"==" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ p"!=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } ||
   (AExp ~ p"<" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ p">" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">", x, z) } ||
   (AExp ~ p">=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z) } || 
   (AExp ~ p"<=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z) } ||  Bt
lazy val Bt: Parser[List[Token], BExp] =    
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
   (p"for" ~ AExp ~ p":=" ~ AExp ~ p"upto" ~ AExp ~ p"do" ~ Block)
   .map[Stmt]{ case _ ~ x ~ _ ~ y ~ _ ~ u ~ _ ~ w =>
        ForLoop(x , y, u, w)
   })     


// statements
lazy val Stmts: Parser[List[Token], Block] =
  (Stmt ~ p";").map[Block]{ case x ~ _ => List(x) } ||
  (Stmt ~ p";" ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[Token], Block] =
  ((p"{" ~ Stmts ~ p"}").map{ case _ ~ y ~ _ => y } || 
  (p"(" ~ Stmts ~ p")").map{ case _ ~ y ~ _ => y } ||
   (Stmt.map(s => List(s))))

