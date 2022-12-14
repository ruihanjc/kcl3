// A version with simplification of derivatives;
// this keeps the regular expressions small, which
// is good for the run-time
// 
// call the test cases with X = {1,2}
//
//   amm re3.sc testX
//
// or 
//
//   amm re3.sc all

  
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class RANGE(cs: Set[Char]) extends Rexp
case class PLUS(r : Rexp) extends Rexp 
case class OPTIONAL(r : Rexp) extends Rexp
case class UPTO(r : Rexp, m: Int) extends Rexp
case class FROM(r : Rexp, n: Int) extends Rexp
case class BETWEEN(r : Rexp, n: Int, m: Int) extends Rexp
case class NOT(r : Rexp) extends Rexp
case class CFUN(f : Char => Boolean) extends Rexp
       




// the nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case UPTO(_, _) => true
  case FROM(r, i) => if (i==0) true else nullable(r)
  case BETWEEN(r, n, m) => if(n==0) true else nullable(r)
  case NOT(r) =>  !(nullable(r))
  case CFUN(r) => false
}

// the derivative of a regular expression w.r.t. a character
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case NTIMES(r, i) => if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i-1))
  case RANGE(cs) => if(cs.contains(c)) ONE else ZERO
  case PLUS(r) => ALT(der(c, r), PLUS(r))
  case OPTIONAL(r) => der(c,r)
  case UPTO(r, i) => if(i == 0) ZERO else SEQ(der(c,r), UPTO(r, i-1))
  case FROM(r, i) => if(i == 0) SEQ(der(c,r),FROM(r,i)) else SEQ(der(c,r),FROM(r, i-1))
  case BETWEEN(r, n, m) => if(m == 0) ZERO else if(n == m) SEQ(der(c,r), BETWEEN(r , n-1, m-1)) else if(n == 0) ALT(der(c,r), BETWEEN(r, n, m-1)) else BETWEEN(r, n-1,m-1)
  case NOT(r) => NOT(der(c,r))
  case CFUN(f) => if(f(c) == true) ONE else ZERO
}
  
def CHAR2(c: Char) : CFUN = CFUN((d: Char)  => (c == d))
def RANGE2(cs: Set[Char]) : CFUN = CFUN((d: Char)  => (cs.contains(d)))
val ALL : CFUN = CFUN((d: Char)  => (true))


def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s

    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}

// the derivative w.r.t. a string (iterates der)
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}


// the main matcher function
def matcher(r: Rexp, s: String) : Boolean = 
  nullable(ders(s.toList, r))


// one or zero
def OPT(r: Rexp) = ALT(r, ONE)


// Test Cases

// evil regular expressions: (a?){n} a{n}  and (a*)* b
def EVIL1(n: Int) = SEQ(NTIMES(OPT(CHAR('a')), n), NTIMES(CHAR('a'), n))
val EVIL2 = SEQ(STAR(STAR(CHAR('a'))), CHAR('b'))

val LET = ('a'to 'z').toSet
val NUM = ('0' to '9').toSet
val SYM:Set[Char]  = Set( '_', '.', '-')

def EMAIL =  SEQ( SEQ(PLUS(RANGE(LET ++ NUM ++ SYM)) , SEQ(CHAR('@'), PLUS(RANGE(LET ++ NUM ++ SYM)))) , SEQ(CHAR('.') ,BETWEEN(RANGE(LET + '.'),2,6)) )

// SEQ(CHAR('.') ,BETWEEN(RANGE(LET + '.'),2,6))    .ac.uk
// SEQ(CHAR('@'), PLUS(RANGE(LET ++ NUM ++ SYM)))   @kcl
// PLUS(RANGE(LET ++ NUM ++ SYM))   K20027110 || ruihan.ji

def UTEST = ALL


 

@arg(doc = "testD")
@main
def testD() = {
    println(matcher(EMAIL, "k20027110@kcl.ac.uk"))
}


@arg(doc = "dersD")
@main
def dersD() = {
    println((ders("ruihan.ji@kcl.ac.uk".toList, EMAIL)))
}

def TEST = NTIMES(OPTIONAL(CHAR('a')), 3) 

@arg(doc = "testF")
@main
def testF() = {
    println(matcher(UTEST, "w"))
}



def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}


@arg(doc = "Test (a?{n}) (a{n})")
@main
def test1() = {
  println("Test (a?{n}) (a{n})")

  for (i <- 0 to 9000 by 1000) {
    println(f"$i: ${time_needed(3, matcher(EVIL1(i), "a" * i))}%.5f")
  }
}  

@arg(doc = "Test (a*)* b")
@main
def test2() = {
  println("Test (a*)* b")

  for (i <- 0 to 6000000 by 500000) {
    println(f"$i: ${time_needed(3, matcher(EVIL2, "a" * i))}%.5f")
  }
}

// size of a regular expressions - for testing purposes 
def size(r: Rexp) : Int = r match {
  case ZERO => 1
  case ONE => 1
  case CHAR(_) => 1
  case ALT(r1, r2) => 1 + size(r1) + size(r2)
  case SEQ(r1, r2) => 1 + size(r1) + size(r2)
  case STAR(r) => 1 + size(r)

  case NTIMES(r, _) => 1 + size(r)
}


// now the size of the derivatives grows 
// much, much slower

size(ders("".toList, EVIL2))      // 5
size(ders("a".toList, EVIL2))     // 8
size(ders("aa".toList, EVIL2))    // 8
size(ders("aaa".toList, EVIL2))   // 8
size(ders("aaaa".toList, EVIL2))  // 8
size(ders("aaaaa".toList, EVIL2)) // 8


@arg(doc = "All tests.")
@main
def all() = { test1(); test2() } 





// PS:
//
// If you want to dig deeper into the topic, you can have 
// a look at these examples which still explode. They
// need an even more aggressive simplification.

// test: (a + aa)*
val EVIL3 = STAR(ALT(CHAR('a'), SEQ(CHAR('a'), CHAR('a'))))


@arg(doc = "Test EVIL3")
@main
def test3() = {
  println("Test (a + aa)*")

  for (i <- 0 to 30 by 5) {
    println(f"$i: ${time_needed(1, matcher(EVIL3, "a" * i))}%.5f")
  }
}



// test: (1 + a + aa)*
val EVIL4 = STAR(ALT(ONE, ALT(CHAR('a'), SEQ(CHAR('a'), CHAR('a')))))

@arg(doc = "Test EVIL4")
@main
def test4() = {
  println("Test (1 + a + aa)*")

  for (i <- 0 to 30 by 5) {
    println(f"$i: ${time_needed(1, matcher(EVIL4, "a" * i))}%.5f")
  }
}

@arg(doc = "Tests that show not all is hunky-dory, but a solution leads too far afield.")
@main
def fail() = { test3(); test4() } 


