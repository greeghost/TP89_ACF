package bank

import bank.observer.Observer
import bank.observer.Subject



object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
  implicit def `Product_Type.equal_prod`[A : equal, B : equal]: equal[(A, B)] =
    new equal[(A, B)] {
    val `HOL.equal` = (a: (A, B), b: (A, B)) =>
      Product_Type.equal_proda[A, B](a, b)
  }
  implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
    val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Orderings {

trait ord[A] {
  val `Orderings.less_eq`: (A, A) => Boolean
  val `Orderings.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Orderings.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)
object ord {
  implicit def `Code_Numeral.ord_integer`: ord[BigInt] = new ord[BigInt] {
    val `Orderings.less_eq` = (a: BigInt, b: BigInt) => a <= b
    val `Orderings.less` = (a: BigInt, b: BigInt) => a < b
  }
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

} /* object Orderings */

object Code_Numeral {

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

def nat_of_integer(k: BigInt): Nat.nat =
  Nat.Nata(Orderings.max[BigInt](BigInt(0), k))

} /* object Code_Numeral */

object Nat {

abstract sealed class nat
final case class Nata(a: BigInt) extends nat

def equal_nata(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) == Code_Numeral.integer_of_nat(n)

def less_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) < Code_Numeral.integer_of_nat(n)

def zero_nat: nat = Nata(BigInt(0))

def less_eq_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) <= Code_Numeral.integer_of_nat(n)

} /* object Nat */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

} /* object Num */

object Product_Type {

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
}

} /* object Product_Type */

object table {

abstract sealed class option[A]
final case class Somea[A](a: A) extends option[A]
final case class Nonea[A]() extends option[A]

def assoc[A : HOL.equal, B](uu: A, x1: List[(A, B)]): option[B] = (uu, x1) match
  {
  case (uu, Nil) => Nonea[B]()
  case (x1, (x, y) :: xs) =>
    (if (HOL.eq[A](x, x1)) Somea[B](y) else assoc[A, B](x1, xs))
}

def modify[A : HOL.equal, B](x: A, y: B, xa2: List[(A, B)]): List[(A, B)] =
  (x, y, xa2) match {
  case (x, y, Nil) => List((x, y))
  case (x, y, (z, u) :: r) =>
    (if (HOL.eq[A](x, z)) (x, y) :: r else (z, u) :: modify[A, B](x, y, r))
}

} /* object table */

object tp89 {

abstract sealed class message
final case class Pay(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
  message
final case class Ack(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
  message
final case class Cancel(a: (Nat.nat, (Nat.nat, Nat.nat))) extends message

def export(x0: List[((Nat.nat, (Nat.nat, Nat.nat)),
                      (Nat.nat, (Nat.nat, (Boolean, Boolean))))]):
      List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)]
  =
  x0 match {
  case Nil => Nil
  case v :: va =>
    (v match {
       case (_, (_, (_, (true, _)))) => export(va)
       case (tid, (_, (amc, (false, true)))) => (tid, amc) :: export(va)
       case (_, (_, (_, (false, false)))) => export(va)
     })
}

def traiterMessage(x0: message,
                    bdd: List[((Nat.nat, (Nat.nat, Nat.nat)),
                                (Nat.nat, (Nat.nat, (Boolean, Boolean))))]):
      List[((Nat.nat, (Nat.nat, Nat.nat)),
             (Nat.nat, (Nat.nat, (Boolean, Boolean))))]
  =
  (x0, bdd) match {
  case (Cancel(i), bdd) =>
    table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                  (Nat.nat,
                    (Nat.nat,
                      (Boolean,
                        Boolean)))](i, (Nat.zero_nat,
 (Nat.zero_nat, (true, false))),
                                     bdd)
  case (Pay(i, amc), bdd) =>
    (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
                  (Nat.nat, (Nat.nat, (Boolean, Boolean)))](i, bdd)
       match {
       case table.Somea((amm, (amc2, (ann, vala)))) =>
         (if (! ann && (! vala && Nat.less_nat(amc2, amc)))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         (Nat.nat,
                           (Nat.nat,
                             (Boolean,
                               Boolean)))](i,
    (amm, (amc, (ann, Nat.less_eq_nat(amm, amc)))), bdd)
           else bdd)
       case table.Nonea() =>
         table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                       (Nat.nat,
                         (Nat.nat,
                           (Boolean,
                             Boolean)))](i,
  (Code_Numeral.nat_of_integer(BigInt(999999)), (amc, (false, false))), bdd)
     })
  case (Ack(i, amm), bdd) =>
    (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
                  (Nat.nat, (Nat.nat, (Boolean, Boolean)))](i, bdd)
       match {
       case table.Somea((amm2, (amc, (ann, vala)))) =>
         (if (! ann && (! vala && Nat.less_nat(amm, amm2)))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         (Nat.nat,
                           (Nat.nat,
                             (Boolean,
                               Boolean)))](i,
    (amm, (amc, (ann, Nat.less_eq_nat(amm, amc)))), bdd)
           else bdd)
       case table.Nonea() =>
         table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                       (Nat.nat,
                         (Nat.nat,
                           (Boolean,
                             Boolean)))](i,
  (amm, (Nat.zero_nat, (false, false))), bdd)
     })
}

} /* object tp89 */

	
	
}