package validator.BOULIER_SOURISSEAU

import bank._


// Automatic conversion of bank.message to tp89.messages and Nat to bank.Nat
object Converter{
  implicit def bank2message(m:bank.message):tp89.message=
    m match {
    case bank.Pay((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Pay((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Ack((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Ack((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Cancel((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i)))) => tp89.Cancel((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))))
  }
  
  implicit def trans2bankTrans(l:List[((Nat.nat,(Nat.nat,Nat.nat)),Nat.nat)]): List[((bank.Nat.nat,(bank.Nat.nat,bank.Nat.nat)),bank.Nat.nat)]=
    l match {
    case Nil => Nil
    case ((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))::r => ((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p))::trans2bankTrans(r)
  }
}

import Converter._


/* The object to complete */
class ConcreteValidator extends TransValidator{
  var transBdd: List[((Nat.nat, (Nat.nat, Nat.nat)),
                      (tp89.betterNat, (tp89.betterNat, (Boolean, Boolean))))] = List()
  def process(m:message):Unit={
    this.transBdd = tp89.traiterMessage(m, this.transBdd)
  }
  // TODO
  def getValidTrans= tp89.export(transBdd)
}


// Objets utile pour pouvoir compiler avant la première exportation
// ...à supprimer une fois que votre export aura été fait.
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

object Code_Numeral {

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

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

abstract sealed class betterNat
final case class N(a: Nat.nat) extends betterNat
final case class Undeclared() extends betterNat

def export(x0: List[((Nat.nat, (Nat.nat, Nat.nat)),
                      (betterNat, (betterNat, (Boolean, Boolean))))]):
      List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)]
  =
  x0 match {
  case Nil => Nil
  case v :: va =>
    (v match {
       case (_, (_, (_, (true, _)))) => export(va)
       case (tid, (_, (N(amcnat), (false, true)))) =>
         (tid, amcnat) :: export(va)
       case (_, (_, (_, (false, false)))) => export(va)
     })
}

def comparison(x0: betterNat, uu: betterNat, uv: Nat.nat => Nat.nat => Boolean):
      Boolean
  =
  (x0, uu, uv) match {
  case (Undeclared(), uu, uv) => false
  case (N(v), Undeclared(), ux) => false
  case (N(i), N(j), f) => (f(i))(j)
}

def equal_betterNat(x0: betterNat, x1: betterNat): Boolean = (x0, x1) match {
  case (N(x1), Undeclared()) => false
  case (Undeclared(), N(x1)) => false
  case (N(x1), N(y1)) => Nat.equal_nata(x1, y1)
  case (Undeclared(), Undeclared()) => true
}

def traiterMessage(x0: message,
                    bdd: List[((Nat.nat, (Nat.nat, Nat.nat)),
                                (betterNat, (betterNat, (Boolean, Boolean))))]):
      List[((Nat.nat, (Nat.nat, Nat.nat)),
             (betterNat, (betterNat, (Boolean, Boolean))))]
  =
  (x0, bdd) match {
  case (Cancel(i), bdd) =>
    table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                  (betterNat,
                    (betterNat,
                      (Boolean,
                        Boolean)))](i, (Undeclared(),
 (Undeclared(), (true, false))),
                                     bdd)
  case (Pay(i, amc), bdd) =>
    (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
                  (betterNat, (betterNat, (Boolean, Boolean)))](i, bdd)
       match {
       case table.Somea((amm, (amc2, (ann, vala)))) =>
         (if (! ann &&
                (! vala &&
                  (comparison(N(amc), amc2,
                               ((x: Nat.nat) => (y: Nat.nat) =>
                                 Nat.less_nat(y, x))) &&
                    comparison(N(amc), N(Nat.zero_nat),
                                ((x: Nat.nat) => (y: Nat.nat) =>
                                  Nat.less_nat(y, x))))))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         (betterNat,
                           (betterNat,
                             (Boolean,
                               Boolean)))](i,
    (amm, (N(amc),
            (false,
              comparison(N(amc), amm,
                          ((x: Nat.nat) => (y: Nat.nat) =>
                            Nat.less_eq_nat(y, x)))))),
    bdd)
           else bdd)
       case table.Nonea() =>
         (if (Nat.less_nat(Nat.zero_nat, amc))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         (betterNat,
                           (betterNat,
                             (Boolean,
                               Boolean)))](i,
    (Undeclared(), (N(amc), (false, false))), bdd)
           else bdd)
     })
  case (Ack(i, amm), bdd) =>
    (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
                  (betterNat, (betterNat, (Boolean, Boolean)))](i, bdd)
       match {
       case table.Somea((amm2, (amc, (ann, vala)))) =>
         (if (! ann &&
                (! vala &&
                  ((equal_betterNat(amm2, Undeclared()) ||
                     ! (comparison(N(amm), amm2,
                                    ((x: Nat.nat) => (y: Nat.nat) =>
                                      Nat.less_eq_nat(y, x))))) &&
                    ((equal_betterNat(amc, Undeclared()) ||
                       comparison(amc, N(Nat.zero_nat),
                                   ((x: Nat.nat) => (y: Nat.nat) =>
                                     Nat.less_nat(y, x)))) &&
                      (equal_betterNat(amm2, Undeclared()) ||
                        comparison(amm2, N(Nat.zero_nat),
                                    ((x: Nat.nat) => (y: Nat.nat) =>
                                      Nat.less_eq_nat(y, x))))))))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         (betterNat,
                           (betterNat,
                             (Boolean,
                               Boolean)))](i,
    (N(amm),
      (amc, (false,
              equal_betterNat(amc, Undeclared()) ||
                comparison(amc, N(amm),
                            ((x: Nat.nat) => (y: Nat.nat) =>
                              Nat.less_eq_nat(y, x)))))),
    bdd)
           else bdd)
       case table.Nonea() =>
         table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                       (betterNat,
                         (betterNat,
                           (Boolean,
                             Boolean)))](i,
  (N(amm), (N(Nat.zero_nat), (false, false))), bdd)
     })
}

} /* object tp89 */
