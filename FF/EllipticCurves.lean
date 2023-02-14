import FF.GaloisField

open GaloisField

namespace EllipticCurves

inductive AffinePoint (Q : Type _) (R : Type _) where
  -- affine point
  | A : Q → Q → AffinePoint Q R
  -- infinity point
  | O : AffinePoint Q R
  deriving BEq

inductive ProjectivePoint (Q : Type _) (R : Type _) where
  | P : Q → Q → Q → ProjectivePoint Q R
  deriving BEq

class Curve (Q : Type _) (R : Type _) where
  char : AffinePoint Q R → Nat
  cof : AffinePoint Q R → Nat
  isWellDefined : AffinePoint Q R → Bool
  disc : AffinePoint Q R → Q
  order : AffinePoint Q R → Nat
  add : AffinePoint Q R → AffinePoint Q R → AffinePoint Q R
  dbl : AffinePoint Q R → AffinePoint Q R
  id : AffinePoint Q R
  inv : AffinePoint Q R → AffinePoint Q R
  frob : AffinePoint Q R → AffinePoint Q R
  gen : AffinePoint Q R
  point : Q → Q → Option (AffinePoint Q R)
  a_ : Q
  b_ : Q
  h_ : Nat
  q_ : Nat
  r_ : Nat
  gA_ : AffinePoint Q R

open Curve AffinePoint

variable {Q R : Type _}  [galq : GaloisField Q] [BEq Q] [cur : Curve Q R]
  [Neg Q] [OfNat Q 4] [OfNat Q 27] [OfNat Q 2] [OfNat Q 3] 
  [galr : GaloisField R] [prr : PrimeField R] [OfNat Q 0] 

def char : AffinePoint Q R → Nat := fun _ => cur.q_

def cof : AffinePoint Q R → Nat := fun _ => cur.h_

def add (x : AffinePoint Q R) (y : AffinePoint Q R) : AffinePoint Q R  :=
  match (x, y) with
  | (.O, _) => .O
  | (_, .O) => .O
  | (.A x₁ y₁, .A x₂ y₂) =>
    if x₁ == x₂ then .O else
      let l := (y₁ - y₂) / (x₁ - x₂)
      let x₃ := ((l * l) - x₁) - x₂
      let y₃ := (l * (x₁ - x₃)) - y₁
      .A x₃ y₃

def isWellDefined : AffinePoint Q R → Bool
    | .O => true
    | .A x y => 
    (((x * x) + @a_ Q R cur) * x) + cur.b_ == y * y

def disc (_ : AffinePoint Q R) : Q 
  := (((4 * cur.a_ : Q) * cur.a_) * cur.a_) + ((27 * cur.b_ : Q) * cur.b_ : Q)

def order : AffinePoint Q R → Nat := fun _ => cur.r_

def dbl : AffinePoint Q R → AffinePoint Q R
  | .O => .O
  | .A x y =>
    if y == 0 then .O else
    let xx := x * x
    let l := (((xx + xx) + xx) + cur.a_) / (y + y)
    let x' := ((l * l) - x) - x
    let y' := (l * (x - x')) - y
    .A x' y'

def id : AffinePoint Q R := .O

def inv : AffinePoint Q R → AffinePoint Q R
  | .O => .O
  | .A x y => .A x (-y)

def frob : AffinePoint Q R → AffinePoint Q R
  | .O => .O
  | .A x y => .A (GaloisField.frob x) (GaloisField.frob y)

def gen : AffinePoint Q R := cur.gA_

def point (x : Q) (y : Q) : Option (AffinePoint Q R) :=
  let p := AffinePoint.A x y
  if (((x * x) + cur.a_) * x) + cur.b_ == y * y then Option.some p else none

instance [BEq (AffinePoint Q R)] : Add (AffinePoint Q R) where
  add x y := if x == y then dbl x else add x y

instance : OfNat (AffinePoint Q R) 0 where
  ofNat := cur.id

open Nat in
def mulNat (p : AffinePoint Q R) (n : Nat) : AffinePoint Q R :=
  match h : n with
    | 0 => id
    | (Nat.succ k) =>
      if k == 0 then p
      else
        have : n / 2 < n := 
        div_lt_self (zero_lt_of_ne_zero (h ▸ succ_ne_zero k)) (by decide)
        let p' := mulNat (dbl p) (n / 2)
        let isEven n := if n % 2 == 0 then true else false
        if isEven n then p' else add p p'
    termination_by _ => n

instance : Sub (AffinePoint Q R) where
  sub a b := add a (inv b)

end EllipticCurves