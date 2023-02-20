import FF.NewField

import Init.Data.Nat.Basic
import Init.Data.Nat.Div

/-- Curves with Weierstrass form satisfying the equation `y² = x³ + a x + b` -/
class Curve (K : Type _) (F : outParam (Type _)) [PrimeField F] where
  /-- `a` coefficient -/
  a : F
  /-- `b` coefficient -/
  b : F
  /-- Curve order -/
  order : Nat
  /-- Curve cofactor -/
  cofactor : Nat
  /-- Curve characteristic -/
  characteristic : Nat
  /- More here -/

class EdwardsCurve (C : Type _) (F : Type _) [PrimeField F] extends Curve C F where
  edwardsForm : F × F × F

namespace Curve

/-- `y² = x³ + a x + b ↦ (a, b)`   -/
def weierstrassForm (C : Type _) [PrimeField F] [Curve C F] : F × F := 
  (Curve.a C, Curve.b C) 

def jacobianForm (C : Type _) [PrimeField F] [Curve C F] : F × F := sorry 

end Curve

structure AffinePoint (F : Type _) [PrimeField F] where
  x : F
  y : F
  isInfty : Bool

structure ProjectivePoint (F : Type _) [PrimeField F] where
  x : F
  y : F
  z : F

/--
`CurvePoint` provides algebraic operations on elliptic curve points and related constants
-/
class CurvePoint {F : Type _} (C : Type _) (K : Type _) [PrimeField F] [Curve C F] where
  /-- The neutral element of the Abelian group of points. -/
  zero : K
  /-- The base point. -/
  base : K
  /-- `inv` inverses a given point. -/
  inv : K → K
  /-- Point addition. -/
  add : K → K → K
  /-- `double : p ↦ 2 ⬝ p` -/
  double : K → K := fun x => add x x 
  /-- Number-point multiplication. -/
  smul : Nat → K → K
  /-- `toPoint` form a point from prime field elements whenever it is possible -/
  toPoint : F → F → Option K
  /-- Frobenius endomorphism -/
  frobenius : F → F
  

def infinity [PrimeField F] : ProjectivePoint F :=
  ProjectivePoint.mk 0 1 0

def ProjectivePoint.isInfinity {F : Type _} [PrimeField F] : ProjectivePoint F → Bool
  | c => c.z == 0

-- P₁ : AffinePoint, P₂ : ProjectivePoint ==> P₁ + P₂
-- (x, y) : AffinePoint => (x, y, 1) : ProjectivePoint
-- (x, y, z) : ProjectivePoint => (x/z, y/z) : AffinePoint
-- If z ≠ 0
-- If z = 0

def affineAdd [PrimeField F] [Curve C F] : 
  AffinePoint F → AffinePoint F → AffinePoint F
  | a@⟨x₁, y₁, i⟩, b@⟨x₂, y₂, j⟩ => 
    match i, j with
    | true, _ => a
    | _, true => b
    | false, false => 
      let lambda := (y₁ + y₂) / (x₁ + y₂)
      let x₃ := lambda^2 + lambda + x₁ + x₂ + Curve.a C
      let y₃ := lambda * (x₁ + x₃) + x₃ + x₁
      ⟨ x₃, y₃, false ⟩

def affineDouble [PrimeField F] [Curve C F] :
  AffinePoint F → AffinePoint F
  | ⟨x, y, i⟩ =>
    let lambda := ((3 : Nat) * x^2 + Curve.a C) / (2 : Nat) * y
    let x' := lambda^2 - (2 : Nat) * x
    let y' := lambda * (x - x') - y
    ⟨x', y', i⟩

def affineSmul [pr : PrimeField F] [c : Curve C F] (n : Nat) (p : AffinePoint F) : AffinePoint F :=
  match h : n with
  | 0 => ⟨ 0, 1, true ⟩
  | k + 1 =>
  if k == 0 then p
  else
    have : n / 2 < n := 
    Nat.div_lt_self (Nat.zero_lt_of_ne_zero (h ▸ Nat.succ_ne_zero k)) (by decide)
    let p' := @affineSmul F C pr c (n / 2) (@affineDouble F C pr c p)
    let isEven n := if n % 2 == 0 then true else false
    if isEven n then p' else @affineAdd F C pr c p p'
  termination_by _ => n

instance {F} [p : PrimeField F] [c : Curve C F] : CurvePoint C (AffinePoint F) where
  base := sorry
  zero := sorry
  inv := fun a@⟨x, y, i⟩ => if i then a else ⟨x, -y, i⟩
  add := @affineAdd F C p c
  double := @affineDouble F C p c
  smul := @affineSmul F C p c
  toPoint := sorry
  frobenius := sorry

instance {F} [PrimeField F] [Curve C F] : CurvePoint C (ProjectivePoint F) where
  zero := sorry
  base := sorry
  inv := sorry
  add := sorry
  smul := sorry
  toPoint := sorry
  frobenius := sorry
  double := sorry

-- class CurveGroup (C : Type _) {F : outParam (Type _)} [PrimeField F] [Curve C F] where
  -- zero {K : Type _} [CurvePoint C K] : K
  -- gen {K : Type _} [CurvePoint C K] : K
  -- inv {K : Type _} [CurvePoint C K] : K → K
  -- double {K : Type _} [CurvePoint C K] : K → K
  -- add {K L M : Type _} [CurvePoint C K] [CurvePoint C L] [CurvePoint C M] : K → L → M