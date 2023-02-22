import FF.NewField

import Init.Data.Nat.Basic
import Init.Data.Nat.Div

import YatimaStdLib.Bit

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
  A : F
  B : F
  C : F

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

def mapAffine [PrimeField F] [PrimeField G] (f : F → G) : AffinePoint F → AffinePoint G
  | ⟨ x, y, i ⟩ => ⟨f x, f y, i⟩ 

structure ProjectivePoint (F : Type _) [PrimeField F] where
  x : F
  y : F
  z : F

def mapProjective [PrimeField F] [PrimeField G] (f : F → G) : ProjectivePoint F → ProjectivePoint G
  | ⟨x, y, z⟩ => ⟨f x, f y, f z⟩

def infinity [PrimeField F] : ProjectivePoint F :=
  ProjectivePoint.mk 0 1 0

def ProjectivePoint.isInfinity {F : Type _} [PrimeField F] : ProjectivePoint F → Bool
  | c => c.z == 0

def toAffine [PrimeField F] : ProjectivePoint F → AffinePoint F
  | ⟨x, y, z⟩ => if z == 0 then ⟨0, 1, true⟩ else ⟨x / z, y / z, false⟩

/--
`CurvePoint` provides algebraic operations on elliptic curve points and constants.
-/
class CurvePoint {F : Type _} (C : Type _) (K : Type _) [PrimeField F] [Curve C F] where
  /-- The neutral element of the Abelian group of points. -/
  zero : K
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
  frobenius : K → K

def smul' [pr : PrimeField F] [cur : Curve C F] 
  [point : @CurvePoint F C K pr cur] (n : Nat) (p : K) : K := Id.run do
  let mut p₁ := p
  let mut p₂ := point.double p
  let n₂ := n.toBits
  for i in [0:n₂.length - 1] do
    -- TODO: rewrite this line safely
    if List.get! n₂ i == 0 then
    p₁ := point.double p₁
    p₂ := point.add p₁ p₂
    else
    p₁ := point.add p₁ p₂
    p₂ := point.double p₂
  return p₂

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
  zero := sorry
  inv := fun a@⟨x, y, i⟩ => if i then a else ⟨x, -y, i⟩
  add := @affineAdd F C p c
  double := @affineDouble F C p c
  smul := @affineSmul F C p c
  toPoint x y :=
    let p := ⟨x, y, true⟩
    if (x * x + c.a * x) * x + c.b == y * y then some p else none
  frobenius := mapAffine fun a => a ^ p.char

instance {F} [p : PrimeField F] [c : Curve C F] : CurvePoint C (ProjectivePoint F) where
  zero := infinity
  inv := fun ⟨x, y, z⟩ => ⟨x, -y, z⟩
  add :=
    fun p₁@⟨x₁, y₁, z₁⟩ p₂@⟨x₂, y₂, z₂⟩ =>
      match p₁.isInfinity, p₂.isInfinity with
        | true, _ => infinity
        | _, true => infinity
        | false, false =>
          let y₁z₂ := y₁ * z₂
          let x₁z₂ := x₁ * z₂
          let z₁z₂ := z₁ * z₂
          let u := y₂ * z₁ - y₁z₂
          let uSquare := u * u
          let v := x₂ * z₁ - x₁z₂
          let vSquare := v^2
          let vCube := v^3
          let r := vSquare * x₁z₂
          let a := uSquare * z₁z₂ - vCube - (2 : Nat) * r
          ⟨v * a, u * (r - a) - vCube * y₁z₂, vCube * z₁z₂⟩
  smul := sorry
  toPoint x y :=
    let p := ⟨x, y, 1⟩
    let isDef := fun (⟨x, y, z⟩ : ProjectivePoint F) =>
      (x * x + c.a * z * z) * x == (y * y - c.b * z * z) * z
    if isDef p then some p else none
  frobenius := mapProjective fun a => p.char
  double :=
    fun p@⟨x, y, z⟩ => if p.isInfinity then infinity
    else
    let xSquare := x * x
    let zSquare := z * z
    let w := c.a * zSquare + (3 : Nat) * xSquare
    let s := (2 : Nat) * y * z
    let sCube := s * s * s
    let r := y * s
    let rSquare := r * r
    let xr := r + x
    let b := xr * xr - xSquare - xr
    let h := w * w - (2 : Nat) * c.b
    ⟨h * s, w * (b - h) - (2 : Nat) * rSquare, sCube⟩

class CurveGenerator (K : Type _) where
  /-- The base point. -/
  base : K

-- class CurveGroup (C : Type _) {F : outParam (Type _)} [PrimeField F] [Curve C F] where
  -- zero {K : Type _} [CurvePoint C K] : K
  -- gen {K : Type _} [CurvePoint C K] : K
  -- inv {K : Type _} [CurvePoint C K] : K → K
  -- double {K : Type _} [CurvePoint C K] : K → K
  -- add {K L M : Type _} [CurvePoint C K] [CurvePoint C L] [CurvePoint C M] : K → L → M