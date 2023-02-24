import FF.NewField

structure Curve (F : Type _) [Field F] where
  a : F
  b : F

structure ProjectivePoint {F : Type _} [Field F] (C : Curve F) where
  X : F
  Y : F
  Z : F

instance [ToString F] [Field F] {C : Curve F} : ToString $ ProjectivePoint C where
  toString := fun ⟨x, y, z⟩ => s!"({x} : {y} : {z})"

def ProjectivePoint.isInfinity {F : Type _} [Field F] {C : Curve F} (P : ProjectivePoint C) :=
  P.X == 0 && P.Y == 1 && P.Z == 0

def ProjectivePoint.infinity {F : Type _} [Field F] {C : Curve F} : ProjectivePoint C :=
  ⟨0, 1, 0⟩

def ProjectivePoint.add {F : Type _} [Field F] {C : Curve F} (P Q : ProjectivePoint C) : ProjectivePoint C :=
  let ⟨x₁, y₁, z₁⟩ := P
  let ⟨x₂, y₂, z₂⟩ := Q
    match P.isInfinity, Q.isInfinity with
      | true, _ => Q
      | _, true => P
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

partial def ProjectivePoint.scaleAux {F : Type _} [Field F] {C : Curve F} (n : Nat) 
  (P acc : ProjectivePoint C) : ProjectivePoint C :=
  if n == 0 then acc else
    if n % 2 == 0 then
      scaleAux (n >>> 1) (add P P) (add P acc)
    else
      scaleAux (n >>> 1) (add P P) acc
  

inductive AffinePoint {F : Type _} [Field F] (C : Curve F) where
  | affine (X : F) (Y : F) : AffinePoint C
  | infinity : AffinePoint C

class CurveGroup {F : Type _} [Field F] (C : Curve F) (K : Type _) where 
  zero : K 
  inv : K → K
  add : K → K → K
  scale : Nat → K → K  

instance {F K : Type _} [Field F] (C : Curve F) [CurveGroup C K] : Add K where
  add := CurveGroup.add C

instance {F K : Type _} [Field F] (C : Curve F) [CurveGroup C K] : Neg K where
  neg := CurveGroup.inv C

instance {F K : Type _} [Field F] (C : Curve F) [CurveGroup C K] : HMul Nat K K where
  hMul := CurveGroup.scale C
  
open ProjectivePoint in
instance {F : Type _} [Field F] {C : Curve F} : CurveGroup C (ProjectivePoint C) where 
  zero := infinity
  inv := fun ⟨x, y, z⟩ => ⟨x, 0 - y, z⟩ 
  add := ProjectivePoint.add
  scale n := ProjectivePoint.scaleAux n infinity

instance {F : Type _} [Field F] {C : Curve F} : CurveGroup C (AffinePoint C) where 
  zero := .infinity
  inv := sorry
  add := sorry
  scale := sorry

abbrev Fp := Zmod 101

instance : ToString Fp where
  toString n := reprStr n  

def NewCurve : Curve Fp where
  a := 2
  b := 3  

def G : ProjectivePoint NewCurve := ⟨52, 74, 1⟩

#eval G + G + G
#eval 2 * G