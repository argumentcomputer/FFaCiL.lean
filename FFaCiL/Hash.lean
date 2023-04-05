import FFaCiL.EllipticCurve
import FFaCiL.PrimeField

/-!
# Shallue-van de Woestijne method

Shallue-van de Woestijne method is an algorithm allowing representing
an elliptic curve point (of Weierstrass form) as an element of the 
underlying scalar field.

See https://eprint.iacr.org/2022/759.pdf.
-/

variable {F : Type _} [PrimeField F] (C : Curve F)

open PrimeField (isSquare) in 
/--
Find a Z for Shallue-van de Woestijne method.

https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-10.html#section-h.1
-/
private def findZ : F := Id.run do
  let g := fun x => x^3 + C.a * x + C.b
  let h := fun z => - ((3 : Nat) * z^2 + (4 : Nat) * C.a) / ((4 : Nat) * g z)
  let mut ctr : F := 1
    while true do
      for Z_cand in [ctr, -ctr] do
        if g Z_cand == 0 then 
          continue
        else if h Z_cand == 0 then 
          continue
        else if not $ isSquare (h Z_cand) then 
          continue
        else if isSquare (g Z_cand) || isSquare (g (-Z_cand / (2 : Nat))) then
          return Z_cand
      ctr := ctr + 1
  return ctr

open Field (inv) in
open PrimeField (sqrt natRepr) in
/--
Shallue-van de Woestijne method.

Based on https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-10.html#straightline-svdw
-/
def genPoint (u : F) : AffinePoint C := Id.run do
  let g := fun x => x^3 + C.a * x + C.b
  let z : F := findZ C
  let c₁ := g z
  let c₂ := -z / (2 : Nat)
  let c₃ := Option.getD (sqrt (- g z * ((3 : Nat) * z^2 + (4 : Nat) * C.a))) 0
  let c₄ := - (4 : Nat) * g z / ((3 : Nat) * z^2 + (4 : Nat) * C.a)
  let mut tv₁ := u^2
  tv₁ := tv₁ * c₁
  let mut tv₂ := 1 + tv₁
  tv₁ := 1 - tv₁
  let mut tv₃ := tv₁ * tv₂
  tv₃ := inv tv₃
  let mut tv₄ := u * tv₁
  tv₄ := tv₄ * tv₃
  tv₄ := tv₄ * c₃
  let x₁ := c₂ - tv₄
  let mut gx₁ := x₁^2
  gx₁ := gx₁ + C.a
  gx₁ := gx₁ * x₁
  gx₁ := gx₁ + C.b
  let e₁ := match sqrt gx₁ with
    | some _ => true
    | _    => false
  let x₂ := c₂ + tv₄
  let mut gx₂ := x₂^2
  gx₂ := gx₂ + C.a
  gx₂ := gx₂ * x₂
  gx₂ := gx₂ + C.b
  let e₂ :=
    let e' := match sqrt gx₂ with
      | some _ => true
      | _      => false
    e' && not e₁
  let mut x₃ := tv₂^2
  x₃ := x₃ * tv₃
  x₃ := x₃^2
  x₃ := x₃ * c₄
  x₃ := x₃ + z
  let mut x :=
    if e₁ then x₁ else x₃
  x := if e₂ then x₂ else x
  let mut gx := x^2
  gx := gx + C.a
  gx := gx * x
  gx := gx + C.b
  let mut y := Option.getD (sqrt gx) 0
  let e₃ := Nat.mod (natRepr u) 2 == Nat.mod (natRepr y) 2
  y := if e₃ then y else -y
  return .affine x y
