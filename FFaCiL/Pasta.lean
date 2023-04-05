import FFaCiL.PrimeField
import FFaCiL.EllipticCurve
import YatimaStdLib.Rat
import YatimaStdLib.Matrix

/-!
# Pasta Curves

In this module we define the Pasta curves, and implement the GLV optimization for their scalar
multiplication.
-/
private def getPair (k : Int) (transform : Matrix Rat) (v₁ v₂ : Vector Int) : Int × Int := 
  let vec := transform.twoInv.action #[k, 0] 
  let vec' : Vector Int := vec[0]!.round * v₁ + vec[1]!.round * v₂
  (k - vec'[0]!, -vec'[1]!)

private def twoMSM [Field F] {C : Curve F} (P Q : ProjectivePoint C) (k₁ k₂ : Int) 
    : ProjectivePoint C :=
  let task₁ := Task.spawn fun _ => k₁ * P
  let task₂ := Task.spawn fun _ => k₂ * Q
  task₁.get + task₂.get

/--
The order of the Pallas base field.
-/
def Pallas.p : Nat := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001 

/--
The order of the Vesta base field.
-/
def Vesta.q : Nat := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001 

namespace Pallas

/--
The base field for the Pallas curve
-/
abbrev F := Zmod p 

/--
The Pasta curve has Weierstrass form `y² = x³ + 5` defined over `Zmod Pallas.p`
-/
def Curve : Curve F := {a := 0, b := 5}

abbrev Point := ProjectivePoint Curve

/-- A choice of primitive cube root of unity in `Pallas.F` -/
def ζ : F := 0x2d33357cb532458ed3552a23a8554e5005270d29d19fc7d27b7fd22f0201b547

/-- An efficiently computable endomorphism of Pallas used for the GLV optimization -/
def Φ : Point → Point
  | ⟨x, y, z⟩ => ⟨ζ * x, y, z⟩

/-- The scalar corresponding to the endomorphism `Φ` -/
def Λ : Int := 0x397e65a7d7c1ad71aee24b27e308f0a61259527ec1d4752e619d1840af55f1b1

/-- 
Together with `v₂`, two linearly independent vectors that span the kernel of
`(k₁, k₂) ↦ k₁ + Λ k₂ (mod Vesta.q)`
-/
def v₁ : Vector Int := #[0x93cd3a2c8198e2690c7c095a00000001, 0x49e69d1640a899538cb1279300000000]

/-- 
Together with `v₁`, two linearly independent vectors that span the kernel of
`(k₁, k₂) ↦ k₁ + Λ k₂ (mod Vesta.q)`
-/
def v₂ : Vector Int := #[0x49e69d1640a899538cb1279300000000, -0x49e69d1640f049157fcae1c700000001]

def m : Matrix Rat := #[v₁, v₂]

instance(priority := high) : HMul Nat Point Point where
  hMul n P := 
    let (k₁, k₂) := getPair n m v₁ v₂
    twoMSM P (Φ P) k₁ k₂

end Pallas

namespace Vesta

/--
The base field for the Vesta curve
-/
abbrev F := Zmod q

/--
The Vesta curve has Weierstrass form `y² = x³ + 5` defined over `Zmod Vesta.q`
-/
def Curve : Curve F := {a := 0, b:= 5}

abbrev Point := ProjectivePoint Curve

/-- A choice of primitive cube root of unity in `Vesta.F` -/
def ζ : F := 0x397e65a7d7c1ad71aee24b27e308f0a61259527ec1d4752e619d1840af55f1b1

/-- An efficiently computable endomorphism of Pallas used for the GLV optimization -/
def Φ : Point → Point
  | ⟨x, y, z⟩ => ⟨ζ * x, y, z⟩

/-- The scalar corresponding to the endomorphism `Φ` -/
def Λ : Int := 0x2d33357cb532458ed3552a23a8554e5005270d29d19fc7d27b7fd22f0201b547

/-- 
Together with `v₂`, two linearly independent vectors that span the kernel of
`(k₁, k₂) ↦ k₁ + Λ k₂ (mod Pallas.p)`
-/
def v₁ : Vector Int := #[0xddb3d742c2417bbc992d30ed00000002, -0x47afc1f319ba33ffffffff]

/-- 
Together with `v₁`, two linearly independent vectors that span the kernel of
`(k₁, k₂) ↦ k₁ + Λ k₂ (mod Pallas.p)`
-/
def v₂ : Vector Int := #[0x93cd3a2c8198e2690c7c095a00000001, 0x49e69d1640a899538cb1279300000001]

def m : Matrix Rat := #[v₁, v₂]

instance(priority := high) : HMul Nat Point Point where
  hMul n P := 
    let (k₁, k₂) := getPair n m v₁ v₂
    twoMSM P (Φ P) k₁ k₂

end Vesta
