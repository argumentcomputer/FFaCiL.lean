import FF.EllipticCurve
import FF.NewField
import FF.Util

private def twoMSM [Field F] {C : Curve F} (P Q : ProjectivePoint C) (k₁ k₂ : Int) : ProjectivePoint C :=
  let task₁ := Task.spawn fun _ => k₁ * P
  let task₂ := Task.spawn fun _ => k₂ * Q
  task₁.get + task₂.get

def Pallas.p : Nat := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001 

def Vesta.q : Nat := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001 

namespace Pallas

abbrev F := Zmod p 

def Curve : Curve F := {a := 0, b := 5}

abbrev Point := ProjectivePoint Curve

-- TODO : Delete this, this is some random test thing (or is it??)
def G : Point := ProjectivePoint.mkD 
0x3fe2f0feb60f920d4e7f06867da64339010388ac84b3395bfefc948e31fb1d4c 
0x338fdec7c16c1871b4973f0be5b0c0ffbbe32e969ebf106c73601af301d235ee
1

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

def getPair (k : Int) : Int × Int := 
  let vec := m.twoInv.action #[k, 0] 
  let vec' : Vector Int := vec[0]!.round * v₁ + vec[1]!.round * v₂
  (k - vec'[0]!, -vec'[1]!)

def checkGetPair (k : Int) : Bool :=
  let (k₁, k₂) := getPair k
  dbg_trace Vesta.q
  dbg_trace (k₁, k₂)
  (k₁ + Λ * k₂) % Vesta.q == k % Vesta.q

instance(priority := high) : HMul Nat Point Point where
  hMul n P := 
    let (k₁, k₂) := getPair n
    twoMSM P (Φ P) k₁ k₂

end Pallas

namespace Vesta

abbrev F := Zmod q

def Curve : Curve F := {a := 0, b:= 5}

abbrev Point := ProjectivePoint Curve

end Vesta


