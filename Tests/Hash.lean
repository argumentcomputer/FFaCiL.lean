import FFaCiL.EllipticCurve
import FFaCiL.Hash
import FFaCiL.Pasta

import LSpec

open LSpec

section TestingInstances

/- 
In this section we define the necessary `SlimCheck` instances to define tests for field elements

Note: It may be worth putting this into YSL, so it can be used elsewhere
-/

open SlimCheck

instance : Shrinkable (Zmod p) where
  shrink a := 
    let aNat := PrimeField.natRepr a
    let shrunkA := Shrinkable.shrink aNat
    shrunkA.map PrimeField.fromNat

def zModGen : Gen (Zmod p) := return ← Gen.chooseAny Nat

/--
Generate a random smooth elliptic curve

Note: Note actually used in the below tests, but could be plugged in later
-/
def curveGen : Gen $ Curve (Zmod p) := do
  let mut actualC := ⟨0, 1⟩
  while true do 
    let candidateC : Curve (Zmod p) :=  {
      a := ← Gen.chooseAny Nat
      b := ← Gen.chooseAny Nat
    }
    if candidateC.discriminant != 0 then
      actualC := candidateC
      break
    else
      continue
  return actualC

instance : SampleableExt (Zmod p) := .mkSelfContained zModGen

end TestingInstances

section Tests

def swmTestPallas := check "SWM works on Pallas" $ ∀ (x : Pallas.F), genPoint Pallas.Curve x |>.onCurve

def swmTestVesta := check "SWM works on Vesta" $ ∀ (x : Vesta.F), genPoint Vesta.Curve x |>.onCurve

def main := lspecIO $ swmTestPallas ++ swmTestVesta

end Tests
