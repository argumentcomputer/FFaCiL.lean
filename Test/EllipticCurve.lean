import FF.EllipticCurves
import LSpec

-- TODO : Add SAGE calculations

section smalltest

new_field TestField with
  prime: 101
  generator: 2

structure TestCurve where

end smalltest

section bigtest

structure BLS12381 where

instance [PrimeField F] : Curve BLS12381 F where
  a := 0
  b := (4 : Nat)
  order := 0x923480928340981
  cofactor := sorry
  characteristic := sorry

end bigtest

section notsobigtest

new_field Test101 with
  prime: 101
  generator: 1   

structure Kitten where

instance cur : Curve Kitten Test101 where
  a := 2
  b := 3
  order := 96
  cofactor := sorry
  characteristic := sorry

instance : CurvePoint Kitten (AffinePoint Test101) where
  zero := aff.zero
  inv := aff.inv
  add := aff.add
  toPoint := aff.toPoint
  frobenius := aff.frobenius

def p₁ : AffinePoint Test101 := ⟨ 23, 57, false ⟩
def p₂ : AffinePoint Test101 := ⟨ 31, 74, false ⟩

#eval @smul Test101 Kitten (AffinePoint Test101) _ _ _ (5 : Nat) p₁

end notsobigtest