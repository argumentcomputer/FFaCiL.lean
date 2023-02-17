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