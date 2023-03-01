import FF.EllipticCurve
import LSpec

-- TODO : Add this (or a better instance) to the `Zmod` file
instance : ToString $ Zmod n where
  toString x := ToString.toString x.rep

section smalltest

abbrev SmallField := Zmod 0x65

def SmallCurve : Curve SmallField where
  a := 2
  b := 3

namespace SmallCurve

def G : ProjectivePoint SmallCurve := ⟨52, 74, 1⟩ -- TODO: Validate these

def P : ProjectivePoint SmallCurve := ⟨98, 24, 1⟩ -- Validate these
#eval G + G == ⟨79, 44, 1⟩

#eval 0 * G -- This is right

#eval 1 * G -- not G

#eval 2 * G == ⟨79, 44, 1⟩

#eval 7 * P == ⟨50, 41, 1⟩

#eval 96 * P == P -- Should be P

#eval P + G == ⟨57, 50, 1⟩

#eval (19 : SmallField) * G

#eval (19 : SmallField) * G == G

-- TODO: re-use the above for the affine tests

end SmallCurve

end smalltest

section notsobigtest

abbrev MediumField := Zmod 0x6fe7b597

end notsobigtest

section bigtest

abbrev BigField := Zmod 0x4c4b2d1587029f7d01d6c6c399c235c544ef233215b42392c6e2838fb6cefd51

end bigtest

def main := IO.println "hi'"