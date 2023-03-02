import FF.EllipticCurve
import LSpec

open LSpec

-- TODO : Add this (or a better instance) to the `Zmod` file
instance : ToString $ Zmod n where
  toString x := ToString.toString x.rep

section smalltest

abbrev SmallField := Zmod 0x65

def SmallCurve : Curve SmallField where
  a := 2
  b := 3

namespace SmallCurve

def G : ProjectivePoint SmallCurve := .mkD 52 74 1 

def P : ProjectivePoint SmallCurve := .mkD 98 24 1 

open ProjectivePoint 

def onCurveTests : TestSeq :=
  test "onCurve" (ProjectivePoint.onCurve SmallCurve G.X G.Y G.Z) $
  test "notOnCurve" (not $ ProjectivePoint.onCurve SmallCurve P.X (P.Y + 1) P.Z)

def pAddTests : TestSeq :=
  test "add 1" (G + G == ⟨79, 44, 1⟩) $
  test "add 2" (P + G == ⟨57, 50, 1⟩) $
  test "add 3" ((zero : ProjectivePoint SmallCurve) + zero == zero)

def pDoubleTests : TestSeq :=
  test "double 1" (G + G == .double G) $
  test "double 2" (P + P == .double P) $
  test "double 3" ((zero : ProjectivePoint SmallCurve) + zero == .double zero)

def pSMultests : TestSeq :=
  test "smul 0" (0 * G == zero) $
  test "smul 1" (1 * P == P) $
  test "smul 2" (2 * G == double G) $
  test "smul 2'" (2 * P == P + P) $
  test "smul 7" (7 * P == ⟨50, 41, 1⟩) $
  test "smul 97" (97 * P == P)

def fieldSMulTests : TestSeq :=
  test "scale 1" ((1 : SmallField) * P == P) $
  test "scale 2" ((19 : SmallField) * G == G)

-- TODO: re-use the above for the affine tests

end SmallCurve

end smalltest

section notsobigtest

abbrev MediumField := Zmod 0x6fe7b597

end notsobigtest

section bigtest

abbrev BigField := Zmod 0x4c4b2d1587029f7d01d6c6c399c235c544ef233215b42392c6e2838fb6cefd51

end bigtest

open SmallCurve

def main := lspecIO $ onCurveTests ++ pAddTests ++ pDoubleTests ++ pSMultests ++ fieldSMulTests
