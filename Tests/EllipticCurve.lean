import FFaCiL.EllipticCurve
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

def pOnCurveTests : TestSeq :=
  test "projective: onCurve" (ProjectivePoint.onCurve SmallCurve G.X G.Y G.Z) $
  test "projective: notOnCurve" (not $ ProjectivePoint.onCurve SmallCurve P.X (P.Y + 1) P.Z)

def pAddTests : TestSeq :=
  test "projective: add 1" (G + G == ⟨79, 44, 1⟩) $
  test "projective: add 2" (P + G == ⟨57, 50, 1⟩) $
  test "projective: add 3" ((zero : ProjectivePoint SmallCurve) + zero == zero) $
  test "projective: add 4" (G + zero == G) $
  test "projective: add 5" (zero + P == P)

def pDoubleTests : TestSeq :=
  test "projective: double 1" (G + G == .double G) $
  test "projective: double 2" (P + P == .double P) $
  test "projective: double 3" ((zero : ProjectivePoint SmallCurve) + zero == .double zero)

def pSMultests : TestSeq :=
  test "projective: smul 0" (0 * G == zero) $
  test "projective: smul 1" (1 * P == P) $
  test "projective: smul 2" (2 * G == double G) $
  test "projective: smul 2'" (2 * P == P + P) $
  test "projective: smul 7" (7 * P == ⟨50, 41, 1⟩) $
  test "projective: smul 97" (97 * P == P)

def pFieldSMulTests : TestSeq :=
  test "projective: scale 1" ((1 : SmallField) * P == P) $
  test "projective: scale 2" ((19 : SmallField) * G == G)

end SmallCurve

namespace AffineCase

def G : AffinePoint SmallCurve := .affine 52 74

def P : AffinePoint SmallCurve := .affine 98 24

open AffinePoint

def aOnCurveTests : TestSeq :=
  test "affine: onCurve" (AffinePoint.fieldEltsOnCurve SmallCurve 52 74) $
  test "affine: notOnCurve" (not $ AffinePoint.fieldEltsOnCurve SmallCurve 98 25)

def aAddTests : TestSeq :=
  test "affine: add 1" (G + G == .affine 79 44) $
  test "affine: add 2" (P + G == .affine 57 50) $
  test "affine: add 3" ((zero : AffinePoint SmallCurve) + AffinePoint.infinity == AffinePoint.infinity) $
  test "affine: add 4" (G + infinity == G) $
  test "affine: add 5" (infinity + G == G)

def aDoubleTests : TestSeq :=
  test "affine: double 1" (G + G == .double G) $
  test "affine: double 2" (P + P == .double P) $
  test "affine: double 3" ((zero : AffinePoint SmallCurve) + zero == .double zero)

def aSMultests : TestSeq :=
  test "affine: smul 0" (0 * G == zero) $
  test "affine: smul 1" (1 * P == P) $
  test "affine: smul 2" (2 * G == double G) $
  test "affine: smul 2'" (2 * P == P + P) $
  test "affine: smul 7" (7 * P == .affine 50 41) $
  test "affine: smul 97" (97 * P == P)

end AffineCase
end smalltest

open SmallCurve
open AffineCase

def main := lspecIO $
  pOnCurveTests ++ pAddTests ++ pDoubleTests ++ pSMultests ++ pFieldSMulTests ++
  aOnCurveTests ++ aAddTests ++ aDoubleTests ++ aSMultests
