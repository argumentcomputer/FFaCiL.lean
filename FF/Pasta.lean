import FF.EllipticCurve
import FF.NewField
import YatimaStdLib.Matrix
import Std.Data.Rat.Basic

namespace Pallas

abbrev F := Zmod 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

instance : ToString F where
  toString := reprStr

def Curve : Curve F := {a := 0, b := 5}

abbrev Point := ProjectivePoint Curve

end Pallas

namespace Vesta

abbrev F := Zmod 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

#check hexDigitRepr


def Curve : Curve F := {a := 0, b:= 5}

abbrev Point := ProjectivePoint Curve

instance(priority := high) : HMul Nat Point Point where
  hMul foo bar := 
    dbg_trace "noooo"
    ⟨0, 0, 0⟩

end Vesta

-- #eval 5 * (⟨1, 2, 3⟩ : Vesta.Point)

def G : Pallas.Point := ProjectivePoint.mkD 
28896680183508622939825607448046027482759649890292397923555082389158610279756 
23322151981098009229640914949988019390245012628977873075130252157080438978030
1

def ζ : Pallas.F :=  
20444556541222657078399132219657928148671392403212669005631716460534733845831

def G' : Pallas.Point := 
  let ⟨x, y, z⟩ := G
  ProjectivePoint.mkD (ζ * x) y z

#eval G' == 26005156700822196841419187675678338661165322343552424574062261873906994770353 * G

private def matrix2x2.inv [Field R] (M : Matrix R) : Matrix R :=
  let det := M[0]![0]! * M[1]![1]! - M[0]![1]! * M[1]![0]!
  (Field.inv det) * #[#[M[1]![1]!, -M[0]![1]!], #[-M[1]![0]!, M[0]![0]!]]

instance : Field Rat where
  hPow r n := 0
  coe a := 0
  zero := 0
  one := 1
  inv x := 1/x
  sqrt x := .none

#eval matrix2x2.inv (#[#[1,2],#[3,7]] : Matrix Rat) |>.mul (#[#[1,2],#[3,7]] : Matrix Rat)
#check Rat
