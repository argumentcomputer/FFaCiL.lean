import LSpec
import FFaCiL.MSM
import FFaCiL.PrimeField

open LSpec

new_field TestField with
  prime: 2011
  generator: 7

def TestCurve : Curve TestField := {a := 0, b := 5}

def testInstance := Array.iota 1983 |>.zip TestCurve.points

def msmTest : TestSeq := test "Naive matches Pippenger" $ 
  (naiveMSM testInstance == pippengerMSM testInstance)

def main : IO UInt32 := lspecIO msmTest