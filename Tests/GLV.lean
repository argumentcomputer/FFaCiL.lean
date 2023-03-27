import FFaCiL.Pasta
import LSpec

open LSpec 

def testInputs : List Int := [
  -8, -1, 0, 1, 100, 1000, (-2)^256 - 1, 
  0x338fdec7c177777777777f0be5b0c0ffbbe33e969eb999999999999999d235ee,
  0x4280000000001871b497999999999999999999969e77777777771af301d235ee,
  0xe38fffffffffffffff999999999999999990000000000000000000000aaaaaaa
]

def Pallas.G : Point := .mkD 
0x3fe2f0feb60f920d4e7f06867da64339010388ac84b3395bfefc948e31fb1d4c 
0x338fdec7c16c1871b4973f0be5b0c0ffbbe32e969ebf106c73601af301d235ee
1

def Vesta.G : Point := .mkD
  0x2d3996e18f134bd93aec73c9b984dbf27074e544029e4ac122fb219fde2b20eb
  0x2afaa43f3c902b3d19adc0b90aa1e9a37d55c73d7753f722f34d456e530854f0
  1

open Pallas CurveGroup in
def pallasTests : TestSeq := 
  testInputs.foldl (init := .done) fun tSeq n =>
    tSeq ++ (test "Optimized Pallas matches unoptimized" $ n * G == instHMulInt.hMul n G)

open Vesta CurveGroup in
def vestaTests : TestSeq := 
  testInputs.foldl (init := .done) fun tSeq n =>
    tSeq ++ (test "Optimized Vesta matches unoptimized" $ n * G == instHMulInt.hMul n G)

def main := lspecIO $ pallasTests ++ vestaTests
