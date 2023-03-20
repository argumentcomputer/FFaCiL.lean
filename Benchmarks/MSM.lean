import FFaCiL.MSM
import FFaCiL.Pasta
import YatimaStdLib.Benchmark

open Benchmark

instance : FixedSize (Array $ Pallas.Point × Nat) where
  random size := do
    let mut answer := #[] 
    let g ← get
    let mut g := g.down
    let mut n := 0
    let mut p := .infinity
    for _ in [:size] do
      (n, g) := randNat g 0 Vesta.q
      (p, g) := Random.random g
      answer := answer.push (p, n)

    return answer
  size ps := ps.size

def f : Array (Pallas.Point × Nat) → Pallas.Point :=
  fun x => naiveMSM x.toList

def naiveBench : FunctionAsymptotics f where
  inputSizes := #[1, 2, 4, 8, 16, 32, 64, 128]

def main (args : List String) := benchMain args naiveBench.benchmark

