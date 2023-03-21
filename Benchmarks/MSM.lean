import FFaCiL.MSM
import FFaCiL.Pasta
import YatimaStdLib.Benchmark

open Benchmark Better

instance : FixedSize (Array $ Nat × Pallas.Point) where
  random size := do
    let mut answer := #[] 
    let g ← get
    let mut g := g.down
    let mut n := 0
    let mut p := .infinity
    for _ in [:size] do
      (n, g) := randNat g 0 Vesta.q
      (p, g) := Random.random g
      answer := answer.push (n, p)

    return answer
  size ps := ps.size

def exampel := @FixedSize.random (Array $ Nat × Pallas.Point) _ (2^9) (mkStdGen 15 |> ULift.up) |> Prod.fst

-- #eval exampel

-- #eval generateInstances exampel |>.map fun m => m.evaluate

def f : Array (Nat × Pallas.Point) → Pallas.Point :=
  fun x => naiveMSM x 

def g : Array (Nat × Pallas.Point) → Pallas.Point :=
  fun x =>
    let instances := generateInstances x
    let answers := instances.map fun inst => inst.evaluate
    answers.foldl (init := .zero) fun acc P => acc + P

instance {α : Type _} : Ord $ Array α where
  compare as bs := compare as.size bs.size

def naiveBench : RandomComparison f g where
  inputSizes := #[2^13]

def main (args : List String) : IO UInt32 := do
  -- let answer := splitMSM exampel |>.get! 7 |>.fst |>.get! 0 
  -- IO.println answer
  -- return 0
benchMain args naiveBench.benchmark

