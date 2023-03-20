import FFaCiL.EllipticCurve

def naiveMSM {F : Type _} [PrimeField F] {C : Curve F} (params : List $ (ProjectivePoint C) × Nat)
    : ProjectivePoint C :=
  params.foldl (init := .infinity) fun acc (p, n) => acc + n * p

