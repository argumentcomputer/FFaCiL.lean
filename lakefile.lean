import Lake
open Lake DSL

package FFaCiL

@[default_target]
lean_lib FFaCiL

require LightData from git
  "https://github.com/lurk-lab/LightData" @ "7492abeae41f3a469396c73e13f48cd2b8da4a02" 

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "df30d88d06e22d7c418fb8eee2996dd44cd1c547"

require LSpec from git
  "https://github.com/lurk-lab/LSpec" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

lean_exe Tests.EllipticCurve
lean_exe Tests.GLV
lean_exe Tests.MSM

lean_exe Benchmarks.GLV
lean_exe Benchmarks.MSM
