import Lake
open Lake DSL

package FFaCiL

@[default_target]
lean_lib FFaCiL

require LightData from git
  "https://github.com/yatima-inc/LightData" @ "7492abeae41f3a469396c73e13f48cd2b8da4a02" 

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "78b02f02367cdf3bfa1b65c0efbd40e56a47588b"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"
  
require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

lean_exe Tests.EllipticCurve
lean_exe Tests.GLV

lean_exe Benchmarks.GLV