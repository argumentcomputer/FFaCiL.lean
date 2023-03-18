import Lake
open Lake DSL

package FF

@[default_target]
lean_lib FF

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "e1e1c681e0a97176ae9e73ac5b0257fdd9b07ca4"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"
  
require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

lean_exe Tests.EllipticCurve
lean_exe Tests.GLV

lean_exe Benchmarks.GLV