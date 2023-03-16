import Lake
open Lake DSL

package FFaCiL

@[default_target]
lean_lib FFaCiL

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "f616da79a3ffe29d1a04b956ed36ebfdc6e82a7f"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

lean_exe Tests.EllipticCurve