import Lake
open Lake DSL

package FFaCiL

@[default_target]
lean_lib FFaCiL

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "78b02f02367cdf3bfa1b65c0efbd40e56a47588b"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

lean_exe Tests.EllipticCurve