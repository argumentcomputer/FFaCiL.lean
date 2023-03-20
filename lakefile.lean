import Lake
open Lake DSL

package FFaCiL

@[default_target]
lean_lib FFaCiL

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "df30d88d06e22d7c418fb8eee2996dd44cd1c547"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

lean_exe Tests.EllipticCurve