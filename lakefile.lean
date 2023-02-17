import Lake
open Lake DSL

package FF

@[default_target]
lean_lib FF

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "d8febaaef9a7cc28c1bb0e651ae337f09da9061a"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"