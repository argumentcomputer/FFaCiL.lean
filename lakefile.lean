import Lake
open Lake DSL

package FF

@[default_target]
lean_lib FF

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "533d71efa5853ff014f42c174d6321d74251209f"
