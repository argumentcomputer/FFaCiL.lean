import Lake
open Lake DSL

package FF

@[default_target]
lean_lib FF

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "515b7eff7765dcf55ce275ac41fa13a30a59f1d0"