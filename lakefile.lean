import Lake
open Lake DSL

package «traat» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require aesop from git "https://github.com/JLimperg/aesop"

@[default_target]
lean_lib «Traat» {
  -- add any library configuration options here
}
