import Lake
open Lake DSL

package pcfAlephOmega4 where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib PcfProject where
