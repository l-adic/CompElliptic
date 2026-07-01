import Lake
open System Lake DSL

package CompElliptic where
  version := v!"0.1.0"

-- Mathlib is pulled in transitively (and version-pinned) by CompPoly, so that the two
-- always agree on the toolchain and Mathlib revision.
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly.git" @ "18c1613e9186c7afa79a4179eea5f4b80d8e9e00"

@[default_target]
lean_lib CompElliptic
