import Lake
open System Lake DSL

package CompElliptic where
  version := v!"0.1.0"

-- Mathlib is pulled in transitively (and version-pinned) by CompPoly, so that the two
-- always agree on the toolchain and Mathlib revision.
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly.git" @ "84fc00c2f7f72d50231b8cf90586280e381ec313"

@[default_target]
lean_lib CompElliptic
