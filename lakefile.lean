import Lake
open System Lake DSL

package CompElliptic where
  version := v!"0.1.0"

require CompPoly from git
  "https://github.com/l-adic/CompPoly.git" @ "codex/lean-4.31-cleanup"

require "leanprover-community" / mathlib @ git "v4.31.0"

post_update _pkg do
  let rootPkg ← getRootPackage
  let file := rootPkg.dir / ".lake" / "packages" / "CompPoly" / "CompPoly" / "Fields" / "PrattCertificate.lean"
  if !(← file.pathExists) then
    return
  let content ← IO.FS.readFile file
  let old := "    convert h'\n    replace hn := of_decide_eq_true hn\n    exact (Nat.mod_eq_of_lt hn).symm"
  let new := "    replace hn := of_decide_eq_true hn\n    rw [Nat.mod_eq_of_lt hn] at h'\n    exact h'"
  if content.contains old then
    IO.FS.writeFile file (content.replace old new)

@[default_target]
lean_lib CompElliptic
