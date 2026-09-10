/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta.Fast.MsmProj.Core
import CompElliptic.Curves.Pasta.Fast.Projective

/-!
# The projective Pippenger MSM at the Pallas curve

The Pallas instantiation of the field-generic projective Pippenger core
(`Fast.MsmProj.Core`): the windowed multi-scalar multiplication run in projective coordinates
over the Pallas affine group `SWPoint Pallas.curve`, proven equal to the naive MSM. The curve
facts (`A = 0`, `B = 5`, no 2-torsion, `2 ≠ 0`) are supplied by `Fast.Projective.Pallas`. The
basic path, the single-pass-scatter path, and the windows-parallel path all delegate to the
core.

This is the fast MSM a recursion verifier's `2^k`-point IPA opening check uses on the Pallas
side — one field inversion for the whole sum instead of one per addition. The `commit_lagrange`
wrappers are Vesta-only (their coefficients live in `VestaScalarField`), so they are not mirrored
here.

The `Fast` interfaces are provisional: they are not guaranteed to remain public, and may be
folded into the existing API or otherwise changed incompatibly.
-/

open CompElliptic
open CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta
open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.Projective.Pallas

namespace CompElliptic.Curves.Pasta.Fast.MsmProjPallas

/-! ## The projective Pippenger MSM -/

/-- Pallas' windowed Pippenger MSM run in projective coordinates: the generic core
(`MsmProj.Core.pippengerProj`) at the Pallas curve. -/
abbrev pippengerProj : ℕ → List (ℕ × G) → G := MsmProj.Core.pippengerProj Pallas.curve hA hB

theorem pippengerProj_eq (c : ℕ) (terms : List (ℕ × G)) :
    pippengerProj c terms = Msm.pippenger c terms :=
  MsmProj.Core.pippengerProj_eq Pallas.curve hA hB hy0 htwo c terms

/-- **Pallas' projective Pippenger equals the naive MSM** (`c ≥ 1`): the whole multi-scalar
multiplication runs in projective coordinates, one inversion at the end, and computes
`∑ᵢ aᵢ • gᵢ`. -/
theorem pippengerProj_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × G)) :
    pippengerProj c terms = (terms.map fun t => t.1 • t.2).sum :=
  MsmProj.Core.pippengerProj_eq_msm Pallas.curve hA hB hy0 htwo c hc terms

/-! ## Single-pass Array bucketing -/

/-- One projective scatter step (Pallas instance of `Core.pscatterStep`). -/
abbrev pscatterStep : Array PPal → ℕ × PPal → Array PPal := MsmProj.Core.pscatterStep (F := Fp)

/-- Scatter into `base − 1` buckets in one pass (Pallas instance of `Core.pbucketScatter`). -/
abbrev pbucketScatter : ℕ → List (ℕ × PPal) → Array PPal := MsmProj.Core.pbucketScatter (F := Fp)

theorem pbucketScatter_spec (base : ℕ) (dp : List (ℕ × PPal)) (hdp : ∀ p ∈ dp, Valid p.2) :
    (∀ P ∈ (pbucketScatter base dp).toList, Valid P)
      ∧ (pbucketScatter base dp).toList.map toAffine
        = (List.range (base - 1)).map fun k =>
            Msm.bucketOf (dp.map fun t => (t.1, toAffine t.2)) (k + 1) :=
  MsmProj.Core.pbucketScatter_spec Pallas.curve hA hB hy0 htwo base dp hdp

/-- The scatter-bucketed projective window value (Pallas instance of `Core.pwindowValueFast`). -/
abbrev pwindowValueFast : ℕ → ℕ → List (ℕ × PPal) → PPal :=
  MsmProj.Core.pwindowValueFast (F := Fp)

theorem pwindowValueFast_spec (base i : ℕ) (pterms : List (ℕ × PPal))
    (h : ∀ p ∈ pterms, Valid p.2) :
    Valid (pwindowValueFast base i pterms)
      ∧ toAffine (pwindowValueFast base i pterms)
        = Msm.windowValue base i (pterms.map fun t => (t.1, toAffine t.2)) :=
  MsmProj.Core.pwindowValueFast_spec Pallas.curve hA hB hy0 htwo base i pterms h

/-! ## The scatter-bucketed projective Pippenger MSM -/

/-- **Scatter-bucketed projective Pippenger** (Pallas instance of `Core.pippengerProjScatter`). -/
abbrev pippengerProjScatter : ℕ → List (ℕ × G) → G :=
  MsmProj.Core.pippengerProjScatter Pallas.curve hA hB

theorem pippengerProjScatter_eq (c : ℕ) (terms : List (ℕ × G)) :
    pippengerProjScatter c terms = Msm.pippenger c terms :=
  MsmProj.Core.pippengerProjScatter_eq Pallas.curve hA hB hy0 htwo c terms

theorem pippengerProjScatter_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × G)) :
    pippengerProjScatter c terms = (terms.map fun t => t.1 • t.2).sum :=
  MsmProj.Core.pippengerProjScatter_eq_msm Pallas.curve hA hB hy0 htwo c hc terms

/-! ## Windows-parallel projective Pippenger -/

/-- **Windows-parallel scatter-bucketed projective Pippenger** (Pallas instance of
`Core.pippengerProjScatterPar`). -/
abbrev pippengerProjScatterPar : ℕ → List (ℕ × G) → G :=
  MsmProj.Core.pippengerProjScatterPar Pallas.curve hA hB

theorem pippengerProjScatterPar_eq (c : ℕ) (terms : List (ℕ × G)) :
    pippengerProjScatterPar c terms = pippengerProjScatter c terms :=
  MsmProj.Core.pippengerProjScatterPar_eq Pallas.curve hA hB c terms

theorem pippengerProjScatterPar_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × G)) :
    pippengerProjScatterPar c terms = (terms.map fun t => t.1 • t.2).sum :=
  MsmProj.Core.pippengerProjScatterPar_eq_msm Pallas.curve hA hB hy0 htwo c hc terms

end CompElliptic.Curves.Pasta.Fast.MsmProjPallas
