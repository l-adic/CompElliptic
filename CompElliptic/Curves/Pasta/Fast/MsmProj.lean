/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta.Fast.Msm
import CompElliptic.Curves.Pasta.Fast.Projective
import CompElliptic.Curves.Pasta.Fast.MsmProj.Core

/-!
# The windowed Pippenger MSM run entirely in projective coordinates (Vesta)

The Vesta instantiation of the field-generic `MsmProj.Core`: `PVes`/`Projective.G` at
`Vesta.curve`, with the basic, single-pass-scatter, and windows-parallel projective Pippenger
paths delegating to the core (fed Vesta's `no_onCurve_y_zero`/`2 ≠ 0` facts). Every group addition
of `Msm.lean` at the affine group pays a field inversion; this runs the whole interior over `PVes`
with `padd`/`pnsmulFast`, one inversion per MSM.

The `commit_lagrange` wrappers stay here: their coefficients live in `Msm.Fp = VestaScalarField`,
so they are Vesta-specific; they delegate to the (now core-backed) `pippengerProj` /
`pippengerProjScatter`.

The `Fast` interfaces are provisional: they are not guaranteed to remain public, and may be folded
into the existing API or otherwise changed incompatibly.
-/

open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.Msm (Fp)
open CompElliptic.Curves.Pasta.Fast.Projective
open CompElliptic.Curves.Pasta.Fast.Projective.PVes
open CompElliptic
open CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta

namespace CompElliptic.Curves.Pasta.Fast.MsmProj

/-- The Vesta affine group carries a default point (the `Fast.Msm` wrapper section fixes
`[Inhabited G]`). -/
local instance : Inhabited Projective.G := ⟨0⟩

/-! ## Basic path — the Vesta instantiation of `MsmProj.Core` -/

/-- The `padd`-fold sum of a list of projective points (Vesta instance of `Core.psum`). -/
abbrev psum : List PVes → PVes := Core.psum (F := Fq)

theorem psum_cons (a : PVes) (xs : List PVes) : psum (a :: xs) = padd a (psum xs) :=
  Core.psum_cons (F := Fq) a xs

theorem psum_spec (L : List PVes) (h : ∀ P ∈ L, Valid P) :
    Valid (psum L) ∧ toAffine (psum L) = (L.map toAffine).sum :=
  Core.psum_spec Vesta.curve hA hB hy0 htwo L h

/-- The projective bucket-`b` sum (Vesta instance of `Core.pbucketOf`). -/
abbrev pbucketOf : List (ℕ × PVes) → ℕ → PVes := Core.pbucketOf (F := Fq)

theorem pbucketOf_spec (dp : List (ℕ × PVes)) (b : ℕ) (h : ∀ p ∈ dp, Valid p.2) :
    Valid (pbucketOf dp b)
      ∧ toAffine (pbucketOf dp b) = Msm.bucketOf (dp.map fun t => (t.1, toAffine t.2)) b :=
  Core.pbucketOf_spec Vesta.curve hA hB hy0 htwo dp b h

/-- One step of the projective suffix-sum accumulator (Vesta instance of `Core.paccStep`). -/
abbrev paccStep : PVes → PVes × PVes → PVes × PVes := Core.paccStep (F := Fq)

theorem foldr_paccStep_spec (L : List PVes) (h : ∀ P ∈ L, Valid P) :
    Valid (L.foldr paccStep (pid, pid)).1 ∧ Valid (L.foldr paccStep (pid, pid)).2
      ∧ (toAffine (L.foldr paccStep (pid, pid)).1, toAffine (L.foldr paccStep (pid, pid)).2)
        = List.foldr Msm.accStep ((0 : Projective.G), (0 : Projective.G)) (L.map toAffine) :=
  Core.foldr_paccStep_spec Vesta.curve hA hB hy0 htwo L h

/-- The digit-tagged projective term list for window `i` (Vesta instance of `Core.pdpOf`). -/
abbrev pdpOf : ℕ → ℕ → List (ℕ × PVes) → List (ℕ × PVes) := Core.pdpOf (F := Fq)

/-- The projective window value (Vesta instance of `Core.pwindowValue`). -/
abbrev pwindowValue : ℕ → ℕ → List (ℕ × PVes) → PVes := Core.pwindowValue (F := Fq)

theorem pwindowValue_spec (base i : ℕ) (pterms : List (ℕ × PVes)) (h : ∀ p ∈ pterms, Valid p.2) :
    Valid (pwindowValue base i pterms)
      ∧ toAffine (pwindowValue base i pterms)
        = Msm.windowValue base i (pterms.map fun t => (t.1, toAffine t.2)) :=
  Core.pwindowValue_spec Vesta.curve hA hB hy0 htwo base i pterms h

/-- Horner across windows in projective coordinates (Vesta instance of `Core.phornerList`). -/
abbrev phornerList : ℕ → List PVes → PVes := Core.phornerList (F := Fq)

theorem phornerList_spec (base : ℕ) (vals : List PVes) (h : ∀ P ∈ vals, Valid P) :
    Valid (phornerList base vals)
      ∧ toAffine (phornerList base vals) = Msm.hornerList base (vals.map toAffine) :=
  Core.phornerList_spec Vesta.curve hA hB hy0 htwo base vals h

/-! ## The projective Pippenger MSM -/

/-- **Windowed Pippenger MSM run in projective coordinates** (Vesta instance of
`Core.pippengerProj`): one field inversion per MSM instead of one per add. -/
abbrev pippengerProj : ℕ → List (ℕ × Projective.G) → Projective.G :=
  Core.pippengerProj Vesta.curve hA hB

theorem pippengerProj_eq (c : ℕ) (terms : List (ℕ × Projective.G)) :
    pippengerProj c terms = Msm.pippenger c terms :=
  Core.pippengerProj_eq Vesta.curve hA hB hy0 htwo c terms

/-- **The projective Pippenger equals the naive MSM.** -/
theorem pippengerProj_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × Projective.G)) :
    pippengerProj c terms = (terms.map fun t => t.1 • t.2).sum :=
  Core.pippengerProj_eq_msm Vesta.curve hA hB hy0 htwo c hc terms

/-! ## Single-pass Array bucketing -/

/-- One projective scatter step (Vesta instance of `Core.pscatterStep`). -/
abbrev pscatterStep : Array PVes → ℕ × PVes → Array PVes := Core.pscatterStep (F := Fq)

/-- Scatter into `base − 1` buckets in one pass (Vesta instance of `Core.pbucketScatter`). -/
abbrev pbucketScatter : ℕ → List (ℕ × PVes) → Array PVes := Core.pbucketScatter (F := Fq)

theorem pbucketScatter_spec (base : ℕ) (dp : List (ℕ × PVes)) (hdp : ∀ p ∈ dp, Valid p.2) :
    (∀ P ∈ (pbucketScatter base dp).toList, Valid P)
      ∧ (pbucketScatter base dp).toList.map toAffine
        = (List.range (base - 1)).map fun k =>
            Msm.bucketOf (dp.map fun t => (t.1, toAffine t.2)) (k + 1) :=
  Core.pbucketScatter_spec Vesta.curve hA hB hy0 htwo base dp hdp

/-- The scatter-bucketed projective window value (Vesta instance of `Core.pwindowValueFast`). -/
abbrev pwindowValueFast : ℕ → ℕ → List (ℕ × PVes) → PVes := Core.pwindowValueFast (F := Fq)

theorem pwindowValueFast_spec (base i : ℕ) (pterms : List (ℕ × PVes))
    (h : ∀ p ∈ pterms, Valid p.2) :
    Valid (pwindowValueFast base i pterms)
      ∧ toAffine (pwindowValueFast base i pterms)
        = Msm.windowValue base i (pterms.map fun t => (t.1, toAffine t.2)) :=
  Core.pwindowValueFast_spec Vesta.curve hA hB hy0 htwo base i pterms h

/-! ## The scatter-bucketed projective Pippenger MSM -/

/-- **Scatter-bucketed projective Pippenger** (Vesta instance of `Core.pippengerProjScatter`). -/
abbrev pippengerProjScatter : ℕ → List (ℕ × Projective.G) → Projective.G :=
  Core.pippengerProjScatter Vesta.curve hA hB

theorem pippengerProjScatter_eq (c : ℕ) (terms : List (ℕ × Projective.G)) :
    pippengerProjScatter c terms = Msm.pippenger c terms :=
  Core.pippengerProjScatter_eq Vesta.curve hA hB hy0 htwo c terms

theorem pippengerProjScatter_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × Projective.G)) :
    pippengerProjScatter c terms = (terms.map fun t => t.1 • t.2).sum :=
  Core.pippengerProjScatter_eq_msm Vesta.curve hA hB hy0 htwo c hc terms

/-! ## Windows-parallel projective Pippenger -/

/-- **Windows-parallel scatter-bucketed projective Pippenger** (Vesta instance of
`Core.pippengerProjScatterPar`). -/
abbrev pippengerProjScatterPar : ℕ → List (ℕ × Projective.G) → Projective.G :=
  Core.pippengerProjScatterPar Vesta.curve hA hB

theorem pippengerProjScatterPar_eq (c : ℕ) (terms : List (ℕ × Projective.G)) :
    pippengerProjScatterPar c terms = pippengerProjScatter c terms :=
  Core.pippengerProjScatterPar_eq Vesta.curve hA hB c terms

theorem pippengerProjScatterPar_eq_msm (c : ℕ) (hc : 0 < c)
    (terms : List (ℕ × Projective.G)) :
    pippengerProjScatterPar c terms = (terms.map fun t => t.1 • t.2).sum :=
  Core.pippengerProjScatterPar_eq_msm Vesta.curve hA hB hy0 htwo c hc terms

/-! ## The `commit_lagrange` wrapper (Vesta-specific: coeffs in `Msm.Fp = VestaScalarField`) -/

/-- The fast `commit_lagrange` in projective coordinates: projective windowed Pippenger over the
`(coeffᵢ.val, basisᵢ)` terms (single final inversion), plus the blind. -/
def commitLagrangeProjWith (c : ℕ) (blind : Projective.G) (basis : List Projective.G)
    (coeffs : List Fp) : Projective.G :=
  pippengerProj c
    ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
      fun t => (t.1.val, t.2)) + blind

/-- **The projective commitment equals the naive `commit_lagrange` spec**
(`Fast.Msm.commitLagrangeSpec`). -/
theorem commitLagrangeProjWith_eq (c : ℕ) (hc : 0 < c)
    (blind : Projective.G) (basis : List Projective.G) (coeffs : List Fp) :
    commitLagrangeProjWith c blind basis coeffs = Msm.commitLagrangeSpec blind basis coeffs := by
  unfold commitLagrangeProjWith Msm.commitLagrangeSpec
  rw [pippengerProj_eq, Msm.zip_terms_eq, Msm.pippenger_eq_msm c hc, List.map_map]
  rfl

/-- The fast `commit_lagrange` with scatter-bucketed projective Pippenger. -/
def commitLagrangeProjScatterWith (c : ℕ) (blind : Projective.G) (basis : List Projective.G)
    (coeffs : List Fp) : Projective.G :=
  pippengerProjScatter c
    ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
      fun t => (t.1.val, t.2)) + blind

/-- **The scatter-bucketed projective commitment equals the naive `commit_lagrange` spec**. -/
theorem commitLagrangeProjScatterWith_eq (c : ℕ) (hc : 0 < c)
    (blind : Projective.G) (basis : List Projective.G) (coeffs : List Fp) :
    commitLagrangeProjScatterWith c blind basis coeffs
      = Msm.commitLagrangeSpec blind basis coeffs := by
  unfold commitLagrangeProjScatterWith Msm.commitLagrangeSpec
  rw [pippengerProjScatter_eq, Msm.zip_terms_eq, Msm.pippenger_eq_msm c hc, List.map_map]
  rfl

end CompElliptic.Curves.Pasta.Fast.MsmProj
