/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta.Fast.Msm
import CompElliptic.Curves.Pasta.Fast.Projective.Core

/-!
# The windowed Pippenger MSM run in projective coordinates, generic over the base field

The affine Pippenger accelerator (`Fast.Msm`) is already generic over any `[AddCommGroup G]`, but at
a curve's affine group every group addition pays a field inversion. This module runs the whole
Pippenger interior over the field-generic `Projective.Core.PPoint` with `padd`/`pnsmulFast` — one
inversion per MSM instead of one per add — and proves the result equal to the affine accelerator
(`pippengerProj_eq`) and to the naive MSM (`pippengerProj_eq_msm`).

`PPoint` is not a lawful monoid on the nose (associativity only holds after `toAffine`), so the
Pippenger equality is not re-run here: each fold of `Fast.Msm` is mirrored by a `padd`/`pid` version
and shown to commute with `toAffine`, carrying `Valid` through every intermediate (`psum_spec`,
`pbucketOf_spec`, `foldr_paccStep_spec`, `pwindowValue_spec`, `phornerList_spec`).

This is the field-generic core; each Pasta curve instantiates it (Vesta in `Fast/MsmProj.lean`,
Pallas in `Fast/MsmProjPallas.lean`) by supplying its curve `E` (with `E.A = 0`, `E.B = 5`) and the
no-2-torsion facts `hy0`/`htwo`. Only the basic path is generic here; the Array-scatter and
parallel variants remain in the Vesta module.

The `Fast` interfaces are provisional: they are not guaranteed to remain public, and may be folded
into the existing API or otherwise changed incompatibly.
-/

open CompElliptic
open CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.Projective.Core
open CompElliptic.Curves.Pasta.Fast.Projective.Core.PPoint

namespace CompElliptic.Curves.Pasta.Fast.MsmProj.Core

variable {F : Type*} [Field F] [DecidableEq F]
variable (E : SWCurve F) (hA : E.A = 0) (hB : E.B = 5)

/-- The affine group `SWPoint E` carries a default point, needed to instantiate the `Fast.Msm`
wrapper (`Msm.pippenger`) whose section fixes `[Inhabited G]`. -/
local instance : Inhabited (SWPoint E) := ⟨0⟩

/-! ## Projective bucket sum (`foldr padd pid`), mirroring `Fast.Msm.bucketOf` -/

/-- The `padd`-fold sum of a list of projective points, from the projective identity `pid`. -/
def psum (L : List (PPoint F)) : PPoint F := L.foldr padd pid

omit [DecidableEq F] in
theorem psum_cons (a : PPoint F) (xs : List (PPoint F)) :
    psum (a :: xs) = padd a (psum xs) := rfl

/-- A projective `padd`-sum of valid points is valid, and `toAffine` carries it to the affine sum. -/
theorem psum_spec (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (L : List (PPoint F)) (h : ∀ P ∈ L, Valid P) :
    Valid (psum L) ∧ toAffine E hA hB (psum L) = (L.map (toAffine E hA hB)).sum := by
  induction L with
  | nil => exact ⟨valid_pid, by simp [psum]⟩
  | cons a xs ih =>
    have ha : Valid a := h a (by simp)
    have hxs : ∀ P ∈ xs, Valid P := fun P hP => h P (by simp [hP])
    obtain ⟨hvxs, hxseq⟩ := ih hxs
    rw [psum_cons]
    exact ⟨valid_padd hy0 htwo ha hvxs, by
      rw [toAffine_padd E hA hB hy0 htwo ha hvxs, hxseq, List.map_cons, List.sum_cons]⟩

/-- The projective bucket-`b` sum: `padd`-fold the points whose digit tag is `b`. -/
def pbucketOf (dp : List (ℕ × PPoint F)) (b : ℕ) : PPoint F :=
  psum (dp.filterMap fun p => if p.1 = b then some p.2 else none)

/-- The projective bucket sum is valid and matches `Fast.Msm.bucketOf` of the `toAffine`-mapped
digit-tagged list. -/
theorem pbucketOf_spec (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (dp : List (ℕ × PPoint F)) (b : ℕ) (h : ∀ p ∈ dp, Valid p.2) :
    Valid (pbucketOf dp b)
      ∧ toAffine E hA hB (pbucketOf dp b)
        = Msm.bucketOf (dp.map fun t => (t.1, toAffine E hA hB t.2)) b := by
  have hval : ∀ P ∈ dp.filterMap (fun p => if p.1 = b then some p.2 else none), Valid P := by
    intro P hP
    rw [List.mem_filterMap] at hP
    obtain ⟨q, hq, hqeq⟩ := hP
    by_cases hc : q.1 = b
    · rw [if_pos hc, Option.some.injEq] at hqeq; rw [← hqeq]; exact h q hq
    · rw [if_neg hc] at hqeq; exact absurd hqeq (by simp)
  obtain ⟨hv, heq⟩ := psum_spec E hA hB hy0 htwo _ hval
  refine ⟨hv, ?_⟩
  rw [pbucketOf, heq, Msm.bucketOf, List.filterMap_map, List.map_filterMap]
  refine congrArg List.sum (congrArg (dp.filterMap ·) ?_)
  funext p
  by_cases hc : p.1 = b <;> simp [hc, Function.comp]

/-! ## Projective suffix-sum accumulator, mirroring `Fast.Msm.accStep` -/

/-- One step of the projective suffix-sum accumulator: carry `(running, total)`, `padd` the next
bucket into `running`, then `padd` `running` into `total`. -/
def paccStep (a : PPoint F) (p : PPoint F × PPoint F) : PPoint F × PPoint F :=
  (padd p.1 a, padd p.2 (padd p.1 a))

/-- Folding `paccStep` over valid points keeps both accumulator components valid, and `toAffine`
carries the whole fold (componentwise) to the affine `Fast.Msm.accStep` fold. -/
theorem foldr_paccStep_spec (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (L : List (PPoint F)) (h : ∀ P ∈ L, Valid P) :
    Valid (L.foldr paccStep (pid, pid)).1 ∧ Valid (L.foldr paccStep (pid, pid)).2
      ∧ (toAffine E hA hB (L.foldr paccStep (pid, pid)).1,
          toAffine E hA hB (L.foldr paccStep (pid, pid)).2)
        = List.foldr Msm.accStep ((0 : SWPoint E), (0 : SWPoint E)) (L.map (toAffine E hA hB)) := by
  induction L with
  | nil => exact ⟨valid_pid, valid_pid, by simp⟩
  | cons a xs ih =>
    have ha : Valid a := h a (by simp)
    have hxs : ∀ P ∈ xs, Valid P := fun P hP => h P (by simp [hP])
    obtain ⟨hv1, hv2, heq⟩ := ih hxs
    have hstep : (a :: xs).foldr paccStep (pid, pid)
        = paccStep a (xs.foldr paccStep (pid, pid)) := rfl
    rw [hstep]
    have hv1' : Valid (padd (xs.foldr paccStep (pid, pid)).1 a) := valid_padd hy0 htwo hv1 ha
    refine ⟨hv1', valid_padd hy0 htwo hv2 hv1', ?_⟩
    rw [List.map_cons, List.foldr_cons, ← heq, Msm.accStep]
    simp only [paccStep, toAffine_padd E hA hB hy0 htwo hv1 ha,
      toAffine_padd E hA hB hy0 htwo hv2 hv1']

/-! ## Projective window value, mirroring `Fast.Msm.windowValue` -/

/-- The digit-tagged projective term list for window `i`. -/
def pdpOf (base i : ℕ) (pterms : List (ℕ × PPoint F)) : List (ℕ × PPoint F) :=
  pterms.map fun t => (Msm.digit base i t.1, t.2)

/-- The projective window value: build the `base − 1` projective buckets, then run the projective
suffix-sum accumulation. -/
def pwindowValue (base i : ℕ) (pterms : List (ℕ × PPoint F)) : PPoint F :=
  (List.foldr paccStep (pid, pid)
    ((List.range (base - 1)).map fun k => pbucketOf (pdpOf base i pterms) (k + 1))).2

/-- The projective window value is valid and matches `Fast.Msm.windowValue` of the `toAffine`-mapped
terms. -/
theorem pwindowValue_spec (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (base i : ℕ) (pterms : List (ℕ × PPoint F)) (h : ∀ p ∈ pterms, Valid p.2) :
    Valid (pwindowValue base i pterms)
      ∧ toAffine E hA hB (pwindowValue base i pterms)
        = Msm.windowValue base i (pterms.map fun t => (t.1, toAffine E hA hB t.2)) := by
  have hdp : ∀ p ∈ pdpOf base i pterms, Valid p.2 := by
    intro p hp
    rw [pdpOf, List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact h t ht
  simp only [pwindowValue]
  set buckets := (List.range (base - 1)).map fun k => pbucketOf (pdpOf base i pterms) (k + 1)
    with hbuck
  have hbval : ∀ P ∈ buckets, Valid P := by
    intro P hP
    rw [hbuck, List.mem_map] at hP
    obtain ⟨k, _, rfl⟩ := hP
    exact (pbucketOf_spec E hA hB hy0 htwo _ _ hdp).1
  obtain ⟨_, hv2, heq⟩ := foldr_paccStep_spec E hA hB hy0 htwo buckets hbval
  refine ⟨hv2, ?_⟩
  have hmap : buckets.map (toAffine E hA hB)
      = (List.range (base - 1)).map fun k =>
          Msm.bucketOf (Msm.dpOf base i (pterms.map fun t => (t.1, toAffine E hA hB t.2))) (k + 1) := by
    rw [hbuck, List.map_map]
    apply List.map_congr_left
    intro k _
    rw [Function.comp_apply, (pbucketOf_spec E hA hB hy0 htwo _ _ hdp).2]
    congr 1
    simp only [pdpOf, Msm.dpOf, List.map_map, Function.comp_def]
  rw [Msm.windowValue, ← hmap, ← heq]

/-! ## Projective Horner fold, mirroring `Fast.Msm.hornerList` -/

/-- Horner across windows in projective coordinates: each `base •` doubling is the fast binary
scalar multiplication `pnsmulFast base`, and the window value is folded in with `padd`. -/
def phornerList (base : ℕ) (vals : List (PPoint F)) : PPoint F :=
  List.foldr (fun v acc => padd (pnsmulFast base acc) v) pid vals

/-- The projective Horner fold is valid and matches `Fast.Msm.hornerList` of the `toAffine`-mapped
window values; each `base`-fold doubling transports via `pnsmulFast_spec`. -/
theorem phornerList_spec (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (base : ℕ) (vals : List (PPoint F)) (h : ∀ P ∈ vals, Valid P) :
    Valid (phornerList base vals)
      ∧ toAffine E hA hB (phornerList base vals)
        = Msm.hornerList base (vals.map (toAffine E hA hB)) := by
  induction vals with
  | nil => exact ⟨valid_pid, by simp [phornerList, Msm.hornerList]⟩
  | cons v xs ih =>
    have hv : Valid v := h v (by simp)
    have hxs : ∀ P ∈ xs, Valid P := fun P hP => h P (by simp [hP])
    obtain ⟨hvacc, heq⟩ := ih hxs
    have hstep : phornerList base (v :: xs)
        = padd (pnsmulFast base (phornerList base xs)) v := rfl
    rw [hstep]
    refine ⟨valid_padd hy0 htwo (pnsmulFast_spec E hA hB hy0 htwo hvacc base).1 hv, ?_⟩
    rw [toAffine_padd E hA hB hy0 htwo (pnsmulFast_spec E hA hB hy0 htwo hvacc base).1 hv,
      (pnsmulFast_spec E hA hB hy0 htwo hvacc base).2, heq, List.map_cons]
    simp only [Msm.hornerList, List.foldr_cons]

/-! ## The projective Pippenger MSM and its equality to the affine accelerator -/

/-- **Windowed Pippenger MSM run in projective coordinates.** Each affine point is lifted via
`ofAffine`; the windowed algorithm (digits, buckets, suffix-sum, Horner doublings) runs over
`PPoint` with `padd`/`pnsmulFast`; a single `toAffine` (one field inversion) is taken at the end. -/
def pippengerProj (c : ℕ) (terms : List (ℕ × SWPoint E)) : SWPoint E :=
  toAffine E hA hB (phornerList (2 ^ c)
    ((List.range (Msm.numWindows c terms)).map fun i =>
      pwindowValue (2 ^ c) i (terms.map fun t => (t.1, ofAffine E t.2))))

/-- **The projective Pippenger equals the affine Pippenger.** Lifting by `ofAffine` and reading back
by `toAffine` is the identity on terms (`toAffine_ofAffine`); each window and the Horner fold commute
with `toAffine`, so the whole projective interior collapses to the affine `Fast.Msm.pippenger`. -/
theorem pippengerProj_eq (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (c : ℕ) (terms : List (ℕ × SWPoint E)) :
    pippengerProj E hA hB c terms = Msm.pippenger c terms := by
  rw [pippengerProj]
  set pterms := terms.map (fun t => (t.1, ofAffine E t.2)) with hpterms
  set windows := (List.range (Msm.numWindows c terms)).map fun i => pwindowValue (2 ^ c) i pterms
    with hwin
  have hval : ∀ p ∈ pterms, Valid p.2 := by
    intro p hp
    rw [hpterms, List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    exact valid_ofAffine E hA hB t.2
  have hf : pterms.map (fun t => (t.1, toAffine E hA hB t.2)) = terms := by
    rw [hpterms, List.map_map]
    conv_rhs => rw [← List.map_id terms]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, toAffine_ofAffine E hA hB, id_eq]
  have hwval : ∀ P ∈ windows, Valid P := by
    intro P hP
    rw [hwin, List.mem_map] at hP
    obtain ⟨i, _, rfl⟩ := hP
    exact (pwindowValue_spec E hA hB hy0 htwo (2 ^ c) i pterms hval).1
  rw [(phornerList_spec E hA hB hy0 htwo (2 ^ c) windows hwval).2, Msm.pippenger]
  congr 1
  rw [hwin, List.map_map]
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, (pwindowValue_spec E hA hB hy0 htwo (2 ^ c) i pterms hval).2, hf]

/-- **The projective Pippenger equals the naive MSM.** End-to-end correctness for `c ≥ 1`. -/
theorem pippengerProj_eq_msm (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (c : ℕ) (hc : 0 < c) (terms : List (ℕ × SWPoint E)) :
    pippengerProj E hA hB c terms = (terms.map fun t => t.1 • t.2).sum := by
  rw [pippengerProj_eq E hA hB hy0 htwo, Msm.pippenger_eq_msm c hc]

/-! ## Single-pass Array bucketing for the projective interior

`pwindowValue`'s per-bucket `filterMap` dominates the group work at `base = 2 ^ 8`; `pbucketScatter`
builds all buckets in one pass. Its invariant cannot reuse `Msm.bucketScatter_toList` (that uses
`add_assoc`, and `padd` is not associative on the nose), so it too is transported through
`toAffine` (`foldl_pscatterStep_spec`). -/

/-- One projective scatter step: drop digit-`0` terms, otherwise `padd` the point into bucket
slot `d − 1` (slot `k` holds bucket `k + 1`). -/
def pscatterStep (a : Array (PPoint F)) (p : ℕ × PPoint F) : Array (PPoint F) :=
  if p.1 = 0 then a else a.modify (p.1 - 1) (fun v => padd v p.2)

/-- Scatter a digit-tagged projective point list into its `base − 1` buckets in one pass. -/
def pbucketScatter (base : ℕ) (dp : List (ℕ × PPoint F)) : Array (PPoint F) :=
  dp.foldl pscatterStep (Array.replicate (base - 1) pid)

omit [DecidableEq F] in
@[simp] theorem size_pscatterStep (a : Array (PPoint F)) (p : ℕ × PPoint F) :
    (pscatterStep a p).size = a.size := by
  unfold pscatterStep; split <;> simp

omit [DecidableEq F] in
@[simp] theorem size_foldl_pscatterStep (dp : List (ℕ × PPoint F)) (a : Array (PPoint F)) :
    (dp.foldl pscatterStep a).size = a.size := by
  induction dp generalizing a with
  | nil => rfl
  | cons p dp ih => rw [List.foldl_cons, ih, size_pscatterStep]

omit [DecidableEq F] in
/-- A single projective scatter step through `getElem?`: slot `k` gains a right-`padd` of `x`
exactly when the digit is `k + 1`. -/
theorem getElem?_pscatterStep (a : Array (PPoint F)) (d : ℕ) (x : PPoint F) (k : ℕ) :
    (pscatterStep a (d, x))[k]?
      = if d = k + 1 then a[k]?.map (fun v => padd v x) else a[k]? := by
  unfold pscatterStep
  by_cases h0 : d = 0
  · subst h0
    rw [if_pos rfl, if_neg (by omega)]
  · rw [if_neg h0, Array.getElem?_modify]
    by_cases hdk : d = k + 1
    · rw [if_pos (by omega), if_pos hdk]
    · rw [if_neg (by omega), if_neg hdk]

/-- **The scatter fold invariant, transported through `toAffine`.** Starting from a valid slot
value `v`, slot `k` ends valid and reads — in `SWPoint E` — as `toAffine v` plus the affine bucket
sum of the processed digit-tagged list. -/
private theorem foldl_pscatterStep_spec (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (dp : List (ℕ × PPoint F)) (hdp : ∀ p ∈ dp, Valid p.2) :
    ∀ (a : Array (PPoint F)) (k : ℕ) (v : PPoint F), a[k]? = some v → Valid v →
      ∃ w, (dp.foldl pscatterStep a)[k]? = some w ∧ Valid w ∧
        toAffine E hA hB w = toAffine E hA hB v
          + Msm.bucketOf (dp.map fun t => (t.1, toAffine E hA hB t.2)) (k + 1) := by
  induction dp with
  | nil =>
    intro a k v hv hval
    exact ⟨v, hv, hval, by simp⟩
  | cons p dp ih =>
    intro a k v hv hval
    obtain ⟨d, x⟩ := p
    have hx : Valid x := hdp (d, x) (by simp)
    have hdp' : ∀ q ∈ dp, Valid q.2 := fun q hq => hdp q (by simp [hq])
    rw [List.foldl_cons]
    by_cases hdk : d = k + 1
    · have hv' : (pscatterStep a (d, x))[k]? = some (padd v x) := by
        rw [getElem?_pscatterStep, if_pos hdk, hv, Option.map_some]
      obtain ⟨w, hw, hwval, hweq⟩ :=
        ih hdp' (pscatterStep a (d, x)) k (padd v x) hv' (valid_padd hy0 htwo hval hx)
      refine ⟨w, hw, hwval, ?_⟩
      rw [hweq, toAffine_padd E hA hB hy0 htwo hval hx, List.map_cons, Msm.bucketOf_cons,
        if_pos hdk, _root_.add_assoc]
    · have hv' : (pscatterStep a (d, x))[k]? = some v := by
        rw [getElem?_pscatterStep, if_neg hdk, hv]
      obtain ⟨w, hw, hwval, hweq⟩ := ih hdp' (pscatterStep a (d, x)) k v hv' hval
      refine ⟨w, hw, hwval, ?_⟩
      rw [hweq, List.map_cons, Msm.bucketOf_cons, if_neg hdk, _root_.zero_add]

/-- **The scattered buckets are the affine bucket list, slotwise.** Every slot is valid, and
`toAffine` maps the slot list to exactly the bucket list `Msm.windowValue` folds over. -/
theorem pbucketScatter_spec (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (base : ℕ) (dp : List (ℕ × PPoint F)) (hdp : ∀ p ∈ dp, Valid p.2) :
    (∀ P ∈ (pbucketScatter base dp).toList, Valid P)
      ∧ (pbucketScatter base dp).toList.map (toAffine E hA hB)
        = (List.range (base - 1)).map fun k =>
            Msm.bucketOf (dp.map fun t => (t.1, toAffine E hA hB t.2)) (k + 1) := by
  have hsize : (pbucketScatter base dp).size = base - 1 := by
    rw [pbucketScatter, size_foldl_pscatterStep, Array.size_replicate]
  have hslot : ∀ k, k < base - 1 →
      ∃ w, (pbucketScatter base dp)[k]? = some w ∧ Valid w ∧
        toAffine E hA hB w = Msm.bucketOf (dp.map fun t => (t.1, toAffine E hA hB t.2)) (k + 1) := by
    intro k hk
    have hinit : (Array.replicate (base - 1) (pid : PPoint F))[k]? = some pid := by
      rw [Array.getElem?_replicate, if_pos hk]
    obtain ⟨w, hw, hwval, hweq⟩ :=
      foldl_pscatterStep_spec E hA hB hy0 htwo dp hdp (Array.replicate (base - 1) pid) k pid
        hinit valid_pid
    exact ⟨w, hw, hwval, by rw [hweq, toAffine_pid E hA hB, _root_.zero_add]⟩
  constructor
  · intro P hP
    obtain ⟨k, hk, hPk⟩ := List.mem_iff_getElem.mp hP
    have hk' : k < base - 1 := by
      rw [Array.length_toList, hsize] at hk
      exact hk
    obtain ⟨w, hw, hwval, -⟩ := hslot k hk'
    have hPk? : (pbucketScatter base dp)[k]? = some P := by
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hk, hPk]
    rw [hPk?] at hw
    obtain rfl : P = w := Option.some.inj hw
    exact hwval
  · apply List.ext_getElem?
    intro k
    rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList]
    by_cases hk : k < base - 1
    · obtain ⟨w, hw, -, hweq⟩ := hslot k hk
      rw [hw, List.getElem?_range hk, Option.map_some, Option.map_some, hweq]
    · rw [Array.getElem?_eq_none (by rw [hsize]; omega),
        List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl

/-- The projective window value via the single-pass scatter (mirror of `Msm.windowValueFast`). -/
def pwindowValueFast (base i : ℕ) (pterms : List (ℕ × PPoint F)) : PPoint F :=
  (List.foldr paccStep (pid, pid) (pbucketScatter base (pdpOf base i pterms)).toList).2

/-- The scatter-bucketed projective window value is valid and matches `Msm.windowValue` of the
`toAffine`-mapped terms — the scatter twin of `pwindowValue_spec`. -/
theorem pwindowValueFast_spec (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (base i : ℕ) (pterms : List (ℕ × PPoint F)) (h : ∀ p ∈ pterms, Valid p.2) :
    Valid (pwindowValueFast base i pterms)
      ∧ toAffine E hA hB (pwindowValueFast base i pterms)
        = Msm.windowValue base i (pterms.map fun t => (t.1, toAffine E hA hB t.2)) := by
  have hdp : ∀ p ∈ pdpOf base i pterms, Valid p.2 := by
    intro p hp
    rw [pdpOf, List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact h t ht
  obtain ⟨hbval, hbmap⟩ := pbucketScatter_spec E hA hB hy0 htwo base (pdpOf base i pterms) hdp
  have hdpof : (pdpOf base i pterms).map (fun t => (t.1, toAffine E hA hB t.2))
      = Msm.dpOf base i (pterms.map fun t => (t.1, toAffine E hA hB t.2)) := by
    simp only [pdpOf, Msm.dpOf, List.map_map, Function.comp_def]
  rw [hdpof] at hbmap
  obtain ⟨-, hv2, heq⟩ := foldr_paccStep_spec E hA hB hy0 htwo _ hbval
  simp only [pwindowValueFast]
  refine ⟨hv2, ?_⟩
  rw [Msm.windowValue, ← hbmap, ← heq]

/-! ## The scatter-bucketed projective Pippenger MSM -/

/-- **Windowed Pippenger MSM in projective coordinates with single-pass Array bucketing** — the
fast serial form of `pippengerProj`. Proven equal to the affine `Msm.pippenger`. -/
def pippengerProjScatter (c : ℕ) (terms : List (ℕ × SWPoint E)) : SWPoint E :=
  toAffine E hA hB (phornerList (2 ^ c)
    ((List.range (Msm.numWindows c terms)).map fun i =>
      pwindowValueFast (2 ^ c) i (terms.map fun t => (t.1, ofAffine E t.2))))

/-- **The scatter-bucketed projective Pippenger equals the affine Pippenger** — same transport as
`pippengerProj_eq`, window values via `pwindowValueFast_spec`. -/
theorem pippengerProjScatter_eq (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (c : ℕ) (terms : List (ℕ × SWPoint E)) :
    pippengerProjScatter E hA hB c terms = Msm.pippenger c terms := by
  rw [pippengerProjScatter]
  set pterms := terms.map (fun t => (t.1, ofAffine E t.2)) with hpterms
  set windows := (List.range (Msm.numWindows c terms)).map fun i =>
      pwindowValueFast (2 ^ c) i pterms
    with hwin
  have hval : ∀ p ∈ pterms, Valid p.2 := by
    intro p hp
    rw [hpterms, List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    exact valid_ofAffine E hA hB t.2
  have hf : pterms.map (fun t => (t.1, toAffine E hA hB t.2)) = terms := by
    rw [hpterms, List.map_map]
    conv_rhs => rw [← List.map_id terms]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, toAffine_ofAffine E hA hB, id_eq]
  have hwval : ∀ P ∈ windows, Valid P := by
    intro P hP
    rw [hwin, List.mem_map] at hP
    obtain ⟨i, _, rfl⟩ := hP
    exact (pwindowValueFast_spec E hA hB hy0 htwo (2 ^ c) i pterms hval).1
  rw [(phornerList_spec E hA hB hy0 htwo (2 ^ c) windows hwval).2, Msm.pippenger]
  congr 1
  rw [hwin, List.map_map]
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, (pwindowValueFast_spec E hA hB hy0 htwo (2 ^ c) i pterms hval).2, hf]

/-- The scatter-bucketed projective Pippenger equals the naive MSM. -/
theorem pippengerProjScatter_eq_msm (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (c : ℕ) (hc : 0 < c) (terms : List (ℕ × SWPoint E)) :
    pippengerProjScatter E hA hB c terms = (terms.map fun t => t.1 • t.2).sum := by
  rw [pippengerProjScatter_eq E hA hB hy0 htwo, Msm.pippenger_eq_msm c hc]

/-! ## Windows-parallel projective Pippenger -/

/-- **Windows-parallel scatter-bucketed projective Pippenger**: `pippengerProjScatter` with the
window values evaluated as parallel tasks (`Msm.parMap`). -/
def pippengerProjScatterPar (c : ℕ) (terms : List (ℕ × SWPoint E)) : SWPoint E :=
  toAffine E hA hB (phornerList (2 ^ c)
    (Msm.parMap (fun i =>
      pwindowValueFast (2 ^ c) i (terms.map fun t => (t.1, ofAffine E t.2)))
      (List.range (Msm.numWindows c terms))))

/-- The windows-parallel projective Pippenger is the sequential one: `parMap` is `map`. -/
theorem pippengerProjScatterPar_eq (c : ℕ) (terms : List (ℕ × SWPoint E)) :
    pippengerProjScatterPar E hA hB c terms = pippengerProjScatter E hA hB c terms := by
  rw [pippengerProjScatterPar, Msm.parMap_eq_map, pippengerProjScatter]

/-- The windows-parallel projective Pippenger equals the naive MSM. -/
theorem pippengerProjScatterPar_eq_msm (hy0 : ∀ x : F, ¬ OnCurve 0 5 (x, 0)) (htwo : (2 : F) ≠ 0)
    (c : ℕ) (hc : 0 < c) (terms : List (ℕ × SWPoint E)) :
    pippengerProjScatterPar E hA hB c terms = (terms.map fun t => t.1 • t.2).sum := by
  rw [pippengerProjScatterPar_eq E hA hB c terms, pippengerProjScatter_eq_msm E hA hB hy0 htwo c hc]

end CompElliptic.Curves.Pasta.Fast.MsmProj.Core
