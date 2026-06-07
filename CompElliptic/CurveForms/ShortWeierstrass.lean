/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Short-Weierstrass elliptic curves

One module for the short-Weierstrass curve form `y² = x³ + A x + B`, layered:

1. **Raw computable kernel** — `OnCurve`, `neg`, complete `add` (identity `𝒪 ≡ (0, 0)`), `smul`,
   as plain functions on `F × F`. `add` models complete addition: it is total and evaluable
   using `native_decide`, with a decidable case split for `𝒪` / doubling / `P + (-P)`.
2. **Transport foundation** — `toW`, identifying the form with Mathlib's `WeierstrassCurve` so
   that the hard group axioms can be borrowed from Mathlib's proven `AddCommGroup`.
3. **Rich bundled types** — `SWCurve` (bundles ellipticity and `B ≠ 0`) and `SWPoint E`
   (correct-by-construction: on the curve or `𝒪`). This is the correct-by-construction interface
   used to express the group structure and circuit gadgets.

The field assumption is a generic `[Field F]`: `SWCurve.IsElliptic` excludes characteristic 2
(`sw_Δ = 0` there), so binary fields are gracefully excluded, but without precluding any future
separate binary-field curve form. See `TODO.md`.
-/

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Raw computable kernel -/

/-- `p` lies on `y² = x³ + a x + b` as an affine point. -/
def OnCurve (a b : F) (p : F × F) : Prop := p.2 ^ 2 = p.1 ^ 3 + a * p.1 + b

instance (a b : F) (p : F × F) : Decidable (OnCurve a b p) := by unfold OnCurve; infer_instance

/-- A representable point: on the curve, or the `(0, 0)` identity sentinel `𝒪`. -/
def Valid (a b : F) (p : F × F) : Prop := OnCurve a b p ∨ p = (0, 0)

omit [DecidableEq F] in
/-- The `(0, 0)` sentinel is off the curve exactly when `b ≠ 0` (which holds for any elliptic
curve: `a = b = 0` is the singular cusp `y² = x³`). This is what makes `(0, 0) ≡ 𝒪` unambiguous. -/
theorem not_onCurve_zero {a b : F} (hb : b ≠ 0) : ¬ OnCurve a b (0, 0) := by
  intro h
  apply hb
  have h' : (0 : F) ^ 2 = (0 : F) ^ 3 + a * 0 + b := h
  simpa using h'.symm

/-- Negation `(x, y) ↦ (x, -y)`; fixes the `(0, 0)` sentinel. -/
def neg (p : F × F) : F × F := (p.1, -p.2)

/-- Complete affine addition with `(0, 0) ≡ 𝒪`.
Only the curve coefficient `a` appears (in the doubling slope `(3x² + a)/(2y)`);
`b` is not needed. -/
def add (a : F) (p q : F × F) : F × F :=
  if p = (0, 0) then q
  else if q = (0, 0) then p
  else if p.1 = q.1 then
    if p.2 + q.2 = 0 then (0, 0)                 -- q = -p ⇒ 𝒪
    else                                         -- doubling (same x, so same nonzero y)
      let lam := (3 * p.1 ^ 2 + a) / (2 * p.2)
      let x₃ := lam ^ 2 - p.1 - q.1
      (x₃, lam * (p.1 - x₃) - p.2)
  else                                           -- distinct x-coordinates
    let lam := (q.2 - p.2) / (q.1 - p.1)
    let x₃ := lam ^ 2 - p.1 - q.1
    (x₃, lam * (p.1 - x₃) - p.2)

/-- `[n] p`, by iterated addition (spec-level, not the windowed circuit form). -/
def smul (a : F) : ℕ → F × F → F × F
  | 0, _ => (0, 0)
  | n + 1, p => add a (smul a n p) p

/-! ## Identity, involution, and inverse laws (raw, no hypotheses) -/

/-- `𝒪 + p = p`. -/
theorem zero_add (a : F) (p : F × F) : add a (0, 0) p = p := by
  simp [add]

/-- `p + 𝒪 = p`. -/
theorem add_zero (a : F) (p : F × F) : add a p (0, 0) = p := by
  rcases eq_or_ne p (0, 0) with h | h <;> simp [add, h]

omit [DecidableEq F] in
/-- `-(-p) = p`. -/
theorem neg_neg (p : F × F) : neg (neg p) = p := by
  simp [neg]

/-- `p + (-p) = 𝒪`: for `p = 𝒪` immediate; otherwise the addends share an `x`-coordinate with
`p.2 + (neg p).2 = 0`, so the `q = -p` branch fires. Proved by an explicit `if`-branch walk
rather than `split_ifs <;> simp_all`, which blows the recursion limit on the nested `ite`. -/
theorem add_neg (a : F) (p : F × F) : add a p (neg p) = (0, 0) := by
  rcases eq_or_ne p (0, 0) with h | h
  · simp [add, neg, h]
  · have hn : neg p ≠ (0, 0) := fun hc => h (by simpa [neg, Prod.ext_iff] using hc)
    have hx : p.1 = (neg p).1 := rfl
    have hy : p.2 + (neg p).2 = 0 := by simp [neg]
    unfold add
    rw [if_neg h, if_neg hn, if_pos hx, if_pos hy]

/-! ## Transport foundation: identify the short form with a Mathlib `WeierstrassCurve`

For the short form (`a₁ = a₂ = a₃ = 0`, `a₄ = a`, `a₆ = b`) Mathlib's computable coordinate
formulas (`negY`, `slope`, `addX`, `addY`) reduce to exactly our `add`/`neg`, so closure and
associativity can be borrowed from Mathlib's proven `AddCommGroup` on `WeierstrassCurve.Affine.Point`
(`Affine/Point.lean`). The carried `Nonsingular` proof is a `Prop`, so the bridge is
computation-erasable. The curve must be nonsingular (`[(toW a b).IsElliptic]`). -/

/-- The short-Weierstrass curve `y² = x³ + a x + b` as a Mathlib `WeierstrassCurve`. -/
def toW (a b : F) : WeierstrassCurve F := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

omit [DecidableEq F]
@[simp] lemma toW_a₁ (a b : F) : (toW a b).a₁ = 0 := rfl
@[simp] lemma toW_a₂ (a b : F) : (toW a b).a₂ = 0 := rfl
@[simp] lemma toW_a₃ (a b : F) : (toW a b).a₃ = 0 := rfl
@[simp] lemma toW_a₄ (a b : F) : (toW a b).a₄ = a := rfl
@[simp] lemma toW_a₆ (a b : F) : (toW a b).a₆ = b := rfl

/-- Our on-curve predicate is Mathlib's affine curve equation for `toW a b`. -/
lemma equation_toW {a b x y : F} :
    WeierstrassCurve.Affine.Equation (toW a b) x y ↔ OnCurve a b (x, y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆, OnCurve]
  constructor <;> intro h <;> linear_combination h

/-- On a nonsingular curve, every on-curve point gives a nonsingular Mathlib point. -/
lemma nonsingular_toW {a b : F} [(toW a b).IsElliptic] {x y : F}
    (h : OnCurve a b (x, y)) : WeierstrassCurve.Affine.Nonsingular (toW a b) x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_toW.mpr h)

end CompElliptic.CurveForms.ShortWeierstrass

namespace CompElliptic.CurveForms.ShortWeierstrass
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Closure, commutativity, associativity (raw workhorses)

Stated with the hypotheses the transport needs: `[(toW a b).IsElliptic]` throughout, and `b ≠ 0`
for the laws whose `𝒪`-sentinel cases require `(0, 0)` to be off the curve. The `SWPoint`
`AddCommGroup` instance below discharges these from `SWCurve`'s bundled fields. -/

/-- Closure: `add` preserves `Valid`. (Result coords = Mathlib `addX`/`addY`; `nonsingular_add`
gives on-curveness.) -/
theorem valid_add {a b : F} [(toW a b).IsElliptic] {p q : F × F}
    (hp : Valid a b p) (hq : Valid a b q) : Valid a b (add a p q) := by
  sorry

/-- Commutativity. (Generic branch is pure field algebra; doubling branch forces `p = q` from
on-curve; `𝒪` branches from the identity laws.) -/
theorem add_comm {a b : F} {p q : F × F} (hp : Valid a b p) (hq : Valid a b q) :
    add a p q = add a q p := by
  sorry

/-- Associativity (the hard axiom), by transport to Mathlib's `Point` `AddCommGroup`. -/
theorem add_assoc {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] {p q r : F × F}
    (hp : Valid a b p) (hq : Valid a b q) (hr : Valid a b r) :
    add a (add a p q) r = add a p (add a q r) := by
  sorry

/-! ## Rich bundled types -/

/-- The discriminant of the short-Weierstrass curve `y² = x³ + A x + B`. -/
def sw_Δ (A B : F) : F := -16 * (4 * A ^ 3 + 27 * B ^ 2)

/-- A short-Weierstrass elliptic curve: coefficients `A`, `B`, bundled with nonsingularity
(`IsUnit sw_Δ`, which over a field is `sw_Δ ≠ 0` and self-excludes characteristic 2) and `B ≠ 0`
(so the `𝒪 = (0, 0)` sentinel is off the curve). -/
structure SWCurve (F : Type*) [Field F] where
  A : F
  B : F
  IsElliptic : IsUnit (sw_Δ A B)
  B_nonzero : B ≠ 0

/-- A point on `E`, correct by construction: on the curve, or the identity `𝒪 = (0, 0)`. -/
structure SWPoint (E : SWCurve F) where
  x : F
  y : F
  onCurve : Valid E.A E.B (x, y)
deriving Repr

omit [DecidableEq F] in
/-- `(0, 0)` is off the curve `E`, immediate from `E.B_nonzero`. -/
theorem origin_not_on_curve (E : SWCurve F) : ¬ OnCurve E.A E.B (0, 0) :=
  not_onCurve_zero E.B_nonzero

/-- The identity point `𝒪` on `E`. -/
def SWPoint.zero (E : SWCurve F) : SWPoint E := ⟨0, 0, Or.inr rfl⟩

instance (E : SWCurve F) : Zero (SWPoint E) := ⟨SWPoint.zero E⟩

-- TODO (next): bridge `[(E.toW).IsElliptic]` from `E.IsElliptic`, lift `add`/`neg` to `SWPoint E`
-- via `valid_add`, and assemble the `AddCommGroup (SWPoint E)` instance.

end CompElliptic.CurveForms.ShortWeierstrass
