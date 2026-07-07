/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.Pasta
import CompElliptic.CurveOrder

/-!
# Orders of the Pasta curve groups (Pallas and Vesta)

Instantiates `CompElliptic.CurveOrder.card_eq_of_hasse_of_field_ge_37` at the two Pasta curves:
assuming Hasse's bound (`HasseBound`, the one irreducible hypothesis — Mathlib lacks Hasse's
theorem), the Pallas group has order `PALLAS_SCALAR_CARD` and the Vesta group has order
`PALLAS_BASE_CARD` (the Pasta cycle: each curve's order is the other's base-field size).

Everything else is discharged outright. The test point `G = (-1, 2)` is the prime-order witness,
and the witness fact `[order] G = 𝒪` (a `≈ 2^254` scalar multiplication) is a one-line
`native_decide` now that the `SWPoint` scalar action `•` itself computes in `O(log n)`. The
field-size facts (`order ∈ hasseInterval (#F)`, `37 ≤ #F`) are concrete closed facts.
-/

namespace CompElliptic.Curves.Pasta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder CompElliptic.Fields.Pasta

namespace Pallas

/-- The test point `(-1, 2)` as a point of the Pallas curve — the prime-order witness. -/
def Gpt : SWPoint curve := ⟨-1, 2, Or.inl (by native_decide)⟩

theorem Gpt_ne_zero : Gpt ≠ 0 := by native_decide

/-- `[q] G = 𝒪`, where `q = PALLAS_SCALAR_CARD` is the Pallas group order. -/
theorem scalarCard_nsmul_Gpt : PALLAS_SCALAR_CARD • Gpt = 0 := by native_decide

/-- **The Pallas curve group has order `PALLAS_SCALAR_CARD`**, assuming Hasse's bound. -/
theorem card_eq (hHasse : HasseBound curve) :
    Nat.card (SWPoint curve) = PALLAS_SCALAR_CARD := by
  refine card_eq_of_hasse_of_field_ge_37 curve PALLAS_SCALAR_is_prime Gpt_ne_zero
    scalarCard_nsmul_Gpt hHasse ?_ ?_
  · rw [show Fintype.card Fp = PALLAS_BASE_CARD from ZMod.card _]
    simp only [hasseInterval, Set.mem_setOf_eq]; native_decide
  · rw [show Fintype.card Fp = PALLAS_BASE_CARD from ZMod.card _]; decide

end Pallas

namespace Vesta

/-- The test point `(-1, 2)` as a point of the Vesta curve — the prime-order witness. -/
def Gpt : SWPoint curve := ⟨-1, 2, Or.inl (by native_decide)⟩

theorem Gpt_ne_zero : Gpt ≠ 0 := by native_decide

/-- `[p] G = 𝒪`, where `p = PALLAS_BASE_CARD` is the Vesta group order. -/
theorem baseCard_nsmul_Gpt : PALLAS_BASE_CARD • Gpt = 0 := by native_decide

/-- **The Vesta curve group has order `PALLAS_BASE_CARD`**, assuming Hasse's bound. -/
theorem card_eq (hHasse : HasseBound curve) :
    Nat.card (SWPoint curve) = PALLAS_BASE_CARD := by
  refine card_eq_of_hasse_of_field_ge_37 curve PALLAS_BASE_is_prime Gpt_ne_zero
    baseCard_nsmul_Gpt hHasse ?_ ?_
  · rw [show Fintype.card Fq = PALLAS_SCALAR_CARD from ZMod.card _]
    simp only [hasseInterval, Set.mem_setOf_eq]; native_decide
  · rw [show Fintype.card Fq = PALLAS_SCALAR_CARD from ZMod.card _]; decide

end Vesta

end CompElliptic.Curves.Pasta
