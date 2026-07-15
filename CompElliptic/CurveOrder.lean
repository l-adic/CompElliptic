/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.CurveForms.ShortWeierstrass
import Mathlib.GroupTheory.OrderOfElement

/-!
# Pinning a prime-order curve group's order without point-counting

For a curve whose group is *known to have prime order* r, fixing the order to exactly r needs
no point-counting algorithm (no Schoof, no proof of a counting algorithm's correctness).
It needs only:

1. a non-identity point P killed by r (so r ∣ #G, since r is prime); and
2. an *upper* bound #G < 2r, which can be provided by the Hasse bound for elliptic curves.

This module is the curve-agnostic core of that argument, in two layers.

* **Layer 1 — pure finite-group theory.** `card_eq_of_prime_witness` holds for *any* finite
  additive group, with no reference to elliptic curves. A witness of r • P = 0 forces r ∣ #G,
  and #G < 2r then forces #G = r.

* **Layer 2 — the Hasse bound.** If G is any elliptic curve E(F) over any finite field F of
  order q ≥ 37, Hasse's theorem |#E(F) - (q+1)| ≤ 2·√q supplies the #G < 2r premiss provided
  that r also satisfies the Hasse bound. For a prime-order cryptographic curve r ≈ q, so 2r
  sits far above the Hasse upper bound. Mathlib does not yet have Hasse's theorem for
  `WeierstrassCurve`, so we state it as a predicate (`HasseBound`) and take it as a hypothesis.

This is an application of the *Independently re-checkable trust* principle: the one piece
of trust beyond the kernel + standard axioms is a single *named general theorem* (Hasse),
flagged as an explicit hypothesis. It is separated from the concrete *closed numeric* fact
4q < (2r - (q+1))² (`hgap`), or alternatively the Hasse bound on r (`hr`), either of which
can be verified by any independent tool.
-/

namespace CompElliptic.CurveOrder

open CompElliptic.CurveForms.ShortWeierstrass

/-! ## Layer 1: pin the order from a prime-order witness (any finite additive group) -/

/-- **The prime-order witness step.** A non-identity `P` killed by a prime `r` has `addOrderOf P`
exactly `r` (`addOrderOf_eq_prime`), so `r ∣ #G` by Lagrange.

This is the half of the argument that uses the witness, and the only half; everything downstream
just rules out the remaining multiples of `r` using an upper bound on `#G`. -/
theorem dvd_natCard_of_prime_witness {G : Type*} [AddGroup G] [Finite G] {r : ℕ}
    (hr : r.Prime) {P : G} (hP : P ≠ 0) (hPr : r • P = 0) : r ∣ Nat.card G := by
  haveI := Fact.mk hr
  exact addOrderOf_eq_prime hPr hP ▸ addOrderOf_dvd_natCard P

/-- If `r` is prime, the finite additive group `G` has a non-identity element `P` killed by `r`
(`r • P = 0`), and `#G < 2r`, then `#G = r`.

The witness gives `r ∣ #G` (`dvd_natCard_of_prime_witness`); with `0 < #G < 2r` the only multiple
of `r` available is `r` itself. -/
theorem card_eq_of_prime_witness {G : Type*} [AddGroup G] [Finite G] {r : ℕ}
    (hr : r.Prime) {P : G} (hP : P ≠ 0) (hPr : r • P = 0)
    (hlt : Nat.card G < 2 * r) : Nat.card G = r := by
  have hne0 : Nat.card G ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨P⟩, inferInstance⟩
  exact Nat.eq_of_dvd_of_lt_two_mul hne0 (dvd_natCard_of_prime_witness hr hP hPr) hlt

/-! ## Layer 2: the Hasse bound (assumed; not yet in Mathlib) discharges `#G < 2r` -/

/-- The Hasse interval for a field of size `q`: the cardinalities `n` within `2√q` of `q + 1`,
written sqrt-free over `ℤ` as `(n - (q+1))² ≤ 4·q` (equivalently `|n - (q+1)| ≤ 2√q`). By Hasse's
theorem every point count `#E(F)` lies in it (with `q = #F`); we use the same interval to constrain
a candidate prime order. -/
def hasseInterval (q : ℕ) : Set ℕ := { n | ((n : ℤ) - (q+1))^2 ≤ 4*q }

/-- The arithmetic step from Hasse to the layer-1 premiss, purely over `ℕ`/`ℤ` and independent of
any particular curve. From the sqrt-free Hasse inequality on `N` relative to the field size `q`
(`(N - (q+1))² ≤ 4·q`), the concrete gap `4·q < (2r - (q+1))²`, and `q + 1 ≤ 2r`, conclude `N < 2r`.
(Only the *upper* Hasse bound is used; the gap and `q + 1 ≤ 2r` are closed facts about the two
relevant numbers, true here because `r ≈ q` so `2r` clears the upper bound with room.) -/
theorem lt_two_mul_of_hasse {N q r : ℕ}
    (hHasse : N ∈ hasseInterval q)
    (hgap : 4*(q : ℤ) < (2*r - (q+1))^2)
    (hle : (q : ℤ) + 1 ≤ 2*r) :
    N < 2*r := by
  simp only [hasseInterval, Set.mem_setOf_eq] at hHasse
  by_contra hcon
  rw [not_lt] at hcon
  have hN : (2*r : ℤ) ≤ (N : ℤ) := by exact_mod_cast hcon
  have h0 : (0 : ℤ) ≤ 2*r - (q+1) := by linarith
  have h1 : 2*(r : ℤ) - (q+1) ≤ (N : ℤ) - (q+1) := by linarith
  have hmono : (2*(r : ℤ) - (q+1))^2 ≤ ((N : ℤ) - (q+1))^2 := pow_le_pow_left₀ h0 h1 2
  linarith

/-- The Hasse bound for a short-Weierstrass elliptic curve `E` over a finite field `F` with
`q = #F`: `|#E(F) - (q+1)| ≤ 2·√q`, written sqrt-free over `ℤ` as `(#E(F) - (q+1))² ≤ 4·q`,
where `#E(F) = Nat.card (SWPoint E)`.

This is Hasse's theorem, the "Riemann hypothesis for elliptic function fields":

> H. Hasse, *Zur Theorie der abstrakten elliptischen Funktionenkörper III: Die Struktur des
> Meromorphismenrings; Die Riemannsche Vermutung*, Journal für die reine und angewandte
> Mathematik (Crelle's Journal) *175* (1936), 193–208. doi:10.1515/crll.1936.175.193.

The point-count form used here is §4.2 (p. 206): for `N₁` the number of degree-one prime divisors
(`= #E(F)`, the `F`-rational places including `𝒪`) and `q = #F`, `(q + 1 - N₁)² ≤ 4q`. It rests on
§3.1 (p. 203), where the Frobenius meromorphism `π : (x, y) ↦ (x^q, y^q)` satisfies
`Q(π) = π² - lπ + q = 0` with `l² ≤ 4q`. A scan of part III is available at
https://download.uni-mainz.de/mathematik/Algebraische%20Geometrie/Lehre/WS23.Padische.Hasse.III.pdf

Mathlib does not yet carry this for `WeierstrassCurve`, so we define the statement and take it
as a hypothesis where needed. -/
def HasseBound {F : Type*} [Field F] [Fintype F] (E : SWCurve F) : Prop :=
  Nat.card (SWPoint E) ∈ hasseInterval (Fintype.card F)

/-- `SWPoint E` is finite whenever the base field is: it is a subtype of `F × F`
(`SWPoint.equivSubtype`). -/
instance instFiniteSWPoint {F : Type*} [Field F] [DecidableEq F] [Fintype F] (E : SWCurve F) :
    Finite (SWPoint E) :=
  Finite.of_equiv _ (SWPoint.equivSubtype E).symm

/-- **Order of a prime-order short-Weierstrass curve group, via Hasse.** Given Hasse's bound
(assumed), a prime `r`, a non-identity point `P` with `r • P = 0`, and the concrete gap
`4q < (2r - (q+1))²` together with `q + 1 ≤ 2r`, the curve group has exactly `r` points. -/
theorem card_eq_of_hasse {F : Type*} [Field F] [DecidableEq F] [Fintype F] (E : SWCurve F)
    {r : ℕ} (hrPrime : r.Prime) {P : SWPoint E} (hP : P ≠ 0) (hPr : r • P = 0)
    (hHasse : HasseBound E)
    (hgap : 4*(Fintype.card F : ℤ) < (2*r - (Fintype.card F + 1))^2)
    (hle : (Fintype.card F : ℤ) + 1 ≤ 2*r) :
    Nat.card (SWPoint E) = r :=
  card_eq_of_prime_witness hrPrime hP hPr (lt_two_mul_of_hasse hHasse hgap hle)

/-! ## Alternative approach that reaches the same conclusion -/

/-- Convenience form of `lt_two_mul_of_hasse` for callers who already hold the two-sided Hasse
bound. For `37 ≤ q` (the least prime power for which `2·(q + 1 - 2√q) > q + 1 + 2√q`), the
explicit gap inequalities are implied by the Hasse bound on `r` itself: a `r` in the Hasse interval
`[q + 1 - 2√q, q + 1 + 2√q]` has `2r ≥ 2·(q + 1 - 2√q) > q + 1 + 2√q ≥ N`, so `N < 2r`.

The Hasse bound on `r` (`hr`) is essential — `37 ≤ q` alone is unsound. A witness of small prime
order (e.g. an order-2 point on a group of composite order in the interval) would otherwise force a
wrong conclusion; `hr` pins `r` to the interval from below, ruling that out. -/
theorem lt_two_mul_of_hasse_of_field_ge_37 {N q r : ℕ}
    (hN : N ∈ hasseInterval q)
    (hr : r ∈ hasseInterval q)
    (hq : 37 ≤ q) :
    N < 2*r := by
  simp only [hasseInterval, Set.mem_setOf_eq] at hN hr
  have hq' : (36 : ℤ) < q := by exact_mod_cast hq
  by_contra hcon
  rw [not_lt] at hcon
  have hcon' : 2 * (r : ℤ) ≤ (N : ℤ) := by exact_mod_cast hcon
  -- Writing `n = N - (q+1)`, `m = r - (q+1)`: from `hN`/`hr`, `(n - 2m)² ≤ 3n² + 6m² ≤ 36·q`
  -- (the `sq_nonneg (n+m)` hint supplies `-4nm ≤ 2(n² + m²)`); but `N ≥ 2r` gives `n - 2m ≥ q+1`,
  -- so `(q+1)² ≤ (n-2m)² ≤ 36·q`, contradicting `37 ≤ q` (where `(q+1)² > 36·q`).
  nlinarith [hN, hr, hq', hcon',
    sq_nonneg ((N : ℤ) - (q+1) + ((r : ℤ) - (q+1))),
    mul_nonneg (show (0 : ℤ) ≤ (N : ℤ) - 2*r by linarith)
               (show (0 : ℤ) ≤ (N : ℤ) - 2*r + 2*((q : ℤ)+1) by linarith)]

/-- Curve-level capstone of the `37 ≤ #F` route: combine `HasseBound` (assumed) with `37 ≤ #F` and
the Hasse bound on the prime `r` to conclude the curve group has exactly `r` points, without the
caller having to supply the explicit gap inequalities `hgap` and `hle`.

`hHasse` is definitionally the two-sided bound on `#E(F)` that `lt_two_mul_of_hasse_of_field_ge_37`
needs; see there for why `hr` is needed. -/
theorem card_eq_of_hasse_of_field_ge_37 {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (E : SWCurve F) {r : ℕ} (hrPrime : r.Prime) {P : SWPoint E} (hP : P ≠ 0) (hPr : r • P = 0)
    (hHasse : HasseBound E)
    (hr : r ∈ hasseInterval (Fintype.card F))
    (hq : 37 ≤ Fintype.card F) :
    Nat.card (SWPoint E) = r :=
  card_eq_of_prime_witness hrPrime hP hPr (lt_two_mul_of_hasse_of_field_ge_37 hHasse hr hq)

end CompElliptic.CurveOrder
