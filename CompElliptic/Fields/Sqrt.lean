/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Fields.Pasta
import Mathlib.FieldTheory.Finite.Basic

/-!
# Computable square roots in prime fields (Tonelli–Shanks)

A *computable* square root for any odd-characteristic prime field, via the **general** Tonelli–Shanks
algorithm, parameterised by the 2-adic factorisation `card-1 = 2^twoAdicity * oddPart` (`oddPart`
odd). This is the fully general case — `twoAdicity = 1` (i.e. `p ≡ 3 mod 4`) degenerates to the
closed form `a^((p+1)/4)` with no loop iterations — not a variant specialised to `p ≡ 1 mod 16`. We
are not optimising for speed or brevity, only for correctness and computability. It is a field-level
primitive (it knows nothing about curves) and a candidate for upstreaming to CompPoly; it lives here
for now so the Pasta point decoder (`abst`) can use it.

`TonelliShanks.sqrt?` is **self-validating**: it returns `some r` only after checking `r*r = a`,
so an incorrect `TonelliShanks` instance (wrong `rootOfUnity` / `oddPart`) yields `none`, never a
wrong root. *Soundness* (`sqrt?_mul_self`: anything it returns squares to `a`) follows unconditionally
from this. *Completeness* (a genuine square yields `some`) needs the loop invariant and a valid
instance, and is deferred — it will accompany the encoding round-trip lemmas.

The default `Monoid.npow` (`a^n`) is linear in `n`, so it cannot evaluate the `≈ 2²⁵³`-sized
exponents here. `fpow` is square-and-multiply (logarithmic), fast enough to `#eval`.

## References

The classical algorithm:

- A. Tonelli, "Bemerkung über die Auflösung quadratischer Congruenzen", Nachrichten von der Königl.
  Gesellschaft der Wissenschaften und der Georg-Augusts-Universität zu Göttingen, 1891, pp. 344–346.
  <https://eudml.org/doc/180329>
- D. Shanks, "Five number-theoretic algorithms", Proceedings of the Second Manitoba Conference on
  Numerical Mathematics, 1973, pp. 51–70. (The original is not available online; see Shanks' later
  notes at <https://homes.cerias.purdue.edu/~ssw/shanks.pdf>.)

The specific formulation implemented here is Algorithm 5 (the prime-field Tonelli–Shanks square
root, with the quadratic-residue test folded in) of — and is the algorithm `pallas.py` in
`zcash-test-vectors` cites:

- G. Adj and F. Rodríguez-Henríquez, "Square root computation over even extension fields", IACR
  Cryptology ePrint Archive, Report 2012/685, <https://eprint.iacr.org/2012/685> (later published
  in IEEE Transactions on Computers, 2014).

(Despite the title, this paper covers more cases than even extension fields.)
-/

namespace CompElliptic.Fields

/-- Square-and-multiply exponentiation: `fpow a n = a^n`, but logarithmic in `n` so it is
feasible to evaluate for large exponents (unlike `Monoid.npow`). -/
def fpow {F : Type*} [Monoid F] (a : F) : ℕ → F
  | 0 => 1
  | n + 1 => (if (n+1) % 2 = 1 then a else 1) * fpow (a*a) ((n+1) / 2)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) one_lt_two

theorem fpow_spec {F : Type*} [Monoid F] (a : F) (n : ℕ) : fpow a n = a^n := by
  induction a, n using fpow.induct with
  | case1 a => simp [fpow]
  | case2 a n ih =>
    rw [fpow, ih, ← pow_two, ← pow_mul]
    rcases Nat.mod_two_eq_zero_or_one (n+1) with h | h
    · rw [if_neg (by omega), one_mul]; congr 1; omega
    · rw [if_pos h, ← pow_succ']; congr 1; omega

/-- `iterSq c k = c^(2^k)`, by squaring `k` times. -/
def iterSq {F : Type*} [Monoid F] (c : F) : ℕ → F
  | 0 => c
  | k + 1 => iterSq (c*c) k

theorem iterSq_spec {F : Type*} [Monoid F] (c : F) (k : ℕ) : iterSq c k = c^(2^k) := by
  induction k generalizing c with
  | zero => simp [iterSq]
  | succ k ih => rw [iterSq, ih, ← pow_two, ← pow_mul, ← pow_succ']

/-- The least `k ≥ 1` with `b^(2^k) = 1`, searched up to `fuel` steps (returning the current
`k` if the fuel runs out). Used on `b` known to lie in the 2-power-torsion subgroup. -/
def leastPow2Order {F : Type*} [Monoid F] [DecidableEq F] (b : F) (fuel : ℕ) : ℕ :=
  go 1 (b*b) fuel
where
  go (k : ℕ) (b2k : F) : ℕ → ℕ
    | 0 => k
    | fuel + 1 => if b2k = 1 then k else go (k+1) (b2k*b2k) fuel

/-- Validity of Tonelli–Shanks data for `F`, as a predicate on the *bare components* (mirroring
`IsCanonical` for encodings): the 2-adic factorisation `card - 1 = 2^twoAdicity * oddPart` holds
with `oddPart` odd and `twoAdicity` positive, and `rootOfUnity` is a primitive `2^twoAdicity`-th
root of unity. -/
structure IsValidTonelliShanks {F : Type*} [Field F] [Fintype F]
    (twoAdicity oddPart : ℕ) (rootOfUnity : F) : Prop where
  /-- `card - 1 = 2^twoAdicity * oddPart`. -/
  card_eq : Fintype.card F = 2^twoAdicity * oddPart + 1
  /-- The odd part is odd. -/
  oddPart_odd : Odd oddPart
  /-- There is at least one factor of two (the field is not of characteristic 2). -/
  twoAdicity_pos : 0 < twoAdicity
  /-- `rootOfUnity` has multiplicative order exactly `2^twoAdicity`. -/
  rootOfUnity_order : orderOf rootOfUnity = 2^twoAdicity

/-- The data Tonelli–Shanks needs for a field `F`: the 2-adic factorisation
`card-1 = 2^twoAdicity * oddPart`, a primitive `2^twoAdicity`-th root of unity `rootOfUnity`
(equivalently `g^oddPart` for any quadratic non-residue `g`), bundled with a proof of their
validity (`IsValidTonelliShanks`). This ensures that a invalid instance cannot be constructed,
and completeness needs no separate hypothesis. -/
structure TonelliShanks (F : Type*) [Field F] [Fintype F] where
  /-- The 2-adic valuation `S` of `card-1`. -/
  twoAdicity : ℕ
  /-- The odd part `T` of `card-1 = 2^S * T`. -/
  oddPart : ℕ
  /-- A primitive `2^twoAdicity`-th root of unity (`g^oddPart` for a non-residue `g`). -/
  rootOfUnity : F
  /-- The data is valid for `F`. -/
  valid : IsValidTonelliShanks twoAdicity oddPart rootOfUnity

namespace TonelliShanks

/-- The Tonelli–Shanks main loop (the `while` of Algorithm 5 in Adj–Rodríguez-Henríquez; see the
module references): maintains `x` (the running square-root candidate), `b` (driven to `1`), `c`
(the paper's root of unity `z`), and `y` (the paper's `v`, the current 2-power bound). `fuel` bounds
the iteration count (`y` strictly decreases, so `twoAdicity` steps suffice). -/
def loop {F : Type*} [Field F] [DecidableEq F] (x b c : F) (y : ℕ) : ℕ → F
  | 0 => x
  | fuel + 1 =>
    if b = 1 then x
    else
      let k := leastPow2Order b y
      let w := iterSq c (y - k - 1)
      loop (x*w) (b * (w*w)) (w*w) k fuel

/-- Tonelli–Shanks square root. Returns `some r` with `r*r = a` when `a` is a square in `F`, and
`none` when it is not. Self-validating: the result is checked against `r*r = a` before being
returned. -/
def sqrt? {F : Type*} [Field F] [Fintype F] [DecidableEq F] (d : TonelliShanks F) (a : F) : Option F :=
  if a = 0 then some 0
  else
    -- Euler's criterion: `a` is a square iff `a^((card-1) / 2) = 1`, where `(card-1) / 2 = 2^(S-1) * T`.
    let pm1d2 := 2^(d.twoAdicity - 1) * d.oddPart
    if fpow a pm1d2 = 1 then
      let x := loop (fpow a ((d.oddPart + 1) / 2)) (fpow a d.oddPart) d.rootOfUnity d.twoAdicity
                    d.twoAdicity
      if x*x = a then some x else none
    else none

/-- **Soundness** of `sqrt?`: anything it returns squares to `a`. This holds for *any*
`TonelliShanks` data —even an invalid one— because `sqrt?` re-checks `r*r = a` before returning
`some r`. (Completeness —that a genuine square yields `some`— needs the loop invariant and a valid
instance, and is not proved here.) -/
theorem sqrt?_mul_self {F : Type*} [Field F] [Fintype F] [DecidableEq F] (d : TonelliShanks F)
    {a r : F} (h : d.sqrt? a = some r) : r*r = a := by
  simp only [sqrt?] at h
  split_ifs at h with h0 h1 hx <;> simp_all
  subst h
  simp only [mul_zero]

/-- **Completeness** of `sqrt?` (scaffold): for a valid instance, every square decodes to `some`.
The remaining `sorry` is the loop invariant (the loop produces an actual root). -/
theorem sqrt?_isSome_of_isSquare {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : TonelliShanks F) {a : F} (ha : IsSquare a) :
    ∃ r, d.sqrt? a = some r := by
  -- The residue-test exponent `2^(S-1) * T` is `(card-1) / 2`, and the field has odd order.
  have hodd : Fintype.card F % 2 = 1 := by
    have h2 : 2 ∣ 2^d.twoAdicity * d.oddPart :=
      (dvd_pow_self 2 d.valid.twoAdicity_pos.ne').mul_right d.oddPart
    rw [d.valid.card_eq]; omega
  have hchar : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_of_char_two h; omega
  have hexp : Fintype.card F / 2 = 2^(d.twoAdicity - 1) * d.oddPart := by
    have hpow : 2^d.twoAdicity = 2 * 2^(d.twoAdicity - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel d.valid.twoAdicity_pos]
    rw [d.valid.card_eq, hpow, mul_assoc]; omega
  simp only [sqrt?]
  split_ifs with h0 h1 hx
  · exact ⟨0, rfl⟩
  · exact ⟨_, rfl⟩
  · -- a ≠ 0, residue test passed, but `x*x ≠ a`: contradicted by the loop invariant.
    exact absurd (sorry : _ * _ = a) hx
  · -- a ≠ 0 and the residue test failed: contradicted by Euler's criterion for a square.
    exact absurd (by rw [fpow_spec, ← hexp]; exact (FiniteField.isSquare_iff hchar h0).mp ha) h1

open CompElliptic.Fields.Pasta in
/-- Tonelli–Shanks data for the Pallas base field `𝔽ₚ`: `p-1 = 2³² · T`, with `rootOfUnity = 5ᵀ`
(`pallas.py`). -/
def pallasBase : TonelliShanks PallasBaseField where
  twoAdicity := 32
  oddPart := 0x40000000000000000000000000000000224698fc094cf91b992d30ed
  rootOfUnity := 0x2bce74deac30ebda362120830561f81aea322bf2b7bb7584bdad6fabd87ea32f
  valid := {
    card_eq := by rw [ZMod.card]; native_decide
    oddPart_odd := by decide
    twoAdicity_pos := by decide
    rootOfUnity_order := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime_pow (p := 2) (n := 31) (by native_decide) (by native_decide)
  }

-- `√4 = ±2` (a square); `√5 = none` (5 is a non-residue, cf. `Pallas.five_not_isSquare`).
#eval (pallasBase.sqrt? 4).map (·.val)
#eval pallasBase.sqrt? 5
-- `√((-1)³ + 5) = √4`: the `y` of the test point `G = (-1, 2)`.
#eval (pallasBase.sqrt? ((-1 : Fields.Pasta.PallasBaseField)^3 + 5)).map (·.val)

end TonelliShanks

end CompElliptic.Fields
