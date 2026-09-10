/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.Pasta.Fast.Projective.Core

/-!
# Projective (Renes–Costello–Batina) point arithmetic for Vesta

The Vesta instantiation of the field-generic projective core
(`CompElliptic.Curves.Pasta.Fast.Projective.Core`): `PVes` is `Core.PPoint 𝔽_q`, and every
operation and lemma below is the generic one specialized at the Vesta base field and curve. The
completeness hypotheses the core threads — no 2-torsion (`Vesta.no_onCurve_y_zero`), `2 ≠ 0`,
`5 ≠ 0` — and the curve coefficients `Vesta.curve.A = 0`, `Vesta.curve.B = 5` are discharged once,
here, and fed to the generic results.

The one genuinely Vesta-specific piece is `paddFast`: the raw-`ℕ` compiled spelling of `padd` at
the Vesta base-field modulus, with `padd_eq_paddFast` its proven equality.

The `Fast` interfaces are provisional: they are not guaranteed to remain public, and
may be folded into the existing API or otherwise changed incompatibly.
-/

open CompElliptic
open CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta

namespace CompElliptic.Curves.Pasta.Fast.Projective

/-- The Vesta base field `𝔽_q` (= `PallasScalarField`), over which the Vesta curve is defined. -/
abbrev Fq := CompElliptic.Fields.Pasta.VestaBaseField

/-- The downstream affine group: on-curve points of Vesta with the complete affine group law. -/
abbrev G := SWPoint Vesta.curve

/-- A projective point in `(X : Y : Z)` coordinates over `𝔽_q`, from the generic core. -/
abbrev PVes := Core.PPoint Fq

namespace PVes

/-! ## The Vesta curve facts feeding the generic core -/

/-- Vesta's curve coefficient `A = 0`. -/
theorem hA : Vesta.curve.A = 0 := rfl

/-- Vesta's curve coefficient `B = 5`. -/
theorem hB : Vesta.curve.B = 5 := rfl

/-- `2 ≠ 0` in the Vesta base field. -/
theorem htwo : (2 : Fq) ≠ 0 := by decide

/-- `5 ≠ 0` in the Vesta base field. -/
theorem hfive : (5 : Fq) ≠ 0 := by decide

/-- Vesta has no 2-torsion: no curve point with `y = 0` (`Vesta.no_onCurve_y_zero`). -/
theorem hy0 : ∀ x : Fq, ¬ OnCurve 0 5 (x, 0) := Vesta.no_onCurve_y_zero

/-! ## Operations, specialized from the core -/

/-- Renes–Costello–Batina complete addition, at Vesta. -/
abbrev padd : PVes → PVes → PVes := Core.PPoint.padd

/-- Scalar (representative) rescaling, at Vesta. -/
abbrev smul : Fq → PVes → PVes := Core.PPoint.smul

/-- The projective identity `𝒪 = (0 : 1 : 0)`. -/
abbrev pid : PVes := Core.PPoint.pid

/-- The homogeneous projective curve equation, at Vesta. -/
abbrev OnCurveP : PVes → Prop := Core.PPoint.OnCurveP

/-- A representable projective point: on the projective curve and not the zero vector. -/
abbrev Valid : PVes → Prop := Core.PPoint.Valid

/-- Affine interpretation as a raw coordinate pair. -/
abbrev aff : PVes → Fq × Fq := Core.PPoint.aff

/-- Interpret a projective point as an element of the affine group `G`. -/
abbrev toAffine : PVes → G := Core.PPoint.toAffine Vesta.curve hA hB

/-- Materialize an affine group element as a projective representative. -/
abbrev ofAffine : G → PVes := Core.PPoint.ofAffine Vesta.curve

/-- Binary double-and-add scalar multiplication over `PVes`. -/
abbrev pnsmulFast : ℕ → PVes → PVes := Core.PPoint.pnsmulFast

/-- The packaged fast scalar multiplication on `G`, through projective coordinates. -/
abbrev smulFast : ℕ → G → G := Core.PPoint.smulFast Vesta.curve hA hB

/-! ## Lemmas, specialized from the core -/

/-- The identity `(0 : 1 : 0)` is valid. -/
theorem valid_pid : Valid pid := Core.PPoint.valid_pid

/-- Validity is preserved by `padd` (closure). -/
theorem valid_padd {P Q : PVes} (hP : Valid P) (hQ : Valid Q) : Valid (padd P Q) :=
  Core.PPoint.valid_padd hy0 htwo hP hQ

/-- `aff` is a homomorphism from `padd` to the affine group law on valid inputs. -/
theorem aff_padd {P Q : PVes} (hP : Valid P) (hQ : Valid Q) :
    aff (padd P Q) = add 0 (aff P) (aff Q) :=
  Core.PPoint.aff_padd hy0 htwo hP hQ

/-- **General equivalence.** The RCB sum interprets affinely as the complete affine sum, and
stays valid. -/
theorem padd_spec {P Q : PVes} (hP : Valid P) (hQ : Valid Q) :
    aff (padd P Q) = add 0 (aff P) (aff Q) ∧ Valid (padd P Q) :=
  Core.PPoint.padd_spec hy0 htwo hP hQ

@[simp] theorem toAffine_pid : toAffine pid = 0 := Core.PPoint.toAffine_pid Vesta.curve hA hB

/-- **The homomorphism.** `toAffine` carries the projective RCB addition to the affine group law. -/
theorem toAffine_padd {P Q : PVes} (hP : Valid P) (hQ : Valid Q) :
    toAffine (padd P Q) = toAffine P + toAffine Q :=
  Core.PPoint.toAffine_padd Vesta.curve hA hB hy0 htwo hP hQ

/-- Every affine group element materializes to a valid projective representative. -/
theorem valid_ofAffine (p : G) : Valid (ofAffine p) :=
  Core.PPoint.valid_ofAffine Vesta.curve hA hB p

/-- `toAffine` is a left inverse of `ofAffine`. -/
theorem toAffine_ofAffine (p : G) : toAffine (ofAffine p) = p :=
  Core.PPoint.toAffine_ofAffine Vesta.curve hA hB p

/-- **Fast scalar multiplication is the genuine group action**, projectively. -/
theorem pnsmulFast_spec {P : PVes} (hP : Valid P) : ∀ n : ℕ,
    Valid (pnsmulFast n P) ∧ toAffine (pnsmulFast n P) = n • toAffine P :=
  Core.PPoint.pnsmulFast_spec Vesta.curve hA hB hy0 htwo hP

/-- **Correctness of `smulFast`:** it equals the affine scalar multiplication `n • p`. -/
theorem smulFast_eq (n : ℕ) (p : G) : smulFast n p = n • p :=
  Core.PPoint.smulFast_eq Vesta.curve hA hB hy0 htwo n p

/-! ## Fast compiled spelling of `padd` (compiled-tier only)

Compiled generically, every field operation in `padd` goes through boxed `CommRing (ZMod q)`
dictionary projections.  `paddFast` is the same closed forms over raw `ℕ` representatives with
fused mul-mod, and `padd_eq_paddFast` is the proven equality — the proven counterpart of
`implemented_by` — so `padd` stays the statement surface while compiled call sites run fast. -/

/-- The Vesta base-field order, the modulus of the raw-`ℕ` fast path (reducible so `ZMod qv`
unifies with `Fq`). -/
private abbrev qv : ℕ := CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD

private theorem qv_pos : 0 < qv := by decide

private instance : NeZero qv := ⟨qv_pos.ne'⟩

/-- Fused modular addition on canonical representatives. -/
@[inline] private def fadd (a b : ℕ) : ℕ := (a + b) % qv

/-- Fused modular multiplication: one GMP multiply, one GMP mod. -/
@[inline] private def fmul (a b : ℕ) : ℕ := (a * b) % qv

/-- Modular subtraction without hypotheses: `a + (q − b mod q) ≡ a − b`. -/
@[inline] private def fsub (a b : ℕ) : ℕ := (a + (qv - b % qv)) % qv

private theorem cast_fadd (a b : ℕ) : ((fadd a b : ℕ) : Fq) = (a : Fq) + (b : Fq) := by
  rw [fadd, ZMod.natCast_mod, Nat.cast_add]

private theorem cast_fmul (a b : ℕ) : ((fmul a b : ℕ) : Fq) = (a : Fq) * (b : Fq) := by
  rw [fmul, ZMod.natCast_mod, Nat.cast_mul]

private theorem cast_fsub (a b : ℕ) : ((fsub a b : ℕ) : Fq) = (a : Fq) - (b : Fq) := by
  rw [fsub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ qv_pos).le,
    ZMod.natCast_mod, ZMod.natCast_self]
  ring

private theorem cast_val (a : Fq) : ((ZMod.val a : ℕ) : Fq) = a :=
  ZMod.natCast_rightInverse a

/-- `padd` over raw `ℕ` representatives: same RCB closed forms, fused mul-mod, shared
subproducts. Statement-surface code should keep calling `padd`; the compiler substitutes this
body via `padd_eq_paddFast`. -/
def paddFast (P Q : PVes) : PVes :=
  let x1 := P.X.val; let y1 := P.Y.val; let z1 := P.Z.val
  let x2 := Q.X.val; let y2 := Q.Y.val; let z2 := Q.Z.val
  let y2sq := fmul y2 y2
  let z2sq := fmul z2 z2
  let x1y1 := fmul x1 y1
  let y1sq := fmul y1 y1
  let z1sq := fmul z1 z1
  let x2y2 := fmul x2 y2
  let y1z1 := fmul y1 z1
  let x1z1 := fmul x1 z1
  let y2z2 := fmul y2 z2
  let x2z2 := fmul x2 z2
  let x1sq := fmul x1 x1
  let x2sq := fmul x2 x2
  let X3 := fsub (fadd (fsub (fsub (fmul x1y1 y2sq) (fmul 15 (fmul x1y1 z2sq)))
                    (fmul 30 (fmul x1z1 y2z2)))
               (fsub (fmul y1sq x2y2) (fmul 15 (fmul z1sq x2y2))))
              (fmul 30 (fmul y1z1 x2z2))
  let Y3 := fsub (fadd (fadd (fmul y1sq y2sq) (fmul 45 (fmul x1sq x2z2)))
                    (fmul 45 (fmul x1z1 x2sq)))
              (fmul 225 (fmul z1sq z2sq))
  let Z3 := fadd (fadd (fadd (fadd (fadd (fmul y1sq y2z2) (fmul y1z1 y2sq))
                    (fmul 3 (fmul x1sq x2y2)))
                    (fmul 3 (fmul x1y1 x2sq)))
                    (fmul 15 (fmul y1z1 z2sq)))
                    (fmul 15 (fmul z1sq y2z2))
  ⟨(X3 : Fq), (Y3 : Fq), (Z3 : Fq)⟩

/-- **The fast spelling is `padd`.** NOT registered `@[csimp]`: in the current
`native_decide` tier, library calls execute through interpreted IR, where this raw-`ℕ`
spelling measured ~17× SLOWER than the typeclass path it replaces (1.5 ms vs 85 µs per
add — many small interpreted steps lose to few boxed GMP calls; the same effect that
makes interpreted Montgomery a 40× regression). The equality is kept for the compiled
tier: once the fast-field lib ships precompiled (`precompileModules` dylib), registering
this `@[csimp]` (or the Montgomery successor) makes every compiled call site (including
`native_decide` auxiliaries) run the fused raw-`ℕ` form. -/
theorem padd_eq_paddFast : @padd = @paddFast := by
  funext P Q
  simp only [padd, Core.PPoint.padd, paddFast, Core.PPoint.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cast_fadd, cast_fmul, cast_fsub, cast_val, Nat.cast_ofNat] <;> ring

end PVes
end CompElliptic.Curves.Pasta.Fast.Projective
