# TODO

Tracking list for the CompElliptic library and for the Orchard elliptic-curve circuit-soundness
verification that motivates it (CompElliptic itself is a general-purpose computable-EC library).
Entries are brief; design context lives in the module doc-comments and in the Claude project
memory `project_orchard_ecc_lean_verification`.

## Design principles (foundational)

These are fixed; see also `README.md`.

1. **One Lean type per abstraction level**, kept distinct: *group element* (the mathematical
   notion); *internal representation* of a group element (a quotient in general — valid coordinate
   representatives modulo an equivalence: equality for affine forms, non-trivial for projective /
   Jacobian); *byte-sequence* representation; *bit-sequence* representation; *circuit* representation
   (can be several, typically two field elements); and *coordinates* (field elements tagged with
   which kind of coordinate they are).
2. **Conversions between these types are always explicit** — no hidden coercions across abstraction
   levels.
3. **Terminology follows the Zcash Protocol Specification and common cryptographic usage** (which do
   not conflict). In particular the
   [Zcash Protocol Specification §5.4.9](https://zips.z.cash/protocol/protocol.pdf#concretepairing)
   "represented group" = a group bundled with its `repr` / `abst` encoding (`repr_𝔾` maps to a
   bit sequence; a byte encoding is a further step), so that name is reserved for the encoding bundle,
   not the coordinate quotient (which is the "internal representation" layer).
4. **No class of mistake you can make in a cryptographic protocol is hidden by the API** — the type
   discipline turns each potential error (non-canonical encoding treated as canonical, raw
   coordinates used as a group element without the on-curve check, circuit cells not anchored to
   their source, ...) into a visible, type-level obligation. Keep historical warts (e.g. Sapling's
   non-canonical-encoding acceptance) out of the core abstractions, as separate lenient layers.

Secondary criterion (ranked below the four above; may be in tension): the type a spec writer reaches
for as a *group element* should not be horribly inefficient for general computation. It may be
*implemented* in a more efficient coordinate system (inversion-free projective / Jacobian, complete
formulas) so long as it abstractly means "group element". So the canonical computable group element
should be projective/Jacobian-backed, not affine (affine `add` needs a field inversion per op, so the
affine-backed `smul` is the "horribly inefficient" case); affine is a coordinate system for encoding
/ readability, reached by explicit conversion.

## Design decisions (settled)

- **Style: rich typing / correct-by-construction**, à la carte per curve form and coordinate
  system (mirroring `Zcash/Math/CtEdwards.lean`). Each form bundles its validity conditions into
  the type so illegal states are unrepresentable; we implement each form rather than seek a general
  *representation*. Generality comes at a *represented-group* / pairing abstraction that each form
  implements — and that is also where quotients/setoids belong (e.g. projective/Jacobian
  representative-equivalence; trivial for affine forms). "Elliptic ⊂ Weierstrass" is a **subtype**,
  not a quotient. (Contrast Mathlib: it keeps `WeierstrassCurve` un-bundled plus an `IsElliptic`
  *mixin* because its scope needs singular curves, bad reduction, families, base change — generality
  we scope out. Current Mathlib has *no* bundled `EllipticCurve` type; it went fully to the mixin,
  and is moving toward an even lighter `abbrev IsElliptic := IsUnit Δ`.)
- **Curve form = module; directory split by axis.** Two orthogonal axes get two directories:
  `CompElliptic/CurveForms/` holds one module per curve *form* (`ShortWeierstrass` now; `CtEdwards`
  and `Montgomery` anticipated — both needed if/when we formalize Sapling, whose Jubjub curve has
  twisted-Edwards and Montgomery forms), and `CompElliptic/Curves/` holds specific *named* curves as
  instances (`Pasta` = Pallas/Vesta now; `Jubjub` later). `CompElliptic/Fields/` holds the fields.
  (All three directory names plural.) Within a form module, layer: raw computable kernel (functions
  on `F × F`) → rich bundled types (`SWCurve` / `SWPoint`) → group structure; concrete-curve
  instances live in `Curves/`.
- **Typed interfaces everywhere, including the circuit.** Gadget instances and witnesses carry
  point / scalar types (as halo2 itself does: `Point` / `NonIdentityPoint` / `EccPoint`,
  `ScalarVar` / `ScalarFixed`, x-only `X`), not flat field elements; coordinate access is the
  explicit exception. Two distinct bundlings: *math point* (values + on-curve) vs *circuit point*
  (cells); soundness bridges them. **Anchoring is not subsumed by the type** — `NonIdentityPoint`
  encodes on-curve / non-identity, but *which cells* a point is copy-constrained to is a cell-level
  property (the NU6.2 bug was a well-typed point whose cells were not anchored to the input base).
  So the model keeps cells and copy-constraints explicit even with typed interfaces.
- **Binary fields (char 2): deferred, not precluded.** Zcash uses none, so no work now. Short
  Weierstrass is the wrong form for char 2 anyway, and `SWCurve.IsElliptic = IsUnit sw_Δ`
  self-excludes it (`sw_Δ = 0` in char 2 since `16 ≡ 0`, and `IsUnit 0` is false) — graceful, no
  special-casing. Keep `[Field F]` generic (NOT `CharZero` — Pasta is a large-prime field, not
  char-zero — and no char-specific typeclasses bolted on preemptively) and keep the
  represented-group abstraction characteristic-agnostic, so a future long / binary-Weierstrass form
  module can support char 2 for other CompElliptic users.

## CompElliptic — fields

- [x] Pasta base/scalar prime fields (`Fields/Pasta.lean`) with Lucas/Pratt primality
  certificates, in the style of CompPoly's `Fields/Secp256k1.lean`: `PallasBaseField`,
  `PallasScalarField` = `VestaBaseField`, `VestaScalarField`, each with a `Field` instance. The
  certificates are generated by `scripts/gen_pratt.py` from the `p-1` / `q-1` factorizations
  (PARI/GP). Machine-verified, no `sorry`.

## CompElliptic — short-Weierstrass form (`CurveForms/ShortWeierstrass.lean`)

File layout (done): the short-Weierstrass form lives in one module, namespace
`CompElliptic.CurveForms.ShortWeierstrass` (raw kernel + transport + rich types); concrete
Pallas/Vesta `SWCurve` instances live in `Curves/Pasta.lean`, namespace `CompElliptic.Curves.Pasta`
(with `Pallas` / `Vesta` nested), depending on `Fields/Pasta.lean` (namespace
`CompElliptic.Fields.Pasta`). Namespaces mirror the directory path throughout. The earlier
single-directory `Curve/` layout (a `Weierstrass.lean` raw kernel plus a `Group.lean` for rich
types + transport) has been consolidated into these and removed.

- [x] Raw computable kernel: `OnCurve`, `neg`, complete `add` (`(0,0) ≡ 𝒪`), spec-level `smul`
  (iterated add), `native_decide` sanity. `not_onCurve_zero` proved (needs `b ≠ 0`).
- [x] Identity/inverse laws (Lean-checked, no `sorry`): `zero_add`, `add_zero`, `neg_neg`,
  `add_neg`.
- [x] Mathlib transport foundation (validated, builds): `toW` (short-form `WeierstrassCurve`),
  `equation_toW` (`Equation ↔ OnCurve`), `nonsingular_toW` (`OnCurve → Nonsingular`, via
  `equation_iff_nonsingular [IsElliptic]`).
- [x] Rich bundled types: `sw_Δ = -16(4A³ + 27B²)`; `SWCurve` bundling `IsElliptic : IsUnit sw_Δ`
  AND `B_nonzero : B ≠ 0` (for the `𝒪 = (0,0)` sentinel); `SWPoint (E : SWCurve F)` parameterized
  by the curve (like `CtEdwardsPoint`), bundling `Valid E.A E.B (x, y)` (`OnCurve ∨ (0,0)`), with
  `SWPoint.zero` and a `Zero` instance. The bundled fields discharge the hypotheses the raw lemmas
  need, so the earlier "correctness caveat" (generic `(a b)` lemmas false on singular curves) is
  resolved by construction. `origin_not_on_curve` (`¬ OnCurve A B (0,0)`) is immediate from `B ≠ 0`.
- [x] Group laws — raw-kernel workhorses with explicit `[(toW A B).IsElliptic]` / `b ≠ 0` hyps
  (Lean-checked, no `sorry`; each depends only on `propext` / `Classical.choice` / `Quot.sound`):
  - closure (`valid_add`): via `add_eq_addXY` (our `add` = Mathlib `addX` / `addY` for the
    short form) + `nonsingular_add` ⟹ on-curve.
  - `add_comm`: direct — generic branch is pure field algebra (`field_simp` / `ring`); doubling
    branch forces `p = q` from on-curve (`y₁² = y₂²` with `y₁ + y₂ ≠ 0`); `𝒪` branches from the
    identity laws. No Mathlib group needed.
  - `add_assoc`: transport via `toPt : F × F → (toW A B).Point` (with coordinate left-inverse
    `ofPt`) and the homomorphism `toPt_add`, inheriting Mathlib's `AddCommGroup`. Needs `b ≠ 0` so
    the `(0, 0)` sentinel maps to `0`.
  - [x] `AddCommGroup (SWPoint E)` instance: `sw_add` / `sw_neg` lifted via `valid_add` / `valid_neg`,
    `toW_Δ` + `instIsElliptic` bridging `E.IsElliptic` to `(toW E.A E.B).IsElliptic`, and the raw
    laws transported through `SWPoint.ext_pair`. So `+`, `-`, `0`, and `n • P` / `k • P` work on
    `SWPoint E` for any `SWCurve`.
  - [x] closure of the raw `smul` (`valid_smul`, induction on `valid_add`) and `coords_nsmul`
    relating the group action `n • P` to the spec-level `smul` on the underlying coordinates.
- [x] Non-residue `five_not_isSquare` (Euler's criterion `ZMod.euler_criterion`: `5 ^ (p / 2) = -1
  ≠ 1`) ⟹ no Pallas point has `x = 0` (`no_onCurve_x_zero`), in `Curves/Pasta.lean` — the spec
  §5.4.9.7 property the `(0,0) ≡ 𝒪` representation relies on. The power is evaluated by
  `reduce_mod_char` (fast modexp via `NormNum.PowMod`); finished with `decide`. (Earlier `decide`
  `maxRecDepth` failures were from missing the `import Mathlib.NumberTheory.LegendreSymbol.Basic`
  and applying `decide` directly to the un-reduced power.)
- [x] Pallas `SWCurve` instance (`A = 0`, `B = 5`) in `Curves/Pasta.lean`; `IsElliptic` via
  `isUnit_iff_ne_zero` + `native_decide` (Pallas `sw_Δ = -10800 ≠ 0`), `B ≠ 0` by `decide`.
- [x] Vesta `SWCurve` instance (identical, over the Vesta base field), with its own
  `five_not_isSquare` / `no_onCurve_x_zero` (`5` is a non-residue in the Vesta base field too).
- [ ] A windowed / double-and-add `smul` matching the circuit's scalar decomposition. (The
  iterated-add `smul` is adequate for *stating* soundness; the circuit's structure is what the
  gadget proofs reduce to.)

## CompElliptic — other forms & the group abstraction (later)

- [x] Coordinate-system abstraction (`CoordinateSystem.lean`): carrier + `Valid` + `Rel` + ops →
  derived `AddCommGroup` on the quotient. The locus of generality; the setoid/quotient that
  non-injective coordinate systems need lives here. Affine is the `Rel = Eq` instance.
- [ ] Projective (and/or Jacobian) coordinate system with inversion-free complete formulas,
  transported to Mathlib's `Projective.Point` group, designated the canonical efficient group element
  (`Point`); explicit `toAffine` / `fromAffine` conversions. (Per the efficiency criterion.)
- [ ] Represented group (spec §5.4.9): a group-element type bundled with `repr` / `abst` as a
  canonical bijection. The serialization type is a *parameter*: support byte-oriented protocols
  *directly* (no forced bit-sequence detour) as well as Zcash's bit-oriented
  `repr_𝔾` → bits → `LEBS2OSP` → bytes. Distinct bit-sequence / byte-sequence types; explicit
  endianness-bearing conversions named after the spec primitives (`LEBS2OSP` etc.) — bit ordering is
  a mistake class (a Sapling testnet bug). Sapling's non-canonical-encoding acceptance goes in a
  separate lenient `abst'` layer.
- [ ] Pairings (will be needed eventually): a represented-pairing abstraction — a bilinear
  `e : G₁ × G₂ → G_T` (the spec's §5.4.9 also covers represented pairings) — and a pairing-friendly
  curve such as BLS12-381 (used by Sapling / Groth16). Mathlib has `WeierstrassCurve` pairing
  material and the zkcrypto `pairing::Engine` shape is a naming reference.
- [ ] AGM (Algebraic Group Model) group representation (will likely be needed): the notion that any
  group element an algebraic adversary outputs comes with a *representation* as a linear combination
  of the group elements it has seen — ArkLib's `AGM.GroupRepresentation` is exponents plus a proof
  the target equals that combination. Needed for knowledge-soundness / extractor arguments. Likely
  import or adapt from ArkLib rather than reinvent. NB: this is a *third* sense of "representation"
  (distinct from coordinate and byte representations) — keep the naming distinct.
- [ ] Twisted Edwards form (`CurveForms/CtEdwards.lean`; port/adapt `Zcash/Math/CtEdwards.lean` —
  complete addition, so closure and commutativity are near-syntactic). Needed for Sapling (Jubjub).
- [ ] Montgomery form (`CurveForms/Montgomery.lean`) and x-only ladder if/when a gadget needs them.
  Also a Sapling/Jubjub need.
- [ ] Jubjub as a named curve (`Curves/Jubjub.lean`) once the Edwards/Montgomery forms exist.

## Tooling and conventions

- [ ] Script (under `scripts/`) to check, and update in place, the copyright/licence header on
  every source file (`*.lean`, `*.py`): verify each file starts with the canonical dual-licence
  header (Apache 2.0 or MIT, `LICENSE-APACHE` / `LICENSE-MIT`, `Authors:` line) in the right comment
  syntax for its language, and rewrite stale or missing headers. Run it in CI / as a pre-commit
  check. (Motivated by `Basic.lean` having drifted to an Apache-only, `LICENSE`-referencing header.)
- [ ] Add the `LICENSE-APACHE` and `LICENSE-MIT` files the headers reference (they do not yet exist).

## Constraint model (Plonkish)

- [ ] Build the gadget-soundness layer on `wg-plonkish` (zkpstandard; Maller / Grigg / Béguier),
  which models Plonkish gates with first-class copy constraints — the anchoring-faithful model
  needed here. Align toolchains (it is on `v4.22.0-rc3`; bring it up to CompElliptic's
  `v4.30.0-rc2`).
- [ ] Adapt the soundness / refinement framing from `Zcash/Proofs/Relations.lean` (the one
  cleanly reusable piece of the prior Zcash Lean explorations).

## Orchard ECC gadget soundness — the goal (lands in `Zcash.Orchard`, on wg-plonkish + CompElliptic)

Per-gadget obligation: (1) intended relation; (2) soundness (constraints ⟹ relation);
(3) input-anchoring (every input copy-constrained to its source); (4) exceptional-case
unreachability (where incomplete formulas are used); (5) completeness (secondary). In dependency
order:

- [ ] `witness_point` — on-curve, `(0,0) ≡ 𝒪`, non-identity.
- [ ] `add_incomplete` — `P + Q` for `P ≠ ±Q`.
- [ ] `add` (complete) — full case split.
- [ ] `mul/incomplete` (`q_mul_1/2/3`) — double-and-add; **anchoring** of the incomplete-loop
  base (the NU6.2 variable-base soundness bug). Likely rests on `distinct_x_axis_symmetric` and
  `odd_order_double_inj` from `Zcash/Math/{Curves,Groups}.lean`.
- [ ] `mul/complete` + `mul/overflow` + LSB — assembling `[k]·base` and the `k = α + t_q`
  overflow handling.
- [ ] `mul_fixed` — "Running sum coordinates check" plus the `full_width` / `base_field_elem`
  (canonicity) / `short` (signed) variants.
- [ ] Sinsemilla `hash_to_point` — incomplete additions + generator-table base anchoring.

## Possible upstreaming

- [ ] The Pasta fields and the computable short-Weierstrass group law fill a gap in the
  Verified-zkEVM ecosystem (ArkLib's only curve is a noncomputable Mathlib BN254; CompPoly has no
  curve content at all — confirmed: its only secp256k1 file is the two prime fields). Candidate
  contribution back upstream, once the axioms are established.
