# Naming conventions in cryptographic and circuit libraries

A survey of how established elliptic-curve and zero-knowledge-circuit libraries name the
abstractions CompElliptic needs to name, carried out to keep CompElliptic's terminology consistent
with the Zcash Protocol Specification and with common cryptographic-engineering usage (see
[Design principles in the README](../README.md#design-principles)). Terminology here feeds the
choice of Lean type names for the distinct abstraction levels: group element, internal (coordinate)
representation, byte sequence, bit sequence, circuit representation, and coordinates.

## Libraries surveyed

- **Formal / Lean:** Mathlib, ArkLib (Verified-zkEVM), Clean (Verified-zkEVM).
- **Geometry reference:** the Explicit-Formulas Database (EFD).
- **Rust trait stacks:** zkcrypto `ff` / `group` / `pairing`; RustCrypto `elliptic-curve`; arkworks
  `ark-ec` / `ark-serialize`.
- **Rust concrete curves:** `curve25519-dalek`, `bls12_381`, `k256` / `p256`.
- **Rust circuit layers:** arkworks `ark-r1cs-std`, halo2 (`halo2_proofs`, `halo2_gadgets`,
  `halo2curves`) including the Zcash (ECC) and Privacy & Scaling Explorations (PSE) forks,
  `halo2-lib` / `halo2-ecc` (Axiom), `bellman` and the Zcash Sapling circuit gadgets, ragu
  (Project Tachyon).
- **Other circuit frameworks:** gnark, circom / circomlib, Noir.
- **Classic C / C++:** RELIC, BLST, libff, OpenSSL, MIRACL, libsodium.
- **Standards:** RFC 9380 (hashing to elliptic curves), RFC 9496 (ristretto255 / decaf448), and the
  Ristretto explainer (ristretto.group).

## Consensus vocabulary

| Concept | Dominant term(s) |
| --- | --- |
| The mathematical group element | **point** (universal); group-centric type names `G1` / `blst_p1` in pairing libraries |
| Coordinate scheme | **coordinate system**: **affine** / **projective** / **Jacobian** (/ Chudnovsky / López–Dahab / extended) — universal |
| Non-injective coordinates | explicitly **equivalence classes** (projective `(X : Y : Z)` notation signals "a class") |
| Conversion to the unique form | **normalize** / `norm`, **to-affine**, **make-affine** |
| Byte / wire form | **encoding**, **serialize**, **compress(ed)** / **uncompressed** |
| Affine x, y getters | **coordinates** (a narrow accessor concept, not a type) |
| In-circuit value | **variable** / **Var**, **assigned (cell)**, **wire**, **witness** |

Two cautions stand out for a library that wants unambiguous names:

1. **"Repr" / "representation" is badly overloaded.** It means at least four different things across
   widely used libraries (see the dedicated section below). CompElliptic should avoid "Repr" for the
   coordinate-quotient layer.
2. **Affine versus projective is the one distinction everyone makes**, and the cleanest libraries
   make it with *distinct types plus explicit conversions* (BLST `blst_p1` vs `blst_p1_affine`;
   Mathlib `Projective.Point` vs `Affine.Point`), rather than a runtime tag (RELIC's `coord` field).

## Concept by concept

### Field elements and their representations

- **zkcrypto `ff`:** `Field`, `PrimeField`; the associated type **`PrimeField::Repr`** is *"the byte
  representation of a field element"* — a fixed-length byte array (`AsRef<[u8]>`), via `to_repr` /
  `from_repr` (the latter *"failing if the input is not canonical"*). A separate *bit* view is
  `PrimeFieldBits::ReprBits`. So in this stack **`Repr` = canonical byte serialization of a scalar**.
- **RustCrypto:** `AffineCoordinates` exposes `x() -> FieldRepr` where `FieldRepr: AsRef<[u8]>` — a
  field-element *byte* string.
- **Clean (Lean):** field elements are just the circuit's `F`; the `Variable` / `Expression F`
  distinction (not a "Repr") carries the in-circuit-vs-concrete split.

### Group elements ("points")

- Every library calls the mathematical object a **point**. Type names split into point-centric
  (`EC_POINT`, `ECP`, `ep_t`, dalek `EdwardsPoint`) and group-centric (`G1`, `blst_p1`, arkworks
  `CurveGroup`, zkcrypto `Group`).
- **arkworks:** `Group` / `PrimeGroup` (generic), `CurveGroup` = *"an opaque representation of an
  elliptic curve group element suitable for efficient group arithmetic"* (the fast, non-unique form).
- **zkcrypto `group`:** `Group` = *"an element of a cryptographic group"*; `PrimeGroup` /
  `PrimeCurve` for prime order.
- **Mathlib:** no neutral group-element type — each coordinate system has its own `Point`
  (`Affine.Point`, `Projective.Point`, `Jacobian.Point`), linked by `...AddEquiv`.

### Coordinate systems (the internal representation)

- **EFD** is the canonical reference and organizes everything by **coordinate system**: affine,
  projective, Jacobian, Chudnovsky Jacobian, and so on, each with its own explicit formulas. Affine
  is listed as one coordinate system among the others, not as a privileged base.
- Projective and Jacobian points are described everywhere as **equivalence classes** of tuples
  (`(X : Y : Z) = (sX : sY : sZ)`); the colon notation exists precisely to flag the equivalence.
  This is exactly the quotient CompElliptic's coordinate-system abstraction models, with the affine
  case being the degenerate one where the equivalence is equality.
- **arkworks:** `Affine` and `Projective` concrete types; `AffineRepr` = *"the canonical
  representation ... the affine coordinates of the point"* (the unique representative, slow
  arithmetic) versus `CurveGroup` (fast, non-unique). Two model modules: `short_weierstrass`
  (Jacobian projective) and `twisted_edwards` (extended coordinates).
- **zkcrypto `group`:** `Curve` = *"efficient representation of an elliptic curve point"* (the
  projective form), `CurveAffine` / `PrimeCurveAffine` = *"affine representation"*; conversions
  `to_affine()` / `to_curve()`.
- **halo2curves:** `CurveAffine` (*"used for serialization, storage, and inspection of x and y
  coordinates"*) versus `CurveExt` (*"'projective' form, where arithmetic is usually more
  efficient"*), linked by the `AffineExt` / `CurveExt` associated types ("Ext" = the extended /
  projective group element).
- **bls12_381 / k256 / p256:** `G1Affine` / `G1Projective`, `AffinePoint` / `ProjectivePoint` — bare
  name or `Projective` suffix = projective, `Affine` suffix = affine.
- **BLST:** distinct structs `blst_p1` (projective, has `x, y, z`) versus `blst_p1_affine` (`x, y`);
  the type *is* the representation. **RELIC** instead tags the representation at runtime with a
  `coord` field (`RLC_AFFINE` / `RLC_PROJC` / `RLC_JACOB`).
- **Mathlib:** `Projective.Point` is literally `{ point : PointClass R, nonsingular }`, where
  `PointClass` is the scaling-orbit quotient — i.e. Mathlib already builds the projective point type
  as a quotient of representatives, per coordinate system, exactly as proposed here.

### Coordinate accessors

- **RustCrypto:** `AffineCoordinates` with `x()` and `y_is_odd()` (no `y()`); the word
  **coordinates** is reserved for this accessor.
- **halo2curves:** `Coordinates<C>` = *"the affine coordinates of a point"*, accessors `x()` / `y()`
  (with `u()` / `v()` aliases); `from_xy()` (*"failing if not on the curve"*), `is_on_curve()`.
- **OpenSSL / MIRACL:** `EC_POINT_get_affine_coordinates`, `ECP_affine`.

### Serialisation: byte and bit encodings

- **zkcrypto `group`:** `GroupEncoding` with associated type **`Repr` = "the encoding of group
  elements"** (a byte array); `UncompressedEncoding` for the uncompressed form. So here **`Repr` =
  the byte encoding of a point** — the opposite of arkworks' usage.
- **arkworks:** `CanonicalSerialize` / `CanonicalDeserialize`, `serialize_compressed` /
  `serialize_uncompressed`, governed by `Compress` and `Validate` enums; custom types implement
  `Valid`.
- **dalek:** dedicated wrapper types `CompressedEdwardsY` / `CompressedRistretto`, via `compress()` /
  `decompress()`.
- **Classic libs:** "compress" (x plus a sign bit) versus "serialize" / `write_bin` / `point2oct` /
  `toBytes` (full); OpenSSL's `point_conversion_form_t` enum (`COMPRESSED` / `UNCOMPRESSED` /
  `HYBRID`) is the canonical taxonomy. libsodium folds it away entirely — *"points are represented as
  their Y coordinate"* and validity is *"canonical form, on the main subgroup"*.
- **ArkLib (Lean):** a two-parameter `Serialize α β` / `Deserialize α β` / `Serde α β` class family
  with `β = ByteArray` or `BitVec n`, plus `Serialize.IsInjective`.
- **Zcash spec §5.4.9** names this bundle a **represented group**: a group together with `repr_𝔾`
  and a partial `abst_𝔾` such that `abst ∘ repr = id`. Note `repr_𝔾 : 𝔾 → 𝔹^[ℓ]` yields a
  **bit-sequence** serialization (`𝔹^[ℓ]` is a sequence of `ℓ` bits); a byte serialization is a
  further, separate step. This is the term CompElliptic reserves for the encoding bundle.
- **RFC 9496** (ristretto255 / decaf448) makes exactly CompElliptic's group-element-vs-representation
  distinction, and even uses the term: an *"element encoding"* is *"the unique reversible encoding of
  a group element"*, and an *"internal representation"* is *"a point on the curve used to implement
  ristretto255"* (extended coordinates `(x, y, z, t)`). `Encode` / `Decode`, 32-byte (octet) strings,
  with *"non-canonical values rejected"* on decode — a canonical encoding. ristretto255 is framed as
  a *"prime-order group"* abstraction over a cofactor-8 curve. RFC 9380 (hash-to-curve) speaks of
  *"points with affine coordinates (x, y)"* in the prime-order subgroup `G`, with the
  `hash_to_field` / `map_to_curve` / `clear_cofactor` / `hash_to_curve` pipeline, `I2OSP` / `OS2IP`
  for integer-octet conversion; it explicitly *"does not cover serialization"* of points.

### In-circuit representations

- **arkworks `ark-r1cs-std`:** the **`Var` suffix** is the universal marker for an in-circuit value:
  `CurveVar` (*"a variable that represents a curve point"*), `ProjectiveVar { x, y, z }`,
  `AffineVar { x, y, infinity }`, `FpVar`, `EmulatedFpVar`. Subgroup membership is explicit at
  allocation: `new_variable` enforces it, `new_variable_omit_prime_order_check` does not.
- **halo2:** layered. `Assigned<F>` = a field value stored as a fraction for batched inversion;
  `Value<V>` = a maybe-known witness; `Cell` = a grid location; `AssignedCell<V, F>` = a value bound
  to a cell. The `ecc` gadget then offers `Point` (*"a point on a specific elliptic curve"*) versus
  `NonIdentityPoint` (*"guaranteed to not be the identity"*), backed by `EccPoint` /
  `NonIdentityEccPoint` (*"represented in affine (x, y) coordinates ... each coordinate is assigned to
  a cell"*), and `X` for a lone coordinate. This `Point` / `NonIdentityPoint` / `AssignedCell`
  split is the best precedent for distinguishing a raw cell-pair from a validated, non-identity
  point — directly relevant to CompElliptic's anchoring-bug concern.
- **halo2-lib / halo2-ecc (Axiom):** `EcPoint { x, y }` (affine, generic non-native `FieldPoint`
  coordinates), with `StrictEcPoint` / `ComparableEcPoint` variants; in-circuit values are
  `AssignedValue<F>` in a `Context`.
- **bellman:** `Variable` (*"a variable in our constraint system"*, `Index::Input` vs `Index::Aux`),
  `AllocatedNum { value, variable }`, `Num` (linear-combination-backed), `AllocatedBit`, and
  `Boolean::{Is, Not, Constant}` (the explicit constant-vs-variable split). "Allocated..." = witnessed
  in-circuit value; "Constant" = literal.
- **Zcash Sapling gadgets** (`sapling-crypto` circuit): in-circuit Jubjub points are
  `EdwardsPoint { u, v }` (twisted-Edwards coordinates named `u`, `v`, each an `AllocatedNum`) and
  `MontgomeryPoint { x, y }`. The raw-versus-validated distinction is carried by the *constructor*:
  `witness` (*"guarantees the point is on the curve"*) and `interpret` (validate already-allocated
  coordinates), with `assert_not_small_order` as a further check.
- **gnark:** `AffinePoint { X, Y }` / `G1Affine`, coordinates `frontend.Variable` (native) or
  `emulated.Element` (non-native); deliberately *"we do not check the point is on the curve"*.
- **circom / circomlib:** points are individual `signal`s (`x`, `y` or `Ax`, `Ay`); on-curve checks
  are separate templates (`BabyCheck`), not types.
- **Noir:** `EmbeddedCurvePoint { x, y, is_infinite }`; identity is a boolean flag.
- **ragu (Project Tachyon):** abstracts the synthesis backend behind a `Driver`; the in-circuit
  value is an opaque **`Wire`** (*"deliberately opaque ... cannot be compared or manipulated"*), with
  `Maybe` as the maybe-known-witness analogue of halo2's `Value`, and `Gadget` / `GadgetKind` for
  reusable components. No exposed cell or coordinate accessor surface.

### The "Repr" / "representation" overload — caution

The same token carries incompatible meanings across the most-used libraries:

| Identifier | Library | Meaning |
| --- | --- | --- |
| `AffineRepr` | arkworks `ark-ec` | the canonical **affine point** (a coordinate form) |
| `GroupEncoding::Repr` | zkcrypto `group` | the **byte encoding** of a point |
| `PrimeField::Repr` | zkcrypto `ff` | the **byte serialization** of a scalar |
| `AffineCoordinates::FieldRepr` | RustCrypto | a field-element **byte string** |
| `GroupRepresentation` | ArkLib (AGM) | an **algebraic-group-model linear combination** |

Because of this, CompElliptic avoids "Repr" for the coordinate-quotient layer, and — where it does
use "representation" — pins the meaning (byte representation, internal representation, ...).

### "Encoding": the scheme (map) versus the encoded value — caution

A second overload bites inside CompElliptic's own `Encoding.lean`: "encoding" names both the *map*
(the `CanonicalEncoding` bundle, and the `encode` / `decode` functions) and the *value* that map
produces (an element of the value type `D` — "a valid result of encoding"). The surveyed libraries
always separate the two, but they disagree on which role keeps the word:

| Identifier / phrase | Library | "encoding" (or synonym) denotes |
| --- | --- | --- |
| `Encodable`, `encode` / `decode` | Mathlib | the **map / scheme** (the value is a bare `ℕ`, unnamed) |
| `GroupEncoding` (trait) | zkcrypto `group` | the **scheme** |
| `GroupEncoding::Repr` = *"the encoding of group elements"* | zkcrypto `group` | the **value** (a byte array) |
| *"element encoding"* = *"the unique reversible encoding of a group element"* | RFC 9496 | the **value** |
| `Encode` / `Decode` | RFC 9496 | the **map** |
| `repr_𝔾` / `abst_𝔾`; *"the representation of P"* | Zcash spec §5.4.9 | map (`repr` / `abst`) versus value (*"representation"*) |
| `CompressedEdwardsY`; `compress()` / `decompress()` | dalek | value (the wrapper type) versus map (the methods) |

No convention dominates: Mathlib and the trait names use "encoding" / "encodable" for the scheme;
zkcrypto's `Repr`, RFC 9496's "element encoding", and the spec's "representation" use it (or a
synonym) for the value. What is universal is that the distinction is *drawn* — the two roles get
*different* names (scheme: a trait or `Encodable`; value: `Repr` / "element encoding" / a
`Compressed…` wrapper).

**Recommendation for CompElliptic.** Give the two roles two words:

- **"encoding" is the scheme** — the `CanonicalEncoding` bundle and the `encode` / `decode` maps ("a
  canonical encoding of `G` into `D`"). This matches Mathlib's `Encodable` and incurs no rename. The
  scheme is always *qualified* — `CanonicalEncoding` (the everyday type) or `LenientEncoding` (an
  explicit sibling, for the rare consensus-enshrined lenient case) — with no bare `Encoding` type to
  reach for, so the canonical-versus-lenient choice is always made deliberately (no weak default).
- **"depiction" is the encoded value** — an element of `D`. The verb form is natural and
  relational: `encode g` is "the (canonical) depiction of `g`", and "`r` is a depiction of `g`" iff
  `decode r = some g`. The tagged types refine it: `Canonical e` and `Decodable e` are checked
  depictions (members of `canonicalSet` / `decodableSet`), and `Raw e` is an unchecked one.

"Depiction" is a deliberate coinage. No surveyed library uses it, so it carries no prior meaning —
which is exactly the point: the natural synonym, "representation", is four-ways overloaded (preceding
section) and "encoding" is the word we are trying to free. A reader must learn it once, but it is
self-explanatory and reads well in the relational form that "codeword" and "encoded value" do not
("codeword of `g`" is ungrammatical; "encoded value of `g`" is clunky). The coding-theory **codeword**
(member of the **code**) remains a recognized synonym to mention in passing.

Whichever value-noun is chosen, values should still be named by their **type** (`D`, `Raw e`,
`Canonical e`, `Decodable e`) wherever a type can stand in, per the distinct-types principle.

The runner-up is to flip the word entirely — "encoding = value" (following zkcrypto `Repr` and RFC
9496) and rename the scheme `Codec` (an encode-plus-decode pair) or `EncodingScheme`. It reads
naturally at value sites ("a valid encoding") but renames the central structure and diverges from
`Encodable`.

## Implications for CompElliptic naming

- The two orthogonal axes have stable names: **curve shape / form** (Weierstrass, Edwards,
  Montgomery — already CompElliptic's `CurveForms/`) and **coordinate system** (affine, projective,
  Jacobian). EFD's "coordinate system" is the natural name for the layer that bundles a carrier, a
  validity predicate, an equivalence, and the group formulas — i.e. the structure currently called
  `GroupRep`.
- The **group element** is a "point" everywhere; non-injective coordinate systems are genuinely
  equivalence classes, matching the quotient construction.
- The **byte / bit** layer is "encoding" / "serialization"; the bundle of a group with its encoding
  is precisely the spec's **represented group** (§5.4.9), so that name is reserved for it and not for
  the coordinate quotient.
- Within that layer, the two senses of "encoding" are split: **"encoding" is the scheme/map**
  (`CanonicalEncoding`, `encode` / `decode`), and **"depiction" is the encoded value** (an element
  of `D`; `encode g` is the canonical depiction of `g`). Not "representation" for the value (Repr
  overload). See the caution above.
- The **circuit** layer should follow halo2's `Point` / `NonIdentityPoint` (validated, on-curve,
  non-identity) over raw assigned cells, and arkworks' `Var` marker for "in-circuit value", so that
  the raw-cell-pair-versus-validated-point distinction — the locus of the NU6.2 anchoring bug — is a
  type-level distinction (the *No hidden mistakes* principle).

## Sources

Geometry and the Zcash specification:

- Explicit-Formulas Database — <https://www.hyperelliptic.org/EFD/>
- D. J. Bernstein, "The Explicit-Formulas Database" (slides) — <https://cr.yp.to/talks/2007.09.05/slides.pdf>
- Zcash Protocol Specification §5.4.9 (represented groups and pairings) — <https://zips.z.cash/protocol/protocol.pdf#concretepairing>

Standards:

- RFC 9380, Hashing to Elliptic Curves — <https://www.rfc-editor.org/rfc/rfc9380.html>
- RFC 9496, The ristretto255 and decaf448 Groups — <https://www.rfc-editor.org/rfc/rfc9496.html>
- Ristretto — <https://ristretto.group>

Formal / Lean:

- Mathlib elliptic-curve docs — <https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.html>, <https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.html>, <https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.html>
- ArkLib — <https://github.com/Verified-zkEVM/ArkLib>
- Clean — <https://github.com/Verified-zkEVM/clean>

Rust trait stacks (zkcrypto / RustCrypto / arkworks):

- `ff` — <https://docs.rs/ff/latest/ff/>
- `group` — <https://docs.rs/group/latest/group/>
- `pairing` — <https://docs.rs/pairing/latest/pairing/>
- `elliptic-curve` — <https://docs.rs/elliptic-curve/latest/elliptic_curve/>
- `ark-ec` — <https://docs.rs/ark-ec/latest/ark_ec/>
- `ark-serialize` — <https://docs.rs/ark-serialize/latest/ark_serialize/>
- `ark-r1cs-std` — <https://docs.rs/ark-r1cs-std/latest/ark_r1cs_std/>
- zkcrypto org / RFCs — <https://github.com/zkcrypto>

Rust concrete curves:

- `curve25519-dalek` — <https://docs.rs/curve25519-dalek/latest/curve25519_dalek/>
- `bls12_381` — <https://docs.rs/bls12_381/latest/bls12_381/>
- `k256` — <https://docs.rs/k256/latest/k256/>

Circuit layers:

- `halo2_proofs` — <https://docs.rs/halo2_proofs/latest/halo2_proofs/>
- `halo2_gadgets` — <https://docs.rs/halo2_gadgets/latest/halo2_gadgets/>
- `halo2curves` — <https://docs.rs/halo2curves/latest/halo2curves/>; PSE fork — <https://github.com/privacy-scaling-explorations/halo2curves>
- halo2 (Zcash / ECC) — <https://github.com/zcash/halo2>; halo2 (PSE) — <https://github.com/privacy-scaling-explorations/halo2>
- `halo2-lib` / `halo2-ecc` — <https://github.com/axiom-crypto/halo2-lib>
- `bellman` — <https://docs.rs/bellman/latest/bellman/>, <https://github.com/zkcrypto/bellman>
- Zcash Sapling circuit — <https://github.com/zcash/sapling-crypto>
- ragu (Project Tachyon) — <https://github.com/QED-it/ragu>, <https://tachyon.z.cash/ragu/>

Other circuit frameworks:

- gnark — <https://github.com/Consensys/gnark>, <https://docs.gnark.consensys.io/>
- circomlib — <https://github.com/iden3/circomlib>
- Noir — <https://noir-lang.org/docs/>, <https://github.com/noir-lang/noir>

Classic C / C++:

- RELIC — <https://github.com/relic-toolkit/relic>
- BLST — <https://github.com/supranational/blst>
- libff — <https://github.com/scipr-lab/libff>
- OpenSSL `EC_POINT` — <https://docs.openssl.org/master/man3/EC_POINT_new/>
- MIRACL Core — <https://github.com/miracl/core>
- libsodium point arithmetic — <https://doc.libsodium.org/advanced/point-arithmetic>
