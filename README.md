# CompElliptic

Computable elliptic-curve abstractions for Lean 4, built in the style of (and on top of)
[CompPoly](https://github.com/Verified-zkEVM/CompPoly).

The aim is a *computable* development of finite fields and elliptic-curve group laws — across
multiple curve forms and coordinate systems, with correct-by-construction types — suitable for
reasoning about elliptic-curve arithmetic in formally verified settings, such as zero-knowledge
circuits. The first form is short Weierstrass over the Pasta (Pallas/Vesta) cycle.

## Design principles

CompElliptic follows four principles, chosen so that the type structure mirrors the cryptography and
makes mistakes visible rather than silent:

1. **One Lean type per abstraction level**, kept distinct: a *group element* (the mathematical
   notion); the *internal representation* of a group element (a quotient in general — valid
   coordinate representatives modulo an equivalence, which is equality for affine forms and
   non-trivial for projective or Jacobian forms); the *byte-sequence* representation; the
   *bit-sequence* representation; the *circuit* representation (there can be several, but typically
   two field elements); and *coordinates* (field elements tagged with which kind of coordinate they
   are).
2. **Conversions between these types are always explicit** — no hidden coercions that silently cross
   abstraction levels; every conversion is a named function.
3. **Terminology is consistent with the Zcash Protocol Specification and common cryptographic usage**
   (which do not conflict) — see the [naming survey](design/naming-survey.md).
4. **No class of mistake you can make in a cryptographic protocol is hidden by the API.** The type
   discipline exists to turn each potential error — treating a non-canonical encoding as canonical,
   getting an encoding's bit ordering (endianness) wrong, using raw coordinates as a group element
   without the on-curve check, or using circuit cells that are not anchored to their intended
   source — into a visible, type-level obligation.

A secondary criterion, ranked below the four above and sometimes in tension with them: the type a
specification writer reaches for as a *group element* should not be horribly inefficient for general
computation. It may be *implemented* in a more efficient coordinate system (inversion-free projective
or Jacobian, complete formulas) so long as it abstractly means "group element". So the canonical
computable group element should be projective- or Jacobian-backed, not affine — affine addition needs
a field inversion per operation, so the affine-backed scalar multiplication is the "horribly
inefficient" case — while affine is a coordinate system for encoding and readability, reached by
explicit conversion.

## Status

Early work in progress. Present so far:

- the Pasta (Pallas/Vesta) base and scalar prime fields, with machine-verified Pratt primality
  certificates (`CompElliptic/Fields/Pasta.lean`);
- a computable short-Weierstrass affine group law with correct-by-construction `SWCurve` /
  `SWPoint` types, with closure, commutativity, and associativity fully proved — associativity by
  transport to Mathlib's `WeierstrassCurve.Affine.Point` group (`CompElliptic/CurveForms/ShortWeierstrass.lean`);
- Pallas as a concrete `SWCurve` instance, with `5` shown to be a quadratic non-residue (so the
  curve has no point with `x = 0`) via Euler's criterion (`CompElliptic/Curves/Pasta.lean`).

The library currently builds with no `sorry`; the proved theorems depend only on the standard
`propext` / `Classical.choice` / `Quot.sound` axioms. Next steps (assembling the
`AddCommGroup (SWPoint E)` instance, the Vesta instance, and further curve forms) are tracked in
`TODO.md`.

## License

Dual-licensed under your choice of the Apache License, Version 2.0 or the MIT license.

## Acknowledgements

Claude Opus 4.8 was used in the development of this project.
