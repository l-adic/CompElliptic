# CompElliptic

Computable elliptic-curve abstractions for Lean 4, built in the style of (and on top of)
[CompPoly](https://github.com/Verified-zkEVM/CompPoly).

The aim is a *computable* development of finite fields and elliptic-curve group laws — across
multiple curve forms and coordinate systems, with correct-by-construction types — suitable for
reasoning about elliptic-curve arithmetic in formally verified settings, such as zero-knowledge
circuits. The first form is short Weierstrass over the Pasta (Pallas/Vesta) cycle.

## Status

Early work in progress. Present so far:

- the Pasta (Pallas/Vesta) base and scalar prime fields, with machine-verified Pratt primality
  certificates (`CompElliptic/Fields/Pasta.lean`);
- a computable short-Weierstrass affine group law with correct-by-construction `SWCurve` /
  `SWPoint` types, identity and inverse laws proved, and a transport foundation to Mathlib's
  `WeierstrassCurve` for the remaining group axioms (`CompElliptic/CurveForms/ShortWeierstrass.lean`);
- Pallas as a concrete `SWCurve` instance (`CompElliptic/Curves/Pasta.lean`).

Group-law closure, commutativity, and associativity, together with the Pallas
quadratic-non-residue fact, are currently stated with `sorry`. See `TODO.md`.

## License

Dual-licensed under your choice of the Apache License, Version 2.0 or the MIT license.

## Acknowledgements

Claude Opus 4.8 was used in the development of this project.
