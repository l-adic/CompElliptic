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
