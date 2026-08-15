# OEIS A112521 — Lean proof for Formal Conjectures

This repository contains a complete, hypothesis-free Lean proof of the theorem
currently registered as
[`OeisA112521.conjecture`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/112521.lean):

```lean
∀ (n : ℕ), n ≥ 1 → (OeisA112521.a n : ℤ) = OeisA112521.T n n
```

The exported theorem is:

```lean
OeisA112521Proof.formal_conjectures_target
```

`OeisA112521.conjecture_solved` is a thin entry point with exactly the upstream
statement and the proposed `@[category research solved, AMS 11]` annotation.

## Status

Complete and kernel-checked. There are no bridge hypotheses such as
`SignedSumBridge` or `DiagonalBridge`. The development does not use `sorry`,
`admit`, custom axioms, `native_decide`, or the upstream open conjecture.

The axiom audit reports only the standard mathlib dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

## Proof outline

Write

```text
S(d) = Σ_{0 ≤ j ≤ d} (-1)^j C(2j,j) C(2d-j,d-j).
```

The proof has four parts.

1. Define homogeneous Fibonacci polynomials
   `H₀ = 1`, `H₁ = v`, `Hₘ₊₂ = vHₘ₊₁ + u²Hₘ`, then apply the linear change
   `v = x + y`, `u = x - y`. Their coefficients satisfy exactly the recursive
   equation defining the Formal Conjectures array `T`.
2. Use iterated partial derivatives and a commuting-operator binomial
   expansion to prove that the main diagonal is `S`:
   `T (d+1) (d+1) = S(d)`.
3. Prove a Wilf–Zeilberger telescoping identity. It yields, for `n ≥ 3`,

   ```text
   5n(n+1) S(n+1)
     = 2n(2n+1) S(n) + 4(16n²-1) S(n-1).
   ```

   Together with the four explicit initial cases, this proves `0 ≤ S(d)`.
4. Rewrite the signed sum inside `OeisA112521.a (d+1)` as `S(d)`. The
   nonnegativity result removes `Int.toNat`, and the two exact identities finish
   the target theorem.

All identities used in the WZ step, including both boundary terms, are proved
in Lean.

## Files

| Path | Purpose |
|---|---|
| `lean/OeisA112521Proof.lean` | Complete proof, including the coefficient argument, WZ certificate, positivity, and final theorem |
| `lean/OeisA112521FC.lean` | Small Formal Conjectures entry point and axiom audit |
| `lean4web/OeisA112521Lean4Web.lean` | Single-file, Mathlib-only copy containing the definitions, complete proof, and final theorem; ready to paste into Lean4Web |

Both Lake projects pin Lean `v4.27.0` and Formal Conjectures commit
`230782e37bbf5aa0cab03874e876626beacac009`.

## Verification

Formal Conjectures build:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Lean4Web/project build:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

For Lean4Web, copy the complete contents of
`lean4web/OeisA112521Lean4Web.lean` into one editor buffer. It imports only
`Mathlib`; no sibling source file or Formal Conjectures package is required.

## Sources

- [OEIS A112521](https://oeis.org/A112521)
- [Formal Conjectures `OEIS/112521.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/112521.lean)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## License

Apache License 2.0. See `LICENSE`.

## AI usage disclosure

This development was prepared with assistance from OpenAI Codex.
