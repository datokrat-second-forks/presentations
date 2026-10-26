# Mathematics with Lean: Proof Mechanization as a Research Tool

Paul Reichert, Lean FRO

A [verso-slides](https://github.com/leanprover/verso-slides) deck with the shared Lean FRO theme
from `../static` (CSS, logos, title slide and per-slide header, wired up in `Main.lean`).

## Abstract

Over the last few years, it has become possible to write cutting-edge mathematical proofs in a form
that a computer can check, using a proof assistant such as Lean. This talk is for mathematicians who
are curious about what is often called the mechanization of proofs but have never tried it. After an
introduction to Lean, the talk focuses on the benefits of mechanization: gaining confidence in a
subtle argument, deciding whether a disputed proof deserves attention and, perhaps surprisingly,
clarifying and simplifying proofs. Community projects such as the Liquid Tensor Experiment serve as
examples. The talk ends with advice on how to get started. Depending on the interest of the
audience, we can also talk about why AI systems often write proofs in Lean and what this means for
the mathematical community.

## Building

```
lake build
lake env lean --run Main.lean
```

The output is written to `_slides/`. Serve it with a local web server, for example
`python3 -m http.server -d _slides`.

The slides import only the Mathlib modules they need, so building Mathlib from source stays
feasible when the Mathlib cache is not available. There is no `lean_exe`: linking an executable
would compile Mathlib natively. Rendering with `lean --run` only needs the oleans.

## Worked examples

`Examples/` contains three self-contained worked examples of elementary bounds. Each example
first proves a bound, then tightens it and shows which parts of the proof Lean rejects after the
change:

* `Examples/BaselBound.lean`: upper bounds `2`, `7/4` and `5/3` for the partial sums of `∑ 1/k²`.
* `Examples/EuclidPrimeBound.lean`: Euclid's bound on the `n`-th prime, `p n ≤ 2 ^ 2 ^ n`.
* `Examples/SqrtRecurrence.lean`: bounds for `a (n+1) = a n + 1 / a n`.

Like the slides, the examples import only the Mathlib modules they need. They are not part of
the default target. Build them with
`lake build Examples`.

## Worked examples

`Examples/` contains worked examples of tightening a bound, where Lean marks exactly the part of
the proof that breaks. Build them with `lake build Examples`. The slides on modifying a proof
follow `Examples/EuclidPrimeBound.lean`.
