# ConjecturesArxiv formalization workspace

This directory contains the Lean 4 workspace used to formalize selected solver proof attempts from the main `conjectures-arxiv` repository.

## Build

From this directory:

```sh
lake build
lake build ConjecturesArxiv
```

To build a single module:

```sh
lake build QuasimodularSturm
lake build HilbertDepth
lake build MagnitudeDisproof
lake build GeneralSGDMomentDisproof
lake build SteinDisproof
lake build XiZeroLimit
```

## Main library file

[ConjecturesArxiv.lean](ConjecturesArxiv.lean) re-exports the currently active modules:

- `QuasimodularSturm`
- `HilbertDepth`
- `MagnitudeDisproof`
- `GeneralSGDMomentDisproof`
- `SteinDisproof`
- `XiZeroLimit`

## Structure

The workspace is organized as follows:

- `QuasimodularSturm/`: the original quasimodular-Sturm formalization files.
- top-level modules such as `HilbertDepth.lean` and `SteinDisproof.lean`: independent Lean formalizations for individual solver attempts.
- `XiZeroLimit/`: auxiliary modules for the Xi zero-limit formalization.
- `notes/`: markdown notes describing scope, caveats, and verification status for each attempt.

## Current modules

- [HilbertDepth.lean](HilbertDepth.lean): full formalization of Attempt 10, proving all four product inequalities from Conjecture 4.1 in the Hilbert-depth paper.
- [MagnitudeDisproof.lean](MagnitudeDisproof.lean): full formalization of the explicit `F = {0,1}` counterexample for Attempt 9.
- [GeneralSGDMomentDisproof.lean](GeneralSGDMomentDisproof.lean): full formalization of two Attempt 16 disproof routes. For the substantive route, we first shore up the conjecture by restoring the mean-zero noise assumption omitted from the printed A6 and then move to the simplest repaired case: `h = 2` and `f(x) = x^2 / 2`. In that setting the SGD recursion becomes the linear update `X_(k+1) = (1 - α) X_k + α ξ_(k+1)`. Lean then formalizes the counterexample itself by constructing explicit centered dyadic heavy-tail noise with finite third moment but infinite sixth moment, proving that the iterate laws converge to the stationary series `∑ n, α (1 - α)^n ξ_n`, and showing that this limit law still has infinite sixth moment. The same file also formalizes a separate disproof of the literal printed statement via deterministic noise on a one-point probability space, exposing the missing centering assumption that lets the iterates drift to infinity.
- [SteinDisproof.lean](SteinDisproof.lean): full formal disproof of the literal printed Stein-equation conjecture for Attempt 3.
- [XiZeroLimit.lean](XiZeroLimit.lean): full formalization of the adapted-`\widetilde\Xi_n` zero-limit theorem for Attempt 22, up to the file's explicit nonzero scalar normalization and solver indexing.
- [XiZeroLimit/Analytic.lean](XiZeroLimit/Analytic.lean): analytic Bernoulli and Dirichlet-beta bridge lemmas used by the Xi zero-limit proof.
- [QuasimodularSturm/DiagonalCriterion.lean](QuasimodularSturm/DiagonalCriterion.lean): abstract diagonal criterion used in the quasimodular Sturm-bound investigation.
- [QuasimodularSturm/Concrete.lean](QuasimodularSturm/Concrete.lean): concrete low-weight `E_2, E_4, E_6` model for the quasimodular Sturm-bound attempt.
- [QuasimodularSturm/Basic.lean](QuasimodularSturm/Basic.lean): small shared lemmas used by the quasimodular-Sturm files.

## Notes

These notes explain scope, caveats, and verification status for the formalization attempts:

- [notes/HilbertDepthNotes.md](notes/HilbertDepthNotes.md)
- [notes/MagnitudeDisproofNotes.md](notes/MagnitudeDisproofNotes.md)
- [notes/GeneralSGDMomentDisproofNotes.md](notes/GeneralSGDMomentDisproofNotes.md)
- [notes/SteinDisproofNotes.md](notes/SteinDisproofNotes.md)
- [notes/XiZeroLimitNotes.md](notes/XiZeroLimitNotes.md)
- [notes/QuasimodularSturmNotes.md](notes/QuasimodularSturmNotes.md)

Some notes describe completed formal verifications of the solver argument or counterexample. Others describe partial formalizations or formalization attempts that exposed a gap in the original solver proof.
