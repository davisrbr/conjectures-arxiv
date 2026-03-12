# Attempt 9 Lean Formalization Notes

This note documents the Lean formalization for Attempt 9, the disconfirmation of Conjecture 6.3 in "Continuity of Magnitude at Skew Finite Subsets of `\ell_1^N`."

## Scope

The Lean proof is in [QuasimodularSturm/MagnitudeDisproof.lean](QuasimodularSturm/MagnitudeDisproof.lean).

The main theorems are:

- `kmsFour_det`
- `attemptNineDet_eq`
- `attemptNineDet_div_rsq_tendsto`
- `attemptNineDet_div_rsq_not_tendsto_conjectured`

What these theorems formalize is the explicit one-dimensional counterexample with `F = {0,1}`. For `0 < r < 1/2`, the vertex set of the cubical thickening is

`{-r, r, 1-r, 1+r}`.

The Lean file proves the determinant identity

`det(Z) = (1 - e^(-4r))^2 (1 - e^(-2(1-2r)))`

for the associated similarity matrix, and then proves

`det(Z) / r^2 -> 16 (1 - e^(-2))`.

Since `16 (1 - e^(-2)) != 16`, this formally disconfirms the conjectured leading coefficient in the case `N = 1`, `|F| = 2`, and `k = 2`.

## Match To The Solver Attempt

This is a full formalization of the explicit four-vertex disproof, not of every generalization discussed in the solver writeup.

The natural-language attempt also observed a more general one-dimensional formula for arbitrary ordered finite `F ⊂ \ell_1^1`. The current Lean development does not formalize that full `n`-point product formula. Instead, it specializes directly to the concrete `F = {0,1}` matrix and proves the exact determinant and limiting contradiction needed for the disproof.

So this note should be read as a completed formal verification of the explicit counterexample calculation itself.

## What Is Not Yet Formalized

The current Lean file does not yet formalize:

- the paper's full definitions of skewness and cubical thickening from first principles,
- the general ordered-point determinant formula in dimension `1`,
- the broader statement that every skew `F ⊂ \ell_1^1` with more than one point gives the wrong leading coefficient.

Those are natural next extensions, but they are not needed to refute the printed conjecture.

## Verification

The formalization is re-exported from [QuasimodularSturm.lean](QuasimodularSturm.lean).

`~/.elan/bin/lake build QuasimodularSturm.MagnitudeDisproof` succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.

`~/.elan/bin/lake build QuasimodularSturm` also succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.
