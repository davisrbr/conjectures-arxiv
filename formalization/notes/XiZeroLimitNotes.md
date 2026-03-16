# Attempt 22 Lean Formalization Notes

This note documents the Lean formalization for Attempt 22, the confirmation of the `\widetilde\Xi_n` smallest-zero conjecture from "Algebraic representatives of the ratios `ζ(2n+1)/π^{2n}` and `β(2n)/π^{2n-1}`."

## Scope

The Lean development is in:

- [../QuasimodularSturm/Attempts/XiZeroLimit.lean](../QuasimodularSturm/Attempts/XiZeroLimit.lean)
- [../QuasimodularSturm/Attempts/XiZeroLimitAnalytic.lean](../QuasimodularSturm/Attempts/XiZeroLimitAnalytic.lean)

The main theorem is:

- `xi_smallestRoot_tendsto_zero_of_solverRawAdaptedXi`

The main Xi-specific bridge theorems are:

- `solverRawAdaptedXi_eq_solverSechXiExact`
- `solverRawAdaptedXi_coeff_ratio_eq_secantEulerRatioShift`
- `solverRawAdaptedXi_roots_nonempty`
- `solverRawAdaptedXi_roots_pos`
- `solverRawAdaptedXi_roots_card`

The Lean object `solverRawAdaptedXi n = rawAdaptedXi (n + 2)` is the paper's adapted Xi family
`\widetilde\Xi_n`, presented in the solver indexing and up to the explicit nonzero scalar
normalization recorded in the file. That normalization preserves the positive zeros and the
coefficient ratio `-coeff 1 / coeff 0`, so it does not change the conjecture being proved.

What is now formalized end to end is the full proof of the adapted-Xi smallest-zero statement:

- the explicit coefficient formula for the adapted Xi polynomial in terms of type-B Eulerian data,
- the identification of that coefficient-defined family with the odd `sech` derivative model,
- the positive-root and root-count statements needed for the smallest-root argument,
- the exact coefficient-ratio identity in terms of secant-Euler data, via the Bernoulli /
  Dirichlet-beta bridge,
- the corrected finite-root endgame turning reciprocal-root growth into `\beta_n \to 0`.

## Match To The Solver Attempt

This is not a literal line-by-line transcription of the solver writeup, because the solver's step

`sum_j 1 / y_{n,j} >= 1 / beta_n`

is true but too weak on its own to force `beta_n -> 0` by itself.

The Lean development makes that issue explicit and replaces it with the stronger averaged inequality
that is actually needed:

- `inv_smallestValue_le_sumInv` formalizes the weak inequality itself,
- `smallestValue_le_card_div_sumInv` formalizes the stronger averaged inequality that is actually
  needed,
- `neg_deriv_scaledRootProduct_div_eq_sumInv` formalizes the exact log-derivative identity from the
  factorized polynomial,
- `xi_logDerivRatio_from_auxiliary_data` formalizes the exact algebra needed to reach the Euler-ratio
  formula once the Taylor and auxiliary-function identities are available.

So the right reading is: this is a full formalization of the corrected proof of the paper's
adapted-Xi conjecture, not of the solver's one-line too-weak implication taken in isolation.

## What Is Not Yet Formalized

What is not formalized is the rest of the surrounding paper beyond this conjecture.

In particular, this note should not be read as claiming a formalization of:

- the entire paper's notation layer for both `\Xi_n` and `\widetilde\Xi_n` beyond the adapted-Xi
  family needed here,
- the paper's broader zero-distribution results beyond the smallest-positive-zero limit,
- the follow-up literature on the full `\widetilde\Xi_n` zero distribution.

The conjecture itself is formalized, but the whole paper is not.

## Verification

The formalization is re-exported from [../QuasimodularSturm.lean](../QuasimodularSturm.lean).

`~/.elan/bin/lake build QuasimodularSturm.Attempts.XiZeroLimit` succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.

`~/.elan/bin/lake env lean /Users/davisbrown/conjectures-arxiv/formalization/QuasimodularSturm/Attempts/XiZeroLimit.lean`
succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.
