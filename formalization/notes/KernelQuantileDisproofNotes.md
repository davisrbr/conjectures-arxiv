# Attempt 2 Lean Formalization Notes

This note documents the current Lean state for Attempt 2, the kernel-quantile-discrepancy disproof project for Conjecture 152 in "Scalable Kernel-Based Distances for Statistical Inference and Integration."

## Scope

The Lean proof is in [../QuasimodularSturm/Attempts/KernelQuantileDisproof.lean](../QuasimodularSturm/Attempts/KernelQuantileDisproof.lean).

The main definitions and theorems are:

- `AttemptTwo.sortedFeature`
- `AttemptTwo.empiricalRankOneEKQD2`
- `AttemptTwo.tailKernel_diagonal_moment_finite`
- `AttemptTwo.paperEqFiveTailEKQD2`
- `AttemptTwo.OneDimPrintedConjecture152Data`
- `AttemptTwo.OneDimPrintedConjecture152Data.rhoP`
- `AttemptTwo.OneDimPrintedConjecture152Data.rhoQ`
- `AttemptTwo.PrintedConjecture152_d1_p2`
- `AttemptTwo.tailCounterexampleData_sideConditions`
- `AttemptTwo.rawRankOneTailWitness_le_empiricalRankOneEKQD2`
- `AttemptTwo.PrintedConjecture152_d1_p2_false`
- `AttemptTwo.tailKernel_counterexample_refutes_conjecture152`

## What Is Formalized

The file currently formalizes a fixed one-dimensional specialization of the printed conjecture and
checks one explicit rank-one tail-kernel counterexample data set end to end:

- the source space is fixed to `[0,1]`,
- `OneDimPrintedConjecture152Data` carries the actual front-end objects used by the paper-side
  notation: probability measures `P,Q,ν`, density witnesses for `ν,P,Q`, a Hilbert space `H`,
  evaluation maps `u(x)`, kernel sections `k(x, ·)`, and sampled directions standing in for the
  empirical `γ_L`,
- `OneDimPrintedConjecture152Data.rhoP` and `rhoQ` formalize the paper's H-valued directional
  quantiles `ρ^{α,u}_P = ρ^α_{u#P} u` and `ρ^{α,u}_Q = ρ^α_{u#Q} u`,
- the rank-1 feature is the explicit tail map
  `tailFeature x = sqrt (sqrt ((1 - x)^(-1)))`,
- `tailCounterexampleData_sideConditions` proves the concrete admissibility facts for this data:
  `ν = P = Q = volume` with density `1`, the rank-1 reproducing-kernel identities, and the
  balanced two-point direction law
  `γ = (1/2) δ_u + (1/2) δ_{-u}` together with the matching deterministic empirical direction
  measure used in the current specialization,
- `tailKernel_diagonal_moment_finite` proves the printed moment hypothesis for
  `k(x,y) = tailFeature x * tailFeature y`,
- `tau2Sq` is now defined from the actual H-norm gap between those directional quantiles, and
  `tau2Sq_eq_quantile_gap_formula` proves the scalar reduction used later in the rank-one
  specialization,
- `paperEqFiveTailEKQD2Sq` and `paperEqFiveTailEKQD2` formalize Equation (5) from the paper in the
  current rank-one two-sign specialization,
- `paperEqFiveTailEKQD2Sq_signedDirections_eq_empiricalRankOneEKQD2Sq` proves that the same
  empirical quantity is unchanged for any coordinatewise sign pattern `u_i ∈ {u,-u}`,
- `randomizedSignedDirectionAbsoluteError_eq_empiricalRankOneEKQD2` shows that even after averaging
  Equation (5) over an i.i.d. product sign law on those directions, the resulting absolute error is
  still exactly the same one-dimensional empirical rank-one discrepancy,
- `paperEqFiveTailEKQD2_eq_empiricalRankOneEKQD2` reduces that paper formula to the one-dimensional
  sorted projected-sample `L²` discrepancy,
- `PrintedConjecture152_d1_p2` is the `d = 1`, `p = 2` specialization encoded in the current file,
- and `PrintedConjecture152_d1_p2_false` proves that this specialized sentence is false for the
  current encoded data.

So the current final theorem
`AttemptTwo.tailKernel_counterexample_refutes_conjecture152`
is a mechanically checked disproof of that encoded `d = 1`, `p = 2` specialization with the
explicit admissible tail-kernel data above.

After checking the source text directly, the formalization treats the actual printed front-end
conditions as the conjecture states them: `ν` has a density, `P` and `Q` have densities bounded
away from zero, and the kernel diagonal `p/2` moments are finite. The extra bounded-kernel and
`J_p` integrability conditions appear only in the surrounding proof sketch and auxiliary lemma, not
in the conjecture statement itself, so they are not added as hypotheses.

## Relation To The Solver Attempt

This is still a substantive rank-1-kernel / one-dimensional empirical transport disproof. It is not
a wording-defect objection.

What changed relative to the solver writeup is the lower-bound mechanism. Instead of importing the
Gaussian empirical `W₂` theorem, the Lean file closes the disproof internally with an explicit
tail-kernel event that yields a slower empirical rate in the same rank-1 transport framework.

That means this file is not yet a formalization of the literal Gaussian Attempt 2 route from the
solver audit. In particular, it does not yet formalize:

- the inverse-CDF Gaussian witness `u(x) = Φ⁻¹(x)`,
- the exact reduction to empirical Gaussian `W₂`,
- or the Gaussian lower-rate theorem itself.

It should therefore be read as a checked surrogate disproof of the printed specialization, not yet
as the completed formalization of the intended Gaussian Attempt 2 argument or of the strongest
repaired version of the conjecture.

## Verification

The formalization is re-exported from [../QuasimodularSturm.lean](../QuasimodularSturm.lean).

`~/.elan/bin/lake build QuasimodularSturm.Attempts.KernelQuantileDisproof` succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.

At the moment, a full `~/.elan/bin/lake build` of the whole workspace is blocked by unrelated pre-existing errors in [../QuasimodularSturm/Attempts/XiZeroLimit.lean](../QuasimodularSturm/Attempts/XiZeroLimit.lean), not by the Attempt 2 module.
