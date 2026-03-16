# Attempt 16 Lean Formalization Notes

This note documents the Lean formalization for Attempt 16, the disconfirmation of Conjecture 5.1 in "Steady-State Behavior of Constant-Stepsize Stochastic Approximation: Gaussian Approximation and Tail Bounds."

## Scope

The Lean proof is in [../QuasimodularSturm/Attempts/GeneralSGDMomentDisproof.lean](../QuasimodularSturm/Attempts/GeneralSGDMomentDisproof.lean).

The file now contains three connected pieces:

- a scalar heavy-tail base construction
  - `attemptSixteen_noise_thirdMoment_integrable`
  - `attemptSixteen_noise_sixthMoment_not_integrable`
  - `attemptSixteenCenteredNoise_thirdMoment_integrable`
  - `attemptSixteenCenteredNoise_sixthMoment_not_integrable`
  - these establish the centered finite-third / infinite-sixth moment noise law used in the repaired counterexample
- a centered heavy-tail AR(1) counterexample for the repaired conjecture with centering restored
  - `attemptSixteenCenteredARIterate_tendstoInDistribution`
  - `attemptSixteenCenteredSeries_sixthMoment_not_integrable`
  - this is the substantive route closest to the solver write-up: we first shore up the conjecture by putting back the missing mean-zero assumption, then specialize to `h = 2` and `f(x) = x^2 / 2`, so the SGD update becomes the linear AR(1) recursion `X_(k+1) = (1 - α) X_k + α ξ_(k+1)`
  - Lean then formalizes the counterexample itself: the iterate laws converge in distribution to the stationary series `∑ n, α (1 - α)^n ξ_n`, and this limit law is proved not to have the conjectured sixth moment
- a direct literal-conjecture counterexample built from deterministic noise on the one-point probability space
  - `attemptSixteenLiteralObjective_satisfies_A5`
  - `attemptSixteenLiteralNoise_satisfies_A6Moment`
  - `attemptSixteen_conjecture_disconfirmed`

The literal-statement route targets the printed statement more directly than the original solver sketch. It takes

- `f(x) = x arctan x - (1 / 2) log (1 + x^2)`, whose derivative is `arctan x`,
- deterministic noise `ξ_k ≡ 2`,
- the SGD recursion started at `0`.

Since `arctan x < π / 2 < 2` for every real `x`, each iterate gains at least
`α * (2 - π / 2)`, so the sequence grows at least linearly and cannot converge to any finite real
limit. On the one-point sample space, every random variable is deterministic, so this rules out
the conjectured convergence-in-distribution claim for every positive stepsize.

Here "repaired" means the following. The printed A6 dropped the earlier mean-zero assumption on the
noise, so the literal statement admits the deterministic counterexample above. To get back to the
more mathematically natural version considered in the solver write-up, we first shore up the
conjecture by reinstating that centering assumption. We then move to the simplest repaired case by
specializing to `h = 2` and using the quadratic objective `f(x) = x^2 / 2`, so the SGD recursion
becomes exactly a linear AR(1) process.

With the repaired statement in that form, the formalization builds the counterexample explicitly.
It defines centered noise `ξ_k` of the form `sign_k * 2^(N_k)` with a fair sign and geometric
magnitude, proves `E |ξ_k|^3 < ∞` but `E |ξ_k|^6 = ∞`, identifies the stationary candidate as the
series `∑ n, α (1 - α)^n ξ_n`, and derives the contradiction by showing that if this stationary
limit had finite sixth moment then the innovation `ξ_0` would too.

## Relation To The Solver Write-Up

The solver write-up targeted a repaired, centered interpretation of the conjecture using an `h = 2`
linear AR(1) recursion with heavy-tailed noise: finite third moment, infinite sixth moment, and a
stationary law with infinite sixth moment.

The Lean formalization follows that same order. First it shores up the conjecture by restoring the
missing mean-zero assumption from the printed statement. Then it moves to the clean quadratic
special case, where the update becomes `X_(k+1) = (1 - α) X_k + α ξ_(k+1)`.

After that setup, Lean formalizes the counterexample itself. The centered noise is constructed
explicitly, the SGD recursion is identified with the corresponding AR(1) partial sums, the iterate
laws are shown to converge in distribution to the stationary series `∑ n, α (1 - α)^n ξ_n`, and
that series is proved not to have finite sixth moment. The final contradiction is not just a loose
analogy: Lean proves that finite sixth moment for the stationary series would force finite sixth
moment for the driving noise itself, contradicting the explicit heavy-tail calculation.

The file also contains a second, separate literal-statement disproof that exploits a specification
defect in the printed assumptions. As printed, Assumption A6 does not restate the earlier
mean-zero condition on the noise. That omission permits deterministic nonzero noise `ξ_k ≡ 2`,
and then the recursion drifts to `+∞`. So the file now contains both the substantive repaired
heavy-tail counterexample and the narrower statement-level objection to the exact printed text.

## Match To The Paper

This formalization now addresses both the literal printed Conjecture 5.1 and the shored-up version
that matches the solver's natural-language objection. In that shored-up version, the missing
mean-zero noise assumption is restored before the argument is specialized to the quadratic `h = 2`
case.

For the literal printed statement, the Lean counterexample exploits the omission of a centering
assumption from A6. For the shored-up version, the Lean counterexample shows that even after
putting mean-zero noise back into the assumptions and reducing to the clean linear AR(1) case, a
third-moment hypothesis still does not force the conjectured `3h` stationary moment bound.

The scalar heavy-tail witness from the earlier partial development is still present because it is
used to build the centered noise law and to separate the finite-third from infinite-sixth moment
claims cleanly.

## Verification

The current file has been verified with

- `lake build QuasimodularSturm.Attempts.GeneralSGDMomentDisproof`
- `lake build QuasimodularSturm`

in `/Users/davisbrown/conjectures-arxiv/formalization`.
