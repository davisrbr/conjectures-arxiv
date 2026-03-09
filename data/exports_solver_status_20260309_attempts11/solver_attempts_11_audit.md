# Solver Attempt Audit

Date: 2026-03-09

## Bottom Line

This corrected batch has 4 clear settlement-quality results, 1 additional qualified confirmation that depends on the paper's natural interpretation of "related," 1 strong formalization failure, 3 good conservative unresolved or partial answers, and 2 Ramanujan-series draft artifacts that should not be counted as ordinary theorem wins.

The clear settlement-quality results are:

- The kernel quantile discrepancy rate conjecture is likely false as written. The solver gives a concrete rank-1-kernel reduction to one-dimensional Gaussian empirical `W_2`, where the claimed `N^{-1/2}` rate fails by a `sqrt(log log N)` factor.
- The Stein-equation conjecture in the stochastic-approximation paper is likely false as written. Taking the Lipschitz test function `h(y)=|y|` blocks the existence of a classically `C^3` solution with bounded derivatives.
- The magnitude asymptotic for skew finite subsets of `\ell_1^N` is likely false as written. The solver gives the explicit one-dimensional counterexample `F={0,1}`, where the leading coefficient is not the conjectured `4^k`.
- The Hilbert-depth product inequalities look genuinely proved. This is still worth a human proofread, but it is the strongest affirmative result in the set.

The qualified additional positive result is:

- The conjectured relation between the level-2 series with `N = {25,45,85}` and the level-10 series with `N = {5,9,17}` now looks confirmed under the paper's natural hypergeometric/modular meaning of "related." I would treat this as real progress, but not as a fully clean theorem settlement because the statement itself remains interpretation-dependent.

## What Looks Strong

### Kernel quantile discrepancy

The conjecture claims an expected error rate `O(L^{-1/2}+N^{-1/2})` for empirical kernel quantile discrepancy under weak assumptions. The solver's disproof is strong because it builds a concrete rank-1 kernel that collapses the problem to one-dimensional Gaussian empirical `W_2`, and that regime is known to have the slower `sqrt((log log N)/N)` behavior. This is the right shape of counterexample.

### Stein equation for constant-stepsize stochastic approximation

The conjecture says every Lipschitz test function should admit a Stein solution with bounded first three derivatives. The answer here is also strong. Plugging in `h(y)=|y|` immediately creates a differentiability obstruction at `0`, so the exact statement cannot hold. The solver also correctly notices that the surrounding notation in the paper appears internally inconsistent.

### Magnitude continuity at skew finite subsets of `\ell_1^N`

This is probably the cleanest disproof in the batch. The conjecture predicts a universal leading term `4^k r^k + O(r^{k+1})`. The solver checks the one-dimensional set `F={0,1}`, computes the determinant explicitly, and gets a different leading coefficient. That is a direct contradiction of the stated formula.

### Hilbert depth of edge ideals of complete bipartite graphs

This is the best affirmative result. The solver gives an actual proof strategy based on monotonicity, pairing factors, and exponential bounds, not just a vague appeal to nearby literature. I also numerically checked the threshold inequalities for small `s`, and they behave as claimed.

### Level-2 `{25,45,85}` versus level-10 `{5,9,17}`

This now looks materially stronger than it did in the earlier version of the export. The solver gives a positive resolution under the paper's standard transformation-theoretic reading of "related," with the pairings `25↔5`, `45↔9`, and `85↔17`. Because the exact wording is still vague, I would label this as a qualified confirmation rather than a clean theorem proof, but I would no longer leave it in the unresolved bucket.

## Useful but Should Be Labeled Carefully

### Yu-Gi-Oh successor-state computability

The solver's objection is good, but it should be labeled as a formalization failure, not just "disconfirmed." Under the paper's own later semantics, configurations are information states rather than full omniscient states, so hidden deck order can make the successor non-unique.

### Perfect Prishchepov groups

This is a solid partial result, not a full resolution. The solver correctly says the conjecture is now proved in the `gcd(n,6)=1` case but remains open when `n` has a factor of `2` or `3`.

### Graham's rearrangement conjecture

This answer is appropriately conservative. The solver finds recent work proving the conjecture for all sufficiently large primes, but it does not inflate that into a proof for every prime.

### Universal models for matroids from Frobenius-group gain graphs

This is also a reasonable conservative answer. The solver gives a plausible route and does not overclaim a proof or counterexample.

## What I Would Discount

Two outputs should still not be counted as ordinary wins because the inputs are really draft artifacts rather than clean theorem statements.

- The `N=15` Ramanujan-series leftover is a question rather than a proposition. The useful content is that, under the intended reading, the case is already absorbed by later results in the same paper.
- The conjecture relating `N = {8,12,16,28}` to `N = {2,3,4,7}` remains too vague to count as a theorem settlement. The paper clearly handles the `N=12` and `N=28` subcases, but the full four-case statement is not proved there, and the `N=8` and `N=16` cases remain unresolved on the available evidence.

## Overall Judgment

If the question is whether the model produced anything real here, the answer is yes. The disproofs for the kernel-quantile, Stein-equation, and magnitude conjectures are substantial, and the Hilbert-depth proof is the strongest positive result in the set. The level-2 versus level-10 Ramanujan relation also now looks genuinely stronger than a mere unresolved plausibility claim.

If the question is how many clean open-conjecture solves are in this file, I would still say four, with a possible fifth if you are willing to count the `{25,45,85}` versus `{5,9,17}` relation under the paper's natural meaning of "related." The Yu-Gi-Oh result is best treated as an ill-posedness diagnosis, the Prishchepov result as a partial, Graham and the matroid conjecture as cautious unresolved answers, and the remaining Ramanujan leftovers as draft-only items rather than benchmark-quality theorem statements.
