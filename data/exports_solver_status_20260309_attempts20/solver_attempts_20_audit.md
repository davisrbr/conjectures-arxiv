# Solver Attempt Audit (using GPT 5.4 Thinking xhigh, in codex)

Date: 2026-03-09 

**Summary:** This 20-attempt combined batch now has 6 results that are likely to hold up: four results showing that the conjecture is false and two results proving the conjecture.

Of the rest of the 20 attempts, there are 4 mathematically useful partial results, 1 qualified confirmation, 1 draft question that is effectively already absorbed by its own paper, 2 specification/formalization issues, and 6 unresolved outcomes.

The strongest clear results are:

- The kernel quantile discrepancy rate conjecture is **likely a false conjecture**. The rank-1-kernel reduction to one-dimensional empirical `W_2` remains the cleanest disproof in the whole project.
- The Stein-equation conjecture in the stochastic-approximation paper is **likely a false conjecture**. The `|y|` test function blocks the claimed `C^3` bounded-derivative solution.
- The magnitude asymptotic for skew finite subsets of `\ell_1^N` is **likely a false conjecture**. The one-dimensional `F={0,1}` counterexample directly contradicts the claimed leading term.
- The second conjecture from the same stochastic-approximation paper, asserting a uniform `3h` stationary moment bound under only a third moment assumption on the noise, is **also likely false**. The quadratic `h=2` AR(1) example with finite third but infinite sixth innovation moment is decisive.
- The Hilbert-depth product inequalities look genuinely proved and remain the strongest clean **affirmative result** in the current 20-attempt set.
- The `\widetilde\Xi_n` zero-limit conjecture looks like genuinely proved **affirmative result**. The coefficient-ratio argument forcing `\beta_n \to 0` is strong.

Two more outputs are useful, but they should be read as statement failures rather than theorem disproofs:

- The Yu-Gi-Oh successor-state conjecture fails under the paper's own later semantics because information states do not determine a unique next state.
- The cyclically covering-subspace max formula fails literally because the printed hypothesis allows trivial operators `\sigma` with `\sigma^n=\mathrm{id}` that are not the intended Frobenius/shift map.

## What Looks Real

### Constant-stepsize SGD: both conjectures went down

The earlier batch already likely killed the paper's Stein-equation conjecture. This new batch likely kills the companion stationary-law / uniform-moment conjecture too. The new counterexample is especially good because it uses the easiest allowed case, `h=2`, where the recursion becomes linear. With centered heavy-tailed noise having finite third but infinite sixth moment, the stationary AR(1) law exists, but it cannot have the conjectured sixth moment. That is the right kind of obstruction: simple, structural, and hard to repair without changing the assumptions.

### The `\widetilde\Xi_n` zero-limit conjecture

This is the best new affirmative result. The solver notices two harmless statement defects, corrects them, and then gives an exact coefficient-ratio identity involving Euler numbers. Once that identity is written down, the conclusion `\beta_n \to 0` follows cleanly. There is apparently already a very close same-month follow-up paper on the exact `\widetilde\Xi_n` zero distribution, so this should be scored as a strong confirmation but not as a brand-new literature-free breakthrough.

### Hilbert depth of complete bipartite edge ideals

This remains the cleanest positive theorem closure in the full 20-attempt set. The inequalities were conjectural in the source paper, the solver supplied a coherent proof path, and spot checks behaved correctly. I would still human-proofread the factor pairing argument before citing it as done, but this is exactly the sort of output the pipeline was supposed to find.

### Kernel quantile discrepancy and magnitude asymptotics

These still look like the two clearest negative results in the full 20-attempt set. Both rest on explicit reductions to simpler objects rather than vague plausibility arguments.

## Strong Partial Results

### Arrow-pattern avoidance

The solver did not finish all three formulas, but proving the odd-Fibonacci and Motzkin enumerations is still meaningful progress. Those two parts look mathematically natural and connect cleanly to standard noncrossing/nonnesting partition and partial-matching models. The remaining `2^n-n` formula is still open on the available evidence.

### Vigemers / minimizer counting

This result is useful but should be labeled carefully. The solver proved that the published dynamic program extends to coordinatewise maps `g_1,\dots,g_m` when each coordinate map is bijective. It also found that the recurrence scheme already breaks for noninjective coordinate maps. So the paper's broad claim is not proved, but the right repaired version looks real.

### Optimal quasimodular Sturm bound

The solver proved the complex-coefficient half: a level-1 quasimodular form is determined by its first `dim \widetilde M_{2k}` coefficients. That is substantial. But the paper's sharper mod-`m` statement over the full integral lattice remains open, and that is exactly where the paper itself says the real subtlety lies.

### Quarter-turn symmetric ASM polytope

This stayed unresolved, but the solver did prove the conjectured dimension as an upper bound and checked the first nontrivial case `n=5`. That is not a settlement, but it is more useful than a bare shrug.

### Colored interlacing triangles and Genocchi medians

The solver did not prove the main leading-coefficient claim. What it did show is that the integrality half of the conjecture is largely formal once one grants the preceding eventual-polynomiality conjecture. So the actual mathematical content is narrower than the source paper's wording suggests: the hard part is the top-degree coefficient `5^k`.

## Still Unresolved

These remain basically conservative unresolved answers:

- Graham's rearrangement conjecture: substantial recent progress, but still not the full all-primes theorem.
- The matroid universal-model conjecture from Frobenius-group gain graphs: plausible, but not settled.
- The improved randomized range-finder constant: good reductions and special cases, but no decisive proof or counterexample.
- The quarter-turn symmetric ASM dimension formula: upper bound only.
- The Genocchi leading-coefficient conjecture: reduction only.
- The Ramanujan `{8,12,16,28}` relation statement: still too draft-like and vague to count as resolved.

## Ramanujan-Series Cleanup

The Ramanujan-family outputs still need to be scored with care.

- The `N=15` leftover is not really a theorem statement at all; it is a draft question, and the right reading is that the intended content is already absorbed later in the same paper.
- The `{25,45,85}` versus `{5,9,17}` relation remains a qualified confirmation under the paper's natural modular/hypergeometric notion of “related.”
- The `{8,12,16,28}` versus `{2,3,4,7}` relation remains unresolved and should not be counted as a clean win.

## Overall Judgment

If the question is whether the pipeline is still finding genuinely useful things, the answer is yes. The batch now contains multiple plausible disproofs, two solid affirmative results, several partial theorem-level reductions, and a few very revealing “the statement itself is broken” diagnoses.

If the question is how many clean benchmark-quality open-conjecture resolutions are here, I would count 6 strong ones:

- kernel quantile discrepancy: likely false,
- SGD Stein equation: likely false,
- magnitude asymptotic: likely false,
- Hilbert-depth inequalities: likely true,
- SGD stationary `3h` moment conjecture: likely false,
- `\widetilde\Xi_n` zero-limit conjecture: likely true.

Then I would put the rest into narrower buckets:

- formalization failures: Yu-Gi-Oh, cyclically covering subspaces,
- qualified confirmation: Ramanujan `{25,45,85}`,
- partials: Prishchepov, arrow-pattern formulas, Vigemers, quasimodular Sturm bound,
- draft-resolved-in-substance: the `N=15` Ramanujan leftover,
- unresolved: Graham, universal models for the Frobenius-gain-graph matroid class, the randomized range-finder constant, the Genocchi leading coefficient, the QTSASM dimension formula, and the remaining draft Ramanujan relation.
