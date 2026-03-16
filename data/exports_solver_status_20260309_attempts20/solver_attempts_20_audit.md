# Solver Attempt Audit (using GPT 5.4 Thinking xhigh, in codex)

Date: 2026-03-09 

**Summary:** This 20-attempt combined batch now has 6 results that are likely to hold up: four results showing that the conjecture is false and two results proving the conjecture.

Of the rest of the 20 attempts, there are 3 mathematically useful partial results, 1 qualified confirmation, 1 draft question that is effectively already absorbed by its own paper, 2 specification/formalization issues, and 7 unresolved outcomes.

The strongest clear results are:

- The kernel quantile discrepancy rate conjecture is **likely a false conjecture**. The rank-1-kernel reduction to one-dimensional empirical `W_2` remains the cleanest disproof in the whole project.
- The Stein-equation conjecture in the stochastic-approximation paper is **likely a false conjecture**. The `|y|` test function blocks the claimed `C^3` bounded-derivative solution, and we now have a corresponding Lean formalization attempt recorded in [solver_attempts_20_summary.md](solver_attempts_20_summary.md) and [../../formalization/notes/SteinDisproofNotes.md](../../formalization/notes/SteinDisproofNotes.md).
- The magnitude asymptotic for skew finite subsets of `\ell_1^N` is **likely a false conjecture**. The one-dimensional `F={0,1}` counterexample directly contradicts the claimed leading term.
- The second conjecture from the same stochastic-approximation paper, asserting a uniform `3h` stationary moment bound under only a third moment assumption on the noise, is **also likely false**. The quadratic `h=2` AR(1) example with finite third but infinite sixth innovation moment is decisive, and we now have a full Lean formalization of that route after first restoring the mean-zero noise assumption omitted from the printed statement. In that shored-up version, the SGD update becomes a linear AR(1) recursion driven by explicit centered heavy-tail noise. The same Lean file also records a separate deterministic disproof of the literal printed statement, exposing the omitted centering assumption as a technical defect in the published wording.
- The Hilbert-depth product inequalities look genuinely proved and remain the strongest clean **affirmative result** in the current 20-attempt set. We now also have a full Lean formalization recorded in [solver_attempts_20_summary.md](solver_attempts_20_summary.md) and [../../formalization/notes/HilbertDepthNotes.md](../../formalization/notes/HilbertDepthNotes.md).
- The `\widetilde\Xi_n` zero-limit conjecture looks like genuinely proved **affirmative result**. The coefficient-ratio argument forcing `\beta_n \to 0` is strong, and we now have a full Lean formalization recorded in [solver_attempts_20_summary.md](solver_attempts_20_summary.md) and [../../formalization/notes/XiZeroLimitNotes.md](../../formalization/notes/XiZeroLimitNotes.md).

Two more outputs are useful, but they should be read as statement failures rather than theorem disproofs:

- The Yu-Gi-Oh successor-state conjecture fails under the paper's own later semantics because information states do not determine a unique next state.
- The cyclically covering-subspace max formula fails literally because the printed hypothesis allows trivial operators `\sigma` with `\sigma^n=\mathrm{id}` that are not the intended Frobenius/shift map.

## What Looks Real

### Constant-stepsize SGD: stationary moment conjecture likely false

A strong counterexample targets the stationary-law / uniform-moment conjecture directly. It uses the simplest admissible case, `h=2`, where the recursion reduces to a linear AR(1) model. With centered heavy-tailed noise whose third moment is finite but sixth moment is infinite, the stationary law still exists, but it cannot satisfy the conjectured sixth-moment bound. That is a compelling obstruction on its own merits: it appears in a basic allowed regime, it is easy to state, and it is not the kind of failure that can be repaired without strengthening the assumptions.

### Constant-stepsize SGD stationary-moment conjecture: full formalization added

We now have a Lean formalization for two different versions of Attempt 16. One formalizes the
natural repaired version of the conjecture, where the missing mean-zero noise assumption is put
back and the argument is carried out in the quadratic `h = 2` case so that the SGD recursion is a
linear AR(1) process. The other formalizes the literal printed statement as written. The note [../../formalization/notes/GeneralSGDMomentDisproofNotes.md](../../formalization/notes/GeneralSGDMomentDisproofNotes.md)
links the proof file [../../formalization/QuasimodularSturm/Attempts/GeneralSGDMomentDisproof.lean](../../formalization/QuasimodularSturm/Attempts/GeneralSGDMomentDisproof.lean).

The substantive route matches the solver's natural-language argument. It proceeds in two stages.
First we shore up the conjecture by putting back the mean-zero noise assumption omitted from the
printed A6. Then we formalize the counterexample in the clean quadratic `h = 2` case, where the
SGD recursion becomes the linear AR(1) update `X_(k+1) = (1 - α) X_k + α ξ_(k+1)`. Lean constructs
an explicit centered heavy-tailed noise with finite third moment but infinite sixth moment, proves
that the iterate laws converge in distribution to the stationary series `∑ n, α (1 - α)^n ξ_n`,
and then shows that this limit law still has infinite sixth moment. So the repaired conjecture
fails for the same basic reason identified in the original write-up.

The same file also contains a separate disproof of the literal printed statement. That construction
works on a one-point probability space with deterministic noise `ξ_k ≡ 2` and the explicit convex
objective

`f(x) = x arctan x - (1/2) log(1+x^2)`.

Its derivative is `arctan x`, so the SGD increment is always at least `α (2 - π/2) > 0`. Therefore
the iterates diverge to `+∞`, and the associated Dirac laws cannot converge to any finite limit
law. This exposes the omitted centering assumption as a genuine technical defect in the published
wording.

So the Lean file now contains two complementary disproofs: a substantive heavy-tail AR(1)
counterexample for the shored-up version where mean-zero noise is restored, and a narrower
statement-level objection to the exact printed text.

### Stein equation: formalization attempt added

For the other stochastic-approximation disconfirmation, we now also have a Lean formalization attempt of the literal printed conjecture. The note [../../formalization/notes/SteinDisproofNotes.md](../../formalization/notes/SteinDisproofNotes.md) links the proof file and records the main caveat: the formalization cleanly disconfirms the conjecture as printed, and also any minimal repair that still quantifies over all `1`-Lipschitz test functions and demands classical bounded derivatives through order `3`, but it does not by itself rule out a stronger repair that changes the test-function or derivative class.

### The `\widetilde\Xi_n` zero-limit conjecture

This is the best new affirmative result. The solver notices two harmless statement defects, corrects them, and then gives an exact coefficient-ratio identity involving Euler numbers. Once that identity is written down, the conclusion `\beta_n \to 0` follows cleanly. There is apparently already a very close same-month follow-up paper on the exact `\widetilde\Xi_n` zero distribution, so this should be scored as a strong confirmation but not as a brand-new literature-free breakthrough.

### The `\widetilde\Xi_n` conjecture: full formalization added

We now also have a Lean note for this proof route. The note [../../formalization/notes/XiZeroLimitNotes.md](../../formalization/notes/XiZeroLimitNotes.md) links a completed end-to-end formalization of the adapted-`\widetilde\Xi_n` smallest-zero theorem itself. The Lean development now derives the coefficient-defined adapted Xi family, identifies it with the odd `sech` model, discharges the positive-root and root-count input internally, proves the exact secant-Euler coefficient-ratio identity, and closes the final hypothesis-free theorem that the smallest positive zero tends to `0`.

There is one explicit normalization caveat, and it is harmless for the conjecture: the Lean family is presented in solver indexing and up to a nonzero scalar factor from the paper. Since the conjecture concerns the location of the positive zeros, that normalization does not change the mathematical content of the theorem. So this should now be read as a completed formal verification of the paper's adapted-Xi zero-limit conjecture, not merely a structural check of the endgame.

### Hilbert depth of complete bipartite edge ideals

This remains the cleanest positive theorem closure in the full 20-attempt set. The inequalities were conjectural in the source paper, the solver supplied a coherent proof path, and that proof path is now backed by a full Lean formalization of the four inequality statements themselves. This is exactly the sort of output the pipeline was supposed to find.

### The Hilbert-depth inequalities: full formalization added

We now also have a Lean note for this proof route. The note [../../formalization/notes/HilbertDepthNotes.md](../../formalization/notes/HilbertDepthNotes.md) explains the scope of the formalization and links the proof file [../../formalization/QuasimodularSturm/Attempts/HilbertDepth.lean](../../formalization/QuasimodularSturm/Attempts/HilbertDepth.lean).

What is formalized is the full four-part inequality package from Conjecture 4.1 itself: monotonicity in `k`, reduction to the threshold cases, reflected pair-product identities, the elementary two-factor exponential bound, and the explicit endpoint algebra needed for the `P`, `Q`, and `R` product families.

The note is explicit about one strengthening and one boundary. The strengthening is that the final Lean theorems are proved for real `k` above the thresholds, not just integer `k`. The boundary is that the current file does not formalize the downstream commutative-algebra consequences such as Proposition 4.2 or the broader Hilbert-depth machinery. So this should be read as a completed formal verification of the conjectured inequalities themselves.

### Kernel quantile discrepancy and magnitude asymptotics

These still look like the two clearest negative results in the full 20-attempt set. Both rest on explicit reductions to simpler objects rather than vague plausibility arguments.

### The magnitude asymptotic conjecture: formalization attempt added

We now also have a Lean note for the magnitude counterexample. The note [../../formalization/notes/MagnitudeDisproofNotes.md](../../formalization/notes/MagnitudeDisproofNotes.md) explains the scope of the formalization and links the proof file [../../formalization/QuasimodularSturm/Attempts/MagnitudeDisproof.lean](../../formalization/QuasimodularSturm/Attempts/MagnitudeDisproof.lean).

What is formalized is the explicit `F={0,1}` disproof: the `4 × 4` similarity matrix for the vertices `{-r, r, 1-r, 1+r}`, the exact determinant formula

`(1-e^{-4r})^2 (1-e^{-2(1-2r)})`,

and the limiting coefficient `16(1-e^{-2})` rather than the conjectured `16`.

The note is explicit that this does not yet formalize the broader one-dimensional product formula for arbitrary finite `F ⊂ \ell_1^1`. So it should be read as a completed formal verification of the concrete counterexample, not yet of the full general `N=1` strengthening discussed in the natural-language attempt.

From an audit perspective, that still materially strengthens the status of Attempt 9. The main computational risk in the original writeup was an explicit determinant/asymptotic calculation on a `4 × 4` exponential-kernel matrix, and that part is now mechanically checked. So the remaining uncertainty is no longer algebraic correctness of the counterexample itself, but only the higher-level scope question of how far one wants to generalize beyond the concrete `F={0,1}` instance.

## Strong Partial Results

### Arrow-pattern avoidance

The solver did not finish all three formulas, but proving the odd-Fibonacci and Motzkin enumerations is still meaningful progress. Those two parts look mathematically natural and connect cleanly to standard noncrossing/nonnesting partition and partial-matching models. The remaining `2^n-n` formula is still open on the available evidence.

### Vigemers / minimizer counting

This result is useful but should be labeled carefully. The solver proved that the published dynamic program extends to coordinatewise maps `g_1,\dots,g_m` when each coordinate map is bijective. It also found that the recurrence scheme already breaks for noninjective coordinate maps. So the paper's broad claim is not proved, but the right repaired version looks real.

### Quarter-turn symmetric ASM polytope

This stayed unresolved, but the solver did prove the conjectured dimension as an upper bound and checked the first nontrivial case `n=5`. That is not a settlement, but it is more useful than a bare shrug.

### Colored interlacing triangles and Genocchi medians

The solver did not prove the main leading-coefficient claim. What it did show is that the integrality half of the conjecture is largely formal once one grants the preceding eventual-polynomiality conjecture. So the actual mathematical content is narrower than the source paper's wording suggests: the hard part is the top-degree coefficient `5^k`.

## Formalization Revisions

### Optimal quasimodular Sturm bound: formalization attempt invalidated the proof sketch

We now also have a Lean note for this attempt, but unlike the Stein and Xi notes, this one cuts against the original solver verdict. The note [../../formalization/notes/QuasimodularSturmNotes.md](../../formalization/notes/QuasimodularSturmNotes.md) records that the claimed complex-coefficient proof does not actually go through: the key elimination step uses only a counting statement about how many monomials have `q`-order at most `n`, and that is too weak to imply the existence of a diagonal basis. The formalization instead isolates the correct abstract diagonal criterion and checks low-weight evidence in the concrete `E_2,E_4,E_6` model. So this entry should no longer be scored as a partial confirmation; it moves back to the unresolved bucket.

## Still Unresolved

These remain basically conservative unresolved answers:

- Graham's rearrangement conjecture: substantial recent progress, but still not the full all-primes theorem.
- The matroid universal-model conjecture from Frobenius-group gain graphs: plausible, but not settled.
- The improved randomized range-finder constant: good reductions and special cases, but no decisive proof or counterexample.
- The optimal quasimodular Sturm bound: the earlier claimed complex-half proof does not survive formalization.
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
- partials: Prishchepov, arrow-pattern formulas, Vigemers,
- draft-resolved-in-substance: the `N=15` Ramanujan leftover,
- unresolved: Graham, universal models for the Frobenius-gain-graph matroid class, the randomized range-finder constant, the quasimodular Sturm bound, the Genocchi leading coefficient, the QTSASM dimension formula, and the remaining draft Ramanujan relation.
