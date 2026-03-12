# Attempt 10 Lean Formalization Notes

This note documents the Lean formalization for Attempt 10, the confirmation of Conjecture 4.1 in "On the Hilbert depth of the quotient ring of the edge ideal of a complete bipartite graph."

## Scope

The Lean proof is in [QuasimodularSturm/HilbertDepth.lean](QuasimodularSturm/HilbertDepth.lean).

The main theorems are:

- `attemptTen_part_a`
- `attemptTen_part_b`
- `attemptTen_part_c`
- `attemptTen_part_d`

The supporting threshold theorems are:

- `pProd_threshold_le_two` and `pProd_le_two`
- `qProd_threshold_le_two` and `qProd_le_two`
- `rProd_threshold_le_two` and `rProd_le_two`

What these theorems formalize is exactly the four explicit product inequalities from Conjecture 4.1.

The file packages the products into three families:

- `pProd m k = ∏_{j=1}^m (1 + (m+1)/(k-j))`, covering parts (a) and (b),
- `qProd m k = ∏_{j=0}^{m-1} (1 + m/(k-j))`, covering part (c),
- `rProd m k = ∏_{j=2}^{m+1} (1 + (m+2)/(k-j))`, covering part (d).

For each family, the Lean proof does the same four things:

- proves the product is monotone decreasing in `k`,
- reduces the argument to the conjectured threshold value of `k`,
- rewrites the square of the whole product as a product of reflected pairs,
- bounds each pair by `exp(2 log 2 / m)` using the elementary estimate `1 + u + u^2 / 2 ≤ exp u` together with an explicit endpoint inequality.

The endpoint inequalities are formalized as:

- `p_endpoint_sum_le`,
- `q_endpoint_sum_le`,
- `r_endpoint_sum_le`.

For the `P` and `R` families, the final threshold algebra is reduced to explicit polynomial nonnegativity lemmas `pEndpointPoly_nonneg` and `rEndpointPoly_nonneg`. For the `Q` family, the endpoint estimate closes by a simpler direct denominator normalization.

## Match To The Solver Attempt

This is a full formalization of Attempt 10 itself, not just a partial structural check.

It follows the same elementary proof pattern as the natural-language attempt:

- monotonicity in `k`,
- pairing outer factors with reflected inner factors,
- reducing pair bounds to the endpoint pair,
- using the AM-GM style two-factor estimate packaged in `pair_exp_bound`,
- and checking the threshold algebra explicitly.

The Lean development does not import any external gamma-function inequality library or hide the argument behind asymptotic black boxes. It proves the finite products directly.

One slight strengthening is worth stating explicitly: the final Lean theorems are proved for real `k` above the threshold, not only integer `k`. That is stronger than the paper's intended application and implies the integer case immediately.

## What Is Not Yet Formalized

The current Lean file does not try to formalize the whole surrounding commutative-algebra story of the paper.

In particular, it does not yet formalize:

- the downstream deduction of the paper's Proposition 4.2 from Conjecture 4.1,
- the translation of these products into gamma-ratio or binomial-ratio language,
- the broader Hilbert-depth setup and later lower-bound consequences for `h(n,n)`.

So this note should be read as a completed formal verification of the four conjectured inequalities themselves, not of the entire paper.

## Verification

The formalization is re-exported from [QuasimodularSturm.lean](QuasimodularSturm.lean).

`~/.elan/bin/lake build QuasimodularSturm.HilbertDepth` succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.

`~/.elan/bin/lake build QuasimodularSturm` also succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.
