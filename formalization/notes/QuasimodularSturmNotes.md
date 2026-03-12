# Attempt 24 Lean Formalization Notes

This note documents the Lean formalization attempt for Attempt 24, the claimed partial confirmation of the quasimodular Sturm-bound conjecture from "New Types of Sturm bounds via `p`-adic transfer methods."

## Scope

The current Lean files are:

- [../QuasimodularSturm/Sturm/DiagonalCriterion.lean](../QuasimodularSturm/Sturm/DiagonalCriterion.lean)
- [../QuasimodularSturm/Sturm/Concrete.lean](../QuasimodularSturm/Sturm/Concrete.lean)

What these files formalize is deliberately narrower than the original solver writeup.

- `DiagonalCriterion.lean` proves the abstract implication that if one has a diagonal family of `q`-series, then the first `d` coefficients determine a linear combination of that family.
- `Concrete.lean` builds a concrete `\mathbf Q`-coefficient `q`-series model for `E_2`, `E_4`, `E_6`, defines the usual `X,Y,Z` combinations, and verifies diagonal families in small weights `1` through `5`.

So the Lean development formalizes a reusable criterion and some low-weight evidence, but not the full theorem.

## Match To The Solver Attempt

The important outcome of the formalization attempt is negative: it exposed a real gap in the natural-language proof sketch.

The solver argument claimed that for each `n` there are at least `n+1` basis monomials with `q`-order at most `n`, and then used that counting statement to assert that one can inductively construct a diagonal basis by elimination. That step is not valid. Counting low-order monomials does not imply that the truncated coefficient vectors have rank `n+1`, and the elimination step does not preserve the needed rank information for free.

So the claimed proof of the complex-coefficient half should not be treated as correct.

## Why The Gap Matters

The failure is not merely formal or stylistic. The same weight/order combinatorics can occur in toy models where the conclusion is false.

For example, if one replaces the actual quasimodular generators by the toy series

- `X = 1 + q`,
- `Y = q`,
- `Z = q^2`,

then the same counting argument still goes through, but the matrix of the first `d` coefficients of the weight-`k` monomials becomes singular from weight `k = 6` onward. So the solver proof was using information that is too weak to imply the desired injectivity statement.

This does not show the actual quasimodular conjecture is false. It only shows that the attempted proof route does not work as stated.

## What The Current Lean Files Do Show

The current formalization gives two narrower outputs:

- an abstract theorem isolating the exact extra ingredient needed for a correct proof, namely a genuine diagonal family of `q`-series;
- concrete low-weight evidence in the actual `E_2,E_4,E_6` model, where suitable diagonal families were verified for weights `1` through `5`.

So the right reading is:

- the previous "partial confirmation" no longer stands as a proof claim;
- the conjecture remains unresolved;
- the formalization attempt still produced useful structural clarification.

## Verification

The formalization is re-exported from [../QuasimodularSturm.lean](../QuasimodularSturm.lean), and `~/.elan/bin/lake build QuasimodularSturm` succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.
