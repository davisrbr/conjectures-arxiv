# Attempt 3 Lean Formalization Notes

This note documents the Lean formalization for Attempt 3, the disconfirmation of Conjecture 5.2 in "Steady-State Behavior of Constant-Stepsize Stochastic Approximation: Gaussian Approximation and Tail Bounds."

## Scope

The Lean proof is in [../QuasimodularSturm/Attempts/SteinDisproof.lean](../QuasimodularSturm/Attempts/SteinDisproof.lean).

The main theorem is `stein_conjecture_disconfirmed`. It formalizes the following obstruction:

- if a Stein operator has the form `Lg(y) = A(y, g'(y), g''(y))` with `g` of class `C^3`,
- then `Lg` is differentiable at `0`,
- but the `1`-Lipschitz test function `y ↦ |y|` is not differentiable at `0`,
- so `|y| - c = Lg(y)` cannot hold for any constant `c`.

## Match To The Paper

The formalization is aimed at the literal printed Conjecture 5.2 in arXiv:2602.13960v1. In the paper source (`Arxiv_Version.tex`, lines 797-804), the conjecture says that for any `h ∈ Lip_1(R)`, the equation

`h(y) - E[h(Z)] = -y^h g_h'(y) + E[ξ_k^2] g_h''(y)`

admits a solution with uniformly bounded `g_h'`, `g_h''`, and `g_h'''`.

That is enough for the `|y|` counterexample. So this Lean proof is not based on a transcription mistake in the extracted dataset row.

## Repair Caveat

The paper appears internally inconsistent. Later in the general-SGD section, the generator used for the Gibbs target is instead of the form

`Lg(y) = -κ y^(h-1) g'(y) + (σ^2 / 2) g''(y)`.

This matters as follows.

- If the conjecture is only repaired at the operator level, the same `|y|` obstruction still applies. A `C^3` solution would still make `Lg` differentiable at `0`.
- If the conjecture is repaired more substantially, for example by restricting the test class to `Lip_1 ∩ C^1` or by weakening the derivative notion for `g`, then this specific counterexample is no longer decisive.

So the Lean theorem should be read as a formal disproof of the conjecture as printed, and of any minimally repaired version that still quantifies over all `1`-Lipschitz test functions and still asks for classical bounded derivatives through order `3`.

## Verification

The formalization is re-exported from [../QuasimodularSturm.lean](../QuasimodularSturm.lean), and `~/.elan/bin/lake build` succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.
