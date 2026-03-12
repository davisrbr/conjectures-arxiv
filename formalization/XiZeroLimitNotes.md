# Attempt 22 Lean Formalization Notes

This note documents the Lean formalization attempt for Attempt 22, the claimed confirmation of the `\widetilde\Xi_n` smallest-zero conjecture from "Algebraic representatives of the ratios `ζ(2n+1)/π^{2n}` and `β(2n)/π^{2n-1}`."

## Scope

The Lean proof attempt is in [QuasimodularSturm/XiZeroLimit.lean](QuasimodularSturm/XiZeroLimit.lean).

The main theorems are:

- `smallestValue_le_card_div_sumInv`
- `xi_smallestRoot_tendsto_zero`
- `xi_smallestRoot_tendsto_zero_of_sumInv`

What these theorems formalize is the finite-root endgame:

- for a nonempty finite family of positive real roots, the smallest root is at most
  `(# roots) / (sum of reciprocal roots)`,
- therefore, if for `\widetilde\Xi_n` one can prove that
  `(# positive roots of \widetilde\Xi_n) / (sum of reciprocal roots)` tends to `0`,
  then the smallest positive root tends to `0`.

## Match To The Solver Attempt

This is not a line-by-line formalization of the solver writeup.

The solver sketch used the true inequality

`sum_j 1 / y_{n,j} >= 1 / beta_n`,

but that inequality alone is too weak to conclude `beta_n -> 0` from growth of the reciprocal-root sum. In Lean I instead formalized the corrected averaged bound

`beta_n <= (# roots) / (sum_j 1 / y_{n,j})`.

So the current Lean file should be read as a formalization of the corrected endgame of the argument, not of every sentence in the original natural-language proof sketch.

## What Is Not Yet Formalized

This is not an exact formal proof of the conjecture as stated in the paper.

In particular, the current Lean development does not yet formalize:

- the exact definitions of `\Xi_n` and `\widetilde\Xi_n` from theorem 3.1,
- the typo repair in the printed conjecture (`\Lambda_n` versus `\Xi_n`) and the `n >= 2` restriction needed because `\widetilde\Xi_1` has no positive zero,
- the paper's real-rootedness and root-location input for `\widetilde\Xi_n`,
- the representation of `\Xi_n` via the type-B Eulerian polynomial `B_{2n-1}`,
- the exact coefficient-ratio identity involving the Euler numbers,
- the asymptotic growth needed to show that the reciprocal-root sum dominates the number of roots.

Those missing ingredients are the substantive Xi-specific part of the proof. Mathlib in this repository does not currently provide the needed type-B Eulerian polynomial and secant-Euler-number infrastructure, so an exact end-to-end formalization would require building that theory first.

## Verification

`lake build QuasimodularSturm.XiZeroLimit` succeeds in `/Users/davisbrown/conjectures-arxiv/formalization`.

I did not verify the note via `lake build QuasimodularSturm`, because that full target is currently blocked by pre-existing unrelated errors in [QuasimodularSturm/Concrete.lean](QuasimodularSturm/Concrete.lean).
