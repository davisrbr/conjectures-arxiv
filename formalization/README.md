# QuasimodularSturm formalization workspace

This directory contains the Lean 4 workspace used to formalize selected solver proof attempts from the main `conjectures-arxiv` repository.

The package name is `QuasimodularSturm` for historical reasons. It now contains several independent formalization files, not just the original quasimodular-Sturm work.

## Build

From this directory:

```sh
lake build QuasimodularSturm
```

To build a single module:

```sh
lake build QuasimodularSturm.Attempts.HilbertDepth
lake build QuasimodularSturm.Attempts.MagnitudeDisproof
lake build QuasimodularSturm.Attempts.SteinDisproof
lake build QuasimodularSturm.Attempts.XiZeroLimit
```

## Main library file

[QuasimodularSturm.lean](QuasimodularSturm.lean) re-exports the currently active modules:

- `QuasimodularSturm.Sturm.Basic`
- `QuasimodularSturm.Sturm.DiagonalCriterion`
- `QuasimodularSturm.Sturm.Concrete`
- `QuasimodularSturm.Attempts.HilbertDepth`
- `QuasimodularSturm.Attempts.MagnitudeDisproof`
- `QuasimodularSturm.Attempts.SteinDisproof`
- `QuasimodularSturm.Attempts.XiZeroLimit`

## Structure

The workspace is organized as follows:

- `QuasimodularSturm/Sturm/`: the original quasimodular-Sturm formalization files.
- `QuasimodularSturm/Attempts/`: independent Lean formalizations for individual solver attempts.
- `notes/`: markdown notes describing scope, caveats, and verification status for each attempt.

## Current modules

- [QuasimodularSturm/Attempts/HilbertDepth.lean](QuasimodularSturm/Attempts/HilbertDepth.lean): full formalization of Attempt 10, proving all four product inequalities from Conjecture 4.1 in the Hilbert-depth paper.
- [QuasimodularSturm/Attempts/MagnitudeDisproof.lean](QuasimodularSturm/Attempts/MagnitudeDisproof.lean): full formalization of the explicit `F = {0,1}` counterexample for Attempt 9.
- [QuasimodularSturm/Attempts/SteinDisproof.lean](QuasimodularSturm/Attempts/SteinDisproof.lean): full formal disproof of the literal printed Stein-equation conjecture for Attempt 3.
- [QuasimodularSturm/Attempts/XiZeroLimit.lean](QuasimodularSturm/Attempts/XiZeroLimit.lean): partial formalization of the corrected finite-root endgame for Attempt 22.
- [QuasimodularSturm/Sturm/DiagonalCriterion.lean](QuasimodularSturm/Sturm/DiagonalCriterion.lean): abstract diagonal criterion used in the quasimodular Sturm-bound investigation.
- [QuasimodularSturm/Sturm/Concrete.lean](QuasimodularSturm/Sturm/Concrete.lean): concrete low-weight `E_2, E_4, E_6` model for the quasimodular Sturm-bound attempt.
- [QuasimodularSturm/Sturm/Basic.lean](QuasimodularSturm/Sturm/Basic.lean): small shared lemmas used by the quasimodular-Sturm files.

## Notes

These notes explain scope, caveats, and verification status for the formalization attempts:

- [notes/HilbertDepthNotes.md](notes/HilbertDepthNotes.md)
- [notes/MagnitudeDisproofNotes.md](notes/MagnitudeDisproofNotes.md)
- [notes/SteinDisproofNotes.md](notes/SteinDisproofNotes.md)
- [notes/XiZeroLimitNotes.md](notes/XiZeroLimitNotes.md)
- [notes/QuasimodularSturmNotes.md](notes/QuasimodularSturmNotes.md)

Some notes describe completed formal verifications of the solver argument or counterexample. Others describe partial formalizations or formalization attempts that exposed a gap in the original solver proof.
