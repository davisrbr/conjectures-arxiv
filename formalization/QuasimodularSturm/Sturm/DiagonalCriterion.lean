import QuasimodularSturm.Sturm.Basic

namespace QuasimodularSturm

section DiagonalCriterion

variable {K : Type*} [Field K]

/-- A coefficient sequence indexed by `q`-powers. -/
abbrev Series (K : Type*) := ℕ → K

/-- Truncate a coefficient sequence to its first `d` coefficients. -/
def seriesTrunc (d : ℕ) : Series K →ₗ[K] (Fin d → K) where
  toFun f i := f i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
A diagonal family of `q`-series: the `i`-th series has vanishing coefficients below `q^i` and
coefficient `1` at `q^i`.
-/
structure DiagonalFamily (d : ℕ) where
  series : Fin d → Series K
  lower_zero : ∀ i j, j < i → series i j = 0
  diagonal_one : ∀ i, series i i = 1

/--
If a family of `d` coefficient sequences is diagonal on its first `d` coefficients, then a linear
combination of that family is determined by those first `d` coefficients.
-/
theorem coefficients_determine_combination
    {d : ℕ} (F : DiagonalFamily (K := K) d)
    {c : Fin d → K}
    (hvanish : seriesTrunc (K := K) d (∑ i, c i • F.series i) = 0) :
    c = 0 := by
  exact coeffs_zero_imp_zero (K := K) (trunc := seriesTrunc d) (F := F.series)
    F.lower_zero F.diagonal_one hvanish

end DiagonalCriterion

end QuasimodularSturm
