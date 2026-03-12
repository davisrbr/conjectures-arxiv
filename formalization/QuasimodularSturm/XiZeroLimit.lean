import Mathlib

open scoped BigOperators
open Filter

namespace QuasimodularSturm

section SmallestValue

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The smallest value attained by a nonempty finite family of real numbers. -/
noncomputable def smallestValue (f : ι → ℝ) : ℝ :=
  (Finset.univ.image f).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem exists_eq_smallestValue (f : ι → ℝ) :
    ∃ i, f i = smallestValue f := by
  classical
  have hmem : smallestValue f ∈ (Finset.univ.image f : Finset ℝ) := by
    simpa [smallestValue] using
      ((Finset.univ.image f).min'_mem (Finset.image_nonempty.mpr Finset.univ_nonempty))
  rcases Finset.mem_image.mp hmem with ⟨i, -, hi⟩
  exact ⟨i, hi⟩

theorem smallestValue_le (f : ι → ℝ) (i : ι) :
    smallestValue f ≤ f i := by
  simpa [smallestValue] using
    ((Finset.univ.image f).min'_le (f i) (by simp))

theorem smallestValue_pos (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    0 < smallestValue f := by
  rcases exists_eq_smallestValue f with ⟨i, hi⟩
  rw [← hi]
  exact hf i

/--
If `β` is the smallest value in a positive finite family, then `β` is bounded above by the number
of terms divided by the sum of the reciprocal values.
-/
theorem smallestValue_le_card_div_sumInv (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    smallestValue f ≤ (Fintype.card ι : ℝ) / (∑ i, (f i)⁻¹) := by
  have hsmallPos : 0 < smallestValue f := smallestValue_pos f hf
  have hsumLe : (∑ i, (f i)⁻¹) ≤ (Fintype.card ι : ℝ) * (smallestValue f)⁻¹ := by
    calc
      ∑ i, (f i)⁻¹ ≤ ∑ _i : ι, (smallestValue f)⁻¹ := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact (inv_le_inv₀ (hf i) hsmallPos).2 (smallestValue_le f i)
      _ = (Fintype.card ι : ℝ) * (smallestValue f)⁻¹ := by
        simp
  have hsumPos : 0 < ∑ i, (f i)⁻¹ := by
    rcases exists_eq_smallestValue f with ⟨i, hi⟩
    calc
      0 < (f i)⁻¹ := inv_pos.mpr (hf i)
      _ ≤ ∑ j, (f j)⁻¹ := by
        refine Finset.single_le_sum (s := Finset.univ) (a := i) (f := fun j : ι => (f j)⁻¹) ?_ ?_
        · intro j hj
          exact inv_nonneg.mpr (le_of_lt (hf j))
        · simp
  refine (le_div_iff₀ hsumPos).2 ?_
  calc
    smallestValue f * (∑ i, (f i)⁻¹)
        ≤ smallestValue f * ((Fintype.card ι : ℝ) * (smallestValue f)⁻¹) := by
          exact mul_le_mul_of_nonneg_left hsumLe (le_of_lt hsmallPos)
    _ = (Fintype.card ι : ℝ) := by
      ring_nf
      field_simp [hsmallPos.ne']

end SmallestValue

section XiZeroLimit

/--
Correct endgame of the `\widetilde Ξ_n` proof: for each `n`, let `roots n` enumerate the positive
zeros of `\widetilde Ξ_n`. If the ratio
`(# roots of \widetilde Ξ_n) / (sum of reciprocal roots)` tends to `0`, then the smallest root
tends to `0`.

This packages the analytic heart of the conjecture in a way that can be combined with the paper's
root-location theorem and any separate asymptotic estimate for the reciprocal-root sum.
-/
theorem xi_smallestRoot_tendsto_zero
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (roots : ∀ n, ι n → ℝ)
    (hpos : ∀ n i, 0 < roots n i)
    (hsmall : Tendsto (fun n ↦ (Fintype.card (ι n) : ℝ) / ∑ i, (roots n i)⁻¹) atTop (nhds 0)) :
    Tendsto (fun n ↦ smallestValue (roots n)) atTop (nhds 0) := by
  refine squeeze_zero (fun n ↦ (smallestValue_pos (roots n) (hpos n)).le) ?_ hsmall
  intro n
  exact smallestValue_le_card_div_sumInv (roots n) (hpos n)

/--
Version of `xi_smallestRoot_tendsto_zero` where the reciprocal-root sum has already been
identified as an explicit sequence `A n`.
-/
theorem xi_smallestRoot_tendsto_zero_of_sumInv
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (roots : ∀ n, ι n → ℝ)
    (hpos : ∀ n i, 0 < roots n i)
    (A : ℕ → ℝ)
    (hsum : ∀ n, ∑ i, (roots n i)⁻¹ = A n)
    (hA : Tendsto (fun n ↦ (Fintype.card (ι n) : ℝ) / A n) atTop (nhds 0)) :
    Tendsto (fun n ↦ smallestValue (roots n)) atTop (nhds 0) := by
  refine xi_smallestRoot_tendsto_zero roots hpos ?_
  refine hA.congr' <| Filter.Eventually.of_forall ?_
  intro n
  simp [hsum n]

end XiZeroLimit

end QuasimodularSturm
