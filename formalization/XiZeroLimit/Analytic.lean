import Mathlib

open scoped BigOperators Polynomial
open Filter
open PowerSeries

namespace XiZeroLimit

section SecantEuler

/-- The positive tail summand in the odd Dirichlet-beta value `β(2n+5)`. -/
noncomputable def dirichletBetaOddTailTerm (n k : ℕ) : ℝ :=
  1 / ((4 * k + 5 : ℝ) ^ (2 * n + 5 : ℕ)) - 1 / ((4 * k + 7 : ℝ) ^ (2 * n + 5 : ℕ))

/--
The odd Dirichlet-beta value `β(2n+5)`, written as a manifestly convergent positive series.
-/
noncomputable def dirichletBetaOddShift (n : ℕ) : ℝ :=
  1 - 1 / ((3 : ℝ) ^ (2 * n + 5 : ℕ)) + ∑' k : ℕ, dirichletBetaOddTailTerm n k

/--
The shifted secant-Euler ratio in the solver proof. By the classical beta-value formula for Euler
numbers, this is `-E_{2n+6} / E_{2n+4}`.
-/
noncomputable def secantEulerRatioShift (n : ℕ) : ℝ :=
  4 * (2 * n + 6 : ℝ) * (2 * n + 5 : ℝ) * dirichletBetaOddShift (n + 1) /
    (Real.pi ^ 2 * dirichletBetaOddShift n)

private theorem sum_range_one_div_nat_mul_succ (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / (((i + 1 : ℝ) * (i + 2 : ℝ))) = 1 - 1 / (n + 1 : ℝ) := by
  let f : ℕ → ℝ := fun i ↦ 1 / (i + 1 : ℝ)
  have hterm : ∀ i : ℕ, 1 / (((i + 1 : ℝ) * (i + 2 : ℝ))) = f i - f (i + 1) := by
    intro i
    have hi1 : (i + 1 : ℝ) ≠ 0 := by positivity
    have hi2 : (i + 2 : ℝ) ≠ 0 := by positivity
    calc
      1 / (((i + 1 : ℝ) * (i + 2 : ℝ))) =
          1 / (i + 1 : ℝ) * ((i + 2 : ℝ) - (i + 1 : ℝ)) * (1 / (i + 2 : ℝ)) := by
            have hdiff : ((i + 2 : ℝ) - (i + 1 : ℝ)) = 1 := by ring
            rw [hdiff]
            field_simp [hi1, hi2]
      _ = 1 / (i + 1 : ℝ) - 1 / (i + 2 : ℝ) := by
          exact one_div_mul_sub_mul_one_div_eq_one_div_add_one_div hi1 hi2
      _ = f i - f (i + 1) := by
          unfold f
          congr 2
          rw [Nat.cast_add, Nat.cast_one]
          ring
  calc
    ∑ i ∈ Finset.range n, 1 / (((i + 1 : ℝ) * (i + 2 : ℝ)))
        = ∑ i ∈ Finset.range n, (f i - f (i + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hterm i]
    _ = f 0 - f n := by
          simpa using Finset.sum_range_sub' f n
    _ = 1 - 1 / (n + 1 : ℝ) := by
          simp [f]

private theorem hasSum_one_div_nat_mul_succ :
    HasSum (fun k : ℕ ↦ 1 / (((k + 1 : ℝ) * (k + 2 : ℝ)))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k ↦ by positivity)]
  have hseq :
      (fun n : ℕ ↦ ∑ i ∈ Finset.range n, 1 / (((i + 1 : ℝ) * (i + 2 : ℝ)))) =
        fun n : ℕ ↦ 1 - 1 / (n + 1 : ℝ) := by
    ext n
    rw [sum_range_one_div_nat_mul_succ]
  rw [hseq]
  have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 1 : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hnat)
  simpa using (tendsto_const_nhds.sub hinv)

private theorem dirichletBetaOddTailTerm_nonneg (n k : ℕ) :
    0 ≤ dirichletBetaOddTailTerm n k := by
  unfold dirichletBetaOddTailTerm
  refine sub_nonneg.mpr ?_
  have hpow :
      (4 * k + 5 : ℝ) ^ (2 * n + 5 : ℕ) ≤ (4 * k + 7 : ℝ) ^ (2 * n + 5 : ℕ) := by
    gcongr
    nlinarith
  exact (one_div_le_one_div (by positivity) (by positivity)).2 hpow

private theorem dirichletBetaOddTailTerm_le_majorant (n k : ℕ) :
    dirichletBetaOddTailTerm n k ≤ 1 / (((k + 1 : ℝ) * (k + 2 : ℝ))) := by
  have hdrop :
      dirichletBetaOddTailTerm n k ≤ 1 / ((4 * k + 5 : ℝ) ^ (2 * n + 5 : ℕ)) := by
    unfold dirichletBetaOddTailTerm
    have hnonneg : 0 ≤ 1 / ((4 * k + 7 : ℝ) ^ (2 * n + 5 : ℕ)) := by
      positivity
    nlinarith
  have hexp : (5 : ℕ) ≤ 2 * n + 5 := by omega
  have hpow :
      (4 * k + 5 : ℝ) ^ (5 : ℕ) ≤ (4 * k + 5 : ℝ) ^ (2 * n + 5 : ℕ) := by
    have hbase : (1 : ℝ) ≤ 4 * k + 5 := by nlinarith
    exact pow_le_pow_right₀ hbase hexp
  have hstep :
      1 / ((4 * k + 5 : ℝ) ^ (2 * n + 5 : ℕ)) ≤ 1 / ((4 * k + 5 : ℝ) ^ (5 : ℕ)) := by
    exact (one_div_le_one_div (by positivity) (by positivity)).2 hpow
  have hpoly :
      ((k + 1 : ℝ) * (k + 2 : ℝ)) ≤ (4 * k + 5 : ℝ) ^ (5 : ℕ) := by
    have hquad : ((k + 1 : ℝ) * (k + 2 : ℝ)) ≤ (4 * k + 5 : ℝ) ^ (2 : ℕ) := by
      nlinarith
    have hsquare :
        (4 * k + 5 : ℝ) ^ (2 : ℕ) ≤ (4 * k + 5 : ℝ) ^ (5 : ℕ) := by
      have hbase : (1 : ℝ) ≤ 4 * k + 5 := by nlinarith
      exact pow_le_pow_right₀ hbase (by norm_num)
    exact hquad.trans hsquare
  have hmajor :
      1 / ((4 * k + 5 : ℝ) ^ (5 : ℕ)) ≤ 1 / (((k + 1 : ℝ) * (k + 2 : ℝ))) := by
    exact (one_div_le_one_div (by positivity) (by positivity)).2 hpoly
  exact hdrop.trans (hstep.trans hmajor)

private theorem dirichletBetaOddTailTerm_summable (n : ℕ) :
    Summable (dirichletBetaOddTailTerm n) := by
  refine Summable.of_nonneg_of_le
    (fun k ↦ dirichletBetaOddTailTerm_nonneg n k)
    (fun k ↦ dirichletBetaOddTailTerm_le_majorant n k)
    hasSum_one_div_nat_mul_succ.summable

private theorem two_thirds_le_dirichletBetaOddShift (n : ℕ) :
    (2 / 3 : ℝ) ≤ dirichletBetaOddShift n := by
  have htailNonneg :
      0 ≤ ∑' k : ℕ, dirichletBetaOddTailTerm n k := by
    exact tsum_nonneg (fun k ↦ dirichletBetaOddTailTerm_nonneg n k)
  have hpow :
      1 / ((3 : ℝ) ^ (2 * n + 5 : ℕ)) ≤ 1 / (3 : ℝ) := by
    have hexp : (1 : ℕ) ≤ 2 * n + 5 := by omega
    have hpow' : (3 : ℝ) ^ (1 : ℕ) ≤ (3 : ℝ) ^ (2 * n + 5 : ℕ) := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hexp
    simpa using (one_div_le_one_div (by positivity) (by positivity)).2 hpow'
  unfold dirichletBetaOddShift
  nlinarith

theorem dirichletBetaOddShift_pos (n : ℕ) : 0 < dirichletBetaOddShift n := by
  linarith [two_thirds_le_dirichletBetaOddShift n]

private theorem dirichletBetaOddShift_le_two (n : ℕ) :
    dirichletBetaOddShift n ≤ 2 := by
  have htail :
      ∑' k : ℕ, dirichletBetaOddTailTerm n k ≤ 1 := by
    have hmajor :
        ∑' k : ℕ, dirichletBetaOddTailTerm n k ≤
          ∑' k : ℕ, 1 / (((k + 1 : ℝ) * (k + 2 : ℝ))) :=
      (dirichletBetaOddTailTerm_summable n).tsum_le_tsum
        (fun k ↦ dirichletBetaOddTailTerm_le_majorant n k)
        hasSum_one_div_nat_mul_succ.summable
    calc
      ∑' k : ℕ, dirichletBetaOddTailTerm n k
          ≤ ∑' k : ℕ, 1 / (((k + 1 : ℝ) * (k + 2 : ℝ))) := hmajor
      _ = 1 := hasSum_one_div_nat_mul_succ.tsum_eq
  unfold dirichletBetaOddShift
  have hpowNonneg : 0 ≤ 1 / ((3 : ℝ) ^ (2 * n + 5 : ℕ)) := by positivity
  nlinarith

theorem tendsto_card_mul_six_div_secantEulerRatio_sub_five :
    Tendsto (fun n : ℕ ↦ 6 * (n + 1 : ℝ) / (secantEulerRatioShift n - 5)) atTop (nhds 0) := by
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ 6 * (n + 1 : ℝ) / (secantEulerRatioShift n - 5) ∧
          6 * (n + 1 : ℝ) / (secantEulerRatioShift n - 5) ≤ 36 / (n + 1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (6 : ℕ)] with n hn
    have hβnum : (2 / 3 : ℝ) ≤ dirichletBetaOddShift (n + 1) :=
      two_thirds_le_dirichletBetaOddShift (n + 1)
    have hβden : dirichletBetaOddShift n ≤ 2 := dirichletBetaOddShift_le_two n
    have hβdenPos : 0 < dirichletBetaOddShift n := by
      linarith [two_thirds_le_dirichletBetaOddShift n]
    have hq :
        (1 / 3 : ℝ) ≤ dirichletBetaOddShift (n + 1) / dirichletBetaOddShift n := by
      refine (le_div_iff₀ hβdenPos).2 ?_
      nlinarith
    have hcoeff :
        (1 / 4 : ℝ) ≤ 4 / Real.pi ^ 2 := by
      have hpi2 : Real.pi ^ 2 < 16 := by
        nlinarith [Real.pi_pos, Real.pi_lt_four]
      have hpos : 0 < Real.pi ^ 2 := by positivity
      exact (le_div_iff₀ hpos).2 (by nlinarith)
    have hpoly :
        4 * (n + 1 : ℝ) ^ 2 ≤ (2 * n + 6 : ℝ) * (2 * n + 5 : ℝ) := by
      nlinarith
    have hratioLower :
        (1 / 3 : ℝ) * (n + 1 : ℝ) ^ 2 ≤ secantEulerRatioShift n := by
      calc
        (1 / 3 : ℝ) * (n + 1 : ℝ) ^ 2 = (1 / 12 : ℝ) * (4 * (n + 1 : ℝ) ^ 2) := by ring
        _ ≤ (1 / 12 : ℝ) * ((2 * n + 6 : ℝ) * (2 * n + 5 : ℝ)) := by
          gcongr
        _ ≤ ((dirichletBetaOddShift (n + 1) / dirichletBetaOddShift n) * (4 / Real.pi ^ 2)) *
              ((2 * n + 6 : ℝ) * (2 * n + 5 : ℝ)) := by
          have hqp :
              (1 / 12 : ℝ) ≤
                (dirichletBetaOddShift (n + 1) / dirichletBetaOddShift n) * (4 / Real.pi ^ 2) := by
            calc
              (1 / 12 : ℝ) = (1 / 3 : ℝ) * (1 / 4 : ℝ) := by norm_num
              _ ≤ (dirichletBetaOddShift (n + 1) / dirichletBetaOddShift n) *
                    (4 / Real.pi ^ 2) := by
                  gcongr
          gcongr
        _ = secantEulerRatioShift n := by
          have hpi2 : Real.pi ^ 2 ≠ 0 := by positivity
          have hβ0 : dirichletBetaOddShift n ≠ 0 := hβdenPos.ne'
          rw [secantEulerRatioShift]
          field_simp [hpi2, hβ0]
    have hdenLower :
        (1 / 6 : ℝ) * (n + 1 : ℝ) ^ 2 ≤ secantEulerRatioShift n - 5 := by
      have hcast : (6 : ℝ) ≤ n := by exact_mod_cast hn
      have hfive : (5 : ℝ) ≤ (1 / 6 : ℝ) * (n + 1 : ℝ) ^ 2 := by
        nlinarith
      linarith
    have hdenPos : 0 < secantEulerRatioShift n - 5 := by
      nlinarith [hdenLower]
    constructor
    · positivity
    · refine (div_le_iff₀ hdenPos).2 ?_
      have hnp1 : 0 < (n + 1 : ℝ) := by positivity
      have hnp1ne : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hnp1ne]
      nlinarith [hdenLower]
  have hzero : Tendsto (fun n : ℕ ↦ 36 / (n + 1 : ℝ)) atTop (nhds 0) := by
    have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 1 : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop)
    have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hnat)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hinv.const_mul (36 : ℝ)
  refine squeeze_zero' ?_ ?_ hzero
  · filter_upwards [hbound] with n hn using hn.1
  · filter_upwards [hbound] with n hn using hn.2

end SecantEuler

section BernoulliQuarter

/-- Bernoulli generating series specialized at a real parameter `t`. -/
noncomputable def bernoulliSeriesAt (t : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun n =>
    Polynomial.aeval t (((1 : ℚ) / ((n.factorial : ℕ) : ℚ)) • Polynomial.bernoulli n)

/-- The rescaled exponential series `e^{X/4}`. -/
noncomputable def expQuarter : ℝ⟦X⟧ :=
  PowerSeries.rescale (1 / 4 : ℝ) (PowerSeries.exp ℝ)

/-- The rescaled exponential series `e^{-X/4}`. -/
noncomputable def expNegQuarter : ℝ⟦X⟧ :=
  PowerSeries.rescale (-(1 / 4 : ℝ)) (PowerSeries.exp ℝ)

/-- The rescaled exponential series `e^{X/2}`. -/
noncomputable def expHalf : ℝ⟦X⟧ :=
  PowerSeries.rescale (1 / 2 : ℝ) (PowerSeries.exp ℝ)

/-- The rescaled exponential series `e^{3X/4}`. -/
noncomputable def expThreeQuarter : ℝ⟦X⟧ :=
  PowerSeries.rescale (3 / 4 : ℝ) (PowerSeries.exp ℝ)

/-- The odd part of the Bernoulli generating series at `1/4`. -/
noncomputable def bernoulliQuarterOddSeries : ℝ⟦X⟧ :=
  bernoulliSeriesAt (1 / 4 : ℝ) - bernoulliSeriesAt (3 / 4 : ℝ)

theorem bernoulliSeriesAt_mul_exp_sub_one (t : ℝ) :
    bernoulliSeriesAt t * (PowerSeries.exp ℝ - 1) =
      PowerSeries.X * PowerSeries.rescale t (PowerSeries.exp ℝ) := by
  simpa [bernoulliSeriesAt] using (Polynomial.bernoulli_generating_function (A := ℝ) t)

private theorem expQuarter_mul_expQuarter :
    expQuarter * expQuarter = expHalf := by
  rw [expQuarter, expHalf]
  have hadd : (1 / 2 : ℝ) = 1 / 4 + 1 / 4 := by norm_num
  rw [hadd]
  exact PowerSeries.exp_mul_exp_eq_exp_add (A := ℝ) (1 / 4 : ℝ) (1 / 4 : ℝ)

private theorem expQuarter_mul_expNegQuarter :
    expQuarter * expNegQuarter = 1 := by
  simpa [expQuarter, expNegQuarter] using
    (PowerSeries.exp_mul_exp_eq_exp_add (A := ℝ) (1 / 4 : ℝ) (-(1 / 4 : ℝ)))

private theorem expQuarter_mul_expHalf :
    expQuarter * expHalf = expThreeQuarter := by
  rw [expQuarter, expHalf, expThreeQuarter]
  have hadd : (3 / 4 : ℝ) = 1 / 4 + 1 / 2 := by norm_num
  rw [hadd]
  exact PowerSeries.exp_mul_exp_eq_exp_add (A := ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ)

private theorem expHalf_mul_expHalf :
    expHalf * expHalf = PowerSeries.exp ℝ := by
  calc
    expHalf * expHalf = PowerSeries.rescale ((1 / 2 : ℝ) + 1 / 2) (PowerSeries.exp ℝ) := by
      simpa [expHalf] using
        (PowerSeries.exp_mul_exp_eq_exp_add (A := ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ))
    _ = PowerSeries.exp ℝ := by
          have hfun :
              PowerSeries.rescale ((1 / 2 : ℝ) + 1 / 2) = RingHom.id (PowerSeries ℝ) := by
            ext φ n
            have hadd : ((1 / 2 : ℝ) + 1 / 2) = 1 := by norm_num
            rw [PowerSeries.coeff_rescale, hadd]
            simp
          simpa using congrArg (fun φ => φ (PowerSeries.exp ℝ)) hfun

private theorem exp_sub_one_factor :
    PowerSeries.exp ℝ - 1 =
      expQuarter * (expHalf - 1) * (expQuarter + expNegQuarter) := by
  calc
    PowerSeries.exp ℝ - 1
        = PowerSeries.exp ℝ + expHalf - expHalf - 1 := by ring
    _ = expQuarter * (expHalf - 1) * (expQuarter + expNegQuarter) := by
          calc
            PowerSeries.exp ℝ + expHalf - expHalf - 1
                = expQuarter * expHalf * expQuarter + expQuarter * expHalf * expNegQuarter -
                    expQuarter * expQuarter - expQuarter * expNegQuarter := by
                      rw [show expQuarter * expHalf * expQuarter = PowerSeries.exp ℝ by
                            calc
                              expQuarter * expHalf * expQuarter =
                                  expHalf * (expQuarter * expQuarter) := by ring
                              _ = expHalf * expHalf := by rw [expQuarter_mul_expQuarter]
                              _ = PowerSeries.exp ℝ := expHalf_mul_expHalf,
                          show expQuarter * expHalf * expNegQuarter = expHalf by
                            calc
                              expQuarter * expHalf * expNegQuarter =
                                  expHalf * (expQuarter * expNegQuarter) := by ring
                              _ = expHalf := by rw [expQuarter_mul_expNegQuarter]; ring,
                          expQuarter_mul_expQuarter, expQuarter_mul_expNegQuarter]
            _ = expQuarter * (expHalf - 1) * (expQuarter + expNegQuarter) := by
                  ring

private theorem expQuarter_sub_expThreeQuarter_factor :
    expQuarter - expThreeQuarter = -(expQuarter * (expHalf - 1)) := by
  rw [← expQuarter_mul_expHalf]
  ring

private theorem expQuarter_ne_zero : expQuarter ≠ 0 := by
  intro h
  have hcoeff := congrArg (PowerSeries.coeff 0) h
  simp [expQuarter] at hcoeff

private theorem expHalf_sub_one_ne_zero : expHalf - 1 ≠ 0 := by
  intro h
  have hcoeff := congrArg (PowerSeries.coeff 1) h
  norm_num [expHalf] at hcoeff

theorem bernoulliQuarterOddSeries_mul_expQuarter_add_expNegQuarter :
    bernoulliQuarterOddSeries * (expQuarter + expNegQuarter) = -PowerSeries.X := by
  have h14 :
      bernoulliSeriesAt (1 / 4 : ℝ) * (PowerSeries.exp ℝ - 1) =
        PowerSeries.X * expQuarter := by
    simpa [expQuarter] using bernoulliSeriesAt_mul_exp_sub_one (1 / 4 : ℝ)
  have h34 :
      bernoulliSeriesAt (3 / 4 : ℝ) * (PowerSeries.exp ℝ - 1) =
        PowerSeries.X * expThreeQuarter := by
    simpa [expThreeQuarter] using bernoulliSeriesAt_mul_exp_sub_one (3 / 4 : ℝ)
  have hcommon : expQuarter * (expHalf - 1) ≠ 0 := by
    exact mul_ne_zero expQuarter_ne_zero expHalf_sub_one_ne_zero
  apply mul_right_cancel₀ hcommon
  calc
    (bernoulliQuarterOddSeries * (expQuarter + expNegQuarter)) * (expQuarter * (expHalf - 1))
        = bernoulliQuarterOddSeries * (PowerSeries.exp ℝ - 1) := by
            rw [bernoulliQuarterOddSeries, exp_sub_one_factor]
            ring
    _ = PowerSeries.X * expQuarter - PowerSeries.X * expThreeQuarter := by
          rw [bernoulliQuarterOddSeries, sub_mul, h14, h34]
    _ = -PowerSeries.X * (expQuarter * (expHalf - 1)) := by
          calc
            PowerSeries.X * expQuarter - PowerSeries.X * expThreeQuarter =
                PowerSeries.X * (expQuarter - expThreeQuarter) := by ring
            _ = -PowerSeries.X * (expQuarter * (expHalf - 1)) := by
                  rw [expQuarter_sub_expThreeQuarter_factor]
                  ring

private theorem eval_map_bernoulli_threeQuarter (n : ℕ) :
    Polynomial.eval (3 / 4 : ℝ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)) =
      (-1 : ℝ) ^ n *
        Polynomial.eval (1 / 4 : ℝ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)) := by
  have hq : (Polynomial.bernoulli n).eval (1 - (1 / 4 : ℚ)) =
      (-1 : ℚ) ^ n * (Polynomial.bernoulli n).eval (1 / 4 : ℚ) := by
    simpa using Polynomial.bernoulli_eval_one_sub n (1 / 4 : ℚ)
  have hq' :
      (((Polynomial.bernoulli n).eval (1 - (1 / 4 : ℚ)) : ℚ) : ℝ) =
        (-1 : ℝ) ^ n * (((Polynomial.bernoulli n).eval (1 / 4 : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast hq
  have hleft' :
      Polynomial.eval (1 - (1 / 4 : ℝ)) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)) =
        (((Polynomial.bernoulli n).eval (1 - (1 / 4 : ℚ)) : ℚ) : ℝ) := by
    simpa [Polynomial.eval_map] using
      (Polynomial.eval₂_at_apply (p := Polynomial.bernoulli n) (algebraMap ℚ ℝ) (1 - (1 / 4 : ℚ)))
  have hleft :
      Polynomial.eval (3 / 4 : ℝ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)) =
        (((Polynomial.bernoulli n).eval (1 - (1 / 4 : ℚ)) : ℚ) : ℝ) := by
    rw [← show (1 - (1 / 4 : ℝ)) = (3 / 4 : ℝ) by norm_num]
    exact hleft'
  have hright :
      Polynomial.eval (1 / 4 : ℝ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)) =
        (((Polynomial.bernoulli n).eval (1 / 4 : ℚ) : ℚ) : ℝ) := by
    simpa [Polynomial.eval_map] using
      (Polynomial.eval₂_at_apply (p := Polynomial.bernoulli n) (algebraMap ℚ ℝ) (1 / 4 : ℚ))
  calc
    Polynomial.eval (3 / 4 : ℝ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n))
        = (((Polynomial.bernoulli n).eval (1 - (1 / 4 : ℚ)) : ℚ) : ℝ) := hleft
    _ = (-1 : ℝ) ^ n * (((Polynomial.bernoulli n).eval (1 / 4 : ℚ) : ℚ) : ℝ) := hq'
    _ = (-1 : ℝ) ^ n *
          Polynomial.eval (1 / 4 : ℝ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)) := by
          congr 1
          exact hright.symm

private theorem aeval_scaled_bernoulli_threeQuarter (n : ℕ) :
    Polynomial.aeval (3 / 4 : ℝ)
        (((1 : ℚ) / ((n.factorial : ℕ) : ℚ)) • Polynomial.bernoulli n) =
      (-1 : ℝ) ^ n *
        Polynomial.aeval (1 / 4 : ℝ)
          (((1 : ℚ) / ((n.factorial : ℕ) : ℚ)) • Polynomial.bernoulli n) := by
  rw [Polynomial.smul_eq_C_mul, Polynomial.aeval_def, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_eq_eval_map, Polynomial.aeval_def, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_eq_eval_map, eval_map_bernoulli_threeQuarter]
  ring

private theorem aeval_bernoulli_threeQuarter (n : ℕ) :
    Polynomial.aeval (3 / 4 : ℝ) (Polynomial.bernoulli n) =
      (-1 : ℝ) ^ n * Polynomial.aeval (1 / 4 : ℝ) (Polynomial.bernoulli n) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    Polynomial.eval₂_eq_eval_map]
  simpa using eval_map_bernoulli_threeQuarter n

theorem coeff_bernoulliQuarterOddSeries_odd (m : ℕ) :
    PowerSeries.coeff (2 * m + 1) bernoulliQuarterOddSeries =
      2 *
        Polynomial.aeval (1 / 4 : ℝ)
          (((1 : ℚ) / (((2 * m + 1).factorial : ℕ) : ℚ)) •
            Polynomial.bernoulli (2 * m + 1)) := by
  rw [bernoulliQuarterOddSeries, map_sub]
  simp [bernoulliSeriesAt]
  rw [aeval_bernoulli_threeQuarter (2 * m + 1)]
  have hodd : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hodd]
  have hquarter : ((4 : ℝ)⁻¹) = (1 / 4 : ℝ) := by norm_num
  rw [hquarter]
  rw [show (-1 : ℝ) * Polynomial.aeval (1 / 4 : ℝ) (Polynomial.bernoulli (2 * m + 1)) =
      -Polynomial.aeval (1 / 4 : ℝ) (Polynomial.bernoulli (2 * m + 1)) by ring]
  rw [show (2 : ℝ) * Polynomial.aeval (1 / 4 : ℝ) (Polynomial.bernoulli (2 * m + 1)) =
      Polynomial.aeval (1 / 4 : ℝ) (Polynomial.bernoulli (2 * m + 1)) * 2 by ring]
  rw [sub_eq_add_neg, smul_neg, neg_neg,
    show Polynomial.aeval (1 / 4 : ℝ) (Polynomial.bernoulli (2 * m + 1)) * 2 =
      Polynomial.aeval (1 / 4 : ℝ) (Polynomial.bernoulli (2 * m + 1)) +
        Polynomial.aeval (1 / 4 : ℝ) (Polynomial.bernoulli (2 * m + 1)) by ring,
    smul_add]

private noncomputable def dirichletBetaOddSinTerm (n m : ℕ) : ℝ :=
  1 / ((m : ℝ) ^ (2 * n + 5 : ℕ)) * Real.sin (Real.pi * m / 2)

private theorem dirichletBetaOddSinTerm_zero (n : ℕ) :
    dirichletBetaOddSinTerm n 0 = 0 := by
  simp [dirichletBetaOddSinTerm]

private theorem dirichletBetaOddSinTerm_four_mul_add_one (n k : ℕ) :
    dirichletBetaOddSinTerm n (4 * k + 1) = 1 / ((4 * k + 1 : ℝ) ^ (2 * n + 5 : ℕ)) := by
  have hang :
      Real.pi * (4 * k + 1 : ℝ) / 2 = Real.pi / 2 + k * (2 * Real.pi) := by
    ring
  have hsin : Real.sin (Real.pi * (4 * k + 1 : ℝ) / 2) = 1 := by
    rw [hang]
    simpa [Real.sin_pi_div_two] using (Real.sin_add_nat_mul_two_pi (Real.pi / 2) k)
  simp [dirichletBetaOddSinTerm, hsin]

private theorem dirichletBetaOddSinTerm_four_mul_add_two (n k : ℕ) :
    dirichletBetaOddSinTerm n (4 * k + 2) = 0 := by
  have hang :
      Real.pi * (4 * k + 2 : ℝ) / 2 = k * (2 * Real.pi) + Real.pi := by
    ring
  have hsin : Real.sin (Real.pi * (4 * k + 2 : ℝ) / 2) = 0 := by
    rw [hang, Real.sin_add_pi]
    simpa [Real.sin_zero] using (Real.sin_add_nat_mul_two_pi 0 k)
  simp [dirichletBetaOddSinTerm, hsin]

private theorem dirichletBetaOddSinTerm_four_mul_add_three (n k : ℕ) :
    dirichletBetaOddSinTerm n (4 * k + 3) = -1 / ((4 * k + 3 : ℝ) ^ (2 * n + 5 : ℕ)) := by
  have hang :
      Real.pi * (4 * k + 3 : ℝ) / 2 = (Real.pi / 2 + k * (2 * Real.pi)) + Real.pi := by
    ring
  have hsin : Real.sin (Real.pi * (4 * k + 3 : ℝ) / 2) = -1 := by
    rw [hang, Real.sin_add_pi]
    simpa [Real.sin_pi_div_two] using (Real.sin_add_nat_mul_two_pi (Real.pi / 2) k)
  calc
    dirichletBetaOddSinTerm n (4 * k + 3)
        = (1 / ((4 * k + 3 : ℝ) ^ (2 * n + 5 : ℕ))) * (-1) := by
            simp [dirichletBetaOddSinTerm, hsin]
    _ = -1 / ((4 * k + 3 : ℝ) ^ (2 * n + 5 : ℕ)) := by ring

private theorem dirichletBetaOddSinTerm_four_mul_add_four (n k : ℕ) :
    dirichletBetaOddSinTerm n (4 * k + 4) = 0 := by
  have hang :
      Real.pi * (4 * k + 4 : ℝ) / 2 = 0 + (k + 1) * (2 * Real.pi) := by
    ring
  have hsin : Real.sin (Real.pi * (4 * k + 4 : ℝ) / 2) = 0 := by
    rw [hang]
    simpa [Real.sin_zero] using (Real.sin_add_nat_mul_two_pi 0 (k + 1))
  simp [dirichletBetaOddSinTerm, hsin]

private theorem sum_range_four_mul_add_four_dirichletBetaOddSinTerm (n N : ℕ) :
    ∑ m ∈ Finset.range (4 * N + 4), dirichletBetaOddSinTerm n m =
      1 - 1 / ((3 : ℝ) ^ (2 * n + 5 : ℕ)) +
        ∑ k ∈ Finset.range N, dirichletBetaOddTailTerm n k := by
  induction N with
  | zero =>
      conv_lhs =>
        rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ,
          show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_range_succ,
          show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ,
          show (1 : ℕ) = 0 + 1 by norm_num, Finset.sum_range_succ]
      have h1 : dirichletBetaOddSinTerm n 1 = 1 := by
        simpa using dirichletBetaOddSinTerm_four_mul_add_one n 0
      have h2 : dirichletBetaOddSinTerm n 2 = 0 := by
        simpa using dirichletBetaOddSinTerm_four_mul_add_two n 0
      have h3 : dirichletBetaOddSinTerm n 3 = -1 / ((3 : ℝ) ^ (2 * n + 5 : ℕ)) := by
        simpa using dirichletBetaOddSinTerm_four_mul_add_three n 0
      rw [sub_eq_add_neg]
      simpa [div_eq_mul_inv, dirichletBetaOddSinTerm_zero, h1, h2, h3]
  | succ N ih =>
      rw [show 4 * (N + 1) + 4 = (4 * N + 4) + 4 by ring, Finset.sum_range_add, ih]
      have hblock :
          ∑ x ∈ Finset.range 4, dirichletBetaOddSinTerm n (4 * N + 4 + x) =
            dirichletBetaOddTailTerm n N := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ,
          show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_range_succ,
          show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ,
          show (1 : ℕ) = 0 + 1 by norm_num, Finset.sum_range_succ]
        simp [dirichletBetaOddTailTerm, dirichletBetaOddSinTerm_four_mul_add_one,
          dirichletBetaOddSinTerm_four_mul_add_two, dirichletBetaOddSinTerm_four_mul_add_three,
          dirichletBetaOddSinTerm_four_mul_add_four,
          show 4 * N + 4 + 0 = 4 * N + 4 by ring,
          show 4 * N + 4 + 1 = 4 * (N + 1) + 1 by ring,
          show 4 * N + 4 + 2 = 4 * (N + 1) + 2 by ring,
          show 4 * N + 4 + 3 = 4 * (N + 1) + 3 by ring]
        ring_nf
      rw [hblock, Finset.sum_range_succ]
      ring

private theorem hasSum_dirichletBetaOddSinTerm (n : ℕ) :
    HasSum (dirichletBetaOddSinTerm n) (dirichletBetaOddShift n) := by
  have hsummable :
      Summable (dirichletBetaOddSinTerm n) := by
    have hsin :=
      hasSum_one_div_nat_pow_mul_sin (k := n + 2) (Nat.succ_ne_zero _) (by
        constructor <;> norm_num : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    refine hsin.summable.congr ?_
    intro m
    rw [dirichletBetaOddSinTerm]
    congr 1
    ring
  have hNat : Tendsto (fun N : ℕ ↦ 4 * N + 4) atTop atTop := by
    refine tendsto_atTop.mpr ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hsubseq :
      Tendsto
        (fun N : ℕ => ∑ m ∈ Finset.range (4 * N + 4), dirichletBetaOddSinTerm n m)
        atTop (nhds (∑' m : ℕ, dirichletBetaOddSinTerm n m)) := by
    simpa using hsummable.hasSum.tendsto_sum_nat.comp hNat
  have hblocks :
      Tendsto
        (fun N : ℕ => ∑ m ∈ Finset.range (4 * N + 4), dirichletBetaOddSinTerm n m)
        atTop (nhds (dirichletBetaOddShift n)) := by
    have htail :
        Tendsto
          (fun N : ℕ => ∑ k ∈ Finset.range N, dirichletBetaOddTailTerm n k)
          atTop (nhds (∑' k : ℕ, dirichletBetaOddTailTerm n k)) :=
      (dirichletBetaOddTailTerm_summable n).hasSum.tendsto_sum_nat
    refine htail.const_add (1 - 1 / ((3 : ℝ) ^ (2 * n + 5 : ℕ))) |>.congr' ?_
    exact Filter.Eventually.of_forall fun N =>
      (sum_range_four_mul_add_four_dirichletBetaOddSinTerm n N).symm
  have htsum :
      (∑' m : ℕ, dirichletBetaOddSinTerm n m) = dirichletBetaOddShift n :=
    tendsto_nhds_unique hsubseq hblocks
  simpa [htsum] using hsummable.hasSum

theorem coeff_bernoulliQuarterOddSeries_odd_eq_dirichletBetaOddShift (n : ℕ) :
    PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries =
      (-1 : ℝ) ^ (n + 3) * 4 * dirichletBetaOddShift n / (2 * Real.pi) ^ (2 * n + 5) := by
  have hsin :
      HasSum (dirichletBetaOddSinTerm n)
        (((-1 : ℝ) ^ (n + 3) * (2 * Real.pi) ^ (2 * n + 5) / 4) *
          PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries) := by
    have hbase :=
      hasSum_one_div_nat_pow_mul_sin (k := n + 2) (Nat.succ_ne_zero _) (by
        constructor <;> norm_num : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    convert hbase using 1
    · ext m
      rw [dirichletBetaOddSinTerm]
      congr 1
      ring
    · have hscaled :
          Polynomial.aeval (1 / 4 : ℝ)
              (((1 : ℚ) / (((2 * (n + 2) + 1).factorial : ℕ) : ℚ)) •
                Polynomial.bernoulli (2 * (n + 2) + 1)) =
            ((((2 * (n + 2) + 1).factorial : ℕ) : ℝ))⁻¹ *
              Polynomial.eval (1 / 4 : ℝ)
                (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * (n + 2) + 1))) := by
        rw [Polynomial.smul_eq_C_mul, Polynomial.aeval_def, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_eq_eval_map]
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [coeff_bernoulliQuarterOddSeries_odd (n + 2), hscaled]
      ring
  have hEq :
      (((-1 : ℝ) ^ (n + 3) * (2 * Real.pi) ^ (2 * n + 5) / 4) *
          PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries) =
        dirichletBetaOddShift n :=
    hsin.unique (hasSum_dirichletBetaOddSinTerm n)
  have hsign :
      (-1 : ℝ) ^ (n + 3) * (-1 : ℝ) ^ (n + 3) = 1 := by
    rw [← pow_add]
    simp
  have hpow : ((2 * Real.pi : ℝ) ^ (2 * n + 5)) ≠ 0 := by positivity
  have hEq' :
      (2 * Real.pi : ℝ) ^ (2 * n + 5) *
          PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries =
        (-1 : ℝ) ^ (n + 3) * 4 * dirichletBetaOddShift n := by
    calc
      (2 * Real.pi : ℝ) ^ (2 * n + 5) *
          PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries
          =
        (-1 : ℝ) ^ (n + 3) * 4 *
          (((( -1 : ℝ) ^ (n + 3) * (2 * Real.pi) ^ (2 * n + 5) / 4) *
            PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries)) := by
              have hsign_sq : ((-1 : ℝ) ^ (n + 3)) ^ 2 = 1 := by
                rw [pow_two]
                simpa [mul_comm] using hsign
              field_simp [hpow]
              rw [hsign_sq]
              ring
      _ = (-1 : ℝ) ^ (n + 3) * 4 * dirichletBetaOddShift n := by rw [hEq]
  calc
    PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries
        =
      ((2 * Real.pi : ℝ) ^ (2 * n + 5) *
          PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries) /
        (2 * Real.pi) ^ (2 * n + 5) := by
          field_simp [hpow]
    _ = ((-1 : ℝ) ^ (n + 3) * 4 * dirichletBetaOddShift n) / (2 * Real.pi) ^ (2 * n + 5) := by
          rw [hEq']
    _ = (-1 : ℝ) ^ (n + 3) * 4 * dirichletBetaOddShift n / (2 * Real.pi) ^ (2 * n + 5) := by
          ring

end BernoulliQuarter

end XiZeroLimit
