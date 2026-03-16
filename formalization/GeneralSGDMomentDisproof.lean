import Mathlib

namespace GeneralSGDMomentDisproof

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

/--
A geometric law with success probability `15/16`. Together with the dyadic random variable
`n ↦ 2^n`, this gives the one-coordinate heavy-tail input for the repaired Attempt 16
counterexample.

This opening block isolates the finite-third / infinite-sixth moment calculation that is later
reused in the centered AR(1) construction. It is still independent from the separate literal
printed-statement theorem `attemptSixteen_conjecture_disconfirmed` below.
-/
def attemptSixteenGeomPmf : PMF ℕ :=
  ProbabilityTheory.geometricPMF (p := (15 : ℝ) / 16) (by norm_num) (by norm_num)

def attemptSixteenGeomMeasure : Measure ℕ :=
  attemptSixteenGeomPmf.toMeasure

def attemptSixteenNoise : ℕ → ℝ :=
  fun n ↦ (2 : ℝ) ^ n

@[simp]
lemma attemptSixteenGeomMeasure_singleton (n : ℕ) :
    attemptSixteenGeomMeasure {n} = ENNReal.ofReal (((1 / 16 : ℝ) ^ n) * (15 / 16)) := by
  rw [attemptSixteenGeomMeasure,
    PMF.toMeasure_apply_singleton attemptSixteenGeomPmf n (MeasurableSet.singleton n)]
  norm_num [attemptSixteenGeomPmf, ProbabilityTheory.geometricPMF,
    ProbabilityTheory.geometricPMFReal]
  rfl

lemma attemptSixteenNoise_pow_three (n : ℕ) :
    attemptSixteenNoise n ^ 3 = (8 : ℝ) ^ n := by
  calc
    attemptSixteenNoise n ^ 3 = ((2 : ℝ) ^ n) ^ 3 := by rfl
    _ = (2 : ℝ) ^ (n * 3) := by rw [pow_mul]
    _ = (2 : ℝ) ^ (3 * n) := by rw [Nat.mul_comm]
    _ = ((2 : ℝ) ^ 3) ^ n := by rw [pow_mul]
    _ = (8 : ℝ) ^ n := by norm_num

lemma attemptSixteenNoise_pow_six (n : ℕ) :
    attemptSixteenNoise n ^ 6 = (64 : ℝ) ^ n := by
  calc
    attemptSixteenNoise n ^ 6 = ((2 : ℝ) ^ n) ^ 6 := by rfl
    _ = (2 : ℝ) ^ (n * 6) := by rw [pow_mul]
    _ = (2 : ℝ) ^ (6 * n) := by rw [Nat.mul_comm]
    _ = ((2 : ℝ) ^ 6) ^ n := by rw [pow_mul]
    _ = (64 : ℝ) ^ n := by norm_num

lemma attemptSixteen_thirdMoment_term (n : ℕ) :
    ENNReal.ofReal (attemptSixteenNoise n ^ 3) * attemptSixteenGeomMeasure {n} =
      ENNReal.ofReal (15 / 16 : ℝ) * (ENNReal.ofReal (1 / 2 : ℝ) ^ n) := by
  rw [attemptSixteenNoise_pow_three, attemptSixteenGeomMeasure_singleton]
  have hreal :
      (8 : ℝ) ^ n * ((1 / 16 : ℝ) ^ n * (15 / 16))
        = (15 / 16 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
    calc
      (8 : ℝ) ^ n * ((1 / 16 : ℝ) ^ n * (15 / 16))
          = ((8 : ℝ) ^ n * (1 / 16 : ℝ) ^ n) * (15 / 16) := by ring
      _ = ((8 : ℝ) * (1 / 16 : ℝ)) ^ n * (15 / 16) := by rw [← mul_pow]
      _ = ((1 / 2 : ℝ) ^ n) * (15 / 16) := by norm_num
      _ = (15 / 16 : ℝ) * ((1 / 2 : ℝ) ^ n) := by ring
  have h8_nonneg : 0 ≤ (8 : ℝ) ^ n := by positivity
  have hgeom_nonneg : 0 ≤ ((1 / 16 : ℝ) ^ n) * (15 / 16) := by positivity
  have hconst_nonneg : 0 ≤ (15 / 16 : ℝ) := by positivity
  rw [← ENNReal.ofReal_mul h8_nonneg, hreal, ENNReal.ofReal_mul hconst_nonneg]
  rw [ENNReal.ofReal_pow (by positivity : 0 ≤ (1 / 2 : ℝ)) n]

lemma attemptSixteen_firstMoment_term (n : ℕ) :
    ENNReal.ofReal (attemptSixteenNoise n) * attemptSixteenGeomMeasure {n} =
      ENNReal.ofReal (15 / 16 : ℝ) * (ENNReal.ofReal (1 / 8 : ℝ) ^ n) := by
  rw [attemptSixteenGeomMeasure_singleton]
  have hreal :
      (2 : ℝ) ^ n * ((1 / 16 : ℝ) ^ n * (15 / 16))
        = (15 / 16 : ℝ) * ((1 / 8 : ℝ) ^ n) := by
    calc
      (2 : ℝ) ^ n * ((1 / 16 : ℝ) ^ n * (15 / 16))
          = ((2 : ℝ) ^ n * (1 / 16 : ℝ) ^ n) * (15 / 16) := by ring
      _ = ((2 : ℝ) * (1 / 16 : ℝ)) ^ n * (15 / 16) := by rw [← mul_pow]
      _ = ((1 / 8 : ℝ) ^ n) * (15 / 16) := by norm_num
      _ = (15 / 16 : ℝ) * ((1 / 8 : ℝ) ^ n) := by ring
  have h2_nonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hgeom_nonneg : 0 ≤ ((1 / 16 : ℝ) ^ n) * (15 / 16) := by positivity
  have hconst_nonneg : 0 ≤ (15 / 16 : ℝ) := by positivity
  rw [attemptSixteenNoise, ← ENNReal.ofReal_mul h2_nonneg, hreal, ENNReal.ofReal_mul hconst_nonneg]
  rw [ENNReal.ofReal_pow (by positivity : 0 ≤ (1 / 8 : ℝ)) n]

lemma attemptSixteen_sixthMoment_term (n : ℕ) :
    ENNReal.ofReal (attemptSixteenNoise n ^ 6) * attemptSixteenGeomMeasure {n} =
      ENNReal.ofReal (15 / 16 : ℝ) * (ENNReal.ofReal (4 : ℝ) ^ n) := by
  rw [attemptSixteenNoise_pow_six, attemptSixteenGeomMeasure_singleton]
  have hreal :
      (64 : ℝ) ^ n * ((1 / 16 : ℝ) ^ n * (15 / 16))
        = (15 / 16 : ℝ) * ((4 : ℝ) ^ n) := by
    calc
      (64 : ℝ) ^ n * ((1 / 16 : ℝ) ^ n * (15 / 16))
          = ((64 : ℝ) ^ n * (1 / 16 : ℝ) ^ n) * (15 / 16) := by ring
      _ = ((64 : ℝ) * (1 / 16 : ℝ)) ^ n * (15 / 16) := by rw [← mul_pow]
      _ = ((4 : ℝ) ^ n) * (15 / 16) := by norm_num
      _ = (15 / 16 : ℝ) * ((4 : ℝ) ^ n) := by ring
  have h64_nonneg : 0 ≤ (64 : ℝ) ^ n := by positivity
  have hgeom_nonneg : 0 ≤ ((1 / 16 : ℝ) ^ n) * (15 / 16) := by positivity
  have hconst_nonneg : 0 ≤ (15 / 16 : ℝ) := by positivity
  have hfour_nonneg : 0 ≤ (4 : ℝ) ^ n := by positivity
  rw [← ENNReal.ofReal_mul h64_nonneg, hreal, ENNReal.ofReal_mul hconst_nonneg]
  simp

/--
The dyadic heavy-tail witness already has finite first moment under the geometric law.
-/
theorem attemptSixteen_noise_firstMoment_integrable :
    Integrable attemptSixteenNoise attemptSixteenGeomMeasure := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal]
  · rw [MeasureTheory.lintegral_countable']
    simp_rw [attemptSixteen_firstMoment_term]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hOneEighth : ENNReal.ofReal (1 / 8 : ℝ) = (1 / 8 : ENNReal) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    have hgeom_ne_top : (1 - (1 / 8 : ENNReal))⁻¹ ≠ ⊤ := by
      rw [ENNReal.inv_ne_top]
      exact ne_of_gt (by norm_num : (0 : ENNReal) < 1 - (1 / 8 : ENNReal))
    rw [hOneEighth]
    exact lt_top_iff_ne_top.2 <| ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgeom_ne_top
  · exact Filter.Eventually.of_forall fun n ↦ by
      dsimp [attemptSixteenNoise]
      positivity

/--
The dyadic heavy-tail witness has finite third moment under the geometric law.
-/
theorem attemptSixteen_noise_thirdMoment_integrable :
    Integrable (fun n ↦ attemptSixteenNoise n ^ 3) attemptSixteenGeomMeasure := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal]
  · rw [MeasureTheory.lintegral_countable']
    simp_rw [attemptSixteen_thirdMoment_term]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    have hgeom : (1 - (1 / 2 : ENNReal))⁻¹ = (2 : ENNReal) := by
      norm_num
    rw [hhalf, hgeom]
    exact lt_top_iff_ne_top.2 <| ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  · exact Filter.Eventually.of_forall fun n ↦ by
      dsimp [attemptSixteenNoise]
      positivity

/--
The same witness has divergent sixth moment, showing the gap in Attempt 16's conjectured
`3h`-moment conclusion already in the quadratic (`h = 2`) regime.
-/
theorem attemptSixteen_noise_sixthMoment_not_integrable :
    ¬ Integrable (fun n ↦ attemptSixteenNoise n ^ 6) attemptSixteenGeomMeasure := by
  intro hInt
  have hfi := hInt.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal] at hfi
  · rw [MeasureTheory.lintegral_countable'] at hfi
    simp_rw [attemptSixteen_sixthMoment_term] at hfi
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric] at hfi
    have hfour : ENNReal.ofReal (4 : ℝ) = (4 : ENNReal) := by
      norm_num
    have hgeom : (1 - ENNReal.ofReal (4 : ℝ))⁻¹ = (⊤ : ENNReal) := by
      rw [hfour]
      have hsub : (1 - (4 : ENNReal)) = 0 := by
        exact tsub_eq_zero_of_le (by norm_num : (1 : ENNReal) ≤ 4)
      rw [hsub]
      simp
    rw [hgeom] at hfi
    norm_num at hfi
  · exact Filter.Eventually.of_forall fun n ↦ by
      dsimp [attemptSixteenNoise]
      positivity

def attemptSixteenHalf : ENNReal :=
  ENNReal.ofReal (1 / 2 : ℝ)

lemma attemptSixteenHalf_eq : attemptSixteenHalf = (1 / 2 : ENNReal) := by
  rw [attemptSixteenHalf, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

lemma attemptSixteenHalf_ne_top : attemptSixteenHalf ≠ ⊤ := by
  simp [attemptSixteenHalf]

def attemptSixteenSignMeasure : Measure Bool :=
  attemptSixteenHalf • Measure.dirac true + attemptSixteenHalf • Measure.dirac false

instance : IsProbabilityMeasure attemptSixteenGeomMeasure := by
  dsimp [attemptSixteenGeomMeasure]
  infer_instance

instance : IsProbabilityMeasure attemptSixteenSignMeasure := by
  refine ⟨by
    rw [attemptSixteenSignMeasure, Measure.add_apply]
    · rw [Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply_of_mem (by simp), Measure.dirac_apply_of_mem (by simp)]
      · rw [attemptSixteenHalf_eq]
        simpa using (ENNReal.add_halves (1 : ENNReal))
    ⟩

def attemptSixteenSignValue (b : Bool) : ℝ :=
  if b then 1 else -1

def attemptSixteenCenteredNoiseMeasure : Measure (Bool × ℕ) :=
  attemptSixteenSignMeasure.prod attemptSixteenGeomMeasure

def attemptSixteenCenteredNoiseValue : Bool × ℕ → ℝ
  | (b, n) => attemptSixteenSignValue b * attemptSixteenNoise n

lemma attemptSixteenCenteredNoiseValue_measurable :
    Measurable attemptSixteenCenteredNoiseValue :=
  measurable_of_countable _

lemma attemptSixteenCenteredNoise_abs_pow_three (z : Bool × ℕ) :
    |attemptSixteenCenteredNoiseValue z| ^ 3 = attemptSixteenNoise z.2 ^ 3 := by
  rcases z with ⟨b, n⟩
  have hnonneg : 0 ≤ attemptSixteenNoise n := by
    dsimp [attemptSixteenNoise]
    positivity
  by_cases hb : b
  · simp [attemptSixteenCenteredNoiseValue, attemptSixteenSignValue, hb, abs_of_nonneg hnonneg]
  · simp [attemptSixteenCenteredNoiseValue, attemptSixteenSignValue, hb, abs_of_nonneg hnonneg]

lemma attemptSixteenCenteredNoise_abs_pow_six (z : Bool × ℕ) :
    |attemptSixteenCenteredNoiseValue z| ^ 6 = attemptSixteenNoise z.2 ^ 6 := by
  rcases z with ⟨b, n⟩
  have hnonneg : 0 ≤ attemptSixteenNoise n := by
    dsimp [attemptSixteenNoise]
    positivity
  by_cases hb : b
  · simp [attemptSixteenCenteredNoiseValue, attemptSixteenSignValue, hb, abs_of_nonneg hnonneg]
  · simp [attemptSixteenCenteredNoiseValue, attemptSixteenSignValue, hb, abs_of_nonneg hnonneg]

lemma attemptSixteenSignMeasure_ne_zero : attemptSixteenSignMeasure ≠ 0 := by
  exact IsProbabilityMeasure.ne_zero attemptSixteenSignMeasure

/--
A centered version of the dyadic heavy-tail noise: a fair random sign times the same geometric
dyadic magnitude.
-/
theorem attemptSixteenCenteredNoise_thirdMoment_integrable :
    Integrable (fun z ↦ |attemptSixteenCenteredNoiseValue z| ^ 3)
      attemptSixteenCenteredNoiseMeasure := by
  have hbase :
      Integrable (fun z : Bool × ℕ ↦ attemptSixteenNoise z.2 ^ 3)
        attemptSixteenCenteredNoiseMeasure := by
    simpa [attemptSixteenCenteredNoiseMeasure] using
      attemptSixteen_noise_thirdMoment_integrable.comp_snd attemptSixteenSignMeasure
  refine hbase.congr ?_
  filter_upwards with z
  rw [attemptSixteenCenteredNoise_abs_pow_three]

/--
The centered dyadic heavy-tail noise still has divergent sixth moment.
-/
theorem attemptSixteenCenteredNoise_sixthMoment_not_integrable :
    ¬ Integrable (fun z ↦ |attemptSixteenCenteredNoiseValue z| ^ 6)
      attemptSixteenCenteredNoiseMeasure := by
  intro hInt
  have hbase :
      Integrable (fun z : Bool × ℕ ↦ attemptSixteenNoise z.2 ^ 6)
        attemptSixteenCenteredNoiseMeasure := by
    refine hInt.congr ?_
    filter_upwards with z
    rw [attemptSixteenCenteredNoise_abs_pow_six]
  have hgeom :
      Integrable (fun n ↦ attemptSixteenNoise n ^ 6) attemptSixteenGeomMeasure := by
    have :=
      (Integrable.comp_snd_iff (μ := attemptSixteenSignMeasure)
        (ν := attemptSixteenGeomMeasure) (f := fun n ↦ attemptSixteenNoise n ^ 6)
        attemptSixteenSignMeasure_ne_zero).mp hbase
    simpa using this
  exact attemptSixteen_noise_sixthMoment_not_integrable hgeom

theorem attemptSixteenCenteredNoise_firstMoment_integrable :
    Integrable (fun z ↦ |attemptSixteenCenteredNoiseValue z|)
      attemptSixteenCenteredNoiseMeasure := by
  have hbase :
      Integrable (fun z : Bool × ℕ ↦ attemptSixteenNoise z.2)
        attemptSixteenCenteredNoiseMeasure := by
    simpa [attemptSixteenCenteredNoiseMeasure] using
      attemptSixteen_noise_firstMoment_integrable.comp_snd attemptSixteenSignMeasure
  refine hbase.congr ?_
  filter_upwards with z
  rcases z with ⟨b, n⟩
  have hnonneg : 0 ≤ attemptSixteenNoise n := by
    dsimp [attemptSixteenNoise]
    positivity
  by_cases hb : b
  · simp [attemptSixteenCenteredNoiseValue, attemptSixteenSignValue, hb, abs_of_nonneg hnonneg]
  · simp [attemptSixteenCenteredNoiseValue, attemptSixteenSignValue, hb, abs_of_nonneg hnonneg]

theorem attemptSixteenSignValue_integrable :
    Integrable attemptSixteenSignValue attemptSixteenSignMeasure := by
  have htrue : Integrable attemptSixteenSignValue (Measure.dirac true) := by
    refine integrable_dirac ?_
    simp [attemptSixteenSignValue]
  have hfalse : Integrable attemptSixteenSignValue (Measure.dirac false) := by
    refine integrable_dirac ?_
    simp [attemptSixteenSignValue]
  rw [attemptSixteenSignMeasure]
  exact (htrue.smul_measure attemptSixteenHalf_ne_top).add_measure
    (hfalse.smul_measure attemptSixteenHalf_ne_top)

theorem attemptSixteenCenteredNoise_centered :
    ∫ z, attemptSixteenCenteredNoiseValue z ∂ attemptSixteenCenteredNoiseMeasure = 0 := by
  have hsign_int :
      ∫ b, attemptSixteenSignValue b ∂ attemptSixteenSignMeasure = 0 := by
    have htrue : Integrable attemptSixteenSignValue (Measure.dirac true) := by
      refine integrable_dirac ?_
      simp [attemptSixteenSignValue]
    have hfalse : Integrable attemptSixteenSignValue (Measure.dirac false) := by
      refine integrable_dirac ?_
      simp [attemptSixteenSignValue]
    rw [attemptSixteenSignMeasure,
      integral_add_measure (htrue.smul_measure attemptSixteenHalf_ne_top)
        (hfalse.smul_measure attemptSixteenHalf_ne_top)]
    simp [attemptSixteenSignValue, integral_smul_measure, attemptSixteenHalf]
  have hnoise_int :
      Integrable (fun n ↦ attemptSixteenNoise n) attemptSixteenGeomMeasure :=
    attemptSixteen_noise_firstMoment_integrable
  have hprod_int :
      Integrable attemptSixteenCenteredNoiseValue attemptSixteenCenteredNoiseMeasure := by
    simpa [attemptSixteenCenteredNoiseMeasure, attemptSixteenCenteredNoiseValue] using
      attemptSixteenSignValue_integrable.mul_prod hnoise_int
  rw [attemptSixteenCenteredNoiseMeasure,
    integral_prod (f := fun z : Bool × ℕ ↦ attemptSixteenCenteredNoiseValue z) hprod_int]
  simp_rw [attemptSixteenCenteredNoiseValue, integral_const_mul]
  rw [integral_mul_const]
  simp [hsign_int]

def attemptSixteenCenteredProcessMeasure : Measure (ℕ → Bool × ℕ) :=
  Measure.infinitePi (fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure)

instance : IsProbabilityMeasure attemptSixteenCenteredNoiseMeasure := by
  dsimp [attemptSixteenCenteredNoiseMeasure]
  infer_instance

instance : IsProbabilityMeasure attemptSixteenCenteredProcessMeasure := by
  dsimp [attemptSixteenCenteredProcessMeasure]
  infer_instance

def attemptSixteenCenteredProcessValue (n : ℕ) (ω : ℕ → Bool × ℕ) : ℝ :=
  attemptSixteenCenteredNoiseValue (ω n)

def attemptSixteenCenteredShift (ω : ℕ → Bool × ℕ) : ℕ → Bool × ℕ :=
  fun n ↦ ω (n + 1)

lemma attemptSixteenCenteredProcessValue_measurable (n : ℕ) :
    Measurable (attemptSixteenCenteredProcessValue n) := by
  unfold attemptSixteenCenteredProcessValue
  exact attemptSixteenCenteredNoiseValue_measurable.comp (measurable_pi_apply n)

lemma attemptSixteenCenteredShift_measurable :
    Measurable attemptSixteenCenteredShift := by
  unfold attemptSixteenCenteredShift
  fun_prop

def attemptSixteenCenteredSeriesTerm (α : ℝ) (n : ℕ) (ω : ℕ → Bool × ℕ) : ℝ :=
  α * (1 - α) ^ n * attemptSixteenCenteredProcessValue n ω

def attemptSixteenCenteredPartialSum (α : ℝ) (n : ℕ) (ω : ℕ → Bool × ℕ) : ℝ :=
  Finset.sum (Finset.range n) fun i => attemptSixteenCenteredSeriesTerm α i ω

lemma attemptSixteenCenteredPartialSum_measurable (α : ℝ) (n : ℕ) :
    Measurable (attemptSixteenCenteredPartialSum α n) := by
  unfold attemptSixteenCenteredPartialSum attemptSixteenCenteredSeriesTerm
  refine Finset.measurable_sum (Finset.range n) ?_
  intro i hi
  exact measurable_const.mul <| attemptSixteenCenteredProcessValue_measurable i

def attemptSixteenCenteredSeries (α : ℝ) (ω : ℕ → Bool × ℕ) : ℝ :=
  ∑' n, attemptSixteenCenteredSeriesTerm α n ω

def attemptSixteenCenteredARIterate (α : ℝ) : ℕ → (ℕ → Bool × ℕ) → ℝ
  | 0 => 0
  | n + 1 => fun ω ↦
      (1 - α) * attemptSixteenCenteredARIterate α n ω +
        α * attemptSixteenCenteredProcessValue n ω

def attemptSixteenPrefixIndex (n : ℕ) : Type :=
  Fin n

instance (n : ℕ) : MeasurableSpace (attemptSixteenPrefixIndex n) := by
  dsimp [attemptSixteenPrefixIndex]
  infer_instance

instance (n : ℕ) : Fintype (attemptSixteenPrefixIndex n) := by
  dsimp [attemptSixteenPrefixIndex]
  infer_instance

def attemptSixteenPrefixRestrict (n : ℕ) (ω : ℕ → Bool × ℕ) :
    attemptSixteenPrefixIndex n → Bool × ℕ :=
  fun i ↦ ω i.1

def attemptSixteenPrefixMeasure (n : ℕ) : Measure (attemptSixteenPrefixIndex n → Bool × ℕ) :=
  Measure.pi (fun _ : attemptSixteenPrefixIndex n ↦ attemptSixteenCenteredNoiseMeasure)

def attemptSixteenPrefixRev (n : ℕ) : attemptSixteenPrefixIndex n ≃ attemptSixteenPrefixIndex n where
  toFun i := ⟨n - 1 - i.1, by
    have hi : i.1 < n := i.2
    omega⟩
  invFun i := ⟨n - 1 - i.1, by
    have hi : i.1 < n := i.2
    omega⟩
  left_inv := by
    intro i
    apply Fin.ext
    simp
    omega
  right_inv := by
    intro i
    apply Fin.ext
    simp
    omega

@[simp]
lemma attemptSixteenPrefixRev_val {n : ℕ} (i : attemptSixteenPrefixIndex n) :
    (attemptSixteenPrefixRev n i).1 = n - 1 - i.1 := by
  rfl

@[simp]
lemma attemptSixteenPrefixRev_symm (n : ℕ) :
    (attemptSixteenPrefixRev n).symm = attemptSixteenPrefixRev n := by
  ext i
  simp [attemptSixteenPrefixRev]

def attemptSixteenPrefixForwardSum (α : ℝ) (n : ℕ)
    (x : attemptSixteenPrefixIndex n → Bool × ℕ) : ℝ :=
  Finset.sum Finset.univ fun i => α * (1 - α) ^ i.1 * attemptSixteenCenteredNoiseValue (x i)

def attemptSixteenPrefixBackwardSum (α : ℝ) (n : ℕ)
    (x : attemptSixteenPrefixIndex n → Bool × ℕ) : ℝ :=
  Finset.sum Finset.univ fun i =>
    α * (1 - α) ^ i.1 * attemptSixteenCenteredNoiseValue (x (attemptSixteenPrefixRev n i))

lemma attemptSixteenPrefixForwardSum_measurable (α : ℝ) (n : ℕ) :
    Measurable (attemptSixteenPrefixForwardSum α n) := by
  unfold attemptSixteenPrefixForwardSum
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_const.mul <|
    attemptSixteenCenteredNoiseValue_measurable.comp (measurable_pi_apply i)

lemma attemptSixteenPrefixBackwardSum_measurable (α : ℝ) (n : ℕ) :
    Measurable (attemptSixteenPrefixBackwardSum α n) := by
  unfold attemptSixteenPrefixBackwardSum
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_const.mul <|
    attemptSixteenCenteredNoiseValue_measurable.comp (measurable_pi_apply _)

lemma attemptSixteenCenteredARIterate_eq_sum (α : ℝ) :
    ∀ n ω, attemptSixteenCenteredARIterate α n ω =
      Finset.sum (Finset.range n)
        (fun i => α * (1 - α) ^ (n - 1 - i) * attemptSixteenCenteredProcessValue i ω) := by
  intro n ω
  induction n with
  | zero =>
      simp [attemptSixteenCenteredARIterate]
  | succ n ih =>
      rw [attemptSixteenCenteredARIterate]
      calc
        (1 - α) * attemptSixteenCenteredARIterate α n ω +
            α * attemptSixteenCenteredProcessValue n ω
            =
            (1 - α) *
                (Finset.sum (Finset.range n)
                  (fun i => α * (1 - α) ^ (n - 1 - i) * attemptSixteenCenteredProcessValue i ω)) +
              α * attemptSixteenCenteredProcessValue n ω := by
              rw [ih]
        _ =
            (Finset.sum (Finset.range n)
              (fun i => α * (1 - α) ^ (n - i) * attemptSixteenCenteredProcessValue i ω)) +
              α * attemptSixteenCenteredProcessValue n ω := by
              rw [Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hi' : i < n := Finset.mem_range.mp hi
              have hexp : n - i = (n - 1 - i) + 1 := by
                omega
              rw [hexp, pow_succ']
              ring
        _ =
            Finset.sum (Finset.range (n + 1))
              (fun i => α * (1 - α) ^ ((n + 1) - 1 - i) * attemptSixteenCenteredProcessValue i ω) := by
              simp [Finset.sum_range_succ]

lemma attemptSixteenCenteredPartialSum_eq_prefixForward (α : ℝ) (n : ℕ)
    (ω : ℕ → Bool × ℕ) :
    attemptSixteenCenteredPartialSum α n ω =
      attemptSixteenPrefixForwardSum α n (attemptSixteenPrefixRestrict n ω) := by
  simpa [attemptSixteenCenteredPartialSum, attemptSixteenPrefixForwardSum,
    attemptSixteenPrefixRestrict, attemptSixteenCenteredSeriesTerm,
    attemptSixteenCenteredProcessValue] using
    (Fin.sum_univ_eq_sum_range
      (fun i : ℕ => α * (1 - α) ^ i * attemptSixteenCenteredNoiseValue (ω i)) n).symm

lemma attemptSixteenCenteredARIterate_eq_prefixBackward (α : ℝ) (n : ℕ)
    (ω : ℕ → Bool × ℕ) :
    attemptSixteenCenteredARIterate α n ω =
      attemptSixteenPrefixBackwardSum α n (attemptSixteenPrefixRestrict n ω) := by
  rw [attemptSixteenCenteredARIterate_eq_sum]
  have hreflect :
      (Finset.sum (Finset.range n)
        (fun j => α * (1 - α) ^ (n - 1 - j) * attemptSixteenCenteredProcessValue j ω))
        =
      Finset.sum (Finset.range n)
        (fun j => α * (1 - α) ^ j * attemptSixteenCenteredNoiseValue (ω (n - 1 - j))) := by
    calc
      (Finset.sum (Finset.range n)
        (fun j => α * (1 - α) ^ (n - 1 - j) * attemptSixteenCenteredProcessValue j ω))
          =
        Finset.sum (Finset.range n)
          (fun j => α * (1 - α) ^ (n - 1 - j) * attemptSixteenCenteredNoiseValue (ω j)) := by
            simp [attemptSixteenCenteredProcessValue]
      _ =
        Finset.sum (Finset.range n)
          (fun j => α * (1 - α) ^ j * attemptSixteenCenteredNoiseValue (ω (n - 1 - j))) := by
            calc
              Finset.sum (Finset.range n)
                (fun j =>
                  α * (1 - α) ^ (n - 1 - j) *
                    attemptSixteenCenteredNoiseValue (ω j)) =
                Finset.sum (Finset.range n)
                  (fun j =>
                    α * (1 - α) ^ (n - 1 - j) *
                      attemptSixteenCenteredNoiseValue (ω (n - 1 - (n - 1 - j)))) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        have hjn : j < n := Finset.mem_range.mp hj
                        congr 1
                        have hpred : j ≤ n - 1 := Nat.le_pred_of_lt hjn
                        have hsuble : n - 1 - j ≤ n - 1 := Nat.sub_le _ _
                        have hindex : n - 1 - (n - 1 - j) = j := by
                          rw [Nat.sub_eq_iff_eq_add hsuble]
                          simpa [add_comm] using (Nat.sub_add_cancel hpred).symm
                        simpa [hindex]
              _ =
                Finset.sum (Finset.range n)
                  (fun j => α * (1 - α) ^ j * attemptSixteenCenteredNoiseValue (ω (n - 1 - j))) := by
                        simpa using
                          (Finset.sum_range_reflect
                            (fun j ↦ α * (1 - α) ^ j *
                              attemptSixteenCenteredNoiseValue (ω (n - 1 - j))) n)
  rw [hreflect]
  simpa [attemptSixteenPrefixBackwardSum, attemptSixteenPrefixRestrict, attemptSixteenPrefixRev_val] using
    (Fin.sum_univ_eq_sum_range
      (fun i : ℕ => α * (1 - α) ^ i * attemptSixteenCenteredNoiseValue (ω (n - 1 - i))) n).symm

lemma attemptSixteenPrefixBackward_eq_forward_comp (α : ℝ) (n : ℕ) :
    attemptSixteenPrefixBackwardSum α n =
      attemptSixteenPrefixForwardSum α n ∘
        MeasurableEquiv.piCongrLeft (fun _ : attemptSixteenPrefixIndex n ↦ Bool × ℕ)
          (attemptSixteenPrefixRev n) := by
  funext x
  unfold attemptSixteenPrefixBackwardSum attemptSixteenPrefixForwardSum
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hpi :
      (MeasurableEquiv.piCongrLeft (fun _ : attemptSixteenPrefixIndex n ↦ Bool × ℕ)
        (attemptSixteenPrefixRev n) x) i =
        x ((attemptSixteenPrefixRev n) i) := by
    have hrevrev : attemptSixteenPrefixRev n (attemptSixteenPrefixRev n i) = i := by
      exact (attemptSixteenPrefixRev n).left_inv i
    simpa [hrevrev] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := attemptSixteenPrefixRev n)
        (β := fun _ : attemptSixteenPrefixIndex n ↦ Bool × ℕ)
        (x := x) (i := attemptSixteenPrefixRev n i))
  simpa [hpi]

theorem attemptSixteenPrefixSums_identDistrib (α : ℝ) (n : ℕ) :
    ProbabilityTheory.IdentDistrib
      (attemptSixteenPrefixBackwardSum α n) (attemptSixteenPrefixForwardSum α n)
      (attemptSixteenPrefixMeasure n) (attemptSixteenPrefixMeasure n) := by
  let κ : Measure ℝ := (attemptSixteenPrefixMeasure n).map (attemptSixteenPrefixForwardSum α n)
  have hforward :
      ProbabilityTheory.HasLaw (attemptSixteenPrefixForwardSum α n) κ
        (attemptSixteenPrefixMeasure n) := by
    exact ⟨(attemptSixteenPrefixForwardSum_measurable α n).aemeasurable, rfl⟩
  have hrev :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : attemptSixteenPrefixIndex n ↦ Bool × ℕ)
          (attemptSixteenPrefixRev n))
        (attemptSixteenPrefixMeasure n) (attemptSixteenPrefixMeasure n) := by
    simpa [attemptSixteenPrefixMeasure] using
      (measurePreserving_piCongrLeft
        (α := fun _ : attemptSixteenPrefixIndex n ↦ Bool × ℕ)
        (μ := fun _ : attemptSixteenPrefixIndex n ↦ attemptSixteenCenteredNoiseMeasure)
        (f := attemptSixteenPrefixRev n))
  have hbackward :
      ProbabilityTheory.HasLaw (attemptSixteenPrefixBackwardSum α n) κ
        (attemptSixteenPrefixMeasure n) := by
    simpa [κ, attemptSixteenPrefixBackward_eq_forward_comp α n] using
      (hforward.comp hrev.hasLaw)
  exact hbackward.identDistrib hforward

lemma attemptSixteenPrefixCoords_hasLaw (n : ℕ) :
    ProbabilityTheory.HasLaw (attemptSixteenPrefixRestrict n) (attemptSixteenPrefixMeasure n)
      attemptSixteenCenteredProcessMeasure := by
  refine ⟨(measurable_pi_lambda _
      (fun i : attemptSixteenPrefixIndex n => measurable_pi_apply i.1)).aemeasurable, ?_⟩
  have hall :
      ProbabilityTheory.iIndepFun
        (fun i : ℕ ↦ fun ω : ℕ → Bool × ℕ ↦ ω i)
        attemptSixteenCenteredProcessMeasure := by
    simpa [attemptSixteenCenteredProcessMeasure] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure)
        (X := fun _ x ↦ x) (fun _ ↦ measurable_id))
  have hfin :
      ProbabilityTheory.iIndepFun
        (fun i : attemptSixteenPrefixIndex n ↦ fun ω : ℕ → Bool × ℕ ↦ ω i.1)
        attemptSixteenCenteredProcessMeasure := by
    exact hall.precomp Fin.val_injective
  have hmap :
      attemptSixteenCenteredProcessMeasure.map (attemptSixteenPrefixRestrict n) =
        Measure.pi
          (fun i : attemptSixteenPrefixIndex n ↦
            attemptSixteenCenteredProcessMeasure.map (fun ω : ℕ → Bool × ℕ ↦ ω i.1)) := by
    simpa [attemptSixteenPrefixRestrict] using
      (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (μ := attemptSixteenCenteredProcessMeasure)
        (f := fun i : attemptSixteenPrefixIndex n ↦ fun ω : ℕ → Bool × ℕ ↦ ω i.1)
        (hf := fun i ↦ (measurable_pi_apply i.1).aemeasurable)).1 hfin
  rw [hmap]
  congr
  funext i
  simpa [attemptSixteenCenteredProcessMeasure] using
    (measurePreserving_eval_infinitePi
      (μ := fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure) (i := i.1)).map_eq

theorem attemptSixteenCenteredIterate_identDistrib_partialSum (α : ℝ) (n : ℕ) :
    ProbabilityTheory.IdentDistrib
      (attemptSixteenCenteredARIterate α n) (attemptSixteenCenteredPartialSum α n)
      attemptSixteenCenteredProcessMeasure attemptSixteenCenteredProcessMeasure := by
  let κ : Measure ℝ := (attemptSixteenPrefixMeasure n).map (attemptSixteenPrefixForwardSum α n)
  have hcoords := attemptSixteenPrefixCoords_hasLaw n
  have hforward :
      ProbabilityTheory.HasLaw
        (attemptSixteenPrefixForwardSum α n ∘ attemptSixteenPrefixRestrict n) κ
        attemptSixteenCenteredProcessMeasure := by
    exact
      (show ProbabilityTheory.HasLaw (attemptSixteenPrefixForwardSum α n) κ
          (attemptSixteenPrefixMeasure n) from
            ⟨(attemptSixteenPrefixForwardSum_measurable α n).aemeasurable, rfl⟩).comp hcoords
  have hbackwardBase :
      ProbabilityTheory.HasLaw (attemptSixteenPrefixBackwardSum α n) κ
        (attemptSixteenPrefixMeasure n) := by
    exact (attemptSixteenPrefixSums_identDistrib α n).symm.hasLaw
      (show ProbabilityTheory.HasLaw (attemptSixteenPrefixForwardSum α n) κ
        (attemptSixteenPrefixMeasure n) from
          ⟨(attemptSixteenPrefixForwardSum_measurable α n).aemeasurable, rfl⟩)
  have hbackward :
      ProbabilityTheory.HasLaw
        (attemptSixteenPrefixBackwardSum α n ∘ attemptSixteenPrefixRestrict n) κ
        attemptSixteenCenteredProcessMeasure := by
    exact hbackwardBase.comp hcoords
  have hiterate :
      ProbabilityTheory.HasLaw (attemptSixteenCenteredARIterate α n) κ
        attemptSixteenCenteredProcessMeasure := by
    have hEq :
        attemptSixteenPrefixBackwardSum α n ∘ attemptSixteenPrefixRestrict n =
          attemptSixteenCenteredARIterate α n := by
      funext ω
      symm
      exact attemptSixteenCenteredARIterate_eq_prefixBackward α n ω
    simpa [hEq] using hbackward
  have hpartial' :
      ProbabilityTheory.HasLaw (attemptSixteenCenteredPartialSum α n) κ
        attemptSixteenCenteredProcessMeasure := by
    have hEq :
        attemptSixteenPrefixForwardSum α n ∘ attemptSixteenPrefixRestrict n =
          attemptSixteenCenteredPartialSum α n := by
      funext ω
      symm
      exact attemptSixteenCenteredPartialSum_eq_prefixForward α n ω
    simpa [hEq] using hforward
  exact hiterate.identDistrib hpartial'

theorem attemptSixteenCenteredProcessValue_abs_integrable (n : ℕ) :
    Integrable (fun ω ↦ |attemptSixteenCenteredProcessValue n ω|)
      attemptSixteenCenteredProcessMeasure := by
  have hmp :
      MeasurePreserving (Function.eval n) attemptSixteenCenteredProcessMeasure
        attemptSixteenCenteredNoiseMeasure := by
    simpa [attemptSixteenCenteredProcessMeasure] using
      (measurePreserving_eval_infinitePi
        (μ := fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure) (i := n))
  simpa [attemptSixteenCenteredProcessValue, Function.comp] using
    (hmp.integrable_comp_of_integrable
      (g := fun z : Bool × ℕ ↦ |attemptSixteenCenteredNoiseValue z|)
      attemptSixteenCenteredNoise_firstMoment_integrable)

lemma attemptSixteenCenteredProcessValue_abs_integral_eq (n : ℕ) :
    ∫ ω, |attemptSixteenCenteredProcessValue n ω| ∂ attemptSixteenCenteredProcessMeasure =
      ∫ z, |attemptSixteenCenteredNoiseValue z| ∂ attemptSixteenCenteredNoiseMeasure := by
  have hmp :
      MeasurePreserving (Function.eval n) attemptSixteenCenteredProcessMeasure
        attemptSixteenCenteredNoiseMeasure := by
    simpa [attemptSixteenCenteredProcessMeasure] using
      (measurePreserving_eval_infinitePi
        (μ := fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure) (i := n))
  have hEvalLaw :
      ProbabilityTheory.HasLaw (Function.eval n) attemptSixteenCenteredNoiseMeasure
        attemptSixteenCenteredProcessMeasure := hmp.hasLaw
  simpa [attemptSixteenCenteredProcessValue, Function.comp] using
    hEvalLaw.integral_comp attemptSixteenCenteredNoise_firstMoment_integrable.aestronglyMeasurable

theorem attemptSixteenCenteredProcessValue_zero_sixthMoment_not_integrable :
    ¬ Integrable (fun ω ↦ |attemptSixteenCenteredProcessValue 0 ω| ^ 6)
      attemptSixteenCenteredProcessMeasure := by
  intro hInt
  have hmp :
      MeasurePreserving (Function.eval 0) attemptSixteenCenteredProcessMeasure
        attemptSixteenCenteredNoiseMeasure := by
    simpa [attemptSixteenCenteredProcessMeasure] using
      (measurePreserving_eval_infinitePi
        (μ := fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure) (i := 0))
  have hbase :
      Integrable (fun z ↦ |attemptSixteenCenteredNoiseValue z| ^ 6)
        attemptSixteenCenteredNoiseMeasure := by
    simpa [attemptSixteenCenteredProcessValue, Function.comp] using
      (hmp.integrable_comp
        (g := fun z : Bool × ℕ ↦ |attemptSixteenCenteredNoiseValue z| ^ 6)
        (by fun_prop)).mp hInt
  exact attemptSixteenCenteredNoise_sixthMoment_not_integrable hbase

lemma attemptSixteenCenteredOffsetTerm_norm_integrable (α : ℝ) (m n : ℕ)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    Integrable
      (fun ω ↦ ‖α * (1 - α) ^ n * attemptSixteenCenteredProcessValue (n + m) ω‖)
      attemptSixteenCenteredProcessMeasure := by
  have hsub : 0 ≤ 1 - α := sub_nonneg.mpr hα.2
  refine
    ((attemptSixteenCenteredProcessValue_abs_integrable (n + m)).const_mul
      (α * (1 - α) ^ n)).congr ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_mul, abs_of_nonneg hα.1,
    abs_of_nonneg (pow_nonneg hsub _)]
  ring

lemma attemptSixteenCenteredOffsetTerm_integral_norm (α : ℝ) (m n : ℕ)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, ‖α * (1 - α) ^ n * attemptSixteenCenteredProcessValue (n + m) ω‖
      ∂ attemptSixteenCenteredProcessMeasure =
      α * (1 - α) ^ n *
        ∫ z, |attemptSixteenCenteredNoiseValue z| ∂ attemptSixteenCenteredNoiseMeasure := by
  have hsub : 0 ≤ 1 - α := sub_nonneg.mpr hα.2
  have hEq :
      (fun ω ↦ ‖α * (1 - α) ^ n * attemptSixteenCenteredProcessValue (n + m) ω‖) =
        fun ω ↦ α * (1 - α) ^ n * |attemptSixteenCenteredProcessValue (n + m) ω| := by
    funext ω
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_mul, abs_of_nonneg hα.1,
      abs_of_nonneg (pow_nonneg hsub _)]
    ring
  rw [hEq, integral_const_mul]
  rw [attemptSixteenCenteredProcessValue_abs_integral_eq (n + m)]

lemma attemptSixteenCenteredOffsetSeries_summable_integral_norm {α : ℝ} (m : ℕ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    Summable
      (fun n ↦
        ∫ ω, ‖α * (1 - α) ^ n * attemptSixteenCenteredProcessValue (n + m) ω‖
          ∂ attemptSixteenCenteredProcessMeasure) := by
  let C : ℝ := ∫ z, |attemptSixteenCenteredNoiseValue z| ∂ attemptSixteenCenteredNoiseMeasure
  have hgeom : Summable (fun n : ℕ ↦ α * (1 - α) ^ n) := by
    exact (summable_geometric_of_lt_one (sub_nonneg.mpr hα.2.le) (sub_lt_self 1 hα.1)).mul_left α
  refine (hgeom.mul_right C).congr ?_
  intro n
  rw [attemptSixteenCenteredOffsetTerm_integral_norm α m n ⟨hα.1.le, hα.2.le⟩]

lemma attemptSixteenCenteredOffsetSeries_ae_summable {α : ℝ} (m : ℕ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂ attemptSixteenCenteredProcessMeasure,
      Summable (fun n ↦ α * (1 - α) ^ n * attemptSixteenCenteredProcessValue (n + m) ω) := by
  let F : ℕ → (ℕ → Bool × ℕ) → ℝ :=
    fun n ω ↦ α * (1 - α) ^ n * attemptSixteenCenteredProcessValue (n + m) ω
  have hmeas : ∀ n, AEStronglyMeasurable (F n) attemptSixteenCenteredProcessMeasure := by
    intro n
    simpa [F, mul_assoc] using
      (((attemptSixteenCenteredProcessValue_measurable (n + m)).aestronglyMeasurable).const_mul
        ((1 - α) ^ n)).const_mul α
  have htop :
      ∫⁻ ω, ∑' n, ‖F n ω‖ₑ ∂ attemptSixteenCenteredProcessMeasure < ⊤ := by
    have hsum :
        Summable
          (fun n ↦
            ∫ ω, ‖F n ω‖ ∂ attemptSixteenCenteredProcessMeasure) :=
      attemptSixteenCenteredOffsetSeries_summable_integral_norm m hα
    have hsumAbs :
        Summable
          (fun n ↦
            ∫ ω, |F n ω| ∂ attemptSixteenCenteredProcessMeasure) := by
      simpa [Real.norm_eq_abs] using hsum
    have hnonneg :
        ∀ n, 0 ≤ ∫ ω, |F n ω| ∂ attemptSixteenCenteredProcessMeasure := by
      intro n
      exact integral_nonneg fun _ ↦ abs_nonneg _
    let G : ℕ → NNReal := fun n =>
      ⟨∫ ω, |F n ω| ∂ attemptSixteenCenteredProcessMeasure, hnonneg n⟩
    have hEq :
        (fun n ↦ ∫⁻ ω, ‖F n ω‖ₑ ∂ attemptSixteenCenteredProcessMeasure) =
          fun n ↦ (G n : ENNReal) := by
      funext n
      change
        ∫⁻ ω, ((‖F n ω‖₊ : NNReal) : ENNReal) ∂ attemptSixteenCenteredProcessMeasure = (G n : ENNReal)
      rw [lintegral_coe_eq_integral]
      · apply congrArg (fun x : NNReal => (x : ENNReal))
        apply Subtype.ext
        simp [G, Real.toNNReal_of_nonneg (hnonneg n)]
      · simpa [F, Real.norm_eq_abs] using
          attemptSixteenCenteredOffsetTerm_norm_integrable α m n ⟨hα.1.le, hα.2.le⟩
    have hsumNN : Summable G := by
      exact (NNReal.summable_coe (f := G)).1 (by simpa [G] using hsumAbs)
    have htsum :
        ∑' n, ∫⁻ ω, ‖F n ω‖ₑ ∂ attemptSixteenCenteredProcessMeasure ≠ ⊤ := by
      rw [hEq]
      exact ENNReal.tsum_coe_ne_top_iff_summable.2 hsumNN
    rwa [lintegral_tsum (fun n ↦ (hmeas n).enorm), lt_top_iff_ne_top]
  have hnorm :
      ∀ᵐ ω ∂ attemptSixteenCenteredProcessMeasure,
        Summable (fun n ↦ (‖F n ω‖₊ : ℝ)) := by
    refine (ae_lt_top' (AEMeasurable.ennreal_tsum fun n ↦ (hmeas n).enorm) htop.ne).mono ?_
    intro ω hω
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hω.ne
  filter_upwards [hnorm] with ω hω
  exact hω.of_norm

lemma attemptSixteenCenteredSeries_ae_summable {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂ attemptSixteenCenteredProcessMeasure,
      Summable (fun n ↦ attemptSixteenCenteredSeriesTerm α n ω) := by
  simpa [attemptSixteenCenteredSeriesTerm] using
    attemptSixteenCenteredOffsetSeries_ae_summable (m := 0) hα

lemma attemptSixteenCenteredShiftSeries_ae_summable {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂ attemptSixteenCenteredProcessMeasure,
      Summable (fun n ↦ attemptSixteenCenteredSeriesTerm α n (attemptSixteenCenteredShift ω)) := by
  simpa [attemptSixteenCenteredSeriesTerm, attemptSixteenCenteredShift,
    attemptSixteenCenteredProcessValue, Nat.add_assoc] using
    attemptSixteenCenteredOffsetSeries_ae_summable (m := 1) hα

lemma attemptSixteenCenteredPartialSum_tendsto_ae {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂ attemptSixteenCenteredProcessMeasure,
      Tendsto (fun n ↦ attemptSixteenCenteredPartialSum α n ω) atTop
        (𝓝 (attemptSixteenCenteredSeries α ω)) := by
  filter_upwards [attemptSixteenCenteredSeries_ae_summable hα] with ω hω
  simpa [attemptSixteenCenteredPartialSum, attemptSixteenCenteredSeries] using
    hω.hasSum.tendsto_sum_nat

lemma attemptSixteenCenteredSeries_aestronglyMeasurable {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    AEStronglyMeasurable (attemptSixteenCenteredSeries α) attemptSixteenCenteredProcessMeasure := by
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun n ↦ (attemptSixteenCenteredPartialSum_measurable α n).aestronglyMeasurable)
    (attemptSixteenCenteredPartialSum_tendsto_ae hα)

theorem attemptSixteenCenteredPartialSum_tendstoInDistribution {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    MeasureTheory.TendstoInDistribution
      (fun n ↦ attemptSixteenCenteredPartialSum α n) atTop
      (attemptSixteenCenteredSeries α) attemptSixteenCenteredProcessMeasure := by
  have hMeasure :
      MeasureTheory.TendstoInMeasure attemptSixteenCenteredProcessMeasure
        (fun n ↦ attemptSixteenCenteredPartialSum α n) atTop
        (attemptSixteenCenteredSeries α) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (attemptSixteenCenteredPartialSum_measurable α n).aestronglyMeasurable)
      (attemptSixteenCenteredPartialSum_tendsto_ae hα)
  exact hMeasure.tendstoInDistribution
    (fun n ↦ (attemptSixteenCenteredPartialSum_measurable α n).aemeasurable)

theorem attemptSixteenCenteredARIterate_tendstoInDistribution {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    MeasureTheory.TendstoInDistribution
      (fun n ↦ attemptSixteenCenteredARIterate α n) atTop
      (attemptSixteenCenteredSeries α) attemptSixteenCenteredProcessMeasure := by
  have hpartial := attemptSixteenCenteredPartialSum_tendstoInDistribution hα
  have hEq :
      (fun n ↦
        (⟨attemptSixteenCenteredProcessMeasure.map (attemptSixteenCenteredARIterate α n),
          Measure.isProbabilityMeasure_map
            ((attemptSixteenCenteredIterate_identDistrib_partialSum α n).aemeasurable_fst)⟩ :
          MeasureTheory.ProbabilityMeasure ℝ))
        =
      fun n ↦
        (⟨attemptSixteenCenteredProcessMeasure.map (attemptSixteenCenteredPartialSum α n),
          Measure.isProbabilityMeasure_map
            ((attemptSixteenCenteredIterate_identDistrib_partialSum α n).aemeasurable_snd)⟩ :
          MeasureTheory.ProbabilityMeasure ℝ) := by
    funext n
    apply Subtype.ext
    exact (attemptSixteenCenteredIterate_identDistrib_partialSum α n).map_eq
  refine ⟨fun n ↦ (attemptSixteenCenteredIterate_identDistrib_partialSum α n).aemeasurable_fst,
    hpartial.aemeasurable_limit, ?_⟩
  simpa [hEq] using hpartial.tendsto

lemma attemptSixteenCenteredShift_identDistrib :
    ProbabilityTheory.IdentDistrib
      attemptSixteenCenteredShift id
      attemptSixteenCenteredProcessMeasure attemptSixteenCenteredProcessMeasure := by
  have hcoord :
      ProbabilityTheory.iIndepFun
        (fun i : ℕ ↦ fun ω : ℕ → Bool × ℕ ↦ ω i)
        attemptSixteenCenteredProcessMeasure := by
    simpa [attemptSixteenCenteredProcessMeasure] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure)
        (X := fun _ x ↦ x) (fun _ ↦ measurable_id))
  have hshift :
      ProbabilityTheory.iIndepFun
        (fun i : ℕ ↦ fun ω : ℕ → Bool × ℕ ↦ (attemptSixteenCenteredShift ω) i)
        attemptSixteenCenteredProcessMeasure := by
    simpa [attemptSixteenCenteredShift] using hcoord.precomp Nat.succ_injective
  refine ⟨attemptSixteenCenteredShift_measurable.aemeasurable, aemeasurable_id, ?_⟩
  calc
    attemptSixteenCenteredProcessMeasure.map attemptSixteenCenteredShift
        =
      Measure.infinitePi
        (fun i : ℕ ↦
          attemptSixteenCenteredProcessMeasure.map
            (fun ω : ℕ → Bool × ℕ ↦ (attemptSixteenCenteredShift ω) i)) := by
          simpa [attemptSixteenCenteredShift] using
            (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
              (P := attemptSixteenCenteredProcessMeasure)
              (X := fun i : ℕ ↦ fun ω : ℕ → Bool × ℕ ↦ (attemptSixteenCenteredShift ω) i)
              (fun i ↦ measurable_pi_apply (i + 1))).1 hshift
    _ = Measure.infinitePi (fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure) := by
          congr
          funext i
          simpa [attemptSixteenCenteredProcessMeasure, attemptSixteenCenteredShift] using
            (measurePreserving_eval_infinitePi
              (μ := fun _ : ℕ ↦ attemptSixteenCenteredNoiseMeasure) (i := i + 1)).map_eq
    _ = attemptSixteenCenteredProcessMeasure.map id := by
          simp [attemptSixteenCenteredProcessMeasure]

lemma attemptSixteenCenteredSeries_shift_identDistrib {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ProbabilityTheory.IdentDistrib
      (attemptSixteenCenteredSeries α ∘ attemptSixteenCenteredShift)
      (attemptSixteenCenteredSeries α)
      attemptSixteenCenteredProcessMeasure attemptSixteenCenteredProcessMeasure := by
  have hseries :
      AEMeasurable (attemptSixteenCenteredSeries α) attemptSixteenCenteredProcessMeasure :=
    (attemptSixteenCenteredSeries_aestronglyMeasurable hα).aemeasurable
  refine attemptSixteenCenteredShift_identDistrib.comp_of_aemeasurable ?_
  simpa [attemptSixteenCenteredShift_identDistrib.map_eq] using hseries

lemma attemptSixteenCenteredSeries_fixedPoint_ae {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂ attemptSixteenCenteredProcessMeasure,
      attemptSixteenCenteredSeries α ω =
        α * attemptSixteenCenteredProcessValue 0 ω +
          (1 - α) * attemptSixteenCenteredSeries α (attemptSixteenCenteredShift ω) := by
  filter_upwards [attemptSixteenCenteredSeries_ae_summable hα,
    attemptSixteenCenteredShiftSeries_ae_summable hα] with ω hω hshift
  have htail :
      ∑' n, attemptSixteenCenteredSeriesTerm α (n + 1) ω =
        (1 - α) * attemptSixteenCenteredSeries α (attemptSixteenCenteredShift ω) := by
    calc
      ∑' n, attemptSixteenCenteredSeriesTerm α (n + 1) ω
          = ∑' n, (1 - α) * attemptSixteenCenteredSeriesTerm α n
              (attemptSixteenCenteredShift ω) := by
              apply tsum_congr
              intro n
              unfold attemptSixteenCenteredSeriesTerm attemptSixteenCenteredShift
                attemptSixteenCenteredProcessValue
              rw [pow_succ']
              ring
      _ = (1 - α) * ∑' n, attemptSixteenCenteredSeriesTerm α n
            (attemptSixteenCenteredShift ω) := by
              simpa [attemptSixteenCenteredSeries] using hshift.tsum_mul_left (1 - α)
  calc
    attemptSixteenCenteredSeries α ω
        =
      Finset.sum (Finset.range 1) (fun i => attemptSixteenCenteredSeriesTerm α i ω) +
        ∑' n, attemptSixteenCenteredSeriesTerm α (n + 1) ω := by
          simpa [attemptSixteenCenteredSeries] using (hω.sum_add_tsum_nat_add 1).symm
    _ =
      α * attemptSixteenCenteredProcessValue 0 ω +
        (1 - α) * attemptSixteenCenteredSeries α (attemptSixteenCenteredShift ω) := by
          rw [htail]
          simp [attemptSixteenCenteredSeriesTerm]

theorem attemptSixteenCenteredSeries_sixthMoment_not_integrable {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ Integrable (fun ω ↦ |attemptSixteenCenteredSeries α ω| ^ 6)
      attemptSixteenCenteredProcessMeasure := by
  intro hInt
  let p : ENNReal := 6
  have hseriesMemLp :
      MemLp (attemptSixteenCenteredSeries α) p
        attemptSixteenCenteredProcessMeasure := by
    have hnormInt :
        Integrable (fun ω ↦ ‖attemptSixteenCenteredSeries α ω‖ ^ (6 : ℝ))
          attemptSixteenCenteredProcessMeasure := by
      simpa [Real.norm_eq_abs] using hInt
    exact
      (integrable_norm_rpow_iff
        (μ := attemptSixteenCenteredProcessMeasure)
        (f := attemptSixteenCenteredSeries α)
        (p := p)
        (attemptSixteenCenteredSeries_aestronglyMeasurable hα)
        (by simp [p]) (by simp [p])).1 hnormInt
  have hshiftMemLp :
      MemLp (attemptSixteenCenteredSeries α ∘ attemptSixteenCenteredShift) p
        attemptSixteenCenteredProcessMeasure := by
    exact (attemptSixteenCenteredSeries_shift_identDistrib hα).symm.memLp_snd hseriesMemLp
  have hdiffInt :
      Integrable
        (fun ω ↦
          |attemptSixteenCenteredSeries α ω -
            (1 - α) * attemptSixteenCenteredSeries α (attemptSixteenCenteredShift ω)| ^ 6)
        attemptSixteenCenteredProcessMeasure := by
    simpa [Real.norm_eq_abs] using
      (hseriesMemLp.sub (hshiftMemLp.const_mul (1 - α))).integrable_norm_pow (by norm_num)
  have hscaled :
      Integrable (fun ω ↦ |α * attemptSixteenCenteredProcessValue 0 ω| ^ 6)
        attemptSixteenCenteredProcessMeasure := by
    refine hdiffInt.congr ?_
    filter_upwards [attemptSixteenCenteredSeries_fixedPoint_ae hα] with ω hω
    have hsub :
        attemptSixteenCenteredSeries α ω -
            (1 - α) * attemptSixteenCenteredSeries α (attemptSixteenCenteredShift ω) =
          α * attemptSixteenCenteredProcessValue 0 ω := by
      linarith
    simpa [hsub]
  have hunit : IsUnit (|α| ^ 6) := by
    refine isUnit_iff_ne_zero.mpr ?_
    exact pow_ne_zero 6 (abs_ne_zero.mpr <| by linarith [hα.1])
  have hproc :
      Integrable (fun ω ↦ |attemptSixteenCenteredProcessValue 0 ω| ^ 6)
        attemptSixteenCenteredProcessMeasure := by
    have hEq :
        (fun ω ↦ |α * attemptSixteenCenteredProcessValue 0 ω| ^ 6) =
          fun ω ↦ (|α| ^ 6) * |attemptSixteenCenteredProcessValue 0 ω| ^ 6 := by
      funext ω
      rw [abs_mul, mul_pow]
    rw [hEq] at hscaled
    exact (integrable_const_mul_iff hunit _).1 hscaled
  exact attemptSixteenCenteredProcessValue_zero_sixthMoment_not_integrable hproc

/--
An `h = 2` specialization of the printed Assumption A5. We package exactly the regularity and
minimum data needed for the literal Conjecture 5.1 counterexample.
-/
def attemptSixteenPrintedA5h2 (f : ℝ → ℝ) (xStar : ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧
    ContDiff ℝ 3 f ∧
    IsLocalMin f xStar ∧
    deriv f xStar = 0 ∧
    0 < (deriv^[2] f) xStar ∧
    ∃ M : ℝ, ∀ x, |(deriv^[3] f) x| ≤ M

/--
The finite-third-moment part of the printed Assumption A6, specialized to a one-point probability
space.
-/
def attemptSixteenPrintedA6Moment (ξ : ℕ → Unit → ℝ) : Prop :=
  ∀ n, Integrable (fun ω ↦ ξ n ω ^ 3) (Measure.dirac ())

/--
The convex objective
`f(x) = x arctan x - (1 / 2) log (1 + x^2)`,
whose derivative is the bounded monotone function `arctan`.
-/
def attemptSixteenLiteralObjective (x : ℝ) : ℝ :=
  x * Real.arctan x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2)

/--
The omitted centering assumption in the printed conjecture allows a deterministic nonzero noise.
-/
def attemptSixteenLiteralNoise (_ : ℕ) (_ : Unit) : ℝ :=
  2

/--
The one-point sample space used to turn the deterministic recursion into a sequence of random
variables.
-/
def attemptSixteenLiteralMeasure : Measure Unit :=
  Measure.dirac ()

/--
The SGD recursion from Conjecture 5.1 with the deterministic noise `ξ_k ≡ 2`, started at `0`.
-/
def attemptSixteenLiteralIterate (α : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      attemptSixteenLiteralIterate α n +
        α * (attemptSixteenLiteralNoise n () -
          deriv attemptSixteenLiteralObjective (attemptSixteenLiteralIterate α n))

/--
The same iterates viewed as random variables on the one-point space.
-/
def attemptSixteenLiteralRandomVariable (α : ℝ) (n : ℕ) : Unit → ℝ :=
  fun _ ↦ attemptSixteenLiteralIterate α n

@[simp]
lemma attemptSixteenLiteralObjective_zero :
    attemptSixteenLiteralObjective 0 = 0 := by
  simp [attemptSixteenLiteralObjective]

lemma attemptSixteenLiteralObjective_deriv :
    deriv attemptSixteenLiteralObjective = Real.arctan := by
  funext x
  have hId : DifferentiableAt ℝ (fun y : ℝ ↦ y) x := by
    exact differentiableAt_id
  have hArctan : DifferentiableAt ℝ Real.arctan x := by
    simpa using Real.differentiableAt_arctan x
  have hPoly : DifferentiableAt ℝ (fun y : ℝ ↦ 1 + y ^ 2) x := by
    fun_prop
  have hPolyNe : 1 + x ^ 2 ≠ 0 := by
    positivity
  have hLog : DifferentiableAt ℝ (fun y : ℝ ↦ Real.log (1 + y ^ 2)) x := by
    exact hPoly.log hPolyNe
  change deriv ((fun y ↦ y * Real.arctan y) - fun y ↦ (1 / 2 : ℝ) * Real.log (1 + y ^ 2)) x =
    Real.arctan x
  have hSub :
      deriv ((fun y ↦ y * Real.arctan y) - fun y ↦ (1 / 2 : ℝ) * Real.log (1 + y ^ 2)) x =
        deriv (fun y ↦ y * Real.arctan y) x -
          deriv (fun y ↦ (1 / 2 : ℝ) * Real.log (1 + y ^ 2)) x := by
    simpa using
      (deriv_sub (f := fun y ↦ y * Real.arctan y)
        (g := fun y ↦ (1 / 2 : ℝ) * Real.log (1 + y ^ 2))
        (x := x) (hId.mul hArctan) (hLog.const_mul (1 / 2 : ℝ)))
  rw [hSub]
  have hMulRule :
      deriv (fun y ↦ y * Real.arctan y) x =
        deriv (fun y ↦ y) x * Real.arctan x + x * deriv Real.arctan x := by
    simpa using
      (deriv_mul (c := fun y ↦ y) (d := Real.arctan) (x := x) hId hArctan)
  have hConstRule :
      deriv (fun y ↦ (1 / 2 : ℝ) * Real.log (1 + y ^ 2)) x =
        (1 / 2 : ℝ) * deriv (fun y ↦ Real.log (1 + y ^ 2)) x := by
    exact
      (deriv_const_mul (x := x) (c := (1 / 2 : ℝ))
        (d := fun y ↦ Real.log (1 + y ^ 2)) hLog)
  have hLogComp :
      deriv (fun y ↦ Real.log (1 + y ^ 2)) x = logDeriv (fun y ↦ 1 + y ^ 2) x := by
    simpa [Function.comp] using
      (Real.deriv_log_comp_eq_logDeriv (f := fun y ↦ 1 + y ^ 2) (x := x) hPoly hPolyNe)
  rw [hMulRule, deriv_id'', Real.deriv_arctan]
  rw [hConstRule, hLogComp]
  rw [logDeriv, Pi.div_apply, deriv_const_add, deriv_pow_field]
  field_simp [hPolyNe]
  ring

lemma attemptSixteenLiteralObjective_secondDeriv :
    deriv^[2] attemptSixteenLiteralObjective = fun x ↦ 1 / (1 + x ^ 2) := by
  funext x
  change deriv (deriv attemptSixteenLiteralObjective) x = 1 / (1 + x ^ 2)
  rw [attemptSixteenLiteralObjective_deriv, Real.deriv_arctan]

lemma attemptSixteenLiteralObjective_thirdDeriv :
    deriv^[3] attemptSixteenLiteralObjective =
      fun x ↦ -(2 * x) / (1 + x ^ 2) ^ 2 := by
  funext x
  change deriv (deriv^[2] attemptSixteenLiteralObjective) x =
      -(2 * x) / (1 + x ^ 2) ^ 2
  rw [attemptSixteenLiteralObjective_secondDeriv]
  rw [show (fun y : ℝ ↦ 1 / (1 + y ^ 2)) = fun y ↦ (1 + y ^ 2)⁻¹ by
    funext y
    simp [one_div]]
  have hPoly : DifferentiableAt ℝ (fun y : ℝ ↦ 1 + y ^ 2) x := by
    fun_prop
  have hPolyNe : 1 + x ^ 2 ≠ 0 := by
    positivity
  rw [deriv_fun_inv'' hPoly hPolyNe, deriv_const_add, deriv_pow_field]
  ring

lemma attemptSixteenLiteralObjective_thirdDeriv_bound (x : ℝ) :
    |(deriv^[3] attemptSixteenLiteralObjective) x| ≤ 1 := by
  rw [attemptSixteenLiteralObjective_thirdDeriv]
  have hnum : |2 * x| ≤ 1 + x ^ 2 := by
    calc
      |2 * x| = 2 * |x| := by
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      _ ≤ |x| ^ 2 + (1 : ℝ) ^ 2 := by
        simpa [pow_two] using (two_mul_le_add_sq |x| (1 : ℝ))
      _ = 1 + x ^ 2 := by
        rw [sq_abs]
        ring
  have hnum' : |2 * x| ≤ (1 + x ^ 2) ^ 2 := by
    have hgrow : 1 + x ^ 2 ≤ (1 + x ^ 2) ^ 2 := by
      nlinarith [sq_nonneg x]
    exact hnum.trans hgrow
  have hden : 0 < (1 + x ^ 2) ^ 2 := by
    positivity
  calc
    |-(2 * x) / (1 + x ^ 2) ^ 2|
        = |2 * x| / (1 + x ^ 2) ^ 2 := by
          rw [abs_div, abs_neg, abs_of_pos hden]
    _ ≤ 1 := by
      exact (div_le_iff₀ hden).2 <| by simpa using hnum'

lemma attemptSixteenLiteralObjective_contDiff :
    ContDiff ℝ 3 attemptSixteenLiteralObjective := by
  have hId : ContDiff ℝ 3 (fun x : ℝ ↦ x) := by
    simpa using (contDiff_id : ContDiff ℝ 3 (fun x : ℝ ↦ x))
  have hArctan : ContDiff ℝ 3 Real.arctan := by
    simpa using (Real.contDiff_arctan : ContDiff ℝ 3 Real.arctan)
  have hMul : ContDiff ℝ 3 (fun x : ℝ ↦ x * Real.arctan x) := by
    exact hId.mul hArctan
  have hPoly : ContDiff ℝ 3 (fun x : ℝ ↦ 1 + x ^ 2) := by
    fun_prop
  have hLog : ContDiff ℝ 3 (fun x : ℝ ↦ Real.log (1 + x ^ 2)) := by
    exact hPoly.log fun x => by positivity
  have hScaled : ContDiff ℝ 3 (fun x : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 + x ^ 2)) := by
    simpa [smul_eq_mul] using
      (ContDiff.const_smul (c := (1 / 2 : ℝ)) hLog)
  change ContDiff ℝ 3 (fun x ↦ x * Real.arctan x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2))
  exact hMul.sub hScaled

lemma attemptSixteenLiteralObjective_convex :
    ConvexOn ℝ Set.univ attemptSixteenLiteralObjective := by
  have hdiff : Differentiable ℝ attemptSixteenLiteralObjective :=
    attemptSixteenLiteralObjective_contDiff.differentiable (by norm_num)
  refine Monotone.convexOn_univ_of_deriv hdiff ?_
  simpa [attemptSixteenLiteralObjective_deriv] using (Real.arctan_mono : Monotone Real.arctan)

lemma attemptSixteenLiteralObjective_isLocalMin :
    IsLocalMin attemptSixteenLiteralObjective 0 := by
  apply isLocalMin_of_deriv_deriv_pos
  · change (deriv^[2] attemptSixteenLiteralObjective) 0 > 0
    rw [attemptSixteenLiteralObjective_secondDeriv]
    norm_num
  · rw [attemptSixteenLiteralObjective_deriv]
    simp
  · exact attemptSixteenLiteralObjective_contDiff.continuous.continuousAt

/--
The arctan-based convex objective satisfies the printed `h = 2` regularity assumptions.
-/
theorem attemptSixteenLiteralObjective_satisfies_A5 :
    attemptSixteenPrintedA5h2 attemptSixteenLiteralObjective 0 := by
  refine ⟨attemptSixteenLiteralObjective_convex, attemptSixteenLiteralObjective_contDiff,
    attemptSixteenLiteralObjective_isLocalMin, ?_, ?_, ⟨1, ?_⟩⟩
  · rw [attemptSixteenLiteralObjective_deriv]
    simp
  · rw [attemptSixteenLiteralObjective_secondDeriv]
    simp
  · intro x
    exact attemptSixteenLiteralObjective_thirdDeriv_bound x

/--
The deterministic noise sequence `ξ_k ≡ 2` has finite third moment on the one-point probability
space.
-/
theorem attemptSixteenLiteralNoise_satisfies_A6Moment :
    attemptSixteenPrintedA6Moment attemptSixteenLiteralNoise := by
  unfold attemptSixteenPrintedA6Moment
  intro n
  simp [attemptSixteenLiteralNoise]

/--
The deterministic increment in the literal counterexample is bounded below by `2 - π / 2`.
-/
def attemptSixteenLiteralDrift : ℝ :=
  2 - Real.pi / 2

lemma attemptSixteenLiteralDrift_pos :
    0 < attemptSixteenLiteralDrift := by
  unfold attemptSixteenLiteralDrift
  have hpi : Real.pi < 4 := Real.pi_lt_four
  linarith

@[simp]
lemma attemptSixteenLiteralIterate_zero (α : ℝ) :
    attemptSixteenLiteralIterate α 0 = 0 := by
  rfl

lemma attemptSixteenLiteralIterate_succ (α : ℝ) (n : ℕ) :
    attemptSixteenLiteralIterate α (n + 1) =
      attemptSixteenLiteralIterate α n +
        α * (2 - Real.arctan (attemptSixteenLiteralIterate α n)) := by
  simp [attemptSixteenLiteralIterate, attemptSixteenLiteralNoise,
    attemptSixteenLiteralObjective_deriv]

lemma attemptSixteenLiteralIterate_lower_bound {α : ℝ} (hα : 0 ≤ α) :
    ∀ n : ℕ, (n : ℝ) * (α * attemptSixteenLiteralDrift) ≤ attemptSixteenLiteralIterate α n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hstep :
          α * attemptSixteenLiteralDrift ≤
            α * (2 - Real.arctan (attemptSixteenLiteralIterate α n)) := by
        have hfactor :
            attemptSixteenLiteralDrift ≤
              2 - Real.arctan (attemptSixteenLiteralIterate α n) := by
          unfold attemptSixteenLiteralDrift
          linarith [Real.arctan_lt_pi_div_two (attemptSixteenLiteralIterate α n)]
        exact mul_le_mul_of_nonneg_left hfactor hα
      calc
        ((n + 1 : ℕ) : ℝ) * (α * attemptSixteenLiteralDrift) =
            (n : ℝ) * (α * attemptSixteenLiteralDrift) + α * attemptSixteenLiteralDrift := by
          norm_num [Nat.cast_add]
          ring
        _ ≤ attemptSixteenLiteralIterate α n + α * attemptSixteenLiteralDrift := by
          exact add_le_add ih le_rfl
        _ ≤ attemptSixteenLiteralIterate α n +
              α * (2 - Real.arctan (attemptSixteenLiteralIterate α n)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hstep (attemptSixteenLiteralIterate α n)
        _ = attemptSixteenLiteralIterate α (n + 1) := by
          rw [attemptSixteenLiteralIterate_succ]

lemma tendsto_atTop_attemptSixteenLiteralIterate {α : ℝ} (hα : 0 < α) :
    Tendsto (attemptSixteenLiteralIterate α) atTop atTop := by
  have hPosDrift : 0 < α * attemptSixteenLiteralDrift := by
    exact mul_pos hα attemptSixteenLiteralDrift_pos
  have hlin : Tendsto (fun n : ℕ ↦ (n : ℝ) * (α * attemptSixteenLiteralDrift)) atTop atTop := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Filter.Tendsto.const_mul_atTop hPosDrift tendsto_natCast_atTop_atTop)
  exact tendsto_atTop_mono (attemptSixteenLiteralIterate_lower_bound hα.le) hlin

lemma attemptSixteenLiteralIterate_not_tendsto_nhds {α z : ℝ} (hα : 0 < α) :
    ¬ Tendsto (attemptSixteenLiteralIterate α) atTop (𝓝 z) := by
  intro h
  have hBelow :
      ∀ᶠ n in atTop, attemptSixteenLiteralIterate α n < z + 1 := by
    exact h.eventually (Iio_mem_nhds (by linarith))
  have hAbove :
      ∀ᶠ n in atTop, z + 1 < attemptSixteenLiteralIterate α n := by
    exact (tendsto_atTop_attemptSixteenLiteralIterate hα).eventually_gt_atTop (z + 1)
  have hFalse : ∀ᶠ n in atTop, False := (hBelow.and hAbove).mono fun n hn ↦ by
    linarith
  exact atTop_neBot.ne ((eventually_false_iff_eq_bot).mp hFalse)

/--
The literal Conjecture 5.1 fails on the one-point probability space: with the bounded-derivative
convex objective above and deterministic noise `ξ_k ≡ 2`, the laws `δ_{X_k^(α)}` escape to
infinity, so no deterministic limit law can exist.

This is a literal-statement disproof that exploits the printed omission of a centering assumption.
It is separate from the centered heavy-tail AR(1) counterexample formalized earlier in this file.
-/
theorem attemptSixteen_conjecture_disconfirmed :
    attemptSixteenPrintedA5h2 attemptSixteenLiteralObjective 0 ∧
      attemptSixteenPrintedA6Moment attemptSixteenLiteralNoise ∧
      ∀ a > 0, ∃ α ∈ Set.Ioo (0 : ℝ) a,
        ¬ ∃ z : ℝ,
          Tendsto (fun n ↦ MeasureTheory.diracProba (attemptSixteenLiteralIterate α n)) atTop
            (𝓝 (MeasureTheory.diracProba z)) := by
  refine ⟨attemptSixteenLiteralObjective_satisfies_A5,
    attemptSixteenLiteralNoise_satisfies_A6Moment, ?_⟩
  intro a ha
  refine ⟨a / 2, by constructor <;> linarith, ?_⟩
  intro hconv
  rcases hconv with ⟨z, hZ⟩
  have hDirac :
      Tendsto MeasureTheory.diracProba (Filter.map (attemptSixteenLiteralIterate (a / 2)) atTop)
        (𝓝 (MeasureTheory.diracProba z)) := by
    simpa [Filter.Tendsto, Function.comp, Filter.map_map] using hZ
  have hIter :
      Tendsto (attemptSixteenLiteralIterate (a / 2)) atTop (𝓝 z) := by
    have :=
      (MeasureTheory.tendsto_diracProba_iff_tendsto
        (L := Filter.map (attemptSixteenLiteralIterate (a / 2)) atTop) (x := z)).mp hDirac
    simpa [Filter.Tendsto] using this
  exact attemptSixteenLiteralIterate_not_tendsto_nhds (by linarith) hIter

end

end GeneralSGDMomentDisproof
