import Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open scoped BigOperators Topology unitInterval
open Filter MeasureTheory

noncomputable section

namespace QuasimodularSturm

namespace AttemptTwo

abbrev SourceSpace := unitInterval

def sampleCount (n : ℕ) : ℕ :=
  2 * (n + 1)

def sampleCountReal (n : ℕ) : ℝ :=
  sampleCount n

def rootRate (n : ℕ) : ℝ :=
  1 / Real.sqrt (sampleCountReal n)

def quarterTailRate (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (sampleCountReal n)) * rootRate n

def EventuallyBoundedByRootRate (err : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ n in atTop, err n ≤ C * rootRate n

def EventuallyLowerBoundedByQuarterTailRate (err : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∀ᶠ n in atTop, c * quarterTailRate n ≤ err n

lemma sampleCountReal_pos (n : ℕ) : 0 < sampleCountReal n := by
  simpa [sampleCountReal, sampleCount] using
    (show (0 : ℝ) < 2 * ((n : ℝ) + 1) by positivity)

lemma sampleCountReal_ne_zero (n : ℕ) : sampleCountReal n ≠ 0 :=
  (sampleCountReal_pos n).ne'

lemma one_le_sampleCountReal (n : ℕ) : (1 : ℝ) ≤ sampleCountReal n := by
  have h : (1 : ℕ) ≤ sampleCount n := by
    change (1 : ℕ) ≤ 2 * (n + 1)
    omega
  have h' : (1 : ℝ) ≤ (sampleCount n : ℝ) := by
    exact_mod_cast h
  simpa [sampleCountReal] using h'

lemma rootRate_pos (n : ℕ) : 0 < rootRate n := by
  unfold rootRate
  exact one_div_pos.mpr <| Real.sqrt_pos.2 (sampleCountReal_pos n)

lemma quarterTailRate_pos (n : ℕ) : 0 < quarterTailRate n := by
  unfold quarterTailRate
  exact mul_pos (Real.sqrt_pos.2 <| Real.sqrt_pos.2 (sampleCountReal_pos n)) (rootRate_pos n)

lemma tendsto_sampleCountReal_atTop : Tendsto sampleCountReal atTop atTop := by
  have h :
      Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun n : ℕ ↦ (2 : ℝ) * ((n : ℝ) + 1)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) h
  convert h' using 1
  ext n
  simp [sampleCountReal, sampleCount, mul_assoc]

lemma tendsto_sqrt_sqrt_sampleCountReal_atTop :
    Tendsto (fun n ↦ Real.sqrt (Real.sqrt (sampleCountReal n))) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp <|
    Real.tendsto_sqrt_atTop.comp tendsto_sampleCountReal_atTop

theorem not_eventuallyBoundedByRootRate_of_quarterTailLowerBound
    {err : ℕ → ℝ} (hlower : EventuallyLowerBoundedByQuarterTailRate err) :
    ¬ EventuallyBoundedByRootRate err := by
  intro hupper
  rcases hlower with ⟨c, hc, hlower⟩
  rcases hupper with ⟨C, hC, hupper⟩
  have hbounded : ∀ᶠ n in atTop, c * Real.sqrt (Real.sqrt (sampleCountReal n)) ≤ C := by
    filter_upwards [hlower, hupper] with n hnLower hnUpper
    have hroot : 0 < rootRate n := rootRate_pos n
    have hmul :
        c * (Real.sqrt (Real.sqrt (sampleCountReal n)) * rootRate n) ≤ C * rootRate n := by
      rw [← quarterTailRate]
      exact le_trans hnLower hnUpper
    have hmul' :
        (c * Real.sqrt (Real.sqrt (sampleCountReal n))) * rootRate n ≤ C * rootRate n := by
      simpa [mul_assoc] using hmul
    exact le_of_mul_le_mul_right hmul' hroot
  have htendsto :
      Tendsto (fun n ↦ c * Real.sqrt (Real.sqrt (sampleCountReal n))) atTop atTop := by
    exact Tendsto.const_mul_atTop hc tendsto_sqrt_sqrt_sampleCountReal_atTop
  have hlarge : ∀ᶠ n in atTop, C < c * Real.sqrt (Real.sqrt (sampleCountReal n)) := by
    exact htendsto.eventually_gt_atTop C
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hbounded, hlarge] with n hnBound hnLarge
    linarith
  exact atTop_neBot.ne <| by
    rwa [Filter.eventually_false_iff_eq_bot] at hfalse

/-- The explicit power-tail feature used in the fully formalized rank-1 reduction. -/
def tailFeature (x : SourceSpace) : ℝ :=
  Real.sqrt (Real.sqrt ((1 - (x : ℝ))⁻¹))

lemma tailFeature_nonneg (x : SourceSpace) : 0 ≤ tailFeature x := by
  unfold tailFeature
  positivity

lemma tailFeature_sq (x : SourceSpace) :
    tailFeature x ^ 2 = Real.sqrt ((1 - (x : ℝ))⁻¹) := by
  change (Real.sqrt (Real.sqrt ((1 - (x : ℝ))⁻¹))) ^ 2 = Real.sqrt ((1 - (x : ℝ))⁻¹)
  exact Real.sq_sqrt (Real.sqrt_nonneg _)

lemma tailFeature_monotone_on_Iic {x y : SourceSpace} (hy : (y : ℝ) < 1)
    (hx_le : x ≤ y) :
    tailFeature x ≤ tailFeature y := by
  have hxy : (x : ℝ) ≤ (y : ℝ) := hx_le
  have hy0 : 0 < 1 - (y : ℝ) := by linarith [y.2]
  have hx0 : 0 < 1 - (x : ℝ) := by
    have hx1 : (x : ℝ) < 1 := lt_of_le_of_lt hxy hy
    linarith
  have hsub : 1 - (y : ℝ) ≤ 1 - (x : ℝ) := by linarith
  unfold tailFeature
  apply Real.sqrt_le_sqrt
  apply Real.sqrt_le_sqrt
  exact (inv_le_inv₀ hx0 hy0).2 hsub

def lowThreshold (n : ℕ) : SourceSpace :=
  ⟨1 - 1 / (2 * sampleCountReal n), by
    constructor
    · have htwo : (1 : ℝ) ≤ 2 * sampleCountReal n := by
        nlinarith [one_le_sampleCountReal n]
      have h' : 1 / (2 * sampleCountReal n) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) htwo
      linarith
    · have hden : 0 < 2 * sampleCountReal n := by
        nlinarith [sampleCountReal_pos n]
      have h' : 0 < 1 / (2 * sampleCountReal n) := one_div_pos.mpr hden
      linarith⟩

def highThreshold (n : ℕ) : SourceSpace :=
  ⟨1 - 1 / (4 * sampleCountReal n), by
    constructor
    · have hfour : (1 : ℝ) ≤ 4 * sampleCountReal n := by
        nlinarith [one_le_sampleCountReal n]
      have h' : 1 / (4 * sampleCountReal n) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hfour
      linarith
    · have hden : 0 < 4 * sampleCountReal n := by
        nlinarith [sampleCountReal_pos n]
      have h' : 0 < 1 / (4 * sampleCountReal n) := one_div_pos.mpr hden
      linarith⟩

lemma lowThreshold_coe (n : ℕ) :
    ((lowThreshold n : SourceSpace) : ℝ) = 1 - 1 / (2 * sampleCountReal n) := rfl

lemma highThreshold_coe (n : ℕ) :
    ((highThreshold n : SourceSpace) : ℝ) = 1 - 1 / (4 * sampleCountReal n) := rfl

lemma lowThreshold_lt_one (n : ℕ) : ((lowThreshold n : SourceSpace) : ℝ) < 1 := by
  rw [lowThreshold_coe]
  have h : 0 < 1 / (2 * sampleCountReal n) := by
    have h' : 0 < 2 * sampleCountReal n := by nlinarith [sampleCountReal_pos n]
    exact one_div_pos.mpr h'
  linarith

lemma highThreshold_lt_one (n : ℕ) : ((highThreshold n : SourceSpace) : ℝ) < 1 := by
  rw [highThreshold_coe]
  have h : 0 < 1 / (4 * sampleCountReal n) := by
    have h' : 0 < 4 * sampleCountReal n := by nlinarith [sampleCountReal_pos n]
    exact one_div_pos.mpr h'
  linarith

def gapConstant : ℝ :=
  Real.sqrt 2 - Real.sqrt (Real.sqrt 2)

lemma gapConstant_pos : 0 < gapConstant := by
  unfold gapConstant
  have hsq : (Real.sqrt (Real.sqrt 2)) ^ 2 < (Real.sqrt 2) ^ 2 := by
    rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  have hlt : Real.sqrt (Real.sqrt 2) < Real.sqrt 2 := by
    nlinarith [hsq, Real.sqrt_nonneg (Real.sqrt 2), Real.sqrt_nonneg (2 : ℝ)]
  linarith

lemma tailFeature_lowThreshold (n : ℕ) :
    tailFeature (lowThreshold n) =
      Real.sqrt (Real.sqrt (2 * sampleCountReal n)) := by
  unfold tailFeature
  rw [lowThreshold_coe]
  have hN : sampleCountReal n ≠ 0 := sampleCountReal_ne_zero n
  have htwo : (2 : ℝ) * sampleCountReal n ≠ 0 := by positivity
  congr 2
  field_simp [hN]
  ring

lemma tailFeature_highThreshold (n : ℕ) :
    tailFeature (highThreshold n) =
      Real.sqrt (Real.sqrt (4 * sampleCountReal n)) := by
  unfold tailFeature
  rw [highThreshold_coe]
  have hN : sampleCountReal n ≠ 0 := sampleCountReal_ne_zero n
  have hfour : (4 : ℝ) * sampleCountReal n ≠ 0 := by positivity
  congr 2
  field_simp [hN]
  ring

lemma high_minus_low_eq_gap (n : ℕ) :
    tailFeature (highThreshold n) - tailFeature (lowThreshold n) =
      gapConstant * Real.sqrt (Real.sqrt (sampleCountReal n)) := by
  rw [tailFeature_highThreshold, tailFeature_lowThreshold, gapConstant]
  have hN : 0 ≤ sampleCountReal n := (sampleCountReal_pos n).le
  rw [show 4 * sampleCountReal n = sampleCountReal n * 4 by ring,
    show 2 * sampleCountReal n = sampleCountReal n * 2 by ring]
  rw [Real.sqrt_mul hN, Real.sqrt_mul hN]
  norm_num
  ring

lemma gap_over_root_eq_quarter (n : ℕ) :
    gapConstant * Real.sqrt (Real.sqrt (sampleCountReal n)) * rootRate n =
      gapConstant * quarterTailRate n := by
  unfold quarterTailRate
  ring

abbrev Sample (n : ℕ) := Fin (sampleCount n) → SourceSpace

def lastIndex (n : ℕ) : Fin (sampleCount n) :=
  ⟨sampleCount n - 1, by
    have hpos : 0 < sampleCount n := by
      simp [sampleCount]
    exact Nat.sub_lt hpos (by decide)⟩

lemma le_lastIndex (n : ℕ) (i : Fin (sampleCount n)) : i ≤ lastIndex n := by
  apply Fin.le_iff_val_le_val.2
  change i.1 ≤ sampleCount n - 1
  omega

def sampleMeasure (n : ℕ) : Measure (Sample n) :=
  Measure.pi fun _ => (volume : Measure SourceSpace)

instance sampleMeasure_isProbability (n : ℕ) : IsProbabilityMeasure (sampleMeasure n) := by
  unfold sampleMeasure
  infer_instance

def pairMeasure (n : ℕ) : Measure (Sample n × Sample n) :=
  (sampleMeasure n).prod (sampleMeasure n)

instance pairMeasure_isProbability (n : ℕ) : IsProbabilityMeasure (pairMeasure n) := by
  unfold pairMeasure
  infer_instance

def allBelow (n : ℕ) (a : SourceSpace) : Set (Sample n) :=
  Set.pi Set.univ fun _ => Set.Iic a

def someAbove (n : ℕ) (a : SourceSpace) : Set (Sample n) :=
  { x | ∃ i, a < x i }

def counterexampleEvent (n : ℕ) : Set (Sample n × Sample n) :=
  allBelow n (lowThreshold n) ×ˢ someAbove n (highThreshold n)

lemma measurableSet_allBelow (n : ℕ) (a : SourceSpace) : MeasurableSet (allBelow n a) := by
  classical
  simp [allBelow]

lemma measurableSet_someAbove (n : ℕ) (a : SourceSpace) : MeasurableSet (someAbove n a) := by
  classical
  rw [someAbove]
  classical
  simpa [Set.setOf_exists] using
    MeasurableSet.iUnion (fun i : Fin (sampleCount n) =>
      measurable_pi_apply i (measurableSet_Ioi))

lemma someAbove_eq_compl_allBelow (n : ℕ) (a : SourceSpace) :
    someAbove n a = (allBelow n a)ᶜ := by
  ext x
  constructor
  · rintro ⟨i, hi⟩ hxAll
    exact not_lt_of_ge (by simpa [allBelow] using hxAll i) hi
  · intro hxComp
    by_contra hxNo
    apply hxComp
    have hxAll : ∀ i, x i ≤ a := by
      intro i
      by_contra hlt
      exact hxNo ⟨i, lt_of_not_ge hlt⟩
    simpa [allBelow] using hxAll

lemma sampleMeasure_allBelow (n : ℕ) (a : SourceSpace) :
    sampleMeasure n (allBelow n a) = ENNReal.ofReal ((a : ℝ) ^ sampleCount n) := by
  classical
  calc
    sampleMeasure n (allBelow n a) = (ENNReal.ofReal (a : ℝ)) ^ sampleCount n := by
      simpa [sampleMeasure, allBelow, Finset.prod_const] using
        (Measure.pi_pi (μ := fun _ : Fin (sampleCount n) => (volume : Measure SourceSpace))
          (s := fun _ : Fin (sampleCount n) => Set.Iic a))
    _ = ENNReal.ofReal ((a : ℝ) ^ sampleCount n) := by
      symm
      exact ENNReal.ofReal_pow a.2.1 (sampleCount n)

lemma sampleMeasure_someAbove (n : ℕ) (a : SourceSpace) :
    sampleMeasure n (someAbove n a) = ENNReal.ofReal (1 - (a : ℝ) ^ sampleCount n) := by
  have hmeas : MeasurableSet (allBelow n a) := measurableSet_allBelow n a
  have hfin : sampleMeasure n (allBelow n a) ≠ ⊤ := by
    refine ne_of_lt ?_
    calc
      sampleMeasure n (allBelow n a) ≤ sampleMeasure n Set.univ := by
        exact measure_mono (by intro x hx; simp)
      _ = 1 := by simp [sampleMeasure]
      _ < ⊤ := by simp
  have hprob : sampleMeasure n Set.univ = 1 := by simp [sampleMeasure]
  rw [someAbove_eq_compl_allBelow, measure_compl hmeas hfin, hprob, sampleMeasure_allBelow]
  rw [← ENNReal.ofReal_one]
  simpa using (ENNReal.ofReal_sub (1 : ℝ) (pow_nonneg a.2.1 _)).symm

lemma lowThreshold_prob_ge_half (n : ℕ) :
    (1 / 2 : ℝ) ≤ ((lowThreshold n : SourceSpace) : ℝ) ^ sampleCount n := by
  have hbase : (-1 : ℝ) ≤ ((lowThreshold n : SourceSpace) : ℝ) := by
    have hnonneg : 0 ≤ ((lowThreshold n : SourceSpace) : ℝ) := (lowThreshold n).2.1
    linarith
  have hbern :=
    one_add_mul_sub_le_pow (a := ((lowThreshold n : SourceSpace) : ℝ)) hbase (sampleCount n)
  rw [show ((sampleCount n : ℝ) = sampleCountReal n) by simp [sampleCountReal]] at hbern
  rw [lowThreshold_coe] at hbern
  have hcalc :
      1 + sampleCountReal n * ((1 - 1 / (2 * sampleCountReal n)) - 1) = (1 / 2 : ℝ) := by
    field_simp [sampleCountReal_ne_zero n]
    ring
  have hbern' : (1 / 2 : ℝ) ≤ (1 - 1 / (2 * sampleCountReal n)) ^ sampleCount n := by
    rw [hcalc] at hbern
    exact hbern
  simpa [lowThreshold_coe] using hbern'

lemma highThreshold_prob_compl_ge_fifth (n : ℕ) :
    (1 / 5 : ℝ) ≤ 1 - ((highThreshold n : SourceSpace) : ℝ) ^ sampleCount n := by
  have hdenom_pos : 0 < (4 * sampleCountReal n - 1 : ℝ) := by
    nlinarith [one_le_sampleCountReal n]
  have hdenom : (4 * sampleCountReal n - 1 : ℝ) ≠ 0 := hdenom_pos.ne'
  have hrewrite :
      ((highThreshold n : SourceSpace) : ℝ) =
        (1 + 1 / (4 * sampleCountReal n - 1))⁻¹ := by
    rw [highThreshold_coe]
    field_simp [sampleCountReal_ne_zero n, hdenom]
    ring
  have hbern :
      1 + (sampleCount n : ℝ) * (1 / (4 * sampleCountReal n - 1)) ≤
        (1 + 1 / (4 * sampleCountReal n - 1)) ^ sampleCount n := by
    have hsq : 0 ≤ (1 / (4 * sampleCountReal n - 1)) ^ 2 := by positivity
    have hone : 0 ≤ (1 + 1 / (4 * sampleCountReal n - 1)) ^ 2 := by positivity
    have htwo : 0 ≤ 2 + 1 / (4 * sampleCountReal n - 1) := by
      have hfrac : 0 ≤ 1 / (4 * sampleCountReal n - 1) := by positivity
      linarith
    simpa using one_add_mul_le_pow_of_sq_nonneg hsq hone htwo (sampleCount n)
  have hinv :
      ((1 + 1 / (4 * sampleCountReal n - 1)) ^ sampleCount n)⁻¹ ≤
        (1 + (sampleCount n : ℝ) * (1 / (4 * sampleCountReal n - 1)))⁻¹ := by
    have hleft : 0 < (1 + 1 / (4 * sampleCountReal n - 1)) ^ sampleCount n := by
      positivity
    have hright : 0 < 1 + (sampleCount n : ℝ) * (1 / (4 * sampleCountReal n - 1)) := by
      have hfrac : 0 < 1 / (4 * sampleCountReal n - 1) := one_div_pos.mpr hdenom_pos
      positivity
    exact (inv_le_inv₀ hleft hright).2 hbern
  have hbern' :
      1 + sampleCountReal n * (1 / (4 * sampleCountReal n - 1)) ≤
        (1 + 1 / (4 * sampleCountReal n - 1)) ^ sampleCount n := by
    simpa [sampleCountReal] using hbern
  have hinv' :
      ((1 + 1 / (4 * sampleCountReal n - 1)) ^ sampleCount n)⁻¹ ≤
        (1 + sampleCountReal n * (1 / (4 * sampleCountReal n - 1)))⁻¹ := by
    have hleft : 0 < (1 + 1 / (4 * sampleCountReal n - 1)) ^ sampleCount n := by
      positivity
    have hright : 0 < 1 + sampleCountReal n * (1 / (4 * sampleCountReal n - 1)) := by
      have hfrac : 0 < 1 / (4 * sampleCountReal n - 1) := one_div_pos.mpr hdenom_pos
      have hmul : 0 < sampleCountReal n * (1 / (4 * sampleCountReal n - 1)) := by
        exact mul_pos (sampleCountReal_pos n) hfrac
      linarith
    exact (inv_le_inv₀ hleft hright).2 hbern'
  have hcalc :
      (1 + sampleCountReal n * (1 / (4 * sampleCountReal n - 1)))⁻¹ =
        (4 * sampleCountReal n - 1) / (5 * sampleCountReal n - 1) := by
    have hfive_pos : 0 < (5 * sampleCountReal n - 1 : ℝ) := by
      nlinarith [one_le_sampleCountReal n]
    have hsum :
        1 + sampleCountReal n * (1 / (4 * sampleCountReal n - 1)) =
          (5 * sampleCountReal n - 1) / (4 * sampleCountReal n - 1) := by
      have hone :
          (1 : ℝ) = (4 * sampleCountReal n - 1) * (4 * sampleCountReal n - 1)⁻¹ := by
        symm
        exact mul_inv_cancel₀ hdenom
      have hstep :
          1 + sampleCountReal n * (4 * sampleCountReal n - 1)⁻¹ =
            (4 * sampleCountReal n - 1) * (4 * sampleCountReal n - 1)⁻¹ +
              sampleCountReal n * (4 * sampleCountReal n - 1)⁻¹ :=
        congrArg (fun t : ℝ => t + sampleCountReal n * (4 * sampleCountReal n - 1)⁻¹) hone
      calc
        1 + sampleCountReal n * (1 / (4 * sampleCountReal n - 1))
            = 1 + sampleCountReal n * (4 * sampleCountReal n - 1)⁻¹ := by
                rw [one_div]
        _ = (4 * sampleCountReal n - 1) * (4 * sampleCountReal n - 1)⁻¹ +
              sampleCountReal n * (4 * sampleCountReal n - 1)⁻¹ := hstep
        _ = (5 * sampleCountReal n - 1) * (4 * sampleCountReal n - 1)⁻¹ := by ring
        _ = (5 * sampleCountReal n - 1) / (4 * sampleCountReal n - 1) := by
              rw [div_eq_mul_inv]
    calc
      (1 + sampleCountReal n * (1 / (4 * sampleCountReal n - 1)))⁻¹
          = ((5 * sampleCountReal n - 1) / (4 * sampleCountReal n - 1))⁻¹ := by rw [hsum]
      _ = (4 * sampleCountReal n - 1) / (5 * sampleCountReal n - 1) := by
        apply (eq_div_iff hfive_pos.ne').2
        field_simp [hdenom, hfive_pos.ne']
  have haux :
      ((highThreshold n : SourceSpace) : ℝ) ^ sampleCount n ≤
        (4 * sampleCountReal n - 1) / (5 * sampleCountReal n - 1) := by
    rw [hrewrite, inv_pow]
    exact hinv'.trans_eq hcalc
  have hcomp :
      (1 / 5 : ℝ) ≤ 1 - (4 * sampleCountReal n - 1) / (5 * sampleCountReal n - 1) := by
    have hfive : 0 < (5 * sampleCountReal n - 1 : ℝ) := by
      nlinarith [one_le_sampleCountReal n]
    field_simp [hfive.ne']
    ring_nf
    nlinarith
  linarith

lemma event_probability_ge_tenth (n : ℕ) :
    (1 / 10 : ℝ) ≤ (pairMeasure n (counterexampleEvent n)).toReal := by
  have hA :
      (sampleMeasure n (allBelow n (lowThreshold n))).toReal =
        ((lowThreshold n : SourceSpace) : ℝ) ^ sampleCount n := by
    rw [sampleMeasure_allBelow]
    exact ENNReal.toReal_ofReal (pow_nonneg (lowThreshold n).2.1 _)
  have hB :
      (sampleMeasure n (someAbove n (highThreshold n))).toReal =
        1 - ((highThreshold n : SourceSpace) : ℝ) ^ sampleCount n := by
    rw [sampleMeasure_someAbove]
    have hnonneg : 0 ≤ 1 - ((highThreshold n : SourceSpace) : ℝ) ^ sampleCount n := by
      have hpow : ((highThreshold n : SourceSpace) : ℝ) ^ sampleCount n ≤ 1 := by
        exact pow_le_one₀ (highThreshold n).2.1 (highThreshold n).2.2
      linarith
    exact ENNReal.toReal_ofReal hnonneg
  rw [counterexampleEvent, pairMeasure, Measure.prod_prod, ENNReal.toReal_mul, hA, hB]
  have hA' := lowThreshold_prob_ge_half n
  have hB' := highThreshold_prob_compl_ge_fifth n
  nlinarith

def someAtTop (n : ℕ) : Set (Sample n) :=
  { x | ∃ i, x i = 1 }

lemma measurableSet_someAtTop (n : ℕ) : MeasurableSet (someAtTop n) := by
  classical
  simpa [someAtTop, Set.setOf_exists] using
    MeasurableSet.iUnion fun i : Fin (sampleCount n) =>
      measurable_pi_apply i (measurableSet_singleton (1 : SourceSpace))

lemma sampleMeasure_someAtTop_zero (n : ℕ) : sampleMeasure n (someAtTop n) = 0 := by
  classical
  simpa [someAtTop, Set.setOf_exists, sampleMeasure] using
    (measure_iUnion_null fun i : Fin (sampleCount n) =>
      Measure.pi_hyperplane
        (μ := fun _ : Fin (sampleCount n) => (volume : Measure SourceSpace))
        i (1 : SourceSpace))

lemma pairMeasure_univ_prod_someAtTop_zero (n : ℕ) :
    pairMeasure n (Set.univ ×ˢ someAtTop n) = 0 := by
  rw [pairMeasure, Measure.prod_prod, sampleMeasure_someAtTop_zero]
  simp

def refinedCounterexampleEvent (n : ℕ) : Set (Sample n × Sample n) :=
  counterexampleEvent n \ (Set.univ ×ˢ someAtTop n)

lemma measurableSet_counterexampleEvent (n : ℕ) :
    MeasurableSet (counterexampleEvent n) := by
  exact (measurableSet_allBelow n (lowThreshold n)).prod
    (measurableSet_someAbove n (highThreshold n))

lemma measurableSet_refinedCounterexampleEvent (n : ℕ) :
    MeasurableSet (refinedCounterexampleEvent n) := by
  exact measurableSet_counterexampleEvent n |>.diff
    (MeasurableSet.univ.prod (measurableSet_someAtTop n))

lemma refinedCounterexampleEvent_probability_ge_tenth (n : ℕ) :
    (1 / 10 : ℝ) ≤ (pairMeasure n (refinedCounterexampleEvent n)).toReal := by
  rw [refinedCounterexampleEvent, measure_diff_null (pairMeasure_univ_prod_someAtTop_zero n)]
  exact event_probability_ge_tenth n

lemma sampleIndices_nonempty (n : ℕ) :
    (Finset.univ : Finset (Fin (sampleCount n))).Nonempty := by
  refine ⟨⟨0, by simp [sampleCount]⟩, Finset.mem_univ _⟩

def sampleMaxFeature (n : ℕ) (x : Sample n) : ℝ :=
  Finset.sup' Finset.univ
    (sampleIndices_nonempty n)
    fun i => tailFeature (x i)

lemma tailFeature_le_sampleMaxFeature (n : ℕ) (x : Sample n) (i : Fin (sampleCount n)) :
    tailFeature (x i) ≤ sampleMaxFeature n x := by
  unfold sampleMaxFeature
  exact Finset.le_sup' (f := fun j => tailFeature (x j)) (Finset.mem_univ i)

lemma sampleMaxFeature_le_tailFeature_of_mem_allBelow
    {n : ℕ} {a : SourceSpace} {x : Sample n}
    (hx : x ∈ allBelow n a) (ha : (a : ℝ) < 1) :
    sampleMaxFeature n x ≤ tailFeature a := by
  unfold sampleMaxFeature
  refine Finset.sup'_le (s := (Finset.univ : Finset (Fin (sampleCount n))))
    (f := fun i : Fin (sampleCount n) => tailFeature (x i))
    (sampleIndices_nonempty n) ?_
  intro i hi
  exact tailFeature_monotone_on_Iic ha (by simpa [allBelow] using hx i)

/--
The exact empirical `e-KQD₂` formula from the paper in the special case of a single sampled
rank-one feature and Lebesgue `ν`: sort the projected samples and take their normalized `L²` gap.
-/
def sortedFeature {n : ℕ} (u : SourceSpace → ℝ) (x : Sample n) :
    Fin (sampleCount n) → ℝ :=
  (fun i => u (x i)) ∘ Tuple.sort (fun i => u (x i))

lemma monotone_sortedFeature {n : ℕ} (u : SourceSpace → ℝ) (x : Sample n) :
    Monotone (sortedFeature u x) := by
  simpa [sortedFeature] using Tuple.monotone_sort (fun i => u (x i))

lemma sortedFeature_neg {n : ℕ} (u : SourceSpace → ℝ) (x : Sample n) :
    sortedFeature (fun t => -u t) x = fun i => -sortedFeature u x (Fin.rev i) := by
  let f : Fin (sampleCount n) → ℝ := fun i => u (x i)
  let g : Fin (sampleCount n) → ℝ := fun i => -f i
  have hmono : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
  have hmonoNeg :
      Monotone (g ∘ (Tuple.sort f * @Fin.revPerm (sampleCount n))) := by
    intro i j hij
    change -(f ((Tuple.sort f * @Fin.revPerm (sampleCount n)) i)) ≤
      -(f ((Tuple.sort f * @Fin.revPerm (sampleCount n)) j))
    simp [Function.comp]
    have hrev : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
    exact hmono hrev
  let sigma : Equiv.Perm (Fin (sampleCount n)) := Tuple.sort f * @Fin.revPerm (sampleCount n)
  have hEq :
      g ∘ sigma = g ∘ Tuple.sort g := by
    exact Tuple.unique_monotone (by simpa [sigma] using hmonoNeg) (Tuple.monotone_sort g)
  ext i
  have := congrFun hEq i
  simp [sortedFeature, f, g, sigma, Function.comp, Equiv.Perm.coe_mul] at this ⊢
  simpa using this.symm

lemma sortedFeature_neg_sum_sq {n : ℕ} (u : SourceSpace → ℝ) (x y : Sample n) :
    ∑ j : Fin (sampleCount n),
      (sortedFeature (fun t => -u t) x j - sortedFeature (fun t => -u t) y j) ^ 2 =
    ∑ j : Fin (sampleCount n),
      (sortedFeature u x j - sortedFeature u y j) ^ 2 := by
  rw [sortedFeature_neg, sortedFeature_neg]
  refine Fintype.sum_equiv Fin.revPerm _ _ ?_
  intro i
  simp [Fin.revPerm]
  ring

lemma feature_le_sortedFeature_last {n : ℕ} (u : SourceSpace → ℝ) (x : Sample n)
    (i : Fin (sampleCount n)) :
    u (x i) ≤ sortedFeature u x (lastIndex n) := by
  let perm : Equiv.Perm (Fin (sampleCount n)) := Tuple.sort (fun j => u (x j))
  have hmono : Monotone (sortedFeature u x) := monotone_sortedFeature u x
  have hle : perm.symm i ≤ lastIndex n := le_lastIndex n (perm.symm i)
  have hsorted := hmono hle
  simpa [sortedFeature, perm] using hsorted

lemma sortedTailFeature_last_eq_sampleMaxFeature {n : ℕ} (x : Sample n) :
    sortedFeature tailFeature x (lastIndex n) = sampleMaxFeature n x := by
  apply le_antisymm
  · have hlast :=
      tailFeature_le_sampleMaxFeature n x
        ((Tuple.sort (fun j => tailFeature (x j))) (lastIndex n))
    simpa [sortedFeature, lastIndex] using hlast
  · unfold sampleMaxFeature
    refine Finset.sup'_le (s := (Finset.univ : Finset (Fin (sampleCount n))))
      (f := fun i : Fin (sampleCount n) => tailFeature (x i))
      (sampleIndices_nonempty n) ?_
    intro i hi
    have hmono : Monotone (sortedFeature tailFeature x) := monotone_sortedFeature tailFeature x
    have hle : (Tuple.sort (fun j => tailFeature (x j))).symm i ≤ lastIndex n :=
      le_lastIndex n ((Tuple.sort (fun j => tailFeature (x j))).symm i)
    have hsorted := hmono hle
    simpa [sortedFeature] using hsorted

def empiricalRankOneEKQD2Sq (u : SourceSpace → ℝ) (n : ℕ) (x y : Sample n) : ℝ :=
  (1 / sampleCountReal n) *
    ∑ i : Fin (sampleCount n), (sortedFeature u x i - sortedFeature u y i) ^ 2

def empiricalRankOneEKQD2 (u : SourceSpace → ℝ) (n : ℕ) (x y : Sample n) : ℝ :=
  Real.sqrt (empiricalRankOneEKQD2Sq u n x y)

lemma empiricalRankOneEKQD2Sq_nonneg (u : SourceSpace → ℝ) (n : ℕ) (x y : Sample n) :
    0 ≤ empiricalRankOneEKQD2Sq u n x y := by
  unfold empiricalRankOneEKQD2Sq
  refine mul_nonneg ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
  exact one_div_nonneg.mpr (sampleCountReal_pos n).le

lemma empiricalRankOneEKQD2Sq_neg (u : SourceSpace → ℝ) (n : ℕ) (x y : Sample n) :
    empiricalRankOneEKQD2Sq (fun t => -u t) n x y = empiricalRankOneEKQD2Sq u n x y := by
  unfold empiricalRankOneEKQD2Sq
  rw [sortedFeature_neg_sum_sq]

def witnessScale (n : ℕ) : ℝ :=
  gapConstant * quarterTailRate n

lemma witnessScale_pos (n : ℕ) : 0 < witnessScale n := by
  unfold witnessScale
  exact mul_pos gapConstant_pos (quarterTailRate_pos n)

def rawRankOneTailWitness (n : ℕ) (z : Sample n × Sample n) : ℝ :=
  rootRate n * max (sampleMaxFeature n z.2 - sampleMaxFeature n z.1) 0

def clippedRankOneTailWitness (n : ℕ) (z : Sample n × Sample n) : ℝ :=
  min (rawRankOneTailWitness n z) (witnessScale n)

lemma rootRate_sq (n : ℕ) : rootRate n ^ 2 = 1 / sampleCountReal n := by
  unfold rootRate
  have hsqrt : Real.sqrt (sampleCountReal n) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (sampleCountReal_pos n)
  have hsq : (Real.sqrt (sampleCountReal n)) ^ 2 = sampleCountReal n := by
    rw [Real.sq_sqrt (sampleCountReal_pos n).le]
  calc
    (1 / Real.sqrt (sampleCountReal n)) ^ 2 = 1 / (Real.sqrt (sampleCountReal n)) ^ 2 := by
      field_simp [hsqrt]
    _ = 1 / sampleCountReal n := by rw [hsq]

lemma rawRankOneTailWitness_le_empiricalRankOneEKQD2 (n : ℕ) (z : Sample n × Sample n) :
    rawRankOneTailWitness n z ≤ empiricalRankOneEKQD2 tailFeature n z.1 z.2 := by
  let d := sampleMaxFeature n z.2 - sampleMaxFeature n z.1
  have hterm :
      d ^ 2 ≤
        ∑ i : Fin (sampleCount n),
          (sortedFeature tailFeature z.1 i - sortedFeature tailFeature z.2 i) ^ 2 := by
    have hsingle :
        (sortedFeature tailFeature z.1 (lastIndex n) -
            sortedFeature tailFeature z.2 (lastIndex n)) ^ 2 ≤
          ∑ i : Fin (sampleCount n),
            (sortedFeature tailFeature z.1 i - sortedFeature tailFeature z.2 i) ^ 2 := by
      exact Finset.single_le_sum
        (fun i _ => sq_nonneg (sortedFeature tailFeature z.1 i - sortedFeature tailFeature z.2 i))
        (by simp [lastIndex])
    have hd :
        d ^ 2 =
          (sortedFeature tailFeature z.1 (lastIndex n) -
              sortedFeature tailFeature z.2 (lastIndex n)) ^ 2 := by
      dsimp [d]
      rw [sortedTailFeature_last_eq_sampleMaxFeature, sortedTailFeature_last_eq_sampleMaxFeature]
      ring
    exact hd.trans_le hsingle
  have hsq :
      (rootRate n * d) ^ 2 ≤ empiricalRankOneEKQD2Sq tailFeature n z.1 z.2 := by
    calc
      (rootRate n * d) ^ 2 = (1 / sampleCountReal n) * d ^ 2 := by
        rw [mul_pow, rootRate_sq]
      _ ≤
          (1 / sampleCountReal n) *
            ∑ i : Fin (sampleCount n),
              (sortedFeature tailFeature z.1 i - sortedFeature tailFeature z.2 i) ^ 2 := by
            have hnonneg : 0 ≤ 1 / sampleCountReal n := by
              exact one_div_nonneg.mpr (sampleCountReal_pos n).le
            exact mul_le_mul_of_nonneg_left hterm hnonneg
      _ = empiricalRankOneEKQD2Sq tailFeature n z.1 z.2 := by
            simp [empiricalRankOneEKQD2Sq]
  have habs :
      |rootRate n * d| ≤ empiricalRankOneEKQD2 tailFeature n z.1 z.2 := by
    simpa [empiricalRankOneEKQD2] using Real.abs_le_sqrt hsq
  have hmaxabs : max d 0 ≤ |d| := by
    exact max_le (le_abs_self d) (abs_nonneg d)
  have hmul :
      rootRate n * max d 0 ≤ |rootRate n * d| := by
    calc
      rootRate n * max d 0 ≤ rootRate n * |d| := by
        exact mul_le_mul_of_nonneg_left hmaxabs (rootRate_pos n).le
      _ = |rootRate n * d| := by
        rw [abs_mul, abs_of_nonneg (rootRate_pos n).le]
  exact by
    simpa [rawRankOneTailWitness, d] using hmul.trans habs

lemma rawRankOneTailWitness_lower_bound_of_refinedCounterexampleEvent
    {n : ℕ} {z : Sample n × Sample n} (hz : z ∈ refinedCounterexampleEvent n) :
    witnessScale n ≤ rawRankOneTailWitness n z := by
  have hzCounter : z ∈ counterexampleEvent n := hz.1
  have hzNotTop : z ∉ Set.univ ×ˢ someAtTop n := hz.2
  have hzSplit :
      z.1 ∈ allBelow n (lowThreshold n) ∧ z.2 ∈ someAbove n (highThreshold n) := by
    simpa [counterexampleEvent] using hzCounter
  rcases hzSplit with ⟨hxAll, hySome⟩
  rcases hySome with ⟨i, hi⟩
  have hyi_ne_top : z.2 i ≠ (1 : SourceSpace) := by
    intro hEq
    exact hzNotTop ⟨by simp, ⟨i, hEq⟩⟩
  have hyi_lt_one : ((z.2 i : SourceSpace) : ℝ) < 1 := by
    have hle : ((z.2 i : SourceSpace) : ℝ) ≤ 1 := (z.2 i).2.2
    have hne : ((z.2 i : SourceSpace) : ℝ) ≠ 1 := by
      intro hEq
      apply hyi_ne_top
      ext
      simpa using hEq
    exact lt_of_le_of_ne hle hne
  have hxMax :
      sampleMaxFeature n z.1 ≤ tailFeature (lowThreshold n) :=
    sampleMaxFeature_le_tailFeature_of_mem_allBelow hxAll (lowThreshold_lt_one n)
  have hyMax :
      tailFeature (highThreshold n) ≤ sampleMaxFeature n z.2 := by
    have hmono :
        tailFeature (highThreshold n) ≤ tailFeature (z.2 i) :=
      tailFeature_monotone_on_Iic hyi_lt_one hi.le
    exact hmono.trans (tailFeature_le_sampleMaxFeature n z.2 i)
  have hgap :
      gapConstant * Real.sqrt (Real.sqrt (sampleCountReal n)) ≤
        max (sampleMaxFeature n z.2 - sampleMaxFeature n z.1) 0 := by
    have hdiff :
        tailFeature (highThreshold n) - tailFeature (lowThreshold n) ≤
          sampleMaxFeature n z.2 - sampleMaxFeature n z.1 := by
      nlinarith [hyMax, hxMax]
    have hgap' :
        gapConstant * Real.sqrt (Real.sqrt (sampleCountReal n)) ≤
          sampleMaxFeature n z.2 - sampleMaxFeature n z.1 := by
      simpa [high_minus_low_eq_gap n] using hdiff
    exact hgap'.trans (le_max_left _ _)
  rw [witnessScale, ← gap_over_root_eq_quarter n]
  unfold rawRankOneTailWitness
  have hmul := mul_le_mul_of_nonneg_right hgap (rootRate_pos n).le
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

lemma clippedRankOneTailWitness_eq_scale_of_refinedCounterexampleEvent
    {n : ℕ} {z : Sample n × Sample n} (hz : z ∈ refinedCounterexampleEvent n) :
    clippedRankOneTailWitness n z = witnessScale n := by
  unfold clippedRankOneTailWitness
  exact min_eq_right (rawRankOneTailWitness_lower_bound_of_refinedCounterexampleEvent hz)

def expectedPairError (err : ∀ n, Sample n × Sample n → ℝ) (n : ℕ) : ℝ :=
  (∫⁻ z, ENNReal.ofReal (err n z) ∂ pairMeasure n).toReal

def expectedClippedRankOneTailWitness (n : ℕ) : ℝ :=
  expectedPairError clippedRankOneTailWitness n

lemma expectedClippedRankOneTailWitness_lower_bound (n : ℕ) :
    (gapConstant / 10) * quarterTailRate n ≤ expectedClippedRankOneTailWitness n := by
  have hpoint :
      Set.indicator (refinedCounterexampleEvent n) (fun _ => ENNReal.ofReal (witnessScale n)) ≤
        fun z => ENNReal.ofReal (clippedRankOneTailWitness n z) := by
    intro z
    by_cases hz : z ∈ refinedCounterexampleEvent n
    · simp [hz, clippedRankOneTailWitness_eq_scale_of_refinedCounterexampleEvent hz]
    · simp [hz]
  have hlin :
      ENNReal.ofReal (witnessScale n) * pairMeasure n (refinedCounterexampleEvent n) ≤
        ∫⁻ z, ENNReal.ofReal (clippedRankOneTailWitness n z) ∂ pairMeasure n := by
    rw [← lintegral_indicator_const (measurableSet_refinedCounterexampleEvent n)
      (ENNReal.ofReal (witnessScale n))]
    exact lintegral_mono hpoint
  have hbound :
      (∫⁻ z, ENNReal.ofReal (clippedRankOneTailWitness n z) ∂ pairMeasure n) ≤
        ENNReal.ofReal (witnessScale n) := by
    calc
      (∫⁻ z, ENNReal.ofReal (clippedRankOneTailWitness n z) ∂ pairMeasure n) ≤
          ∫⁻ z, ENNReal.ofReal (witnessScale n) ∂ pairMeasure n := by
            refine lintegral_mono ?_
            intro z
            exact ENNReal.ofReal_le_ofReal (by
              unfold clippedRankOneTailWitness
              exact min_le_right _ _)
      _ = ENNReal.ofReal (witnessScale n) * pairMeasure n Set.univ := by
            rw [lintegral_const]
      _ = ENNReal.ofReal (witnessScale n) := by simp [pairMeasure]
  have hfinite :
      (∫⁻ z, ENNReal.ofReal (clippedRankOneTailWitness n z) ∂ pairMeasure n) ≠ ⊤ := by
    exact ne_of_lt <| lt_of_le_of_lt hbound (by simp)
  have hto :
      (ENNReal.ofReal (witnessScale n) * pairMeasure n (refinedCounterexampleEvent n)).toReal ≤
        expectedClippedRankOneTailWitness n :=
    ENNReal.toReal_mono hfinite hlin
  rw [expectedClippedRankOneTailWitness, expectedPairError, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (witnessScale_pos n).le] at hto
  have hprob := refinedCounterexampleEvent_probability_ge_tenth n
  unfold witnessScale at hto
  have hscaled :
      gapConstant * quarterTailRate n * (1 / 10 : ℝ) ≤
        gapConstant * quarterTailRate n *
          ((pairMeasure n) (refinedCounterexampleEvent n)).toReal := by
    exact mul_le_mul_of_nonneg_left hprob
      (mul_nonneg gapConstant_pos.le (quarterTailRate_pos n).le)
  calc
    (gapConstant / 10) * quarterTailRate n
        = gapConstant * quarterTailRate n * (1 / 10 : ℝ) := by ring
    _ ≤ gapConstant * quarterTailRate n * ((pairMeasure n) (refinedCounterexampleEvent n)).toReal :=
        hscaled
    _ ≤ expectedClippedRankOneTailWitness n := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hto

theorem clippedRankOneTailWitness_has_quarterTail_lower_rate :
    EventuallyLowerBoundedByQuarterTailRate expectedClippedRankOneTailWitness := by
  refine ⟨gapConstant / 10, by nlinarith [gapConstant_pos], ?_⟩
  exact Filter.Eventually.of_forall fun n =>
    expectedClippedRankOneTailWitness_lower_bound n

theorem clippedRankOneTailWitness_not_eventuallyBoundedByRootRate :
    ¬ EventuallyBoundedByRootRate expectedClippedRankOneTailWitness := by
  exact not_eventuallyBoundedByRootRate_of_quarterTailLowerBound
    clippedRankOneTailWitness_has_quarterTail_lower_rate

theorem expectedPairError_lower_rate_of_dominatesClippedRankOneTailWitness
    {err : ∀ n, Sample n × Sample n → ℝ}
    (hdom : ∀ n z, clippedRankOneTailWitness n z ≤ err n z)
    (hfinite : ∀ n, (∫⁻ z, ENNReal.ofReal (err n z) ∂pairMeasure n) ≠ ⊤) :
    EventuallyLowerBoundedByQuarterTailRate (expectedPairError err) := by
  refine ⟨gapConstant / 10, by nlinarith [gapConstant_pos], ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro n
  have hwit := expectedClippedRankOneTailWitness_lower_bound n
  have hlin :
      (∫⁻ z, ENNReal.ofReal (clippedRankOneTailWitness n z) ∂ pairMeasure n) ≤
        ∫⁻ z, ENNReal.ofReal (err n z) ∂ pairMeasure n := by
    refine lintegral_mono ?_
    intro z
    exact ENNReal.ofReal_le_ofReal (hdom n z)
  have hmono :
      expectedClippedRankOneTailWitness n ≤ expectedPairError err n := by
    exact ENNReal.toReal_mono (hfinite n) hlin
  exact le_trans hwit hmono

theorem not_eventuallyBoundedByRootRate_of_dominatesClippedRankOneTailWitness
    {err : ∀ n, Sample n × Sample n → ℝ}
    (hdom : ∀ n z, clippedRankOneTailWitness n z ≤ err n z)
    (hfinite : ∀ n, (∫⁻ z, ENNReal.ofReal (err n z) ∂pairMeasure n) ≠ ⊤) :
    ¬ EventuallyBoundedByRootRate (expectedPairError err) := by
  exact not_eventuallyBoundedByRootRate_of_quarterTailLowerBound
    (expectedPairError_lower_rate_of_dominatesClippedRankOneTailWitness hdom hfinite)

/-- The clipped empirical rank-one `e-KQD₂` error for the explicit tail kernel. -/
def clippedEmpiricalRankOneTailEKQD2 (n : ℕ) (z : Sample n × Sample n) : ℝ :=
  min (empiricalRankOneEKQD2 tailFeature n z.1 z.2) (witnessScale n)

lemma clippedRankOneTailWitness_le_clippedEmpiricalRankOneTailEKQD2
    (n : ℕ) (z : Sample n × Sample n) :
    clippedRankOneTailWitness n z ≤ clippedEmpiricalRankOneTailEKQD2 n z := by
  unfold clippedRankOneTailWitness clippedEmpiricalRankOneTailEKQD2
  exact min_le_min (rawRankOneTailWitness_le_empiricalRankOneEKQD2 n z) le_rfl

lemma clippedEmpiricalRankOneTailEKQD2_lintegral_ne_top (n : ℕ) :
    (∫⁻ z, ENNReal.ofReal (clippedEmpiricalRankOneTailEKQD2 n z) ∂ pairMeasure n) ≠ ⊤ := by
  have hbound :
      (∫⁻ z, ENNReal.ofReal (clippedEmpiricalRankOneTailEKQD2 n z) ∂ pairMeasure n) ≤
        ENNReal.ofReal (witnessScale n) := by
    calc
      (∫⁻ z, ENNReal.ofReal (clippedEmpiricalRankOneTailEKQD2 n z) ∂ pairMeasure n) ≤
          ∫⁻ z, ENNReal.ofReal (witnessScale n) ∂ pairMeasure n := by
            refine lintegral_mono ?_
            intro z
            exact ENNReal.ofReal_le_ofReal (by
              unfold clippedEmpiricalRankOneTailEKQD2
              exact min_le_right _ _)
      _ = ENNReal.ofReal (witnessScale n) * pairMeasure n Set.univ := by
            rw [lintegral_const]
      _ = ENNReal.ofReal (witnessScale n) := by simp [pairMeasure]
  exact ne_of_lt <| lt_of_le_of_lt hbound (by simp)

def expectedClippedEmpiricalRankOneTailEKQD2 (n : ℕ) : ℝ :=
  expectedPairError clippedEmpiricalRankOneTailEKQD2 n

theorem expectedClippedEmpiricalRankOneTailEKQD2_has_quarterTail_lower_rate :
    EventuallyLowerBoundedByQuarterTailRate expectedClippedEmpiricalRankOneTailEKQD2 := by
  exact expectedPairError_lower_rate_of_dominatesClippedRankOneTailWitness
    clippedRankOneTailWitness_le_clippedEmpiricalRankOneTailEKQD2
    clippedEmpiricalRankOneTailEKQD2_lintegral_ne_top

theorem expectedClippedEmpiricalRankOneTailEKQD2_not_eventuallyBoundedByRootRate :
    ¬ EventuallyBoundedByRootRate expectedClippedEmpiricalRankOneTailEKQD2 := by
  exact not_eventuallyBoundedByRootRate_of_quarterTailLowerBound
    expectedClippedEmpiricalRankOneTailEKQD2_has_quarterTail_lower_rate

def tailKernel (x y : SourceSpace) : ℝ :=
  tailFeature x * tailFeature y

lemma tailKernel_diag_eq_symm_rpow (x : SourceSpace) :
    tailKernel x x = (((unitInterval.symm x : SourceSpace) : ℝ) ^ (-(1 / 2 : ℝ))) := by
  unfold tailKernel
  rw [show tailFeature x * tailFeature x = tailFeature x ^ 2 by ring, tailFeature_sq,
    unitInterval.coe_symm_eq, Real.sqrt_eq_rpow]
  rw [← Real.rpow_neg_one (1 - (x : ℝ))]
  rw [← Real.rpow_mul (unitInterval.one_minus_nonneg x)]
  congr 1
  ring

lemma integrable_symm_rpow_neg_half :
    Integrable (fun x : SourceSpace => ((x : ℝ) ^ (-(1 / 2 : ℝ)))) volume := by
  have hIoo :
      IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Set.Ioo (0 : ℝ) 1) volume := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
    norm_num
  have hIcc :
      IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Set.Icc (0 : ℝ) 1) volume := by
    rwa [integrableOn_Icc_iff_integrableOn_Ioo]
  have hSubtype :
      Integrable
        ((fun t : ℝ => t ^ (-(1 / 2 : ℝ))) ∘ ((↑) : SourceSpace → ℝ))
        (volume.comap ((↑) : SourceSpace → ℝ)) := by
    exact
      (integrableOn_iff_comap_subtypeVal
        (μ := volume) (s := Set.Icc (0 : ℝ) 1)
        (f := fun t : ℝ => t ^ (-(1 / 2 : ℝ))) measurableSet_Icc).1 hIcc
  simpa [unitInterval.volume_def] using hSubtype

lemma tailKernel_diagonal_moment_finite :
    Integrable (fun x : SourceSpace => tailKernel x x) volume := by
  have hpow : Integrable (fun x : SourceSpace => ((x : ℝ) ^ (-(1 / 2 : ℝ)))) volume :=
    integrable_symm_rpow_neg_half
  have hsymm :
      Integrable
        (fun x : SourceSpace => (((unitInterval.symm x : SourceSpace) : ℝ) ^ (-(1 / 2 : ℝ))))
        volume := by
    simpa [Function.comp] using
      unitInterval.measurePreserving_symm.integrable_comp_of_integrable
        (g := fun x : SourceSpace => ((x : ℝ) ^ (-(1 / 2 : ℝ)))) hpow
  refine hsymm.congr ?_
  exact Filter.Eventually.of_forall fun x => (tailKernel_diag_eq_symm_rpow x).symm

/-- The one-dimensional RKHS unit sphere for the rank-one tail kernel. -/
abbrev RankOneUnitSphere := {u : ℝ // ‖u‖ = 1}

/-- The positive unit direction generating the rank-one tail kernel. -/
def tailDirection : RankOneUnitSphere :=
  ⟨1, by simp⟩

/-- The negative unit direction on the same rank-one sphere. -/
def negTailDirection : RankOneUnitSphere :=
  ⟨-1, by simp⟩

/-- Evaluation in the explicit rank-one RKHS model. -/
def rankOneEval (u : ℝ) (x : SourceSpace) : ℝ :=
  u * tailFeature x

/-- Kernel section `k(x, ·)` in the rank-one RKHS model. -/
def tailKernelSection (x : SourceSpace) : ℝ :=
  tailFeature x

lemma measurable_tailFeature : Measurable tailFeature := by
  unfold tailFeature
  fun_prop

lemma rankOneEval_measurable (u : ℝ) : Measurable (rankOneEval u) := by
  unfold rankOneEval
  exact measurable_const.mul measurable_tailFeature

lemma tailDirection_eval_eq_tailFeature (x : SourceSpace) :
    rankOneEval tailDirection.1 x = tailFeature x := by
  simp [rankOneEval, tailDirection]

lemma negTailDirection_eval_eq_neg_tailFeature (x : SourceSpace) :
    rankOneEval negTailDirection.1 x = -tailFeature x := by
  simp [rankOneEval, negTailDirection]

lemma rankOneEval_reproducing (u : ℝ) (x : SourceSpace) :
    rankOneEval u x = inner ℝ u (tailKernelSection x) := by
  simp [rankOneEval, tailKernelSection, RCLike.inner_apply, mul_comm]

lemma tailKernel_eq_inner_feature (x y : SourceSpace) :
    tailKernel x y = tailFeature x * tailFeature y := by
  rfl

lemma tailKernel_eq_inner_sections (x y : SourceSpace) :
    tailKernel x y = inner ℝ (tailKernelSection x) (tailKernelSection y) := by
  simp [tailKernel, tailKernelSection, RCLike.inner_apply, mul_comm]

lemma rankOneEval_eq_inner_feature (u : ℝ) (x : SourceSpace) :
    rankOneEval u x = u * tailFeature x := by
  rfl

def tailGamma : Measure RankOneUnitSphere :=
  ((2 : ENNReal)⁻¹ • Measure.dirac tailDirection) +
    ((2 : ENNReal)⁻¹ • Measure.dirac negTailDirection)

instance tailGamma_isProbability : IsProbabilityMeasure tailGamma := by
  refine ⟨by
    rw [tailGamma]
    simpa using ENNReal.inv_two_add_inv_two⟩

def halfSampleCount (l : ℕ) : ℕ :=
  l + 1

lemma sampleCount_eq_double_half (l : ℕ) :
    sampleCount l = halfSampleCount l + halfSampleCount l := by
  simp [sampleCount, halfSampleCount, two_mul, add_comm, add_left_comm, add_assoc]

def positiveDirectionIndices (l : ℕ) : Set (Fin (sampleCount l)) :=
  {i | i.1 < halfSampleCount l}

lemma halfSampleCount_le_sampleCount (l : ℕ) :
    halfSampleCount l ≤ sampleCount l := by
  rw [sampleCount_eq_double_half]
  omega

def positiveDirectionIndicesEquiv (l : ℕ) :
    positiveDirectionIndices l ≃ Fin (halfSampleCount l) where
  toFun i := ⟨i.1.1, i.2⟩
  invFun i := ⟨⟨i.1, lt_of_lt_of_le i.2 (halfSampleCount_le_sampleCount l)⟩, i.2⟩
  left_inv i := by
    cases i with
    | mk i hi =>
        cases i with
        | mk val isLt =>
            rfl
  right_inv i := by
    cases i
    rfl

lemma card_positiveDirectionIndices (l : ℕ) :
    Fintype.card (positiveDirectionIndices l) = halfSampleCount l := by
  exact (Fintype.card_congr (positiveDirectionIndicesEquiv l)).trans (Fintype.card_fin _)

lemma count_positiveDirectionIndices (l : ℕ) :
    Measure.count (positiveDirectionIndices l) = halfSampleCount l := by
  rw [Measure.count_apply_finite _ (positiveDirectionIndices l).toFinite]
  rw [Set.toFinite_toFinset, Set.toFinset_card]
  exact_mod_cast card_positiveDirectionIndices l

lemma count_positiveDirectionIndices_compl (l : ℕ) :
    Measure.count ((positiveDirectionIndices l)ᶜ) = halfSampleCount l := by
  rw [Measure.count_apply_finite _ ((positiveDirectionIndices l)ᶜ).toFinite]
  rw [Set.toFinite_toFinset, Set.toFinset_card, Fintype.card_compl_set]
  rw [show Fintype.card (Fin (sampleCount l)) = sampleCount l by simp]
  rw [card_positiveDirectionIndices]
  rw [sampleCount_eq_double_half]
  simp

lemma uniformOn_positiveDirectionIndices (l : ℕ) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin (sampleCount l)))
      (positiveDirectionIndices l) = (2 : ENNReal)⁻¹ := by
  rw [ProbabilityTheory.uniformOn_univ, count_positiveDirectionIndices]
  rw [Fintype.card_fin]
  rw [show ((sampleCount l : ℕ) : ENNReal) =
      (halfSampleCount l : ENNReal) + halfSampleCount l by
    simp [sampleCount_eq_double_half]]
  have hhalf_ne_zero : ((halfSampleCount l : ℕ) : ENNReal) ≠ 0 := by
    simpa [halfSampleCount] using (Nat.succ_ne_zero l)
  have hhalf_ne_top : ((halfSampleCount l : ℕ) : ENNReal) ≠ ⊤ := by
    simp
  calc
    (halfSampleCount l : ENNReal) / ((halfSampleCount l : ENNReal) + halfSampleCount l)
        = ((1 : ENNReal) * (halfSampleCount l : ENNReal)) /
            ((2 : ENNReal) * (halfSampleCount l : ENNReal)) := by
              simp [two_mul]
    _ = (1 : ENNReal) / 2 := by
          simpa using
            (ENNReal.mul_div_mul_right (1 : ENNReal) (2 : ENNReal) hhalf_ne_zero hhalf_ne_top)
  simp [one_div]

lemma uniformOn_positiveDirectionIndices_compl (l : ℕ) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin (sampleCount l)))
      ((positiveDirectionIndices l)ᶜ) = (2 : ENNReal)⁻¹ := by
  rw [ProbabilityTheory.uniformOn_univ, count_positiveDirectionIndices_compl]
  rw [Fintype.card_fin]
  rw [show ((sampleCount l : ℕ) : ENNReal) =
      (halfSampleCount l : ENNReal) + halfSampleCount l by
    simp [sampleCount_eq_double_half]]
  have hhalf_ne_zero : ((halfSampleCount l : ℕ) : ENNReal) ≠ 0 := by
    simpa [halfSampleCount] using (Nat.succ_ne_zero l)
  have hhalf_ne_top : ((halfSampleCount l : ℕ) : ENNReal) ≠ ⊤ := by
    simp
  calc
    (halfSampleCount l : ENNReal) / ((halfSampleCount l : ENNReal) + halfSampleCount l)
        = ((1 : ENNReal) * (halfSampleCount l : ENNReal)) /
            ((2 : ENNReal) * (halfSampleCount l : ENNReal)) := by
              simp [two_mul]
    _ = (1 : ENNReal) / 2 := by
          simpa using
            (ENNReal.mul_div_mul_right (1 : ENNReal) (2 : ENNReal) hhalf_ne_zero hhalf_ne_top)
  simp [one_div]

def tailSampledDirections (l : ℕ) (i : Fin (sampleCount l)) : RankOneUnitSphere :=
  if i.1 < halfSampleCount l then tailDirection else negTailDirection

lemma tailSampledDirections_eq_tailDirection {l : ℕ} {i : Fin (sampleCount l)}
    (hi : i.1 < halfSampleCount l) :
    tailSampledDirections l i = tailDirection := by
  simp [tailSampledDirections, hi]

lemma tailSampledDirections_eq_negTailDirection {l : ℕ} {i : Fin (sampleCount l)}
    (hi : halfSampleCount l ≤ i.1) :
    tailSampledDirections l i = negTailDirection := by
  simp [tailSampledDirections, Nat.not_lt.mpr hi]

def repeatedTailDirection (l : ℕ) (i : Fin (sampleCount l)) : SourceSpace → ℝ :=
  rankOneEval (tailSampledDirections l i).1

abbrev SignSample (l : ℕ) := Fin (sampleCount l) → Bool

def directionOfSign (b : Bool) : RankOneUnitSphere :=
  if b then tailDirection else negTailDirection

def signedDirections (l : ℕ) (s : SignSample l) (i : Fin (sampleCount l)) : RankOneUnitSphere :=
  directionOfSign (s i)

def signMeasure : Measure Bool :=
  ((2 : ENNReal)⁻¹ • Measure.dirac true) + ((2 : ENNReal)⁻¹ • Measure.dirac false)

instance signMeasure_isProbability : IsProbabilityMeasure signMeasure := by
  refine ⟨by
    rw [signMeasure]
    simpa using ENNReal.inv_two_add_inv_two⟩

def signSampleMeasure (l : ℕ) : Measure (SignSample l) :=
  Measure.pi fun _ => signMeasure

instance signSampleMeasure_isProbability (l : ℕ) :
    IsProbabilityMeasure (signSampleMeasure l) := by
  unfold signSampleMeasure
  infer_instance

def paperEqFiveTailEKQD2SqWithDirections (n l : ℕ)
    (dirs : Fin (sampleCount l) → RankOneUnitSphere) (z : Sample n × Sample n) : ℝ :=
  (1 / (sampleCountReal l * sampleCountReal n)) *
    ∑ i : Fin (sampleCount l),
      ∑ j : Fin (sampleCount n),
        (sortedFeature (rankOneEval (dirs i).1) z.1 j -
          sortedFeature (rankOneEval (dirs i).1) z.2 j) ^ 2

def paperEqFiveTailEKQD2WithDirections (n l : ℕ)
    (dirs : Fin (sampleCount l) → RankOneUnitSphere) (z : Sample n × Sample n) : ℝ :=
  Real.sqrt (paperEqFiveTailEKQD2SqWithDirections n l dirs z)

lemma paperEqFiveTailEKQD2SqWithDirections_nonneg
    (n l : ℕ) (dirs : Fin (sampleCount l) → RankOneUnitSphere) (z : Sample n × Sample n) :
    0 ≤ paperEqFiveTailEKQD2SqWithDirections n l dirs z := by
  unfold paperEqFiveTailEKQD2SqWithDirections
  refine mul_nonneg ?_ (Finset.sum_nonneg fun i _ => ?_)
  · exact one_div_nonneg.mpr (mul_nonneg (sampleCountReal_pos l).le (sampleCountReal_pos n).le)
  · exact Finset.sum_nonneg fun j _ => sq_nonneg _

lemma paperEqFiveTailEKQD2Sq_signedDirections_eq_empiricalRankOneEKQD2Sq
    (n l : ℕ) (s : SignSample l) (z : Sample n × Sample n) :
    paperEqFiveTailEKQD2SqWithDirections n l (signedDirections l s) z =
      empiricalRankOneEKQD2Sq tailFeature n z.1 z.2 := by
  let inner : ℝ :=
    ∑ j : Fin (sampleCount n),
      (sortedFeature tailFeature z.1 j - sortedFeature tailFeature z.2 j) ^ 2
  have hsum :
      ∑ i : Fin (sampleCount l),
        ∑ j : Fin (sampleCount n),
          (sortedFeature (rankOneEval (signedDirections l s i).1) z.1 j -
            sortedFeature (rankOneEval (signedDirections l s i).1) z.2 j) ^ 2
        = (sampleCount l : ℝ) * inner := by
    calc
      ∑ i : Fin (sampleCount l),
          ∑ j : Fin (sampleCount n),
            (sortedFeature (rankOneEval (signedDirections l s i).1) z.1 j -
              sortedFeature (rankOneEval (signedDirections l s i).1) z.2 j) ^ 2
        = ∑ i : Fin (sampleCount l), inner := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hsign : s i
            · have hdir : rankOneEval (signedDirections l s i).1 = tailFeature := by
                funext x
                simp [signedDirections, directionOfSign, hsign, tailDirection, rankOneEval]
              simpa [hdir, inner]
            · have hdir : rankOneEval (signedDirections l s i).1 = fun x => -tailFeature x := by
                funext x
                simp [signedDirections, directionOfSign, hsign, negTailDirection, rankOneEval]
              simpa [hdir, inner] using sortedFeature_neg_sum_sq tailFeature z.1 z.2
      _ = (sampleCount l : ℝ) * inner := by
            simp [Finset.sum_const, nsmul_eq_mul]
  unfold paperEqFiveTailEKQD2SqWithDirections empiricalRankOneEKQD2Sq
  rw [hsum, show (sampleCount l : ℝ) = sampleCountReal l by simp [sampleCountReal]]
  field_simp [sampleCountReal_ne_zero l, sampleCountReal_ne_zero n]
  ring

lemma paperEqFiveTailEKQD2_signedDirections_eq_empiricalRankOneEKQD2
    (n l : ℕ) (s : SignSample l) (z : Sample n × Sample n) :
    paperEqFiveTailEKQD2WithDirections n l (signedDirections l s) z =
      empiricalRankOneEKQD2 tailFeature n z.1 z.2 := by
  unfold paperEqFiveTailEKQD2WithDirections empiricalRankOneEKQD2
  rw [paperEqFiveTailEKQD2Sq_signedDirections_eq_empiricalRankOneEKQD2Sq]

/-- Equation (5) from the paper in the point-mass `γ_L = δ_u` tail-kernel specialization. -/
def paperEqFiveTailEKQD2Sq (n l : ℕ) (z : Sample n × Sample n) : ℝ :=
  (1 / (sampleCountReal l * sampleCountReal n)) *
    ∑ i : Fin (sampleCount l),
      ∑ j : Fin (sampleCount n),
        (sortedFeature (repeatedTailDirection l i) z.1 j -
          sortedFeature (repeatedTailDirection l i) z.2 j) ^ 2

def paperEqFiveTailEKQD2 (n l : ℕ) (z : Sample n × Sample n) : ℝ :=
  Real.sqrt (paperEqFiveTailEKQD2Sq n l z)

lemma paperEqFiveTailEKQD2Sq_nonneg (n l : ℕ) (z : Sample n × Sample n) :
    0 ≤ paperEqFiveTailEKQD2Sq n l z := by
  unfold paperEqFiveTailEKQD2Sq
  refine mul_nonneg ?_ (Finset.sum_nonneg fun i _ => ?_)
  · exact one_div_nonneg.mpr (mul_nonneg (sampleCountReal_pos l).le (sampleCountReal_pos n).le)
  · exact Finset.sum_nonneg fun j _ => sq_nonneg _

lemma paperEqFiveTailEKQD2Sq_eq_empiricalRankOneEKQD2Sq (n l : ℕ) (z : Sample n × Sample n) :
    paperEqFiveTailEKQD2Sq n l z = empiricalRankOneEKQD2Sq tailFeature n z.1 z.2 := by
  let inner : ℝ :=
    ∑ j : Fin (sampleCount n),
      (sortedFeature tailFeature z.1 j - sortedFeature tailFeature z.2 j) ^ 2
  have hsum :
      ∑ i : Fin (sampleCount l),
        ∑ j : Fin (sampleCount n),
          (sortedFeature (repeatedTailDirection l i) z.1 j -
            sortedFeature (repeatedTailDirection l i) z.2 j) ^ 2
        = (sampleCount l : ℝ) * inner := by
    calc
      ∑ i : Fin (sampleCount l),
          ∑ j : Fin (sampleCount n),
            (sortedFeature (repeatedTailDirection l i) z.1 j -
              sortedFeature (repeatedTailDirection l i) z.2 j) ^ 2
          = ∑ i : Fin (sampleCount l), inner := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hi' : i.1 < halfSampleCount l
              · have hdir : repeatedTailDirection l i = tailFeature := by
                  funext x
                  simp [repeatedTailDirection, tailSampledDirections, hi', tailDirection,
                    rankOneEval]
                simpa [hdir, inner]
              · have hle : halfSampleCount l ≤ i.1 := Nat.le_of_not_lt hi'
                have hdir : repeatedTailDirection l i = fun x => -tailFeature x := by
                  funext x
                  simp [repeatedTailDirection, tailSampledDirections, hi', negTailDirection,
                    rankOneEval]
                simpa [hdir, inner] using sortedFeature_neg_sum_sq tailFeature z.1 z.2
      _ = (sampleCount l : ℝ) * inner := by
            simp [Finset.sum_const, nsmul_eq_mul]
  unfold paperEqFiveTailEKQD2Sq empiricalRankOneEKQD2Sq
  rw [hsum, show (sampleCount l : ℝ) = sampleCountReal l by simp [sampleCountReal]]
  field_simp [sampleCountReal_ne_zero l, sampleCountReal_ne_zero n]
  ring

lemma paperEqFiveTailEKQD2_eq_empiricalRankOneEKQD2 (n l : ℕ) (z : Sample n × Sample n) :
    paperEqFiveTailEKQD2 n l z = empiricalRankOneEKQD2 tailFeature n z.1 z.2 := by
  unfold paperEqFiveTailEKQD2 empiricalRankOneEKQD2
  rw [paperEqFiveTailEKQD2Sq_eq_empiricalRankOneEKQD2Sq]

/-- The conjectured `L^{-1/2} + N^{-1/2}` error law, abstracted for a two-parameter rate claim. -/
def ConjecturedTwoParameterRootRate (err : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ n l, err n ≤ C * (rootRate l + rootRate n)

lemma ConjecturedTwoParameterRootRate.of_le {f g : ℕ → ℝ}
    (hle : ∀ n, f n ≤ g n) :
    ConjecturedTwoParameterRootRate g → ConjecturedTwoParameterRootRate f := by
  rintro ⟨C, hC, hbound⟩
  exact ⟨C, hC, fun n l => (hle n).trans (hbound n l)⟩

lemma ConjecturedTwoParameterRootRate.eventuallyBoundedByRootRate {err : ℕ → ℝ}
    (hRate : ConjecturedTwoParameterRootRate err) :
    EventuallyBoundedByRootRate err := by
  rcases hRate with ⟨C, hC, hbound⟩
  refine ⟨2 * C, by positivity, Filter.Eventually.of_forall ?_⟩
  intro n
  have hnn := hbound n n
  calc
    err n ≤ C * (rootRate n + rootRate n) := by simpa using hnn
    _ = (2 * C) * rootRate n := by ring

theorem expectedClippedEmpiricalRankOneTailEKQD2_not_twoParameterRootRate :
    ¬ ConjecturedTwoParameterRootRate expectedClippedEmpiricalRankOneTailEKQD2 := by
  intro hRate
  exact expectedClippedEmpiricalRankOneTailEKQD2_not_eventuallyBoundedByRootRate
    (ConjecturedTwoParameterRootRate.eventuallyBoundedByRootRate hRate)

/-- The quantile grid used in Equation (5), with the index shift `N = sampleCount n`. -/
def quantileGridPoint (n : ℕ) (j : Fin (sampleCount n)) : SourceSpace :=
  ⟨((j.1 : ℝ) + 1) / sampleCountReal n, by
    have hN : 0 < sampleCountReal n := sampleCountReal_pos n
    constructor
    · exact div_nonneg (by positivity) hN.le
    · have hj : j.1 + 1 ≤ sampleCount n := Nat.succ_le_of_lt j.2
      have hj' : (((j.1 + 1 : ℕ) : ℝ)) ≤ (sampleCount n : ℝ) := by
        exact_mod_cast hj
      have hj'' : ((j.1 : ℝ) + 1) ≤ sampleCountReal n := by
        simpa [sampleCountReal] using hj'
      calc
        ((j.1 : ℝ) + 1) / sampleCountReal n ≤ sampleCountReal n / sampleCountReal n := by
          exact div_le_div_of_nonneg_right hj'' hN.le
        _ = 1 := by
          field_simp [sampleCountReal_ne_zero n]⟩

/-- Right-quantile of a real probability law, defined from its CDF. -/
def realQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (α : SourceSpace) : ℝ :=
  sInf {x : ℝ | (α : ℝ) ≤ ProbabilityTheory.cdf μ x}

def realQuantileLevelSet (μ : Measure ℝ) [IsProbabilityMeasure μ] (α : SourceSpace) : Set ℝ :=
  {x : ℝ | (α : ℝ) ≤ ProbabilityTheory.cdf μ x}

lemma realQuantile_eq_sInf_levelSet (μ : Measure ℝ) [IsProbabilityMeasure μ] (α : SourceSpace) :
    realQuantile μ α = sInf (realQuantileLevelSet μ α) := rfl

lemma realQuantileLevelSet_nonempty {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : SourceSpace}
    (hα0 : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1) :
    (realQuantileLevelSet μ α).Nonempty := by
  obtain ⟨x, hx⟩ :
      ∃ x : ℝ, (α : ℝ) < ProbabilityTheory.cdf μ x := by
    exact ((ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hα1)).exists
  exact ⟨x, hx.le⟩

lemma realQuantileLevelSet_bddBelow {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : SourceSpace}
    (hα0 : 0 < (α : ℝ)) :
    BddBelow (realQuantileLevelSet μ α) := by
  obtain ⟨b, hb⟩ :
      ∃ b : ℝ, ProbabilityTheory.cdf μ b < (α : ℝ) := by
    exact ((ProbabilityTheory.tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hα0)).exists
  refine ⟨b, ?_⟩
  intro x hx
  by_contra hxb
  have hmono := ProbabilityTheory.monotone_cdf μ
  have hxb' : x < b := lt_of_not_ge hxb
  have hxlt : ProbabilityTheory.cdf μ x < (α : ℝ) := by
    exact lt_of_le_of_lt (hmono hxb'.le) hb
  exact not_le_of_gt hxlt hx

lemma realQuantile_le_of_cdf_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : SourceSpace}
    (hα0 : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1) {x : ℝ}
    (hx : (α : ℝ) ≤ ProbabilityTheory.cdf μ x) :
    realQuantile μ α ≤ x := by
  exact csInf_le (realQuantileLevelSet_bddBelow hα0) hx

lemma cdf_realQuantile_ge {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : SourceSpace}
    (hα0 : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1) :
    (α : ℝ) ≤ ProbabilityTheory.cdf μ (realQuantile μ α) := by
  let S : Set ℝ := realQuantileLevelSet μ α
  have hS_nonempty : S.Nonempty := realQuantileLevelSet_nonempty hα0 hα1
  have hS_bdd : BddBelow S := realQuantileLevelSet_bddBelow hα0
  obtain ⟨u, _, hu_tendsto, hu_mem⟩ :=
    exists_seq_tendsto_sInf hS_nonempty hS_bdd
  have hu_ge :
      ∀ n, realQuantile μ α ≤ u n := by
    intro n
    exact csInf_le hS_bdd (hu_mem n)
  have hu_within : Tendsto u atTop (𝓝[Set.Ici (realQuantile μ α)] (realQuantile μ α)) := by
    refine tendsto_nhdsWithin_iff.mpr ?_
    refine ⟨hu_tendsto, Filter.Eventually.of_forall ?_⟩
    intro n
    exact hu_ge n
  have hcont :
      Tendsto (ProbabilityTheory.cdf μ)
        (𝓝[Set.Ici (realQuantile μ α)] (realQuantile μ α))
        (𝓝 (ProbabilityTheory.cdf μ (realQuantile μ α))) := by
    exact ((ProbabilityTheory.cdf μ).right_continuous (realQuantile μ α)).tendsto
  have hlim :
      Tendsto (fun n => ProbabilityTheory.cdf μ (u n)) atTop
        (𝓝 (ProbabilityTheory.cdf μ (realQuantile μ α))) :=
    hcont.comp hu_within
  have hmem :
      ∀ n, ProbabilityTheory.cdf μ (u n) ∈ Set.Ici (α : ℝ) := by
    intro n
    exact hu_mem n
  exact isClosed_Ici.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)

lemma realQuantile_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : SourceSpace}
    (hα0 : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1) {x : ℝ} :
    realQuantile μ α ≤ x ↔ (α : ℝ) ≤ ProbabilityTheory.cdf μ x := by
  constructor
  · intro hx
    exact (cdf_realQuantile_ge hα0 hα1).trans <| (ProbabilityTheory.monotone_cdf μ) hx
  · intro hx
    exact realQuantile_le_of_cdf_le hα0 hα1 hx

/--
Patch the CDF-based quantile at the null endpoints `0` and `1`, where the set-theoretic
right-quantile on `ℝ` does not represent the extended-valued inverse CDF.
-/
def safeRealQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (α : SourceSpace) : ℝ :=
  if hα : 0 < (α : ℝ) ∧ (α : ℝ) < 1 then realQuantile μ α else 0

lemma safeRealQuantile_of_mem_Ioo {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : SourceSpace}
    (hα0 : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1) :
    safeRealQuantile μ α = realQuantile μ α := by
  simp [safeRealQuantile, hα0, hα1]

lemma safeRealQuantile_of_left_endpoint {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {α : SourceSpace} (hα : (α : ℝ) ≤ 0) :
    safeRealQuantile μ α = 0 := by
  simp [safeRealQuantile, not_lt.mpr hα]

lemma safeRealQuantile_of_right_endpoint {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {α : SourceSpace} (hα : 1 ≤ (α : ℝ)) :
    safeRealQuantile μ α = 0 := by
  simp [safeRealQuantile, not_lt.mpr hα]

lemma safeRealQuantile_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : SourceSpace}
    (hα0 : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1) {x : ℝ} :
    safeRealQuantile μ α ≤ x ↔ (α : ℝ) ≤ ProbabilityTheory.cdf μ x := by
  rw [safeRealQuantile_of_mem_Ioo hα0 hα1]
  exact realQuantile_le_iff hα0 hα1

def endpointSet : Set SourceSpace := {(0 : SourceSpace), (1 : SourceSpace)}

lemma mem_endpointSet_iff {α : SourceSpace} :
    α ∈ endpointSet ↔ (α : ℝ) = 0 ∨ (α : ℝ) = 1 := by
  rw [endpointSet]
  constructor
  · intro hα
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with hα | hα
    · left
      exact congrArg (fun z : SourceSpace => (z : ℝ)) hα
    · right
      exact congrArg (fun z : SourceSpace => (z : ℝ)) hα
  · intro hα
    rcases hα with hα | hα
    · left
      exact Subtype.ext hα
    · right
      exact Subtype.ext hα

lemma not_mem_endpointSet_iff {α : SourceSpace} :
    α ∉ endpointSet ↔ 0 < (α : ℝ) ∧ (α : ℝ) < 1 := by
  constructor
  · intro hα
    have hα0 : (α : ℝ) ≠ 0 := by
      intro hEq
      exact hα ((mem_endpointSet_iff).2 (Or.inl hEq))
    have hα1 : (α : ℝ) ≠ 1 := by
      intro hEq
      exact hα ((mem_endpointSet_iff).2 (Or.inr hEq))
    constructor
    · have hαnonneg : 0 ≤ (α : ℝ) := α.2.1
      exact lt_of_le_of_ne hαnonneg hα0.symm
    · have hαle : (α : ℝ) ≤ 1 := α.2.2
      exact lt_of_le_of_ne hαle hα1
  · rintro ⟨hα0, hα1⟩ hmem
    rcases (mem_endpointSet_iff).1 hmem with hEq | hEq
    · exact hα0.ne' hEq
    · exact hα1.ne hEq

lemma safeRealQuantile_sublevel_eq_prefix_diff_endpoints_union_patch
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (x : ℝ) :
    {α : SourceSpace | safeRealQuantile μ α ≤ x} =
      ({α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} \ endpointSet) ∪
        if 0 ≤ x then endpointSet else ∅ := by
  ext α
  by_cases hmem : α ∈ endpointSet
  · rcases (mem_endpointSet_iff).1 hmem with hEq0 | hEq1
    · have hα0 : α = (0 : SourceSpace) := Subtype.ext hEq0
      subst hα0
      by_cases hx : 0 ≤ x <;> simp [safeRealQuantile, endpointSet, hx]
    · have hα1 : α = (1 : SourceSpace) := Subtype.ext hEq1
      subst hα1
      by_cases hx : 0 ≤ x <;> simp [safeRealQuantile, endpointSet, hx]
  · have hα : 0 < (α : ℝ) ∧ (α : ℝ) < 1 := (not_mem_endpointSet_iff).1 hmem
    have hiff := safeRealQuantile_le_iff (μ := μ) hα.1 hα.2 (x := x)
    by_cases hx : 0 ≤ x
    · simp [hmem, hiff, hx]
    · simp [hmem, hiff, hx]

lemma measurableSet_safeRealQuantile_sublevel {μ : Measure ℝ} [IsProbabilityMeasure μ] (x : ℝ) :
    MeasurableSet {α : SourceSpace | safeRealQuantile μ α ≤ x} := by
  let r : SourceSpace :=
    ⟨ProbabilityTheory.cdf μ x, ProbabilityTheory.cdf_nonneg μ x, ProbabilityTheory.cdf_le_one μ x⟩
  have h_prefix :
      MeasurableSet {α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} := by
    have hset :
        {α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} = Set.Iic r := by
      ext α
      constructor <;> intro h <;> exact h
    rw [hset]
    exact measurableSet_Iic
  have h_endpoints : MeasurableSet endpointSet := by
    classical
    simp [endpointSet]
  rw [safeRealQuantile_sublevel_eq_prefix_diff_endpoints_union_patch]
  by_cases hx : 0 ≤ x
  · simp [h_prefix, h_endpoints, hx]
  · simp [h_prefix, h_endpoints, hx]

@[fun_prop]
lemma measurable_safeRealQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (safeRealQuantile μ) := by
  refine measurable_of_Iic fun x => ?_
  simpa [Set.preimage] using measurableSet_safeRealQuantile_sublevel (μ := μ) x

lemma measure_endpointSet_zero :
    (volume : Measure SourceSpace) endpointSet = 0 := by
  classical
  exact (by simp [endpointSet] : endpointSet.Finite).measure_zero _

lemma measure_safeRealQuantile_sublevel_eq_prefix {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (x : ℝ) :
    (volume : Measure SourceSpace) {α : SourceSpace | safeRealQuantile μ α ≤ x} =
      (volume : Measure SourceSpace) {α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} := by
  have hzero : (volume : Measure SourceSpace) endpointSet = 0 := measure_endpointSet_zero
  have h_prefix :
      MeasurableSet {α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} := by
    let r : SourceSpace :=
      ⟨ProbabilityTheory.cdf μ x, ProbabilityTheory.cdf_nonneg μ x, ProbabilityTheory.cdf_le_one μ x⟩
    have hset :
        {α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} = Set.Iic r := by
      ext α
      constructor <;> intro h <;> exact h
    rw [hset]
    exact measurableSet_Iic
  have h_endpoints : MeasurableSet endpointSet := by
    classical
    simp [endpointSet]
  rw [safeRealQuantile_sublevel_eq_prefix_diff_endpoints_union_patch]
  by_cases hx : 0 ≤ x
  · have hdisj :
        Disjoint ({α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} \ endpointSet) endpointSet := by
      refine Set.disjoint_iff_inter_eq_empty.2 ?_
      ext α
      simp
    rw [if_pos hx, measure_union hdisj h_endpoints]
    simp [measure_diff_null, hzero]
  · rw [if_neg hx, Set.union_empty, measure_diff_null hzero]

lemma measure_prefix_eq_cdf {μ : Measure ℝ} [IsProbabilityMeasure μ] (x : ℝ) :
    (volume : Measure SourceSpace) {α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} =
      ENNReal.ofReal (ProbabilityTheory.cdf μ x) := by
  let r : SourceSpace :=
    ⟨ProbabilityTheory.cdf μ x, ProbabilityTheory.cdf_nonneg μ x, ProbabilityTheory.cdf_le_one μ x⟩
  have hset :
      {α : SourceSpace | (α : ℝ) ≤ ProbabilityTheory.cdf μ x} = Set.Iic r := by
    ext α
    constructor <;> intro h <;> exact h
  rw [hset, unitInterval.volume_Iic]

lemma map_safeRealQuantile_apply_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ] (x : ℝ) :
    Measure.map (safeRealQuantile μ) (volume : Measure SourceSpace) (Set.Iic x) =
      ENNReal.ofReal (ProbabilityTheory.cdf μ x) := by
  rw [Measure.map_apply (measurable_safeRealQuantile μ) measurableSet_Iic]
  change (volume : Measure SourceSpace) {α : SourceSpace | safeRealQuantile μ α ≤ x} =
    ENNReal.ofReal (ProbabilityTheory.cdf μ x)
  rw [measure_safeRealQuantile_sublevel_eq_prefix, measure_prefix_eq_cdf]

theorem map_safeRealQuantile_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    Measure.map (safeRealQuantile μ) (volume : Measure SourceSpace) = μ := by
  let ν : Measure ℝ := Measure.map (safeRealQuantile μ) (volume : Measure SourceSpace)
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_safeRealQuantile μ).aemeasurable
  apply Measure.eq_of_cdf
  ext x
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, map_safeRealQuantile_apply_Iic]
  simp [ProbabilityTheory.cdf_nonneg μ x]

/-- The standard Gaussian law used in the literal Attempt 2 reduction. -/
def standardGaussian : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : NNReal)

instance standardGaussian_isProbability : IsProbabilityMeasure standardGaussian := by
  unfold standardGaussian
  infer_instance

/-- The `[0,1] → N(0,1)` Gaussianizing quantile feature. -/
def gaussianFeature : SourceSpace → ℝ :=
  safeRealQuantile standardGaussian

@[fun_prop]
lemma measurable_gaussianFeature : Measurable gaussianFeature := by
  simpa [gaussianFeature] using measurable_safeRealQuantile standardGaussian

lemma map_gaussianFeature_eq_standardGaussian :
    Measure.map gaussianFeature (volume : Measure SourceSpace) = standardGaussian := by
  simpa [gaussianFeature, standardGaussian] using
    (map_safeRealQuantile_eq (μ := standardGaussian))

lemma integrable_gaussianFeature_sq :
    Integrable (fun x : SourceSpace => gaussianFeature x ^ 2) volume := by
  have hgauss :
      Integrable (fun t : ℝ => t ^ 2) standardGaussian := by
    simpa [standardGaussian] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := (1 : NNReal)) (2 : NNReal)).integrable_sq
  have hgauss_map :
      Integrable (fun t : ℝ => t ^ 2) (Measure.map gaussianFeature (volume : Measure SourceSpace)) := by
    simpa [map_gaussianFeature_eq_standardGaussian] using hgauss
  simpa [Function.comp, gaussianFeature] using
    hgauss_map.comp_measurable measurable_gaussianFeature

/-- A sample of real points indexed like the empirical samples in the paper. -/
abbrev RealSample (n : ℕ) := Fin (sampleCount n) → ℝ

def sortedRealSample {n : ℕ} (x : RealSample n) : Fin (sampleCount n) → ℝ :=
  x ∘ Tuple.sort x

def empiricalRealW2Sq (n : ℕ) (x y : RealSample n) : ℝ :=
  (1 / sampleCountReal n) *
    ∑ i : Fin (sampleCount n), (sortedRealSample x i - sortedRealSample y i) ^ 2

def empiricalRealW2 (n : ℕ) (x y : RealSample n) : ℝ :=
  Real.sqrt (empiricalRealW2Sq n x y)

lemma sum_weighted_abs_le_l2Norm_mul_l2Norm {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) :
    ∑ i, w i * |z i| ≤
      Real.sqrt (∑ i, (w i) ^ 2) * Real.sqrt (∑ i, (z i) ^ 2) := by
  simpa [abs_sq] using Real.sum_mul_le_sqrt_mul_sqrt (s := Finset.univ) w (fun i => |z i|)

lemma sum_weighted_abs_le_l2Norm {ι : Type*} [Fintype ι]
    {w z : ι → ℝ} (hw : ∑ i, (w i) ^ 2 ≤ 1) :
    ∑ i, w i * |z i| ≤ Real.sqrt (∑ i, (z i) ^ 2) := by
  calc
    ∑ i, w i * |z i| ≤
        Real.sqrt (∑ i, (w i) ^ 2) * Real.sqrt (∑ i, (z i) ^ 2) :=
      sum_weighted_abs_le_l2Norm_mul_l2Norm w z
    _ ≤ 1 * Real.sqrt (∑ i, (z i) ^ 2) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      exact Real.sqrt_le_iff.mpr ⟨by positivity, by simpa using hw⟩
    _ = Real.sqrt (∑ i, (z i) ^ 2) := by ring

lemma normalized_weights_sq_sum_eq_one {ι : Type*} [Fintype ι]
    (m : ι → ℝ)
    (hpos : 0 < Real.sqrt (∑ i, (m i) ^ 2)) :
    ∑ i, (m i / Real.sqrt (∑ i, (m i) ^ 2)) ^ 2 = 1 := by
  let s : ℝ := Real.sqrt (∑ i, (m i) ^ 2)
  have hs : s ≠ 0 := by
    exact hpos.ne'
  calc
    ∑ i, (m i / s) ^ 2 = (∑ i, (m i) ^ 2) / s ^ 2 := by
      simp [s, div_pow, Finset.sum_div]
    _ = (∑ i, (m i) ^ 2) / (∑ i, (m i) ^ 2) := by
      rw [show s ^ 2 = ∑ i, (m i) ^ 2 by
        unfold s
        rw [Real.sq_sqrt]
        positivity]
    _ = 1 := by
      have hsum : ∑ i, (m i) ^ 2 ≠ 0 := by
        intro hsum0
        apply hs
        unfold s
        rw [hsum0, Real.sqrt_zero]
      field_simp [hsum]

lemma normalized_weights_dot_self {ι : Type*} [Fintype ι]
    (m : ι → ℝ)
    (hpos : 0 < Real.sqrt (∑ i, (m i) ^ 2)) :
    ∑ i, (m i / Real.sqrt (∑ i, (m i) ^ 2)) * m i =
      Real.sqrt (∑ i, (m i) ^ 2) := by
  let s : ℝ := Real.sqrt (∑ i, (m i) ^ 2)
  have hs : s ≠ 0 := by
    exact hpos.ne'
  calc
    ∑ i, (m i / s) * m i = ∑ i, (m i) ^ 2 / s := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      field_simp [hs]
    _ = (∑ i, (m i) ^ 2) / s := by
      rw [Finset.sum_div]
    _ = s ^ 2 / s := by
      congr 1
      unfold s
      rw [Real.sq_sqrt]
      positivity
    _ = s := by
      field_simp [hs]
    _ = Real.sqrt (∑ i, (m i) ^ 2) := rfl

lemma sum_sq_sortedRealSample_eq_sum_sq {n : ℕ} (x : RealSample n) :
    ∑ i : Fin (sampleCount n), (sortedRealSample x i) ^ 2 =
      ∑ i : Fin (sampleCount n), (x i) ^ 2 := by
  unfold sortedRealSample
  refine Fintype.sum_equiv (Tuple.sort x) _ _ ?_
  intro i
  simp [Function.comp]

lemma sq_sortedRealSample_le_sum_sq {n : ℕ} (x : RealSample n) (i : Fin (sampleCount n)) :
    (sortedRealSample x i) ^ 2 ≤ ∑ j : Fin (sampleCount n), (x j) ^ 2 := by
  calc
    (sortedRealSample x i) ^ 2 ≤
        ∑ j : Fin (sampleCount n), (sortedRealSample x j) ^ 2 := by
          exact Finset.single_le_sum (fun j _ => sq_nonneg _) (by simp)
    _ = ∑ j : Fin (sampleCount n), (x j) ^ 2 := sum_sq_sortedRealSample_eq_sum_sq x

def gaussianizedSample {n : ℕ} (x : Sample n) : RealSample n :=
  fun i => gaussianFeature (x i)

@[fun_prop]
lemma measurable_gaussianizedSample (n : ℕ) : Measurable (gaussianizedSample (n := n)) := by
  unfold gaussianizedSample
  fun_prop

lemma sortedFeature_gaussianFeature_eq_sortedRealSample_gaussianized {n : ℕ} (x : Sample n) :
    sortedFeature gaussianFeature x = sortedRealSample (gaussianizedSample x) := by
  rfl

lemma empiricalRankOneEKQD2Sq_gaussianFeature_eq_empiricalRealW2Sq
    (n : ℕ) (x y : Sample n) :
    empiricalRankOneEKQD2Sq gaussianFeature n x y =
      empiricalRealW2Sq n (gaussianizedSample x) (gaussianizedSample y) := by
  rfl

lemma empiricalRankOneEKQD2_gaussianFeature_eq_empiricalRealW2
    (n : ℕ) (x y : Sample n) :
    empiricalRankOneEKQD2 gaussianFeature n x y =
      empiricalRealW2 n (gaussianizedSample x) (gaussianizedSample y) := by
  unfold empiricalRankOneEKQD2 empiricalRealW2
  rw [empiricalRankOneEKQD2Sq_gaussianFeature_eq_empiricalRealW2Sq]

def gaussianSampleMeasure (n : ℕ) : Measure (RealSample n) :=
  Measure.pi fun _ => standardGaussian

instance gaussianSampleMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (gaussianSampleMeasure n) := by
  unfold gaussianSampleMeasure
  infer_instance

lemma integrable_square_eval_gaussianSampleMeasure (n : ℕ) (i : Fin (sampleCount n)) :
    Integrable (fun x : RealSample n => x i ^ 2) (gaussianSampleMeasure n) := by
  have hgauss :
      Integrable (fun t : ℝ => t ^ 2) standardGaussian := by
    simpa [standardGaussian] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := (1 : NNReal)) (2 : NNReal)).integrable_sq
  have hmap :
      Measure.map (Function.eval i) (gaussianSampleMeasure n) = standardGaussian := by
    simpa [gaussianSampleMeasure] using
      (measurePreserving_eval (μ := fun _ : Fin (sampleCount n) => standardGaussian) i).map_eq
  have hmapInt :
      Integrable (fun t : ℝ => t ^ 2) (Measure.map (Function.eval i) (gaussianSampleMeasure n)) := by
    simpa [hmap] using hgauss
  simpa [Function.comp] using hmapInt.comp_measurable (by fun_prop)

lemma integrable_sum_sq_gaussianSampleMeasure (n : ℕ) :
    Integrable (fun x : RealSample n => ∑ i : Fin (sampleCount n), (x i) ^ 2)
      (gaussianSampleMeasure n) := by
  refine integrable_finset_sum (μ := gaussianSampleMeasure n) (s := Finset.univ)
      (f := fun i (x : RealSample n) => x i ^ 2) ?_
  intro i hi
  exact integrable_square_eval_gaussianSampleMeasure n i

lemma sampleMeasure_map_gaussianized_eq_gaussianSampleMeasure (n : ℕ) :
    Measure.map (gaussianizedSample (n := n)) (sampleMeasure n) =
      gaussianSampleMeasure n := by
  unfold gaussianizedSample sampleMeasure gaussianSampleMeasure
  calc
    Measure.map (fun x i => gaussianFeature (x i))
        (Measure.pi fun _ : Fin (sampleCount n) => (volume : Measure SourceSpace))
        =
        Measure.pi
          (fun _ : Fin (sampleCount n) =>
            Measure.map gaussianFeature (volume : Measure SourceSpace)) := by
          simpa [gaussianFeature, standardGaussian] using
            (Measure.pi_map_pi
              (μ := fun _ : Fin (sampleCount n) => (volume : Measure SourceSpace))
              (f := fun _ => gaussianFeature)
              (hf := fun _ => measurable_gaussianFeature.aemeasurable))
    _ = Measure.pi (fun _ : Fin (sampleCount n) => standardGaussian) := by
          simp [map_gaussianFeature_eq_standardGaussian]

def gaussianizedPairSample (n : ℕ) (z : Sample n × Sample n) : RealSample n × RealSample n :=
  (gaussianizedSample z.1, gaussianizedSample z.2)

def gaussianPairSampleMeasure (n : ℕ) : Measure (RealSample n × RealSample n) :=
  (gaussianSampleMeasure n).prod (gaussianSampleMeasure n)

instance gaussianPairSampleMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (gaussianPairSampleMeasure n) := by
  unfold gaussianPairSampleMeasure
  infer_instance

lemma pairMeasure_map_gaussianizedPair_eq_gaussianPairSampleMeasure (n : ℕ) :
    Measure.map (gaussianizedPairSample n) (pairMeasure n) = gaussianPairSampleMeasure n := by
  unfold gaussianizedPairSample pairMeasure gaussianPairSampleMeasure
  change
    Measure.map
        (Prod.map (gaussianizedSample (n := n)) (gaussianizedSample (n := n)))
        ((sampleMeasure n).prod (sampleMeasure n)) =
      (gaussianSampleMeasure n).prod (gaussianSampleMeasure n)
  rw [← Measure.map_prod_map _ _ (measurable_gaussianizedSample n) (measurable_gaussianizedSample n)]
  simp [sampleMeasure_map_gaussianized_eq_gaussianSampleMeasure]

/--
The exact `d = 1`, `p = 2` data needed for the printed conjecture's one-dimensional
specialization.
-/
structure OneDimPrintedConjecture152Data where
  P : Measure SourceSpace
  Q : Measure SourceSpace
  instProbP : IsProbabilityMeasure P
  instProbQ : IsProbabilityMeasure Q
  ν : Measure SourceSpace
  νDensity : SourceSpace → ℝ
  ν_hasDensity :
    ν = (volume : Measure SourceSpace).withDensity (fun α => ENNReal.ofReal (νDensity α))
  PDensity : SourceSpace → ℝ
  P_hasDensity :
    P = (volume : Measure SourceSpace).withDensity (fun x => ENNReal.ofReal (PDensity x))
  QDensity : SourceSpace → ℝ
  Q_hasDensity :
    Q = (volume : Measure SourceSpace).withDensity (fun x => ENNReal.ofReal (QDensity x))
  H : Type
  instNormedAddCommGroupH : NormedAddCommGroup H
  instInnerProductSpaceH : InnerProductSpace ℝ H
  instMeasurableSpaceH : MeasurableSpace H
  k : SourceSpace → SourceSpace → ℝ
  eval : H → SourceSpace → ℝ
  measurable_eval : ∀ u : H, Measurable (eval u)
  kernelSection : SourceSpace → H
  reproducing : ∀ u x, eval u x = inner ℝ u (kernelSection x)
  kernel_eq_inner_sections : ∀ x y, k x y = inner ℝ (kernelSection x) (kernelSection y)
  γ : Measure {u : H // ‖u‖ = 1}
  instProbGamma : IsProbabilityMeasure γ
  sampledDirections : ∀ l, Fin (sampleCount l) → {u : H // ‖u‖ = 1}

instance (data : OneDimPrintedConjecture152Data) : IsProbabilityMeasure data.P := data.instProbP

instance (data : OneDimPrintedConjecture152Data) : IsProbabilityMeasure data.Q := data.instProbQ

instance (data : OneDimPrintedConjecture152Data) : NormedAddCommGroup data.H :=
  data.instNormedAddCommGroupH

instance (data : OneDimPrintedConjecture152Data) : InnerProductSpace ℝ data.H :=
  data.instInnerProductSpaceH

instance (data : OneDimPrintedConjecture152Data) : MeasurableSpace data.H :=
  data.instMeasurableSpaceH

instance (data : OneDimPrintedConjecture152Data) : IsProbabilityMeasure data.γ :=
  data.instProbGamma

namespace OneDimPrintedConjecture152Data

abbrev BaseData := _root_.QuasimodularSturm.AttemptTwo.OneDimPrintedConjecture152Data

abbrev Sphere (data : BaseData) := {u : data.H // ‖u‖ = 1}
abbrev Sample (_data : BaseData) (n : ℕ) := Fin (sampleCount n) → SourceSpace

def projectedP (data : BaseData) (u : Sphere data) : Measure ℝ :=
  data.P.map (data.eval u.1)

def projectedQ (data : BaseData) (u : Sphere data) : Measure ℝ :=
  data.Q.map (data.eval u.1)

instance projectedP_isProbability (data : BaseData) (u : Sphere data) :
    IsProbabilityMeasure (projectedP data u) :=
  Measure.isProbabilityMeasure_map (data.measurable_eval u.1).aemeasurable

instance projectedQ_isProbability (data : BaseData) (u : Sphere data) :
    IsProbabilityMeasure (projectedQ data u) :=
  Measure.isProbabilityMeasure_map (data.measurable_eval u.1).aemeasurable

/--
The paper's directional quantile embedding
`ρ^{α,u}_P = ρ^α_{u#P} u`
specialized to the one-dimensional `d = 1`, `p = 2` setting.
-/
def rhoP (data : BaseData) (u : Sphere data) (α : SourceSpace) : data.H :=
  (realQuantile (projectedP data u) α) • u.1

/--
The paper's directional quantile embedding
`ρ^{α,u}_Q = ρ^α_{u#Q} u`
specialized to the one-dimensional `d = 1`, `p = 2` setting.
-/
def rhoQ (data : BaseData) (u : Sphere data) (α : SourceSpace) : data.H :=
  (realQuantile (projectedQ data u) α) • u.1

lemma rho_sub_sq_norm (data : BaseData) (u : Sphere data) (α : SourceSpace) :
    ‖rhoP data u α - rhoQ data u α‖ ^ 2 =
      (realQuantile (projectedP data u) α - realQuantile (projectedQ data u) α) ^ 2 := by
  unfold rhoP rhoQ
  have hsub :
      realQuantile (projectedP data u) α • u.1 -
          realQuantile (projectedQ data u) α • u.1 =
        (realQuantile (projectedP data u) α - realQuantile (projectedQ data u) α) • u.1 := by
    simp [sub_eq_add_neg, add_smul]
  rw [hsub, norm_smul, u.2, mul_one, Real.norm_eq_abs, sq_abs]

def tau2Sq (data : BaseData) (u : Sphere data) : ℝ :=
  (∫⁻ α : SourceSpace,
      ENNReal.ofReal
        (‖rhoP data u α - rhoQ data u α‖ ^ 2)
      ∂ data.ν).toReal

lemma tau2Sq_eq_quantile_gap_formula (data : BaseData) (u : Sphere data) :
    tau2Sq data u =
      (∫⁻ α : SourceSpace,
          ENNReal.ofReal
            ((realQuantile (projectedP data u) α - realQuantile (projectedQ data u) α) ^ 2)
        ∂ data.ν).toReal := by
  unfold tau2Sq
  simp_rw [rho_sub_sq_norm]

def eKQD2Sq (data : BaseData) : ℝ :=
  (∫⁻ u, ENNReal.ofReal (tau2Sq data u) ∂ data.γ).toReal

def eKQD2 (data : BaseData) : ℝ :=
  Real.sqrt (eKQD2Sq data)

def sortedProjection {n : ℕ} (data : BaseData)
    (u : Sphere data) (x : Sample data n) :
    Fin (sampleCount n) → ℝ :=
  (fun i => data.eval u.1 (x i)) ∘ Tuple.sort (fun i => data.eval u.1 (x i))

def empiricalEqFiveEKQD2Sq (data : BaseData)
    (n l : ℕ) (z : Sample data n × Sample data n) : ℝ :=
  (1 / (sampleCountReal l * sampleCountReal n)) *
    ∑ i : Fin (sampleCount l),
      ∑ j : Fin (sampleCount n),
        ((sortedProjection data (data.sampledDirections l i) z.1 j -
            sortedProjection data (data.sampledDirections l i) z.2 j) ^ 2) *
          data.νDensity (quantileGridPoint n j)

def empiricalEqFiveEKQD2 (data : BaseData)
    (n l : ℕ) (z : Sample data n × Sample data n) : ℝ :=
  Real.sqrt (empiricalEqFiveEKQD2Sq data n l z)

def pairSampleMeasure (data : BaseData) (n : ℕ) :
    Measure (Sample data n × Sample data n) :=
  (Measure.pi fun _ => data.P).prod (Measure.pi fun _ => data.Q)

def absoluteError (data : BaseData)
    (n l : ℕ) (z : Sample data n × Sample data n) : ℝ :=
  |empiricalEqFiveEKQD2 data n l z - eKQD2 data|

def expectedAbsoluteError (data : BaseData) (n l : ℕ) : ℝ :=
  (∫⁻ z, ENNReal.ofReal (absoluteError data n l z) ∂ pairSampleMeasure data n).toReal

def empiricalDirectionMeasure (data : BaseData) (l : ℕ) :
    Measure (Sphere data) :=
  (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (sampleCount l)))).map
    (data.sampledDirections l)

end OneDimPrintedConjecture152Data

/-- The exact one-dimensional `p = 2` hypotheses appearing in the printed conjecture. -/
def PrintedConjecture152Hypotheses (data : OneDimPrintedConjecture152Data) : Prop :=
  (∃ cP : ℝ, 0 < cP ∧ ∀ x, cP ≤ data.PDensity x) ∧
  (∃ cQ : ℝ, 0 < cQ ∧ ∀ x, cQ ≤ data.QDensity x) ∧
  Integrable (fun x => data.k x x) data.P ∧
  Integrable (fun y => data.k y y) data.Q

/--
The `d = 1`, `p = 2` specialization of the printed conjecture. Since the paper claims the
rate for all integers `p > 1` and all ambient dimensions, falsity of this specialization already
refutes the printed conjecture.
-/
def PrintedConjecture152_d1_p2 : Prop :=
  ∀ data : OneDimPrintedConjecture152Data, PrintedConjecture152Hypotheses data →
    ∃ C > 0, ∀ n l,
      (∫⁻ z, ENNReal.ofReal (OneDimPrintedConjecture152Data.absoluteError data n l z) ∂
          OneDimPrintedConjecture152Data.pairSampleMeasure data n) ≠ ⊤ ∧
      OneDimPrintedConjecture152Data.expectedAbsoluteError data n l ≤
        C * (rootRate l + rootRate n)

def tailCounterexampleData : OneDimPrintedConjecture152Data where
  P := volume
  Q := volume
  instProbP := by infer_instance
  instProbQ := by infer_instance
  ν := volume
  νDensity := fun _ => 1
  ν_hasDensity := by
    simp
  PDensity := fun _ => 1
  P_hasDensity := by
    simp
  QDensity := fun _ => 1
  Q_hasDensity := by
    simp
  H := ℝ
  instNormedAddCommGroupH := inferInstance
  instInnerProductSpaceH := inferInstance
  instMeasurableSpaceH := borel ℝ
  k := tailKernel
  eval := rankOneEval
  measurable_eval := rankOneEval_measurable
  kernelSection := tailKernelSection
  reproducing := rankOneEval_reproducing
  kernel_eq_inner_sections := tailKernel_eq_inner_sections
  γ := tailGamma
  instProbGamma := by infer_instance
  sampledDirections := tailSampledDirections

lemma tailCounterexampleData_hypotheses :
    PrintedConjecture152Hypotheses tailCounterexampleData := by
  constructor
  · refine ⟨1, by norm_num, fun _ => le_rfl⟩
  constructor
  · refine ⟨1, by norm_num, fun _ => le_rfl⟩
  constructor
  · simpa [tailCounterexampleData] using tailKernel_diagonal_moment_finite
  · simpa [tailCounterexampleData] using tailKernel_diagonal_moment_finite

lemma tailCounterexampleData_nu_has_density_one :
    tailCounterexampleData.ν =
      (volume : Measure SourceSpace).withDensity (fun _ => (1 : ENNReal)) := by
  simp [tailCounterexampleData]

lemma tailCounterexampleData_P_has_density_one :
    tailCounterexampleData.P =
      (volume : Measure SourceSpace).withDensity (fun _ => (1 : ENNReal)) := by
  simp [tailCounterexampleData]

lemma tailCounterexampleData_Q_has_density_one :
    tailCounterexampleData.Q =
      (volume : Measure SourceSpace).withDensity (fun _ => (1 : ENNReal)) := by
  simp [tailCounterexampleData]

lemma tailCounterexampleData_reproducing
    (u : tailCounterexampleData.H) (x : SourceSpace) :
    tailCounterexampleData.eval u x = inner ℝ u (tailCounterexampleData.kernelSection x) := by
  simpa using tailCounterexampleData.reproducing u x

lemma tailCounterexampleData_kernel_eq_inner_sections
    (x y : SourceSpace) :
    tailCounterexampleData.k x y =
      inner ℝ (tailCounterexampleData.kernelSection x)
        (tailCounterexampleData.kernelSection y) := by
  simpa using tailCounterexampleData.kernel_eq_inner_sections x y

lemma tailCounterexampleData_empiricalDirectionMeasure_eq_gamma (l : ℕ) :
    OneDimPrintedConjecture152Data.empiricalDirectionMeasure tailCounterexampleData l =
      tailCounterexampleData.γ := by
  let μ : Measure (Fin (sampleCount l)) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin (sampleCount l)))
  have hμ_pos :
      μ (positiveDirectionIndices l) = (2 : ENNReal)⁻¹ := by
    simpa [μ] using uniformOn_positiveDirectionIndices l
  have hμ_neg :
      μ ((positiveDirectionIndices l)ᶜ) = (2 : ENNReal)⁻¹ := by
    simpa [μ] using uniformOn_positiveDirectionIndices_compl l
  have hμ_univ : μ Set.univ = 1 := by
    haveI : Nonempty (Fin (sampleCount l)) := by
      refine ⟨0, by
        change 0 < 2 * (l + 1)
        omega⟩
    simpa [μ] using
      (ProbabilityTheory.uniformOn_of_univ
        (s := (Set.univ : Set (Fin (sampleCount l))))
        Set.finite_univ Set.univ_nonempty)
  have hmap : Measure.map (tailSampledDirections l) μ = tailGamma := by
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs]
    by_cases htail : tailDirection ∈ s
    · by_cases hneg : negTailDirection ∈ s
      · have hpre : tailSampledDirections l ⁻¹' s = Set.univ := by
          ext i
          by_cases hi : i.1 < halfSampleCount l
          · simp [tailSampledDirections, hi, htail]
          · simp [tailSampledDirections, hi, hneg]
        rw [hpre]
        rw [hμ_univ, tailGamma]
        simp [htail, hneg, ENNReal.inv_two_add_inv_two]
      · have hpre : tailSampledDirections l ⁻¹' s = positiveDirectionIndices l := by
          ext i
          by_cases hi : i.1 < halfSampleCount l
          · simp [tailSampledDirections, positiveDirectionIndices, hi, htail]
          · simp [tailSampledDirections, positiveDirectionIndices, hi, hneg]
        rw [hpre, hμ_pos]
        simp [tailGamma, htail, hneg]
    · by_cases hneg : negTailDirection ∈ s
      · have hpre : tailSampledDirections l ⁻¹' s = (positiveDirectionIndices l)ᶜ := by
          ext i
          by_cases hi : i.1 < halfSampleCount l
          · simp [tailSampledDirections, positiveDirectionIndices, hi, htail]
          · simp [tailSampledDirections, positiveDirectionIndices, hi, hneg]
        rw [hpre, hμ_neg]
        simp [tailGamma, htail, hneg]
      · have hpre : tailSampledDirections l ⁻¹' s = ∅ := by
          ext i
          by_cases hi : i.1 < halfSampleCount l
          · simp [tailSampledDirections, hi, htail]
          · simp [tailSampledDirections, hi, hneg]
        rw [hpre]
        simp [μ, tailGamma, htail, hneg]
  calc
    OneDimPrintedConjecture152Data.empiricalDirectionMeasure tailCounterexampleData l
        = Measure.map (tailSampledDirections l) μ := by
            simp [OneDimPrintedConjecture152Data.empiricalDirectionMeasure,
              tailCounterexampleData, μ]
    _ = tailGamma := hmap
    _ = tailCounterexampleData.γ := by
          simp [tailCounterexampleData]

theorem tailCounterexampleData_sideConditions :
    tailCounterexampleData.ν =
        (volume : Measure SourceSpace).withDensity (fun _ => (1 : ENNReal)) ∧
      tailCounterexampleData.P =
        (volume : Measure SourceSpace).withDensity (fun _ => (1 : ENNReal)) ∧
      tailCounterexampleData.Q =
        (volume : Measure SourceSpace).withDensity (fun _ => (1 : ENNReal)) ∧
      (∀ u x, tailCounterexampleData.eval u x =
          inner ℝ u (tailCounterexampleData.kernelSection x)) ∧
      (∀ x y, tailCounterexampleData.k x y =
          inner ℝ (tailCounterexampleData.kernelSection x)
            (tailCounterexampleData.kernelSection y)) ∧
      (∀ l,
        OneDimPrintedConjecture152Data.empiricalDirectionMeasure tailCounterexampleData l =
          tailCounterexampleData.γ) := by
  refine ⟨tailCounterexampleData_nu_has_density_one, tailCounterexampleData_P_has_density_one,
    tailCounterexampleData_Q_has_density_one, ?_, ?_, ?_⟩
  · intro u x
    exact tailCounterexampleData_reproducing u x
  · intro x y
    exact tailCounterexampleData_kernel_eq_inner_sections x y
  · intro l
    exact tailCounterexampleData_empiricalDirectionMeasure_eq_gamma l

def gaussianKernel (x y : SourceSpace) : ℝ :=
  gaussianFeature x * gaussianFeature y

def gaussianRankOneEval (u : ℝ) (x : SourceSpace) : ℝ :=
  u * gaussianFeature x

def gaussianKernelSection (x : SourceSpace) : ℝ :=
  gaussianFeature x

lemma gaussianRankOneEval_measurable (u : ℝ) : Measurable (gaussianRankOneEval u) := by
  unfold gaussianRankOneEval
  exact measurable_const.mul measurable_gaussianFeature

lemma gaussianRankOneEval_reproducing (u : ℝ) (x : SourceSpace) :
    gaussianRankOneEval u x = inner ℝ u (gaussianKernelSection x) := by
  simp [gaussianRankOneEval, gaussianKernelSection, RCLike.inner_apply, mul_comm]

lemma gaussianKernel_eq_inner_sections (x y : SourceSpace) :
    gaussianKernel x y = inner ℝ (gaussianKernelSection x) (gaussianKernelSection y) := by
  simp [gaussianKernel, gaussianKernelSection, RCLike.inner_apply, mul_comm]

lemma gaussianKernel_diagonal_moment_finite :
    Integrable (fun x : SourceSpace => gaussianKernel x x) volume := by
  simpa [gaussianKernel, pow_two] using integrable_gaussianFeature_sq

def gaussianCounterexampleData : OneDimPrintedConjecture152Data where
  P := volume
  Q := volume
  instProbP := by infer_instance
  instProbQ := by infer_instance
  ν := volume
  νDensity := fun _ => 1
  ν_hasDensity := by simp
  PDensity := fun _ => 1
  P_hasDensity := by simp
  QDensity := fun _ => 1
  Q_hasDensity := by simp
  H := ℝ
  instNormedAddCommGroupH := inferInstance
  instInnerProductSpaceH := inferInstance
  instMeasurableSpaceH := borel ℝ
  k := gaussianKernel
  eval := gaussianRankOneEval
  measurable_eval := gaussianRankOneEval_measurable
  kernelSection := gaussianKernelSection
  reproducing := gaussianRankOneEval_reproducing
  kernel_eq_inner_sections := gaussianKernel_eq_inner_sections
  γ := tailGamma
  instProbGamma := by infer_instance
  sampledDirections := tailSampledDirections

lemma gaussianCounterexampleData_hypotheses :
    PrintedConjecture152Hypotheses gaussianCounterexampleData := by
  constructor
  · refine ⟨1, by norm_num, fun _ => le_rfl⟩
  constructor
  · refine ⟨1, by norm_num, fun _ => le_rfl⟩
  constructor
  · simpa [gaussianCounterexampleData] using gaussianKernel_diagonal_moment_finite
  · simpa [gaussianCounterexampleData] using gaussianKernel_diagonal_moment_finite

lemma rankOneUnitSphere_eq_tail_or_negTail (u : RankOneUnitSphere) :
    u = tailDirection ∨ u = negTailDirection := by
  have hsquare : u.1 ^ 2 = 1 := by
    have hnormsq : ‖u.1‖ ^ 2 = 1 := by
      nlinarith [u.2]
    simpa [Real.norm_eq_abs, sq_abs] using hnormsq
  have hcase : u.1 = 1 ∨ u.1 = -1 := by
    have hpoly : (u.1 - 1) * (u.1 + 1) = 0 := by
      nlinarith [hsquare]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hpoly with h | h
    · left
      linarith
    · right
      linarith
  rcases hcase with h | h
  · left
    exact Subtype.ext h
  · right
    exact Subtype.ext h

lemma gaussianCounterexampleData_projectedP_eq_standardGaussian
    (u : RankOneUnitSphere) :
    OneDimPrintedConjecture152Data.projectedP gaussianCounterexampleData u = standardGaussian := by
  rcases rankOneUnitSphere_eq_tail_or_negTail u with rfl | rfl
  · unfold OneDimPrintedConjecture152Data.projectedP gaussianCounterexampleData gaussianRankOneEval
    simpa [tailDirection, gaussianFeature] using map_gaussianFeature_eq_standardGaussian
  · unfold OneDimPrintedConjecture152Data.projectedP gaussianCounterexampleData gaussianRankOneEval
    simpa [negTailDirection, gaussianRankOneEval] using
      (show Measure.map (fun x : SourceSpace => -gaussianFeature x) volume = standardGaussian from by
        calc
          Measure.map (fun x : SourceSpace => -gaussianFeature x) volume
              = Measure.map (fun t : ℝ => -t) (Measure.map gaussianFeature volume) := by
                  rw [Measure.map_map (by fun_prop) measurable_gaussianFeature]
                  rfl
          _ = Measure.map (fun t : ℝ => -t) standardGaussian := by
                rw [map_gaussianFeature_eq_standardGaussian]
          _ = standardGaussian := by
                simpa [standardGaussian] using
                  (ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := (1 : NNReal))))

lemma gaussianCounterexampleData_projectedQ_eq_standardGaussian
    (u : RankOneUnitSphere) :
    OneDimPrintedConjecture152Data.projectedQ gaussianCounterexampleData u = standardGaussian := by
  exact gaussianCounterexampleData_projectedP_eq_standardGaussian u

lemma gaussianCounterexampleData_tau2Sq_eq_zero (u : RankOneUnitSphere) :
    OneDimPrintedConjecture152Data.tau2Sq gaussianCounterexampleData u = 0 := by
  unfold OneDimPrintedConjecture152Data.tau2Sq
  simp_rw [OneDimPrintedConjecture152Data.rhoP, OneDimPrintedConjecture152Data.rhoQ,
    gaussianCounterexampleData_projectedP_eq_standardGaussian u,
    gaussianCounterexampleData_projectedQ_eq_standardGaussian u]
  simp

lemma gaussianCounterexampleData_eKQD2Sq_eq_zero :
    OneDimPrintedConjecture152Data.eKQD2Sq gaussianCounterexampleData = 0 := by
  unfold OneDimPrintedConjecture152Data.eKQD2Sq
  change (∫⁻ u, ENNReal.ofReal
      (OneDimPrintedConjecture152Data.tau2Sq gaussianCounterexampleData u) ∂
        tailGamma).toReal = 0
  simp [gaussianCounterexampleData_tau2Sq_eq_zero]

lemma gaussianCounterexampleData_eKQD2_eq_zero :
    OneDimPrintedConjecture152Data.eKQD2 gaussianCounterexampleData = 0 := by
  unfold OneDimPrintedConjecture152Data.eKQD2
  rw [gaussianCounterexampleData_eKQD2Sq_eq_zero]
  simp

lemma gaussianCounterexampleData_empiricalEqFiveEKQD2Sq_eq_empiricalRankOneEKQD2Sq
    (n l : ℕ) (z : Sample n × Sample n) :
    OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2Sq gaussianCounterexampleData n l z =
      empiricalRankOneEKQD2Sq gaussianFeature n z.1 z.2 := by
  let inner : ℝ :=
    ∑ j : Fin (sampleCount n),
      (sortedFeature gaussianFeature z.1 j - sortedFeature gaussianFeature z.2 j) ^ 2
  have hsum :
      ∑ i : Fin (sampleCount l),
        ∑ j : Fin (sampleCount n),
          (OneDimPrintedConjecture152Data.sortedProjection gaussianCounterexampleData
              (tailSampledDirections l i) z.1 j -
            OneDimPrintedConjecture152Data.sortedProjection gaussianCounterexampleData
              (tailSampledDirections l i) z.2 j) ^ 2
        = (sampleCount l : ℝ) * inner := by
    calc
      ∑ i : Fin (sampleCount l),
          ∑ j : Fin (sampleCount n),
            (OneDimPrintedConjecture152Data.sortedProjection gaussianCounterexampleData
                (tailSampledDirections l i) z.1 j -
              OneDimPrintedConjecture152Data.sortedProjection gaussianCounterexampleData
                (tailSampledDirections l i) z.2 j) ^ 2
        = ∑ i : Fin (sampleCount l), inner := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hsign : i.1 < halfSampleCount l
            · have hdir :
                  gaussianRankOneEval (tailSampledDirections l i).1 = gaussianFeature := by
                funext x
                simp [tailSampledDirections, hsign, tailDirection, gaussianRankOneEval]
              simpa [OneDimPrintedConjecture152Data.sortedProjection, sortedFeature,
                gaussianCounterexampleData, hdir, inner]
            · have hdir :
                  gaussianRankOneEval (tailSampledDirections l i).1 = fun x => -gaussianFeature x := by
                funext x
                simp [tailSampledDirections, hsign, negTailDirection, gaussianRankOneEval]
              simpa [OneDimPrintedConjecture152Data.sortedProjection, sortedFeature,
                gaussianCounterexampleData, hdir, inner] using
                sortedFeature_neg_sum_sq gaussianFeature z.1 z.2
      _ = (sampleCount l : ℝ) * inner := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hsum' :
      ∑ i : Fin (sampleCount l),
        ∑ j : Fin (sampleCount n),
          (OneDimPrintedConjecture152Data.sortedProjection gaussianCounterexampleData
              (gaussianCounterexampleData.sampledDirections l i) z.1 j -
            OneDimPrintedConjecture152Data.sortedProjection gaussianCounterexampleData
              (gaussianCounterexampleData.sampledDirections l i) z.2 j) ^ 2 *
            gaussianCounterexampleData.νDensity (quantileGridPoint n j)
        = (sampleCount l : ℝ) * inner := by
    simpa [gaussianCounterexampleData] using hsum
  unfold OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2Sq empiricalRankOneEKQD2Sq
  rw [hsum', show (sampleCount l : ℝ) = sampleCountReal l by simp [sampleCountReal]]
  field_simp [sampleCountReal_ne_zero l, sampleCountReal_ne_zero n]
  ring

lemma gaussianCounterexampleData_empiricalEqFiveEKQD2_eq_empiricalRankOneEKQD2
    (n l : ℕ) (z : Sample n × Sample n) :
    OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2 gaussianCounterexampleData n l z =
      empiricalRankOneEKQD2 gaussianFeature n z.1 z.2 := by
  unfold OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2 empiricalRankOneEKQD2
  rw [gaussianCounterexampleData_empiricalEqFiveEKQD2Sq_eq_empiricalRankOneEKQD2Sq]

lemma gaussianCounterexampleData_empiricalEqFiveEKQD2_eq_empiricalRealW2
    (n l : ℕ) (z : Sample n × Sample n) :
    OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2 gaussianCounterexampleData n l z =
      empiricalRealW2 n (gaussianizedSample z.1) (gaussianizedSample z.2) := by
  rw [gaussianCounterexampleData_empiricalEqFiveEKQD2_eq_empiricalRankOneEKQD2,
    empiricalRankOneEKQD2_gaussianFeature_eq_empiricalRealW2]

def paperGaussianPopulationEKQD2 : ℝ :=
  OneDimPrintedConjecture152Data.eKQD2 gaussianCounterexampleData

lemma paperGaussianPopulationEKQD2_eq_zero :
    paperGaussianPopulationEKQD2 = 0 := by
  exact gaussianCounterexampleData_eKQD2_eq_zero

def paperGaussianActualEmpiricalError (n : ℕ) (z : Sample n × Sample n) : ℝ :=
  OneDimPrintedConjecture152Data.absoluteError gaussianCounterexampleData n n z

lemma paperGaussianAbsoluteError_eq_empiricalRealW2
    (n l : ℕ) (z : Sample n × Sample n) :
    OneDimPrintedConjecture152Data.absoluteError gaussianCounterexampleData n l z =
      empiricalRealW2 n (gaussianizedSample z.1) (gaussianizedSample z.2) := by
  unfold OneDimPrintedConjecture152Data.absoluteError
  rw [gaussianCounterexampleData_empiricalEqFiveEKQD2_eq_empiricalRealW2,
    gaussianCounterexampleData_eKQD2_eq_zero, sub_zero, abs_of_nonneg]
  exact Real.sqrt_nonneg _

lemma paperGaussianActualEmpiricalError_eq_empiricalRealW2
    (n : ℕ) (z : Sample n × Sample n) :
    paperGaussianActualEmpiricalError n z =
      empiricalRealW2 n (gaussianizedSample z.1) (gaussianizedSample z.2) := by
  simpa [paperGaussianActualEmpiricalError] using
    paperGaussianAbsoluteError_eq_empiricalRealW2 n n z

lemma tailCounterexampleData_projectedP_eq_projectedQ
    (u : RankOneUnitSphere) :
    OneDimPrintedConjecture152Data.projectedP tailCounterexampleData u =
      OneDimPrintedConjecture152Data.projectedQ tailCounterexampleData u := by
  rfl

lemma tailCounterexampleData_tau2Sq_eq_zero (u : RankOneUnitSphere) :
    OneDimPrintedConjecture152Data.tau2Sq tailCounterexampleData u = 0 := by
  unfold OneDimPrintedConjecture152Data.tau2Sq
  simp_rw [OneDimPrintedConjecture152Data.rhoP, OneDimPrintedConjecture152Data.rhoQ,
    tailCounterexampleData_projectedP_eq_projectedQ u]
  simp

lemma tailCounterexampleData_eKQD2Sq_eq_zero :
    OneDimPrintedConjecture152Data.eKQD2Sq tailCounterexampleData = 0 := by
  unfold OneDimPrintedConjecture152Data.eKQD2Sq
  change (∫⁻ u, ENNReal.ofReal (OneDimPrintedConjecture152Data.tau2Sq tailCounterexampleData u) ∂
      tailGamma).toReal = 0
  simp [tailGamma, tailCounterexampleData_tau2Sq_eq_zero]

lemma tailCounterexampleData_eKQD2_eq_zero :
    OneDimPrintedConjecture152Data.eKQD2 tailCounterexampleData = 0 := by
  unfold OneDimPrintedConjecture152Data.eKQD2
  rw [tailCounterexampleData_eKQD2Sq_eq_zero]
  simp

@[simp] lemma tailCounterexampleData_sortedProjection_eq_sortedFeature {n : ℕ}
    (x : Sample n) :
    OneDimPrintedConjecture152Data.sortedProjection tailCounterexampleData tailDirection x =
      sortedFeature tailFeature x := by
  funext j
  unfold OneDimPrintedConjecture152Data.sortedProjection sortedFeature tailCounterexampleData
  simp [tailDirection, rankOneEval]

lemma tailCounterexampleData_empiricalEqFiveEKQD2Sq_eq_paper
    (n l : ℕ) (z : Sample n × Sample n) :
    OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2Sq tailCounterexampleData n l z =
      paperEqFiveTailEKQD2Sq n l z := by
  unfold OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2Sq paperEqFiveTailEKQD2Sq
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp [OneDimPrintedConjecture152Data.sortedProjection, sortedFeature, tailCounterexampleData,
    tailSampledDirections, repeatedTailDirection, tailDirection, rankOneEval]

lemma tailCounterexampleData_empiricalEqFiveEKQD2_eq_paper
    (n l : ℕ) (z : Sample n × Sample n) :
    OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2 tailCounterexampleData n l z =
      paperEqFiveTailEKQD2 n l z := by
  unfold OneDimPrintedConjecture152Data.empiricalEqFiveEKQD2 paperEqFiveTailEKQD2
  rw [tailCounterexampleData_empiricalEqFiveEKQD2Sq_eq_paper]

def paperTailPopulationEKQD2 : ℝ :=
  OneDimPrintedConjecture152Data.eKQD2 tailCounterexampleData

lemma paperTailPopulationEKQD2_eq_zero :
    paperTailPopulationEKQD2 = 0 := tailCounterexampleData_eKQD2_eq_zero

def randomizedSignedDirectionAbsoluteError (n l : ℕ) (z : Sample n × Sample n) : ℝ :=
  (∫⁻ s, ENNReal.ofReal
      (|paperEqFiveTailEKQD2WithDirections n l (signedDirections l s) z - paperTailPopulationEKQD2|)
    ∂ signSampleMeasure l).toReal

lemma randomizedSignedDirectionAbsoluteError_eq_empiricalRankOneEKQD2
    (n l : ℕ) (z : Sample n × Sample n) :
    randomizedSignedDirectionAbsoluteError n l z =
      empiricalRankOneEKQD2 tailFeature n z.1 z.2 := by
  unfold randomizedSignedDirectionAbsoluteError
  rw [paperTailPopulationEKQD2_eq_zero]
  have hconst :
      ∀ s : SignSample l,
        ENNReal.ofReal
            (|paperEqFiveTailEKQD2WithDirections n l (signedDirections l s) z - 0|) =
          ENNReal.ofReal (empiricalRankOneEKQD2 tailFeature n z.1 z.2) := by
    intro s
    rw [paperEqFiveTailEKQD2_signedDirections_eq_empiricalRankOneEKQD2 n l s z]
    have hnonneg : 0 ≤ empiricalRankOneEKQD2 tailFeature n z.1 z.2 := by
      unfold empiricalRankOneEKQD2
      exact Real.sqrt_nonneg _
    simpa [sub_zero, abs_of_nonneg hnonneg]
  have hnonneg : 0 ≤ empiricalRankOneEKQD2 tailFeature n z.1 z.2 := by
    unfold empiricalRankOneEKQD2
    exact Real.sqrt_nonneg _
  simp_rw [hconst]
  rw [lintegral_const]
  simp [signSampleMeasure, hnonneg]

def paperTailAbsoluteError (n l : ℕ) (z : Sample n × Sample n) : ℝ :=
  OneDimPrintedConjecture152Data.absoluteError tailCounterexampleData n l z

lemma paperTailAbsoluteError_eq_empiricalRankOneEKQD2 (n l : ℕ) (z : Sample n × Sample n) :
    paperTailAbsoluteError n l z = empiricalRankOneEKQD2 tailFeature n z.1 z.2 := by
  unfold paperTailAbsoluteError OneDimPrintedConjecture152Data.absoluteError
  rw [tailCounterexampleData_empiricalEqFiveEKQD2_eq_paper, tailCounterexampleData_eKQD2_eq_zero]
  rw [sub_zero, abs_of_nonneg, paperEqFiveTailEKQD2_eq_empiricalRankOneEKQD2]
  exact Real.sqrt_nonneg _

lemma randomizedSignedDirectionAbsoluteError_eq_paperTailAbsoluteError
    (n l : ℕ) (z : Sample n × Sample n) :
    randomizedSignedDirectionAbsoluteError n l z = paperTailAbsoluteError n l z := by
  rw [randomizedSignedDirectionAbsoluteError_eq_empiricalRankOneEKQD2,
    paperTailAbsoluteError_eq_empiricalRankOneEKQD2]

def paperActualEmpiricalError : ∀ n, Sample n × Sample n → ℝ
  | n, z => empiricalRankOneEKQD2 tailFeature n z.1 z.2

def paperRandomizedDirectionActualEmpiricalError : ∀ n, Sample n × Sample n → ℝ
  | n, z => randomizedSignedDirectionAbsoluteError n n z

lemma paperActualEmpiricalError_eq_tailDiagonalAbsoluteError
    (n : ℕ) (z : Sample n × Sample n) :
    paperActualEmpiricalError n z =
      OneDimPrintedConjecture152Data.absoluteError tailCounterexampleData n n z := by
  symm
  simpa [paperActualEmpiricalError] using paperTailAbsoluteError_eq_empiricalRankOneEKQD2 n n z

lemma paperRandomizedDirectionActualEmpiricalError_eq_paperActualEmpiricalError
    (n : ℕ) (z : Sample n × Sample n) :
    paperRandomizedDirectionActualEmpiricalError n z = paperActualEmpiricalError n z := by
  simpa [paperRandomizedDirectionActualEmpiricalError, paperActualEmpiricalError] using
    randomizedSignedDirectionAbsoluteError_eq_empiricalRankOneEKQD2 n n z

lemma clippedRankOneTailWitness_le_paperActualEmpiricalError
    (n : ℕ) (z : Sample n × Sample n) :
    clippedRankOneTailWitness n z ≤ paperActualEmpiricalError n z := by
  unfold clippedRankOneTailWitness paperActualEmpiricalError
  exact (min_le_left _ _).trans (rawRankOneTailWitness_le_empiricalRankOneEKQD2 n z)

lemma clippedRankOneTailWitness_le_paperRandomizedDirectionActualEmpiricalError
    (n : ℕ) (z : Sample n × Sample n) :
    clippedRankOneTailWitness n z ≤ paperRandomizedDirectionActualEmpiricalError n z := by
  rw [paperRandomizedDirectionActualEmpiricalError_eq_paperActualEmpiricalError]
  exact clippedRankOneTailWitness_le_paperActualEmpiricalError n z

lemma expectedPairError_paperRandomizedDirectionActualEmpiricalError_eq
    (n : ℕ) :
    expectedPairError paperRandomizedDirectionActualEmpiricalError n =
      expectedPairError paperActualEmpiricalError n := by
  unfold expectedPairError
  simp_rw [paperRandomizedDirectionActualEmpiricalError_eq_paperActualEmpiricalError]

lemma tailPrintedBound_yields_finite_expectedError
    (h : PrintedConjecture152_d1_p2)
    (n : ℕ) :
    (∫⁻ z, ENNReal.ofReal (paperActualEmpiricalError n z) ∂ pairMeasure n) ≠ ⊤ := by
  rcases h tailCounterexampleData tailCounterexampleData_hypotheses with ⟨C, hC, hbound⟩
  have hEq :
      (fun z : Sample n × Sample n =>
        OneDimPrintedConjecture152Data.absoluteError tailCounterexampleData n n z) =
        paperActualEmpiricalError n := by
    funext z
    symm
    exact paperActualEmpiricalError_eq_tailDiagonalAbsoluteError n z
  have hbase := (hbound n n).1
  change
    (∫⁻ z : Sample n × Sample n,
        ENNReal.ofReal (OneDimPrintedConjecture152Data.absoluteError tailCounterexampleData n n z) ∂
          pairMeasure n) ≠ ⊤ at hbase
  simpa [hEq] using hbase

lemma printedTailBound_implies_twoParameterRootRate
    (h : PrintedConjecture152_d1_p2) :
    ConjecturedTwoParameterRootRate (expectedPairError paperActualEmpiricalError) := by
  rcases h tailCounterexampleData tailCounterexampleData_hypotheses with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro n l
  have hEq :
      (fun z : Sample n × Sample n =>
        OneDimPrintedConjecture152Data.absoluteError tailCounterexampleData n l z) =
        paperActualEmpiricalError n := by
    funext z
    simpa [paperActualEmpiricalError] using paperTailAbsoluteError_eq_empiricalRankOneEKQD2 n l z
  have hbound' := (hbound n l).2
  change
    (∫⁻ z : Sample n × Sample n,
        ENNReal.ofReal (OneDimPrintedConjecture152Data.absoluteError tailCounterexampleData n l z) ∂
          pairMeasure n).toReal ≤ C * (rootRate l + rootRate n) at hbound'
  calc
    expectedPairError paperActualEmpiricalError n
        = (∫⁻ z : Sample n × Sample n,
            ENNReal.ofReal
              (OneDimPrintedConjecture152Data.absoluteError tailCounterexampleData n l z) ∂
                pairMeasure n).toReal := by
                  unfold expectedPairError
                  simp [hEq]
    _ ≤ C * (rootRate l + rootRate n) := hbound'

theorem PrintedConjecture152_d1_p2_false :
    ¬ PrintedConjecture152_d1_p2 := by
  intro hPrinted
  have hfinite : ∀ n,
      (∫⁻ z, ENNReal.ofReal (paperActualEmpiricalError n z) ∂ pairMeasure n) ≠ ⊤ :=
    tailPrintedBound_yields_finite_expectedError hPrinted
  have hnot :
      ¬ EventuallyBoundedByRootRate (expectedPairError paperActualEmpiricalError) := by
    exact not_eventuallyBoundedByRootRate_of_dominatesClippedRankOneTailWitness
      clippedRankOneTailWitness_le_paperActualEmpiricalError hfinite
  have hrate :
      EventuallyBoundedByRootRate (expectedPairError paperActualEmpiricalError) := by
    exact ConjecturedTwoParameterRootRate.eventuallyBoundedByRootRate
      (printedTailBound_implies_twoParameterRootRate hPrinted)
  exact hnot hrate

theorem tailKernel_counterexample_refutes_conjecture152 :
    ¬ PrintedConjecture152_d1_p2 := by
  exact PrintedConjecture152_d1_p2_false

theorem disproves_conjectured_rate :
    ¬ PrintedConjecture152_d1_p2 := by
  exact PrintedConjecture152_d1_p2_false

end AttemptTwo

end QuasimodularSturm
