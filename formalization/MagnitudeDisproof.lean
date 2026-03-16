import Mathlib

open scoped Topology
open Filter Matrix

namespace MagnitudeDisproof

section KMSFour

variable {R : Type*} [CommRing R]

/--
The `4 × 4` one-dimensional exponential-kernel matrix attached to consecutive gap parameters
`q₀,q₁,q₂`.
-/
def kmsFour (q₀ q₁ q₂ : R) : Matrix (Fin 4) (Fin 4) R :=
  !![
    1, q₀, q₀ * q₁, q₀ * q₁ * q₂;
    q₀, 1, q₁, q₁ * q₂;
    q₀ * q₁, q₁, 1, q₂;
    q₀ * q₁ * q₂, q₁ * q₂, q₂, 1
  ]

/--
After the descending row operations `Rᵢ ← Rᵢ - qᵢ₋₁ Rᵢ₋₁`, the matrix `kmsFour q₀ q₁ q₂`
becomes upper triangular.
-/
def kmsFourRowReduced (q₀ q₁ q₂ : R) : Matrix (Fin 4) (Fin 4) R :=
  !![
    1, q₀, q₀ * q₁, q₀ * q₁ * q₂;
    0, 1 - q₀ ^ 2, q₁ * (1 - q₀ ^ 2), q₁ * q₂ * (1 - q₀ ^ 2);
    0, 0, 1 - q₁ ^ 2, q₂ * (1 - q₁ ^ 2);
    0, 0, 0, 1 - q₂ ^ 2
  ]

theorem kmsFour_det (q₀ q₁ q₂ : R) :
    (kmsFour q₀ q₁ q₂).det = (1 - q₀ ^ 2) * (1 - q₁ ^ 2) * (1 - q₂ ^ 2) := by
  let A := kmsFour q₀ q₁ q₂
  let B := kmsFourRowReduced q₀ q₁ q₂
  have hdet : A.det = B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (c := ![q₀, q₁, q₂])
    · intro j
      fin_cases j <;> simp [A, B, kmsFour, kmsFourRowReduced]
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [A, B, kmsFour, kmsFourRowReduced] <;> ring
  have htri : B.BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [B, kmsFourRowReduced] at hij ⊢
  calc
    A.det = B.det := hdet
    _ = (1 - q₀ ^ 2) * (1 - q₁ ^ 2) * (1 - q₂ ^ 2) := by
      rw [Matrix.det_of_upperTriangular htri, Fin.prod_univ_four]
      simp [B, kmsFourRowReduced]

end KMSFour

section MagnitudeCounterexample

/-- The four vertices of the 1D cubical thickening of `F = {0,1}` at radius `r`. -/
def attemptNinePoint (r : ℝ) : Fin 4 → ℝ
  | 0 => -r
  | 1 => r
  | 2 => 1 - r
  | _ => 1 + r

/-- The similarity matrix `Z_X = (e^{-|xᵢ-xⱼ|})` for the attempt-9 counterexample. -/
noncomputable def attemptNineSimilarity (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ Real.exp (-|attemptNinePoint r i - attemptNinePoint r j|)

/-- The same matrix with all distances simplified for `0 < r < 1/2`. -/
noncomputable def attemptNineExplicitMatrix (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![
    1, Real.exp (-2 * r), Real.exp (-1), Real.exp (-(1 + 2 * r));
    Real.exp (-2 * r), 1, Real.exp (-(1 - 2 * r)), Real.exp (-1);
    Real.exp (-1), Real.exp (-(1 - 2 * r)), 1, Real.exp (-2 * r);
    Real.exp (-(1 + 2 * r)), Real.exp (-1), Real.exp (-2 * r), 1
  ]

noncomputable def attemptNineDet (r : ℝ) : ℝ :=
  (attemptNineSimilarity r).det

lemma abs_attemptNinePoint_zero_one {r : ℝ} (hr : 0 ≤ r) :
    |attemptNinePoint r 0 - attemptNinePoint r 1| = 2 * r := by
  have h : attemptNinePoint r 0 - attemptNinePoint r 1 = -(r * 2) := by
    simp [attemptNinePoint]
    ring
  rw [h, abs_neg, abs_mul, abs_of_nonneg hr]
  norm_num
  ring

lemma abs_attemptNinePoint_zero_two (r : ℝ) :
    |attemptNinePoint r 0 - attemptNinePoint r 2| = 1 := by
  have h : attemptNinePoint r 0 - attemptNinePoint r 2 = -1 := by
    simp [attemptNinePoint]
    ring
  rw [h]
  norm_num

lemma abs_attemptNinePoint_zero_three {r : ℝ} (hr : 0 ≤ r) :
    |attemptNinePoint r 0 - attemptNinePoint r 3| = 1 + 2 * r := by
  have hnonpos : -1 - 2 * r ≤ 0 := by linarith
  calc
    |attemptNinePoint r 0 - attemptNinePoint r 3| = |-1 - 2 * r| := by
      simp [attemptNinePoint]
      ring_nf
    _ = 1 + 2 * r := by
      rw [abs_of_nonpos hnonpos]
      ring_nf

lemma abs_attemptNinePoint_one_two {r : ℝ} (hr : r ≤ 1 / 2) :
    |attemptNinePoint r 1 - attemptNinePoint r 2| = 1 - 2 * r := by
  have hnonpos : -1 + 2 * r ≤ 0 := by linarith
  calc
    |attemptNinePoint r 1 - attemptNinePoint r 2| = |-1 + 2 * r| := by
      simp [attemptNinePoint]
      ring_nf
    _ = 1 - 2 * r := by
      rw [abs_of_nonpos hnonpos]
      ring_nf

lemma abs_attemptNinePoint_one_three (r : ℝ) :
    |attemptNinePoint r 1 - attemptNinePoint r 3| = 1 := by
  have h : attemptNinePoint r 1 - attemptNinePoint r 3 = -1 := by
    simp [attemptNinePoint]
  rw [h]
  norm_num

lemma abs_attemptNinePoint_two_three {r : ℝ} (hr : 0 ≤ r) :
    |attemptNinePoint r 2 - attemptNinePoint r 3| = 2 * r := by
  have h : attemptNinePoint r 2 - attemptNinePoint r 3 = -(r * 2) := by
    simp [attemptNinePoint]
    ring
  rw [h, abs_neg, abs_mul, abs_of_nonneg hr]
  norm_num
  ring

lemma abs_attemptNinePoint_one_zero {r : ℝ} (hr : 0 ≤ r) :
    |attemptNinePoint r 1 - attemptNinePoint r 0| = 2 * r := by
  simpa [abs_sub_comm] using abs_attemptNinePoint_zero_one hr

lemma abs_attemptNinePoint_two_zero (r : ℝ) :
    |attemptNinePoint r 2 - attemptNinePoint r 0| = 1 := by
  simpa [abs_sub_comm] using abs_attemptNinePoint_zero_two r

lemma abs_attemptNinePoint_three_zero {r : ℝ} (hr : 0 ≤ r) :
    |attemptNinePoint r 3 - attemptNinePoint r 0| = 1 + 2 * r := by
  simpa [abs_sub_comm] using abs_attemptNinePoint_zero_three hr

lemma abs_attemptNinePoint_two_one {r : ℝ} (hr : r ≤ 1 / 2) :
    |attemptNinePoint r 2 - attemptNinePoint r 1| = 1 - 2 * r := by
  simpa [abs_sub_comm] using abs_attemptNinePoint_one_two hr

lemma abs_attemptNinePoint_three_one (r : ℝ) :
    |attemptNinePoint r 3 - attemptNinePoint r 1| = 1 := by
  simpa [abs_sub_comm] using abs_attemptNinePoint_one_three r

lemma abs_attemptNinePoint_three_two {r : ℝ} (hr : 0 ≤ r) :
    |attemptNinePoint r 3 - attemptNinePoint r 2| = 2 * r := by
  simpa [abs_sub_comm] using abs_attemptNinePoint_two_three hr

theorem attemptNineSimilarity_eq_explicitMatrix {r : ℝ} (hr₀ : 0 ≤ r) (hrHalf : r ≤ 1 / 2) :
    attemptNineSimilarity r = attemptNineExplicitMatrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [attemptNineSimilarity, attemptNineExplicitMatrix,
      abs_attemptNinePoint_zero_one hr₀, abs_attemptNinePoint_zero_two r,
      abs_attemptNinePoint_zero_three hr₀, abs_attemptNinePoint_one_two hrHalf,
      abs_attemptNinePoint_one_three r, abs_attemptNinePoint_two_three hr₀,
      abs_attemptNinePoint_one_zero hr₀, abs_attemptNinePoint_two_zero r,
      abs_attemptNinePoint_three_zero hr₀, abs_attemptNinePoint_two_one hrHalf,
      abs_attemptNinePoint_three_one r, abs_attemptNinePoint_three_two hr₀]

theorem attemptNineExplicitMatrix_eq_kms (r : ℝ) :
    attemptNineExplicitMatrix r =
      kmsFour (Real.exp (-2 * r)) (Real.exp (-(1 - 2 * r))) (Real.exp (-2 * r)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [attemptNineExplicitMatrix, kmsFour, ← Real.exp_add] <;> ring_nf

theorem attemptNineDet_eq {r : ℝ} (hr₀ : 0 < r) (hrHalf : r < 1 / 2) :
    attemptNineDet r = (1 - Real.exp (-4 * r)) ^ 2 * (1 - Real.exp (-2 * (1 - 2 * r))) := by
  rw [attemptNineDet, attemptNineSimilarity_eq_explicitMatrix hr₀.le hrHalf.le,
    attemptNineExplicitMatrix_eq_kms, kmsFour_det]
  have hsq₀ : Real.exp (-2 * r) ^ 2 = Real.exp (-4 * r) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hsq₁ : Real.exp (-(1 - 2 * r)) ^ 2 = Real.exp (-2 * (1 - 2 * r)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hsq₀, hsq₁]
  ring_nf

theorem tendsto_one_sub_exp_neg4_div :
    Tendsto (fun r : ℝ ↦ (1 - Real.exp (-4 * r)) / r) (𝓝[>] 0) (𝓝 4) := by
  let f : ℝ → ℝ := fun r ↦ 1 - Real.exp (-4 * r)
  have hderiv : HasDerivAt f 4 0 := by
    dsimp [f]
    simpa using ((((hasDerivAt_id 0).const_mul (-4)).exp).const_sub 1)
  have hzero : f 0 = 0 := by
    simp [f]
  simpa [f, slope_def_field, hzero, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
    hderiv.tendsto_slope_zero_right

theorem attemptNineDet_div_rsq_tendsto :
    Tendsto (fun r : ℝ ↦ attemptNineDet r / r ^ 2) (𝓝[>] 0)
      (𝓝 (16 * (1 - Real.exp (-2)))) := by
  have hEventual :
      (fun r : ℝ ↦ attemptNineDet r / r ^ 2) =ᶠ[𝓝[>] 0]
        (fun r : ℝ ↦ ((1 - Real.exp (-4 * r)) / r) ^ 2 * (1 - Real.exp (-2 * (1 - 2 * r)))) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with r hr
    have hr₀ : 0 < r := hr.1
    have hrHalf : r < 1 / 2 := hr.2
    have hrne : r ≠ 0 := ne_of_gt hr₀
    rw [attemptNineDet_eq hr₀ hrHalf]
    field_simp [hrne]
  refine Tendsto.congr' hEventual.symm ?_
  have hFirst := tendsto_one_sub_exp_neg4_div
  have hSecond :
      Tendsto (fun r : ℝ ↦ 1 - Real.exp (-2 * (1 - 2 * r))) (𝓝[>] 0)
        (𝓝 (1 - Real.exp (-2))) := by
    have hCont : Continuous fun r : ℝ ↦ 1 - Real.exp (-2 * (1 - 2 * r)) := by
      continuity
    have hWithin :
        ContinuousWithinAt (fun r : ℝ ↦ 1 - Real.exp (-2 * (1 - 2 * r))) (Set.Ioi 0) 0 :=
      hCont.continuousAt.continuousWithinAt
    simpa using hWithin.tendsto
  have hMul :
      Tendsto
        (fun r : ℝ ↦
          ((1 - Real.exp (-4 * r)) / r) * ((1 - Real.exp (-4 * r)) / r) *
            (1 - Real.exp (-2 * (1 - 2 * r))))
        (𝓝[>] 0) (𝓝 (4 * 4 * (1 - Real.exp (-2)))) := by
    simpa [pow_two] using (hFirst.pow 2).mul hSecond
  convert hMul using 1 <;> ring_nf

theorem attemptNineDet_div_rsq_not_tendsto_conjectured :
    ¬ Tendsto (fun r : ℝ ↦ attemptNineDet r / r ^ 2) (𝓝[>] 0) (𝓝 (16 : ℝ)) := by
  intro h
  have hEq :
      (16 * (1 - Real.exp (-2 : ℝ))) = 16 :=
    tendsto_nhds_unique attemptNineDet_div_rsq_tendsto h
  have hlt : 16 * (1 - Real.exp (-2 : ℝ)) < 16 := by
    have hpos : 0 < Real.exp (-2 : ℝ) := Real.exp_pos (-2)
    nlinarith
  linarith

end MagnitudeCounterexample

end MagnitudeDisproof
