import Mathlib

open scoped BigOperators

noncomputable section

namespace HilbertDepth

lemma log_two_pos : 0 < Real.log 2 := by
  simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)

lemma log_two_lt_one : Real.log 2 < 1 := by
  exact Real.log_two_lt_d9.trans (by norm_num)

lemma log_two_sq_lt_half : (Real.log 2) ^ 2 < (1 : ℝ) / 2 := by
  nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

lemma exp_lower_quadratic {u : ℝ} (hu : 0 ≤ u) :
    1 + u + u ^ 2 / 2 ≤ Real.exp u := by
  have hsum : Summable (fun n ↦ u ^ n / (Nat.factorial n : ℝ)) := by
    simpa using (Real.summable_pow_div_factorial u :
      Summable (fun n ↦ u ^ n / (Nat.factorial n : ℝ)))
  calc
    1 + u + u ^ 2 / 2 =
        Finset.sum (Finset.range 3) (fun n ↦ u ^ n / (Nat.factorial n : ℝ)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      norm_num [pow_two]
    _ ≤ tsum (fun n : ℕ ↦ u ^ n / (Nat.factorial n : ℝ)) := by
      refine hsum.sum_le_tsum _ ?_
      intro n hn
      positivity
    _ = Real.exp u := by
      rw [Real.exp_eq_exp_ℝ]
      simpa using (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) u).symm

lemma pair_exp_bound {x y u : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ 2 * u + u ^ 2) :
    (1 + x) * (1 + y) ≤ Real.exp (2 * u) := by
  have h1 : (1 + x) * (1 + y) ≤ (1 + (x + y) / 2) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have h2 : (1 + (x + y) / 2) ^ 2 ≤ (1 + u + u ^ 2 / 2) ^ 2 := by
    nlinarith
  have h3 : (1 + u + u ^ 2 / 2) ^ 2 ≤ (Real.exp u) ^ 2 := by
    have hq := exp_lower_quadratic hu
    nlinarith [hq, Real.exp_pos u]
  calc
    (1 + x) * (1 + y) ≤ (1 + (x + y) / 2) ^ 2 := h1
    _ ≤ (1 + u + u ^ 2 / 2) ^ 2 := h2
    _ ≤ (Real.exp u) ^ 2 := h3
    _ = Real.exp (2 * u) := by
      rw [pow_two, ← Real.exp_add]
      ring_nf

lemma weighted_recip_sum_le_of_same_sum
    {c a b a₀ b₀ : ℝ}
    (hc : 0 ≤ c)
    (ha : 0 < a) (hb : 0 < b) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hsum : a + b = a₀ + b₀)
    (hprod : a₀ * b₀ ≤ a * b) :
    c / a + c / b ≤ c / a₀ + c / b₀ := by
  have hnum : 0 ≤ c * (a₀ + b₀) := by positivity
  have hab_pos : 0 < a * b := mul_pos ha hb
  have ha₀b₀_pos : 0 < a₀ * b₀ := mul_pos ha₀ hb₀
  have hInv : (a * b)⁻¹ ≤ (a₀ * b₀)⁻¹ := by
    exact (inv_le_inv₀ hab_pos ha₀b₀_pos).2 hprod
  calc
    c / a + c / b = c * (a + b) / (a * b) := by
      field_simp [ha.ne', hb.ne']
      ring
    _ = c * (a₀ + b₀) / (a * b) := by rw [hsum]
    _ ≤ c * (a₀ + b₀) / (a₀ * b₀) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hInv hnum
    _ = c / a₀ + c / b₀ := by
      field_simp [ha₀.ne', hb₀.ne']
      ring

lemma pair_factor_le_exp_of_endpoint
    {c u a b a₀ b₀ : ℝ}
    (hu : 0 ≤ u) (hc : 0 ≤ c)
    (ha : 0 < a) (hb : 0 < b) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hsum : a + b = a₀ + b₀)
    (hprod : a₀ * b₀ ≤ a * b)
    (hend : c / a₀ + c / b₀ ≤ 2 * u + u ^ 2) :
    (1 + c / a) * (1 + c / b) ≤ Real.exp (2 * u) := by
  have hxy : c / a + c / b ≤ 2 * u + u ^ 2 :=
    (weighted_recip_sum_le_of_same_sum hc ha hb ha₀ hb₀ hsum hprod).trans hend
  have hx : 0 ≤ c / a := by positivity
  have hy : 0 ≤ c / b := by positivity
  exact pair_exp_bound hu hx hy hxy

lemma sq_prod_range_eq_prod_reflect (g : ℕ → ℝ) (m : ℕ) :
    (Finset.prod (Finset.range m) fun j ↦ g j) ^ 2 =
      Finset.prod (Finset.range m) fun j ↦ g j * g (m - 1 - j) := by
  calc
    (Finset.prod (Finset.range m) fun j ↦ g j) ^ 2 =
        (Finset.prod (Finset.range m) fun j ↦ g j) *
          (Finset.prod (Finset.range m) fun j ↦ g j) := by ring
    _ = (Finset.prod (Finset.range m) fun j ↦ g j) *
          (Finset.prod (Finset.range m) fun j ↦ g (m - 1 - j)) := by
      rw [← Finset.prod_range_reflect]
    _ = Finset.prod (Finset.range m) (fun j ↦ g j * g (m - 1 - j)) := by
      rw [← Finset.prod_mul_distrib]

def pFactor (m : ℕ) (k : ℝ) (j : ℕ) : ℝ :=
  1 + ((m : ℝ) + 1) / (k - (j + 1))

def pProd (m : ℕ) (k : ℝ) : ℝ :=
  Finset.prod (Finset.range m) fun j ↦ pFactor m k j

def qFactor (m : ℕ) (k : ℝ) (j : ℕ) : ℝ :=
  1 + (m : ℝ) / (k - j)

def qProd (m : ℕ) (k : ℝ) : ℝ :=
  Finset.prod (Finset.range m) fun j ↦ qFactor m k j

def rFactor (m : ℕ) (k : ℝ) (j : ℕ) : ℝ :=
  1 + ((m : ℝ) + 2) / (k - (j + 2))

def rProd (m : ℕ) (k : ℝ) : ℝ :=
  Finset.prod (Finset.range m) fun j ↦ rFactor m k j

def scale (m : ℕ) : ℝ :=
  Real.log 2 / m

def pThreshold (m : ℕ) : ℝ :=
  (((m : ℝ) + 1 / 2) ^ 2) / Real.log 2

def qThreshold (m : ℕ) : ℝ :=
  ((m : ℝ) ^ 2) / Real.log 2

def rThreshold (m : ℕ) : ℝ :=
  (((m : ℝ) + 1) ^ 2) / Real.log 2

lemma scale_nonneg (m : ℕ) : 0 ≤ scale m := by
  unfold scale
  positivity

lemma scale_pos {m : ℕ} (hm : 0 < m) : 0 < scale m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold scale
  positivity

lemma pThreshold_sub_m_pos {m : ℕ} (hm : 1 ≤ m) : 0 < pThreshold m - m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 < Real.log 2 := log_two_pos
  refine sub_pos.mpr ?_
  rw [pThreshold, lt_div_iff₀ hL]
  nlinarith [log_two_lt_one, hm']

lemma pThreshold_sub_succ_pos {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    0 < pThreshold m - (j + 1) := by
  have hbase := pThreshold_sub_m_pos hm
  have hj' : (j : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hj
  have hlt : (j + 1 : ℝ) < pThreshold m := by
    have hm_lt : (m : ℝ) < pThreshold m := by nlinarith
    exact lt_of_le_of_lt hj' hm_lt
  nlinarith

lemma pThreshold_sub_reflect_pos {m j : ℕ} (hm : 1 ≤ m) :
    0 < pThreshold m - m + j := by
  have hbase := pThreshold_sub_m_pos hm
  positivity

lemma qThreshold_sub_base_pos {m : ℕ} (hm : 1 ≤ m) : 0 < qThreshold m - m + 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 < Real.log 2 := log_two_pos
  have h : (m : ℝ) - 1 < qThreshold m := by
    rw [qThreshold, lt_div_iff₀ hL]
    nlinarith [hm', log_two_lt_one]
  nlinarith

lemma qThreshold_sub_pos {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    0 < qThreshold m - j := by
  have hbase := qThreshold_sub_base_pos hm
  have hj' : (j : ℝ) ≤ m - 1 := by
    exact_mod_cast Nat.le_pred_of_lt hj
  nlinarith

lemma qThreshold_sub_reflect_pos {m j : ℕ} (hm : 1 ≤ m) :
    0 < qThreshold m - m + 1 + j := by
  have hbase := qThreshold_sub_base_pos hm
  positivity

lemma rThreshold_sub_base_pos {m : ℕ} (hm : 1 ≤ m) : 0 < rThreshold m - m - 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 < Real.log 2 := log_two_pos
  have h : (m : ℝ) + 1 < rThreshold m := by
    rw [rThreshold, lt_div_iff₀ hL]
    nlinarith [log_two_lt_one, hm']
  nlinarith

lemma rThreshold_sub_left_pos {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    0 < rThreshold m - (j + 2) := by
  have hbase := rThreshold_sub_base_pos hm
  have hj' : (j : ℝ) + 2 ≤ m + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.succ_le_of_lt hj)
  have hlt : (j + 2 : ℝ) < rThreshold m := by
    have hm_lt : (m : ℝ) + 1 < rThreshold m := by nlinarith
    exact lt_of_le_of_lt hj' hm_lt
  nlinarith

lemma rThreshold_sub_reflect_pos {m j : ℕ} (hm : 1 ≤ m) :
    0 < rThreshold m - m - 1 + j := by
  have hbase := rThreshold_sub_base_pos hm
  positivity

lemma exp_two_scale_pow {m : ℕ} (hm : 0 < m) :
    Real.exp (2 * scale m) ^ m = 4 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  calc
    Real.exp (2 * scale m) ^ m = Real.exp (m * (2 * scale m)) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (2 * Real.log 2) := by
      rw [scale]
      field_simp [hm']
    _ = 4 := by
      rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

def pEndpointPoly (m : ℕ) : ℝ :=
  ((1 : ℝ) / 2 - (Real.log 2) ^ 2) * (m : ℝ) ^ 3
    + ((1 : ℝ) / 2) * (m : ℝ) ^ 2
    + ((1 : ℝ) / 8 - 5 * (Real.log 2) ^ 2 / 4 + (Real.log 2) ^ 3) * (m : ℝ)
    + Real.log 2 / 16 - (Real.log 2) ^ 2 / 4

lemma pEndpointPoly_nonneg {m : ℕ} (hm : 2 ≤ m) : 0 ≤ pEndpointPoly m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h₁ : 0 < (1 : ℝ) / 2 - (Real.log 2) ^ 2 := by
    nlinarith [log_two_sq_lt_half]
  have h₂ : -(1 : ℝ) / 2 < (1 : ℝ) / 8 - 5 * (Real.log 2) ^ 2 / 4 + (Real.log 2) ^ 3 := by
    nlinarith [log_two_lt_one, log_two_sq_lt_half, log_two_pos]
  have h₃ : -(1 : ℝ) / 8 < Real.log 2 / 16 - (Real.log 2) ^ 2 / 4 := by
    nlinarith [log_two_sq_lt_half, log_two_pos]
  have hm₀ : 0 ≤ (m : ℝ) := by positivity
  have hfirst : 0 ≤ ((1 : ℝ) / 2 - (Real.log 2) ^ 2) * (m : ℝ) ^ 3 := by
    positivity
  have hmidCoeff : 0 ≤ (1 : ℝ) / 8 - 5 * (Real.log 2) ^ 2 / 4 + (Real.log 2) ^ 3 + 1 / 2 := by
    nlinarith [h₂]
  have hmid :
      0 ≤ ((1 : ℝ) / 8 - 5 * (Real.log 2) ^ 2 / 4 + (Real.log 2) ^ 3 + 1 / 2) * (m : ℝ) := by
    positivity
  have hlast : 0 ≤ Real.log 2 / 16 - (Real.log 2) ^ 2 / 4 + 1 / 8 := by
    nlinarith [h₃]
  have hdiff :
      0 ≤ pEndpointPoly m -
        (((1 : ℝ) / 2) * (m : ℝ) ^ 2 - (1 : ℝ) / 2 * (m : ℝ) - (1 : ℝ) / 8) := by
    unfold pEndpointPoly
    nlinarith [hfirst, hmid, hlast]
  have hbase : 0 ≤ ((1 : ℝ) / 2) * (m : ℝ) ^ 2 - (1 : ℝ) / 2 * (m : ℝ) - (1 : ℝ) / 8 := by
    nlinarith
  nlinarith

lemma one_add_div_antitone {c d k₁ k₂ : ℝ}
    (hc : 0 ≤ c) (hk : k₁ ≤ k₂) (hd : 0 < k₁ - d) :
    1 + c / (k₂ - d) ≤ 1 + c / (k₁ - d) := by
  have hd₂ : 0 < k₂ - d := by linarith
  have hInv : (k₂ - d)⁻¹ ≤ (k₁ - d)⁻¹ := by
    exact (inv_le_inv₀ hd₂ hd).2 (by linarith)
  have hmul : c * (k₂ - d)⁻¹ ≤ c * (k₁ - d)⁻¹ := mul_le_mul_of_nonneg_left hInv hc
  calc
    1 + c / (k₂ - d) = 1 + c * (k₂ - d)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ 1 + c * (k₁ - d)⁻¹ := by nlinarith
    _ = 1 + c / (k₁ - d) := by rw [div_eq_mul_inv]

lemma p_endpoint_sum_le {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) + 1) / (pThreshold m - 1) + ((m : ℝ) + 1) / (pThreshold m - m) ≤
      2 * scale m + scale m ^ 2 := by
  have hm₁ : 1 ≤ m := by omega
  have hm₀ : 0 < m := by omega
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm₀)
  have hL : 0 < Real.log 2 := log_two_pos
  let B : ℝ := (2 * m + 1) ^ 2 - 4 * Real.log 2
  let C : ℝ := (2 * m + 1) ^ 2 - 4 * m * Real.log 2
  have hB_eq : pThreshold m - 1 = B / (4 * Real.log 2) := by
    dsimp [B]
    unfold pThreshold
    field_simp [hL.ne']
    ring
  have hC_eq : pThreshold m - m = C / (4 * Real.log 2) := by
    dsimp [C]
    unfold pThreshold
    field_simp [hL.ne', hm']
    ring
  have hB : 0 < B := by
    calc
      B = 4 * Real.log 2 * (pThreshold m - 1) := by
        rw [hB_eq]
        field_simp [hL.ne']
      _ > 0 := by
        have hden : 0 < pThreshold m - 1 := by simpa using pThreshold_sub_succ_pos hm₁ hm₀
        positivity
  have hC : 0 < C := by
    calc
      C = 4 * Real.log 2 * (pThreshold m - m) := by
        rw [hC_eq]
        field_simp [hL.ne']
      _ > 0 := by
        have hden : 0 < pThreshold m - m := pThreshold_sub_m_pos hm₁
        positivity
  have hpoly := pEndpointPoly_nonneg hm
  unfold pEndpointPoly at hpoly
  have hcrossEq :
      (2 * (m : ℝ) + Real.log 2) * B * C -
        4 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) * (B + C) =
          16 * pEndpointPoly m := by
    unfold pEndpointPoly
    dsimp [B, C]
    ring_nf
  have hcross :
      4 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) * (B + C) ≤
        (2 * (m : ℝ) + Real.log 2) * B * C := by
    have hnonneg :
        0 ≤ (2 * (m : ℝ) + Real.log 2) * B * C -
          4 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) * (B + C) := by
      rw [hcrossEq]
      positivity
    nlinarith
  have hBC : 0 < B * C := mul_pos hB hC
  have hdiv :
      4 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) * (1 / B + 1 / C) ≤
        2 * (m : ℝ) + Real.log 2 := by
    have hEqLeft :
        4 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) * (1 / B + 1 / C) =
          (4 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) * (B + C)) / (B * C) := by
      field_simp [hB.ne', hC.ne']
      ring
    rw [hEqLeft]
    exact (div_le_iff₀ hBC).2 (by simpa [mul_assoc] using hcross)
  have hmSq : ((m : ℝ) ^ 2) ≠ 0 := by positivity
  calc
    ((m : ℝ) + 1) / (pThreshold m - 1) + ((m : ℝ) + 1) / (pThreshold m - m)
        = 4 * Real.log 2 * ((m : ℝ) + 1) / B + 4 * Real.log 2 * ((m : ℝ) + 1) / C := by
          rw [hB_eq, hC_eq]
          field_simp [hL.ne', hB.ne', hC.ne']
    _ = (Real.log 2 / (m : ℝ) ^ 2) *
          (4 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) * (1 / B + 1 / C)) := by
            field_simp [hmSq, hB.ne', hC.ne']
    _ ≤ (Real.log 2 / (m : ℝ) ^ 2) * (2 * (m : ℝ) + Real.log 2) := by
          exact mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ Real.log 2 / (m : ℝ) ^ 2)
    _ = 2 * scale m + scale m ^ 2 := by
          unfold scale
          field_simp [hmSq]

lemma pFactor_antitone {m j : ℕ} {k₁ k₂ : ℝ}
    (hk : k₁ ≤ k₂) (hpos : 0 < k₁ - (j + 1)) :
    pFactor m k₂ j ≤ pFactor m k₁ j := by
  simpa [pFactor] using
    one_add_div_antitone
      (c := (m : ℝ) + 1) (d := (j : ℝ) + 1) (k₁ := k₁) (k₂ := k₂)
      (by positivity) hk hpos

lemma pProd_antitone {m : ℕ} {k₁ k₂ : ℝ}
    (hk : k₁ ≤ k₂) (hpos : ∀ j ∈ Finset.range m, 0 < k₁ - (j + 1)) :
    pProd m k₂ ≤ pProd m k₁ := by
  unfold pProd
  refine Finset.prod_le_prod ?_ ?_
  · intro j hj
    have hpos₂ : 0 < k₂ - (j + 1) := by linarith [hpos j hj, hk]
    unfold pFactor
    positivity
  · intro j hj
    exact pFactor_antitone hk (hpos j hj)

lemma p_pair_nonneg {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    0 ≤ pFactor m (pThreshold m) j * pFactor m (pThreshold m) (m - 1 - j) := by
  have hjle : j ≤ m - 1 := Nat.le_pred_of_lt hj
  have hleft : 0 ≤ pFactor m (pThreshold m) j := by
    unfold pFactor
    have hden : 0 < pThreshold m - (j + 1) := pThreshold_sub_succ_pos hm hj
    positivity
  have hcast_reflect : ((m - 1 - j : ℕ) : ℝ) = m - 1 - j := by
    rw [Nat.cast_sub hjle, Nat.cast_sub hm]
    norm_num
  have hdeneq : pThreshold m - (((m - 1 - j : ℕ) : ℝ) + 1) = pThreshold m - m + j := by
    rw [hcast_reflect]
    ring
  have hright' : 0 ≤ 1 + ((m : ℝ) + 1) / (pThreshold m - m + j) := by
    have hden : 0 < pThreshold m - m + j := pThreshold_sub_reflect_pos hm
    positivity
  have hright : 0 ≤ pFactor m (pThreshold m) (m - 1 - j) := by
    calc
      0 ≤ 1 + ((m : ℝ) + 1) / (pThreshold m - m + j) := hright'
      _ = pFactor m (pThreshold m) (m - 1 - j) := by
        unfold pFactor
        rw [hdeneq]
  positivity

lemma p_pair_le_exp {m j : ℕ} (hm : 2 ≤ m) (hj : j < m) :
    pFactor m (pThreshold m) j * pFactor m (pThreshold m) (m - 1 - j) ≤
      Real.exp (2 * scale m) := by
  have hm₁ : 1 ≤ m := by omega
  have hm₀ : 0 < m := by omega
  have hjle : j ≤ m - 1 := Nat.le_pred_of_lt hj
  have hcast_reflect : ((m - 1 - j : ℕ) : ℝ) = m - 1 - j := by
    rw [Nat.cast_sub hjle, Nat.cast_sub hm₁]
    norm_num
  have hdeneq : pThreshold m - (((m - 1 - j : ℕ) : ℝ) + 1) = pThreshold m - m + j := by
    rw [hcast_reflect]
    ring
  have hu : 0 ≤ scale m := scale_nonneg m
  have hc : 0 ≤ (m : ℝ) + 1 := by positivity
  have ha : 0 < pThreshold m - (j + 1) := pThreshold_sub_succ_pos hm₁ hj
  have hb : 0 < pThreshold m - m + j := pThreshold_sub_reflect_pos hm₁
  have ha₀ : 0 < pThreshold m - 1 := by
    simpa using pThreshold_sub_succ_pos hm₁ hm₀
  have hb₀ : 0 < pThreshold m - m := pThreshold_sub_m_pos hm₁
  have hsum :
      pThreshold m - (j + 1) + (pThreshold m - m + j) =
        (pThreshold m - 1) + (pThreshold m - m) := by
    ring
  have hj' : (j : ℝ) ≤ m - 1 := by exact_mod_cast hjle
  have hprod :
      (pThreshold m - 1) * (pThreshold m - m) ≤
        (pThreshold m - (j + 1)) * (pThreshold m - m + j) := by
    nlinarith
  have hend :
      ((m : ℝ) + 1) / (pThreshold m - 1) + ((m : ℝ) + 1) / (pThreshold m - m) ≤
        2 * scale m + scale m ^ 2 := p_endpoint_sum_le hm
  calc
    pFactor m (pThreshold m) j * pFactor m (pThreshold m) (m - 1 - j) =
        (1 + ((m : ℝ) + 1) / (pThreshold m - (j + 1))) *
          (1 + ((m : ℝ) + 1) / (pThreshold m - m + j)) := by
      unfold pFactor
      rw [hdeneq]
    _ ≤ Real.exp (2 * scale m) := by
      exact pair_factor_le_exp_of_endpoint hu hc ha hb ha₀ hb₀ hsum hprod hend

theorem pProd_threshold_le_two {m : ℕ} (hm : 2 ≤ m) :
    pProd m (pThreshold m) ≤ 2 := by
  have hm₁ : 1 ≤ m := by omega
  have hm₀ : 0 < m := by omega
  have hpair :
      ∀ j ∈ Finset.range m,
        pFactor m (pThreshold m) j * pFactor m (pThreshold m) (m - 1 - j) ≤
          Real.exp (2 * scale m) := by
    intro j hj
    exact p_pair_le_exp hm (Finset.mem_range.mp hj)
  have hnonneg :
      ∀ j ∈ Finset.range m,
        0 ≤ pFactor m (pThreshold m) j * pFactor m (pThreshold m) (m - 1 - j) := by
    intro j hj
    exact p_pair_nonneg hm₁ (Finset.mem_range.mp hj)
  have hsqle : (pProd m (pThreshold m)) ^ 2 ≤ (Real.exp (2 * scale m)) ^ m := by
    calc
      (pProd m (pThreshold m)) ^ 2 =
          Finset.prod (Finset.range m)
            (fun j ↦ pFactor m (pThreshold m) j * pFactor m (pThreshold m) (m - 1 - j)) := by
        rw [pProd, sq_prod_range_eq_prod_reflect]
      _ ≤ Finset.prod (Finset.range m) (fun _ ↦ Real.exp (2 * scale m)) := by
        exact Finset.prod_le_prod hnonneg hpair
      _ = (Real.exp (2 * scale m)) ^ m := by
        simp
  have hpow : (Real.exp (2 * scale m)) ^ m = 4 := exp_two_scale_pow hm₀
  have hnonnegProd : 0 ≤ pProd m (pThreshold m) := by
    unfold pProd
    refine Finset.prod_nonneg ?_
    intro j hj
    unfold pFactor
    have hden : 0 < pThreshold m - (j + 1) := pThreshold_sub_succ_pos hm₁ (Finset.mem_range.mp hj)
    positivity
  have hsqle4 : (pProd m (pThreshold m)) ^ 2 ≤ 4 := by
    simpa [hpow] using hsqle
  nlinarith

theorem pProd_le_two {m : ℕ} (hm : 2 ≤ m) {k : ℝ} (hk : pThreshold m ≤ k) :
    pProd m k ≤ 2 := by
  refine (pProd_antitone hk ?_).trans (pProd_threshold_le_two hm)
  intro j hj
  exact pThreshold_sub_succ_pos (by omega) (Finset.mem_range.mp hj)

theorem attemptTen_part_a {s : ℕ} (hs : 1 ≤ s) {k : ℝ} (hk : pThreshold (2 * s) ≤ k) :
    pProd (2 * s) k ≤ 2 := by
  exact pProd_le_two (by omega) hk

theorem attemptTen_part_b {s : ℕ} (hs : 1 ≤ s) {k : ℝ} (hk : pThreshold (2 * s + 1) ≤ k) :
    pProd (2 * s + 1) k ≤ 2 := by
  exact pProd_le_two (by omega) hk

lemma q_endpoint_sum_le {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) / qThreshold m + (m : ℝ) / (qThreshold m - m + 1) ≤
      2 * scale m + scale m ^ 2 := by
  have hm₀ : 0 < m := by omega
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm₀)
  have hmℝ : (0 : ℝ) < m := by exact_mod_cast hm₀
  have hL : 0 < Real.log 2 := log_two_pos
  have hden : 0 < qThreshold m - m + 1 := qThreshold_sub_base_pos hm
  let D : ℝ := (m : ℝ) ^ 2 - (m : ℝ) * Real.log 2 + Real.log 2
  have hD_eq : qThreshold m - m + 1 = D / Real.log 2 := by
    dsimp [D]
    unfold qThreshold
    field_simp [hL.ne']
  have hD : 0 < D := by
    calc
      D = Real.log 2 * (qThreshold m - m + 1) := by
        rw [hD_eq]
        field_simp [hL.ne']
      _ > 0 := by
        positivity
  have haux : (m : ℝ) / (qThreshold m - m + 1) ≤ scale m + scale m ^ 2 := by
    rw [hD_eq, scale]
    field_simp [hL.ne', hm', hD.ne']
    have hbase : 0 ≤ Real.log 2 * (1 - Real.log 2) * (m : ℝ) + Real.log 2 ^ 2 := by
      have hOne : 0 ≤ 1 - Real.log 2 := by
        nlinarith [log_two_lt_one]
      have hprod : 0 ≤ Real.log 2 * (1 - Real.log 2) * (m : ℝ) := by
        positivity
      nlinarith [hprod]
    have hpoly : 0 ≤ D * ((m : ℝ) + Real.log 2) - (m : ℝ) ^ 3 := by
      dsimp [D]
      nlinarith [hbase]
    nlinarith [hpoly]
  calc
    (m : ℝ) / qThreshold m + (m : ℝ) / (qThreshold m - m + 1)
        = scale m + (m : ℝ) / (qThreshold m - m + 1) := by
          rw [qThreshold, scale]
          field_simp [hL.ne', hm']
    _ ≤ scale m + (scale m + scale m ^ 2) := by gcongr
    _ = 2 * scale m + scale m ^ 2 := by ring

lemma qFactor_antitone {m j : ℕ} {k₁ k₂ : ℝ}
    (hk : k₁ ≤ k₂) (hpos : 0 < k₁ - j) :
    qFactor m k₂ j ≤ qFactor m k₁ j := by
  simpa [qFactor] using
    one_add_div_antitone
      (c := (m : ℝ)) (d := (j : ℝ)) (k₁ := k₁) (k₂ := k₂)
      (by positivity) hk hpos

lemma qProd_antitone {m : ℕ} {k₁ k₂ : ℝ}
    (hk : k₁ ≤ k₂) (hpos : ∀ j ∈ Finset.range m, 0 < k₁ - j) :
    qProd m k₂ ≤ qProd m k₁ := by
  unfold qProd
  refine Finset.prod_le_prod ?_ ?_
  · intro j hj
    have hpos₂ : 0 < k₂ - j := by linarith [hpos j hj, hk]
    unfold qFactor
    positivity
  · intro j hj
    exact qFactor_antitone hk (hpos j hj)

lemma q_pair_nonneg {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    0 ≤ qFactor m (qThreshold m) j * qFactor m (qThreshold m) (m - 1 - j) := by
  have hjle : j ≤ m - 1 := Nat.le_pred_of_lt hj
  have hleft : 0 ≤ qFactor m (qThreshold m) j := by
    unfold qFactor
    have hden : 0 < qThreshold m - j := qThreshold_sub_pos hm hj
    positivity
  have hcast_reflect : ((m - 1 - j : ℕ) : ℝ) = m - 1 - j := by
    rw [Nat.cast_sub hjle, Nat.cast_sub hm]
    norm_num
  have hdeneq : qThreshold m - ((m - 1 - j : ℕ) : ℝ) = qThreshold m - m + 1 + j := by
    rw [hcast_reflect]
    ring
  have hright' : 0 ≤ 1 + (m : ℝ) / (qThreshold m - m + 1 + j) := by
    have hden : 0 < qThreshold m - m + 1 + j := qThreshold_sub_reflect_pos hm
    positivity
  have hright : 0 ≤ qFactor m (qThreshold m) (m - 1 - j) := by
    calc
      0 ≤ 1 + (m : ℝ) / (qThreshold m - m + 1 + j) := hright'
      _ = qFactor m (qThreshold m) (m - 1 - j) := by
        unfold qFactor
        rw [hdeneq]
  positivity

lemma q_pair_le_exp {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    qFactor m (qThreshold m) j * qFactor m (qThreshold m) (m - 1 - j) ≤
      Real.exp (2 * scale m) := by
  have hm₀ : 0 < m := by omega
  have hmℝ : (0 : ℝ) < m := by exact_mod_cast hm₀
  have hjle : j ≤ m - 1 := Nat.le_pred_of_lt hj
  have hcast_reflect : ((m - 1 - j : ℕ) : ℝ) = m - 1 - j := by
    rw [Nat.cast_sub hjle, Nat.cast_sub hm]
    norm_num
  have hdeneq : qThreshold m - ((m - 1 - j : ℕ) : ℝ) = qThreshold m - m + 1 + j := by
    rw [hcast_reflect]
    ring
  have hu : 0 ≤ scale m := scale_nonneg m
  have hc : 0 ≤ (m : ℝ) := by positivity
  have ha : 0 < qThreshold m - j := qThreshold_sub_pos hm hj
  have hb : 0 < qThreshold m - m + 1 + j := qThreshold_sub_reflect_pos hm
  have ha₀ : 0 < qThreshold m := by
    unfold qThreshold
    positivity
  have hb₀ : 0 < qThreshold m - m + 1 := qThreshold_sub_base_pos hm
  have hsum :
      qThreshold m - j + (qThreshold m - m + 1 + j) =
        qThreshold m + (qThreshold m - m + 1) := by
    ring
  have hj' : (j : ℝ) ≤ m - 1 := by exact_mod_cast hjle
  have hprod :
      qThreshold m * (qThreshold m - m + 1) ≤
        (qThreshold m - j) * (qThreshold m - m + 1 + j) := by
    nlinarith
  have hend :
      (m : ℝ) / qThreshold m + (m : ℝ) / (qThreshold m - m + 1) ≤
        2 * scale m + scale m ^ 2 := q_endpoint_sum_le hm
  calc
    qFactor m (qThreshold m) j * qFactor m (qThreshold m) (m - 1 - j) =
        (1 + (m : ℝ) / (qThreshold m - j)) *
          (1 + (m : ℝ) / (qThreshold m - m + 1 + j)) := by
      unfold qFactor
      rw [hdeneq]
    _ ≤ Real.exp (2 * scale m) := by
      exact pair_factor_le_exp_of_endpoint hu hc ha hb ha₀ hb₀ hsum hprod hend

theorem qProd_threshold_le_two {m : ℕ} (hm : 1 ≤ m) :
    qProd m (qThreshold m) ≤ 2 := by
  have hm₀ : 0 < m := by omega
  have hpair :
      ∀ j ∈ Finset.range m,
        qFactor m (qThreshold m) j * qFactor m (qThreshold m) (m - 1 - j) ≤
          Real.exp (2 * scale m) := by
    intro j hj
    exact q_pair_le_exp hm (Finset.mem_range.mp hj)
  have hnonneg :
      ∀ j ∈ Finset.range m,
        0 ≤ qFactor m (qThreshold m) j * qFactor m (qThreshold m) (m - 1 - j) := by
    intro j hj
    exact q_pair_nonneg hm (Finset.mem_range.mp hj)
  have hsqle : (qProd m (qThreshold m)) ^ 2 ≤ (Real.exp (2 * scale m)) ^ m := by
    calc
      (qProd m (qThreshold m)) ^ 2 =
          Finset.prod (Finset.range m)
            (fun j ↦ qFactor m (qThreshold m) j * qFactor m (qThreshold m) (m - 1 - j)) := by
        rw [qProd, sq_prod_range_eq_prod_reflect]
      _ ≤ Finset.prod (Finset.range m) (fun _ ↦ Real.exp (2 * scale m)) := by
        exact Finset.prod_le_prod hnonneg hpair
      _ = (Real.exp (2 * scale m)) ^ m := by
        simp
  have hpow : (Real.exp (2 * scale m)) ^ m = 4 := exp_two_scale_pow hm₀
  have hnonnegProd : 0 ≤ qProd m (qThreshold m) := by
    unfold qProd
    refine Finset.prod_nonneg ?_
    intro j hj
    unfold qFactor
    have hden : 0 < qThreshold m - j := qThreshold_sub_pos hm (Finset.mem_range.mp hj)
    positivity
  have hsqle4 : (qProd m (qThreshold m)) ^ 2 ≤ 4 := by
    simpa [hpow] using hsqle
  nlinarith

theorem qProd_le_two {m : ℕ} (hm : 1 ≤ m) {k : ℝ} (hk : qThreshold m ≤ k) :
    qProd m k ≤ 2 := by
  refine (qProd_antitone hk ?_).trans (qProd_threshold_le_two hm)
  intro j hj
  exact qThreshold_sub_pos hm (Finset.mem_range.mp hj)

theorem attemptTen_part_c {s : ℕ} (hs : 1 ≤ s) {k : ℝ} (hk : qThreshold (2 * s) ≤ k) :
    qProd (2 * s) k ≤ 2 := by
  exact qProd_le_two (by omega) hk

def rEndpointPoly (m : ℕ) : ℝ :=
  (2 - Real.log 2 - (Real.log 2) ^ 2) * (m : ℝ) ^ 3
    + (4 - 2 * Real.log 2 - (Real.log 2) ^ 2) * (m : ℝ) ^ 2
    + (2 - 2 * Real.log 2 - 3 * (Real.log 2) ^ 2 + 2 * (Real.log 2) ^ 3) * (m : ℝ)
    + (Real.log 2 - 3 * (Real.log 2) ^ 2 + 2 * (Real.log 2) ^ 3)

lemma rEndpointPoly_nonneg {m : ℕ} (hm : 2 ≤ m) : 0 ≤ rEndpointPoly m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h₁ : (1 : ℝ) / 2 < 2 - Real.log 2 - (Real.log 2) ^ 2 := by
    nlinarith [log_two_lt_one, log_two_sq_lt_half]
  have h₂ : (3 : ℝ) / 2 < 4 - 2 * Real.log 2 - (Real.log 2) ^ 2 := by
    nlinarith [log_two_lt_one, log_two_sq_lt_half]
  have h₃ : -(3 : ℝ) / 2 < 2 - 2 * Real.log 2 - 3 * (Real.log 2) ^ 2 + 2 * (Real.log 2) ^ 3 := by
    nlinarith [log_two_lt_one, log_two_sq_lt_half, log_two_pos]
  have h₄ : -(1 : ℝ) / 4 < Real.log 2 - 3 * (Real.log 2) ^ 2 + 2 * (Real.log 2) ^ 3 := by
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have h₁' : 0 ≤ 2 - Real.log 2 - (Real.log 2) ^ 2 - 1 / 2 := by
    nlinarith [h₁]
  have h₂' : 0 ≤ 4 - 2 * Real.log 2 - (Real.log 2) ^ 2 - 3 / 2 := by
    nlinarith [h₂]
  have h₃' : 0 ≤ 2 - 2 * Real.log 2 - 3 * (Real.log 2) ^ 2 + 2 * (Real.log 2) ^ 3 + 3 / 2 := by
    nlinarith [h₃]
  have hm₀ : 0 ≤ (m : ℝ) := by positivity
  have hmSq : 0 ≤ (m : ℝ) ^ 2 := by positivity
  have hmCube : 0 ≤ (m : ℝ) ^ 3 := by positivity
  have hfirst : 0 ≤ (2 - Real.log 2 - (Real.log 2) ^ 2 - 1 / 2) * (m : ℝ) ^ 3 := by
    exact mul_nonneg h₁' hmCube
  have hsecond : 0 ≤ (4 - 2 * Real.log 2 - (Real.log 2) ^ 2 - 3 / 2) * (m : ℝ) ^ 2 := by
    exact mul_nonneg h₂' hmSq
  have hthird :
      0 ≤ (2 - 2 * Real.log 2 - 3 * (Real.log 2) ^ 2 + 2 * (Real.log 2) ^ 3 + 3 / 2) * (m : ℝ) := by
    exact mul_nonneg h₃' hm₀
  have hfourth : 0 ≤ Real.log 2 - 3 * (Real.log 2) ^ 2 + 2 * (Real.log 2) ^ 3 + 1 / 4 := by
    nlinarith [h₄]
  have hdiff :
      0 ≤ rEndpointPoly m -
        ((1 : ℝ) / 2 * (m : ℝ) ^ 3 + (3 : ℝ) / 2 * (m : ℝ) ^ 2
          - (3 : ℝ) / 2 * (m : ℝ) - (1 : ℝ) / 4) := by
    unfold rEndpointPoly
    nlinarith [hfirst, hsecond, hthird, hfourth]
  have hbase :
      0 ≤
        (1 : ℝ) / 2 * (m : ℝ) ^ 3 + (3 : ℝ) / 2 * (m : ℝ) ^ 2
          - (3 : ℝ) / 2 * (m : ℝ) - (1 : ℝ) / 4 := by
    nlinarith
  nlinarith

lemma r_endpoint_sum_le {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) + 2) / (rThreshold m - 2) + ((m : ℝ) + 2) / (rThreshold m - m - 1) ≤
      2 * scale m + scale m ^ 2 := by
  have hm₁ : 1 ≤ m := by omega
  have hm₀ : 0 < m := by omega
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm₀)
  have hL : 0 < Real.log 2 := log_two_pos
  let B : ℝ := (m + 1) ^ 2 - 2 * Real.log 2
  let C : ℝ := (m + 1) ^ 2 - m * Real.log 2 - Real.log 2
  have hB_eq : rThreshold m - 2 = B / Real.log 2 := by
    dsimp [B]
    unfold rThreshold
    field_simp [hL.ne']
  have hC_eq : rThreshold m - m - 1 = C / Real.log 2 := by
    dsimp [C]
    unfold rThreshold
    field_simp [hL.ne']
  have hB : 0 < B := by
    calc
      B = Real.log 2 * (rThreshold m - 2) := by
        rw [hB_eq]
        field_simp [hL.ne']
      _ > 0 := by
        have hden : 0 < rThreshold m - 2 := by
          simpa using rThreshold_sub_left_pos hm₁ hm₀
        positivity
  have hC : 0 < C := by
    calc
      C = Real.log 2 * (rThreshold m - m - 1) := by
        rw [hC_eq]
        field_simp [hL.ne']
      _ > 0 := by
        have hden : 0 < rThreshold m - m - 1 := rThreshold_sub_base_pos hm₁
        positivity
  have hpoly := rEndpointPoly_nonneg hm
  unfold rEndpointPoly at hpoly
  have hcrossEq :
      (2 * (m : ℝ) + Real.log 2) * B * C -
        (m : ℝ) ^ 2 * ((m : ℝ) + 2) * (B + C) =
          rEndpointPoly m := by
    unfold rEndpointPoly
    dsimp [B, C]
    ring_nf
  have hcross :
      (m : ℝ) ^ 2 * ((m : ℝ) + 2) * (B + C) ≤
        (2 * (m : ℝ) + Real.log 2) * B * C := by
    have hnonneg :
        0 ≤ (2 * (m : ℝ) + Real.log 2) * B * C -
          (m : ℝ) ^ 2 * ((m : ℝ) + 2) * (B + C) := by
      rw [hcrossEq]
      positivity
    nlinarith
  have hBC : 0 < B * C := mul_pos hB hC
  have hdiv :
      (m : ℝ) ^ 2 * ((m : ℝ) + 2) * (1 / B + 1 / C) ≤
        2 * (m : ℝ) + Real.log 2 := by
    have hEqLeft :
        (m : ℝ) ^ 2 * ((m : ℝ) + 2) * (1 / B + 1 / C) =
          ((m : ℝ) ^ 2 * ((m : ℝ) + 2) * (B + C)) / (B * C) := by
      field_simp [hB.ne', hC.ne']
      ring
    rw [hEqLeft]
    exact (div_le_iff₀ hBC).2 (by simpa [mul_assoc] using hcross)
  have hmSq : ((m : ℝ) ^ 2) ≠ 0 := by positivity
  calc
    ((m : ℝ) + 2) / (rThreshold m - 2) + ((m : ℝ) + 2) / (rThreshold m - m - 1)
        = Real.log 2 * ((m : ℝ) + 2) / B + Real.log 2 * ((m : ℝ) + 2) / C := by
          rw [hB_eq, hC_eq]
          field_simp [hL.ne', hB.ne', hC.ne']
    _ = (Real.log 2 / (m : ℝ) ^ 2) *
          ((m : ℝ) ^ 2 * ((m : ℝ) + 2) * (1 / B + 1 / C)) := by
            field_simp [hmSq, hB.ne', hC.ne']
    _ ≤ (Real.log 2 / (m : ℝ) ^ 2) * (2 * (m : ℝ) + Real.log 2) := by
          exact mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ Real.log 2 / (m : ℝ) ^ 2)
    _ = 2 * scale m + scale m ^ 2 := by
          unfold scale
          field_simp [hmSq]

lemma rFactor_antitone {m j : ℕ} {k₁ k₂ : ℝ}
    (hk : k₁ ≤ k₂) (hpos : 0 < k₁ - (j + 2)) :
    rFactor m k₂ j ≤ rFactor m k₁ j := by
  simpa [rFactor] using
    one_add_div_antitone
      (c := (m : ℝ) + 2) (d := (j : ℝ) + 2) (k₁ := k₁) (k₂ := k₂)
      (by positivity) hk hpos

lemma rProd_antitone {m : ℕ} {k₁ k₂ : ℝ}
    (hk : k₁ ≤ k₂) (hpos : ∀ j ∈ Finset.range m, 0 < k₁ - (j + 2)) :
    rProd m k₂ ≤ rProd m k₁ := by
  unfold rProd
  refine Finset.prod_le_prod ?_ ?_
  · intro j hj
    have hpos₂ : 0 < k₂ - (j + 2) := by linarith [hpos j hj, hk]
    unfold rFactor
    positivity
  · intro j hj
    exact rFactor_antitone hk (hpos j hj)

lemma r_pair_nonneg {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    0 ≤ rFactor m (rThreshold m) j * rFactor m (rThreshold m) (m - 1 - j) := by
  have hjle : j ≤ m - 1 := Nat.le_pred_of_lt hj
  have hleft : 0 ≤ rFactor m (rThreshold m) j := by
    unfold rFactor
    have hden : 0 < rThreshold m - (j + 2) := rThreshold_sub_left_pos hm hj
    positivity
  have hcast_reflect : ((m - 1 - j : ℕ) : ℝ) = m - 1 - j := by
    rw [Nat.cast_sub hjle, Nat.cast_sub hm]
    norm_num
  have hdeneq :
      rThreshold m - (((m - 1 - j : ℕ) : ℝ) + 2) = rThreshold m - m - 1 + j := by
    rw [hcast_reflect]
    ring
  have hright' : 0 ≤ 1 + ((m : ℝ) + 2) / (rThreshold m - m - 1 + j) := by
    have hden : 0 < rThreshold m - m - 1 + j := rThreshold_sub_reflect_pos hm
    positivity
  have hright : 0 ≤ rFactor m (rThreshold m) (m - 1 - j) := by
    calc
      0 ≤ 1 + ((m : ℝ) + 2) / (rThreshold m - m - 1 + j) := hright'
      _ = rFactor m (rThreshold m) (m - 1 - j) := by
        unfold rFactor
        rw [hdeneq]
  positivity

lemma r_pair_le_exp {m j : ℕ} (hm : 2 ≤ m) (hj : j < m) :
    rFactor m (rThreshold m) j * rFactor m (rThreshold m) (m - 1 - j) ≤
      Real.exp (2 * scale m) := by
  have hm₁ : 1 ≤ m := by omega
  have hjle : j ≤ m - 1 := Nat.le_pred_of_lt hj
  have hcast_reflect : ((m - 1 - j : ℕ) : ℝ) = m - 1 - j := by
    rw [Nat.cast_sub hjle, Nat.cast_sub hm₁]
    norm_num
  have hdeneq :
      rThreshold m - (((m - 1 - j : ℕ) : ℝ) + 2) = rThreshold m - m - 1 + j := by
    rw [hcast_reflect]
    ring
  have hu : 0 ≤ scale m := scale_nonneg m
  have hc : 0 ≤ (m : ℝ) + 2 := by positivity
  have ha : 0 < rThreshold m - (j + 2) := rThreshold_sub_left_pos hm₁ hj
  have hb : 0 < rThreshold m - m - 1 + j := rThreshold_sub_reflect_pos hm₁
  have ha₀ : 0 < rThreshold m - 2 := by
    have hm₀ : 0 < m := by omega
    simpa using rThreshold_sub_left_pos hm₁ hm₀
  have hb₀ : 0 < rThreshold m - m - 1 := rThreshold_sub_base_pos hm₁
  have hsum :
      rThreshold m - (j + 2) + (rThreshold m - m - 1 + j) =
        (rThreshold m - 2) + (rThreshold m - m - 1) := by
    ring
  have hj' : (j : ℝ) ≤ m - 1 := by exact_mod_cast hjle
  have hprod :
      (rThreshold m - 2) * (rThreshold m - m - 1) ≤
        (rThreshold m - (j + 2)) * (rThreshold m - m - 1 + j) := by
    nlinarith
  have hend :
      ((m : ℝ) + 2) / (rThreshold m - 2) + ((m : ℝ) + 2) / (rThreshold m - m - 1) ≤
        2 * scale m + scale m ^ 2 := r_endpoint_sum_le hm
  calc
    rFactor m (rThreshold m) j * rFactor m (rThreshold m) (m - 1 - j) =
        (1 + ((m : ℝ) + 2) / (rThreshold m - (j + 2))) *
          (1 + ((m : ℝ) + 2) / (rThreshold m - m - 1 + j)) := by
      unfold rFactor
      rw [hdeneq]
    _ ≤ Real.exp (2 * scale m) := by
      exact pair_factor_le_exp_of_endpoint hu hc ha hb ha₀ hb₀ hsum hprod hend

theorem rProd_threshold_le_two {m : ℕ} (hm : 2 ≤ m) :
    rProd m (rThreshold m) ≤ 2 := by
  have hm₁ : 1 ≤ m := by omega
  have hm₀ : 0 < m := by omega
  have hpair :
      ∀ j ∈ Finset.range m,
        rFactor m (rThreshold m) j * rFactor m (rThreshold m) (m - 1 - j) ≤
          Real.exp (2 * scale m) := by
    intro j hj
    exact r_pair_le_exp hm (Finset.mem_range.mp hj)
  have hnonneg :
      ∀ j ∈ Finset.range m,
        0 ≤ rFactor m (rThreshold m) j * rFactor m (rThreshold m) (m - 1 - j) := by
    intro j hj
    exact r_pair_nonneg hm₁ (Finset.mem_range.mp hj)
  have hsqle : (rProd m (rThreshold m)) ^ 2 ≤ (Real.exp (2 * scale m)) ^ m := by
    calc
      (rProd m (rThreshold m)) ^ 2 =
          Finset.prod (Finset.range m)
            (fun j ↦ rFactor m (rThreshold m) j * rFactor m (rThreshold m) (m - 1 - j)) := by
        rw [rProd, sq_prod_range_eq_prod_reflect]
      _ ≤ Finset.prod (Finset.range m) (fun _ ↦ Real.exp (2 * scale m)) := by
        exact Finset.prod_le_prod hnonneg hpair
      _ = (Real.exp (2 * scale m)) ^ m := by
        simp
  have hpow : (Real.exp (2 * scale m)) ^ m = 4 := exp_two_scale_pow hm₀
  have hnonnegProd : 0 ≤ rProd m (rThreshold m) := by
    unfold rProd
    refine Finset.prod_nonneg ?_
    intro j hj
    unfold rFactor
    have hden : 0 < rThreshold m - (j + 2) := rThreshold_sub_left_pos hm₁ (Finset.mem_range.mp hj)
    positivity
  have hsqle4 : (rProd m (rThreshold m)) ^ 2 ≤ 4 := by
    simpa [hpow] using hsqle
  nlinarith

theorem rProd_le_two {m : ℕ} (hm : 2 ≤ m) {k : ℝ} (hk : rThreshold m ≤ k) :
    rProd m k ≤ 2 := by
  refine (rProd_antitone hk ?_).trans (rProd_threshold_le_two hm)
  intro j hj
  exact rThreshold_sub_left_pos (by omega) (Finset.mem_range.mp hj)

theorem attemptTen_part_d {s : ℕ} (hs : 1 ≤ s) {k : ℝ} (hk : rThreshold (2 * s) ≤ k) :
    rProd (2 * s) k ≤ 2 := by
  exact rProd_le_two (by omega) hk

end HilbertDepth
