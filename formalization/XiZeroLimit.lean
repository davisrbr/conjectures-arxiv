import Mathlib
import XiZeroLimit.Analytic

open scoped BigOperators Polynomial
open Filter
open PowerSeries

namespace XiZeroLimit

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

theorem sumInv_pos (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    0 < ∑ i, (f i)⁻¹ := by
  rcases exists_eq_smallestValue f with ⟨i, hi⟩
  calc
    0 < (f i)⁻¹ := inv_pos.mpr (hf i)
    _ ≤ ∑ j, (f j)⁻¹ := by
      refine Finset.single_le_sum (s := Finset.univ) (a := i) (f := fun j : ι => (f j)⁻¹) ?_ ?_
      · intro j hj
        exact inv_nonneg.mpr (le_of_lt (hf j))
      · simp

theorem inv_smallestValue_le_sumInv (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    (smallestValue f)⁻¹ ≤ ∑ i, (f i)⁻¹ := by
  rcases exists_eq_smallestValue f with ⟨i, hi⟩
  calc
    (smallestValue f)⁻¹ = (f i)⁻¹ := by rw [← hi]
    _ ≤ ∑ j, (f j)⁻¹ := by
      refine Finset.single_le_sum (s := Finset.univ) (a := i) (f := fun j : ι => (f j)⁻¹) ?_ ?_
      · intro j hj
        exact inv_nonneg.mpr (le_of_lt (hf j))
      · simp

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
  have hsumPos : 0 < ∑ i, (f i)⁻¹ := sumInv_pos f hf
  refine (le_div_iff₀ hsumPos).2 ?_
  calc
    smallestValue f * (∑ i, (f i)⁻¹)
        ≤ smallestValue f * ((Fintype.card ι : ℝ) * (smallestValue f)⁻¹) := by
          exact mul_le_mul_of_nonneg_left hsumLe (le_of_lt hsmallPos)
    _ = (Fintype.card ι : ℝ) := by
      ring_nf
      field_simp [hsmallPos.ne']

end SmallestValue

section RootProduct

variable {ι : Type*} [Fintype ι]

/-- The normalized factorized polynomial `∏ᵢ (1 - y / rootsᵢ)`. -/
noncomputable def rootProduct (roots : ι → ℝ) (y : ℝ) : ℝ := by
  classical
  exact ∏ i, (1 - y / roots i)

theorem rootProduct_zero (roots : ι → ℝ) :
    rootProduct roots 0 = 1 := by
  simp [rootProduct]

theorem hasDerivAt_rootFactor_zero (r : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 1 - y / r) (-(r⁻¹)) 0 := by
  simpa using ((hasDerivAt_id 0).div_const r).const_sub (1 : ℝ)

theorem differentiableAt_rootProduct_zero (roots : ι → ℝ) :
    DifferentiableAt ℝ (rootProduct roots) 0 := by
  classical
  have hprod :
      (∏ i : ι, fun y : ℝ ↦ 1 - y / roots i) = fun y : ℝ ↦ ∏ i : ι, (1 - y / roots i) := by
    ext y
    simp
  change DifferentiableAt ℝ (fun y : ℝ ↦ ∏ i : ι, (1 - y / roots i)) 0
  simpa [hprod] using
    (DifferentiableAt.finset_prod (u := (Finset.univ : Finset ι))
      (f := fun i ↦ fun y : ℝ ↦ 1 - y / roots i) fun i hi ↦
        (hasDerivAt_rootFactor_zero (roots i)).differentiableAt)

theorem deriv_rootProduct_zero (roots : ι → ℝ) :
    deriv (rootProduct roots) 0 = -∑ i, (roots i)⁻¹ := by
  classical
  have hprod :
      (∏ i : ι, fun y : ℝ ↦ 1 - y / roots i) = fun y : ℝ ↦ ∏ i : ι, (1 - y / roots i) := by
    ext y
    simp
  change deriv (fun y : ℝ ↦ ∏ i : ι, (1 - y / roots i)) 0 = -∑ i, (roots i)⁻¹
  simpa [hprod, hasDerivAt_rootFactor_zero] using
    (deriv_finset_prod (u := (Finset.univ : Finset ι))
      (f := fun i ↦ fun y : ℝ ↦ 1 - y / roots i)
      (x := 0) fun i hi ↦
        (hasDerivAt_rootFactor_zero (roots i)).differentiableAt)

/--
For a factorization `P(y) = c ∏ᵢ (1 - y / rootsᵢ)`, the logarithmic derivative at `0` is the sum of
the reciprocal roots.
-/
theorem neg_deriv_scaledRootProduct_div_eq_sumInv
    (roots : ι → ℝ) (c : ℝ) (hc : c ≠ 0) :
    -(deriv (fun y ↦ c * rootProduct roots y) 0) / ((fun y ↦ c * rootProduct roots y) 0) =
      ∑ i, (roots i)⁻¹ := by
  have hd : DifferentiableAt ℝ (rootProduct roots) 0 := differentiableAt_rootProduct_zero roots
  rw [deriv_const_mul c hd]
  simp [rootProduct_zero, deriv_rootProduct_zero, hc]

end RootProduct

section ConcreteXi

/--
The coefficient of the type-B Eulerian polynomial `B_m(z)`, defined through the finite numerator
formula coming from
`B_m(z) / (1 - z)^(m + 1) = ∑_{r ≥ 0} (2 r + 1)^m z^r`.
-/
noncomputable def typeBEulerianCoeff (m k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun j =>
    (-1 : ℝ) ^ j * (Nat.choose (m + 1) j : ℝ) * (2 * (k - j) + 1 : ℝ) ^ m

/--
The inner combinatorial coefficient in the explicit formula for the adapted Xi polynomial
`\widetilde Ξ_n(y) = ∑_{t=0}^{n-1} C^(B)_{n,t} y^t`.
-/
noncomputable def xiInnerCoeff (n k t : ℕ) : ℝ :=
  Finset.sum (Finset.range (min k t + 1)) fun i =>
    (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) *
      (Nat.choose (2 * n - 2 * k - 1) (2 * (t - i) + 1) : ℝ)

/-- The unscaled coefficient `C^(B)_{n,t}` from the explicit adapted Xi formula. -/
noncomputable def rawAdaptedXiCoeff (n t : ℕ) : ℝ :=
  Finset.sum (Finset.range n) fun k =>
    typeBEulerianCoeff (2 * n - 1) k * (-1 : ℝ) ^ k * xiInnerCoeff n k t

/--
The adapted Xi polynomial, up to the nonzero scalar factor from the paper. This normalization keeps
the same roots and the same coefficient ratio `-coeff 1 / coeff 0`.
-/
noncomputable def rawAdaptedXi (n : ℕ) : ℝ[X] :=
  Finset.sum (Finset.range n) fun t => Polynomial.C (rawAdaptedXiCoeff n t) * Polynomial.X ^ t

theorem coeff_rawAdaptedXi (n t : ℕ) :
    (rawAdaptedXi n).coeff t = if t < n then rawAdaptedXiCoeff n t else 0 := by
  unfold rawAdaptedXi
  simp

private theorem xiInnerCoeff_zero (n k : ℕ) :
    xiInnerCoeff n k 0 = (((2 * n - 2 * k - 1 : ℕ) : ℝ)) := by
  unfold xiInnerCoeff
  simp

theorem coeff_zero_rawAdaptedXi (n : ℕ) :
    (rawAdaptedXi n).coeff 0 =
      Finset.sum (Finset.range n) fun k =>
        typeBEulerianCoeff (2 * n - 1) k * (-1 : ℝ) ^ k * (((2 * n - 2 * k - 1 : ℕ) : ℝ)) := by
  cases n with
  | zero =>
      simp [rawAdaptedXi, rawAdaptedXiCoeff]
  | succ n =>
      rw [coeff_rawAdaptedXi]
      simp [rawAdaptedXiCoeff, xiInnerCoeff_zero]

private theorem cast_choose_three_of_ge_three (s : ℕ) (hs : 3 ≤ s) :
    (Nat.choose s 3 : ℝ) = (s : ℝ) * (s - 1) * (s - 2) / 6 := by
  have hnat : s.choose 3 * 3 = s.choose 2 * (s - 2) := Nat.choose_succ_right_eq s 2
  have hstep : (Nat.choose s 3 : ℝ) * 3 = (Nat.choose s 2 : ℝ) * (((s - 2 : ℕ) : ℝ)) := by
    simpa [Nat.cast_mul] using congrArg (fun m : ℕ => (m : ℝ)) hnat
  have hdiv : (Nat.choose s 3 : ℝ) = (Nat.choose s 2 : ℝ) * (s - 2 : ℝ) / 3 := by
    have hs1 : 1 ≤ s := by omega
    have hs2 : 2 ≤ s := by omega
    refine (eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)).2 ?_
    simpa [Nat.cast_sub hs1, Nat.cast_sub hs2, mul_comm, mul_left_comm, mul_assoc] using hstep
  rw [hdiv, Nat.cast_choose_two]
  ring

private theorem xiInnerCoeff_one_eq_choose_sub (n k : ℕ) (hk : k < n) :
    xiInnerCoeff n k 1 =
      (Nat.choose (2 * n - 2 * k - 1) 3 : ℝ) -
        (k : ℝ) * (((2 * n - 2 * k - 1 : ℕ) : ℝ)) := by
  cases k with
  | zero =>
      unfold xiInnerCoeff
      simp
  | succ k =>
      unfold xiInnerCoeff
      have hmin : min (k + 1) 1 = 1 := by omega
      rw [hmin]
      norm_num [Finset.sum_range_succ]
      ring

private theorem xiInnerCoeff_one_of_lt (n k : ℕ) (hk : k < n) :
    xiInnerCoeff n k 1 =
      (((2 * n - 2 * k - 1 : ℕ) : ℝ) ^ 3 -
        (6 * n - 5 : ℝ) * (2 * n - 2 * k - 1 : ℝ)) / 6 := by
  rw [xiInnerCoeff_one_eq_choose_sub n k hk]
  by_cases hkn : k + 1 = n
  · have hs : 2 * n - 2 * k - 1 = 1 := by omega
    subst n
    simp [hs]
    ring_nf
  · have hs : 3 ≤ 2 * n - 2 * k - 1 := by omega
    rw [cast_choose_three_of_ge_three _ hs]
    field_simp
    have hk' : k ≤ n := Nat.le_of_lt hk
    have hcast :
        (((2 * n - 2 * k - 1 : ℕ) : ℝ)) = 2 * ((n : ℝ) - k) - 1 := by
      have hsub1 : 2 * k ≤ 2 * n := by omega
      have hsub2 : 1 ≤ 2 * n - 2 * k := by omega
      rw [Nat.cast_sub hsub2, Nat.cast_sub hsub1]
      norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
      ring
    rw [hcast]
    ring_nf

theorem coeff_one_rawAdaptedXi (n : ℕ) :
    (rawAdaptedXi n).coeff 1 =
      Finset.sum (Finset.range n) fun k =>
        typeBEulerianCoeff (2 * n - 1) k * (-1 : ℝ) ^ k *
          ((((2 * n - 2 * k - 1 : ℕ) : ℝ) ^ 3 -
              (6 * n - 5 : ℝ) * (2 * n - 2 * k - 1 : ℝ)) / 6) := by
  cases n with
  | zero =>
      simp [rawAdaptedXi, rawAdaptedXiCoeff]
  | succ n =>
      by_cases hlt : 1 < n + 1
      · rw [coeff_rawAdaptedXi]
        simp [rawAdaptedXiCoeff, hlt]
        change
          Finset.sum (Finset.range (n + 1)) (fun k : ℕ =>
            typeBEulerianCoeff (2 * (n + 1) - 1) k * (-1 : ℝ) ^ k * xiInnerCoeff (n + 1) k 1) =
            Finset.sum (Finset.range (n + 1)) (fun k : ℕ =>
              typeBEulerianCoeff (2 * (n + 1) - 1) k * (-1 : ℝ) ^ k *
                ((((2 * (n + 1) - 2 * k - 1 : ℕ) : ℝ) ^ 3 -
                    (6 * (n + 1) - 5 : ℝ) * (2 * (n + 1) - 2 * k - 1 : ℝ)) / 6))
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [xiInnerCoeff_one_of_lt (n + 1) k (Finset.mem_range.mp hk)]
        norm_num [Nat.cast_add, Nat.cast_mul]
      · have hn : n = 0 := by omega
        subst n
        rw [coeff_rawAdaptedXi]
        norm_num [rawAdaptedXiCoeff, xiInnerCoeff, typeBEulerianCoeff]

/-- The solver indexing: `solverRawAdaptedXi n` is the `(n + 2)`nd adapted Xi polynomial. -/
noncomputable def solverRawAdaptedXi (n : ℕ) : ℝ[X] :=
  rawAdaptedXi (n + 2)

theorem coeff_solverRawAdaptedXi (n t : ℕ) :
    (solverRawAdaptedXi n).coeff t = if t < n + 2 then rawAdaptedXiCoeff (n + 2) t else 0 := by
  simpa [solverRawAdaptedXi] using coeff_rawAdaptedXi (n + 2) t

end ConcreteXi

section SechDerivativePolynomials

/-- The reciprocal hyperbolic cosine, written explicitly to avoid introducing a new global name. -/
noncomputable abbrev realSech (x : ℝ) : ℝ := (Real.cosh x)⁻¹

/-- The derivative update for the polynomial factor in `iteratedDeriv n sech`. -/
noncomputable def sechDerivPolyStep (p : ℝ[X]) : ℝ[X] :=
  (1 - Polynomial.X ^ 2) * p.derivative - Polynomial.X * p

/--
`sechDerivPoly n` is the polynomial in `tanh x` such that
`iteratedDeriv n sech x = sech x * sechDerivPoly n (tanh x)`.
-/
noncomputable def sechDerivPoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => sechDerivPolyStep (sechDerivPoly n)

theorem hasDerivAt_realSech (x : ℝ) :
    HasDerivAt realSech (-(realSech x * Real.tanh x)) x := by
  have hcosh : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hne : Real.cosh x ≠ 0 := by positivity
  convert hcosh.inv hne using 1
  simp [realSech, Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, pow_two,
    mul_comm, mul_assoc]

theorem contDiff_realSech (n : ℕ) : ContDiff ℝ n realSech := by
  simpa [realSech] using Real.contDiff_cosh.inv (fun x => by
    exact (Real.cosh_pos x).ne')

theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hsinh : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
  have hcosh : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hne : Real.cosh x ≠ 0 := by positivity
  convert hsinh.div hcosh hne using 1
  · funext y
    exact Real.tanh_eq_sinh_div_cosh y
  have htanh : Real.tanh x * Real.cosh x = Real.sinh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hne]
  have htanhSq : Real.tanh x ^ 2 * Real.cosh x ^ 2 = Real.sinh x ^ 2 := by
    calc
      Real.tanh x ^ 2 * Real.cosh x ^ 2 = (Real.tanh x * Real.cosh x) ^ 2 := by ring
      _ = Real.sinh x ^ 2 := by rw [htanh]
  have hcosh2 : Real.cosh x ^ 2 ≠ 0 := by exact pow_ne_zero 2 hne
  have hquot :
      (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
        1 / Real.cosh x ^ 2 := by
    field_simp [hcosh2]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have htarget : 1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
    field_simp [Real.tanh_eq_sinh_div_cosh, hne, hcosh2]
    nlinarith [Real.cosh_sq_sub_sinh_sq x, htanhSq]
  exact htarget.trans hquot.symm

theorem hasDerivAt_polyEval_tanh (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ p.eval (Real.tanh y))
      (p.derivative.eval (Real.tanh x) * (1 - Real.tanh x ^ 2)) x := by
  simpa using (p.hasDerivAt (Real.tanh x)).comp x (hasDerivAt_tanh x)

private theorem deriv_sechForm (p : ℝ[X]) (x : ℝ) :
    deriv (fun y : ℝ ↦ realSech y * p.eval (Real.tanh y)) x =
      realSech x * (sechDerivPolyStep p).eval (Real.tanh x) := by
  have h1 := hasDerivAt_realSech x
  have h2 := hasDerivAt_polyEval_tanh p x
  have h := (h1.mul h2).deriv
  calc
    deriv (fun y : ℝ ↦ realSech y * p.eval (Real.tanh y)) x =
        -(realSech x * (Real.tanh x * p.eval (Real.tanh x))) +
          realSech x * ((1 - Real.tanh x ^ 2) * p.derivative.eval (Real.tanh x)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using h
    _ =
        realSech x *
          (((1 - Real.tanh x ^ 2) * p.derivative.eval (Real.tanh x)) -
            Real.tanh x * p.eval (Real.tanh x)) := by
              ring
    _ = realSech x * (sechDerivPolyStep p).eval (Real.tanh x) := by
          simp [sechDerivPolyStep, mul_add, add_mul, sub_eq_add_neg,
            mul_comm, mul_left_comm, mul_assoc]

theorem sechDerivPoly_eval :
    ∀ n x,
      iteratedDeriv n realSech x =
        realSech x * (sechDerivPoly n).eval (Real.tanh x)
  | 0, x => by simp [realSech, sechDerivPoly]
  | n + 1, x => by
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv n realSech =
            fun y : ℝ ↦ realSech y * (sechDerivPoly n).eval (Real.tanh y) := by
        funext y
        exact sechDerivPoly_eval n y
      rw [hfun]
      simpa [sechDerivPoly] using deriv_sechForm (sechDerivPoly n) x

/-- The weighted evaluation `sqrt(1 - x^2) * p(x)` on `[-1,1]`. -/
noncomputable def weightedSechPolyEval (p : ℝ[X]) (x : ℝ) : ℝ :=
  Real.sqrt (1 - x ^ 2) * p.eval x

private theorem hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ ↦ Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hsq :
      HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-(2 * x)) x := by
    have htmp := (((hasDerivAt_id x).mul (hasDerivAt_id x)).const_sub (1 : ℝ))
    convert htmp using 1
    · funext y
      simp [pow_two]
    · simp [two_mul, one_mul]
  have hpos : 0 < 1 - x ^ 2 := by
    nlinarith [hx.1, hx.2]
  have hs := hsq.sqrt hpos.ne'
  convert hs using 1
  field_simp [hpos.ne']

private theorem hasDerivAt_weightedSechPolyEval (p : ℝ[X]) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (weightedSechPolyEval p)
      ((sechDerivPolyStep p).eval x / Real.sqrt (1 - x ^ 2)) x := by
  have h1 := hasDerivAt_sqrt_one_sub_sq hx
  have h2 : HasDerivAt (fun y : ℝ ↦ p.eval y) (p.derivative.eval x) x := p.hasDerivAt x
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 := by
    apply Real.sqrt_ne_zero'.2
    nlinarith [hx.1, hx.2]
  convert h1.mul h2 using 1
  · have hsq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := by
      rw [sq, Real.mul_self_sqrt]
      nlinarith [hx.1, hx.2]
    field_simp [hsqrt]
    rw [hsq]
    have hstep :
        (sechDerivPolyStep p).eval x =
          -(x * p.eval x) - x ^ 2 * p.derivative.eval x + p.derivative.eval x := by
      simp [sechDerivPolyStep, sub_eq_add_neg, mul_add, add_mul,
        mul_comm, mul_left_comm, mul_assoc]
      ring
    rw [hstep]
    ring

private theorem continuousOn_weightedSechPolyEval (p : ℝ[X]) :
    ContinuousOn (weightedSechPolyEval p) (Set.Icc (-1 : ℝ) 1) := by
  have hsq : ContinuousOn (fun x : ℝ ↦ 1 - x ^ 2) (Set.Icc (-1 : ℝ) 1) := by
    simpa using (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hsqrt : ContinuousOn (fun x : ℝ ↦ Real.sqrt (1 - x ^ 2)) (Set.Icc (-1 : ℝ) 1) := by
    exact ContinuousOn.sqrt hsq
  exact hsqrt.mul p.continuous.continuousOn

/-- The endpoint tuple `[-1, roots..., 1]` used in the Rolle induction. -/
noncomputable def rootEndpoints {n : ℕ} (roots : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  Fin.cons (-1) (Fin.snoc roots 1)

private theorem rootEndpoints_cases {n : ℕ} (roots : Fin n → ℝ) (j : Fin (n + 2)) :
    rootEndpoints roots j = -1 ∨
      rootEndpoints roots j = 1 ∨ ∃ i : Fin n, rootEndpoints roots j = roots i := by
  cases j using Fin.cases with
  | zero =>
      left
      simp [rootEndpoints]
  | succ j =>
      cases j using Fin.lastCases with
      | last =>
          right
          left
          simp [rootEndpoints]
      | cast i =>
          right
          right
          refine ⟨i, ?_⟩
          simp [rootEndpoints]

private theorem rootEndpoints_mem_Icc {n : ℕ} (roots : Fin n → ℝ)
    (hmem : ∀ i, roots i ∈ Set.Ioo (-1 : ℝ) 1) (j : Fin (n + 2)) :
    rootEndpoints roots j ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases rootEndpoints_cases roots j with hneg | hrest
  · simpa [hneg]
  · rcases hrest with hone | ⟨i, hi⟩
    · simpa [hone]
    · simpa [hi] using ⟨le_of_lt (hmem i).1, le_of_lt (hmem i).2⟩

private theorem weightedSechPolyEval_rootEndpoints_eq_zero {n : ℕ} (p : ℝ[X])
    (roots : Fin n → ℝ) (hroot : ∀ i, p.eval (roots i) = 0) (j : Fin (n + 2)) :
    weightedSechPolyEval p (rootEndpoints roots j) = 0 := by
  rcases rootEndpoints_cases roots j with hneg | hrest
  · rw [hneg, weightedSechPolyEval]
    simp
  · rcases hrest with hone | ⟨i, hi⟩
    · rw [hone, weightedSechPolyEval]
      simp
    · simp [weightedSechPolyEval, hi, hroot i]

private theorem strictMono_rootEndpoints {n : ℕ} {roots : Fin n → ℝ}
    (hmono : StrictMono roots)
    (hmem : ∀ i, roots i ∈ Set.Ioo (-1 : ℝ) 1) :
    StrictMono (rootEndpoints roots) := by
  refine (Fin.strictMono_iff_lt_succ (f := rootEndpoints roots)).2 ?_
  intro i
  cases i using Fin.cases with
  | zero =>
      cases n with
      | zero =>
          simp [rootEndpoints, Fin.snoc]
      | succ n =>
          simpa [rootEndpoints] using (hmem 0).1
  | succ j =>
      cases n with
      | zero =>
          exact Fin.elim0 j
      | succ n =>
          simp [rootEndpoints, Fin.cons_succ]
          cases j using Fin.lastCases with
          | last =>
              simpa [Fin.snoc_castSucc, Fin.snoc_last] using (hmem (Fin.last n)).2
          | cast k =>
              simpa [Fin.snoc_castSucc, ← Fin.castSucc_succ] using hmono k.castSucc_lt_succ

private theorem exists_strictMono_roots_step
    {n : ℕ} {p : ℝ[X]}
    (roots : Fin n → ℝ)
    (hmono : StrictMono roots)
    (hmem : ∀ i, roots i ∈ Set.Ioo (-1 : ℝ) 1)
    (hroot : ∀ i, p.eval (roots i) = 0) :
    ∃ roots' : Fin (n + 1) → ℝ,
      StrictMono roots' ∧
      (∀ i, roots' i ∈ Set.Ioo (-1 : ℝ) 1) ∧
      (∀ i, (sechDerivPolyStep p).eval (roots' i) = 0) := by
  let a : Fin (n + 2) → ℝ := rootEndpoints roots
  have ha : StrictMono a := strictMono_rootEndpoints hmono hmem
  have hexists :
      ∀ i : Fin (n + 1),
        ∃ c ∈ Set.Ioo (a (Fin.castSucc i)) (a i.succ), (sechDerivPolyStep p).eval c = 0 := by
    intro i
    have hab : a (Fin.castSucc i) < a i.succ :=
      (Fin.strictMono_iff_lt_succ (f := a)).1 ha i
    have hleft : a (Fin.castSucc i) ∈ Set.Icc (-1 : ℝ) 1 :=
      rootEndpoints_mem_Icc roots hmem (Fin.castSucc i)
    have hright : a i.succ ∈ Set.Icc (-1 : ℝ) 1 :=
      rootEndpoints_mem_Icc roots hmem i.succ
    have hsubset :
        Set.Icc (a (Fin.castSucc i)) (a i.succ) ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro x hx
      exact ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩
    have hfc :
        ContinuousOn (weightedSechPolyEval p) (Set.Icc (a (Fin.castSucc i)) (a i.succ)) :=
      (continuousOn_weightedSechPolyEval p).mono hsubset
    have hzero :
        weightedSechPolyEval p (a (Fin.castSucc i)) =
          weightedSechPolyEval p (a i.succ) := by
      rw [weightedSechPolyEval_rootEndpoints_eq_zero p roots hroot (Fin.castSucc i),
        weightedSechPolyEval_rootEndpoints_eq_zero p roots hroot i.succ]
    have hderiv :
        ∀ x ∈ Set.Ioo (a (Fin.castSucc i)) (a i.succ),
          HasDerivAt (weightedSechPolyEval p)
            ((sechDerivPolyStep p).eval x / Real.sqrt (1 - x ^ 2)) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by
        exact ⟨lt_of_le_of_lt hleft.1 hx.1, lt_of_lt_of_le hx.2 hright.2⟩
      exact hasDerivAt_weightedSechPolyEval p hx'
    rcases exists_hasDerivAt_eq_zero hab hfc hzero hderiv with ⟨c, hc, hc0⟩
    have hc' : c ∈ Set.Ioo (-1 : ℝ) 1 := by
      exact ⟨lt_of_le_of_lt hleft.1 hc.1, lt_of_lt_of_le hc.2 hright.2⟩
    have hsqrt : Real.sqrt (1 - c ^ 2) ≠ 0 := by
      apply Real.sqrt_ne_zero'.2
      nlinarith [hc'.1, hc'.2]
    have hc0' := hc0
    field_simp [hsqrt] at hc0'
    exact ⟨c, hc, by simpa using hc0'⟩
  classical
  let roots' : Fin (n + 1) → ℝ := fun i ↦ Classical.choose (hexists i)
  have hroots_mem :
      ∀ i : Fin (n + 1), roots' i ∈ Set.Ioo (a (Fin.castSucc i)) (a i.succ) := by
    intro i
    exact (Classical.choose_spec (hexists i)).1
  have hroots_zero : ∀ i : Fin (n + 1), (sechDerivPolyStep p).eval (roots' i) = 0 := by
    intro i
    exact (Classical.choose_spec (hexists i)).2
  refine ⟨roots', ?_, ?_, hroots_zero⟩
  · refine (Fin.strictMono_iff_lt_succ (f := roots')).2 ?_
    intro i
    have hleft : roots' (Fin.castSucc i) < a ((Fin.castSucc i).succ) := by
      simpa using (hroots_mem (Fin.castSucc i)).2
    have hright : a ((Fin.castSucc i).succ) < roots' i.succ := by
      simpa [← Fin.castSucc_succ] using (hroots_mem i.succ).1
    exact hleft.trans hright
  · intro i
    have hleft : a (Fin.castSucc i) ∈ Set.Icc (-1 : ℝ) 1 :=
      rootEndpoints_mem_Icc roots hmem (Fin.castSucc i)
    have hright : a i.succ ∈ Set.Icc (-1 : ℝ) 1 :=
      rootEndpoints_mem_Icc roots hmem i.succ
    exact ⟨lt_of_le_of_lt hleft.1 (hroots_mem i).1, lt_of_lt_of_le (hroots_mem i).2 hright.2⟩

theorem exists_strictMono_roots_sechDerivPoly :
    ∀ n : ℕ,
      ∃ roots : Fin n → ℝ,
        StrictMono roots ∧
        (∀ i, roots i ∈ Set.Ioo (-1 : ℝ) 1) ∧
        (∀ i, (sechDerivPoly n).eval (roots i) = 0)
  | 0 =>
      by
        refine ⟨Fin.elim0, ?_, ?_, ?_⟩
        · intro i j hij
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
  | n + 1 => by
      rcases exists_strictMono_roots_sechDerivPoly n with ⟨roots, hmono, hmem, hroot⟩
      simpa [sechDerivPoly] using exists_strictMono_roots_step roots hmono hmem hroot

end SechDerivativePolynomials

section SechSquarePolynomials

mutual

/-- The even derivative factor `E_n(y)` with `sechDerivPoly (2n)(x) = E_n(x^2)`. -/
noncomputable def evenSechSquarePoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (1 - 2 * Polynomial.X) * oddSechSquarePoly n +
        2 * Polynomial.X * (1 - Polynomial.X) * (oddSechSquarePoly n).derivative

/-- The odd derivative factor `O_n(y)` with `sechDerivPoly (2n + 1)(x) = x * O_n(x^2)`. -/
noncomputable def oddSechSquarePoly : ℕ → ℝ[X]
  | n => 2 * (1 - Polynomial.X) * (evenSechSquarePoly n).derivative - evenSechSquarePoly n

end

private theorem sechDerivPolyStep_comp_sq (p : ℝ[X]) :
    sechDerivPolyStep (p.comp (Polynomial.X ^ 2)) =
      Polynomial.X * ((2 * (1 - Polynomial.X) * p.derivative - p).comp (Polynomial.X ^ 2)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := (Set.univ : Set ℝ)) ?_ Set.infinite_univ
  intro x hx
  simp [sechDerivPolyStep, Polynomial.eval_comp, Polynomial.derivative_comp, pow_two]
  ring

private theorem sechDerivPolyStep_X_mul_comp_sq (p : ℝ[X]) :
    sechDerivPolyStep (Polynomial.X * p.comp (Polynomial.X ^ 2)) =
      (((1 - 2 * Polynomial.X) * p +
          2 * Polynomial.X * (1 - Polynomial.X) * p.derivative).comp (Polynomial.X ^ 2)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := (Set.univ : Set ℝ)) ?_ Set.infinite_univ
  intro x hx
  simp [sechDerivPolyStep, Polynomial.eval_comp, Polynomial.derivative_comp, pow_two]
  ring

mutual

theorem evenSechSquarePoly_spec :
    ∀ n : ℕ, sechDerivPoly (2 * n) = (evenSechSquarePoly n).comp (Polynomial.X ^ 2)
  | 0 => by simp [evenSechSquarePoly, sechDerivPoly]
  | n + 1 => by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sechDerivPoly]
      rw [oddSechSquarePoly_spec n]
      simpa [evenSechSquarePoly, mul_add, add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using sechDerivPolyStep_X_mul_comp_sq (oddSechSquarePoly n)

theorem oddSechSquarePoly_spec :
    ∀ n : ℕ, sechDerivPoly (2 * n + 1) = Polynomial.X * (oddSechSquarePoly n).comp (Polynomial.X ^ 2)
  | n => by
      rw [show 2 * n + 1 = 2 * n + 1 by ring, sechDerivPoly]
      rw [evenSechSquarePoly_spec n]
      simpa [oddSechSquarePoly, mul_add, add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using sechDerivPolyStep_comp_sq (evenSechSquarePoly n)

end

/-- The solver's adapted Xi polynomial, represented through the odd `sech` derivative factor. -/
noncomputable def solverSechXi (n : ℕ) : ℝ[X] :=
  Polynomial.C ((-4 : ℝ) ^ (n + 1)) * oddSechSquarePoly (n + 1)

/--
The exact scalar normalization matching the coefficient-defined family `solverRawAdaptedXi`.
Numerically this is the right normalization of the odd `sech` square-factor polynomial.
-/
noncomputable def solverSechXiExact (n : ℕ) : ℝ[X] :=
  Polynomial.C (-((4 : ℝ) ^ (n + 1))) * oddSechSquarePoly (n + 1)

theorem coeff_solverSechXi (n t : ℕ) :
    (solverSechXi n).coeff t = ((-4 : ℝ) ^ (n + 1)) * (oddSechSquarePoly (n + 1)).coeff t := by
  rw [solverSechXi, Polynomial.coeff_C_mul]

theorem coeff_solverSechXiExact (n t : ℕ) :
    (solverSechXiExact n).coeff t =
      (-((4 : ℝ) ^ (n + 1))) * (oddSechSquarePoly (n + 1)).coeff t := by
  rw [solverSechXiExact, Polynomial.coeff_C_mul]

theorem coeff_zero_evenSechSquarePoly_succ (n : ℕ) :
    (evenSechSquarePoly (n + 1)).coeff 0 = (oddSechSquarePoly n).coeff 0 := by
  simp [evenSechSquarePoly]

theorem coeff_one_evenSechSquarePoly_succ (n : ℕ) :
    (evenSechSquarePoly (n + 1)).coeff 1 =
      -2 * (oddSechSquarePoly n).coeff 0 + 3 * (oddSechSquarePoly n).coeff 1 := by
  let q := oddSechSquarePoly n
  have hq :
      evenSechSquarePoly (n + 1) =
        q - 2 * Polynomial.X * q + 2 * Polynomial.X * q.derivative -
          2 * Polynomial.X ^ 2 * q.derivative := by
    simp [q, evenSechSquarePoly]
    ring
  have h2Xq : (2 * Polynomial.X * q).coeff 1 = 2 * q.coeff 0 := by
    calc
      (2 * Polynomial.X * q).coeff 1 = 2 * (Polynomial.X * q).coeff 1 := by
        simpa [mul_assoc] using
          (Polynomial.coeff_natCast_mul (p := Polynomial.X * q) (a := 2) (k := 1))
      _ = 2 * q.coeff 0 := by rw [Polynomial.coeff_X_mul]
  have h2Xdq : (2 * Polynomial.X * q.derivative).coeff 1 = 2 * q.coeff 1 := by
    calc
      (2 * Polynomial.X * q.derivative).coeff 1 = 2 * (Polynomial.X * q.derivative).coeff 1 := by
        simpa [mul_assoc] using
          (Polynomial.coeff_natCast_mul (p := Polynomial.X * q.derivative) (a := 2) (k := 1))
      _ = 2 * q.coeff 1 := by
        rw [Polynomial.coeff_X_mul]
        simp [Polynomial.coeff_derivative]
  have h2X2dq : (2 * Polynomial.X ^ 2 * q.derivative).coeff 1 = 0 := by
    have hX2 : (Polynomial.X ^ 2 * q.derivative).coeff 1 = 0 := by
      simp [Polynomial.coeff_X_pow_mul']
    rw [show (2 : ℝ[X]) = Polynomial.C 2 by rfl, mul_assoc, Polynomial.coeff_C_mul]
    simp [hX2]
  rw [hq]
  rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_sub, h2Xq, h2Xdq, h2X2dq]
  ring

theorem coeff_zero_oddSechSquarePoly (n : ℕ) :
    (oddSechSquarePoly n).coeff 0 =
      2 * (evenSechSquarePoly n).coeff 1 - (evenSechSquarePoly n).coeff 0 := by
  simp [oddSechSquarePoly, Polynomial.coeff_derivative]

theorem coeff_zero_oddSechSquarePoly_succ (n : ℕ) :
    (oddSechSquarePoly (n + 1)).coeff 0 =
      6 * (oddSechSquarePoly n).coeff 1 - 5 * (oddSechSquarePoly n).coeff 0 := by
  rw [coeff_zero_oddSechSquarePoly, coeff_one_evenSechSquarePoly_succ, coeff_zero_evenSechSquarePoly_succ]
  ring_nf

theorem oddSechSquarePoly_coeff_ratio (n : ℕ)
    (h0 : (oddSechSquarePoly n).coeff 0 ≠ 0) :
    -((oddSechSquarePoly n).coeff 1) / (oddSechSquarePoly n).coeff 0 =
      (-(oddSechSquarePoly (n + 1)).coeff 0 / (oddSechSquarePoly n).coeff 0 - 5) / 6 := by
  have hrec := coeff_zero_oddSechSquarePoly_succ n
  field_simp [h0]
  nlinarith [hrec]

theorem solverSechXi_coeff_ratio_from_odd_constants (n : ℕ)
    (h0 : (oddSechSquarePoly (n + 1)).coeff 0 ≠ 0) :
    -((solverSechXi n).coeff 1) / (solverSechXi n).coeff 0 =
      (-(oddSechSquarePoly (n + 2)).coeff 0 / (oddSechSquarePoly (n + 1)).coeff 0 - 5) / 6 := by
  have hscale : ((-4 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  have hcancel :
      -((solverSechXi n).coeff 1) / (solverSechXi n).coeff 0 =
        -((oddSechSquarePoly (n + 1)).coeff 1) / (oddSechSquarePoly (n + 1)).coeff 0 := by
    rw [coeff_solverSechXi, coeff_solverSechXi]
    field_simp [h0, hscale]
  rw [hcancel, oddSechSquarePoly_coeff_ratio (n + 1) h0]

theorem iteratedDeriv_two_mul_succ_realSech_zero (n : ℕ) :
    iteratedDeriv (2 * (n + 1)) realSech 0 = (oddSechSquarePoly n).coeff 0 := by
  rw [sechDerivPoly_eval, evenSechSquarePoly_spec (n + 1)]
  simp [realSech, pow_two, Polynomial.eval_comp]
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_zero_evenSechSquarePoly_succ]

end SechSquarePolynomials

section BernoulliSechBridge

private noncomputable def scaledRealSech (x : ℝ) : ℝ :=
  realSech ((1 / 4 : ℝ) * x)

private noncomputable def scaledExpSum (x : ℝ) : ℝ :=
  Real.exp ((1 / 4 : ℝ) * x) + Real.exp (-((1 / 4 : ℝ) * x))

private noncomputable def scaledRealSechSeries : ℝ⟦X⟧ :=
  PowerSeries.mk fun n => iteratedDeriv n scaledRealSech 0 / ((n.factorial : ℕ) : ℝ)

private theorem contDiff_scaledRealSech (n : ℕ) : ContDiff ℝ n scaledRealSech := by
  unfold scaledRealSech
  simpa using (contDiff_realSech n).comp (by
    simpa using (contDiff_const.mul contDiff_id : ContDiff ℝ n (fun x : ℝ => (1 / 4 : ℝ) * x)))

private theorem contDiff_scaledExpSum (n : ℕ) : ContDiff ℝ n scaledExpSum := by
  unfold scaledExpSum
  have hlin : ContDiff ℝ n (fun x : ℝ => (1 / 4 : ℝ) * x) := by
    simpa using (contDiff_const.mul contDiff_id : ContDiff ℝ n (fun x : ℝ => (1 / 4 : ℝ) * x))
  refine (Real.contDiff_exp.comp ?_).add (Real.contDiff_exp.comp ?_)
  · exact hlin
  · simpa using hlin.neg

private theorem scaledRealSech_mul_scaledExpSum :
    (fun x : ℝ => scaledRealSech x * scaledExpSum x) = fun _ => (2 : ℝ) := by
  funext x
  unfold scaledRealSech scaledExpSum realSech
  rw [Real.cosh_eq]
  have hsum : Real.exp ((1 / 4 : ℝ) * x) + Real.exp (-(1 / 4 : ℝ) * x) ≠ 0 := by
    positivity
  field_simp [hsum]

private theorem coeff_scaledRealSechSeries (n : ℕ) :
    PowerSeries.coeff n scaledRealSechSeries =
      iteratedDeriv n scaledRealSech 0 / ((n.factorial : ℕ) : ℝ) := by
  simp [scaledRealSechSeries]

private theorem coeff_expQuarter_add_expNegQuarter_eq_scaledExpSum (n : ℕ) :
    PowerSeries.coeff n (expQuarter + expNegQuarter) =
      iteratedDeriv n scaledExpSum 0 / ((n.factorial : ℕ) : ℝ) := by
  have hlin : ContDiff ℝ n (fun x : ℝ => (1 / 4 : ℝ) * x) := by
    simpa using (contDiff_const.mul contDiff_id : ContDiff ℝ n (fun x : ℝ => (1 / 4 : ℝ) * x))
  have h1 :
      iteratedDeriv n (fun s : ℝ => Real.exp ((1 / 4 : ℝ) * s)) 0 = (1 / 4 : ℝ) ^ n := by
    have h1' := congrArg (fun f : ℝ → ℝ => f 0) (iteratedDeriv_exp_const_mul n (1 / 4 : ℝ))
    calc
      iteratedDeriv n (fun s : ℝ => Real.exp ((1 / 4 : ℝ) * s)) 0
          = (1 / 4 : ℝ) ^ n * Real.exp ((1 / 4 : ℝ) * 0) := by simpa using h1'
      _ = (1 / 4 : ℝ) ^ n := by simp
  have h2 :
      iteratedDeriv n (fun s : ℝ => Real.exp (-((1 / 4 : ℝ) * s))) 0 = (-(1 / 4 : ℝ)) ^ n := by
    have h2' := congrArg (fun f : ℝ → ℝ => f 0) (iteratedDeriv_exp_const_mul n (-(1 / 4 : ℝ)))
    calc
      iteratedDeriv n (fun s : ℝ => Real.exp (-((1 / 4 : ℝ) * s))) 0
          = (-(1 / 4 : ℝ)) ^ n * Real.exp (-(1 / 4 : ℝ) * 0) := by
              simpa [neg_mul] using h2'
      _ = (-(1 / 4 : ℝ)) ^ n := by simp
  have hadd :
      iteratedDeriv n scaledExpSum 0 =
        iteratedDeriv n (fun x : ℝ => Real.exp ((1 / 4 : ℝ) * x)) 0 +
          iteratedDeriv n (fun x : ℝ => Real.exp (-((1 / 4 : ℝ) * x))) 0 := by
    let f : ℝ → ℝ := fun x => Real.exp ((1 / 4 : ℝ) * x)
    let g : ℝ → ℝ := fun x => Real.exp (-((1 / 4 : ℝ) * x))
    unfold scaledExpSum
    change
      iteratedDeriv n (fun z : ℝ => Real.exp ((1 / 4 : ℝ) * z) + Real.exp (-((1 / 4 : ℝ) * z))) 0 =
        iteratedDeriv n (fun x : ℝ => Real.exp ((1 / 4 : ℝ) * x)) 0 +
          iteratedDeriv n (fun x : ℝ => Real.exp (-((1 / 4 : ℝ) * x))) 0
    simpa only [f, g] using
      (iteratedDeriv_fun_add (x := 0) ((Real.contDiff_exp.comp hlin).contDiffAt)
        ((Real.contDiff_exp.comp hlin.neg).contDiffAt))
  change PowerSeries.coeff n expQuarter + PowerSeries.coeff n expNegQuarter =
    iteratedDeriv n scaledExpSum 0 / ((n.factorial : ℕ) : ℝ)
  rw [hadd, h1, h2]
  simp [expQuarter, expNegQuarter, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  ring

private theorem coeff_scaledRealSechSeries_mul_expQuarter_add_expNegQuarter (n : ℕ) :
    PowerSeries.coeff n (scaledRealSechSeries * (expQuarter + expNegQuarter)) =
      iteratedDeriv n (fun x : ℝ => scaledRealSech x * scaledExpSum x) 0 /
        ((n.factorial : ℕ) : ℝ) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
    PowerSeries.coeff i scaledRealSechSeries * PowerSeries.coeff j (expQuarter + expNegQuarter)]
  have hterm :
      ∀ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i scaledRealSechSeries *
            PowerSeries.coeff (n - i) (expQuarter + expNegQuarter) =
          ((n.choose i : ℝ) * iteratedDeriv i scaledRealSech 0 *
              iteratedDeriv (n - i) scaledExpSum 0) /
            ((n.factorial : ℕ) : ℝ) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hnfac : (((n.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
    have hifac : (((i.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
    have hsubfac : ((((n - i).factorial : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [coeff_scaledRealSechSeries, coeff_expQuarter_add_expNegQuarter_eq_scaledExpSum,
      Nat.cast_choose ℝ hi']
    field_simp [hnfac, hifac, hsubfac]
  calc
    ∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i scaledRealSechSeries *
          PowerSeries.coeff (n - i) (expQuarter + expNegQuarter)
        =
      ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * iteratedDeriv i scaledRealSech 0 *
            iteratedDeriv (n - i) scaledExpSum 0) /
          ((n.factorial : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hterm i hi
    _ =
      iteratedDeriv n (fun x : ℝ => scaledRealSech x * scaledExpSum x) 0 /
        ((n.factorial : ℕ) : ℝ) := by
        have hmul :
            iteratedDeriv n (fun x : ℝ => scaledRealSech x * scaledExpSum x) 0 =
              ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * iteratedDeriv i scaledRealSech 0 *
                  iteratedDeriv (n - i) scaledExpSum 0 := by
          simpa using iteratedDeriv_mul
            (x := 0) (n := n) (contDiff_scaledRealSech n).contDiffAt
            (contDiff_scaledExpSum n).contDiffAt
        calc
          ∑ i ∈ Finset.range (n + 1),
              ((n.choose i : ℝ) * iteratedDeriv i scaledRealSech 0 *
                  iteratedDeriv (n - i) scaledExpSum 0) /
                ((n.factorial : ℕ) : ℝ)
              =
            (∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * iteratedDeriv i scaledRealSech 0 *
                  iteratedDeriv (n - i) scaledExpSum 0) /
              ((n.factorial : ℕ) : ℝ) := by
                simp [div_eq_mul_inv, Finset.sum_mul]
          _ = iteratedDeriv n (fun x : ℝ => scaledRealSech x * scaledExpSum x) 0 /
                ((n.factorial : ℕ) : ℝ) := by
                rw [hmul]

private theorem scaledRealSechSeries_mul_expQuarter_add_expNegQuarter :
    scaledRealSechSeries * (expQuarter + expNegQuarter) = (2 : ℝ⟦X⟧) := by
  ext n
  change PowerSeries.coeff n (scaledRealSechSeries * (expQuarter + expNegQuarter)) =
    PowerSeries.coeff n (PowerSeries.C (2 : ℝ))
  rw [coeff_scaledRealSechSeries_mul_expQuarter_add_expNegQuarter, scaledRealSech_mul_scaledExpSum]
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff, iteratedDeriv_const]

private theorem expQuarter_add_expNegQuarter_ne_zero :
    expQuarter + expNegQuarter ≠ 0 := by
  intro h
  have hcoeff :
      PowerSeries.constantCoeff (R := ℝ) (expQuarter + expNegQuarter) = 0 := by
    simpa using congrArg (PowerSeries.constantCoeff (R := ℝ)) h
  have hq1 : PowerSeries.constantCoeff (R := ℝ) expQuarter = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [expQuarter, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have hq2 : PowerSeries.constantCoeff (R := ℝ) expNegQuarter = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [expNegQuarter, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have hq : PowerSeries.constantCoeff (R := ℝ) (expQuarter + expNegQuarter) = 2 := by
    calc
      PowerSeries.constantCoeff (R := ℝ) (expQuarter + expNegQuarter) =
          PowerSeries.constantCoeff (R := ℝ) expQuarter +
            PowerSeries.constantCoeff (R := ℝ) expNegQuarter := by
              exact map_add (PowerSeries.constantCoeff (R := ℝ)) expQuarter expNegQuarter
      _ = 2 := by rw [hq1, hq2]; norm_num
  rw [hq] at hcoeff
  norm_num at hcoeff

private theorem bernoulliQuarterOddSeries_eq_neg_half_X_mul_scaledRealSechSeries :
    bernoulliQuarterOddSeries =
      PowerSeries.C (-(1 / 2 : ℝ)) * PowerSeries.X * scaledRealSechSeries := by
  have hprod :
      (PowerSeries.C (-(1 / 2 : ℝ)) * PowerSeries.X * scaledRealSechSeries) *
          (expQuarter + expNegQuarter) = -PowerSeries.X := by
    calc
      (PowerSeries.C (-(1 / 2 : ℝ)) * PowerSeries.X * scaledRealSechSeries) *
            (expQuarter + expNegQuarter)
          =
        PowerSeries.C (-(1 / 2 : ℝ)) * PowerSeries.X *
          (scaledRealSechSeries * (expQuarter + expNegQuarter)) := by
            rw [mul_assoc]
      _ = PowerSeries.C (-(1 / 2 : ℝ)) * PowerSeries.X * (2 : ℝ⟦X⟧) := by
            rw [scaledRealSechSeries_mul_expQuarter_add_expNegQuarter]
      _ = PowerSeries.C (-(1 / 2 : ℝ)) * PowerSeries.X * PowerSeries.C 2 := by rfl
      _ = -PowerSeries.X := by
            ext n
            cases n with
            | zero =>
                simp [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_X]
            | succ n =>
                cases n with
                | zero =>
                    simp [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_X]
                | succ n =>
                    simp [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_X]
  have hsub :
      (bernoulliQuarterOddSeries -
          PowerSeries.C (-(1 / 2 : ℝ)) * PowerSeries.X * scaledRealSechSeries) *
        (expQuarter + expNegQuarter) = 0 := by
    rw [sub_mul, bernoulliQuarterOddSeries_mul_expQuarter_add_expNegQuarter, hprod]
    ring
  have hzero :
      bernoulliQuarterOddSeries -
          PowerSeries.C (-(1 / 2 : ℝ)) * PowerSeries.X * scaledRealSechSeries = 0 := by
    exact Or.resolve_right (mul_eq_zero.mp hsub) expQuarter_add_expNegQuarter_ne_zero
  simpa using sub_eq_zero.mp hzero

private theorem iteratedDeriv_scaledRealSech (n : ℕ) :
    iteratedDeriv n scaledRealSech 0 = (1 / 4 : ℝ) ^ n * iteratedDeriv n realSech 0 := by
  unfold scaledRealSech
  simpa using
    congrArg (fun f : ℝ → ℝ => f 0)
      (iteratedDeriv_comp_const_mul (n := n) (f := realSech) (contDiff_realSech n) (1 / 4 : ℝ))

theorem coeff_bernoulliQuarterOddSeries_odd_eq_iteratedDeriv_realSech (m : ℕ) :
    PowerSeries.coeff (2 * m + 1) bernoulliQuarterOddSeries =
      -(1 / 2 : ℝ) *
        (((1 / 4 : ℝ) ^ (2 * m)) * iteratedDeriv (2 * m) realSech 0 /
          (((2 * m).factorial : ℕ) : ℝ)) := by
  rw [bernoulliQuarterOddSeries_eq_neg_half_X_mul_scaledRealSechSeries, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul, coeff_scaledRealSechSeries, iteratedDeriv_scaledRealSech]

end BernoulliSechBridge

section TypeBSechBridge

/-- The type-B Eulerian polynomial with the explicit coefficients `typeBEulerianCoeff`. -/
noncomputable def typeBEulerianPoly (m : ℕ) : ℝ[X] :=
  Finset.sum (Finset.range (m + 1)) fun k =>
    Polynomial.C (typeBEulerianCoeff m k) * Polynomial.X ^ k

theorem coeff_typeBEulerianPoly (m k : ℕ) :
    (typeBEulerianPoly m).coeff k =
      if k < m + 1 then typeBEulerianCoeff m k else 0 := by
  unfold typeBEulerianPoly
  simp

private theorem typeBEulerianCoeff_zero (m : ℕ) :
    typeBEulerianCoeff m 0 = 1 := by
  simp [typeBEulerianCoeff]

private theorem typeBEulerianCoeff_succ_summand (m k j : ℕ) :
    ((Nat.choose (m + 2) (j + 1) : ℝ) : ℝ) * (2 * (k - j) + 1 : ℝ) =
      (2 * k + 3 : ℝ) * (Nat.choose (m + 1) (j + 1) : ℝ) -
        (2 * m - 2 * k + 1 : ℝ) * (Nat.choose (m + 1) j : ℝ) := by
  have hchooseNat := Nat.choose_succ_right_eq (m + 1) j
  by_cases hj : j ≤ m + 1
  · have hchoose :
        (Nat.choose (m + 1) (j + 1) : ℝ) * (j + 1 : ℝ) =
          (Nat.choose (m + 1) j : ℝ) * (((m + 1 - j : ℕ) : ℝ)) := by
      exact_mod_cast hchooseNat
    have hlin : (((m + 1 - j : ℕ) : ℝ)) = (m + 1 : ℝ) - j := by
      rw [Nat.cast_sub hj, Nat.cast_add]
      norm_num
    rw [Nat.choose_succ_succ', Nat.cast_add]
    nlinarith [hchoose, hlin]
  · have hgt : m + 1 < j := Nat.lt_of_not_ge hj
    have hzj : (Nat.choose (m + 1) j : ℝ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt hgt
    have hzj1 : (Nat.choose (m + 1) (j + 1) : ℝ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (lt_trans hgt (Nat.lt_succ_self j))
    have hzsucc : (Nat.choose (m + 2) (j + 1) : ℝ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : m + 2 < j + 1)
    rw [hzj, hzj1, hzsucc]
    simp

private theorem typeBEulerianCoeff_reflect (m k : ℕ) :
    typeBEulerianCoeff m k =
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ (k - j) * (Nat.choose (m + 1) (k - j) : ℝ) * (2 * j + 1 : ℝ) ^ m := by
  unfold typeBEulerianCoeff
  calc
    (∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ j * (Nat.choose (m + 1) j : ℝ) * (2 * (k - j) + 1 : ℝ) ^ m)
        =
      ∑ j ∈ Finset.range (k + 1),
        ((fun t : ℕ =>
            (-1 : ℝ) ^ (k - t) * (Nat.choose (m + 1) (k - t) : ℝ) * (2 * t + 1 : ℝ) ^ m)
          ((k + 1) - 1 - j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            have hsub : k + 1 - 1 - j = k - j := by omega
            have hback : k - (k - j) = j := Nat.sub_sub_self hjle
            simp [hsub, hback, Nat.cast_sub hjle]
    _ =
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ (k - j) * (Nat.choose (m + 1) (k - j) : ℝ) * (2 * j + 1 : ℝ) ^ m := by
          simpa using
            (Finset.sum_range_reflect
              (fun t : ℕ =>
                (-1 : ℝ) ^ (k - t) * (Nat.choose (m + 1) (k - t) : ℝ) *
                  (2 * t + 1 : ℝ) ^ m)
              (k + 1))

private theorem typeBEulerianCoeff_succ (m k : ℕ) :
    typeBEulerianCoeff (m + 1) (k + 1) =
      (2 * k + 3 : ℝ) * typeBEulerianCoeff m (k + 1) +
        (2 * m - 2 * k + 1 : ℝ) * typeBEulerianCoeff m k := by
  rw [typeBEulerianCoeff_reflect (m + 1) (k + 1), typeBEulerianCoeff_reflect m (k + 1),
    typeBEulerianCoeff_reflect m k]
  let L : ℕ → ℝ := fun j =>
    (-1 : ℝ) ^ (k + 1 - j) * (Nat.choose (m + 2) (k + 1 - j) : ℝ) * (2 * j + 1 : ℝ) ^ (m + 1)
  let G : ℕ → ℝ := fun j =>
    (-1 : ℝ) ^ (k + 1 - j) * (Nat.choose (m + 1) (k + 1 - j) : ℝ) * (2 * j + 1 : ℝ) ^ m
  let H : ℕ → ℝ := fun j =>
    (-1 : ℝ) ^ (k - j) * (Nat.choose (m + 1) (k - j) : ℝ) * (2 * j + 1 : ℝ) ^ m
  change (∑ j ∈ Finset.range (k + 2), L j) =
      (2 * k + 3 : ℝ) * (∑ j ∈ Finset.range (k + 2), G j) +
        (2 * m - 2 * k + 1 : ℝ) * (∑ j ∈ Finset.range (k + 1), H j)
  have hsplitL :
      (∑ j ∈ Finset.range (k + 2), L j) =
        (∑ j ∈ Finset.range (k + 1), L j) + L (k + 1) := by
    rw [Finset.sum_range_succ]
  have hsplitG :
      (∑ j ∈ Finset.range (k + 2), G j) =
        (∑ j ∈ Finset.range (k + 1), G j) + G (k + 1) := by
    rw [Finset.sum_range_succ]
  rw [hsplitL, hsplitG]
  have hlast : L (k + 1) = (2 * k + 3 : ℝ) * G (k + 1) := by
    simp [L, G, pow_succ]
    ring
  rw [hlast, mul_add]
  have hsum :
      (∑ x ∈ Finset.range (k + 1), L x) =
        ∑ x ∈ Finset.range (k + 1),
          ((2 * k + 3 : ℝ) * G x + (2 * m - 2 * k + 1 : ℝ) * H x) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hkj : k + 1 - j = k - j + 1 := by omega
    have hsummand := typeBEulerianCoeff_succ_summand m k (k - j)
    have hodd :
        (2 * (↑k - ↑(k - j)) + 1 : ℝ) = (2 * j + 1 : ℝ) := by
      rw [← Nat.cast_sub (Nat.sub_le k j), Nat.sub_sub_self hjle]
    have hsummand' :
        (Nat.choose (m + 2) (k + 1 - j) : ℝ) * (2 * j + 1 : ℝ) =
          (2 * k + 3 : ℝ) * (Nat.choose (m + 1) (k + 1 - j) : ℝ) -
            (2 * m - 2 * k + 1 : ℝ) * (Nat.choose (m + 1) (k - j) : ℝ) := by
      simpa [Nat.sub_sub_self hjle, hkj, hodd] using hsummand
    calc
      L j
          = (-1 : ℝ) ^ (k + 1 - j) *
              ((Nat.choose (m + 2) (k + 1 - j) : ℝ) * (2 * j + 1 : ℝ)) *
                (2 * j + 1 : ℝ) ^ m := by
                  dsimp [L]
                  rw [pow_succ]
                  ring
      _ =
          (-1 : ℝ) ^ (k + 1 - j) *
              ((2 * k + 3 : ℝ) * (Nat.choose (m + 1) (k + 1 - j) : ℝ) -
                (2 * m - 2 * k + 1 : ℝ) * (Nat.choose (m + 1) (k - j) : ℝ)) *
                (2 * j + 1 : ℝ) ^ m := by rw [hsummand']
      _ = (2 * k + 3 : ℝ) * G j + (2 * m - 2 * k + 1 : ℝ) * H j := by
            dsimp [G, H]
            rw [hkj, pow_succ]
            ring
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

private theorem typeBEulerianCoeff_eq_zero_of_lt :
    ∀ {m k : ℕ}, m < k → typeBEulerianCoeff m k = 0
  | 0, 0, h => (False.elim (Nat.lt_irrefl _ h))
  | 0, k + 1, h => by
      unfold typeBEulerianCoeff
      rw [show k + 1 + 1 = 2 + k by omega, Finset.sum_range_add]
      have htail :
          ∑ x ∈ Finset.range k, (-1 : ℝ) ^ (x + 2) * (Nat.choose 1 (x + 2) : ℝ) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hxgt : 1 < x + 2 := by omega
        simp [Nat.choose_eq_zero_of_lt hxgt]
      have hhead :
          ∑ x ∈ Finset.range 2, (-1 : ℝ) ^ x * (Nat.choose 1 x : ℝ) = 0 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        norm_num
      simpa [hhead, htail, add_comm, add_left_comm, add_assoc]
  | m + 1, 0, h => (False.elim (Nat.not_lt_zero _ h))
  | m + 1, k + 1, h => by
      rw [typeBEulerianCoeff_succ m k]
      have hk : m < k := by omega
      have hk' : m < k + 1 := by omega
      rw [typeBEulerianCoeff_eq_zero_of_lt hk', typeBEulerianCoeff_eq_zero_of_lt hk]
      ring

private theorem typeBEulerianCoeff_symm :
    ∀ {m k : ℕ}, k ≤ m → typeBEulerianCoeff m (m - k) = typeBEulerianCoeff m k
  | 0, 0, hk => by simp [typeBEulerianCoeff_zero]
  | 0, k + 1, hk => by omega
  | m + 1, 0, hk => by
      have hm : typeBEulerianCoeff m m = 1 := by
        simpa [typeBEulerianCoeff_zero] using
          (typeBEulerianCoeff_symm (m := m) (k := 0) (Nat.zero_le m))
      have hz : typeBEulerianCoeff m (m + 1) = 0 :=
        typeBEulerianCoeff_eq_zero_of_lt (Nat.lt_succ_self m)
      rw [show m + 1 - 0 = m + 1 by omega, typeBEulerianCoeff_succ m m, hz, hm,
        typeBEulerianCoeff_zero]
      ring
  | m + 1, k + 1, hk => by
      by_cases hkm : k = m
      · subst k
        have hm : typeBEulerianCoeff m m = 1 := by
          simpa [typeBEulerianCoeff_zero] using
            (typeBEulerianCoeff_symm (m := m) (k := 0) (Nat.zero_le m))
        have hz : typeBEulerianCoeff m (m + 1) = 0 :=
          typeBEulerianCoeff_eq_zero_of_lt (Nat.lt_succ_self m)
        rw [show m + 1 - (m + 1) = 0 by omega, typeBEulerianCoeff_zero, typeBEulerianCoeff_succ m m,
          hz, hm]
        ring
      · have hklt : k < m := by omega
        have hk0le : k ≤ m := Nat.le_of_lt hklt
        have hk1le : k + 1 ≤ m := by omega
        have hmk1 : 1 ≤ m - k := by omega
        have hleftIndex : m + 1 - (k + 1) = (m - k - 1) + 1 := by omega
        have hsym0 :
            typeBEulerianCoeff m (m - k) = typeBEulerianCoeff m k :=
          typeBEulerianCoeff_symm (m := m) (k := k) hk0le
        have hsym1 :
            typeBEulerianCoeff m (m - k - 1) = typeBEulerianCoeff m (k + 1) := by
          simpa [show m - (k + 1) = m - k - 1 by omega] using
            (typeBEulerianCoeff_symm (m := m) (k := k + 1) hk1le)
        have hmk : m - k - 1 + 1 = m - k := by omega
        rw [hleftIndex, typeBEulerianCoeff_succ m (m - k - 1), typeBEulerianCoeff_succ m k, hmk,
          hsym0, hsym1]
        norm_num [Nat.cast_sub hk0le, Nat.cast_sub hmk1]
        ring

private theorem typeBEulerianCoeff_diag (m : ℕ) :
    typeBEulerianCoeff m m = 1 := by
  simpa [typeBEulerianCoeff_zero] using
    (typeBEulerianCoeff_symm (m := m) (k := 0) (Nat.zero_le m))

private theorem sechDerivPolyStep_add (p q : ℝ[X]) :
    sechDerivPolyStep (p + q) = sechDerivPolyStep p + sechDerivPolyStep q := by
  simp [sechDerivPolyStep, sub_eq_add_neg, add_mul, mul_add, Polynomial.derivative_add,
    add_assoc, add_left_comm, add_comm]

private theorem sechDerivPolyStep_C_mul (a : ℝ) (p : ℝ[X]) :
    sechDerivPolyStep (Polynomial.C a * p) = Polynomial.C a * sechDerivPolyStep p := by
  unfold sechDerivPolyStep
  rw [Polynomial.derivative_mul, Polynomial.derivative_C]
  simp [sub_eq_add_neg, add_mul, mul_add, mul_assoc]
  ring

private theorem sechDerivPolyStep_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    sechDerivPolyStep (∑ i ∈ s, f i) = ∑ i ∈ s, sechDerivPolyStep (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [sechDerivPolyStep]
  · intro a s ha hs
    simp [Finset.sum_insert, ha, sechDerivPolyStep_add, hs]

/--
The Möbius-transformed type-B Eulerian polynomial:
`(1 + x)^m B_m(-(1 - x)/(1 + x))`.
-/
noncomputable def typeBSechBasis (m k : ℕ) : ℝ[X] :=
  Polynomial.C ((-1 : ℝ) ^ k) * (1 - Polynomial.X) ^ k * (1 + Polynomial.X) ^ (m - k)

noncomputable def typeBSechTransform (m : ℕ) : ℝ[X] :=
  Finset.sum (Finset.range (m + 1)) fun k =>
    Polynomial.C (typeBEulerianCoeff m k) * typeBSechBasis m k

private theorem one_sub_X_eq_C_neg_one_mul_X_sub_one :
    (1 - Polynomial.X : ℝ[X]) = Polynomial.C (-1) * (Polynomial.X - 1) := by
  ext n
  rcases n with _ | _ | n <;> simp

private theorem typeBSechBasis_eq (m k : ℕ) :
    typeBSechBasis m k = (Polynomial.X - 1) ^ k * (Polynomial.X + 1) ^ (m - k) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := (Set.univ : Set ℝ)) ?_ Set.infinite_univ
  intro x hx
  change (typeBSechBasis m k).eval x =
    Polynomial.eval x (((Polynomial.X - 1) ^ k * (Polynomial.X + 1) ^ (m - k) : ℝ[X]))
  have hxa : x - 1 = -(1 - x) := by ring
  unfold typeBSechBasis
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have hpow : (x - 1) ^ k = (-1 : ℝ) ^ k * (1 - x) ^ k := by
    rw [hxa, neg_pow]
  rw [hpow]
  ring

private theorem eval_typeBSechBasis_eq (m k : ℕ) (x : ℝ) :
    (typeBSechBasis m k).eval x = (x - 1) ^ k * (x + 1) ^ (m - k) := by
  rw [typeBSechBasis_eq]
  simp

private theorem eval_deriv_typeBSechBasis (m k : ℕ) (x : ℝ) :
    (typeBSechBasis m k).derivative.eval x =
      (k : ℝ) * (x - 1) ^ (k - 1) * (x + 1) ^ (m - k) +
        ((m - k : ℕ) : ℝ) * (x - 1) ^ k * (x + 1) ^ (m - k - 1) := by
  rw [typeBSechBasis_eq, Polynomial.derivative_mul]
  rw [show Polynomial.derivative ((Polynomial.X - 1 : ℝ[X]) ^ k) =
      Polynomial.C (k : ℝ) * (Polynomial.X - 1) ^ (k - 1) by
      simpa using (Polynomial.derivative_X_sub_C_pow (1 : ℝ) k)]
  rw [show Polynomial.derivative ((Polynomial.X + 1 : ℝ[X]) ^ (m - k)) =
      Polynomial.C ((m - k : ℕ) : ℝ) * (Polynomial.X + 1) ^ (m - k - 1) by
      simpa using (Polynomial.derivative_X_add_C_pow (1 : ℝ) (m - k))]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]
  ring_nf

private theorem typeBSechBasis_step (m k : ℕ) (hk : k ≤ m) :
    (-2 : ℝ[X]) * sechDerivPolyStep (typeBSechBasis m k) =
      (2 * k + 1 : ℝ[X]) * typeBSechBasis (m + 1) k +
        (2 * (m - k) + 1 : ℝ[X]) * typeBSechBasis (m + 1) (k + 1) := by
  by_cases hk0 : k = 0
  · subst k
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := (Set.univ : Set ℝ)) ?_ Set.infinite_univ
    intro x hx
    let a : ℝ := x - 1
    let b : ℝ := x + 1
    have hbasis : (typeBSechBasis m 0).eval x = b ^ m := by
      simpa [a, b] using eval_typeBSechBasis_eq m 0 x
    have hderiv : (typeBSechBasis m 0).derivative.eval x = (m : ℝ) * b ^ (m - 1) := by
      simpa [a, b] using eval_deriv_typeBSechBasis m 0 x
    have hbasis_succ_left :
        (typeBSechBasis (m + 1) 0).eval x = b ^ (m + 1) := by
      simpa [a, b] using eval_typeBSechBasis_eq (m + 1) 0 x
    have hbasis_succ_right :
        (typeBSechBasis (m + 1) 1).eval x = a * b ^ m := by
      have hpow : m + 1 - 1 = m := by omega
      simpa [a, b, hpow] using eval_typeBSechBasis_eq (m + 1) 1 x
    have hab : 1 - x ^ 2 = -(a * b) := by
      simp [a, b]
      ring
    have habEval : (1 - Polynomial.X ^ 2 : ℝ[X]).eval x = -(a * b) := by
      simpa [Polynomial.eval_sub, Polynomial.eval_pow] using hab
    have hstep :
        (sechDerivPolyStep (typeBSechBasis m 0)).eval x =
          -((m : ℝ) * a * b ^ m + x * b ^ m) := by
      unfold sechDerivPolyStep
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, hderiv, hbasis, habEval]
      by_cases hm0 : m = 0
      · subst m
        simp
      · have hm1 : m = (m - 1) + 1 := by omega
        rw [hm1]
        simp [pow_succ]
        ring
    have hxeq :
        (((-2 : ℝ[X]) * sechDerivPolyStep (typeBSechBasis m 0)).eval x) =
          (((1 : ℝ[X]) * typeBSechBasis (m + 1) 0 +
              (2 * m + 1 : ℝ[X]) * typeBSechBasis (m + 1) 1).eval x) := by
      calc
        (((-2 : ℝ[X]) * sechDerivPolyStep (typeBSechBasis m 0)).eval x)
            = (-2 : ℝ) * (-((m : ℝ) * a * b ^ m + x * b ^ m)) := by
                rw [Polynomial.eval_mul, hstep]
                simp
        _ = ((2 * m : ℝ) * a + 2 * x) * b ^ m := by
              ring
        _ = (b + (2 * m + 1 : ℝ) * a) * b ^ m := by
              dsimp [a, b]
              ring
        _ = (((1 : ℝ[X]) * typeBSechBasis (m + 1) 0 +
                (2 * m + 1 : ℝ[X]) * typeBSechBasis (m + 1) 1).eval x) := by
              rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
                hbasis_succ_left, hbasis_succ_right]
              simp
              ring
    simpa using hxeq
  · by_cases hkm : k = m
    · subst k
      apply Polynomial.eq_of_infinite_eval_eq
      refine Set.Infinite.mono (s := (Set.univ : Set ℝ)) ?_ Set.infinite_univ
      intro x hx
      let a : ℝ := x - 1
      let b : ℝ := x + 1
      have hbasis : (typeBSechBasis m m).eval x = a ^ m := by
        simpa [a, b] using eval_typeBSechBasis_eq m m x
      have hderiv : (typeBSechBasis m m).derivative.eval x = (m : ℝ) * a ^ (m - 1) := by
        simpa [a, b] using eval_deriv_typeBSechBasis m m x
      have hbasis_succ_left :
          (typeBSechBasis (m + 1) m).eval x = a ^ m * b := by
        have hpow : m + 1 - m = 1 := by omega
        simpa [a, b, hpow] using eval_typeBSechBasis_eq (m + 1) m x
      have hbasis_succ_right :
          (typeBSechBasis (m + 1) (m + 1)).eval x = a ^ (m + 1) := by
        simpa [a, b] using eval_typeBSechBasis_eq (m + 1) (m + 1) x
      have hab : 1 - x ^ 2 = -(a * b) := by
        simp [a, b]
        ring
      have habEval : (1 - Polynomial.X ^ 2 : ℝ[X]).eval x = -(a * b) := by
        simpa [Polynomial.eval_sub, Polynomial.eval_pow] using hab
      have hstep :
          (sechDerivPolyStep (typeBSechBasis m m)).eval x =
            -((m : ℝ) * a ^ m * b + x * a ^ m) := by
        unfold sechDerivPolyStep
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, hderiv, hbasis, habEval]
        by_cases hm0 : m = 0
        · subst m
          simp
        · have hm1 : m = (m - 1) + 1 := by omega
          rw [hm1]
          simp [pow_succ]
          ring
      have hxeq :
          (((-2 : ℝ[X]) * sechDerivPolyStep (typeBSechBasis m m)).eval x) =
            ((((2 * m + 1 : ℝ[X]) * typeBSechBasis (m + 1) m) +
                (1 : ℝ[X]) * typeBSechBasis (m + 1) (m + 1)).eval x) := by
        calc
          (((-2 : ℝ[X]) * sechDerivPolyStep (typeBSechBasis m m)).eval x)
              = (-2 : ℝ) * (-((m : ℝ) * a ^ m * b + x * a ^ m)) := by
                  rw [Polynomial.eval_mul, hstep]
                  simp
          _ = ((2 * m : ℝ) * b + 2 * x) * a ^ m := by
                ring
          _ = ((2 * m + 1 : ℝ) * b + a) * a ^ m := by
                dsimp [a, b]
                ring
          _ = ((((2 * m + 1 : ℝ[X]) * typeBSechBasis (m + 1) m) +
                  (1 : ℝ[X]) * typeBSechBasis (m + 1) (m + 1)).eval x) := by
                rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
                  hbasis_succ_left, hbasis_succ_right]
                simp
                ring
      simpa using hxeq
    · have hk1 : 1 ≤ k := by omega
      have hmk1 : 1 ≤ m - k := by omega
      have hkpow : k = (k - 1) + 1 := by omega
      have hmpow : m - k = (m - k - 1) + 1 := by omega
      have hmksucc : m + 1 - k = m - k + 1 := by omega
      have hmksuccpow : m - k + 1 = (m - k) + 1 := by omega
      apply Polynomial.eq_of_infinite_eval_eq
      refine Set.Infinite.mono (s := (Set.univ : Set ℝ)) ?_ Set.infinite_univ
      intro x hx
      let a : ℝ := x - 1
      let b : ℝ := x + 1
      have hbasis :
          (typeBSechBasis m k).eval x = a ^ k * b ^ (m - k) := by
        simpa [a, b] using eval_typeBSechBasis_eq m k x
      have hderiv :
          (typeBSechBasis m k).derivative.eval x =
            (k : ℝ) * a ^ (k - 1) * b ^ (m - k) +
              ((m - k : ℕ) : ℝ) * a ^ k * b ^ (m - k - 1) := by
        simpa [a, b] using eval_deriv_typeBSechBasis m k x
      have hstep :
          (sechDerivPolyStep (typeBSechBasis m k)).eval x =
            -(a ^ k * b ^ (m - k) * ((k : ℝ) * b + ((m - k : ℕ) : ℝ) * a + x)) := by
        have hab : 1 - x ^ 2 = -(a * b) := by
          simp [a, b]
          ring
        have habEval : (1 - Polynomial.X ^ 2 : ℝ[X]).eval x = -(a * b) := by
          simpa [Polynomial.eval_sub, Polynomial.eval_pow] using hab
        unfold sechDerivPolyStep
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, hderiv, hbasis, habEval]
        simp [Polynomial.eval_X]
        have hmk : m - (k - 1 + 1) = m - k := by omega
        have hkpred : k - 1 + 1 - 1 = k - 1 := by omega
        have hmkpred : m - k - 1 + 1 - 1 = m - k - 1 := by omega
        rw [hkpow, hmk, hkpred, hmpow, hmkpred]
        simp [pow_succ]
        ring
      have hbasis_succ_left :
          (typeBSechBasis (m + 1) k).eval x = a ^ k * b ^ (m - k + 1) := by
        simpa [a, b, hmksucc] using eval_typeBSechBasis_eq (m + 1) k x
      have hbasis_succ_right :
          (typeBSechBasis (m + 1) (k + 1)).eval x = a ^ (k + 1) * b ^ (m - k) := by
        simpa [a, b] using eval_typeBSechBasis_eq (m + 1) (k + 1) x
      have hright :
          (((2 * k + 1 : ℝ[X]) * typeBSechBasis (m + 1) k +
              (2 * (m - k) + 1 : ℝ[X]) * typeBSechBasis (m + 1) (k + 1)).eval x) =
            a ^ k * b ^ (m - k) *
              (((2 * k + 1 : ℝ) * b) + ((2 * ((m : ℝ) - k) + 1) * a)) := by
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
          hbasis_succ_left, hbasis_succ_right]
        simp
        rw [show b ^ (m - k + 1) = b ^ (m - k) * b by rw [pow_succ]]
        rw [show a ^ (k + 1) = a ^ k * a by rw [pow_succ]]
        ring
      have hxeq :
          (((-2 : ℝ[X]) * sechDerivPolyStep (typeBSechBasis m k)).eval x) =
            (((2 * k + 1 : ℝ[X]) * typeBSechBasis (m + 1) k +
                (2 * (m - k) + 1 : ℝ[X]) * typeBSechBasis (m + 1) (k + 1)).eval x) := by
        calc
          (((-2 : ℝ[X]) * sechDerivPolyStep (typeBSechBasis m k)).eval x)
              = (-2 : ℝ) * (-(a ^ k * b ^ (m - k) *
                  ((k : ℝ) * b + ((m - k : ℕ) : ℝ) * a + x))) := by
                    rw [Polynomial.eval_mul, hstep]
                    simp
          _ = a ^ k * b ^ (m - k) *
                (((2 * k + 1 : ℝ) * b) + ((2 * ((m : ℝ) - k) + 1) * a)) := by
                  rw [Nat.cast_sub hk]
                  dsimp [a, b]
                  ring
          _ =
              (((2 * k + 1 : ℝ[X]) * typeBSechBasis (m + 1) k +
                  (2 * (m - k) + 1 : ℝ[X]) * typeBSechBasis (m + 1) (k + 1)).eval x) := by
                    rw [hright]
      simpa using hxeq

private theorem typeBSechTransform_step (m : ℕ) :
    (-2 : ℝ[X]) * sechDerivPolyStep (typeBSechTransform m) = typeBSechTransform (m + 1) := by
  let B : ℕ → ℝ[X] := fun k => typeBSechBasis (m + 1) k
  let F : ℕ → ℝ[X] := fun k =>
    Polynomial.C (typeBEulerianCoeff m k * (2 * k + 1 : ℝ)) * B k
  let G : ℕ → ℝ[X] := fun k =>
    Polynomial.C (typeBEulerianCoeff m k * (2 * (m - k) + 1 : ℝ)) * B (k + 1)
  have hExpand :
      (-2 : ℝ[X]) * sechDerivPolyStep (typeBSechTransform m) =
        (∑ k ∈ Finset.range (m + 1), F k) + ∑ k ∈ Finset.range (m + 1), G k := by
    unfold typeBSechTransform
    rw [sechDerivPolyStep_sum, Finset.mul_sum]
    calc
      ∑ k ∈ Finset.range (m + 1),
          (-2 : ℝ[X]) * sechDerivPolyStep (Polynomial.C (typeBEulerianCoeff m k) * typeBSechBasis m k)
          = ∑ k ∈ Finset.range (m + 1), (F k + G k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              dsimp [F, B]
              calc
                (-2 : ℝ[X]) *
                    sechDerivPolyStep (Polynomial.C (typeBEulerianCoeff m k) * typeBSechBasis m k)
                    = Polynomial.C (typeBEulerianCoeff m k) *
                        ((-2 : ℝ[X]) * sechDerivPolyStep (typeBSechBasis m k)) := by
                            rw [sechDerivPolyStep_C_mul]
                            ring
                _ = Polynomial.C (typeBEulerianCoeff m k) *
                        (((2 * k + 1 : ℝ[X]) * typeBSechBasis (m + 1) k) +
                          (2 * (m - k) + 1 : ℝ[X]) * typeBSechBasis (m + 1) (k + 1)) := by
                            rw [typeBSechBasis_step m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
                _ = Polynomial.C (typeBEulerianCoeff m k) *
                        ((2 * k + 1 : ℝ[X]) * typeBSechBasis (m + 1) k) +
                      Polynomial.C (typeBEulerianCoeff m k) *
                        ((2 * (m - k) + 1 : ℝ[X]) * typeBSechBasis (m + 1) (k + 1)) := by
                            rw [mul_add]
                _ = F k + G k := by
                      have hleft :
                          Polynomial.C (typeBEulerianCoeff m k) *
                              ((2 * k + 1 : ℝ[X]) * typeBSechBasis (m + 1) k) = F k := by
                        dsimp [F, B]
                        simpa using
                          (show
                            Polynomial.C (typeBEulerianCoeff m k) *
                                (Polynomial.C (2 * k + 1 : ℝ) * typeBSechBasis (m + 1) k) =
                              Polynomial.C (typeBEulerianCoeff m k * (2 * k + 1 : ℝ)) *
                                typeBSechBasis (m + 1) k by
                                  rw [← mul_assoc, ← Polynomial.C_mul])
                      have hright :
                          Polynomial.C (typeBEulerianCoeff m k) *
                              ((2 * (m - k) + 1 : ℝ[X]) * typeBSechBasis (m + 1) (k + 1)) = G k := by
                        dsimp [G, B]
                        simpa using
                          (show
                            Polynomial.C (typeBEulerianCoeff m k) *
                                (Polynomial.C (2 * (m - k) + 1 : ℝ) * typeBSechBasis (m + 1) (k + 1)) =
                              Polynomial.C (typeBEulerianCoeff m k * (2 * (m - k) + 1 : ℝ)) *
                                typeBSechBasis (m + 1) (k + 1) by
                                  rw [← mul_assoc, ← Polynomial.C_mul])
                      rw [hleft, hright]
      _ = (∑ k ∈ Finset.range (m + 1), F k) + ∑ k ∈ Finset.range (m + 1), G k := by
            rw [Finset.sum_add_distrib]
  have hFsplit :
      ∑ k ∈ Finset.range (m + 1), F k = F 0 + ∑ k ∈ Finset.range m, F (k + 1) := by
    simpa [add_assoc, add_left_comm, add_comm] using (Finset.sum_range_succ' F m)
  have hGsplit :
      ∑ k ∈ Finset.range (m + 1), G k = (∑ k ∈ Finset.range m, G k) + G m := by
    rw [Finset.sum_range_succ]
  have hF0 : F 0 = Polynomial.C (typeBEulerianCoeff (m + 1) 0) * B 0 := by
    dsimp [F, B]
    simp [typeBEulerianCoeff_zero]
  have hGm : G m = Polynomial.C (typeBEulerianCoeff (m + 1) (m + 1)) * B (m + 1) := by
    dsimp [G, B]
    simp [typeBEulerianCoeff_diag]
  have hFG :
      ∀ k ∈ Finset.range m, F (k + 1) + G k =
        Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1) := by
    intro k hk
    have hkm : k ≤ m := Nat.le_of_lt (Finset.mem_range.mp hk)
    calc
      F (k + 1) + G k
          = Polynomial.C (typeBEulerianCoeff m (k + 1) * (2 * (k + 1) + 1 : ℝ)) * B (k + 1) +
              Polynomial.C (typeBEulerianCoeff m k * (2 * (m - k) + 1 : ℝ)) * B (k + 1) := by
                simpa [F, G, B, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
                  mul_assoc] using
                  (show
                    Polynomial.C (typeBEulerianCoeff m (k + 1) * (2 * ((k + 1 : ℕ) : ℝ) + 1)) *
                        B (k + 1) +
                      Polynomial.C (typeBEulerianCoeff m k * (2 * ((m - k : ℕ) : ℝ) + 1)) *
                        B (k + 1) =
                    Polynomial.C (typeBEulerianCoeff m (k + 1) * (2 * (k + 1) + 1 : ℝ)) *
                        B (k + 1) +
                      Polynomial.C (typeBEulerianCoeff m k * (2 * (m - k) + 1 : ℝ)) *
                        B (k + 1) by rfl)
      _ =
          (Polynomial.C (typeBEulerianCoeff m (k + 1) * (2 * (k + 1) + 1 : ℝ)) +
              Polynomial.C (typeBEulerianCoeff m k * (2 * (m - k) + 1 : ℝ))) *
            B (k + 1) := by
              simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
                (add_mul
                  (Polynomial.C (typeBEulerianCoeff m (k + 1) * (2 * (k + 1) + 1 : ℝ)))
                  (Polynomial.C (typeBEulerianCoeff m k * (2 * (m - k) + 1 : ℝ)))
                  (B (k + 1))).symm
      _ = Polynomial.C
            (typeBEulerianCoeff m (k + 1) * (2 * (k + 1) + 1 : ℝ) +
              typeBEulerianCoeff m k * (2 * (m - k) + 1 : ℝ)) *
            B (k + 1) := by
              rw [← Polynomial.C_add]
      _ = Polynomial.C
            (((2 * (k : ℝ) + 3) * typeBEulerianCoeff m (k + 1)) +
              ((2 * (m : ℝ) - 2 * (k : ℝ) + 1) * typeBEulerianCoeff m k)) *
            B (k + 1) := by
            congr 2
            have hscalar :
                typeBEulerianCoeff m (k + 1) * (2 * (k + 1) + 1 : ℝ) +
                    typeBEulerianCoeff m k * (2 * (m - k) + 1 : ℝ) =
                  ((2 * (k : ℝ) + 3) * typeBEulerianCoeff m (k + 1)) +
                    ((2 * (m : ℝ) - 2 * (k : ℝ) + 1) * typeBEulerianCoeff m k) := by
              norm_num [Nat.cast_sub hkm]
              ring
            simpa using hscalar
      _ = Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1) := by
            rw [typeBEulerianCoeff_succ]
  have hTransform :
      typeBSechTransform (m + 1) =
        Polynomial.C (typeBEulerianCoeff (m + 1) 0) * B 0 +
          (∑ k ∈ Finset.range m,
            Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1)) +
              Polynomial.C (typeBEulerianCoeff (m + 1) (m + 1)) * B (m + 1) := by
    unfold typeBSechTransform
    rw [Finset.sum_range_succ']
    have htail :
        ∑ k ∈ Finset.range (m + 1),
            Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1)
          =
        (∑ k ∈ Finset.range m,
            Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1)) +
          Polynomial.C (typeBEulerianCoeff (m + 1) (m + 1)) * B (m + 1) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        (Finset.sum_range_succ
          (f := fun k ↦ Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1)) m)
    rw [htail]
    simpa [B, add_assoc, add_left_comm, add_comm]
  rw [hExpand, hFsplit, hGsplit, hF0, hGm]
  have hmid :
      (∑ k ∈ Finset.range m, F (k + 1)) + ∑ k ∈ Finset.range m, G k =
        ∑ k ∈ Finset.range m,
          Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1) := by
    calc
      (∑ k ∈ Finset.range m, F (k + 1)) + ∑ k ∈ Finset.range m, G k
          = ∑ k ∈ Finset.range m, (F (k + 1) + G k) := by
              rw [← Finset.sum_add_distrib]
      _ = ∑ k ∈ Finset.range m,
            Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              exact hFG k hk
  calc
    Polynomial.C (typeBEulerianCoeff (m + 1) 0) * B 0 +
        ∑ k ∈ Finset.range m, F (k + 1) +
          (∑ k ∈ Finset.range m, G k +
            Polynomial.C (typeBEulerianCoeff (m + 1) (m + 1)) * B (m + 1))
        =
      Polynomial.C (typeBEulerianCoeff (m + 1) 0) * B 0 +
        (∑ k ∈ Finset.range m, F (k + 1) + ∑ k ∈ Finset.range m, G k) +
          Polynomial.C (typeBEulerianCoeff (m + 1) (m + 1)) * B (m + 1) := by
            ring
    _ =
      Polynomial.C (typeBEulerianCoeff (m + 1) 0) * B 0 +
        (∑ k ∈ Finset.range m,
          Polynomial.C (typeBEulerianCoeff (m + 1) (k + 1)) * B (k + 1)) +
          Polynomial.C (typeBEulerianCoeff (m + 1) (m + 1)) * B (m + 1) := by
            rw [hmid]
    _ = typeBSechTransform (m + 1) := by
          exact hTransform.symm

private theorem typeBSechTransform_eq_scaled_sechDerivPoly :
    ∀ m : ℕ, typeBSechTransform m = Polynomial.C ((-2 : ℝ) ^ m) * sechDerivPoly m
  | 0 => by
      unfold typeBSechTransform sechDerivPoly
      simp [typeBEulerianCoeff_zero, typeBSechBasis]
  | m + 1 => by
      rw [sechDerivPoly]
      rw [← typeBSechTransform_step m, typeBSechTransform_eq_scaled_sechDerivPoly m]
      rw [sechDerivPolyStep_C_mul]
      calc
        (-2 : ℝ[X]) * (Polynomial.C ((-2 : ℝ) ^ m) * sechDerivPolyStep (sechDerivPoly m))
            = (Polynomial.C (-2 : ℝ) * Polynomial.C ((-2 : ℝ) ^ m)) *
                sechDerivPolyStep (sechDerivPoly m) := by
                  have hneg : (-2 : ℝ[X]) = Polynomial.C (-2 : ℝ) := by
                    ext n
                    cases n <;> simp
                  rw [hneg, mul_assoc]
        _ = Polynomial.C ((-2 : ℝ) * ((-2 : ℝ) ^ m)) * sechDerivPolyStep (sechDerivPoly m) := by
              rw [← Polynomial.C_mul]
        _ = Polynomial.C ((-2 : ℝ) ^ (m + 1)) * sechDerivPolyStep (sechDerivPoly m) := by
              rw [pow_succ']

private theorem typeBSechTransform_odd_eq_oddSechSquare (n : ℕ) :
    typeBSechTransform (2 * n + 3) =
      Polynomial.C ((-2 : ℝ) ^ (2 * n + 3)) *
        (Polynomial.X * (oddSechSquarePoly (n + 1)).comp (Polynomial.X ^ 2)) := by
  rw [typeBSechTransform_eq_scaled_sechDerivPoly]
  rw [show 2 * n + 3 = 2 * (n + 1) + 1 by ring, oddSechSquarePoly_spec (n + 1)]

private theorem coeff_comp_X_sq_even (p : ℝ[X]) (t : ℕ) :
    (p.comp (Polynomial.X ^ 2)).coeff (2 * t) = p.coeff t := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add]
  · intro n a
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp]
    rw [show (Polynomial.X ^ 2) ^ n = Polynomial.X ^ (2 * n) by rw [pow_mul]]
    rw [Polynomial.coeff_C_mul]
    by_cases h : n = t
    · subst h
      simp
    · have hne : 2 * n ≠ 2 * t := by
        omega
      simp [Polynomial.coeff_X_pow, hne, h]

private theorem coeff_comp_X_sq_odd (p : ℝ[X]) (t : ℕ) :
    (p.comp (Polynomial.X ^ 2)).coeff (2 * t + 1) = 0 := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, add_zero]
  · intro n a
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp]
    rw [show (Polynomial.X ^ 2) ^ n = Polynomial.X ^ (2 * n) by rw [pow_mul]]
    rw [Polynomial.coeff_C_mul]
    have hne : 2 * n ≠ 2 * t + 1 := by
      omega
    have hne' : ¬2 * t + 1 = 2 * n := by omega
    simp [Polynomial.coeff_X_pow, hne']

private theorem coeff_one_sub_X_pow (k i : ℕ) :
    ((1 - Polynomial.X : ℝ[X]) ^ k).coeff i = (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) := by
  have hscalar :
      ((1 - Polynomial.X : ℝ[X]) ^ k) =
        Polynomial.C ((-1 : ℝ) ^ k) * ((Polynomial.X - 1) ^ k) := by
    calc
      (1 - Polynomial.X : ℝ[X]) ^ k = (Polynomial.C (-1 : ℝ) * (Polynomial.X - 1)) ^ k := by
        congr
        ext j <;> cases j <;> simp
      _ = Polynomial.C ((-1 : ℝ) ^ k) * ((Polynomial.X - 1) ^ k) := by
        rw [mul_pow, ← Polynomial.C_pow]
  rw [hscalar, Polynomial.coeff_C_mul, show (Polynomial.X - 1 : ℝ[X]) = Polynomial.X + Polynomial.C (-1) by
    ext j <;> cases j <;> simp [sub_eq_add_neg]]
  rw [Polynomial.coeff_X_add_C_pow]
  by_cases hik : i ≤ k
  · have hpow :
        (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k - i) = (-1 : ℝ) ^ i := by
      have hsum : k + (k - i) = i + 2 * (k - i) := by omega
      rw [← pow_add, hsum, pow_add, pow_mul]
      norm_num
    calc
      (-1 : ℝ) ^ k * ((-1 : ℝ) ^ (k - i) * (Nat.choose k i : ℝ))
          = (((-1 : ℝ) ^ k * (-1 : ℝ) ^ (k - i)) * (Nat.choose k i : ℝ)) := by ring
      _ = (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) := by rw [hpow]
  · have hchoose : (Nat.choose k i : ℝ) = 0 := by
        simp [Nat.choose_eq_zero_of_lt (Nat.not_le.mp hik)]
    simp [hchoose]

private theorem coeff_one_sub_X_sq_pow_even (k i : ℕ) :
    ((1 - Polynomial.X ^ 2 : ℝ[X]) ^ k).coeff (2 * i) = (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) := by
  have hcomp :
      ((1 - Polynomial.X : ℝ[X]) ^ k).comp (Polynomial.X ^ 2) = (1 - Polynomial.X ^ 2 : ℝ[X]) ^ k := by
    rw [Polynomial.pow_comp]
    congr
    ext j <;> cases j <;> simp [pow_two]
  rw [← hcomp, coeff_comp_X_sq_even, coeff_one_sub_X_pow]

private theorem coeff_one_sub_X_sq_pow_odd (k i : ℕ) :
    ((1 - Polynomial.X ^ 2 : ℝ[X]) ^ k).coeff (2 * i + 1) = 0 := by
  have hcomp :
      ((1 - Polynomial.X : ℝ[X]) ^ k).comp (Polynomial.X ^ 2) = (1 - Polynomial.X ^ 2 : ℝ[X]) ^ k := by
    rw [Polynomial.pow_comp]
    congr
    ext j <;> cases j <;> simp [pow_two]
  rw [← hcomp, coeff_comp_X_sq_odd]

private theorem one_sub_X_sq_pow_eq_sum (k : ℕ) :
    ((1 - Polynomial.X ^ 2 : ℝ[X]) ^ k) =
      ∑ i ∈ Finset.range (k + 1),
        Polynomial.C (((-1 : ℝ) ^ i) * (Nat.choose k i : ℝ)) * Polynomial.X ^ (2 * i) := by
  ext d
  rw [Polynomial.finset_sum_coeff]
  rcases Nat.even_or_odd d with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [show i + i = 2 * i by omega, coeff_one_sub_X_sq_pow_even]
    by_cases hik : i ≤ k
    · rw [Finset.sum_eq_single i]
      · rw [Polynomial.coeff_C_mul_X_pow]
        simp
      · intro b hb hbi
        have hne : 2 * i ≠ 2 * b := by omega
        rw [Polynomial.coeff_C_mul_X_pow]
        simp [hne]
      · intro hi
        exfalso
        exact hi (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
    · have hchoose : (Nat.choose k i : ℝ) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (lt_of_not_ge hik)
      have hsum0 :
          ∑ b ∈ Finset.range (k + 1),
              (Polynomial.C (((-1 : ℝ) ^ b) * (Nat.choose k b : ℝ)) * Polynomial.X ^ (2 * b)).coeff
                (2 * i) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro b hb
        have hbi : b ≠ i := by
          intro hbi
          subst hbi
          exact hik (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
        have hne : 2 * i ≠ 2 * b := by omega
        rw [Polynomial.coeff_C_mul_X_pow]
        simp [hne]
      simpa [hchoose] using hsum0.symm
  · rw [coeff_one_sub_X_sq_pow_odd]
    have hsum0 :
        ∑ b ∈ Finset.range (k + 1),
            (Polynomial.C (((-1 : ℝ) ^ b) * (Nat.choose k b : ℝ)) * Polynomial.X ^ (2 * b)).coeff
              (2 * i + 1) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      have hne : 2 * i + 1 ≠ 2 * b := by omega
      rw [Polynomial.coeff_C_mul_X_pow]
      simp [hne]
    simpa using hsum0.symm

private theorem sum_range_ite_le_eq_sum_range_min (k t : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k + 1), (if i ≤ t then f i else 0) =
      ∑ i ∈ Finset.range (min k t + 1), f i := by
  by_cases hkt : k ≤ t
  · rw [Nat.min_eq_left hkt]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i ≤ t := Nat.le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hkt
    simp [hi']
  · have htk : t < k := lt_of_not_ge hkt
    rw [Nat.min_eq_right (Nat.le_of_lt htk)]
    rw [show k + 1 = (t + 1) + (k - t) by omega, Finset.sum_range_add]
    have htail :
        ∑ x ∈ Finset.range (k - t), (if t + 1 + x ≤ t then f (t + 1 + x) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hx' : ¬t + 1 + x ≤ t := by omega
      simp [hx']
    rw [htail, add_zero]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp [hi']

private theorem coeff_typeBSechBasis_odd_lower (n k t : ℕ) (hk : k < n + 2) :
    (typeBSechBasis (2 * n + 3) k).coeff (2 * t + 1) =
      (-1 : ℝ) ^ k * xiInnerCoeff (n + 2) k t := by
  have hsplit :
      typeBSechBasis (2 * n + 3) k =
        Polynomial.C ((-1 : ℝ) ^ k) *
          ((1 - Polynomial.X ^ 2 : ℝ[X]) ^ k * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k)) := by
    unfold typeBSechBasis
    rw [show 2 * n + 3 - k = k + (2 * n + 3 - 2 * k) by omega, pow_add]
    have hmul :
        ((1 - Polynomial.X : ℝ[X]) * (1 + Polynomial.X)) = (1 - Polynomial.X ^ 2 : ℝ[X]) := by
      ring
    calc
      Polynomial.C ((-1 : ℝ) ^ k) * (1 - Polynomial.X) ^ k * ((1 + Polynomial.X) ^ k * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k))
          = Polynomial.C ((-1 : ℝ) ^ k) * (((1 - Polynomial.X) ^ k * (1 + Polynomial.X) ^ k) * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k)) := by
              ring
      _ = Polynomial.C ((-1 : ℝ) ^ k) * ((((1 - Polynomial.X) * (1 + Polynomial.X)) ^ k) * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k)) := by
            rw [← mul_pow]
      _ = Polynomial.C ((-1 : ℝ) ^ k) * (((1 - Polynomial.X ^ 2 : ℝ[X]) ^ k) * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k)) := by
            rw [hmul]
  rw [hsplit, Polynomial.coeff_C_mul, one_sub_X_sq_pow_eq_sum, Finset.sum_mul,
    Polynomial.finset_sum_coeff]
  have hcoeffsum :
      ∑ i ∈ Finset.range (k + 1),
          (Polynomial.C (((-1 : ℝ) ^ i) * (Nat.choose k i : ℝ)) * Polynomial.X ^ (2 * i) *
              (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k)).coeff (2 * t + 1)
        =
      ∑ i ∈ Finset.range (k + 1),
          (((-1 : ℝ) ^ i) * (Nat.choose k i : ℝ)) *
            Polynomial.coeff
              (Polynomial.X ^ (2 * i) * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k))
              (2 * t + 1) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [show
      Polynomial.C (((-1 : ℝ) ^ i) * (Nat.choose k i : ℝ)) * Polynomial.X ^ (2 * i) *
          (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k) =
        Polynomial.C (((-1 : ℝ) ^ i) * (Nat.choose k i : ℝ)) *
          (Polynomial.X ^ (2 * i) * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k)) by ring]
    rw [Polynomial.coeff_C_mul]
  rw [hcoeffsum]
  have hinner :
      ∑ i ∈ Finset.range (k + 1),
          (((-1 : ℝ) ^ i) * (Nat.choose k i : ℝ)) *
            Polynomial.coeff
              (Polynomial.X ^ (2 * i) * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k))
              (2 * t + 1)
        = xiInnerCoeff (n + 2) k t := by
    calc
      ∑ i ∈ Finset.range (k + 1),
          (((-1 : ℝ) ^ i) * (Nat.choose k i : ℝ)) *
            Polynomial.coeff
              (Polynomial.X ^ (2 * i) * (1 + Polynomial.X) ^ (2 * n + 3 - 2 * k))
              (2 * t + 1)
          =
        ∑ i ∈ Finset.range (k + 1),
          if i ≤ t then
            (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) *
              (Nat.choose (2 * n + 3 - 2 * k) (2 * (t - i) + 1) : ℝ)
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Polynomial.coeff_X_pow_mul']
            by_cases hit : i ≤ t
            · have hle : 2 * i ≤ 2 * t + 1 := by omega
              have hindex : 2 * t + 1 - 2 * i = 2 * (t - i) + 1 := by omega
              rw [if_pos hle, if_pos hit, Polynomial.coeff_one_add_X_pow, hindex]
            · have hnot : ¬2 * i ≤ 2 * t + 1 := by omega
              rw [if_neg hnot, if_neg hit]
              ring
    _ =
      ∑ i ∈ Finset.range (min k t + 1),
        (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) *
          (Nat.choose (2 * n + 3 - 2 * k) (2 * (t - i) + 1) : ℝ) := by
            rw [sum_range_ite_le_eq_sum_range_min]
    _ = xiInnerCoeff (n + 2) k t := by
          unfold xiInnerCoeff
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp hk
          have htop : 2 * n + 3 - 2 * k = 2 * (n + 2) - 2 * k - 1 := by
            omega
          rw [htop]
  exact congrArg (fun x => (-1 : ℝ) ^ k * x) hinner

private theorem typeBSechBasis_reflect_odd (n k : ℕ) (hk : k ≤ n + 1) :
    typeBSechBasis (2 * n + 3) (2 * n + 3 - k) =
      -((typeBSechBasis (2 * n + 3) k).comp (Polynomial.C (-1 : ℝ) * Polynomial.X)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := (Set.univ : Set ℝ)) ?_ Set.infinite_univ
  intro x hx
  rw [typeBSechBasis_eq, typeBSechBasis_eq]
  have h1 : ((-x : ℝ) - 1) = -(x + 1) := by ring
  have h2 : ((-x : ℝ) + 1) = -(x - 1) := by ring
  have hodd : (-1 : ℝ) ^ (2 * n + 3) = -1 := by
    calc
      (-1 : ℝ) ^ (2 * n + 3) = (-1 : ℝ) ^ (2 * n + 2) * (-1 : ℝ) := by
        rw [show 2 * n + 3 = 2 * n + 2 + 1 by ring, pow_add]
        norm_num
      _ = -1 := by
        rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul]
        norm_num
  have hpow : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (2 * n + 3 - k) = -1 := by
    have hsum : k + (2 * n + 3 - k) = 2 * n + 3 := by omega
    rw [← pow_add, hsum, hodd]
  have hk' : 2 * n + 3 - (2 * n + 3 - k) = k := by omega
  simp [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X, hk']
  have hneg1 : (-(x + 1)) ^ k = (-1 : ℝ) ^ k * (x + 1) ^ k := by
    rw [show -(x + 1) = (-1 : ℝ) * (x + 1) by ring, mul_pow]
  have hneg2 :
      (-(x - 1)) ^ (2 * n + 3 - k) =
        (-1 : ℝ) ^ (2 * n + 3 - k) * (x - 1) ^ (2 * n + 3 - k) := by
    rw [show -(x - 1) = (-1 : ℝ) * (x - 1) by ring, mul_pow]
  rw [h1, h2, hneg1, hneg2]
  symm
  calc
    -(((-1 : ℝ) ^ k * (x + 1) ^ k * ((-1 : ℝ) ^ (2 * n + 3 - k) * (x - 1) ^ (2 * n + 3 - k)))) =
        -(((-1 : ℝ) ^ k * (-1 : ℝ) ^ (2 * n + 3 - k)) *
            ((x + 1) ^ k * (x - 1) ^ (2 * n + 3 - k))) := by
              ring
    _ = (x + 1) ^ k * (x - 1) ^ (2 * n + 3 - k) := by
          rw [hpow]
          ring
    _ = (x - 1) ^ (2 * n + 3 - k) * (x + 1) ^ k := by
          ring

private theorem coeff_typeBSechBasis_odd_upper (n k t : ℕ) (hk : k ≤ n + 1) :
    (typeBSechBasis (2 * n + 3) (2 * n + 3 - k)).coeff (2 * t + 1) =
      (typeBSechBasis (2 * n + 3) k).coeff (2 * t + 1) := by
  rw [typeBSechBasis_reflect_odd n k hk, Polynomial.coeff_neg, Polynomial.comp_C_mul_X_coeff]
  have hsign : (-1 : ℝ) ^ (2 * t + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hsign]
  ring

private theorem coeff_typeBSechTransform_odd_eq_two_rawAdaptedXiCoeff (n t : ℕ) :
    (typeBSechTransform (2 * n + 3)).coeff (2 * t + 1) = 2 * rawAdaptedXiCoeff (n + 2) t := by
  let f : ℕ → ℝ := fun k =>
    typeBEulerianCoeff (2 * n + 3) k *
      (typeBSechBasis (2 * n + 3) k).coeff (2 * t + 1)
  have hcoeff :
      (typeBSechTransform (2 * n + 3)).coeff (2 * t + 1) =
        ∑ k ∈ Finset.range (2 * (n + 2)), f k := by
    unfold typeBSechTransform
    rw [show 2 * n + 3 + 1 = 2 * (n + 2) by ring, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [f, Polynomial.coeff_C_mul]
  have hlower :
      ∑ k ∈ Finset.range (n + 2), f k = rawAdaptedXiCoeff (n + 2) t := by
    unfold rawAdaptedXiCoeff
    refine Finset.sum_congr rfl ?_
    intro k hk
    dsimp [f]
    have hindex : 2 * (n + 2) - 1 = 2 * n + 3 := by omega
    rw [coeff_typeBSechBasis_odd_lower n k t (Finset.mem_range.mp hk)]
    simpa [hindex, mul_comm, mul_left_comm, mul_assoc]
  have hupper :
      ∑ k ∈ Finset.range (n + 2), f (n + 2 + k) =
        ∑ k ∈ Finset.range (n + 2), f k := by
    calc
      ∑ k ∈ Finset.range (n + 2), f (n + 2 + k)
          = ∑ k ∈ Finset.range (n + 2), f (n + 1 - k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
              have hindex : n + 2 + k = 2 * n + 3 - (n + 1 - k) := by omega
              rw [hindex]
              dsimp [f]
              rw [typeBEulerianCoeff_symm (m := 2 * n + 3) (k := n + 1 - k) (by omega)]
              rw [coeff_typeBSechBasis_odd_upper n (n + 1 - k) t (by omega)]
      _ = ∑ k ∈ Finset.range (n + 2), f k := by
            simpa using (Finset.sum_range_reflect f (n + 2))
  calc
    (typeBSechTransform (2 * n + 3)).coeff (2 * t + 1)
        = ∑ k ∈ Finset.range (2 * (n + 2)), f k := hcoeff
    _ =
      (∑ k ∈ Finset.range (n + 2), f k) +
        ∑ k ∈ Finset.range (n + 2), f (n + 2 + k) := by
          rw [← Finset.sum_range_add]
          congr 1
          ring_nf
    _ = rawAdaptedXiCoeff (n + 2) t + rawAdaptedXiCoeff (n + 2) t := by
          rw [hlower, hupper, hlower]
    _ = 2 * rawAdaptedXiCoeff (n + 2) t := by ring

private theorem coeff_typeBSechTransform_odd_eq_two_solverSechXiExact (n t : ℕ) :
    (typeBSechTransform (2 * n + 3)).coeff (2 * t + 1) = 2 * (solverSechXiExact n).coeff t := by
  rw [typeBSechTransform_odd_eq_oddSechSquare, Polynomial.coeff_C_mul]
  have hcoeff :
      (Polynomial.X * (oddSechSquarePoly (n + 1)).comp (Polynomial.X ^ 2)).coeff (2 * t + 1) =
        (oddSechSquarePoly (n + 1)).coeff t := by
    rw [show 2 * t + 1 = 2 * t + 1 by ring, Polynomial.coeff_X_mul, coeff_comp_X_sq_even]
  rw [hcoeff, coeff_solverSechXiExact]
  have hscalar : ((-2 : ℝ) ^ (2 * n + 3)) = 2 * (-((4 : ℝ) ^ (n + 1))) := by
    rw [show 2 * n + 3 = 2 * (n + 1) + 1 by ring, pow_add, pow_one, show (-2 : ℝ) ^ (2 * (n + 1)) = ((-2 : ℝ) ^ 2) ^ (n + 1) by rw [pow_mul]]
    norm_num
    ring
  rw [hscalar]
  ring

private theorem rawAdaptedXiCoeff_eq_solverSechXiExact_coeff (n t : ℕ) :
    rawAdaptedXiCoeff (n + 2) t = (solverSechXiExact n).coeff t := by
  have hraw := coeff_typeBSechTransform_odd_eq_two_rawAdaptedXiCoeff n t
  have hsech := coeff_typeBSechTransform_odd_eq_two_solverSechXiExact n t
  linarith

private theorem xiInnerCoeff_eq_zero_of_large_t (n k t : ℕ) (hk : k < n + 2) (ht : n + 2 ≤ t) :
    xiInnerCoeff (n + 2) k t = 0 := by
  unfold xiInnerCoeff
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hik : i ≤ k := by
    exact Nat.le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) (Nat.min_le_left _ _)
  have hchoose :
      (Nat.choose (2 * (n + 2) - 2 * k - 1) (2 * (t - i) + 1) : ℝ) = 0 := by
    have hlt : 2 * (n + 2) - 2 * k - 1 < 2 * (t - i) + 1 := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  simp [hchoose]

private theorem rawAdaptedXiCoeff_eq_zero_of_large_t (n t : ℕ) (ht : n + 2 ≤ t) :
    rawAdaptedXiCoeff (n + 2) t = 0 := by
  unfold rawAdaptedXiCoeff
  refine Finset.sum_eq_zero ?_
  intro k hk
  rw [xiInnerCoeff_eq_zero_of_large_t n k t (Finset.mem_range.mp hk) ht]
  simp

theorem solverRawAdaptedXi_eq_solverSechXiExact (n : ℕ) :
    solverRawAdaptedXi n = solverSechXiExact n := by
  ext t
  by_cases ht : t < n + 2
  · rw [coeff_solverRawAdaptedXi, if_pos ht]
    exact rawAdaptedXiCoeff_eq_solverSechXiExact_coeff n t
  · have ht' : n + 2 ≤ t := Nat.not_lt.mp ht
    rw [coeff_solverRawAdaptedXi, if_neg ht]
    rw [← rawAdaptedXiCoeff_eq_solverSechXiExact_coeff n t,
      rawAdaptedXiCoeff_eq_zero_of_large_t n t ht']


private theorem eval_typeBSechBasis_mobius (m k : ℕ) (hk : k ≤ m)
    {y : ℝ} (hy : y ≠ 1) :
    (typeBSechBasis m k).eval ((1 + y) / (1 - y)) =
      (2 / (1 - y)) ^ m * y ^ k := by
  have hy' : 1 - y ≠ 0 := sub_ne_zero.mpr hy.symm
  have hsub : 1 - (1 + y) / (1 - y) = -((2 * y) / (1 - y)) := by
    field_simp [hy']
    ring
  have hadd : 1 + (1 + y) / (1 - y) = 2 / (1 - y) := by
    field_simp [hy']
    ring
  have hsplit : (2 * y) / (1 - y) = (2 / (1 - y)) * y := by
    field_simp [hy']
  unfold typeBSechBasis
  simp [hsub, hadd]
  calc
    (-1 : ℝ) ^ k * (-((2 * y) / (1 - y))) ^ k * (2 / (1 - y)) ^ (m - k)
        = ((2 * y) / (1 - y)) ^ k * (2 / (1 - y)) ^ (m - k) := by
            rw [show (-((2 * y) / (1 - y))) = (-1 : ℝ) * ((2 * y) / (1 - y)) by ring]
            rw [mul_pow, ← mul_assoc, ← pow_add]
            simp
    _ = ((2 / (1 - y)) * y) ^ k * (2 / (1 - y)) ^ (m - k) := by rw [hsplit]
    _ = (2 / (1 - y)) ^ k * y ^ k * (2 / (1 - y)) ^ (m - k) := by rw [mul_pow]
    _ = (2 / (1 - y)) ^ m * y ^ k := by
          calc
            (2 / (1 - y)) ^ k * y ^ k * (2 / (1 - y)) ^ (m - k)
                = (2 / (1 - y)) ^ k * (2 / (1 - y)) ^ (m - k) * y ^ k := by ring
            _ = (2 / (1 - y)) ^ m * y ^ k := by
                  rw [← pow_add, Nat.add_sub_of_le hk]

theorem eval_typeBSechTransform_mobius (m : ℕ) {y : ℝ} (hy : y ≠ 1) :
    (typeBSechTransform m).eval ((1 + y) / (1 - y)) =
      (2 / (1 - y)) ^ m * (typeBEulerianPoly m).eval y := by
  let a : ℝ := (1 + y) / (1 - y)
  let e : ℝ[X] →+* ℝ := Polynomial.evalRingHom a
  let ey : ℝ[X] →+* ℝ := Polynomial.evalRingHom y
  have hEvalTransform :
      (typeBSechTransform m).eval a =
        ∑ k ∈ Finset.range (m + 1),
          typeBEulerianCoeff m k * (typeBSechBasis m k).eval a := by
    unfold typeBSechTransform
    change e (∑ k ∈ Finset.range (m + 1), Polynomial.C (typeBEulerianCoeff m k) * typeBSechBasis m k) =
      _
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [e, a, Polynomial.eval_mul, Polynomial.eval_C]
  have hEvalPoly :
      (typeBEulerianPoly m).eval y =
        ∑ k ∈ Finset.range (m + 1), typeBEulerianCoeff m k * y ^ k := by
    unfold typeBEulerianPoly
    change ey (∑ k ∈ Finset.range (m + 1), Polynomial.C (typeBEulerianCoeff m k) * Polynomial.X ^ k) =
      _
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [ey, Polynomial.eval_mul, Polynomial.eval_C]
  calc
    (typeBSechTransform m).eval ((1 + y) / (1 - y))
        =
      ∑ k ∈ Finset.range (m + 1),
        typeBEulerianCoeff m k *
          (typeBSechBasis m k).eval ((1 + y) / (1 - y)) := by
            simpa [a] using hEvalTransform
    _ =
      ∑ k ∈ Finset.range (m + 1),
        typeBEulerianCoeff m k * ((2 / (1 - y)) ^ m * y ^ k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [eval_typeBSechBasis_mobius m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hy]
    _ =
      ∑ k ∈ Finset.range (m + 1),
        (2 / (1 - y)) ^ m * (typeBEulerianCoeff m k * y ^ k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ =
      (2 / (1 - y)) ^ m * ∑ k ∈ Finset.range (m + 1), typeBEulerianCoeff m k * y ^ k := by
        rw [← Finset.mul_sum]
    _ =
      (2 / (1 - y)) ^ m * (typeBEulerianPoly m).eval y := by
        rw [hEvalPoly]

end TypeBSechBridge

theorem solverSechXiExact_coeff_ratio_from_odd_constants (n : ℕ)
    (h0 : (oddSechSquarePoly (n + 1)).coeff 0 ≠ 0) :
    -((solverSechXiExact n).coeff 1) / (solverSechXiExact n).coeff 0 =
      (-(oddSechSquarePoly (n + 2)).coeff 0 / (oddSechSquarePoly (n + 1)).coeff 0 - 5) / 6 := by
  have hpow : ((4 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  have hscale : (-((4 : ℝ) ^ (n + 1))) ≠ 0 := by
    exact neg_ne_zero.mpr hpow
  have hcancel :
      -((solverSechXiExact n).coeff 1) / (solverSechXiExact n).coeff 0 =
        -((oddSechSquarePoly (n + 1)).coeff 1) / (oddSechSquarePoly (n + 1)).coeff 0 := by
    rw [coeff_solverSechXiExact, coeff_solverSechXiExact]
    field_simp [h0, hscale]
  rw [hcancel, oddSechSquarePoly_coeff_ratio (n + 1) h0]

theorem solverRawAdaptedXi_coeff_ratio_from_odd_constants (n : ℕ)
    (h0 : (oddSechSquarePoly (n + 1)).coeff 0 ≠ 0) :
    -((solverRawAdaptedXi n).coeff 1) / (solverRawAdaptedXi n).coeff 0 =
      (-(oddSechSquarePoly (n + 2)).coeff 0 / (oddSechSquarePoly (n + 1)).coeff 0 - 5) / 6 := by
  rw [solverRawAdaptedXi_eq_solverSechXiExact]
  exact solverSechXiExact_coeff_ratio_from_odd_constants n h0

private theorem oddSechSquarePoly_coeff_zero_ne_zero_succ (n : ℕ) :
    (oddSechSquarePoly (n + 1)).coeff 0 ≠ 0 := by
  have hbeta :
      PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries ≠ 0 := by
    rw [coeff_bernoulliQuarterOddSeries_odd_eq_dirichletBetaOddShift]
    refine div_ne_zero ?_ ?_
    · exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num))
        (dirichletBetaOddShift_pos n).ne'
    · positivity
  have hcoeff :
      PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries =
        -(1 / 2 : ℝ) *
          (((1 / 4 : ℝ) ^ (2 * (n + 2))) * (oddSechSquarePoly (n + 1)).coeff 0 /
            (((2 * (n + 2)).factorial : ℕ) : ℝ)) := by
    rw [coeff_bernoulliQuarterOddSeries_odd_eq_iteratedDeriv_realSech,
      iteratedDeriv_two_mul_succ_realSech_zero (n + 1)]
  intro h0
  rw [h0] at hcoeff
  simp at hcoeff
  exact hbeta hcoeff

private theorem oddSechSquarePoly_constant_ratio_eq_secantEulerRatioShift (n : ℕ) :
    -((oddSechSquarePoly (n + 2)).coeff 0) / (oddSechSquarePoly (n + 1)).coeff 0 =
      secantEulerRatioShift n := by
  let c0 : ℝ := PowerSeries.coeff (2 * (n + 2) + 1) bernoulliQuarterOddSeries
  let c1 : ℝ := PowerSeries.coeff (2 * (n + 3) + 1) bernoulliQuarterOddSeries
  have hc0_beta :
      c0 =
        (-1 : ℝ) ^ (n + 3) * 4 * dirichletBetaOddShift n / (2 * Real.pi) ^ (2 * n + 5) := by
    simpa [c0] using coeff_bernoulliQuarterOddSeries_odd_eq_dirichletBetaOddShift n
  have hc1_beta :
      c1 =
        (-1 : ℝ) ^ (n + 4) * 4 * dirichletBetaOddShift (n + 1) / (2 * Real.pi) ^ (2 * n + 7) := by
    simpa [c1, add_comm, add_left_comm, add_assoc, mul_add, add_mul, two_mul] using
      coeff_bernoulliQuarterOddSeries_odd_eq_dirichletBetaOddShift (n + 1)
  have hc0_real :
      c0 =
        -(1 / 2 : ℝ) *
          (((1 / 4 : ℝ) ^ (2 * (n + 2))) * (oddSechSquarePoly (n + 1)).coeff 0 /
            (((2 * (n + 2)).factorial : ℕ) : ℝ)) := by
    simpa [c0, iteratedDeriv_two_mul_succ_realSech_zero (n + 1)] using
      coeff_bernoulliQuarterOddSeries_odd_eq_iteratedDeriv_realSech (n + 2)
  have hc1_real :
      c1 =
        -(1 / 2 : ℝ) *
          (((1 / 4 : ℝ) ^ (2 * (n + 3))) * (oddSechSquarePoly (n + 2)).coeff 0 /
            (((2 * (n + 3)).factorial : ℕ) : ℝ)) := by
    simpa [c1, iteratedDeriv_two_mul_succ_realSech_zero (n + 2)] using
      coeff_bernoulliQuarterOddSeries_odd_eq_iteratedDeriv_realSech (n + 3)
  have hc0_ne : c0 ≠ 0 := by
    rw [hc0_beta]
    refine div_ne_zero ?_ ?_
    · exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num))
        (dirichletBetaOddShift_pos n).ne'
    · positivity
  have hodd0 : (oddSechSquarePoly (n + 1)).coeff 0 ≠ 0 :=
    oddSechSquarePoly_coeff_zero_ne_zero_succ n
  have hfac :
      ((((2 * (n + 3)).factorial : ℕ) : ℝ)) =
        (2 * n + 6 : ℝ) * (2 * n + 5 : ℝ) * ((((2 * (n + 2)).factorial : ℕ) : ℝ)) := by
    have hcast1 : (((2 * n + 5 + 1 : ℕ) : ℝ)) = (2 * n + 6 : ℝ) := by
      have hreal : (2 * (n : ℝ) + 5 + 1) = 2 * n + 6 := by ring
      simpa [Nat.cast_add, Nat.cast_mul] using hreal
    have hcast2 : (((2 * (n + 2) + 1 : ℕ) : ℝ)) = (2 * n + 5 : ℝ) := by
      have hreal : (2 * ((n : ℝ) + 2) + 1) = 2 * n + 5 := by ring
      simpa [Nat.cast_add, Nat.cast_mul] using hreal
    calc
      ((((2 * (n + 3)).factorial : ℕ) : ℝ))
          = (2 * n + 6 : ℝ) * ((((2 * n + 5).factorial : ℕ) : ℝ)) := by
              rw [show 2 * (n + 3) = 2 * n + 5 + 1 by ring, Nat.factorial_succ, Nat.cast_mul, hcast1]
      _ = (2 * n + 6 : ℝ) * ((2 * n + 5 : ℝ) * ((((2 * (n + 2)).factorial : ℕ) : ℝ))) := by
            rw [show 2 * n + 5 = 2 * (n + 2) + 1 by ring, Nat.factorial_succ, Nat.cast_mul, hcast2]
      _ = (2 * n + 6 : ℝ) * (2 * n + 5 : ℝ) * ((((2 * (n + 2)).factorial : ℕ) : ℝ)) := by
            ring
  have hratio_real :
      c1 / c0 =
        (oddSechSquarePoly (n + 2)).coeff 0 /
          (16 * (2 * n + 6 : ℝ) * (2 * n + 5 : ℝ) * (oddSechSquarePoly (n + 1)).coeff 0) := by
    rw [hc1_real, hc0_real, hfac]
    field_simp [hodd0]
    ring
  have hratio_beta :
      c1 / c0 =
        -(dirichletBetaOddShift (n + 1)) /
          (4 * Real.pi ^ 2 * dirichletBetaOddShift n) := by
    rw [hc1_beta, hc0_beta]
    have hβ0 : dirichletBetaOddShift n ≠ 0 := (dirichletBetaOddShift_pos n).ne'
    field_simp [hβ0, Real.pi_ne_zero]
    ring
  have hratio :
      (oddSechSquarePoly (n + 2)).coeff 0 /
          (16 * (2 * n + 6 : ℝ) * (2 * n + 5 : ℝ) * (oddSechSquarePoly (n + 1)).coeff 0) =
        -(dirichletBetaOddShift (n + 1)) /
          (4 * Real.pi ^ 2 * dirichletBetaOddShift n) := by
    exact hratio_real.symm.trans hratio_beta
  have hβ0 : dirichletBetaOddShift n ≠ 0 := (dirichletBetaOddShift_pos n).ne'
  rw [secantEulerRatioShift]
  field_simp [hodd0, hβ0, Real.pi_ne_zero] at hratio ⊢
  ring_nf at hratio ⊢
  linarith

theorem solverRawAdaptedXi_coeff_ratio_eq_secantEulerRatioShift (n : ℕ) :
    -((solverRawAdaptedXi n).coeff 1) / (solverRawAdaptedXi n).coeff 0 =
      (secantEulerRatioShift n - 5) / 6 := by
  rw [solverRawAdaptedXi_coeff_ratio_from_odd_constants n
    (oddSechSquarePoly_coeff_zero_ne_zero_succ n),
    oddSechSquarePoly_constant_ratio_eq_secantEulerRatioShift]

section OddSechRootTheory

private theorem natDegree_one_sub_X_sq_le :
    (((1 : ℝ[X]) - Polynomial.X ^ 2).natDegree) ≤ 2 := by
  have h1 : (1 : ℝ[X]).natDegree ≤ 2 := by simp
  have h2 : (Polynomial.X ^ 2 : ℝ[X]).natDegree ≤ 2 := by simp
  exact Polynomial.natDegree_sub_le_of_le h1 h2

private theorem natDegree_sechDerivPoly_le : ∀ n : ℕ, (sechDerivPoly n).natDegree ≤ n
  | 0 => by simp [sechDerivPoly]
  | n + 1 => by
      have hder :
          (sechDerivPoly n).derivative.natDegree ≤ n - 1 := by
        exact (Polynomial.natDegree_derivative_le _).trans <|
          Nat.sub_le_sub_right (natDegree_sechDerivPoly_le n) 1
      have hleft :
          (((1 : ℝ[X]) - Polynomial.X ^ 2) * (sechDerivPoly n).derivative).natDegree ≤ n + 1 := by
        cases n with
        | zero =>
            simp [sechDerivPoly]
        | succ n =>
            have hmul :
                (((1 : ℝ[X]) - Polynomial.X ^ 2) * (sechDerivPoly (n + 1)).derivative).natDegree ≤
                  2 + n := by
              simpa using
                (Polynomial.natDegree_mul_le_of_le natDegree_one_sub_X_sq_le hder)
            exact hmul.trans (by omega)
      have hright :
          (Polynomial.X * sechDerivPoly n).natDegree ≤ n + 1 := by
        by_cases hp : sechDerivPoly n = 0
        · simp [hp]
        · exact (Polynomial.natDegree_X_mul hp).le.trans <|
            Nat.add_le_add_right (natDegree_sechDerivPoly_le n) 1
      simpa [sechDerivPoly, sechDerivPolyStep] using
        (Polynomial.natDegree_sub_le_of_le hleft hright)

private theorem coeff_sechDerivPoly_highest_succ (n : ℕ) :
    (sechDerivPoly (n + 1)).coeff (n + 1) =
      -((n + 1 : ℝ)) * (sechDerivPoly n).coeff n := by
  cases n with
  | zero =>
      simp [sechDerivPoly, sechDerivPolyStep]
  | succ n =>
      let p : ℝ[X] := sechDerivPoly (n + 1)
      have htop : p.derivative.coeff (n + 2) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hpdeg : p.natDegree ≤ n + 1 := by
          simpa [p] using natDegree_sechDerivPoly_le (n + 1)
        exact lt_of_le_of_lt (Polynomial.natDegree_derivative_le p) (by omega)
      have hrepr :
          sechDerivPoly (n + 2) =
            p.derivative - Polynomial.X ^ 2 * p.derivative - Polynomial.X * p := by
        simp [sechDerivPoly, sechDerivPolyStep, p]
        ring
      rw [hrepr]
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, htop]
      rw [show n + 2 = n + 2 by omega, Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_mul]
      simp [p, Polynomial.coeff_derivative]
      ring_nf

private theorem coeff_sechDerivPoly_diag (n : ℕ) :
    (sechDerivPoly n).coeff n = (-1 : ℝ) ^ n * (n.factorial : ℝ) := by
  induction n with
  | zero =>
      simp [sechDerivPoly]
  | succ n ih =>
      rw [coeff_sechDerivPoly_highest_succ, ih, Nat.factorial_succ, Nat.cast_mul, pow_succ]
      have htmp :
          -((n + 1 : ℝ)) * ((-1 : ℝ) ^ n * (n.factorial : ℝ)) =
            -((n.factorial : ℝ) * (n + 1 : ℝ) * (-1 : ℝ) ^ n) := by
              ring
      rw [htmp]
      rw [Nat.cast_add]
      ring

private theorem coeff_sechDerivPoly_diag_ne_zero (n : ℕ) :
    (sechDerivPoly n).coeff n ≠ 0 := by
  rw [coeff_sechDerivPoly_diag]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n)

private theorem sechDerivPoly_ne_zero (n : ℕ) : sechDerivPoly n ≠ 0 := by
  intro h
  exact coeff_sechDerivPoly_diag_ne_zero n (by simpa [h])

private theorem natDegree_sechDerivPoly (n : ℕ) :
    (sechDerivPoly n).natDegree = n := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_sechDerivPoly_le n) (coeff_sechDerivPoly_diag_ne_zero n)

private theorem oddSechSquarePoly_ne_zero (n : ℕ) :
    oddSechSquarePoly n ≠ 0 := by
  intro h
  have hp : sechDerivPoly (2 * n + 1) = 0 := by
    simpa [oddSechSquarePoly_spec n, h]
  exact sechDerivPoly_ne_zero (2 * n + 1) hp

private theorem natDegree_oddSechSquarePoly (n : ℕ) :
    (oddSechSquarePoly n).natDegree = n := by
  let q : ℝ[X] := oddSechSquarePoly n
  have hq : q ≠ 0 := oddSechSquarePoly_ne_zero n
  have hcomp : q.comp (Polynomial.X ^ 2) ≠ 0 := by
    intro hzero
    rcases Polynomial.comp_eq_zero_iff.mp hzero with hq0 | hconst
    · exact hq hq0
    · have hX : (Polynomial.X ^ 2 : ℝ[X]) ≠ Polynomial.C (((Polynomial.X ^ 2 : ℝ[X]).coeff 0)) := by
        simp
      exact hX hconst.2
  have hnat : (sechDerivPoly (2 * n + 1)).natDegree = 2 * n + 1 :=
    natDegree_sechDerivPoly (2 * n + 1)
  rw [oddSechSquarePoly_spec n, Polynomial.natDegree_X_mul hcomp,
    Polynomial.natDegree_comp, Polynomial.natDegree_X_pow] at hnat
  have hmul : q.natDegree * 2 = 2 * n := by
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hnat)
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (by simpa [Nat.mul_comm] using hmul)

private theorem eval_sechDerivPoly_odd (n : ℕ) (x : ℝ) :
    (sechDerivPoly (2 * n + 1)).eval (-x) = -((sechDerivPoly (2 * n + 1)).eval x) := by
  rw [oddSechSquarePoly_spec n]
  simp [pow_two]

private theorem roots_eq_positiveSquares_oddSechSquarePoly (n : ℕ) :
    ∃ S : Finset ℝ,
      (oddSechSquarePoly n).roots = S.val ∧
      S.card = n ∧
      (∀ y ∈ S, 0 < y) := by
  let p : ℝ[X] := sechDerivPoly (2 * n + 1)
  let q : ℝ[X] := oddSechSquarePoly n
  have hp : p ≠ 0 := sechDerivPoly_ne_zero (2 * n + 1)
  have hq : q ≠ 0 := oddSechSquarePoly_ne_zero n
  rcases exists_strictMono_roots_sechDerivPoly (2 * n + 1) with ⟨roots, hmono, hmem, hroot⟩
  let T : Finset ℝ := Finset.univ.image roots
  have hcardT : T.card = 2 * n + 1 := by
    simpa [T] using Finset.card_image_of_injective Finset.univ hmono.injective
  have hrootsT : p.roots = T.val := by
    refine Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero ?_ ?_ hp
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
      exact hroot i
    · rw [natDegree_sechDerivPoly, hcardT]
  have hzeroMem : (0 : ℝ) ∈ T := by
    have hzeroEval : p.eval 0 = 0 := by
      have hodd := eval_sechDerivPoly_odd n 0
      have hzero : p.eval 0 = -(p.eval 0) := by simpa using hodd
      linarith
    have hzeroRoots : (0 : ℝ) ∈ p.roots := by
      rw [Polynomial.mem_roots hp]
      simpa using hzeroEval
    exact (by simpa [hrootsT] using hzeroRoots : (0 : ℝ) ∈ T)
  have hnegClosed : ∀ x, x ∈ T → -x ∈ T := by
    intro x hx
    have hxroot : p.eval x = 0 := by
      have hxroots : x ∈ p.roots := by
        simpa [hrootsT] using hx
      exact (Polynomial.mem_roots hp).1 hxroots
    have hnegroot : p.eval (-x) = 0 := by
      rw [eval_sechDerivPoly_odd n x, hxroot]
      ring
    have hnegroots : (-x : ℝ) ∈ p.roots := by
      rw [Polynomial.mem_roots hp]
      exact hnegroot
    simpa [hrootsT] using hnegroots
  let Tneg : Finset ℝ := T.filter fun x ↦ x < 0
  let Tpos : Finset ℝ := T.filter fun x ↦ 0 < x
  have hcardNegEqPos : Tneg.card = Tpos.card := by
    have hmapNeg : Tneg.image (fun x ↦ -x) = Tpos := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        rcases Finset.mem_filter.mp hy with ⟨hyT, hyneg⟩
        exact Finset.mem_filter.mpr ⟨hnegClosed y hyT, by nlinarith [hyneg]⟩
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hxT, hxpos⟩
        apply Finset.mem_image.mpr
        refine ⟨-x, Finset.mem_filter.mpr ?_, by ring⟩
        exact ⟨hnegClosed x hxT, by nlinarith [hxpos]⟩
    calc
      Tneg.card = (Tneg.image fun x ↦ -x).card := by
        have hnegInj : Function.Injective (fun x : ℝ => -x) := by
          intro x y hxy
          linarith
        exact (Finset.card_image_of_injective Tneg hnegInj).symm
      _ = Tpos.card := by rw [hmapNeg]
  have hzeroFilter : (T.filter fun x ↦ x = 0) = ({0} : Finset ℝ) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨-, hx0⟩
      simpa [hx0]
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      subst x
      exact Finset.mem_filter.mpr ⟨hzeroMem, rfl⟩
  have hsplit₁ :
      Tneg.card + (T.filter fun x ↦ ¬x < 0).card = T.card := by
    simpa [Tneg] using (Finset.card_filter_add_card_filter_not (s := T) (p := fun x ↦ x < 0))
  have hsplit₂ :
      (T.filter fun x ↦ x = 0).card + Tpos.card = (T.filter fun x ↦ ¬x < 0).card := by
    have haux := Finset.card_filter_add_card_filter_not
      (s := T.filter fun x ↦ ¬x < 0) (p := fun x ↦ x = 0)
    have hzeroEq :
        (T.filter fun x ↦ ¬x < 0).filter (fun x ↦ x = 0) = T.filter fun x ↦ x = 0 := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hxN, hx0⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxN).1, hx0⟩
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hxT, hx0⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxT, ?_⟩, hx0⟩
        simpa [hx0]
    have hposEq :
        (T.filter fun x ↦ ¬x < 0).filter (fun x ↦ ¬x = 0) = Tpos := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hxN, hxne0⟩
        rcases Finset.mem_filter.mp hxN with ⟨hxT, hxnonneg⟩
        exact Finset.mem_filter.mpr ⟨hxT, lt_of_le_of_ne (not_lt.mp hxnonneg) (Ne.symm hxne0)⟩
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hxT, hxpos⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxT, not_lt.mpr (le_of_lt hxpos)⟩, ?_⟩
        linarith [hxpos]
    rw [hzeroEq, hposEq] at haux
    simpa [add_comm] using haux
  have hcardPos : Tpos.card = n := by
    rw [hzeroFilter, Finset.card_singleton] at hsplit₂
    rw [← hsplit₂, hcardNegEqPos] at hsplit₁
    rw [hcardT] at hsplit₁
    omega
  let S : Finset ℝ := Tpos.image fun x ↦ x ^ 2
  have hcardS : S.card = n := by
    have hsqInj : Set.InjOn (fun x : ℝ => x ^ 2) Tpos := by
      intro x hx y hy hxy
      have hxpos : 0 < x := by
        change x ∈ T.filter (fun x ↦ 0 < x) at hx
        exact (Finset.mem_filter.mp hx).2
      have hypos : 0 < y := by
        change y ∈ T.filter (fun x ↦ 0 < x) at hy
        exact (Finset.mem_filter.mp hy).2
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with h | h
      · exact h
      · linarith
    dsimp [S]
    rw [Finset.card_image_of_injOn hsqInj, hcardPos]
  have hrootS : ∀ y ∈ S, q.eval y = 0 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxroot : p.eval x = 0 := by
      have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
      have hxroots : x ∈ p.roots := by
        simpa [hrootsT] using hxT
      exact (Polynomial.mem_roots hp).1 hxroots
    have hxne : x ≠ 0 := ne_of_gt ((Finset.mem_filter.mp hx).2)
    have hxroot' :
        x * q.eval (x ^ 2) = 0 := by
      simpa [p, q, oddSechSquarePoly_spec n, Polynomial.eval_mul, Polynomial.eval_comp, pow_two] using hxroot
    exact (mul_eq_zero.mp hxroot').resolve_left hxne
  have hrootsS : q.roots = S.val := by
    refine Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hrootS ?_ hq
    rw [natDegree_oddSechSquarePoly, hcardS]
  refine ⟨S, hrootsS, hcardS, ?_⟩
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  exact sq_pos_iff.mpr (ne_of_gt ((Finset.mem_filter.mp hx).2))

private theorem oddSechSquarePoly_splits (n : ℕ) :
    (oddSechSquarePoly n).Splits := by
  rcases roots_eq_positiveSquares_oddSechSquarePoly n with ⟨S, hroots, hcard, -⟩
  rw [Polynomial.splits_iff_card_roots]
  simpa [hroots, hcard, natDegree_oddSechSquarePoly n]

private theorem oddSechSquarePoly_separable (n : ℕ) :
    (oddSechSquarePoly n).Separable := by
  rw [← Polynomial.nodup_roots_iff_of_splits (oddSechSquarePoly_ne_zero n)
    (oddSechSquarePoly_splits n)]
  rcases roots_eq_positiveSquares_oddSechSquarePoly n with ⟨S, hroots, -, -⟩
  simpa [hroots] using S.2

private theorem solverRawAdaptedXi_roots_eq_positiveFinset (n : ℕ) :
    ∃ S : Finset ℝ,
      (solverRawAdaptedXi n).roots = S.val ∧
      S.card = n + 1 ∧
      (∀ y ∈ S, 0 < y) := by
  have hscale : -((4 : ℝ) ^ (n + 1)) ≠ 0 := by
    exact neg_ne_zero.mpr (by positivity)
  rcases roots_eq_positiveSquares_oddSechSquarePoly (n + 1) with ⟨S, hroots, hcard, hpos⟩
  refine ⟨S, ?_, hcard, hpos⟩
  rw [solverRawAdaptedXi_eq_solverSechXiExact, solverSechXiExact, Polynomial.roots_C_mul _ hscale,
    hroots]

private theorem solverRawAdaptedXi_ne_zero (n : ℕ) :
    solverRawAdaptedXi n ≠ 0 := by
  have hscale : (Polynomial.C (-((4 : ℝ) ^ (n + 1)))) ≠ 0 := by
    simp [neg_ne_zero, pow_ne_zero]
  rw [solverRawAdaptedXi_eq_solverSechXiExact, solverSechXiExact]
  exact mul_ne_zero hscale (oddSechSquarePoly_ne_zero (n + 1))

private theorem solverRawAdaptedXi_splits (n : ℕ) :
    (solverRawAdaptedXi n).Splits := by
  rw [solverRawAdaptedXi_eq_solverSechXiExact, solverSechXiExact]
  exact (oddSechSquarePoly_splits (n + 1)).C_mul _

private theorem solverRawAdaptedXi_separable (n : ℕ) :
    (solverRawAdaptedXi n).Separable := by
  have hscale : -((4 : ℝ) ^ (n + 1)) ≠ 0 := by
    exact neg_ne_zero.mpr (by positivity)
  have hnodup : (oddSechSquarePoly (n + 1)).roots.Nodup := by
    exact (Polynomial.nodup_roots_iff_of_splits
      (oddSechSquarePoly_ne_zero (n + 1)) (oddSechSquarePoly_splits (n + 1))).2
      (oddSechSquarePoly_separable (n + 1))
  rw [← Polynomial.nodup_roots_iff_of_splits (solverRawAdaptedXi_ne_zero n)
    (solverRawAdaptedXi_splits n)]
  rw [solverRawAdaptedXi_eq_solverSechXiExact, solverSechXiExact, Polynomial.roots_C_mul _ hscale]
  exact hnodup

private theorem solverRawAdaptedXi_roots_nonempty (n : ℕ) :
    (solverRawAdaptedXi n).roots.toFinset.Nonempty := by
  rcases solverRawAdaptedXi_roots_eq_positiveFinset n with ⟨S, hroots, hcard, -⟩
  have hrootsF : (solverRawAdaptedXi n).roots.toFinset = S := by
    simpa [hroots]
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    positivity
  simpa [hrootsF] using hS

private theorem solverRawAdaptedXi_roots_pos (n : ℕ) :
    ∀ x, x ∈ (solverRawAdaptedXi n).roots.toFinset → 0 < x := by
  rcases solverRawAdaptedXi_roots_eq_positiveFinset n with ⟨S, hroots, -, hpos⟩
  have hrootsF : (solverRawAdaptedXi n).roots.toFinset = S := by
    simpa [hroots]
  intro x hx
  have hxS : x ∈ S := by simpa [hrootsF] using hx
  exact hpos x hxS

private theorem solverRawAdaptedXi_roots_card (n : ℕ) :
    Fintype.card { z // z ∈ (solverRawAdaptedXi n).roots.toFinset } = n + 1 := by
  rcases solverRawAdaptedXi_roots_eq_positiveFinset n with ⟨S, hroots, hcard, -⟩
  have hrootsF : (solverRawAdaptedXi n).roots.toFinset = S := by
    simpa [hroots]
  simpa [Fintype.card_coe, hrootsF, hcard]

end OddSechRootTheory

section PolynomialRoots

theorem derivative_eval_zero_eq_coeff_one (p : ℝ[X]) :
    p.derivative.eval 0 = p.coeff 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simp [Polynomial.coeff_derivative]

/-- The smallest element of the real root set of `p`, viewed through `p.roots.toFinset`. -/
noncomputable def smallestRootOfRootsToFinset (p : ℝ[X]) (h : p.roots.toFinset.Nonempty) : ℝ := by
  let ι := { z // z ∈ p.roots.toFinset }
  letI : Nonempty ι := by
    rcases h with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  exact smallestValue (fun x : ι ↦ (x : ℝ))

/--
For a nonzero split polynomial over `ℝ` with simple positive roots, the negative logarithmic
derivative at `0` is the sum of the reciprocal roots.
-/
theorem neg_coeff_one_div_coeff_zero_eq_sumInv_rootsToFinset
    {p : ℝ[X]}
    (hp : p ≠ 0)
    (hsplit : p.Splits)
    (hsep : p.Separable)
    (hpos : ∀ x, x ∈ p.roots.toFinset → 0 < x) :
    -(p.coeff 1) / p.coeff 0 =
      ∑ x : {z // z ∈ p.roots.toFinset}, ((x : ℝ)⁻¹) := by
  have h0 : p.eval 0 ≠ 0 := by
    intro hzero
    have hroot : 0 ∈ p.roots := by
      rw [Polynomial.mem_roots hp]
      simpa using hzero
    have hmem : 0 ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr hroot
    exact (lt_irrefl 0) (hpos 0 hmem)
  have hratio :
      p.coeff 1 / p.coeff 0 =
        (p.roots.map fun z ↦ 1 / (0 - z)).sum := by
    simpa [derivative_eval_zero_eq_coeff_one, Polynomial.coeff_zero_eq_eval_zero] using
      hsplit.eval_derivative_div_eval_of_ne_zero (x := 0) h0
  have hmap :
      p.roots.map (fun z ↦ 1 / (0 - z)) = p.roots.map (fun z ↦ -(z⁻¹)) := by
    refine Multiset.map_congr rfl ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      exact (ne_of_gt (hpos z (Multiset.mem_toFinset.mpr hz)))
    field_simp [hz0]
    ring
  have hsum :
      (p.roots.map fun z ↦ z⁻¹).sum =
        ∑ x : {z // z ∈ p.roots.toFinset}, ((x : ℝ)⁻¹) := by
    classical
    have hsub :
        (∑ x : {z // z ∈ p.roots.toFinset}, ((x : ℝ)⁻¹)) =
          Finset.sum p.roots.toFinset fun x ↦ x⁻¹ := by
      simpa using
        (Finset.sum_attach (s := p.roots.toFinset) (f := fun x : ℝ ↦ x⁻¹))
    rw [hsub]
    rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots hsep)]
  have hmapNeg :
      p.roots.map (fun z ↦ -(z⁻¹)) = p.roots.map (fun z ↦ (-1 : ℝ) * z⁻¹) := by
    refine Multiset.map_congr rfl ?_
    intro z hz
    ring
  have hneg :
      -(p.coeff 1) / p.coeff 0 = -((p.roots.map fun z ↦ 1 / (0 - z)).sum) := by
    rw [neg_div]
    exact congrArg Neg.neg hratio
  calc
    -(p.coeff 1) / p.coeff 0 = -((p.roots.map fun z ↦ 1 / (0 - z)).sum) := hneg
    _ = -((p.roots.map fun z ↦ -(z⁻¹)).sum) := by rw [hmap]
    _ = -((p.roots.map fun z ↦ (-1 : ℝ) * z⁻¹).sum) := by rw [hmapNeg]
    _ = -((-1 : ℝ) * (p.roots.map fun z ↦ z⁻¹).sum) := by
      rw [Multiset.sum_map_mul_left]
    _ = (p.roots.map fun z ↦ z⁻¹).sum := by ring
    _ = ∑ x : {z // z ∈ p.roots.toFinset}, ((x : ℝ)⁻¹) := hsum

end PolynomialRoots

section ZeroLimitTheorems

/--
Correct endgame of the `\widetilde Ξ_n` proof: for each `n`, let `roots n` enumerate the positive
zeros of `\widetilde Ξ_n`. If the ratio
`(# roots of \widetilde Ξ_n) / (sum of reciprocal roots)` tends to `0`, then the smallest root
tends to `0`.

This packages the analytic heart of the corrected Xi argument in a way that can be combined with
the paper's root-location theorem and any separate asymptotic estimate for the reciprocal-root sum.
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

/--
If the reciprocal-root sum takes the Xi-specific form `(R - 5) / 6`, then the smallest root is
bounded by `6 * (# roots) / (R - 5)`.
-/
theorem smallestValue_le_card_mul_six_div_sub_five
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (roots : ι → ℝ)
    (hpos : ∀ i, 0 < roots i)
    {R : ℝ}
    (hsum : ∑ i, (roots i)⁻¹ = (R - 5) / 6) :
    smallestValue roots ≤ 6 * (Fintype.card ι : ℝ) / (R - 5) := by
  have hsumPos : 0 < ∑ i, (roots i)⁻¹ := sumInv_pos roots hpos
  have hdenPos : 0 < R - 5 := by
    have : 0 < (R - 5) / 6 := by simpa [hsum] using hsumPos
    nlinarith
  have hrewrite :
      (Fintype.card ι : ℝ) / ((R - 5) / 6) = 6 * (Fintype.card ι : ℝ) / (R - 5) := by
    field_simp [hdenPos.ne']
  calc
    smallestValue roots ≤ (Fintype.card ι : ℝ) / ∑ i, (roots i)⁻¹ :=
      smallestValue_le_card_div_sumInv roots hpos
    _ = (Fintype.card ι : ℝ) / ((R - 5) / 6) := by rw [hsum]
    _ = 6 * (Fintype.card ι : ℝ) / (R - 5) := hrewrite

/--
Xi-specific version of the previous limit theorem, phrased in terms of the explicit reciprocal-root
sum `(R n - 5) / 6`.
-/
theorem xi_smallestRoot_tendsto_zero_of_sub_five
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (roots : ∀ n, ι n → ℝ)
    (hpos : ∀ n i, 0 < roots n i)
    (R : ℕ → ℝ)
    (hsum : ∀ n, ∑ i, (roots n i)⁻¹ = (R n - 5) / 6)
    (hR : Tendsto (fun n ↦ 6 * (Fintype.card (ι n) : ℝ) / (R n - 5)) atTop (nhds 0)) :
    Tendsto (fun n ↦ smallestValue (roots n)) atTop (nhds 0) := by
  refine squeeze_zero (fun n ↦ (smallestValue_pos (roots n) (hpos n)).le) ?_ hR
  intro n
  exact smallestValue_le_card_mul_six_div_sub_five (roots n) (hpos n) (hsum n)

/--
Algebraic elimination step from the Xi proof sketch: once the Taylor data of `P_n` and the first
and third derivative identities coming from the auxiliary function `H_m` are known, the claimed
Euler-ratio formula for the logarithmic derivative follows exactly.
-/
theorem xi_logDerivRatio_from_auxiliary_data
    {m : ℕ} {κ a₁ a₃ E₁ E₃ : ℝ}
    (hκ : κ ≠ 0)
    (hE₁ : E₁ ≠ 0)
    (hFirst : 2 * a₁ = -((2 : ℝ) ^ m) * E₁)
    (hThird :
      (-6 * (m : ℝ) ^ 2 + 24 * (m : ℝ) - 16) * a₁ + 8 * a₃ =
  -((2 : ℝ) ^ m) * (3 * ((m : ℝ) + 1) * E₁ + E₃)) :
    -(κ * (-( ((m : ℝ) - 1) * ((m : ℝ) - 2) * a₁) + (4 / 3) * a₃)) / (2 * κ * a₁) =
      -(5 : ℝ) / 6 - E₃ / (6 * E₁) := by
  have hpow : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  have ha₁ : a₁ = -((2 : ℝ) ^ m) * E₁ / 2 := by
    nlinarith [hFirst]
  have ha₃ :
      a₃ = ((2 : ℝ) ^ m) *
        (-3 * E₁ * (m : ℝ) ^ 2 + 9 * E₁ * (m : ℝ) - 11 * E₁ - E₃) / 8 := by
    nlinarith [hFirst, hThird]
  rw [ha₁, ha₃]
  field_simp [hκ, hE₁, hpow]
  ring

/--
Corrected Xi endgame stated in terms of the logarithmic derivative. The factorization
`P_n(y) = c_n ∏ᵢ (1 - y / y_{n,i})` identifies the logarithmic derivative with the reciprocal-root
sum, and the finite-family averaging bound turns that into a bound on the smallest root.
-/
theorem xi_smallestRoot_tendsto_zero_of_logDerivRatio
    {ι : ℕ → Type*}
    [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (roots : ∀ n, ι n → ℝ)
    (hpos : ∀ n i, 0 < roots n i)
    (c : ℕ → ℝ)
    (hc : ∀ n, c n ≠ 0)
    (R : ℕ → ℝ)
    (hratio :
      ∀ n,
        -(deriv (fun y ↦ c n * rootProduct (roots n) y) 0) /
            ((fun y ↦ c n * rootProduct (roots n) y) 0) =
          (R n - 5) / 6)
    (hR : Tendsto (fun n ↦ 6 * (Fintype.card (ι n) : ℝ) / (R n - 5)) atTop (nhds 0)) :
    Tendsto (fun n ↦ smallestValue (roots n)) atTop (nhds 0) := by
  have hsum : ∀ n, ∑ i, (roots n i)⁻¹ = (R n - 5) / 6 := by
    intro n
    rw [← neg_deriv_scaledRootProduct_div_eq_sumInv (roots n) (c n) (hc n), hratio n]
  exact xi_smallestRoot_tendsto_zero_of_sub_five roots hpos R hsum hR

/--
Concrete version of the corrected solver proof, indexed so that `roots n` represents the `n + 2`nd
adapted Xi polynomial and therefore has exactly `n + 1` positive roots.
-/
theorem xi_smallestRoot_tendsto_zero_of_solver_ratio
    (roots : ∀ n, Fin (n + 1) → ℝ)
    (hpos : ∀ n i, 0 < roots n i)
    (c : ℕ → ℝ)
    (hc : ∀ n, c n ≠ 0)
    (hratio :
      ∀ n,
        -(deriv (fun y ↦ c n * rootProduct (roots n) y) 0) /
            ((fun y ↦ c n * rootProduct (roots n) y) 0) =
          (secantEulerRatioShift n - 5) / 6) :
    Tendsto (fun n ↦ smallestValue (roots n)) atTop (nhds 0) := by
  refine xi_smallestRoot_tendsto_zero_of_logDerivRatio roots hpos c hc
    secantEulerRatioShift hratio ?_
  simpa using tendsto_card_mul_six_div_secantEulerRatio_sub_five

/--
Polynomial-level version of the corrected Xi argument. The smallest positive root is taken over the
actual root set of `P n`, so the theorem can be applied directly to adapted Xi polynomials once the
paper's real-rootedness/root-location input has been instantiated in Lean.
-/
theorem polynomial_smallestRoot_tendsto_zero_of_coeffRatio
    (P : ℕ → ℝ[X])
    (hp : ∀ n, P n ≠ 0)
    (hsplit : ∀ n, (P n).Splits)
    (hsep : ∀ n, (P n).Separable)
    (hnonempty : ∀ n, (P n).roots.toFinset.Nonempty)
    (hpos : ∀ n x, x ∈ (P n).roots.toFinset → 0 < x)
    (R : ℕ → ℝ)
    (hratio : ∀ n, -((P n).coeff 1) / (P n).coeff 0 = (R n - 5) / 6)
    (hR :
      Tendsto
        (fun n ↦ 6 * (Fintype.card { z // z ∈ (P n).roots.toFinset } : ℝ) / (R n - 5))
        atTop (nhds 0)) :
    Tendsto
      (fun n ↦ smallestRootOfRootsToFinset (P n) (hnonempty n))
      atTop (nhds 0) := by
  let roots : ∀ n, { z // z ∈ (P n).roots.toFinset } → ℝ := fun _ x ↦ x
  haveI : ∀ n, Nonempty { z // z ∈ (P n).roots.toFinset } := by
    intro n
    rcases hnonempty n with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  have hrootsPos : ∀ n i, 0 < roots n i := by
    intro n i
    exact hpos n i.1 i.2
  have hsum :
      ∀ n, ∑ i, (roots n i)⁻¹ = (R n - 5) / 6 := by
    intro n
    rw [← neg_coeff_one_div_coeff_zero_eq_sumInv_rootsToFinset (hp n) (hsplit n) (hsep n)
      (hpos n), hratio n]
  simpa [smallestRootOfRootsToFinset, roots] using
    (xi_smallestRoot_tendsto_zero_of_sub_five roots hrootsPos R hsum hR)

/--
Concrete polynomial version of the solver theorem. Here `P n` is the `n + 2`nd adapted Xi
polynomial, so it has exactly `n + 1` positive roots.
-/
theorem xi_smallestRoot_tendsto_zero_of_solver_polynomial_ratio
    (P : ℕ → ℝ[X])
    (hp : ∀ n, P n ≠ 0)
    (hsplit : ∀ n, (P n).Splits)
    (hsep : ∀ n, (P n).Separable)
    (hnonempty : ∀ n, (P n).roots.toFinset.Nonempty)
    (hpos : ∀ n x, x ∈ (P n).roots.toFinset → 0 < x)
    (hcard : ∀ n, Fintype.card { z // z ∈ (P n).roots.toFinset } = n + 1)
    (hratio :
      ∀ n, -((P n).coeff 1) / (P n).coeff 0 = (secantEulerRatioShift n - 5) / 6) :
    Tendsto
      (fun n ↦ smallestRootOfRootsToFinset (P n) (hnonempty n))
      atTop (nhds 0) := by
  refine polynomial_smallestRoot_tendsto_zero_of_coeffRatio P hp hsplit hsep hnonempty hpos
    secantEulerRatioShift hratio ?_
  have hR' :
      Tendsto
        (fun n : ℕ ↦ 6 * (n + 1 : ℝ) / (secantEulerRatioShift n - 5))
        atTop (nhds 0) :=
    tendsto_card_mul_six_div_secantEulerRatio_sub_five
  refine hR'.congr' <| Filter.Eventually.of_forall ?_
  intro n
  simp [hcard n]

/--
Concrete specialization of the polynomial-level limit theorem to the paper's actual adapted Xi
family, represented here by the unscaled coefficient polynomial `solverRawAdaptedXi`.
-/
theorem xi_smallestRoot_tendsto_zero_of_actual_rawAdaptedXi_ratio
    (hp : ∀ n, solverRawAdaptedXi n ≠ 0)
    (hsplit : ∀ n, (solverRawAdaptedXi n).Splits)
    (hsep : ∀ n, (solverRawAdaptedXi n).Separable)
    (hnonempty : ∀ n, (solverRawAdaptedXi n).roots.toFinset.Nonempty)
    (hpos : ∀ n x, x ∈ (solverRawAdaptedXi n).roots.toFinset → 0 < x)
    (hcard : ∀ n, Fintype.card { z // z ∈ (solverRawAdaptedXi n).roots.toFinset } = n + 1)
    (hratio :
      ∀ n,
        -((solverRawAdaptedXi n).coeff 1) / (solverRawAdaptedXi n).coeff 0 =
          (secantEulerRatioShift n - 5) / 6) :
    Tendsto
      (fun n ↦ smallestRootOfRootsToFinset (solverRawAdaptedXi n) (hnonempty n))
      atTop (nhds 0) := by
  exact xi_smallestRoot_tendsto_zero_of_solver_polynomial_ratio
    solverRawAdaptedXi hp hsplit hsep hnonempty hpos hcard hratio

/--
Xi specialization with the root-theoretic input discharged internally from the `sech` model.
The remaining substantive input is the exact secant-Euler coefficient-ratio identity.
-/
theorem xi_smallestRoot_tendsto_zero_of_solverRawAdaptedXi_secantRatio
    (hratio :
      ∀ n,
        -((solverRawAdaptedXi n).coeff 1) / (solverRawAdaptedXi n).coeff 0 =
          (secantEulerRatioShift n - 5) / 6) :
    Tendsto
      (fun n ↦
        smallestRootOfRootsToFinset (solverRawAdaptedXi n) (solverRawAdaptedXi_roots_nonempty n))
      atTop (nhds 0) := by
  exact xi_smallestRoot_tendsto_zero_of_solver_polynomial_ratio
    solverRawAdaptedXi solverRawAdaptedXi_ne_zero solverRawAdaptedXi_splits
    solverRawAdaptedXi_separable solverRawAdaptedXi_roots_nonempty
    solverRawAdaptedXi_roots_pos solverRawAdaptedXi_roots_card hratio

/--
End-to-end Xi zero-limit theorem for the actual coefficient-defined family `solverRawAdaptedXi`,
with both the root-theoretic input and the exact secant-Euler coefficient ratio discharged in Lean.
-/
theorem xi_smallestRoot_tendsto_zero_of_solverRawAdaptedXi :
    Tendsto
      (fun n ↦
        smallestRootOfRootsToFinset (solverRawAdaptedXi n) (solverRawAdaptedXi_roots_nonempty n))
      atTop (nhds 0) := by
  exact xi_smallestRoot_tendsto_zero_of_solverRawAdaptedXi_secantRatio
    solverRawAdaptedXi_coeff_ratio_eq_secantEulerRatioShift

end ZeroLimitTheorems

end XiZeroLimit
