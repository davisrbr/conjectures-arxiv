import Mathlib

namespace SteinDisproof

/--
The Stein operator appearing in the disconfirmed conjecture from the stochastic-approximation
paper.
-/
noncomputable def steinOperator (m : ℕ) (σ : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun y ↦ -(y ^ m * deriv g y) + σ ^ 2 * deriv (deriv g) y

theorem differentiableAt_zero_steinOperator
    {m : ℕ} {σ : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) :
    DifferentiableAt ℝ (steinOperator m σ g) 0 := by
  have hg' : ContDiff ℝ 2 (deriv g) := by
    simpa using hg.deriv'
  have hg'' : ContDiff ℝ 1 (deriv (deriv g)) := by
    simpa using hg'.deriv'
  have hpow : DifferentiableAt ℝ (fun y : ℝ ↦ y ^ m) 0 :=
    differentiableAt_pow (𝕜 := ℝ) (n := m) (x := (0 : ℝ))
  have hderiv : DifferentiableAt ℝ (deriv g) 0 :=
    (hg'.differentiable (by norm_num)) 0
  have hsecond : DifferentiableAt ℝ (deriv (deriv g)) 0 :=
    (hg''.differentiable (by norm_num)) 0
  have hfirst :
      DifferentiableAt ℝ (fun y : ℝ ↦ -(y ^ m) * deriv g y) 0 :=
    hpow.neg.mul hderiv
  have hsecond' :
      DifferentiableAt ℝ (fun y : ℝ ↦ σ ^ 2 * deriv (deriv g) y) 0 :=
    (differentiableAt_const (σ ^ 2)).mul hsecond
  simpa [steinOperator] using hfirst.add hsecond'

theorem no_contDiff_solution_for_abs
    {m : ℕ} {σ c : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) :
    ¬ ∀ y, |y| - c = steinOperator m σ g y := by
  intro hEq
  have hrhs : DifferentiableAt ℝ (steinOperator m σ g) 0 :=
    differentiableAt_zero_steinOperator hg
  have hfun : (fun y : ℝ ↦ |y| - c) = steinOperator m σ g := by
    funext y
    exact hEq y
  have hlhs : DifferentiableAt ℝ (fun y : ℝ ↦ |y| - c) 0 := by
    simpa [hfun] using hrhs
  have habs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    convert hlhs.add_const c using 1
    ext y
    ring
  exact not_differentiableAt_abs_zero habs

theorem lipschitzWith_abs : LipschitzWith 1 (abs : ℝ → ℝ) := by
  simpa using
    (LipschitzWith.of_dist_le' (f := (abs : ℝ → ℝ)) (K := (1 : ℝ)) fun x y ↦ by
      simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y)

/--
The conjecture claimed that every `1`-Lipschitz test function admits a sufficiently smooth Stein
solution. The absolute-value test function is a formal counterexample.
-/
theorem stein_conjecture_disconfirmed (m : ℕ) (σ c : ℝ) :
    ∃ φ : ℝ → ℝ, LipschitzWith 1 φ ∧
      ∀ g : ℝ → ℝ, ContDiff ℝ 3 g →
        ¬ ∀ y, φ y - c = steinOperator m σ g y := by
  refine ⟨abs, lipschitzWith_abs, ?_⟩
  intro g hg
  simpa using no_contDiff_solution_for_abs (m := m) (σ := σ) (c := c) (g := g) hg

end SteinDisproof
