import Mathlib

open scoped BigOperators

namespace QuasimodularSturm

section Triangular

variable {K : Type*} [Field K]
variable {n : ℕ}

/--
An upper-triangular family of coefficient vectors with `1` on the diagonal is linearly
independent. This is the linear-algebra core of the quasimodular Sturm argument once a
triangular basis has been constructed.
-/
theorem linearIndependent_of_upperTriangularOnes
    (v : Fin n → Fin n → K)
    (htri : ∀ i j, j < i → v i j = 0)
    (hdiag : ∀ i, v i i = 1) :
    LinearIndependent K v := by
  let A : Matrix (Fin n) (Fin n) K := fun i j ↦ v i j
  have hAtri : A.BlockTriangular id := by
    intro i j hij
    exact htri i j hij
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hAtri]
    simp [A, hdiag]
  simpa [A, Matrix.row] using Matrix.linearIndependent_rows_of_det_ne_zero hdet

/--
If the truncated coefficient vectors of a family are upper triangular with diagonal `1`, then
the vanishing of the first `n` coefficients of a linear combination forces all coefficients in
that combination to vanish.
-/
theorem coeffs_zero_imp_zero
    {V : Type*} [AddCommMonoid V] [Module K V]
    (trunc : V →ₗ[K] (Fin n → K))
    (F : Fin n → V)
    (htri : ∀ i j, j < i → trunc (F i) j = 0)
    (hdiag : ∀ i, trunc (F i) i = 1)
    {c : Fin n → K}
    (hvanish : trunc (∑ i, c i • F i) = 0) :
    c = 0 := by
  let coeffFamily : Fin n → Fin n → K := fun i j ↦ trunc (F i) j
  have hLI : LinearIndependent K coeffFamily :=
    linearIndependent_of_upperTriangularOnes coeffFamily htri hdiag
  have hinj :=
    (Fintype.linearIndependent_iff'ₛ (R := K) (v := coeffFamily)).1 hLI
  apply hinj
  ext j
  have hcoeff : ∑ x, c x * trunc (F x) j = 0 := by
    simpa [coeffFamily] using congrFun hvanish j
  simpa [coeffFamily] using hcoeff

end Triangular

section WeightedTriples

/--
The weight-`k` monomials `X^a Y^b Z^c` appearing in the quasimodular argument satisfy the linear
constraint `a + 2 b + 3 c = k`.
-/
structure WeightTriple (k : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  weight_eq : a + 2 * b + 3 * c = k

namespace WeightTriple

variable {k : ℕ}

/-- In the `X,Y,Z` model, the `q`-order of `X^a Y^b Z^c` is `b + 2c`. -/
def qOrder (t : WeightTriple k) : ℕ :=
  t.b + 2 * t.c

end WeightTriple

/-- The low-order monomials `X^(k-2n) Y^n` used when `n ≤ k/2`. -/
def leftTriple (k n : ℕ) (h : 2 * n ≤ k) : WeightTriple k where
  a := k - 2 * n
  b := n
  c := 0
  weight_eq := by omega

/-- The low-order monomials `Y^(2k-3n) Z^(2n-k)` used when `k/2 ≤ n ≤ 2k/3`. -/
def rightTriple (k n : ℕ) (hk : k ≤ 2 * n) (hn : 3 * n ≤ 2 * k) : WeightTriple k where
  a := 0
  b := 2 * k - 3 * n
  c := 2 * n - k
  weight_eq := by omega

@[simp]
theorem qOrder_leftTriple (k n : ℕ) (h : 2 * n ≤ k) :
    (leftTriple k n h).qOrder = n := by
  simp [leftTriple, WeightTriple.qOrder]

@[simp]
theorem qOrder_rightTriple (k n : ℕ) (hk : k ≤ 2 * n) (hn : 3 * n ≤ 2 * k) :
    (rightTriple k n hk hn).qOrder = n := by
  simp [rightTriple, WeightTriple.qOrder]
  omega

/--
For every order `n` up to `⌊2k/3⌋`, there is a weight-`k` monomial `X^a Y^b Z^c` with
`q`-order exactly `n`.
-/
def tripleOfOrder (k n : ℕ) (hn : 3 * n ≤ 2 * k) : WeightTriple k :=
  if hleft : 2 * n ≤ k then
    leftTriple k n hleft
  else
    rightTriple k n (le_of_not_ge hleft) hn

@[simp]
theorem qOrder_tripleOfOrder (k n : ℕ) (hn : 3 * n ≤ 2 * k) :
    (tripleOfOrder k n hn).qOrder = n := by
  by_cases hleft : 2 * n ≤ k
  · simp [tripleOfOrder, hleft]
  · simp [tripleOfOrder, hleft]

theorem exists_weightTriple_of_order (k n : ℕ) (hn : 3 * n ≤ 2 * k) :
    ∃ t : WeightTriple k, t.qOrder = n := by
  exact ⟨tripleOfOrder k n hn, qOrder_tripleOfOrder k n hn⟩

theorem exists_weightTriple_of_le_twoThirds (k n : ℕ) (hn : n ≤ (2 * k) / 3) :
    ∃ t : WeightTriple k, t.qOrder = n := by
  apply exists_weightTriple_of_order
  omega

end WeightedTriples

end QuasimodularSturm
