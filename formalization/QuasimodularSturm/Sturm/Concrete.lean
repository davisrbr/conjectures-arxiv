import QuasimodularSturm.Sturm.DiagonalCriterion

open scoped BigOperators

set_option linter.style.nativeDecide false

namespace QuasimodularSturm

section ConcreteModel

abbrev QSeries := Series ℚ

/-- A naive divisor-power sum, adequate for low-weight coefficient checks. -/
def sigmaPow (p n : ℕ) : ℚ :=
  ((Finset.range (n + 1)).filter fun d ↦ d ∣ n).sum fun d ↦ (d : ℚ) ^ p

/-- Cauchy product of coefficient sequences. -/
def qMul (f g : QSeries) : QSeries :=
  fun n ↦ (Finset.range (n + 1)).sum fun i ↦ f i * g (n - i)

/-- Powers under the Cauchy product. -/
def qPow (f : QSeries) : ℕ → QSeries
  | 0 => fun n ↦ if n = 0 then 1 else 0
  | m + 1 => qMul (qPow f m) f

/-- The classical weight-2 Eisenstein series coefficients. -/
def e2 : QSeries
  | 0 => 1
  | n + 1 => -24 * sigmaPow 1 (n + 1)

/-- The classical weight-4 Eisenstein series coefficients. -/
def e4 : QSeries
  | 0 => 1
  | n + 1 => 240 * sigmaPow 3 (n + 1)

/-- The classical weight-6 Eisenstein series coefficients. -/
def e6 : QSeries
  | 0 => 1
  | n + 1 => -504 * sigmaPow 5 (n + 1)

/-- `X = E₂`. -/
def X : QSeries := e2

/-- `Y = (E₄ - E₂²) / 288`. -/
def Y : QSeries :=
  fun n ↦ ((e4 n - qPow e2 2 n) / 288)

/-- `Z = (5E₂³ - 3E₂E₄ - 2E₆) / 51840`. -/
def Z : QSeries :=
  fun n ↦ ((5 * qPow e2 3 n - 3 * qMul e2 e4 n - 2 * e6 n) / 51840)

/-- The first nontrivial extremal combination, with weight `8` and order `3`. -/
def W : QSeries :=
  fun n ↦ qMul X Z n - qPow Y 2 n

/-- Normalized form of `W` with leading coefficient `1`. -/
def F3 : QSeries :=
  fun n ↦ (-W n) / 28

/-- The next extremal combination, with weight `10` and order `4`. -/
def V : QSeries :=
  fun n ↦ qMul X W n + 28 * qMul Y Z n

/-- Normalized form of `V` with leading coefficient `1`. -/
def F4 : QSeries :=
  fun n ↦ V n / 770

theorem Y_initial :
    Y 0 = 0 ∧ Y 1 = 1 := by
  native_decide

theorem Z_initial :
    Z 0 = 0 ∧ Z 1 = 0 ∧ Z 2 = 1 := by
  native_decide

theorem F3_initial :
    F3 0 = 0 ∧ F3 1 = 0 ∧ F3 2 = 0 ∧ F3 3 = 1 := by
  native_decide

theorem F4_initial :
    F4 0 = 0 ∧ F4 1 = 0 ∧ F4 2 = 0 ∧ F4 3 = 0 ∧ F4 4 = 1 := by
  native_decide

def weightOneFamily : Fin 1 → QSeries
  | ⟨0, _⟩ => X

def weightTwoFamily : Fin 2 → QSeries
  | ⟨0, _⟩ => qPow X 2
  | ⟨1, _⟩ => Y

def weightThreeFamily : Fin 3 → QSeries
  | ⟨0, _⟩ => qPow X 3
  | ⟨1, _⟩ => qMul X Y
  | ⟨2, _⟩ => Z

def weightFourFamily : Fin 4 → QSeries
  | ⟨0, _⟩ => qPow X 4
  | ⟨1, _⟩ => qMul (qPow X 2) Y
  | ⟨2, _⟩ => qPow Y 2
  | ⟨3, _⟩ => F3

def weightFiveFamily : Fin 5 → QSeries
  | ⟨0, _⟩ => qPow X 5
  | ⟨1, _⟩ => qMul (qPow X 3) Y
  | ⟨2, _⟩ => qMul X (qPow Y 2)
  | ⟨3, _⟩ => qMul X F3
  | ⟨4, _⟩ => F4

def weightOneDiagonal : DiagonalFamily (K := ℚ) 1 where
  series := weightOneFamily
  lower_zero := by native_decide
  diagonal_one := by native_decide

def weightTwoDiagonal : DiagonalFamily (K := ℚ) 2 where
  series := weightTwoFamily
  lower_zero := by native_decide
  diagonal_one := by native_decide

def weightThreeDiagonal : DiagonalFamily (K := ℚ) 3 where
  series := weightThreeFamily
  lower_zero := by native_decide
  diagonal_one := by native_decide

def weightFourDiagonal : DiagonalFamily (K := ℚ) 4 where
  series := weightFourFamily
  lower_zero := by native_decide
  diagonal_one := by native_decide

def weightFiveDiagonal : DiagonalFamily (K := ℚ) 5 where
  series := weightFiveFamily
  lower_zero := by native_decide
  diagonal_one := by native_decide

theorem weightOne_firstCoeff_determines
    {c : Fin 1 → ℚ}
    (hvanish : seriesTrunc (K := ℚ) 1 (∑ i, c i • weightOneFamily i) = 0) :
    c = 0 := by
  exact coefficients_determine_combination (K := ℚ) weightOneDiagonal hvanish

theorem weightTwo_firstCoeffs_determine
    {c : Fin 2 → ℚ}
    (hvanish : seriesTrunc (K := ℚ) 2 (∑ i, c i • weightTwoFamily i) = 0) :
    c = 0 := by
  exact coefficients_determine_combination (K := ℚ) weightTwoDiagonal hvanish

theorem weightThree_firstCoeffs_determine
    {c : Fin 3 → ℚ}
    (hvanish : seriesTrunc (K := ℚ) 3 (∑ i, c i • weightThreeFamily i) = 0) :
    c = 0 := by
  exact coefficients_determine_combination (K := ℚ) weightThreeDiagonal hvanish

theorem weightFour_firstCoeffs_determine
    {c : Fin 4 → ℚ}
    (hvanish : seriesTrunc (K := ℚ) 4 (∑ i, c i • weightFourFamily i) = 0) :
    c = 0 := by
  exact coefficients_determine_combination (K := ℚ) weightFourDiagonal hvanish

theorem weightFive_firstCoeffs_determine
    {c : Fin 5 → ℚ}
    (hvanish : seriesTrunc (K := ℚ) 5 (∑ i, c i • weightFiveFamily i) = 0) :
    c = 0 := by
  exact coefficients_determine_combination (K := ℚ) weightFiveDiagonal hvanish

end ConcreteModel

end QuasimodularSturm
