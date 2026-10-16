import calculus.Chapter04.Section03
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bài 4.4.11: phân loại các cực trị địa phương

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2725–2733.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04CompleteExtremaExercises
open Set calculus.Chapter04.Section03


theorem not_source_local_maximum_of_right_increase {f : ℝ → ℝ} {c b : ℝ}
    (hcb : c < b) (hinc : ∀ x ∈ Ioo c b, f c < f x) :
    ¬ IsLocalMaximumOn f univ c := by
  rintro ⟨_, δ, hδ, hbound⟩
  let t : ℝ := min (δ / 2) ((b - c) / 2)
  have hbc : 0 < b - c := sub_pos.mpr hcb
  have htpos : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htb : t < b - c := (min_le_right _ _).trans_lt (by linarith)
  let x : ℝ := c + t
  have hx : x ∈ Ioo c b := by dsimp [x]; constructor <;> linarith
  have hb : f x ≤ f c :=
    hbound x ⟨⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩, by simp⟩
  exact (hinc x hx).not_ge hb


theorem not_source_local_minimum_of_right_decrease {f : ℝ → ℝ} {c b : ℝ}
    (hcb : c < b) (hdec : ∀ x ∈ Ioo c b, f x < f c) :
    ¬ IsLocalMinimumOn f univ c := by
  rintro ⟨_, δ, hδ, hbound⟩
  let t : ℝ := min (δ / 2) ((b - c) / 2)
  have hbc : 0 < b - c := sub_pos.mpr hcb
  have htpos : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htb : t < b - c := (min_le_right _ _).trans_lt (by linarith)
  let x : ℝ := c + t
  have hx : x ∈ Ioo c b := by dsimp [x]; constructor <;> linarith
  have hb : f c ≤ f x :=
    hbound x ⟨⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩, by simp⟩
  exact (hdec x hx).not_ge hb


theorem exponential_kernel_strict_maximum {t : ℝ} (ht : t ≠ 1) :
    t * Real.exp (-t) < Real.exp (-1) := by
  have hne : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  have hlt : t < Real.exp (t - 1) := by
    simpa only [sub_add_cancel] using Real.add_one_lt_exp hne
  have hm := mul_lt_mul_of_pos_right hlt (Real.exp_pos (-t))
  have he : Real.exp (t - 1) * Real.exp (-t) = Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact he ▸ hm


def scaledCosh (x : ℝ) : ℝ := Real.cosh (3 * x)

theorem scaledCosh_hasDerivAt (x : ℝ) :
    HasDerivAt scaledCosh (3 * Real.sinh (3 * x)) x := by
  have h := (Real.hasDerivAt_cosh (3 * x)).comp x
    ((hasDerivAt_id x).const_mul 3)
  apply (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  ring

theorem scaledCosh_critical_iff (x : ℝ) : deriv scaledCosh x = 0 ↔ x = 0 := by
  rw [(scaledCosh_hasDerivAt x).deriv]
  constructor
  · intro h
    have hs : Real.sinh (3 * x) = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    have hx := Real.sinh_eq_zero.mp hs
    linarith
  · rintro rfl
    simp

theorem scaledCosh_zero : scaledCosh 0 = 1 := by simp [scaledCosh]

theorem scaledCosh_strict_minimum {x : ℝ} (hx : x ≠ 0) :
    scaledCosh 0 < scaledCosh x := by
  rw [scaledCosh_zero]
  exact Real.one_lt_cosh.mpr (mul_ne_zero (by norm_num) hx)

theorem scaledCosh_source_minimum_zero : IsLocalMinimumOn scaledCosh univ 0 := by
  refine ⟨by simp, 1, by norm_num, ?_⟩
  intro x _
  rw [scaledCosh_zero]
  exact Real.one_le_cosh (3 * x)

theorem scaledCosh_not_source_maximum_zero : ¬ IsLocalMaximumOn scaledCosh univ 0 :=
  not_source_local_maximum_of_right_increase (b := 1) (by norm_num)
    (fun x hx ↦ scaledCosh_strict_minimum hx.1.ne')

/-- Bài 11(a): cực tiểu duy nhất tại 0, giá trị 1, và không có cực đại. -/
theorem source_scaled_cosh_extrema :
    scaledCosh 0 = 1 ∧
      (∀ x : ℝ, IsLocalMinimumOn scaledCosh univ x ↔ x = 0) ∧
      (∀ x : ℝ, ¬ IsLocalMaximumOn scaledCosh univ x) := by
  refine ⟨scaledCosh_zero, ?_, ?_⟩
  · intro x
    constructor
    · intro h
      exact (scaledCosh_critical_iff x).mp
        (fermat isOpen_univ (Or.inl h) (scaledCosh_hasDerivAt x).differentiableAt)
    · rintro rfl
      exact scaledCosh_source_minimum_zero
  · intro x h
    have hx := (scaledCosh_critical_iff x).mp
      (fermat isOpen_univ (Or.inr h) (scaledCosh_hasDerivAt x).differentiableAt)
    subst x
    exact scaledCosh_not_source_maximum_zero h


def atanExponential (x : ℝ) : ℝ := Real.arctan (x * Real.exp x)

theorem atanExponential_hasDerivAt (x : ℝ) :
    HasDerivAt atanExponential
      (Real.exp x * (1 + x) / (1 + (x * Real.exp x) ^ 2)) x := by
  have hi := (hasDerivAt_id x).mul (Real.hasDerivAt_exp x)
  have h := (Real.hasDerivAt_arctan (x * Real.exp x)).comp x hi
  apply (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  simp only [id_eq, one_mul]
  ring

theorem atanExponential_critical_iff (x : ℝ) :
    deriv atanExponential x = 0 ↔ x = -1 := by
  rw [(atanExponential_hasDerivAt x).deriv]
  have hd : 1 + (x * Real.exp x) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    have hn : Real.exp x * (1 + x) = 0 := (div_eq_zero_iff.mp h).resolve_right hd
    have hx : 1 + x = 0 := (mul_eq_zero.mp hn).resolve_left (Real.exp_ne_zero x)
    linarith
  · rintro rfl
    simp

theorem atanExponential_neg_one :
    atanExponential (-1) = Real.arctan (-Real.exp (-1)) := by simp [atanExponential]

theorem atanExponential_strict_minimum {x : ℝ} (hx : x ≠ -1) :
    atanExponential (-1) < atanExponential x := by
  have hne : -x ≠ 1 := by intro h; apply hx; linarith
  have hh := exponential_kernel_strict_maximum hne
  have harg : -Real.exp (-1) < x * Real.exp x := by
    simp only [neg_neg] at hh
    nlinarith
  rw [atanExponential_neg_one]
  exact Real.arctan_lt_arctan_iff.mpr harg

theorem atanExponential_source_minimum_neg_one :
    IsLocalMinimumOn atanExponential univ (-1) := by
  refine ⟨by simp, 1, by norm_num, ?_⟩
  intro x _
  by_cases hx : x = -1
  · subst x
    exact le_rfl
  · exact (atanExponential_strict_minimum hx).le

theorem atanExponential_not_source_maximum_neg_one :
    ¬ IsLocalMaximumOn atanExponential univ (-1) :=
  not_source_local_maximum_of_right_increase (b := 0) (by norm_num)
    (fun x hx ↦ atanExponential_strict_minimum hx.1.ne')

/-- Bài 11(b): cực tiểu duy nhất tại −1, giá trị arctan(−e⁻¹), không có cực đại. -/
theorem source_atan_exponential_extrema :
    atanExponential (-1) = Real.arctan (-Real.exp (-1)) ∧
      (∀ x : ℝ, IsLocalMinimumOn atanExponential univ x ↔ x = -1) ∧
      (∀ x : ℝ, ¬ IsLocalMaximumOn atanExponential univ x) := by
  refine ⟨atanExponential_neg_one, ?_, ?_⟩
  · intro x
    constructor
    · intro h
      exact (atanExponential_critical_iff x).mp
        (fermat isOpen_univ (Or.inl h) (atanExponential_hasDerivAt x).differentiableAt)
    · rintro rfl
      exact atanExponential_source_minimum_neg_one
  · intro x h
    have hx := (atanExponential_critical_iff x).mp
      (fermat isOpen_univ (Or.inr h) (atanExponential_hasDerivAt x).differentiableAt)
    subst x
    exact atanExponential_not_source_maximum_neg_one h


def squareGaussian (x : ℝ) : ℝ := x ^ 2 * Real.exp (-(x ^ 2))

theorem squareGaussian_hasDerivAt (x : ℝ) :
    HasDerivAt squareGaussian (2 * x * (1 - x ^ 2) * Real.exp (-(x ^ 2))) x := by
  have he := (Real.hasDerivAt_exp (-(x ^ 2))).comp x (hasDerivAt_pow 2 x).neg
  have h := (hasDerivAt_pow 2 x).mul he
  apply (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  dsimp only [Function.comp_def, Pi.neg_apply]
  ring

theorem squareGaussian_critical_iff (x : ℝ) :
    deriv squareGaussian x = 0 ↔ x = 0 ∨ x = -1 ∨ x = 1 := by
  rw [(squareGaussian_hasDerivAt x).deriv]
  constructor
  · intro h
    have hm : 2 * x * (1 - x ^ 2) = 0 :=
      (mul_eq_zero.mp h).resolve_right (Real.exp_ne_zero (-(x ^ 2)))
    rcases mul_eq_zero.mp hm with hx | hs
    · left
      linarith
    · have hp : (x - 1) * (x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp with hpos | hneg
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inr (Or.inl (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

theorem squareGaussian_zero : squareGaussian 0 = 0 := by simp [squareGaussian]

theorem squareGaussian_neg_one : squareGaussian (-1) = 1 / Real.exp 1 := by
  simp [squareGaussian, Real.exp_neg]

theorem squareGaussian_one : squareGaussian 1 = 1 / Real.exp 1 := by
  simp [squareGaussian, Real.exp_neg]

theorem squareGaussian_strict_minimum {x : ℝ} (hx : x ≠ 0) :
    squareGaussian 0 < squareGaussian x := by
  rw [squareGaussian_zero]
  exact mul_pos (sq_pos_of_ne_zero hx) (Real.exp_pos (-(x ^ 2)))

theorem squareGaussian_global_maximum (x : ℝ) :
    squareGaussian x ≤ 1 / Real.exp 1 := by
  change x ^ 2 * Real.exp (-(x ^ 2)) ≤ 1 / Real.exp 1
  have h := Real.mul_exp_neg_le_exp_neg_one (x ^ 2)
  simpa only [Real.exp_neg, one_div] using h

theorem squareGaussian_strict_maximum {x : ℝ} (hm : x ≠ -1) (hp : x ≠ 1) :
    squareGaussian x < 1 / Real.exp 1 := by
  change x ^ 2 * Real.exp (-(x ^ 2)) < 1 / Real.exp 1
  have hs : x ^ 2 ≠ 1 := by
    intro h
    have hf : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · exact hp (by linarith)
    · exact hm (by linarith)
  have h := exponential_kernel_strict_maximum hs
  simpa only [Real.exp_neg, one_div] using h

theorem squareGaussian_source_minimum_zero :
    IsLocalMinimumOn squareGaussian univ 0 := by
  refine ⟨by simp, 1, by norm_num, ?_⟩
  intro x _
  rw [squareGaussian_zero]
  exact mul_nonneg (sq_nonneg x) (Real.exp_pos (-(x ^ 2))).le

theorem squareGaussian_source_maximum_neg_one :
    IsLocalMaximumOn squareGaussian univ (-1) := by
  refine ⟨by simp, 1, by norm_num, ?_⟩
  intro x _
  rw [squareGaussian_neg_one]
  exact squareGaussian_global_maximum x

theorem squareGaussian_source_maximum_one :
    IsLocalMaximumOn squareGaussian univ 1 := by
  refine ⟨by simp, 1, by norm_num, ?_⟩
  intro x _
  rw [squareGaussian_one]
  exact squareGaussian_global_maximum x

theorem squareGaussian_not_source_maximum_zero :
    ¬ IsLocalMaximumOn squareGaussian univ 0 :=
  not_source_local_maximum_of_right_increase (b := 1) (by norm_num)
    (fun x hx ↦ squareGaussian_strict_minimum hx.1.ne')

theorem squareGaussian_not_source_minimum_neg_one :
    ¬ IsLocalMinimumOn squareGaussian univ (-1) := by
  apply not_source_local_minimum_of_right_decrease (b := 0) (by norm_num)
  intro x hx
  rw [squareGaussian_neg_one]
  exact squareGaussian_strict_maximum hx.1.ne' (by intro h; linarith [hx.2])

theorem squareGaussian_not_source_minimum_one :
    ¬ IsLocalMinimumOn squareGaussian univ 1 := by
  apply not_source_local_minimum_of_right_decrease (b := 2) (by norm_num)
  intro x hx
  rw [squareGaussian_one]
  exact squareGaussian_strict_maximum (by intro h; linarith [hx.1]) hx.1.ne'

/-- Bài 11(c): cực tiểu duy nhất tại 0; cực đại tại `±1`, giá trị `1/e`. -/
theorem source_square_gaussian_extrema :
    squareGaussian 0 = 0 ∧ squareGaussian (-1) = 1 / Real.exp 1 ∧
      squareGaussian 1 = 1 / Real.exp 1 ∧
      (∀ x : ℝ, IsLocalMinimumOn squareGaussian univ x ↔ x = 0) ∧
      (∀ x : ℝ, IsLocalMaximumOn squareGaussian univ x ↔ x = -1 ∨ x = 1) := by
  refine ⟨squareGaussian_zero, squareGaussian_neg_one, squareGaussian_one, ?_, ?_⟩
  · intro x
    constructor
    · intro h
      have hc := (squareGaussian_critical_iff x).mp
        (fermat isOpen_univ (Or.inl h) (squareGaussian_hasDerivAt x).differentiableAt)
      rcases hc with hx | hx | hx
      · exact hx
      · subst x
        exact False.elim (squareGaussian_not_source_minimum_neg_one h)
      · subst x
        exact False.elim (squareGaussian_not_source_minimum_one h)
    · rintro rfl
      exact squareGaussian_source_minimum_zero
  · intro x
    constructor
    · intro h
      have hc := (squareGaussian_critical_iff x).mp
        (fermat isOpen_univ (Or.inr h) (squareGaussian_hasDerivAt x).differentiableAt)
      rcases hc with hx | hx | hx
      · subst x
        exact False.elim (squareGaussian_not_source_maximum_zero h)
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (rfl | rfl)
      · exact squareGaussian_source_maximum_neg_one
      · exact squareGaussian_source_maximum_one

end calculus.Chapter04.Section04CompleteExtremaExercises
