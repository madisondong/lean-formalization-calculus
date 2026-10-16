import calculus.Chapter04.Section04RationalFunctionInvestigationSupport
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bài 4.4.14(d): khảo sát (x−1)²(x−2)³ trên ℝ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2758–2764.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04PolynomialFunctionInvestigationExercise
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03
open calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04RationalFunctionInvestigationSupport
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport

def subOneSqMulSubTwoCube (x : ℝ) : ℝ := (x - 1) ^ 2 * (x - 2) ^ 3

def subOneSqMulSubTwoCubeFirstDeriv (x : ℝ) : ℝ := (x - 1) * (x - 2) ^ 2 * (5 * x - 7)

def subOneSqMulSubTwoCubeSecondDeriv (x : ℝ) : ℝ := 2 * (x - 2) * (10 * x ^ 2 - 28 * x + 19)

def subOneSqMulSubTwoCubeFirstInflectionAbscissa : ℝ := (14 - Real.sqrt 6) / 10

def subOneSqMulSubTwoCubeSecondInflectionAbscissa : ℝ := (14 + Real.sqrt 6) / 10

theorem subOneSqMulSubTwoCube_hasDerivAt (x : ℝ) :
    HasDerivAt subOneSqMulSubTwoCube (subOneSqMulSubTwoCubeFirstDeriv x) x := by
  change HasDerivAt (fun y : ℝ ↦ (y - 1) ^ 2 * (y - 2) ^ 3) _ x
  have h := (((hasDerivAt_id x).sub_const 1).fun_pow 2).fun_mul
    (((hasDerivAt_id x).sub_const 2).fun_pow 3)
  apply h.congr_deriv
  dsimp only [subOneSqMulSubTwoCubeFirstDeriv]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, mul_one, id_eq]
  ring

theorem subOneSqMulSubTwoCubeFirstDeriv_hasDerivAt (x : ℝ) :
    HasDerivAt subOneSqMulSubTwoCubeFirstDeriv (subOneSqMulSubTwoCubeSecondDeriv x) x := by
  change HasDerivAt (fun y : ℝ ↦ (y - 1) * (y - 2) ^ 2 * (5 * y - 7)) _ x
  have h := (((hasDerivAt_id x).sub_const 1).fun_mul
    (((hasDerivAt_id x).sub_const 2).fun_pow 2)).fun_mul
    (((hasDerivAt_id x).const_mul 5).sub_const 7)
  apply h.congr_deriv
  dsimp only [subOneSqMulSubTwoCubeSecondDeriv]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, mul_one, id_eq]
  ring

theorem subOneSqMulSubTwoCube_second_hasDerivAt (x : ℝ) :
    HasDerivAt (deriv subOneSqMulSubTwoCube) (subOneSqMulSubTwoCubeSecondDeriv x) x :=
  hasDerivAt_deriv_of_open_formula isOpen_univ (mem_univ x)
    (fun y _ ↦ subOneSqMulSubTwoCube_hasDerivAt y) (subOneSqMulSubTwoCubeFirstDeriv_hasDerivAt x)

theorem subOneSqMulSubTwoCube_deriv (x : ℝ) : deriv subOneSqMulSubTwoCube x = subOneSqMulSubTwoCubeFirstDeriv x :=
  (subOneSqMulSubTwoCube_hasDerivAt x).deriv

theorem subOneSqMulSubTwoCube_second_deriv (x : ℝ) :
    deriv (deriv subOneSqMulSubTwoCube) x = subOneSqMulSubTwoCubeSecondDeriv x :=
  (subOneSqMulSubTwoCube_second_hasDerivAt x).deriv

theorem subOneSqMulSubTwoCube_continuous : Continuous subOneSqMulSubTwoCube :=
  continuous_iff_continuousAt.mpr fun x ↦ (subOneSqMulSubTwoCube_hasDerivAt x).continuousAt

theorem subOneSqMulSubTwoCube_second_continuous : Continuous (deriv (deriv subOneSqMulSubTwoCube)) := by
  have he : deriv (deriv subOneSqMulSubTwoCube) = subOneSqMulSubTwoCubeSecondDeriv :=
    funext subOneSqMulSubTwoCube_second_deriv
  rw [he]
  unfold subOneSqMulSubTwoCubeSecondDeriv
  fun_prop

theorem subOneSqMulSubTwoCube_stationary_iff (x : ℝ) :
    deriv subOneSqMulSubTwoCube x = 0 ↔ x = 1 ∨ x = 7 / 5 ∨ x = 2 := by
  rw [subOneSqMulSubTwoCube_deriv]
  unfold subOneSqMulSubTwoCubeFirstDeriv
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp h)))
    · exact Or.inr (Or.inl (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

theorem subOneSqMulSubTwoCube_first_pos_left {x : ℝ} (hx : x < 1) : 0 < deriv subOneSqMulSubTwoCube x := by
  rw [subOneSqMulSubTwoCube_deriv]
  unfold subOneSqMulSubTwoCubeFirstDeriv
  have hs : 0 < (x - 2) ^ 2 := sq_pos_of_ne_zero (by linarith)
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) hs) (by linarith)

theorem subOneSqMulSubTwoCube_first_neg_middle {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) (7 / 5)) :
    deriv subOneSqMulSubTwoCube x < 0 := by
  rw [subOneSqMulSubTwoCube_deriv]
  unfold subOneSqMulSubTwoCubeFirstDeriv
  have hs : 0 < (x - 2) ^ 2 := sq_pos_of_ne_zero (by linarith [hx.2])
  exact mul_neg_of_pos_of_neg (mul_pos (by linarith [hx.1]) hs) (by linarith [hx.2])

theorem subOneSqMulSubTwoCube_first_pos_right {x : ℝ} (hx : 7 / 5 < x) (hne : x ≠ 2) :
    0 < deriv subOneSqMulSubTwoCube x := by
  rw [subOneSqMulSubTwoCube_deriv]
  unfold subOneSqMulSubTwoCubeFirstDeriv
  have hs : 0 < (x - 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  exact mul_pos (mul_pos (by linarith) hs) (by linarith)


theorem subOneSqMulSubTwoCube_variation_closed :
    StrictMonoOn subOneSqMulSubTwoCube (Iic (1 : ℝ)) ∧
      StrictAntiOn subOneSqMulSubTwoCube (Icc (1 : ℝ) (7 / 5)) ∧
      StrictMonoOn subOneSqMulSubTwoCube (Ici (7 / 5 : ℝ)) := by
  have hl : StrictMonoOn subOneSqMulSubTwoCube (Iic (1 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic _) subOneSqMulSubTwoCube_continuous.continuousOn
    intro x hx
    rw [interior_Iic] at hx
    exact subOneSqMulSubTwoCube_first_pos_left hx
  have hm : StrictAntiOn subOneSqMulSubTwoCube (Icc (1 : ℝ) (7 / 5)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) subOneSqMulSubTwoCube_continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact subOneSqMulSubTwoCube_first_neg_middle hx
  have hr₁ : StrictMonoOn subOneSqMulSubTwoCube (Icc (7 / 5 : ℝ) 2) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) subOneSqMulSubTwoCube_continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact subOneSqMulSubTwoCube_first_pos_right hx.1 hx.2.ne
  have hr₂ : StrictMonoOn subOneSqMulSubTwoCube (Ici (2 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) subOneSqMulSubTwoCube_continuous.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact subOneSqMulSubTwoCube_first_pos_right (by linarith [mem_Ioi.mp hx]) hx.ne'
  refine ⟨hl, hm, ?_⟩
  intro x hx y hy hxy
  by_cases hy2 : y ≤ 2
  · exact hr₁ ⟨hx, hxy.le.trans hy2⟩ ⟨hy, hy2⟩ hxy
  · have hygt : 2 < y := lt_of_not_ge hy2
    by_cases hx2 : x < 2
    · exact (hr₁ ⟨hx, hx2.le⟩ ⟨by norm_num, le_refl 2⟩ hx2).trans
        (hr₂ (mem_Ici.mpr (le_refl 2)) (mem_Ici.mpr hygt.le) hygt)
    · exact hr₂ (mem_Ici.mpr (le_of_not_gt hx2)) (mem_Ici.mpr hygt.le) hxy

theorem subOneSqMulSubTwoCube_values :
    subOneSqMulSubTwoCube 0 = -8 ∧ subOneSqMulSubTwoCube 1 = 0 ∧
      subOneSqMulSubTwoCube (7 / 5) = -108 / 3125 ∧ subOneSqMulSubTwoCube 2 = 0 := by
  norm_num [subOneSqMulSubTwoCube]

theorem subOneSqMulSubTwoCube_zero_iff (x : ℝ) : subOneSqMulSubTwoCube x = 0 ↔ x = 1 ∨ x = 2 := by
  unfold subOneSqMulSubTwoCube
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp (sq_eq_zero_iff.mp h))
    · exact Or.inr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h))
  · rintro (rfl | rfl) <;> norm_num

theorem subOneSqMulSubTwoCube_source_maximum_one : IsLocalMaximumOn subOneSqMulSubTwoCube univ 1 := by
  refine ⟨mem_univ _, 1 / 4, by norm_num, ?_⟩
  intro x hx
  rw [subOneSqMulSubTwoCube_values.2.1]
  unfold subOneSqMulSubTwoCube
  have hd : x - 2 < 0 := by linarith [hx.1.2]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    (by rw [pow_succ]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hd.le)

theorem subOneSqMulSubTwoCube_source_minimum_seven_fifths :
    IsLocalMinimumOn subOneSqMulSubTwoCube univ (7 / 5) := by
  refine ⟨mem_univ _, 1 / 5, by norm_num, ?_⟩
  intro x hx
  rcases le_or_gt x (7 / 5) with hl | hr
  · exact subOneSqMulSubTwoCube_variation_closed.2.1.antitoneOn
      ⟨by linarith [hx.1.1], hl⟩ ⟨by norm_num, le_refl _⟩ hl
  · exact subOneSqMulSubTwoCube_variation_closed.2.2.monotoneOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hr.le) hr.le

theorem subOneSqMulSubTwoCube_not_source_minimum_one : ¬ IsLocalMinimumOn subOneSqMulSubTwoCube univ 1 := by
  apply no_local_minimum_of_right_decrease (b := 7 / 5) (by norm_num) (subset_univ _)
  intro x hx
  exact subOneSqMulSubTwoCube_variation_closed.2.1 ⟨le_refl 1, by norm_num⟩ ⟨hx.1.le, hx.2.le⟩ hx.1

theorem subOneSqMulSubTwoCube_not_source_maximum_seven_fifths :
    ¬ IsLocalMaximumOn subOneSqMulSubTwoCube univ (7 / 5) := by
  apply no_local_maximum_of_right_increase (b := 2) (by norm_num) (subset_univ _)
  intro x hx
  exact subOneSqMulSubTwoCube_variation_closed.2.2 (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx.1.le) hx.1

theorem subOneSqMulSubTwoCube_not_source_maximum_two : ¬ IsLocalMaximumOn subOneSqMulSubTwoCube univ 2 := by
  apply no_local_maximum_of_right_increase (b := 3) (by norm_num) (subset_univ _)
  intro x hx
  exact subOneSqMulSubTwoCube_variation_closed.2.2 (mem_Ici.mpr (by norm_num)) (mem_Ici.mpr (by linarith [hx.1])) hx.1

theorem subOneSqMulSubTwoCube_not_source_minimum_two : ¬ IsLocalMinimumOn subOneSqMulSubTwoCube univ 2 := by
  rintro ⟨_, δ, hδ, hbound⟩
  let t : ℝ := min (δ / 2) (1 / 4)
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htq : t ≤ 1 / 4 := min_le_right _ _
  have hx : 7 / 5 ≤ 2 - t := by linarith
  have hs := subOneSqMulSubTwoCube_variation_closed.2.2 hx (by norm_num) (by linarith : 2 - t < 2)
  exact hs.not_ge (hbound (2 - t) ⟨⟨by linarith, by linarith⟩, mem_univ _⟩)

theorem subOneSqMulSubTwoCube_extrema :
    (∀ x : ℝ, IsLocalMaximumOn subOneSqMulSubTwoCube univ x ↔ x = 1) ∧
      (∀ x : ℝ, IsLocalMinimumOn subOneSqMulSubTwoCube univ x ↔ x = 7 / 5) := by
  constructor
  · intro x
    constructor
    · intro h
      have hs := (subOneSqMulSubTwoCube_stationary_iff x).mp
        (fermat isOpen_univ (Or.inr h) (subOneSqMulSubTwoCube_hasDerivAt x).differentiableAt)
      rcases hs with hs | hs | hs
      · exact hs
      · subst x; exact False.elim (subOneSqMulSubTwoCube_not_source_maximum_seven_fifths h)
      · subst x; exact False.elim (subOneSqMulSubTwoCube_not_source_maximum_two h)
    · rintro rfl
      exact subOneSqMulSubTwoCube_source_maximum_one
  · intro x
    constructor
    · intro h
      have hs := (subOneSqMulSubTwoCube_stationary_iff x).mp
        (fermat isOpen_univ (Or.inl h) (subOneSqMulSubTwoCube_hasDerivAt x).differentiableAt)
      rcases hs with hs | hs | hs
      · subst x; exact False.elim (subOneSqMulSubTwoCube_not_source_minimum_one h)
      · exact hs
      · subst x; exact False.elim (subOneSqMulSubTwoCube_not_source_minimum_two h)
    · rintro rfl
      exact subOneSqMulSubTwoCube_source_minimum_seven_fifths

theorem subOneSqMulSubTwoCubeInflectionAbscissae_order :
    1 < subOneSqMulSubTwoCubeFirstInflectionAbscissa ∧ subOneSqMulSubTwoCubeFirstInflectionAbscissa < 7 / 5 ∧
      7 / 5 < subOneSqMulSubTwoCubeSecondInflectionAbscissa ∧ subOneSqMulSubTwoCubeSecondInflectionAbscissa < 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hp := Real.sqrt_nonneg (6 : ℝ)
  have hbounds : 2 < Real.sqrt 6 ∧ Real.sqrt 6 < 3 := by constructor <;> nlinarith
  unfold subOneSqMulSubTwoCubeFirstInflectionAbscissa subOneSqMulSubTwoCubeSecondInflectionAbscissa
  constructor
  · linarith [hbounds.2]
  constructor
  · linarith [hbounds.1]
  constructor <;> linarith [hbounds.1, hbounds.2]

theorem subOneSqMulSubTwoCubeSecondDeriv_factor (x : ℝ) :
    subOneSqMulSubTwoCubeSecondDeriv x =
      20 * (x - 2) * (x - subOneSqMulSubTwoCubeFirstInflectionAbscissa) * (x - subOneSqMulSubTwoCubeSecondInflectionAbscissa) := by
  unfold subOneSqMulSubTwoCubeSecondDeriv subOneSqMulSubTwoCubeFirstInflectionAbscissa subOneSqMulSubTwoCubeSecondInflectionAbscissa
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  ring

theorem subOneSqMulSubTwoCube_second_zero_iff (x : ℝ) :
    deriv (deriv subOneSqMulSubTwoCube) x = 0 ↔
      x = subOneSqMulSubTwoCubeFirstInflectionAbscissa ∨ x = subOneSqMulSubTwoCubeSecondInflectionAbscissa ∨ x = 2 := by
  rw [subOneSqMulSubTwoCube_second_deriv, subOneSqMulSubTwoCubeSecondDeriv_factor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact Or.inr (Or.inr (sub_eq_zero.mp h))
      · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · rintro (rfl | rfl | rfl) <;> simp

theorem subOneSqMulSubTwoCube_second_signs :
    (∀ x < subOneSqMulSubTwoCubeFirstInflectionAbscissa, deriv (deriv subOneSqMulSubTwoCube) x < 0) ∧
      (∀ x ∈ Ioo subOneSqMulSubTwoCubeFirstInflectionAbscissa subOneSqMulSubTwoCubeSecondInflectionAbscissa, 0 < deriv (deriv subOneSqMulSubTwoCube) x) ∧
      (∀ x ∈ Ioo subOneSqMulSubTwoCubeSecondInflectionAbscissa 2, deriv (deriv subOneSqMulSubTwoCube) x < 0) ∧
      (∀ x > (2 : ℝ), 0 < deriv (deriv subOneSqMulSubTwoCube) x) := by
  have ho := subOneSqMulSubTwoCubeInflectionAbscissae_order
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [subOneSqMulSubTwoCube_second_deriv, subOneSqMulSubTwoCubeSecondDeriv_factor]
    have h2 : x - 2 < 0 := by linarith [ho.2.1, ho.2.2.2]
    have hL : x - subOneSqMulSubTwoCubeFirstInflectionAbscissa < 0 := sub_neg.mpr hx
    have hU : x - subOneSqMulSubTwoCubeSecondInflectionAbscissa < 0 := by linarith [ho.2.1, ho.2.2.1]
    exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (by norm_num) h2) hL) hU
  · intro x hx
    rw [subOneSqMulSubTwoCube_second_deriv, subOneSqMulSubTwoCubeSecondDeriv_factor]
    have h2 : x - 2 < 0 := by linarith [hx.2, ho.2.2.2]
    have hL : 0 < x - subOneSqMulSubTwoCubeFirstInflectionAbscissa := sub_pos.mpr hx.1
    have hU : x - subOneSqMulSubTwoCubeSecondInflectionAbscissa < 0 := sub_neg.mpr hx.2
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (by norm_num) h2) hL) hU
  · intro x hx
    rw [subOneSqMulSubTwoCube_second_deriv, subOneSqMulSubTwoCubeSecondDeriv_factor]
    have hL : 0 < x - subOneSqMulSubTwoCubeFirstInflectionAbscissa := by linarith [hx.1, ho.2.1, ho.2.2.1]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hx.2)) hL) (sub_pos.mpr hx.1)
  · intro x hx
    rw [subOneSqMulSubTwoCube_second_deriv, subOneSqMulSubTwoCubeSecondDeriv_factor]
    exact mul_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hx))
      (by linarith [ho.2.1, ho.2.2.2])) (by linarith [ho.2.2.2])

theorem subOneSqMulSubTwoCube_source_two (a b : ℝ) : DifferentiableToOrderOn 2 subOneSqMulSubTwoCube (Ioo a b) :=
  source_two_of_pointwise (subset_univ _)
    (fun x _ ↦ (subOneSqMulSubTwoCube_hasDerivAt x).differentiableAt)
    (fun x _ ↦ (subOneSqMulSubTwoCube_second_hasDerivAt x).differentiableAt)

theorem subOneSqMulSubTwoCube_convexity :
    ConcaveOn ℝ (Iio subOneSqMulSubTwoCubeFirstInflectionAbscissa) subOneSqMulSubTwoCube ∧
      ConvexOnOpenInterval subOneSqMulSubTwoCube subOneSqMulSubTwoCubeFirstInflectionAbscissa subOneSqMulSubTwoCubeSecondInflectionAbscissa ∧
      ConcaveOnOpenInterval subOneSqMulSubTwoCube subOneSqMulSubTwoCubeSecondInflectionAbscissa 2 ∧
      ConvexOn ℝ (Ioi (2 : ℝ)) subOneSqMulSubTwoCube := by
  refine ⟨concaveOn_of_deriv2_nonpos' (convex_Iio _)
    (fun x _ ↦ (subOneSqMulSubTwoCube_hasDerivAt x).differentiableAt.differentiableWithinAt)
    (fun x _ ↦ (subOneSqMulSubTwoCube_second_hasDerivAt x).differentiableAt.differentiableWithinAt) ?_,
    (convexOnOpenInterval_iff_second_deriv_nonneg subOneSqMulSubTwoCube _ _ (subOneSqMulSubTwoCube_source_two _ _)).mpr ?_,
    concaveOnOpenInterval_of_second_deriv_nonpos subOneSqMulSubTwoCube _ _ (subOneSqMulSubTwoCube_source_two _ _) ?_,
    convexOn_of_deriv2_nonneg' (convex_Ioi _)
      (fun x _ ↦ (subOneSqMulSubTwoCube_hasDerivAt x).differentiableAt.differentiableWithinAt)
      (fun x _ ↦ (subOneSqMulSubTwoCube_second_hasDerivAt x).differentiableAt.differentiableWithinAt) ?_⟩
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      (subOneSqMulSubTwoCube_second_signs.1 x hx).le
  · intro x hx
    exact (subOneSqMulSubTwoCube_second_signs.2.1 x hx).le
  · intro x hx
    exact (subOneSqMulSubTwoCube_second_signs.2.2.1 x hx).le
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      (subOneSqMulSubTwoCube_second_signs.2.2.2 x hx).le


theorem subOneSqMulSubTwoCube_first_inflection :
    ∃ a b : ℝ, SourceInflectionOn subOneSqMulSubTwoCube a b subOneSqMulSubTwoCubeFirstInflectionAbscissa := by
  let δ : ℝ := (subOneSqMulSubTwoCubeSecondInflectionAbscissa - subOneSqMulSubTwoCubeFirstInflectionAbscissa) / 2
  have hgap : subOneSqMulSubTwoCubeFirstInflectionAbscissa < subOneSqMulSubTwoCubeSecondInflectionAbscissa :=
    subOneSqMulSubTwoCubeInflectionAbscissae_order.2.1.trans subOneSqMulSubTwoCubeInflectionAbscissae_order.2.2.1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨subOneSqMulSubTwoCubeFirstInflectionAbscissa - δ, subOneSqMulSubTwoCubeFirstInflectionAbscissa + δ,
    sourceInflectionOn_of_second_deriv_neg_pos hδ
      (subOneSqMulSubTwoCube_source_two _ _) (subOneSqMulSubTwoCube_source_two _ _)
      (Or.inl (subOneSqMulSubTwoCube_hasDerivAt _).differentiableAt) ?_ ?_⟩
  · intro x hx
    exact subOneSqMulSubTwoCube_second_signs.1 x hx.2
  · intro x hx
    exact subOneSqMulSubTwoCube_second_signs.2.1 x ⟨hx.1, by dsimp [δ] at hx; linarith [hx.2]⟩


theorem subOneSqMulSubTwoCube_second_inflection :
    ∃ a b : ℝ, SourceInflectionOn subOneSqMulSubTwoCube a b subOneSqMulSubTwoCubeSecondInflectionAbscissa := by
  let δ : ℝ := min ((subOneSqMulSubTwoCubeSecondInflectionAbscissa - subOneSqMulSubTwoCubeFirstInflectionAbscissa) / 2)
    ((2 - subOneSqMulSubTwoCubeSecondInflectionAbscissa) / 2)
  have hgap : subOneSqMulSubTwoCubeFirstInflectionAbscissa < subOneSqMulSubTwoCubeSecondInflectionAbscissa :=
    subOneSqMulSubTwoCubeInflectionAbscissae_order.2.1.trans subOneSqMulSubTwoCubeInflectionAbscissae_order.2.2.1
  have hup : subOneSqMulSubTwoCubeSecondInflectionAbscissa < 2 := subOneSqMulSubTwoCubeInflectionAbscissae_order.2.2.2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by linarith)
  have hL : δ ≤ (subOneSqMulSubTwoCubeSecondInflectionAbscissa - subOneSqMulSubTwoCubeFirstInflectionAbscissa) / 2 := min_le_left _ _
  have hR : δ ≤ (2 - subOneSqMulSubTwoCubeSecondInflectionAbscissa) / 2 := min_le_right _ _
  refine ⟨subOneSqMulSubTwoCubeSecondInflectionAbscissa - δ, subOneSqMulSubTwoCubeSecondInflectionAbscissa + δ,
    sourceInflectionOn_of_second_deriv_pos_neg hδ
      (subOneSqMulSubTwoCube_source_two _ _) (subOneSqMulSubTwoCube_source_two _ _)
      (Or.inl (subOneSqMulSubTwoCube_hasDerivAt _).differentiableAt) ?_ ?_⟩
  · intro x hx
    exact subOneSqMulSubTwoCube_second_signs.2.1 x ⟨by linarith [hx.1], hx.2⟩
  · intro x hx
    exact subOneSqMulSubTwoCube_second_signs.2.2.1 x ⟨hx.1, by linarith [hx.2]⟩


theorem subOneSqMulSubTwoCube_inflection_at_two : ∃ a b : ℝ, SourceInflectionOn subOneSqMulSubTwoCube a b 2 := by
  let δ : ℝ := (2 - subOneSqMulSubTwoCubeSecondInflectionAbscissa) / 2
  have hup : subOneSqMulSubTwoCubeSecondInflectionAbscissa < 2 := subOneSqMulSubTwoCubeInflectionAbscissae_order.2.2.2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨2 - δ, 2 + δ, sourceInflectionOn_of_second_deriv_neg_pos hδ
    (subOneSqMulSubTwoCube_source_two _ _) (subOneSqMulSubTwoCube_source_two _ _)
    (Or.inl (subOneSqMulSubTwoCube_hasDerivAt _).differentiableAt) ?_ ?_⟩
  · intro x hx
    exact subOneSqMulSubTwoCube_second_signs.2.2.1 x ⟨by dsimp [δ] at hx; linarith [hx.1], hx.2⟩
  · intro x hx
    exact subOneSqMulSubTwoCube_second_signs.2.2.2 x hx.1

theorem subOneSqMulSubTwoCube_inflection_iff (x : ℝ) :
    (∃ a b : ℝ, SourceInflectionOn subOneSqMulSubTwoCube a b x) ↔
      x = subOneSqMulSubTwoCubeFirstInflectionAbscissa ∨ x = subOneSqMulSubTwoCubeSecondInflectionAbscissa ∨ x = 2 := by
  constructor
  · rintro ⟨a, b, hu⟩
    exact (subOneSqMulSubTwoCube_second_zero_iff x).mp
      (second_zero_of_sourceInflection (D := univ) (subset_univ _)
        (fun y _ ↦ (subOneSqMulSubTwoCube_hasDerivAt y).differentiableAt)
        (fun y _ ↦ (subOneSqMulSubTwoCube_second_hasDerivAt y).differentiableAt)
        subOneSqMulSubTwoCube_second_continuous.continuousAt hu)
  · rintro (rfl | rfl | rfl)
    · exact subOneSqMulSubTwoCube_first_inflection
    · exact subOneSqMulSubTwoCube_second_inflection
    · exact subOneSqMulSubTwoCube_inflection_at_two

theorem subOneSqMulSubTwoCube_inflection_ordinates :
    subOneSqMulSubTwoCube subOneSqMulSubTwoCubeFirstInflectionAbscissa = -207 / 12500 + 21 * Real.sqrt 6 / 25000 ∧
      subOneSqMulSubTwoCube subOneSqMulSubTwoCubeSecondInflectionAbscissa = -207 / 12500 - 21 * Real.sqrt 6 / 25000 := by
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have h3 : Real.sqrt 6 ^ 3 = 6 * Real.sqrt 6 := by rw [pow_succ, h2]
  have h4 : Real.sqrt 6 ^ 4 = 36 := by
    calc
      Real.sqrt 6 ^ 4 = (Real.sqrt 6 ^ 2) ^ 2 := by ring
      _ = 36 := by rw [h2]; norm_num
  have h5 : Real.sqrt 6 ^ 5 = 36 * Real.sqrt 6 := by rw [pow_succ, h4]
  constructor
  · unfold subOneSqMulSubTwoCube subOneSqMulSubTwoCubeFirstInflectionAbscissa
    ring_nf
    nlinarith [h2, h3, h4, h5]
  · unfold subOneSqMulSubTwoCube subOneSqMulSubTwoCubeSecondInflectionAbscissa
    ring_nf
    nlinarith [h2, h3, h4, h5]

theorem subOneSqMulSubTwoCube_ratio_at_end {F : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ x⁻¹) F (𝓝 0))
    (hp : Tendsto (fun x : ℝ ↦ x ^ 4) F atTop)
    (hn : ∀ᶠ x : ℝ in F, x ≠ 0) :
    Tendsto (fun x : ℝ ↦ subOneSqMulSubTwoCube x / x) F atTop := by
  have hc := ((hi.const_sub 1).pow 2).mul (((hi.const_mul 2).const_sub 1).pow 3)
  norm_num at hc
  have h := hp.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hc
  apply h.congr'
  filter_upwards [hn] with x hx
  dsimp only [subOneSqMulSubTwoCube]
  field_simp [hx]

theorem subOneSqMulSubTwoCube_ratio_top : Tendsto (fun x : ℝ ↦ subOneSqMulSubTwoCube x / x) atTop atTop := by
  apply subOneSqMulSubTwoCube_ratio_at_end tendsto_inv_atTop_zero (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0))
  exact (eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne'

theorem subOneSqMulSubTwoCube_ratio_bot : Tendsto (fun x : ℝ ↦ subOneSqMulSubTwoCube x / x) atBot atTop := by
  have hs : Tendsto (fun x : ℝ ↦ x ^ 2) atBot atTop := by
    simpa only [pow_two] using! (tendsto_id : Tendsto (fun x : ℝ ↦ x) atBot atBot).atBot_mul_atBot₀ tendsto_id
  have hp : Tendsto (fun x : ℝ ↦ x ^ 4) atBot atTop :=
    (hs.atTop_mul_atTop₀ hs).congr fun x ↦ by ring
  apply subOneSqMulSubTwoCube_ratio_at_end tendsto_inv_atBot_zero hp
  exact (eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne

theorem subOneSqMulSubTwoCube_limit_top : Tendsto subOneSqMulSubTwoCube atTop atTop := by
  apply (subOneSqMulSubTwoCube_ratio_top.atTop_mul_atTop₀ tendsto_id).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact div_mul_cancel₀ _ hx.ne'

theorem subOneSqMulSubTwoCube_limit_bot : Tendsto subOneSqMulSubTwoCube atBot atBot := by
  apply (subOneSqMulSubTwoCube_ratio_bot.atTop_mul_atBot₀ tendsto_id).congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  exact div_mul_cancel₀ _ hx.ne

theorem subOneSqMulSubTwoCube_asymptotes :
    (∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt subOneSqMulSubTwoCube univ a) ∧
      (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin subOneSqMulSubTwoCube univ b) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin subOneSqMulSubTwoCube univ m b) := by
  have hfull : ∀ᶠ x : ℝ in atTop, x ∈ (univ : Set ℝ) := Eventually.of_forall mem_univ
  have hfullB : ∀ᶠ x : ℝ in atBot, x ∈ (univ : Set ℝ) := Eventually.of_forall mem_univ
  refine ⟨fun a ↦ no_vertical_of_continuousAt (subOneSqMulSubTwoCube_hasDerivAt a).continuousAt, ?_, ?_⟩
  · intro b
    rw [full_tail_horizontal_iff hfull hfullB, HasHorizontalAsymptote]
    rintro (h | h)
    · exact not_tendsto_atTop_of_tendsto_nhds h subOneSqMulSubTwoCube_limit_top
    · exact not_tendsto_atBot_of_tendsto_nhds h subOneSqMulSubTwoCube_limit_bot
  · intro m b
    rw [full_tail_oblique_iff hfull hfullB, HasObliqueAsymptote]
    rintro ⟨_, h | h⟩
    · have hn : ∀ᶠ x : ℝ in atTop, x ≠ 0 := (eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne'
      have hf := ((affine_residual_limit_iff tendsto_inv_atTop_zero hn subOneSqMulSubTwoCube m b).mp h).1
      exact not_tendsto_atTop_of_tendsto_nhds hf subOneSqMulSubTwoCube_ratio_top
    · have hn : ∀ᶠ x : ℝ in atBot, x ≠ 0 := (eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne
      have hf := ((affine_residual_limit_iff tendsto_inv_atBot_zero hn subOneSqMulSubTwoCube m b).mp h).1
      exact not_tendsto_atTop_of_tendsto_nhds hf subOneSqMulSubTwoCube_ratio_bot

theorem subOneSqMulSubTwoCube_range (y : ℝ) : ∃ x : ℝ, subOneSqMulSubTwoCube x = y := by
  obtain ⟨a, ha, hay⟩ := ((eventually_lt_atBot (0 : ℝ)).and
    (subOneSqMulSubTwoCube_limit_bot.eventually (eventually_lt_atBot y))).exists
  obtain ⟨b, hb, hby⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (subOneSqMulSubTwoCube_limit_top.eventually (eventually_gt_atTop y))).exists
  have hmem := intermediate_value_Icc (show a ≤ b by linarith)
    subOneSqMulSubTwoCube_continuous.continuousOn (show y ∈ Icc (subOneSqMulSubTwoCube a) (subOneSqMulSubTwoCube b) from ⟨hay.le, hby.le⟩)
  rcases hmem with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

theorem subOneSqMulSubTwoCube_graph_iff (x y : ℝ) :
    subOneSqMulSubTwoCube x = y ↔ y = (x - 1) ^ 2 * (x - 2) ^ 3 := by
  unfold subOneSqMulSubTwoCube
  exact eq_comm

/-- Bài 14(d): khảo sát `(x−1)²(x−2)³` trên ℝ. -/
theorem source_polynomial_function_investigation :
    (∀ x : ℝ, HasDerivAt subOneSqMulSubTwoCube ((x - 1) * (x - 2) ^ 2 * (5 * x - 7)) x ∧
      HasDerivAt (deriv subOneSqMulSubTwoCube) (2 * (x - 2) * (10 * x ^ 2 - 28 * x + 19)) x) ∧
      (∀ x : ℝ, deriv subOneSqMulSubTwoCube x = 0 ↔ x = 1 ∨ x = 7 / 5 ∨ x = 2) ∧
      (StrictMonoOn subOneSqMulSubTwoCube (Iic (1 : ℝ)) ∧
        StrictAntiOn subOneSqMulSubTwoCube (Icc (1 : ℝ) (7 / 5)) ∧
        StrictMonoOn subOneSqMulSubTwoCube (Ici (7 / 5 : ℝ))) ∧
      ((∀ x : ℝ, IsLocalMaximumOn subOneSqMulSubTwoCube univ x ↔ x = 1) ∧
        ∀ x : ℝ, IsLocalMinimumOn subOneSqMulSubTwoCube univ x ↔ x = 7 / 5) ∧
      (subOneSqMulSubTwoCube 0 = -8 ∧ subOneSqMulSubTwoCube 1 = 0 ∧
        subOneSqMulSubTwoCube (7 / 5) = -108 / 3125 ∧ subOneSqMulSubTwoCube 2 = 0) ∧
      (∀ x : ℝ, subOneSqMulSubTwoCube x = 0 ↔ x = 1 ∨ x = 2) ∧
      (ConcaveOn ℝ (Iio subOneSqMulSubTwoCubeFirstInflectionAbscissa) subOneSqMulSubTwoCube ∧
        ConvexOnOpenInterval subOneSqMulSubTwoCube subOneSqMulSubTwoCubeFirstInflectionAbscissa subOneSqMulSubTwoCubeSecondInflectionAbscissa ∧
        ConcaveOnOpenInterval subOneSqMulSubTwoCube subOneSqMulSubTwoCubeSecondInflectionAbscissa 2 ∧
        ConvexOn ℝ (Ioi (2 : ℝ)) subOneSqMulSubTwoCube) ∧
      (∀ x : ℝ, (∃ a b : ℝ, SourceInflectionOn subOneSqMulSubTwoCube a b x) ↔
        x = subOneSqMulSubTwoCubeFirstInflectionAbscissa ∨ x = subOneSqMulSubTwoCubeSecondInflectionAbscissa ∨ x = 2) ∧
      (subOneSqMulSubTwoCube subOneSqMulSubTwoCubeFirstInflectionAbscissa = -207 / 12500 + 21 * Real.sqrt 6 / 25000 ∧
        subOneSqMulSubTwoCube subOneSqMulSubTwoCubeSecondInflectionAbscissa = -207 / 12500 - 21 * Real.sqrt 6 / 25000) ∧
      (Tendsto subOneSqMulSubTwoCube atTop atTop ∧ Tendsto subOneSqMulSubTwoCube atBot atBot) ∧
      ((∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt subOneSqMulSubTwoCube univ a) ∧
        (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin subOneSqMulSubTwoCube univ b) ∧
        ∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin subOneSqMulSubTwoCube univ m b) ∧
      (∀ y : ℝ, ∃ x : ℝ, subOneSqMulSubTwoCube x = y) ∧
      (∀ x y : ℝ, subOneSqMulSubTwoCube x = y ↔ y = (x - 1) ^ 2 * (x - 2) ^ 3) :=
  ⟨fun x ↦ ⟨subOneSqMulSubTwoCube_hasDerivAt x, subOneSqMulSubTwoCube_second_hasDerivAt x⟩,
    subOneSqMulSubTwoCube_stationary_iff, subOneSqMulSubTwoCube_variation_closed, subOneSqMulSubTwoCube_extrema,
    subOneSqMulSubTwoCube_values, subOneSqMulSubTwoCube_zero_iff, subOneSqMulSubTwoCube_convexity,
    subOneSqMulSubTwoCube_inflection_iff, subOneSqMulSubTwoCube_inflection_ordinates,
    ⟨subOneSqMulSubTwoCube_limit_top, subOneSqMulSubTwoCube_limit_bot⟩, subOneSqMulSubTwoCube_asymptotes,
    subOneSqMulSubTwoCube_range, subOneSqMulSubTwoCube_graph_iff⟩

end calculus.Chapter04.Section04PolynomialFunctionInvestigationExercise
