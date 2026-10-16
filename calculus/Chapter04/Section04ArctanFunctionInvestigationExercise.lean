import calculus.Chapter04.Section04RationalFunctionInvestigationSupport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bài 4.4.14(f): khảo sát x−4 arctan(x) trên ℝ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2758–2766.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04ArctanFunctionInvestigationExercise
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03
open calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04RationalFunctionInvestigationSupport
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport

def identitySubFourArctan (x : ℝ) : ℝ := x - 4 * Real.arctan x

def identitySubFourArctanFirstDeriv (x : ℝ) : ℝ := (x ^ 2 - 3) / (1 + x ^ 2)

def identitySubFourArctanSecondDeriv (x : ℝ) : ℝ := 8 * x / (1 + x ^ 2) ^ 2

def identitySubFourArctanPositiveCriticalAbscissa : ℝ := Real.sqrt 3

theorem identitySubFourArctanPositiveCriticalAbscissa_bounds :
    0 < identitySubFourArctanPositiveCriticalAbscissa ∧ identitySubFourArctanPositiveCriticalAbscissa ^ 2 = 3 ∧ identitySubFourArctanPositiveCriticalAbscissa < 2 := by
  have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos_of_pos (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  exact ⟨hp, hs, by unfold identitySubFourArctanPositiveCriticalAbscissa; nlinarith⟩

theorem identitySubFourArctan_hasDerivAt (x : ℝ) :
    HasDerivAt identitySubFourArctan (identitySubFourArctanFirstDeriv x) x := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have h := (hasDerivAt_id x).sub ((Real.hasDerivAt_arctan x).const_mul 4)
  apply h.congr_deriv
  unfold identitySubFourArctanFirstDeriv
  field_simp [hd]
  ring

theorem identitySubFourArctanFirstDeriv_hasDerivAt (x : ℝ) :
    HasDerivAt identitySubFourArctanFirstDeriv (identitySubFourArctanSecondDeriv x) x := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have h := (((hasDerivAt_id x).fun_pow 2).sub_const 3).div
    (((hasDerivAt_id x).fun_pow 2).const_add 1) hd
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  apply h.congr_deriv
  unfold identitySubFourArctanSecondDeriv
  field_simp [hd]
  ring

theorem identitySubFourArctan_second_hasDerivAt (x : ℝ) :
    HasDerivAt (deriv identitySubFourArctan) (identitySubFourArctanSecondDeriv x) x :=
  hasDerivAt_deriv_of_open_formula isOpen_univ (mem_univ x)
    (fun y _ ↦ identitySubFourArctan_hasDerivAt y) (identitySubFourArctanFirstDeriv_hasDerivAt x)

theorem identitySubFourArctan_deriv (x : ℝ) : deriv identitySubFourArctan x = identitySubFourArctanFirstDeriv x :=
  (identitySubFourArctan_hasDerivAt x).deriv

theorem identitySubFourArctan_second_deriv (x : ℝ) :
    deriv (deriv identitySubFourArctan) x = identitySubFourArctanSecondDeriv x := (identitySubFourArctan_second_hasDerivAt x).deriv

theorem identitySubFourArctan_continuous : Continuous identitySubFourArctan :=
  continuous_iff_continuousAt.mpr fun x ↦ (identitySubFourArctan_hasDerivAt x).continuousAt

theorem identitySubFourArctan_second_continuous : Continuous (deriv (deriv identitySubFourArctan)) := by
  rw [show deriv (deriv identitySubFourArctan) = identitySubFourArctanSecondDeriv from funext identitySubFourArctan_second_deriv]
  unfold identitySubFourArctanSecondDeriv
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact pow_ne_zero 2 (show 1 + x ^ 2 ≠ 0 by positivity)

theorem identitySubFourArctan_derivative_signs (x : ℝ) :
    (deriv identitySubFourArctan x < 0 ↔ -identitySubFourArctanPositiveCriticalAbscissa < x ∧ x < identitySubFourArctanPositiveCriticalAbscissa) ∧
      (0 < deriv identitySubFourArctan x ↔ x < -identitySubFourArctanPositiveCriticalAbscissa ∨ identitySubFourArctanPositiveCriticalAbscissa < x) ∧
      (deriv identitySubFourArctan x = 0 ↔ x = -identitySubFourArctanPositiveCriticalAbscissa ∨ x = identitySubFourArctanPositiveCriticalAbscissa) := by
  have hr := identitySubFourArctanPositiveCriticalAbscissa_bounds.1
  have hs := identitySubFourArctanPositiveCriticalAbscissa_bounds.2.1
  have hd : 0 < 1 + x ^ 2 := by positivity
  rw [identitySubFourArctan_deriv]
  unfold identitySubFourArctanFirstDeriv
  constructor
  · rw [div_lt_iff₀ hd]
    constructor
    · intro h; exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨hl, hu⟩
      have hp := mul_pos (show 0 < x + identitySubFourArctanPositiveCriticalAbscissa by linarith)
        (show 0 < identitySubFourArctanPositiveCriticalAbscissa - x by linarith)
      nlinarith
  constructor
  · rw [lt_div_iff₀ hd]
    constructor
    · intro h
      by_contra! hn
      have hp := mul_nonneg (show 0 ≤ x + identitySubFourArctanPositiveCriticalAbscissa by linarith [hn.1])
        (show 0 ≤ identitySubFourArctanPositiveCriticalAbscissa - x by linarith [hn.2])
      nlinarith
    · rintro (hl | hu)
      · have hp := mul_pos (show 0 < -x - identitySubFourArctanPositiveCriticalAbscissa by linarith)
          (show 0 < -x + identitySubFourArctanPositiveCriticalAbscissa by linarith)
        nlinarith
      · have hp := mul_pos (show 0 < x - identitySubFourArctanPositiveCriticalAbscissa by linarith)
          (show 0 < x + identitySubFourArctanPositiveCriticalAbscissa by linarith)
        nlinarith
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · have he : x ^ 2 = identitySubFourArctanPositiveCriticalAbscissa ^ 2 := by linarith
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
        · exact Or.inr he
        · exact Or.inl he
      · exact False.elim (hd.ne' h)
    · rintro (rfl | rfl)
      · exact Or.inl (by nlinarith)
      · exact Or.inl (by nlinarith)

theorem identitySubFourArctan_second_signs (x : ℝ) :
    (deriv (deriv identitySubFourArctan) x < 0 ↔ x < 0) ∧
      (0 < deriv (deriv identitySubFourArctan) x ↔ 0 < x) ∧
      (deriv (deriv identitySubFourArctan) x = 0 ↔ x = 0) := by
  have hd : 0 < (1 + x ^ 2) ^ 2 := by positivity
  rw [identitySubFourArctan_second_deriv]
  unfold identitySubFourArctanSecondDeriv
  constructor
  · rw [div_lt_iff₀ hd]; constructor <;> intro h <;> nlinarith
  constructor
  · rw [lt_div_iff₀ hd]; constructor <;> intro h <;> nlinarith
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact False.elim (hd.ne' h)
    · rintro rfl; exact Or.inl (by norm_num)

theorem identitySubFourArctan_variation :
    StrictMonoOn identitySubFourArctan (Iic (-identitySubFourArctanPositiveCriticalAbscissa)) ∧
      StrictAntiOn identitySubFourArctan (Icc (-identitySubFourArctanPositiveCriticalAbscissa) identitySubFourArctanPositiveCriticalAbscissa) ∧
      StrictMonoOn identitySubFourArctan (Ici identitySubFourArctanPositiveCriticalAbscissa) := by
  refine ⟨?_, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Iic _) identitySubFourArctan_continuous.continuousOn
    intro x hx
    rw [interior_Iic] at hx
    exact (identitySubFourArctan_derivative_signs x).2.1.mpr (Or.inl hx)
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _) identitySubFourArctan_continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact (identitySubFourArctan_derivative_signs x).1.mpr hx
  · apply strictMonoOn_of_deriv_pos (convex_Ici _) identitySubFourArctan_continuous.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact (identitySubFourArctan_derivative_signs x).2.1.mpr (Or.inr hx)

theorem identitySubFourArctan_odd (x : ℝ) : identitySubFourArctan (-x) = -identitySubFourArctan x := by
  simp only [identitySubFourArctan, Real.arctan_neg]
  ring

theorem identitySubFourArctan_values :
    identitySubFourArctan 0 = 0 ∧
      identitySubFourArctan (-identitySubFourArctanPositiveCriticalAbscissa) = 4 * Real.pi / 3 - identitySubFourArctanPositiveCriticalAbscissa ∧
      identitySubFourArctan identitySubFourArctanPositiveCriticalAbscissa = identitySubFourArctanPositiveCriticalAbscissa - 4 * Real.pi / 3 ∧
      deriv identitySubFourArctan 0 = -3 := by
  have hv : identitySubFourArctan identitySubFourArctanPositiveCriticalAbscissa = identitySubFourArctanPositiveCriticalAbscissa - 4 * Real.pi / 3 := by
    unfold identitySubFourArctan identitySubFourArctanPositiveCriticalAbscissa
    rw [Real.arctan_sqrt_three]
    ring
  refine ⟨by simp [identitySubFourArctan], ?_, hv, ?_⟩
  · rw [identitySubFourArctan_odd, hv]; ring
  · rw [identitySubFourArctan_deriv]; norm_num [identitySubFourArctanFirstDeriv]

theorem identitySubFourArctan_local_maximum : IsLocalMaximumOn identitySubFourArctan univ (-identitySubFourArctanPositiveCriticalAbscissa) := by
  have hr := identitySubFourArctanPositiveCriticalAbscissa_bounds.1
  refine ⟨mem_univ _, identitySubFourArctanPositiveCriticalAbscissa, hr, ?_⟩
  intro x hx
  rcases le_or_gt x (-identitySubFourArctanPositiveCriticalAbscissa) with hl | hu
  · exact identitySubFourArctan_variation.1.monotoneOn (mem_Iic.mpr hl) (mem_Iic.mpr (le_refl _)) hl
  · exact identitySubFourArctan_variation.2.1.antitoneOn
      ⟨le_refl _, by linarith⟩ ⟨hu.le, by linarith [hx.1.2]⟩ hu.le

theorem identitySubFourArctan_local_minimum : IsLocalMinimumOn identitySubFourArctan univ identitySubFourArctanPositiveCriticalAbscissa := by
  have hr := identitySubFourArctanPositiveCriticalAbscissa_bounds.1
  refine ⟨mem_univ _, identitySubFourArctanPositiveCriticalAbscissa, hr, ?_⟩
  intro x hx
  rcases le_or_gt x identitySubFourArctanPositiveCriticalAbscissa with hl | hu
  · exact identitySubFourArctan_variation.2.1.antitoneOn
      ⟨by linarith [hx.1.1], hl⟩ ⟨by linarith, le_refl _⟩ hl
  · exact identitySubFourArctan_variation.2.2.monotoneOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hu.le) hu.le

theorem identitySubFourArctan_not_minimum_at_negative :
    ¬ IsLocalMinimumOn identitySubFourArctan univ (-identitySubFourArctanPositiveCriticalAbscissa) := by
  apply no_local_minimum_of_right_decrease (b := identitySubFourArctanPositiveCriticalAbscissa)
    (by linarith [identitySubFourArctanPositiveCriticalAbscissa_bounds.1]) (subset_univ _)
  intro x hx
  exact identitySubFourArctan_variation.2.1 ⟨le_refl _, by linarith [identitySubFourArctanPositiveCriticalAbscissa_bounds.1]⟩
    ⟨hx.1.le, hx.2.le⟩ hx.1

theorem identitySubFourArctan_not_maximum_at_positive :
    ¬ IsLocalMaximumOn identitySubFourArctan univ identitySubFourArctanPositiveCriticalAbscissa := by
  apply no_local_maximum_of_right_increase (b := identitySubFourArctanPositiveCriticalAbscissa + 1) (by linarith) (subset_univ _)
  intro x hx
  exact identitySubFourArctan_variation.2.2 (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx.1.le) hx.1

theorem identitySubFourArctan_extrema :
    (∀ x : ℝ, IsLocalMaximumOn identitySubFourArctan univ x ↔ x = -identitySubFourArctanPositiveCriticalAbscissa) ∧
      (∀ x : ℝ, IsLocalMinimumOn identitySubFourArctan univ x ↔ x = identitySubFourArctanPositiveCriticalAbscissa) := by
  constructor
  · intro x
    constructor
    · intro h
      have he := (identitySubFourArctan_derivative_signs x).2.2.mp
        (fermat isOpen_univ (Or.inr h) (identitySubFourArctan_hasDerivAt x).differentiableAt)
      rcases he with he | he
      · exact he
      · subst x; exact False.elim (identitySubFourArctan_not_maximum_at_positive h)
    · rintro rfl; exact identitySubFourArctan_local_maximum
  · intro x
    constructor
    · intro h
      have he := (identitySubFourArctan_derivative_signs x).2.2.mp
        (fermat isOpen_univ (Or.inl h) (identitySubFourArctan_hasDerivAt x).differentiableAt)
      rcases he with he | he
      · subst x; exact False.elim (identitySubFourArctan_not_minimum_at_negative h)
      · exact he
    · rintro rfl; exact identitySubFourArctan_local_minimum

theorem identitySubFourArctan_source_two (a b : ℝ) : DifferentiableToOrderOn 2 identitySubFourArctan (Ioo a b) :=
  source_two_of_pointwise (D := univ) (subset_univ _)
    (fun x _ ↦ (identitySubFourArctan_hasDerivAt x).differentiableAt)
    (fun x _ ↦ (identitySubFourArctan_second_hasDerivAt x).differentiableAt)

theorem identitySubFourArctan_convexity :
    ConcaveOn ℝ (Iic (0 : ℝ)) identitySubFourArctan ∧ ConvexOn ℝ (Ici (0 : ℝ)) identitySubFourArctan := by
  refine ⟨concaveOn_of_deriv2_nonpos' (convex_Iic _)
    (fun x _ ↦ (identitySubFourArctan_hasDerivAt x).differentiableAt.differentiableWithinAt)
    (fun x _ ↦ (identitySubFourArctan_second_hasDerivAt x).differentiableAt.differentiableWithinAt) ?_,
    convexOn_of_deriv2_nonneg' (convex_Ici _)
      (fun x _ ↦ (identitySubFourArctan_hasDerivAt x).differentiableAt.differentiableWithinAt)
      (fun x _ ↦ (identitySubFourArctan_second_hasDerivAt x).differentiableAt.differentiableWithinAt) ?_⟩
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, identitySubFourArctan_second_deriv,
      identitySubFourArctanSecondDeriv] using (div_nonpos_of_nonpos_of_nonneg
        (show 8 * x ≤ 0 by linarith [mem_Iic.mp hx]) (sq_nonneg (1 + x ^ 2)))
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, identitySubFourArctan_second_deriv,
      identitySubFourArctanSecondDeriv] using (div_nonneg (show 0 ≤ 8 * x by linarith [mem_Ici.mp hx]) (sq_nonneg (1 + x ^ 2)))

theorem identitySubFourArctan_inflection_zero : SourceInflectionOn identitySubFourArctan (-1) 1 0 := by
  have h := sourceInflectionOn_of_second_deriv_neg_pos (f := identitySubFourArctan) (x₀ := 0) (δ := 1)
    (by norm_num) (identitySubFourArctan_source_two _ _) (identitySubFourArctan_source_two _ _)
    (Or.inl (identitySubFourArctan_hasDerivAt 0).differentiableAt)
    (fun x hx ↦ (identitySubFourArctan_second_signs x).1.mpr hx.2)
    (fun x hx ↦ (identitySubFourArctan_second_signs x).2.1.mpr hx.1)
  norm_num at h ⊢
  exact h

theorem identitySubFourArctan_inflection_iff (x : ℝ) :
    (∃ a b : ℝ, SourceInflectionOn identitySubFourArctan a b x) ↔ x = 0 := by
  constructor
  · rintro ⟨a, b, hu⟩
    exact (identitySubFourArctan_second_signs x).2.2.mp
      (second_zero_of_sourceInflection (D := univ) (subset_univ _)
        (fun y _ ↦ (identitySubFourArctan_hasDerivAt y).differentiableAt)
        (fun y _ ↦ (identitySubFourArctan_second_hasDerivAt y).differentiableAt)
        identitySubFourArctan_second_continuous.continuousAt hu)
  · rintro rfl; exact ⟨-1, 1, identitySubFourArctan_inflection_zero⟩

theorem identitySubFourArctan_affine_residual_top :
    Tendsto (fun x : ℝ ↦ identitySubFourArctan x - (x - 2 * Real.pi)) atTop (𝓝 0) := by
  have h := (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).const_mul (-4)
  have hh := h.add_const (2 * Real.pi)
  have hz : -4 * (Real.pi / 2) + 2 * Real.pi = 0 := by ring
  rw [hz] at hh
  exact hh.congr fun x ↦ by unfold identitySubFourArctan; ring

theorem identitySubFourArctan_affine_residual_bot :
    Tendsto (fun x : ℝ ↦ identitySubFourArctan x - (x + 2 * Real.pi)) atBot (𝓝 0) := by
  have h := (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).const_mul (-4)
  have hh := h.add_const (-2 * Real.pi)
  have hz : -4 * (-(Real.pi / 2)) + (-2 * Real.pi) = 0 := by ring
  rw [hz] at hh
  exact hh.congr fun x ↦ by unfold identitySubFourArctan; ring

theorem identitySubFourArctan_limits : Tendsto identitySubFourArctan atTop atTop ∧ Tendsto identitySubFourArctan atBot atBot := by
  constructor
  · have h := (tendsto_id : Tendsto (fun x : ℝ ↦ x) atTop atTop).atTop_add
      ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).const_mul (-4))
    exact h.congr fun x ↦ by unfold identitySubFourArctan; simp only [id_eq]; ring
  · have h := (tendsto_id : Tendsto (fun x : ℝ ↦ x) atBot atBot).atBot_add
      ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).const_mul (-4))
    exact h.congr fun x ↦ by unfold identitySubFourArctan; simp only [id_eq]; ring

theorem identitySubFourArctan_affine_parameters_top (m b : ℝ) :
    Tendsto (fun x : ℝ ↦ identitySubFourArctan x - (m * x + b)) atTop (𝓝 0) ↔
      m = 1 ∧ b = -2 * Real.pi := by
  apply affine_parameters_iff tendsto_inv_atTop_zero
    ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne')
  simpa only [one_mul, sub_eq_add_neg, neg_mul] using identitySubFourArctan_affine_residual_top

theorem identitySubFourArctan_affine_parameters_bot (m b : ℝ) :
    Tendsto (fun x : ℝ ↦ identitySubFourArctan x - (m * x + b)) atBot (𝓝 0) ↔
      m = 1 ∧ b = 2 * Real.pi := by
  apply affine_parameters_iff tendsto_inv_atBot_zero
    ((eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne)
  simpa only [one_mul] using identitySubFourArctan_affine_residual_bot

theorem identitySubFourArctan_asymptotes :
    (∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt identitySubFourArctan univ a) ∧
      (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin identitySubFourArctan univ b) ∧
      (∀ m b : ℝ, HasObliqueAsymptoteWithin identitySubFourArctan univ m b ↔
        m = 1 ∧ (b = -2 * Real.pi ∨ b = 2 * Real.pi)) := by
  have hT : ∀ᶠ x : ℝ in atTop, x ∈ (univ : Set ℝ) := Eventually.of_forall mem_univ
  have hB : ∀ᶠ x : ℝ in atBot, x ∈ (univ : Set ℝ) := Eventually.of_forall mem_univ
  refine ⟨fun a ↦ no_vertical_of_continuousAt (identitySubFourArctan_hasDerivAt a).continuousAt, ?_, ?_⟩
  · intro b
    rw [full_tail_horizontal_iff hT hB, HasHorizontalAsymptote]
    rintro (h | h)
    · exact not_tendsto_atTop_of_tendsto_nhds h identitySubFourArctan_limits.1
    · exact not_tendsto_atBot_of_tendsto_nhds h identitySubFourArctan_limits.2
  · intro m b
    rw [full_tail_oblique_iff hT hB, HasObliqueAsymptote,
      identitySubFourArctan_affine_parameters_top, identitySubFourArctan_affine_parameters_bot]
    constructor
    · rintro ⟨_, ⟨hm, hb⟩ | ⟨hm, hb⟩⟩
      · exact ⟨hm, Or.inl hb⟩
      · exact ⟨hm, Or.inr hb⟩
    · rintro ⟨rfl, hb | hb⟩
      · exact ⟨by norm_num, Or.inl ⟨rfl, hb⟩⟩
      · exact ⟨by norm_num, Or.inr ⟨rfl, hb⟩⟩

theorem identitySubFourArctan_asymptote_sides (x : ℝ) :
    x - 2 * Real.pi < identitySubFourArctan x ∧ identitySubFourArctan x < x + 2 * Real.pi := by
  have hu := Real.arctan_lt_pi_div_two x
  have hl := Real.neg_pi_div_two_lt_arctan x
  unfold identitySubFourArctan
  constructor <;> linarith


theorem identitySubFourArctan_positive_root :
    ∃ ρ : ℝ, identitySubFourArctanPositiveCriticalAbscissa < ρ ∧ ρ < 2 * Real.pi ∧ identitySubFourArctan ρ = 0 ∧
      ∀ x : ℝ, 0 < x → (identitySubFourArctan x = 0 ↔ x = ρ) := by
  have hr := identitySubFourArctanPositiveCriticalAbscissa_bounds.1
  have hr2 : identitySubFourArctanPositiveCriticalAbscissa < 2 * Real.pi := by
    linarith [identitySubFourArctanPositiveCriticalAbscissa_bounds.2.2, Real.two_le_pi]
  have hzero := identitySubFourArctan_values.1
  have hleft : identitySubFourArctan identitySubFourArctanPositiveCriticalAbscissa < 0 := by
    have h := identitySubFourArctan_variation.2.1
      (show (0 : ℝ) ∈ Icc (-identitySubFourArctanPositiveCriticalAbscissa) identitySubFourArctanPositiveCriticalAbscissa by constructor <;> linarith)
      ⟨by linarith, le_refl _⟩ hr
    simpa only [hzero] using h
  have hright : 0 < identitySubFourArctan (2 * Real.pi) := by
    unfold identitySubFourArctan
    linarith [Real.arctan_lt_pi_div_two (2 * Real.pi)]
  have him : (0 : ℝ) ∈ identitySubFourArctan '' Icc identitySubFourArctanPositiveCriticalAbscissa (2 * Real.pi) :=
    intermediate_value_Icc hr2.le identitySubFourArctan_continuous.continuousOn ⟨hleft.le, hright.le⟩
  rcases him with ⟨ρ, hρ, hval⟩
  have hρlower : identitySubFourArctanPositiveCriticalAbscissa < ρ := by
    refine lt_of_le_of_ne hρ.1 ?_
    intro he
    have hz : identitySubFourArctan identitySubFourArctanPositiveCriticalAbscissa = 0 := by simpa only [he] using hval
    exact hleft.ne hz
  have hρupper : ρ < 2 * Real.pi := by
    refine lt_of_le_of_ne hρ.2 ?_
    intro he
    have hz : identitySubFourArctan (2 * Real.pi) = 0 := by simpa only [he] using hval
    exact hright.ne' hz
  refine ⟨ρ, hρlower, hρupper, hval, ?_⟩
  intro x hx
  constructor
  · intro hv
    by_cases hxr : x ≤ identitySubFourArctanPositiveCriticalAbscissa
    · have h := identitySubFourArctan_variation.2.1
        (show (0 : ℝ) ∈ Icc (-identitySubFourArctanPositiveCriticalAbscissa) identitySubFourArctanPositiveCriticalAbscissa by constructor <;> linarith)
        ⟨by linarith, hxr⟩ hx
      rw [hzero, hv] at h
      exact False.elim (lt_irrefl _ h)
    · exact identitySubFourArctan_variation.2.2.injOn (mem_Ici.mpr (lt_of_not_ge hxr).le) (mem_Ici.mpr hρ.1) (hv.trans hval.symm)
  · rintro rfl; exact hval


theorem identitySubFourArctan_all_zeros :
    ∃ ρ : ℝ, identitySubFourArctanPositiveCriticalAbscissa < ρ ∧ ρ < 2 * Real.pi ∧
      (∀ x : ℝ, identitySubFourArctan x = 0 ↔ x = -ρ ∨ x = 0 ∨ x = ρ) ∧
      (∀ σ : ℝ, 0 < σ → identitySubFourArctan σ = 0 → σ = ρ) := by
  rcases identitySubFourArctan_positive_root with ⟨ρ, hρl, hρu, hρv, hunique⟩
  refine ⟨ρ, hρl, hρu, ?_, fun σ hσ hv ↦ (hunique σ hσ).mp hv⟩
  intro x
  constructor
  · intro hv
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have hn : identitySubFourArctan (-x) = 0 := by rw [identitySubFourArctan_odd, hv]; simp
      have he := (hunique (-x) (by linarith)).mp hn
      exact Or.inl (by linarith)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr ((hunique x hx).mp hv))
  · rintro (rfl | rfl | rfl)
    · rw [identitySubFourArctan_odd, hρv]; simp
    · exact identitySubFourArctan_values.1
    · exact hρv

theorem identitySubFourArctan_range (y : ℝ) : ∃ x : ℝ, identitySubFourArctan x = y := by
  obtain ⟨a, ha, hay⟩ := ((eventually_lt_atBot (0 : ℝ)).and
    (identitySubFourArctan_limits.2.eventually (eventually_lt_atBot y))).exists
  obtain ⟨b, hb, hby⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (identitySubFourArctan_limits.1.eventually (eventually_gt_atTop y))).exists
  have him := intermediate_value_Icc (show a ≤ b by linarith) identitySubFourArctan_continuous.continuousOn
    (show y ∈ Icc (identitySubFourArctan a) (identitySubFourArctan b) from ⟨hay.le, hby.le⟩)
  rcases him with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

theorem identitySubFourArctan_graph_iff (x y : ℝ) :
    identitySubFourArctan x = y ↔ y = x - 4 * Real.arctan x := by unfold identitySubFourArctan; exact eq_comm

/-- Bài 14(f): khảo sát `x − 4 arctan x` trên ℝ. -/
theorem source_arctan_function_investigation :
    (∀ x : ℝ, HasDerivAt identitySubFourArctan ((x ^ 2 - 3) / (1 + x ^ 2)) x ∧
      HasDerivAt (deriv identitySubFourArctan) (8 * x / (1 + x ^ 2) ^ 2) x) ∧
      (∀ x : ℝ,
        (deriv identitySubFourArctan x < 0 ↔ -identitySubFourArctanPositiveCriticalAbscissa < x ∧ x < identitySubFourArctanPositiveCriticalAbscissa) ∧
        (0 < deriv identitySubFourArctan x ↔ x < -identitySubFourArctanPositiveCriticalAbscissa ∨ identitySubFourArctanPositiveCriticalAbscissa < x) ∧
        (deriv identitySubFourArctan x = 0 ↔ x = -identitySubFourArctanPositiveCriticalAbscissa ∨ x = identitySubFourArctanPositiveCriticalAbscissa)) ∧
      (StrictMonoOn identitySubFourArctan (Iic (-identitySubFourArctanPositiveCriticalAbscissa)) ∧
        StrictAntiOn identitySubFourArctan (Icc (-identitySubFourArctanPositiveCriticalAbscissa) identitySubFourArctanPositiveCriticalAbscissa) ∧
        StrictMonoOn identitySubFourArctan (Ici identitySubFourArctanPositiveCriticalAbscissa)) ∧
      ((∀ x : ℝ, IsLocalMaximumOn identitySubFourArctan univ x ↔ x = -identitySubFourArctanPositiveCriticalAbscissa) ∧
        ∀ x : ℝ, IsLocalMinimumOn identitySubFourArctan univ x ↔ x = identitySubFourArctanPositiveCriticalAbscissa) ∧
      (identitySubFourArctan 0 = 0 ∧
        identitySubFourArctan (-identitySubFourArctanPositiveCriticalAbscissa) = 4 * Real.pi / 3 - identitySubFourArctanPositiveCriticalAbscissa ∧
        identitySubFourArctan identitySubFourArctanPositiveCriticalAbscissa = identitySubFourArctanPositiveCriticalAbscissa - 4 * Real.pi / 3 ∧
        deriv identitySubFourArctan 0 = -3) ∧
      (ConcaveOn ℝ (Iic (0 : ℝ)) identitySubFourArctan ∧ ConvexOn ℝ (Ici (0 : ℝ)) identitySubFourArctan) ∧
      (∀ x : ℝ, (∃ a b : ℝ, SourceInflectionOn identitySubFourArctan a b x) ↔ x = 0) ∧
      (∀ x : ℝ, identitySubFourArctan (-x) = -identitySubFourArctan x) ∧
      (Tendsto identitySubFourArctan atTop atTop ∧ Tendsto identitySubFourArctan atBot atBot) ∧
      (Tendsto (fun x : ℝ ↦ identitySubFourArctan x - (x - 2 * Real.pi)) atTop (𝓝 0) ∧
        Tendsto (fun x : ℝ ↦ identitySubFourArctan x - (x + 2 * Real.pi)) atBot (𝓝 0)) ∧
      ((∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt identitySubFourArctan univ a) ∧
        (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin identitySubFourArctan univ b) ∧
        ∀ m b : ℝ, HasObliqueAsymptoteWithin identitySubFourArctan univ m b ↔
          m = 1 ∧ (b = -2 * Real.pi ∨ b = 2 * Real.pi)) ∧
      (∀ x : ℝ, x - 2 * Real.pi < identitySubFourArctan x ∧ identitySubFourArctan x < x + 2 * Real.pi) ∧
      (∃ ρ : ℝ, identitySubFourArctanPositiveCriticalAbscissa < ρ ∧ ρ < 2 * Real.pi ∧
        (∀ x : ℝ, identitySubFourArctan x = 0 ↔ x = -ρ ∨ x = 0 ∨ x = ρ) ∧
        ∀ σ : ℝ, 0 < σ → identitySubFourArctan σ = 0 → σ = ρ) ∧
      (∀ y : ℝ, ∃ x : ℝ, identitySubFourArctan x = y) ∧
      (∀ x y : ℝ, identitySubFourArctan x = y ↔ y = x - 4 * Real.arctan x) :=
  ⟨fun x ↦ ⟨identitySubFourArctan_hasDerivAt x, identitySubFourArctan_second_hasDerivAt x⟩,
    identitySubFourArctan_derivative_signs, identitySubFourArctan_variation, identitySubFourArctan_extrema, identitySubFourArctan_values,
    identitySubFourArctan_convexity, identitySubFourArctan_inflection_iff, identitySubFourArctan_odd, identitySubFourArctan_limits,
    ⟨identitySubFourArctan_affine_residual_top, identitySubFourArctan_affine_residual_bot⟩,
    identitySubFourArctan_asymptotes, identitySubFourArctan_asymptote_sides, identitySubFourArctan_all_zeros,
    identitySubFourArctan_range, identitySubFourArctan_graph_iff⟩

end calculus.Chapter04.Section04ArctanFunctionInvestigationExercise
