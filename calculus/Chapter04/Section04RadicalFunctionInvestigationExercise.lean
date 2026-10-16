import calculus.Chapter04.Section04RationalFunctionInvestigationSupport
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bài 4.4.14(e): khảo sát x²/√(x+1)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2758–2765. Xét `x > −1`; phương trình đồ thị giữ `y ≥ 0` sau bình phương.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04RadicalFunctionInvestigationExercise
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03
open calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04RationalFunctionInvestigationSupport
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport

def squareDivSqrtAddOne (x : ℝ) : ℝ := x ^ 2 / Real.sqrt (x + 1)

def squareDivSqrtAddOneDomain : Set ℝ := Ioi (-1)

def squareDivSqrtAddOneFirstDeriv (x : ℝ) : ℝ :=
  x * (3 * x + 4) / (2 * (x + 1) * Real.sqrt (x + 1))

def squareDivSqrtAddOneSecondDeriv (x : ℝ) : ℝ :=
  (3 * x ^ 2 + 8 * x + 8) / (4 * (x + 1) ^ 2 * Real.sqrt (x + 1))

theorem squareDivSqrtAddOne_domain_iff (x : ℝ) :
    x ∈ squareDivSqrtAddOneDomain ↔ 0 ≤ x + 1 ∧ Real.sqrt (x + 1) ≠ 0 := by
  change -1 < x ↔ _
  constructor
  · intro hx
    have hd : 0 < x + 1 := by linarith
    exact ⟨hd.le, (Real.sqrt_pos_of_pos hd).ne'⟩
  · rintro ⟨hd, hr⟩
    have hp : 0 < Real.sqrt (x + 1) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
    have hdpos := Real.sqrt_pos.mp hp
    linarith

theorem squareDivSqrtAddOne_domain_open : IsOpen squareDivSqrtAddOneDomain := isOpen_Ioi

theorem squareDivSqrtAddOne_sqrt_hasDerivAt {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    HasDerivAt (fun y : ℝ ↦ Real.sqrt (y + 1)) (1 / (2 * Real.sqrt (x + 1))) x := by
  have hd : 0 < x + 1 := by change -1 < x at hx; linarith
  simpa only [Function.comp_def, id_eq, mul_one] using!
    (Real.hasDerivAt_sqrt hd.ne').comp x ((hasDerivAt_id x).add_const 1)

theorem squareDivSqrtAddOne_hasDerivAt {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    HasDerivAt squareDivSqrtAddOne (squareDivSqrtAddOneFirstDeriv x) x := by
  have hd : 0 < x + 1 := by change -1 < x at hx; linarith
  have hr : 0 < Real.sqrt (x + 1) := Real.sqrt_pos_of_pos hd
  have h := ((hasDerivAt_id x).fun_pow 2).div (squareDivSqrtAddOne_sqrt_hasDerivAt hx) hr.ne'
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  apply h.congr_deriv
  unfold squareDivSqrtAddOneFirstDeriv
  rw [Real.sq_sqrt hd.le]
  field_simp [hd.ne', hr.ne']
  have hsquare := Real.sq_sqrt hd.le
  generalize Real.sqrt (x + 1) = s at hsquare ⊢
  have hxexpr : x = s ^ 2 - 1 := by linarith
  rw [hxexpr]
  ring

theorem squareDivSqrtAddOne_denominator_hasDerivAt {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    HasDerivAt (fun y : ℝ ↦ 2 * (y + 1) * Real.sqrt (y + 1))
      (3 * Real.sqrt (x + 1)) x := by
  have hd : 0 < x + 1 := by change -1 < x at hx; linarith
  have hr := Real.sqrt_pos_of_pos hd
  have h := (((hasDerivAt_id x).add_const 1).const_mul 2).fun_mul
    (squareDivSqrtAddOne_sqrt_hasDerivAt hx)
  apply h.congr_deriv
  simp only [id_eq, mul_one]
  field_simp [hr.ne']
  nlinarith [Real.sq_sqrt hd.le]

theorem squareDivSqrtAddOneFirstDeriv_hasDerivAt {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    HasDerivAt squareDivSqrtAddOneFirstDeriv (squareDivSqrtAddOneSecondDeriv x) x := by
  have hd : 0 < x + 1 := by change -1 < x at hx; linarith
  have hr := Real.sqrt_pos_of_pos hd
  have hn : HasDerivAt (fun y : ℝ ↦ y * (3 * y + 4)) (6 * x + 4) x := by
    have h := (hasDerivAt_id x).fun_mul (((hasDerivAt_id x).const_mul 3).add_const 4)
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring
  have h := hn.div (squareDivSqrtAddOne_denominator_hasDerivAt hx)
    (show 2 * (x + 1) * Real.sqrt (x + 1) ≠ 0 by positivity)
  apply h.congr_deriv
  unfold squareDivSqrtAddOneSecondDeriv
  rw [mul_pow, mul_pow, Real.sq_sqrt hd.le]
  field_simp [hd.ne', hr.ne']
  have hsquare := Real.sq_sqrt hd.le
  generalize Real.sqrt (x + 1) = s at hsquare ⊢
  have hxexpr : x = s ^ 2 - 1 := by linarith
  rw [hxexpr]
  ring

theorem squareDivSqrtAddOne_second_hasDerivAt {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    HasDerivAt (deriv squareDivSqrtAddOne) (squareDivSqrtAddOneSecondDeriv x) x :=
  hasDerivAt_deriv_of_open_formula squareDivSqrtAddOne_domain_open hx
    (fun _ hy ↦ squareDivSqrtAddOne_hasDerivAt hy) (squareDivSqrtAddOneFirstDeriv_hasDerivAt hx)

theorem squareDivSqrtAddOne_deriv {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    deriv squareDivSqrtAddOne x = squareDivSqrtAddOneFirstDeriv x := (squareDivSqrtAddOne_hasDerivAt hx).deriv

theorem squareDivSqrtAddOne_second_deriv {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    deriv (deriv squareDivSqrtAddOne) x = squareDivSqrtAddOneSecondDeriv x := (squareDivSqrtAddOne_second_hasDerivAt hx).deriv

theorem squareDivSqrtAddOne_second_continuousAt {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    ContinuousAt (deriv (deriv squareDivSqrtAddOne)) x := by
  have hd : 0 < x + 1 := by change -1 < x at hx; linarith
  have hr := Real.sqrt_pos_of_pos hd
  have hc : ContinuousAt squareDivSqrtAddOneSecondDeriv x := by
    unfold squareDivSqrtAddOneSecondDeriv
    fun_prop (disch := positivity)
  apply hc.congr_of_eventuallyEq
  filter_upwards [squareDivSqrtAddOne_domain_open.mem_nhds hx] with y hy
  exact squareDivSqrtAddOne_second_deriv hy

theorem squareDivSqrtAddOne_derivative_signs {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    (deriv squareDivSqrtAddOne x < 0 ↔ x < 0) ∧ (0 < deriv squareDivSqrtAddOne x ↔ 0 < x) ∧
      (deriv squareDivSqrtAddOne x = 0 ↔ x = 0) := by
  have hd : 0 < x + 1 := by change -1 < x at hx; linarith
  have hp : 0 < 3 * x + 4 := by linarith
  have hb : 0 < 2 * (x + 1) * Real.sqrt (x + 1) := by positivity
  rw [squareDivSqrtAddOne_deriv hx]
  unfold squareDivSqrtAddOneFirstDeriv
  constructor
  · rw [div_lt_iff₀ hb]
    simpa only [zero_mul] using (mul_lt_mul_iff_of_pos_right hp : x * (3 * x + 4) < 0 * (3 * x + 4) ↔ x < 0)
  constructor
  · rw [lt_div_iff₀ hb]
    simpa only [zero_mul] using (mul_lt_mul_iff_of_pos_right hp : 0 * (3 * x + 4) < x * (3 * x + 4) ↔ 0 < x)
  · rw [div_eq_zero_iff, mul_eq_zero]
    simp only [hp.ne', hb.ne', or_false]

theorem squareDivSqrtAddOne_second_positive {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    0 < deriv (deriv squareDivSqrtAddOne) x := by
  have hd : 0 < x + 1 := by change -1 < x at hx; linarith
  rw [squareDivSqrtAddOne_second_deriv hx]
  unfold squareDivSqrtAddOneSecondDeriv
  apply div_pos
  · nlinarith [sq_nonneg (x + 4 / 3)]
  · positivity

theorem squareDivSqrtAddOne_variation :
    StrictAntiOn squareDivSqrtAddOne (Ioc (-1 : ℝ) 0) ∧ StrictMonoOn squareDivSqrtAddOne (Ici (0 : ℝ)) := by
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
      (fun x hx ↦ (squareDivSqrtAddOne_hasDerivAt hx.1).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ioc] at hx
    exact (squareDivSqrtAddOne_derivative_signs hx.1).1.mpr hx.2
  · apply strictMonoOn_of_deriv_pos (convex_Ici _)
      (fun x hx ↦ (squareDivSqrtAddOne_hasDerivAt (by change -1 < x; linarith [mem_Ici.mp hx])).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    exact (squareDivSqrtAddOne_derivative_signs (by change -1 < x; linarith [mem_Ioi.mp hx])).2.1.mpr hx

theorem squareDivSqrtAddOne_zero : squareDivSqrtAddOne 0 = 0 := by simp [squareDivSqrtAddOne]

theorem squareDivSqrtAddOne_nonneg (x : ℝ) : 0 ≤ squareDivSqrtAddOne x :=
  div_nonneg (sq_nonneg x) (Real.sqrt_nonneg _)

theorem squareDivSqrtAddOne_zero_iff {x : ℝ} (hx : x ∈ squareDivSqrtAddOneDomain) :
    squareDivSqrtAddOne x = 0 ↔ x = 0 := by
  have hr := ((squareDivSqrtAddOne_domain_iff x).mp hx).2
  simp only [squareDivSqrtAddOne, div_eq_zero_iff, hr, or_false, sq_eq_zero_iff]

theorem squareDivSqrtAddOne_extrema :
    (∀ x : ℝ, IsLocalMinimumOn squareDivSqrtAddOne squareDivSqrtAddOneDomain x ↔ x = 0) ∧
      (∀ x : ℝ, ¬ IsLocalMaximumOn squareDivSqrtAddOne squareDivSqrtAddOneDomain x) := by
  have hmin : IsLocalMinimumOn squareDivSqrtAddOne squareDivSqrtAddOneDomain 0 := by
    refine ⟨by norm_num [squareDivSqrtAddOneDomain], 1, by norm_num, ?_⟩
    intro x _
    rw [squareDivSqrtAddOne_zero]
    exact squareDivSqrtAddOne_nonneg x
  have hnmax : ¬ IsLocalMaximumOn squareDivSqrtAddOne squareDivSqrtAddOneDomain 0 := by
    apply no_local_maximum_of_right_increase (b := 1) (by norm_num)
    · intro x hx; change -1 < x; linarith [hx.1]
    · intro x hx
      exact squareDivSqrtAddOne_variation.2 (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hx.1.le) hx.1
  constructor
  · intro x
    constructor
    · intro h
      exact (squareDivSqrtAddOne_derivative_signs h.1).2.2.mp
        (fermat squareDivSqrtAddOne_domain_open (Or.inl h) (squareDivSqrtAddOne_hasDerivAt h.1).differentiableAt)
    · rintro rfl; exact hmin
  · intro x h
    have he := (squareDivSqrtAddOne_derivative_signs h.1).2.2.mp
      (fermat squareDivSqrtAddOne_domain_open (Or.inr h) (squareDivSqrtAddOne_hasDerivAt h.1).differentiableAt)
    subst x
    exact hnmax h

theorem squareDivSqrtAddOne_convex : ConvexOn ℝ squareDivSqrtAddOneDomain squareDivSqrtAddOne := by
  apply convexOn_of_deriv2_nonneg' (convex_Ioi _)
    (fun x hx ↦ (squareDivSqrtAddOne_hasDerivAt hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (squareDivSqrtAddOne_second_hasDerivAt hx).differentiableAt.differentiableWithinAt)
  intro x hx
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
    (squareDivSqrtAddOne_second_positive hx).le

theorem squareDivSqrtAddOne_no_inflection (a b c : ℝ) (hI : Ioo a b ⊆ squareDivSqrtAddOneDomain) :
    ¬ SourceInflectionOn squareDivSqrtAddOne a b c := by
  intro hu
  have hz := second_zero_of_sourceInflection hI
    (fun _ hx ↦ (squareDivSqrtAddOne_hasDerivAt hx).differentiableAt)
    (fun _ hx ↦ (squareDivSqrtAddOne_second_hasDerivAt hx).differentiableAt)
    (squareDivSqrtAddOne_second_continuousAt (hI hu.1)) hu
  exact (squareDivSqrtAddOne_second_positive (hI hu.1)).ne' hz

theorem squareDivSqrtAddOne_boundary_limit : Tendsto squareDivSqrtAddOne (𝓝[>] (-1 : ℝ)) atTop := by
  have hi : Tendsto (fun x : ℝ ↦ x) (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (x + 1)) (𝓝[>] (-1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using! Real.continuous_sqrt.continuousAt.tendsto.comp (hi.add_const 1), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x (hx : -1 < x)
    exact Real.sqrt_pos_of_pos (by linarith)
  have hn : Tendsto (fun x : ℝ ↦ x ^ 2) (𝓝[>] (-1 : ℝ)) (𝓝 (1 : ℝ)) := by simpa using hi.pow 2
  have h := (tendsto_inv_nhdsGT_zero.comp hs).atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hn
  exact h.congr fun x ↦ by dsimp [Function.comp_def, squareDivSqrtAddOne]; ring

theorem squareDivSqrtAddOne_domain_tail_top : ∀ᶠ x : ℝ in atTop, x ∈ squareDivSqrtAddOneDomain :=
  eventually_gt_atTop (-1 : ℝ)


theorem squareDivSqrtAddOne_domain_tail_bot_empty : atBot ⊓ 𝓟 squareDivSqrtAddOneDomain = ⊥ := by
  apply inf_principal_eq_bot.mpr
  filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
  change ¬ -1 < x
  exact not_lt.mpr hx.le

theorem squareDivSqrtAddOne_ratio_top : Tendsto (fun x : ℝ ↦ squareDivSqrtAddOne x / x) atTop atTop := by
  have harg : Tendsto (fun x : ℝ ↦ x + 1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hi : Tendsto (fun x : ℝ ↦ (x + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp harg
  have hg : Tendsto (fun x : ℝ ↦ x ^ 2 / (x + 1)) atTop atTop := by
    have h := (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id).atTop_add hi
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hd : x + 1 ≠ 0 := by linarith
    simp only [id_eq]
    field_simp [hd]
    ring
  have h := Real.tendsto_sqrt_atTop.comp hg
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hd : 0 < x + 1 := by linarith
  have hr := Real.sqrt_pos_of_pos hd
  dsimp only [Function.comp_def]
  rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
  unfold squareDivSqrtAddOne
  field_simp [hx.ne', hr.ne']

theorem squareDivSqrtAddOne_limit_top : Tendsto squareDivSqrtAddOne atTop atTop := by
  have h := squareDivSqrtAddOne_ratio_top.atTop_mul_atTop₀ (tendsto_id : Tendsto (fun x : ℝ ↦ x) atTop atTop)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact div_mul_cancel₀ _ hx.ne'

theorem squareDivSqrtAddOne_continuousAt_outside {a : ℝ} (ha : a < -1) : ContinuousAt squareDivSqrtAddOne a := by
  apply (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) a).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ha] with x (hx : x < -1)
  simp only [squareDivSqrtAddOne, Real.sqrt_eq_zero_of_nonpos (by linarith : x + 1 ≤ 0), div_zero]

theorem squareDivSqrtAddOne_asymptotes :
    (∀ a : ℝ, HasVerticalAsymptoteWithinAt squareDivSqrtAddOne squareDivSqrtAddOneDomain a ↔ a = -1) ∧
      (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin squareDivSqrtAddOne squareDivSqrtAddOneDomain b) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin squareDivSqrtAddOne squareDivSqrtAddOneDomain m b) := by
  have ht : atTop ⊓ 𝓟 squareDivSqrtAddOneDomain = atTop :=
    inf_eq_left.mpr (le_principal_iff.mpr squareDivSqrtAddOne_domain_tail_top)
  constructor
  · intro a
    constructor
    · intro h
      by_contra hn
      rcases lt_or_gt_of_ne hn with hl | hr
      · exact no_vertical_of_continuousAt (squareDivSqrtAddOne_continuousAt_outside hl) h
      · exact no_vertical_of_continuousAt (squareDivSqrtAddOne_hasDerivAt hr).continuousAt h
    · rintro rfl
      apply vertical_of_right_top _ squareDivSqrtAddOne_boundary_limit
      exact self_mem_nhdsWithin
  constructor
  · intro b h
    rw [hasHorizontalAsymptoteWithin_iff, ht, squareDivSqrtAddOne_domain_tail_bot_empty] at h
    rcases h with h | h
    · exact not_tendsto_atTop_of_tendsto_nhds h.2 squareDivSqrtAddOne_limit_top
    · exact h.1.ne rfl
  · intro m b h
    rw [hasObliqueAsymptoteWithin_filter_iff, ht, squareDivSqrtAddOne_domain_tail_bot_empty] at h
    rcases h.2 with h | h
    · have hq := ((affine_residual_limit_iff tendsto_inv_atTop_zero
        ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne') squareDivSqrtAddOne m b).mp h.2).1
      exact not_tendsto_atTop_of_tendsto_nhds hq squareDivSqrtAddOne_ratio_top
    · exact h.1.ne rfl

theorem squareDivSqrtAddOne_graph_iff (x y : ℝ) :
    (x ∈ squareDivSqrtAddOneDomain ∧ squareDivSqrtAddOne x = y) ↔
      -1 < x ∧ 0 ≤ y ∧ (x + 1) * y ^ 2 = x ^ 4 := by
  constructor
  · rintro ⟨hx, hy⟩
    have hd : 0 < x + 1 := by change -1 < x at hx; linarith
    have hr := Real.sqrt_pos_of_pos hd
    have he : x ^ 2 = y * Real.sqrt (x + 1) := (div_eq_iff hr.ne').mp hy
    refine ⟨hx, by rw [← hy]; exact squareDivSqrtAddOne_nonneg x, ?_⟩
    have hs := congrArg (fun t : ℝ ↦ t ^ 2) he
    rw [mul_pow, Real.sq_sqrt hd.le] at hs
    nlinarith [hs]
  · rintro ⟨hx, hy, he⟩
    have hd : 0 < x + 1 := by linarith
    have hr := Real.sqrt_pos_of_pos hd
    have hs : (y * Real.sqrt (x + 1)) ^ 2 = (x ^ 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hd.le]
      nlinarith [he]
    have hv : y * Real.sqrt (x + 1) = x ^ 2 := by
      nlinarith [mul_nonneg hy hr.le, sq_nonneg x]
    exact ⟨hx, (div_eq_iff hr.ne').mpr hv.symm⟩

theorem squareDivSqrtAddOne_range (y : ℝ) :
    (∃ x ∈ squareDivSqrtAddOneDomain, squareDivSqrtAddOne x = y) ↔ 0 ≤ y := by
  constructor
  · rintro ⟨x, _, rfl⟩; exact squareDivSqrtAddOne_nonneg x
  · intro hy
    have hev := (squareDivSqrtAddOne_limit_top.eventually (eventually_gt_atTop y)).and (eventually_gt_atTop (0 : ℝ))
    rcases hev.exists with ⟨b, hb, hbpos⟩
    have hc : ContinuousOn squareDivSqrtAddOne (Icc 0 b) := by
      intro x hx
      exact (squareDivSqrtAddOne_hasDerivAt (by change -1 < x; linarith [hx.1])).continuousAt.continuousWithinAt
    have him : y ∈ squareDivSqrtAddOne '' Icc 0 b := intermediate_value_Icc hbpos.le hc
      ⟨by simpa only [squareDivSqrtAddOne_zero] using hy, hb.le⟩
    rcases him with ⟨x, hx, he⟩
    exact ⟨x, by change -1 < x; linarith [hx.1], he⟩


theorem source_radical_function_investigation :
    (∀ x : ℝ, x ∈ squareDivSqrtAddOneDomain ↔ 0 ≤ x + 1 ∧ Real.sqrt (x + 1) ≠ 0) ∧
      (∀ x ∈ squareDivSqrtAddOneDomain, HasDerivAt squareDivSqrtAddOne (squareDivSqrtAddOneFirstDeriv x) x ∧
        HasDerivAt (deriv squareDivSqrtAddOne) (squareDivSqrtAddOneSecondDeriv x) x) ∧
      (StrictAntiOn squareDivSqrtAddOne (Ioc (-1 : ℝ) 0) ∧ StrictMonoOn squareDivSqrtAddOne (Ici (0 : ℝ))) ∧
      ((∀ x : ℝ, IsLocalMinimumOn squareDivSqrtAddOne squareDivSqrtAddOneDomain x ↔ x = 0) ∧
        ∀ x : ℝ, ¬ IsLocalMaximumOn squareDivSqrtAddOne squareDivSqrtAddOneDomain x) ∧
      squareDivSqrtAddOne 0 = 0 ∧ (∀ x ∈ squareDivSqrtAddOneDomain, squareDivSqrtAddOne x = 0 ↔ x = 0) ∧
      ConvexOn ℝ squareDivSqrtAddOneDomain squareDivSqrtAddOne ∧
      (∀ x ∈ squareDivSqrtAddOneDomain, 0 < deriv (deriv squareDivSqrtAddOne) x) ∧
      (∀ a b c : ℝ, Ioo a b ⊆ squareDivSqrtAddOneDomain → ¬ SourceInflectionOn squareDivSqrtAddOne a b c) ∧
      Tendsto squareDivSqrtAddOne (𝓝[>] (-1 : ℝ)) atTop ∧ Tendsto squareDivSqrtAddOne atTop atTop ∧
      Tendsto (fun x : ℝ ↦ squareDivSqrtAddOne x / x) atTop atTop ∧
      atBot ⊓ 𝓟 squareDivSqrtAddOneDomain = ⊥ ∧
      ((∀ a : ℝ, HasVerticalAsymptoteWithinAt squareDivSqrtAddOne squareDivSqrtAddOneDomain a ↔ a = -1) ∧
        (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin squareDivSqrtAddOne squareDivSqrtAddOneDomain b) ∧
        ∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin squareDivSqrtAddOne squareDivSqrtAddOneDomain m b) ∧
      (∀ x y : ℝ, (x ∈ squareDivSqrtAddOneDomain ∧ squareDivSqrtAddOne x = y) ↔
        -1 < x ∧ 0 ≤ y ∧ (x + 1) * y ^ 2 = x ^ 4) ∧
      (∀ y : ℝ, (∃ x ∈ squareDivSqrtAddOneDomain, squareDivSqrtAddOne x = y) ↔ 0 ≤ y) :=
  ⟨squareDivSqrtAddOne_domain_iff, fun _ hx ↦ ⟨squareDivSqrtAddOne_hasDerivAt hx, squareDivSqrtAddOne_second_hasDerivAt hx⟩,
    squareDivSqrtAddOne_variation, squareDivSqrtAddOne_extrema, squareDivSqrtAddOne_zero, fun _ hx ↦ squareDivSqrtAddOne_zero_iff hx,
    squareDivSqrtAddOne_convex, fun _ hx ↦ squareDivSqrtAddOne_second_positive hx, squareDivSqrtAddOne_no_inflection,
    squareDivSqrtAddOne_boundary_limit, squareDivSqrtAddOne_limit_top, squareDivSqrtAddOne_ratio_top,
    squareDivSqrtAddOne_domain_tail_bot_empty, squareDivSqrtAddOne_asymptotes, squareDivSqrtAddOne_graph_iff, squareDivSqrtAddOne_range⟩

end calculus.Chapter04.Section04RadicalFunctionInvestigationExercise
