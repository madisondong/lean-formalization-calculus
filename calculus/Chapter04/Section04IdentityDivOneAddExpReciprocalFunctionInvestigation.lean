import calculus.Chapter04.Section04RationalFunctionInvestigationSupport
import calculus.Chapter04.Section04AsymptoteClassificationSupport
import calculus.Chapter03.Section07Fundamental
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bài 4.4.14(c): khảo sát x/(1+exp(1/x))

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2758–2763.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04IdentityDivOneAddExpReciprocalFunctionInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03
open calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04RationalFunctionInvestigationSupport
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport


def identityDivOneAddExpReciprocal (x : ℝ) : ℝ := x / (1 + Real.exp (1 / x))

def identityDivOneAddExpReciprocalDomain : Set ℝ := {x | x ≠ 0}

def identityDivOneAddExpReciprocalFirstDeriv (x : ℝ) : ℝ :=
  (1 + Real.exp (1 / x) * (1 + 1 / x)) / (1 + Real.exp (1 / x)) ^ 2

def identityDivOneAddExpReciprocalSecondDeriv (x : ℝ) : ℝ :=
  Real.exp (1 / x) * (Real.exp (1 / x) - 1) /
    (x ^ 3 * (1 + Real.exp (1 / x)) ^ 3)

theorem identityDivOneAddExpReciprocal_denominator_pos (x : ℝ) : 0 < 1 + Real.exp (1 / x) := by
  linarith [Real.exp_pos (1 / x)]

theorem identityDivOneAddExpReciprocal_domain_iff (x : ℝ) :
    x ∈ identityDivOneAddExpReciprocalDomain ↔ x ≠ 0 := Iff.rfl

theorem identityDivOneAddExpReciprocal_domain_open : IsOpen identityDivOneAddExpReciprocalDomain := isOpen_ne

theorem identityDivOneAddExpReciprocal_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt identityDivOneAddExpReciprocal (identityDivOneAddExpReciprocalFirstDeriv x) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ 1 / y) (-1 / x ^ 2) x := by
    simpa only [one_div, neg_div, one_mul] using hasDerivAt_inv hx
  have he := hi.exp
  change HasDerivAt (fun y : ℝ ↦ y / (1 + Real.exp (1 / y)))
    (identityDivOneAddExpReciprocalFirstDeriv x) x
  apply ((hasDerivAt_id x).fun_div (he.const_add 1)
    (identityDivOneAddExpReciprocal_denominator_pos x).ne').congr_deriv
  dsimp only [id_eq, identityDivOneAddExpReciprocalFirstDeriv]
  field_simp [hx, (identityDivOneAddExpReciprocal_denominator_pos x).ne']
  ring

theorem identityDivOneAddExpReciprocalFirstDeriv_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt identityDivOneAddExpReciprocalFirstDeriv (identityDivOneAddExpReciprocalSecondDeriv x) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ 1 / y) (-1 / x ^ 2) x := by
    simpa only [one_div, neg_div, one_mul] using hasDerivAt_inv hx
  have he := hi.exp
  have h := ((he.fun_mul (hi.const_add 1)).const_add 1).div
    ((he.const_add 1).fun_pow 2) (pow_ne_zero 2 (identityDivOneAddExpReciprocal_denominator_pos x).ne')
  apply h.congr_deriv
  dsimp only [identityDivOneAddExpReciprocalSecondDeriv]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, mul_one]
  field_simp [hx, (identityDivOneAddExpReciprocal_denominator_pos x).ne']
  ring

theorem identityDivOneAddExpReciprocal_second_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (deriv identityDivOneAddExpReciprocal) (identityDivOneAddExpReciprocalSecondDeriv x) x :=
  hasDerivAt_deriv_of_open_formula identityDivOneAddExpReciprocal_domain_open hx
    (fun _ hy ↦ identityDivOneAddExpReciprocal_hasDerivAt hy) (identityDivOneAddExpReciprocalFirstDeriv_hasDerivAt hx)

theorem identityDivOneAddExpReciprocal_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv identityDivOneAddExpReciprocal x = identityDivOneAddExpReciprocalFirstDeriv x :=
  (identityDivOneAddExpReciprocal_hasDerivAt hx).deriv

theorem identityDivOneAddExpReciprocal_second_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv identityDivOneAddExpReciprocal) x = identityDivOneAddExpReciprocalSecondDeriv x :=
  (identityDivOneAddExpReciprocal_second_hasDerivAt hx).deriv


theorem identityDivOneAddExpReciprocal_numerator_pos (t : ℝ) : 0 < 1 + Real.exp t * (1 + t) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t - 2)) (Real.exp_pos t).le
  have he : Real.exp (-t - 2) * Real.exp t = Real.exp (-2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  have hlt : Real.exp (-2) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < 0)
  nlinarith [Real.exp_pos t]

theorem identityDivOneAddExpReciprocal_deriv_pos {x : ℝ} (hx : x ≠ 0) :
    0 < deriv identityDivOneAddExpReciprocal x := by
  rw [identityDivOneAddExpReciprocal_deriv hx]
  exact div_pos (identityDivOneAddExpReciprocal_numerator_pos _) (pow_pos (identityDivOneAddExpReciprocal_denominator_pos x) 2)

theorem identityDivOneAddExpReciprocal_second_pos {x : ℝ} (hx : x ≠ 0) :
    0 < deriv (deriv identityDivOneAddExpReciprocal) x := by
  rw [identityDivOneAddExpReciprocal_second_deriv hx]
  unfold identityDivOneAddExpReciprocalSecondDeriv
  have he := Real.exp_pos (1 / x)
  rcases lt_or_gt_of_ne hx with hn | hp
  · have ht : 1 / x < 0 := div_neg_of_pos_of_neg one_pos hn
    have hlt : Real.exp (1 / x) < 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr ht
    have hx3 : x ^ 3 < 0 := by
      rw [pow_succ]
      exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hx) hn
    exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg he (sub_neg.mpr hlt))
      (mul_neg_of_neg_of_pos hx3 (pow_pos (identityDivOneAddExpReciprocal_denominator_pos x) 3))
  · have ht : 0 < 1 / x := div_pos one_pos hp
    have hlt : 1 < Real.exp (1 / x) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr ht
    exact div_pos (mul_pos he (sub_pos.mpr hlt))
      (mul_pos (pow_pos hp 3) (pow_pos (identityDivOneAddExpReciprocal_denominator_pos x) 3))

theorem identityDivOneAddExpReciprocal_variation :
    StrictMonoOn identityDivOneAddExpReciprocal (Iio (0 : ℝ)) ∧
      StrictMonoOn identityDivOneAddExpReciprocal (Ioi (0 : ℝ)) := by
  refine ⟨strictMonoOn_of_domain_derivative (convex_Iio _) ?_
    (fun _ hx ↦ (identityDivOneAddExpReciprocal_hasDerivAt hx).differentiableAt) ?_,
    strictMonoOn_of_domain_derivative (convex_Ioi _) ?_
      (fun _ hx ↦ (identityDivOneAddExpReciprocal_hasDerivAt hx).differentiableAt) ?_⟩
  · intro x hx; exact hx.ne
  · intro x hx; exact identityDivOneAddExpReciprocal_deriv_pos hx.ne
  · intro x hx; exact hx.ne'
  · intro x hx; exact identityDivOneAddExpReciprocal_deriv_pos hx.ne'

theorem identityDivOneAddExpReciprocal_convexity :
    ConvexOn ℝ (Iio (0 : ℝ)) identityDivOneAddExpReciprocal ∧
      ConvexOn ℝ (Ioi (0 : ℝ)) identityDivOneAddExpReciprocal := by
  have hf := fun (x : ℝ) (hx : x ≠ 0) ↦ (identityDivOneAddExpReciprocal_hasDerivAt hx).differentiableAt
  have hg := fun (x : ℝ) (hx : x ≠ 0) ↦ (identityDivOneAddExpReciprocal_second_hasDerivAt hx).differentiableAt
  refine ⟨convexOn_of_deriv2_nonneg' (convex_Iio _)
    (fun x hx ↦ (hf x hx.ne).differentiableWithinAt) (fun x hx ↦ (hg x hx.ne).differentiableWithinAt) ?_,
    convexOn_of_deriv2_nonneg' (convex_Ioi _)
      (fun x hx ↦ (hf x hx.ne').differentiableWithinAt) (fun x hx ↦ (hg x hx.ne').differentiableWithinAt) ?_⟩
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      (identityDivOneAddExpReciprocal_second_pos hx.ne).le
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      (identityDivOneAddExpReciprocal_second_pos hx.ne').le

theorem identityDivOneAddExpReciprocal_no_extrema (x : ℝ) :
    ¬ IsLocalMinimumOn identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain x ∧
      ¬ IsLocalMaximumOn identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain x := by
  constructor <;> intro h
  · exact (identityDivOneAddExpReciprocal_deriv_pos h.1).ne'
      (fermat identityDivOneAddExpReciprocal_domain_open (Or.inl h) (identityDivOneAddExpReciprocal_hasDerivAt h.1).differentiableAt)
  · exact (identityDivOneAddExpReciprocal_deriv_pos h.1).ne'
      (fermat identityDivOneAddExpReciprocal_domain_open (Or.inr h) (identityDivOneAddExpReciprocal_hasDerivAt h.1).differentiableAt)

theorem identityDivOneAddExpReciprocal_second_continuousAt {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (deriv (deriv identityDivOneAddExpReciprocal)) x := by
  have h : ContinuousAt identityDivOneAddExpReciprocalSecondDeriv x := by
    unfold identityDivOneAddExpReciprocalSecondDeriv
    fun_prop (disch := first | exact hx | exact pow_ne_zero 3 hx |
      exact (identityDivOneAddExpReciprocal_denominator_pos x).ne' |
      exact pow_ne_zero 3 (identityDivOneAddExpReciprocal_denominator_pos x).ne' |
      exact mul_ne_zero (pow_ne_zero 3 hx)
        (pow_ne_zero 3 (identityDivOneAddExpReciprocal_denominator_pos x).ne'))
  apply h.congr_of_eventuallyEq
  filter_upwards [identityDivOneAddExpReciprocal_domain_open.mem_nhds hx] with y hy
  exact identityDivOneAddExpReciprocal_second_deriv hy

theorem identityDivOneAddExpReciprocal_no_inflection {a b c : ℝ}
    (hI : Ioo a b ⊆ identityDivOneAddExpReciprocalDomain) :
    ¬ SourceInflectionOn identityDivOneAddExpReciprocal a b c := by
  intro h
  exact (identityDivOneAddExpReciprocal_second_pos (hI h.1)).ne'
    (second_zero_of_sourceInflection hI
      (fun _ hx ↦ (identityDivOneAddExpReciprocal_hasDerivAt hx).differentiableAt)
      (fun _ hx ↦ (identityDivOneAddExpReciprocal_second_hasDerivAt hx).differentiableAt)
      (identityDivOneAddExpReciprocal_second_continuousAt (hI h.1)) h)

theorem identityDivOneAddExpReciprocal_zero : identityDivOneAddExpReciprocal 0 = 0 := by simp [identityDivOneAddExpReciprocal]

theorem identityDivOneAddExpReciprocal_signs (x : ℝ) :
    (0 < identityDivOneAddExpReciprocal x ↔ 0 < x) ∧
      (identityDivOneAddExpReciprocal x < 0 ↔ x < 0) ∧ (identityDivOneAddExpReciprocal x = 0 ↔ x = 0) := by
  unfold identityDivOneAddExpReciprocal
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (identityDivOneAddExpReciprocal_denominator_pos x), zero_mul]
  · rw [div_lt_iff₀ (identityDivOneAddExpReciprocal_denominator_pos x), zero_mul]
  · rw [div_eq_zero_iff]
    exact or_iff_left ((identityDivOneAddExpReciprocal_denominator_pos x).ne')


theorem identityDivOneAddExpReciprocal_abs_bound (x : ℝ) : |identityDivOneAddExpReciprocal x| ≤ |x| := by
  unfold identityDivOneAddExpReciprocal
  rw [abs_div, abs_of_pos (identityDivOneAddExpReciprocal_denominator_pos x)]
  apply (div_le_iff₀ (identityDivOneAddExpReciprocal_denominator_pos x)).mpr
  nlinarith [abs_nonneg x, Real.exp_pos (1 / x)]

theorem identityDivOneAddExpReciprocal_limit_zero : Tendsto identityDivOneAddExpReciprocal (𝓝 (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm (a := fun x : ℝ ↦ |x|)
  · intro x; simpa only [Real.norm_eq_abs] using identityDivOneAddExpReciprocal_abs_bound x
  · simpa only [id_eq, abs_zero] using! (continuousAt_id.tendsto (x := (0 : ℝ))).abs

theorem identityDivOneAddExpReciprocal_continuous : Continuous identityDivOneAddExpReciprocal := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    change Tendsto identityDivOneAddExpReciprocal (𝓝 (0 : ℝ)) (𝓝 (identityDivOneAddExpReciprocal 0))
    rw [identityDivOneAddExpReciprocal_zero]
    exact identityDivOneAddExpReciprocal_limit_zero
  · exact (identityDivOneAddExpReciprocal_hasDerivAt hx).continuousAt

theorem identityDivOneAddExpReciprocal_one_sided_slopes_at_zero :
    Tendsto (fun x : ℝ ↦ identityDivOneAddExpReciprocal x / x) (𝓝[<] (0 : ℝ)) (𝓝 1) ∧
      Tendsto (fun x : ℝ ↦ identityDivOneAddExpReciprocal x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hiL : Tendsto (fun x : ℝ ↦ x⁻¹) (𝓝[<] (0 : ℝ)) atBot := tendsto_inv_nhdsLT_zero
  have hiR : Tendsto (fun x : ℝ ↦ x⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have heL : Tendsto (fun x : ℝ ↦ Real.exp (1 / x)) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using! Real.tendsto_exp_atBot.comp hiL
  have heR : Tendsto (fun x : ℝ ↦ Real.exp (1 / x)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [Function.comp_def, one_div] using! Real.tendsto_exp_atTop.comp hiR
  constructor
  · have h := (heL.const_add 1).inv₀ (by norm_num : (1 + (0 : ℝ)) ≠ 0)
    norm_num at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
    dsimp only [Function.comp_def, identityDivOneAddExpReciprocal]
    field_simp [hx.ne, (identityDivOneAddExpReciprocal_denominator_pos x).ne']
  · have harg : Tendsto (fun x : ℝ ↦ 1 + Real.exp (1 / x)) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_atTop_add_const_left _ _ heR
    have h := tendsto_inv_atTop_zero.comp harg
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    dsimp only [Function.comp_def, identityDivOneAddExpReciprocal]
    field_simp [hx.ne', (identityDivOneAddExpReciprocal_denominator_pos x).ne']

theorem identityDivOneAddExpReciprocal_end_ratio {F : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ x⁻¹) F (𝓝 0)) (hn : ∀ᶠ x : ℝ in F, x ≠ 0) :
    Tendsto (fun x : ℝ ↦ identityDivOneAddExpReciprocal x / x) F (𝓝 (1 / 2 : ℝ)) := by
  have he : Tendsto (fun x : ℝ ↦ Real.exp (1 / x)) F (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero, one_div] using! Real.continuous_exp.continuousAt.tendsto.comp hi
  have h := (he.const_add 1).inv₀ (by norm_num : (1 + (1 : ℝ)) ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [hn] with x hx
  dsimp only [identityDivOneAddExpReciprocal]
  field_simp [hx, (identityDivOneAddExpReciprocal_denominator_pos x).ne']

theorem identityDivOneAddExpReciprocal_affine_residual {F : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ x⁻¹) F (𝓝[≠] (0 : ℝ))) :
    Tendsto (fun x : ℝ ↦ identityDivOneAddExpReciprocal x - (x / 2 - 1 / 4)) F (𝓝 0) := by
  have hq : Tendsto (fun t : ℝ ↦ (Real.exp t - 1) / t) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [zero_add, Real.exp_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have he : Tendsto (fun x : ℝ ↦ Real.exp (1 / x)) F (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero, one_div] using!
      Real.continuous_exp.continuousAt.tendsto.comp (tendsto_nhds_of_tendsto_nhdsWithin hi)
  have h := ((hq.comp hi).neg.div ((he.const_add 1).const_mul 2)
    (by norm_num : 2 * (1 + (1 : ℝ)) ≠ 0)).add_const (1 / 4)
  norm_num at h
  apply h.congr'
  have hn : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [hi.eventually self_mem_nhdsWithin] with x hx
    have hinv : x⁻¹ ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
    intro hzero
    exact hinv (by rw [hzero, inv_zero])
  filter_upwards [hn] with x hx
  dsimp only [Function.comp_def, identityDivOneAddExpReciprocal]
  field_simp [hx, (identityDivOneAddExpReciprocal_denominator_pos x).ne']
  ring

theorem identityDivOneAddExpReciprocal_tail_top : ∀ᶠ x : ℝ in atTop, x ∈ identityDivOneAddExpReciprocalDomain :=
  (eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne'

theorem identityDivOneAddExpReciprocal_tail_bot : ∀ᶠ x : ℝ in atBot, x ∈ identityDivOneAddExpReciprocalDomain :=
  (eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne

theorem identityDivOneAddExpReciprocal_limits_infinite :
    Tendsto identityDivOneAddExpReciprocal atTop atTop ∧ Tendsto identityDivOneAddExpReciprocal atBot atBot := by
  constructor
  · have h := (tendsto_id : Tendsto (fun x : ℝ ↦ x) atTop atTop).atTop_mul_pos
      (by norm_num : (0 : ℝ) < 1 / 2)
      (identityDivOneAddExpReciprocal_end_ratio tendsto_inv_atTop_zero identityDivOneAddExpReciprocal_tail_top)
    apply h.congr'
    filter_upwards [identityDivOneAddExpReciprocal_tail_top] with x hx
    simpa only [id_eq, mul_comm] using! div_mul_cancel₀ (identityDivOneAddExpReciprocal x) hx
  · have h := (tendsto_id : Tendsto (fun x : ℝ ↦ x) atBot atBot).atBot_mul_pos
      (by norm_num : (0 : ℝ) < 1 / 2)
      (identityDivOneAddExpReciprocal_end_ratio tendsto_inv_atBot_zero identityDivOneAddExpReciprocal_tail_bot)
    apply h.congr'
    filter_upwards [identityDivOneAddExpReciprocal_tail_bot] with x hx
    simpa only [id_eq, mul_comm] using! div_mul_cancel₀ (identityDivOneAddExpReciprocal x) hx

theorem identityDivOneAddExpReciprocal_asymptotes :
    (∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain a) ∧
      (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain b) ∧
      (∀ m b : ℝ, HasObliqueAsymptoteWithin identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain m b ↔
        m = 1 / 2 ∧ b = -1 / 4) := by
  have hiT : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsGT_le_nhdsNE 0)
  have hiB : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝[≠] (0 : ℝ)) :=
    tendsto_inv_atBot_nhdsLT_zero.mono_right (nhdsLT_le_nhdsNE 0)
  have hT := identityDivOneAddExpReciprocal_affine_residual hiT
  have hB := identityDivOneAddExpReciprocal_affine_residual hiB
  have hparsT (m b : ℝ) :
      Tendsto (fun x ↦ identityDivOneAddExpReciprocal x - (m * x + b)) atTop (𝓝 0) ↔ m = 1 / 2 ∧ b = -1 / 4 := by
    apply affine_parameters_iff tendsto_inv_atTop_zero identityDivOneAddExpReciprocal_tail_top
    apply hT.congr
    intro x
    ring
  have hparsB (m b : ℝ) :
      Tendsto (fun x ↦ identityDivOneAddExpReciprocal x - (m * x + b)) atBot (𝓝 0) ↔ m = 1 / 2 ∧ b = -1 / 4 := by
    apply affine_parameters_iff tendsto_inv_atBot_zero identityDivOneAddExpReciprocal_tail_bot
    apply hB.congr
    intro x
    ring
  refine ⟨fun a ↦ no_vertical_of_continuousAt identityDivOneAddExpReciprocal_continuous.continuousAt, ?_, ?_⟩
  · intro b
    rw [full_tail_horizontal_iff identityDivOneAddExpReciprocal_tail_top identityDivOneAddExpReciprocal_tail_bot, HasHorizontalAsymptote]
    rintro (h | h)
    · exact not_tendsto_atTop_of_tendsto_nhds h identityDivOneAddExpReciprocal_limits_infinite.1
    · exact not_tendsto_atBot_of_tendsto_nhds h identityDivOneAddExpReciprocal_limits_infinite.2
  · intro m b
    rw [full_tail_oblique_iff identityDivOneAddExpReciprocal_tail_top identityDivOneAddExpReciprocal_tail_bot, HasObliqueAsymptote]
    constructor
    · rintro ⟨_, h | h⟩
      · exact (hparsT m b).mp h
      · exact (hparsB m b).mp h
    · rintro ⟨rfl, rfl⟩
      exact ⟨by norm_num, Or.inl ((hparsT _ _).mpr ⟨rfl, rfl⟩)⟩

theorem identityDivOneAddExpReciprocal_graph (x y : ℝ) :
    (x ∈ identityDivOneAddExpReciprocalDomain ∧ identityDivOneAddExpReciprocal x = y) ↔
      x ≠ 0 ∧ (1 + Real.exp (1 / x)) * y = x := by
  change (x ≠ 0 ∧ x / (1 + Real.exp (1 / x)) = y) ↔ _
  rw [div_eq_iff (identityDivOneAddExpReciprocal_denominator_pos x).ne']
  constructor <;> rintro ⟨hx, hy⟩ <;> exact ⟨hx, by simpa only [mul_comm] using hy.symm⟩

theorem identityDivOneAddExpReciprocal_range (y : ℝ) :
    (∃ x ∈ identityDivOneAddExpReciprocalDomain, identityDivOneAddExpReciprocal x = y) ↔ y ≠ 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact fun hz ↦ hx ((identityDivOneAddExpReciprocal_signs x).2.2.mp hz)
  · intro hy
    obtain ⟨a, ha, hay⟩ := ((eventually_lt_atBot (0 : ℝ)).and
      (identityDivOneAddExpReciprocal_limits_infinite.2.eventually (eventually_lt_atBot y))).exists
    obtain ⟨b, hb, hby⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (identityDivOneAddExpReciprocal_limits_infinite.1.eventually (eventually_gt_atTop y))).exists
    have hmem := intermediate_value_Icc (show a ≤ b by linarith) identityDivOneAddExpReciprocal_continuous.continuousOn
      (show y ∈ Icc (identityDivOneAddExpReciprocal a) (identityDivOneAddExpReciprocal b) from ⟨hay.le, hby.le⟩)
    rcases hmem with ⟨x, _, hx⟩
    refine ⟨x, ?_, hx⟩
    intro hz
    subst x
    exact hy (by simpa only [identityDivOneAddExpReciprocal_zero] using hx.symm)

/-- Bài 14(c): khảo sát `x/(1+exp(1/x))` trên `x ≠ 0`. -/
theorem source_identity_div_one_add_exp_reciprocal_function_investigation :
    (∀ x : ℝ, x ∈ identityDivOneAddExpReciprocalDomain ↔ x ≠ 0) ∧
      (∀ x ∈ identityDivOneAddExpReciprocalDomain, HasDerivAt identityDivOneAddExpReciprocal (identityDivOneAddExpReciprocalFirstDeriv x) x ∧
        HasDerivAt (deriv identityDivOneAddExpReciprocal) (identityDivOneAddExpReciprocalSecondDeriv x) x ∧
        0 < deriv identityDivOneAddExpReciprocal x ∧ 0 < deriv (deriv identityDivOneAddExpReciprocal) x) ∧
      (StrictMonoOn identityDivOneAddExpReciprocal (Iio (0 : ℝ)) ∧ StrictMonoOn identityDivOneAddExpReciprocal (Ioi (0 : ℝ))) ∧
      (ConvexOn ℝ (Iio (0 : ℝ)) identityDivOneAddExpReciprocal ∧ ConvexOn ℝ (Ioi (0 : ℝ)) identityDivOneAddExpReciprocal) ∧
      (∀ x : ℝ, ¬ IsLocalMinimumOn identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain x ∧
        ¬ IsLocalMaximumOn identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain x) ∧
      (∀ a b c : ℝ, Ioo a b ⊆ identityDivOneAddExpReciprocalDomain → ¬ SourceInflectionOn identityDivOneAddExpReciprocal a b c) ∧
      (Tendsto identityDivOneAddExpReciprocal (𝓝[<] (0 : ℝ)) (𝓝 0) ∧ Tendsto identityDivOneAddExpReciprocal (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      (Tendsto (fun x : ℝ ↦ identityDivOneAddExpReciprocal x / x) (𝓝[<] (0 : ℝ)) (𝓝 1) ∧
        Tendsto (fun x : ℝ ↦ identityDivOneAddExpReciprocal x / x) (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      (Tendsto identityDivOneAddExpReciprocal atTop atTop ∧ Tendsto identityDivOneAddExpReciprocal atBot atBot) ∧
      ((∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain a) ∧
        (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain b) ∧
        ∀ m b : ℝ, HasObliqueAsymptoteWithin identityDivOneAddExpReciprocal identityDivOneAddExpReciprocalDomain m b ↔
          m = 1 / 2 ∧ b = -1 / 4) ∧
      (∀ x y : ℝ, (x ∈ identityDivOneAddExpReciprocalDomain ∧ identityDivOneAddExpReciprocal x = y) ↔
        x ≠ 0 ∧ (1 + Real.exp (1 / x)) * y = x) ∧
      (∀ y : ℝ, (∃ x ∈ identityDivOneAddExpReciprocalDomain, identityDivOneAddExpReciprocal x = y) ↔ y ≠ 0) :=
  ⟨identityDivOneAddExpReciprocal_domain_iff, fun _ hx ↦ ⟨identityDivOneAddExpReciprocal_hasDerivAt hx,
    identityDivOneAddExpReciprocal_second_hasDerivAt hx, identityDivOneAddExpReciprocal_deriv_pos hx, identityDivOneAddExpReciprocal_second_pos hx⟩,
    identityDivOneAddExpReciprocal_variation, identityDivOneAddExpReciprocal_convexity, identityDivOneAddExpReciprocal_no_extrema,
    fun _ _ _ hI ↦ identityDivOneAddExpReciprocal_no_inflection hI,
    ⟨identityDivOneAddExpReciprocal_limit_zero.mono_left nhdsWithin_le_nhds,
      identityDivOneAddExpReciprocal_limit_zero.mono_left nhdsWithin_le_nhds⟩,
    identityDivOneAddExpReciprocal_one_sided_slopes_at_zero, identityDivOneAddExpReciprocal_limits_infinite,
    identityDivOneAddExpReciprocal_asymptotes, identityDivOneAddExpReciprocal_graph, identityDivOneAddExpReciprocal_range⟩

end calculus.Chapter04.Section04IdentityDivOneAddExpReciprocalFunctionInvestigation
