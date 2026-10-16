import calculus.Chapter04.Section04InfiniteExtensions
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# §4.4 Bài 9: giới hạn từ ba đạo hàm và tính dương

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1751–1758. Xét hàm khả vi ba lần trên `(0, +∞)`, với `f, f′, f″ > 0`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04ThirdDerivativeRatioLimitExercise
open calculus.Chapter03.Section02Infinite
open calculus.Chapter04.Section04InfiniteExtensions


def ThreeTimesDifferentiableOnPositiveRay (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ f x ∧
    DifferentiableAt ℝ (deriv f) x ∧ DifferentiableAt ℝ (deriv (deriv f)) x


def FunctionAndFirstTwoDerivativesPositiveOnPositiveRay (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ioi (0 : ℝ), 0 < f x ∧ 0 < deriv f x ∧ 0 < deriv (deriv f) x


def firstMulThirdDerivDivSecondDerivSq (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x * deriv (deriv (deriv f)) x / (deriv (deriv f) x) ^ 2


def firstDerivDivSecondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x / deriv (deriv f) x


def firstDerivSqDivSecondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv f x) ^ 2 / deriv (deriv f) x


theorem source_third_derivative_positive_ray_limit_iff {g : ℝ → ℝ} {L : ℝ} :
    DomainAtTopLimit (Ioi (0 : ℝ)) g L ↔ Tendsto g atTop (𝓝 L) := by
  have hfilter : atTop ⊓ 𝓟 (Ioi (0 : ℝ)) = atTop := by
    apply inf_eq_left.mpr
    exact le_principal_iff.mpr (eventually_gt_atTop (0 : ℝ))
  rw [domainAtTopLimit_iff_tendsto (not_bddAbove_Ioi (0 : ℝ)), hfilter]


theorem positive_derivative_lower_bound_tendsto_at_top {g g' : ℝ → ℝ} {a C : ℝ}
    (hC : 0 < C) (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Ioi a, C ≤ g' x) : Tendsto g atTop atTop := by
  have hcont : ContinuousOn g (Ioi a) :=
    fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior (Ioi a)) := by
    rw [interior_Ioi]
    exact fun x hx ↦ (hg x hx).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Ioi a), C ≤ deriv g x := by
    rw [interior_Ioi]
    intro x hx
    rw [(hg x hx).deriv]
    exact hbound x hx
  have hlinear : Tendsto (fun x : ℝ ↦ g (a + 1) + C * (x - (a + 1))) atTop atTop := by
    simpa only [sub_eq_add_neg] using!
      tendsto_atTop_add_const_left atTop (g (a + 1))
      ((tendsto_atTop_add_const_right atTop (-(a + 1)) tendsto_id).const_mul_atTop hC)
  apply tendsto_atTop_mono' atTop _ hlinear
  filter_upwards [eventually_ge_atTop (a + 1)] with x hx
  have hb : a + 1 ∈ Ioi a := by change a < a + 1; linarith
  have hxx : x ∈ Ioi a := by change a < x; linarith
  have h := (convex_Ioi a).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hderiv (a + 1) hb x hxx hx
  linarith


theorem source_first_second_quotient_has_deriv {f : ℝ → ℝ}
    (hf : ThreeTimesDifferentiableOnPositiveRay f) (hp : FunctionAndFirstTwoDerivativesPositiveOnPositiveRay f)
    {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    HasDerivAt (firstDerivDivSecondDeriv f)
      (1 - firstMulThirdDerivDivSecondDerivSq f x) x := by
  have hb : deriv (deriv f) x ≠ 0 := (hp x hx).2.2.ne'
  have h := ((hf x hx).2.1.hasDerivAt).fun_div ((hf x hx).2.2.hasDerivAt) hb
  change HasDerivAt (firstDerivDivSecondDeriv f)
    ((deriv (deriv f) x * deriv (deriv f) x -
      deriv f x * deriv (deriv (deriv f)) x) / (deriv (deriv f) x) ^ 2) x at h
  apply h.congr_deriv
  unfold firstMulThirdDerivDivSecondDerivSq
  rw [sub_div, ← pow_two, div_self (pow_ne_zero 2 hb)]


theorem source_first_second_derivative_scaled_limit (f : ℝ → ℝ) (c : ℝ)
    (hf : ThreeTimesDifferentiableOnPositiveRay f) (hp : FunctionAndFirstTwoDerivativesPositiveOnPositiveRay f)
    (hr : DomainAtTopLimit (Ioi 0) (firstMulThirdDerivDivSecondDerivSq f) c) :
    DomainAtTopLimit (Ioi 0)
      (fun x : ℝ ↦ deriv f x / (x * deriv (deriv f) x)) (1 - c) := by
  have hratio : Tendsto (fun x : ℝ ↦ (1 - firstMulThirdDerivDivSecondDerivSq f x) / 1)
      atTop (𝓝 (1 - c)) := by
    simpa only [div_one] using!
      tendsto_const_nhds.sub (source_third_derivative_positive_ray_limit_iff.mp hr)
  have h := lhopital_infinite_atTop_hasDerivAt (a := 0)
    (fun x hx ↦ source_first_second_quotient_has_deriv hf hp hx)
    (fun x _ ↦ hasDerivAt_id x) (fun _ _ ↦ one_ne_zero)
    (Or.inl tendsto_id) hratio (Or.inl ⟨1 - c, rfl⟩)
  apply source_third_derivative_positive_ray_limit_iff.mpr
  apply h.congr'
  filter_upwards with x
  simp only [firstDerivDivSecondDeriv, id_eq]
  rw [div_div, mul_comm (deriv (deriv f) x) x]


theorem source_third_derivative_ratio_coefficient_le_one {f : ℝ → ℝ} {c : ℝ}
    (hf : ThreeTimesDifferentiableOnPositiveRay f) (hp : FunctionAndFirstTwoDerivativesPositiveOnPositiveRay f)
    (hr : DomainAtTopLimit (Ioi 0) (firstMulThirdDerivDivSecondDerivSq f) c) : c ≤ 1 := by
  have h := source_third_derivative_positive_ray_limit_iff.mp
    (source_first_second_derivative_scaled_limit f c hf hp hr)
  have hnonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ deriv f x / (x * deriv (deriv f) x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (div_pos (hp x hx).2.1 (mul_pos hx (hp x hx).2.2)).le
  have hc : 0 ≤ 1 - c := ge_of_tendsto h hnonneg
  linarith


theorem source_first_derivative_positive_lower_bound {f : ℝ → ℝ}
    (hf : ThreeTimesDifferentiableOnPositiveRay f) (hp : FunctionAndFirstTwoDerivativesPositiveOnPositiveRay f)
    {x : ℝ} (hx : 1 ≤ x) : deriv f 1 ≤ deriv f x := by
  have hm : MonotoneOn (deriv f) (Ioi (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
    · exact fun y hy ↦ (hf y hy).2.1.continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      exact fun y hy ↦ (hf y hy).2.1.differentiableWithinAt
    · rw [interior_Ioi]
      exact fun y hy ↦ (hp y hy).2.2.le
  exact hm (by norm_num : (1 : ℝ) ∈ Ioi 0) (by change 0 < x; linarith) hx


theorem source_squared_first_quotient_has_deriv {f : ℝ → ℝ}
    (hf : ThreeTimesDifferentiableOnPositiveRay f) (hp : FunctionAndFirstTwoDerivativesPositiveOnPositiveRay f)
    {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    HasDerivAt (firstDerivSqDivSecondDeriv f)
      ((2 - firstMulThirdDerivDivSecondDerivSq f x) * deriv f x) x := by
  have hb : deriv (deriv f) x ≠ 0 := (hp x hx).2.2.ne'
  have hpow : HasDerivAt (fun y : ℝ ↦ (deriv f y) ^ 2)
      (2 * deriv f x * deriv (deriv f) x) x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using!
      ((hf x hx).2.1.hasDerivAt).fun_pow 2
  have h := hpow.fun_div ((hf x hx).2.2.hasDerivAt) hb
  change HasDerivAt (firstDerivSqDivSecondDeriv f)
    ((2 * deriv f x * deriv (deriv f) x * deriv (deriv f) x -
      (deriv f x) ^ 2 * deriv (deriv (deriv f)) x) / (deriv (deriv f) x) ^ 2) x at h
  apply h.congr_deriv
  unfold firstMulThirdDerivDivSecondDerivSq
  rw [sub_div, mul_assoc (2 * deriv f x), ← pow_two,
    mul_div_cancel_right₀ (2 * deriv f x) (pow_ne_zero 2 hb)]
  ring


theorem source_positive_first_derivative_function_at_top {f : ℝ → ℝ}
    (hf : ThreeTimesDifferentiableOnPositiveRay f) (hp : FunctionAndFirstTwoDerivativesPositiveOnPositiveRay f) :
    Tendsto f atTop atTop := by
  apply positive_derivative_lower_bound_tendsto_at_top (a := 1)
    ((hp 1 (by norm_num)).2.1)
    (fun x hx ↦ (hf x (by change 0 < x; change 1 < x at hx; linarith)).1.hasDerivAt)
  intro x hx
  exact source_first_derivative_positive_lower_bound hf hp (le_of_lt hx)


theorem functionMulSecondDerivDivFirstDerivSq_limit (f : ℝ → ℝ) (c : ℝ)
    (hf : ThreeTimesDifferentiableOnPositiveRay f) (hp : FunctionAndFirstTwoDerivativesPositiveOnPositiveRay f)
    (hr : DomainAtTopLimit (Ioi 0) (firstMulThirdDerivDivSecondDerivSq f) c) :
    DomainAtTopLimit (Ioi 0)
      (fun x : ℝ ↦ f x * deriv (deriv f) x / (deriv f x) ^ 2) (1 / (2 - c)) := by
  have hc := source_third_derivative_ratio_coefficient_le_one hf hp hr
  have hrlim := source_third_derivative_positive_ray_limit_iff.mp hr
  have hevent : ∀ᶠ x : ℝ in atTop, firstMulThirdDerivDivSecondDerivSq f x < 3 / 2 :=
    hrlim.eventually (eventually_lt_nhds (by linarith : c < (3 : ℝ) / 2))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  let a : ℝ := max 1 M
  have ha1 : 1 ≤ a := le_max_left 1 M
  have haM : M ≤ a := le_max_right 1 M
  have hpos (x : ℝ) (hx : x ∈ Ioi a) : x ∈ Ioi (0 : ℝ) := by
    change a < x at hx
    change 0 < x
    linarith
  have hfactor (x : ℝ) (hx : x ∈ Ioi a) : 1 / 2 ≤ 2 - firstMulThirdDerivDivSecondDerivSq f x := by
    have h := hM x (by change a < x at hx; linarith)
    linarith
  have hm : 0 < deriv f 1 := (hp 1 (by norm_num)).2.1
  have hHbound (x : ℝ) (hx : x ∈ Ioi a) :
      deriv f 1 / 2 ≤ (2 - firstMulThirdDerivDivSecondDerivSq f x) * deriv f x := by
    have hfirst := source_first_derivative_positive_lower_bound hf hp
      (show 1 ≤ x by change a < x at hx; linarith)
    have hmul : (1 / 2 : ℝ) * deriv f 1 ≤
        (2 - firstMulThirdDerivDivSecondDerivSq f x) * deriv f x :=
      (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
        (mul_le_mul_of_nonneg_right (hfactor x hx) (hp x (hpos x hx)).2.1.le)
    nlinarith
  have hHinf : Tendsto (firstDerivSqDivSecondDeriv f) atTop atTop :=
    positive_derivative_lower_bound_tendsto_at_top (a := a) (by positivity : 0 < deriv f 1 / 2)
      (fun x hx ↦ source_squared_first_quotient_has_deriv hf hp (hpos x hx)) hHbound
  have hden : 2 - c ≠ 0 := by linarith
  have hratio : Tendsto (fun x : ℝ ↦ deriv f x /
      ((2 - firstMulThirdDerivDivSecondDerivSq f x) * deriv f x)) atTop (𝓝 (1 / (2 - c))) := by
    apply (tendsto_const_nhds.div (tendsto_const_nhds.sub hrlim) hden).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [mul_comm (2 - firstMulThirdDerivDivSecondDerivSq f x) (deriv f x), ← div_div,
      div_self (hp x hx).2.1.ne']
    rfl
  have h := source_lhopital_infinite_atTop (a := a)
    (fun x hx ↦ (hf x (hpos x hx)).1.hasDerivAt)
    (fun x hx ↦ source_squared_first_quotient_has_deriv hf hp (hpos x hx))
    (fun x hx ↦ mul_ne_zero (by have h := hfactor x hx; linarith)
      (hp x (hpos x hx)).2.1.ne')
    (Or.inl (source_positive_first_derivative_function_at_top hf hp))
    (Or.inl hHinf) hratio (Or.inl ⟨1 / (2 - c), rfl⟩)
  apply source_third_derivative_positive_ray_limit_iff.mpr
  apply h.congr'
  filter_upwards with x
  simp only [firstDerivSqDivSecondDeriv]
  rw [div_div_eq_mul_div]

end calculus.Chapter04.Section04ThirdDerivativeRatioLimitExercise
