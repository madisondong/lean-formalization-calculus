import calculus.Chapter04.Section04RationalFunctionInvestigationSupport
import calculus.Chapter04.Section04CurveInvestigationSourceIssues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bài 4.4.14(g): khảo sát trên toàn miền xác định

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2767, `arcsin √(2 exp x − exp² x)`.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04ArcsineExponentialFunctionInvestigationExercise
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03 calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section01Derivatives
open calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04CurveInvestigationSourceIssues
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport
open calculus.Chapter04.Section04RationalFunctionInvestigationSupport


def arcsinSqrtTwoExpSubExpSq (x : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt (2 * Real.exp x - (Real.exp x) ^ 2))
def arcsinSqrtTwoExpSubExpSqDomain : Set ℝ := Iic (Real.log 2)
def arcsinSqrtTwoExpSubExpSqRadicand (x : ℝ) : ℝ := Real.exp x * (2 - Real.exp x)
def arcsinSqrtTwoExpSubExpSqLeftBranch (x : ℝ) : ℝ := Real.arccos (1 - Real.exp x)
def arcsinSqrtTwoExpSubExpSqRightBranch (x : ℝ) : ℝ := Real.arccos (Real.exp x - 1)
def arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude (x : ℝ) : ℝ :=
  Real.exp x / Real.sqrt (arcsinSqrtTwoExpSubExpSqRadicand x)
def arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude (x : ℝ) : ℝ :=
  (Real.exp x) ^ 2 / (Real.sqrt (arcsinSqrtTwoExpSubExpSqRadicand x)) ^ 3


theorem arcsinSqrtTwoExpSubExpSq_endpoint :
    0 < Real.log 2 ∧ Real.exp (Real.log 2) = 2 := by
  exact ⟨Real.log_pos (by norm_num), Real.exp_log (by norm_num)⟩

theorem arcsinSqrtTwoExpSubExpSq_exp_bound (x : ℝ) :
    (Real.exp x ≤ 2 ↔ x ≤ Real.log 2) ∧
      (Real.exp x < 2 ↔ x < Real.log 2) := by
  constructor
  · simpa only [arcsinSqrtTwoExpSubExpSq_endpoint.2] using
      (Real.exp_le_exp : Real.exp x ≤ Real.exp (Real.log 2) ↔ x ≤ Real.log 2)
  · simpa only [arcsinSqrtTwoExpSubExpSq_endpoint.2] using
      (Real.exp_lt_exp : Real.exp x < Real.exp (Real.log 2) ↔ x < Real.log 2)


theorem arcsinSqrtTwoExpSubExpSq_natural_domain_iff (x : ℝ) :
    x ∈ arcsinSqrtTwoExpSubExpSqDomain ↔
      0 ≤ 2 * Real.exp x - (Real.exp x) ^ 2 ∧
        -1 ≤ Real.sqrt (2 * Real.exp x - (Real.exp x) ^ 2) ∧
        Real.sqrt (2 * Real.exp x - (Real.exp x) ^ 2) ≤ 1 := by
  have hp := Real.exp_pos x
  have he : 2 * Real.exp x - (Real.exp x) ^ 2 =
      Real.exp x * (2 - Real.exp x) := by ring
  have hb : 2 * Real.exp x - (Real.exp x) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.exp x - 1)]
  rw [arcsinSqrtTwoExpSubExpSqDomain, mem_Iic]
  constructor
  · intro hx
    have ht := (arcsinSqrtTwoExpSubExpSq_exp_bound x).1.mpr hx
    refine ⟨?_, ?_, Real.sqrt_le_one.mpr hb⟩
    · rw [he]; exact mul_nonneg hp.le (sub_nonneg.mpr ht)
    · linarith [Real.sqrt_nonneg (2 * Real.exp x - (Real.exp x) ^ 2)]
  · rintro ⟨hq, _, _⟩
    apply (arcsinSqrtTwoExpSubExpSq_exp_bound x).1.mp
    rw [he] at hq
    nlinarith

theorem arcsinSqrtTwoExpSubExpSq_radicand_positive {x : ℝ} (hx : x < Real.log 2) :
    0 < arcsinSqrtTwoExpSubExpSqRadicand x :=
  mul_pos (Real.exp_pos x) (sub_pos.mpr ((arcsinSqrtTwoExpSubExpSq_exp_bound x).2.mpr hx))


theorem arcsinSqrtTwoExpSubExpSq_eq_arccos (x : ℝ) :
    arcsinSqrtTwoExpSubExpSq x = Real.arccos |1 - Real.exp x| := by
  rw [Real.arccos_eq_arcsin (abs_nonneg _)]
  unfold arcsinSqrtTwoExpSubExpSq
  congr 2
  rw [sq_abs]
  ring

theorem arcsinSqrtTwoExpSubExpSq_left_branch {x : ℝ} (hx : x ≤ 0) :
    arcsinSqrtTwoExpSubExpSq x = arcsinSqrtTwoExpSubExpSqLeftBranch x := by
  have ht : Real.exp x ≤ 1 := by simpa using Real.exp_le_exp.mpr hx
  rw [arcsinSqrtTwoExpSubExpSq_eq_arccos, abs_of_nonneg (sub_nonneg.mpr ht)]
  rfl

theorem arcsinSqrtTwoExpSubExpSq_right_branch {x : ℝ} (hx : 0 ≤ x) :
    arcsinSqrtTwoExpSubExpSq x = arcsinSqrtTwoExpSubExpSqRightBranch x := by
  have ht : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  rw [arcsinSqrtTwoExpSubExpSq_eq_arccos, abs_of_nonpos (sub_nonpos.mpr ht)]
  simp only [arcsinSqrtTwoExpSubExpSqRightBranch, neg_sub]

theorem arcsinSqrtTwoExpSubExpSq_continuous : Continuous arcsinSqrtTwoExpSubExpSq := by
  unfold arcsinSqrtTwoExpSubExpSq
  fun_prop

theorem arcsinSqrtTwoExpSubExpSq_values :
    arcsinSqrtTwoExpSubExpSq 0 = Real.pi / 2 ∧
      arcsinSqrtTwoExpSubExpSq (Real.log 2) = 0 := by
  constructor
  · norm_num [arcsinSqrtTwoExpSubExpSq]
  · norm_num [arcsinSqrtTwoExpSubExpSq, arcsinSqrtTwoExpSubExpSq_endpoint.2]

theorem arcsinSqrtTwoExpSubExpSq_bounds (x : ℝ) :
    0 ≤ arcsinSqrtTwoExpSubExpSq x ∧ arcsinSqrtTwoExpSubExpSq x ≤ Real.pi / 2 := by
  unfold arcsinSqrtTwoExpSubExpSq
  exact ⟨Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _), Real.arcsin_le_pi_div_two _⟩


theorem arcsinSqrtTwoExpSubExpSqLeftBranch_hasDerivAt {x : ℝ} (hx : x < Real.log 2) :
    HasDerivAt arcsinSqrtTwoExpSubExpSqLeftBranch (arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude x) x := by
  have ht := (arcsinSqrtTwoExpSubExpSq_exp_bound x).2.mpr hx
  have hp := Real.exp_pos x
  have h := (Real.hasDerivAt_arccos
    (show 1 - Real.exp x ≠ -1 by linarith)
    (show 1 - Real.exp x ≠ 1 by linarith)).comp x
      ((Real.hasDerivAt_exp x).const_sub 1)
  have he : 1 - (1 - Real.exp x) ^ 2 = arcsinSqrtTwoExpSubExpSqRadicand x := by
    unfold arcsinSqrtTwoExpSubExpSqRadicand; ring
  apply h.congr_deriv
  rw [he]
  unfold arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude
  ring

theorem arcsinSqrtTwoExpSubExpSqRightBranch_hasDerivAt {x : ℝ} (hx : x < Real.log 2) :
    HasDerivAt arcsinSqrtTwoExpSubExpSqRightBranch (-arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude x) x := by
  have ht := (arcsinSqrtTwoExpSubExpSq_exp_bound x).2.mpr hx
  have hp := Real.exp_pos x
  have h := (Real.hasDerivAt_arccos
    (show Real.exp x - 1 ≠ -1 by linarith)
    (show Real.exp x - 1 ≠ 1 by linarith)).comp x
      ((Real.hasDerivAt_exp x).sub_const 1)
  have he : 1 - (Real.exp x - 1) ^ 2 = arcsinSqrtTwoExpSubExpSqRadicand x := by
    unfold arcsinSqrtTwoExpSubExpSqRadicand; ring
  apply h.congr_deriv
  rw [he]
  unfold arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude
  ring

theorem arcsinSqrtTwoExpSubExpSqRadicand_hasDerivAt (x : ℝ) :
    HasDerivAt arcsinSqrtTwoExpSubExpSqRadicand
      (2 * Real.exp x * (1 - Real.exp x)) x := by
  have h := (Real.hasDerivAt_exp x).mul ((Real.hasDerivAt_exp x).const_sub 2)
  apply h.congr_deriv
  ring

theorem arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude_hasDerivAt {x : ℝ} (hx : x < Real.log 2) :
    HasDerivAt arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude (arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude x) x := by
  have hp := arcsinSqrtTwoExpSubExpSq_radicand_positive hx
  have hs := Real.sqrt_pos.mpr hp
  have hd := (Real.hasDerivAt_sqrt hp.ne').comp x
    (arcsinSqrtTwoExpSubExpSqRadicand_hasDerivAt x)
  have h := (Real.hasDerivAt_exp x).div hd hs.ne'
  simp only [Function.comp_def] at h
  apply h.congr_deriv
  unfold arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude
  have he := Real.sq_sqrt hp.le
  have het := congrArg (fun u : ℝ ↦ Real.exp x * u) he
  unfold arcsinSqrtTwoExpSubExpSqRadicand at he het hs ⊢
  field_simp [hs.ne']
  nlinarith

theorem arcsinSqrtTwoExpSubExpSqLeftBranch_second_hasDerivAt {x : ℝ} (hx : x < Real.log 2) :
    HasDerivAt (deriv arcsinSqrtTwoExpSubExpSqLeftBranch) (arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude x) x :=
  hasDerivAt_deriv_of_open_formula isOpen_Iio hx
    (fun _ hy ↦ arcsinSqrtTwoExpSubExpSqLeftBranch_hasDerivAt hy)
    (arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude_hasDerivAt hx)

theorem arcsinSqrtTwoExpSubExpSqRightBranch_second_hasDerivAt {x : ℝ} (hx : x < Real.log 2) :
    HasDerivAt (deriv arcsinSqrtTwoExpSubExpSqRightBranch) (-arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude x) x := by
  apply hasDerivAt_deriv_of_open_formula isOpen_Iio hx
    (fun _ hy ↦ arcsinSqrtTwoExpSubExpSqRightBranch_hasDerivAt hy)
  exact (arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude_hasDerivAt hx).fun_neg

theorem arcsinSqrtTwoExpSubExpSq_deriv_magnitudes_pos {x : ℝ} (hx : x < Real.log 2) :
    0 < arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude x ∧ 0 < arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude x := by
  have hs := Real.sqrt_pos.mpr (arcsinSqrtTwoExpSubExpSq_radicand_positive hx)
  exact ⟨div_pos (Real.exp_pos x) hs, div_pos (sq_pos_of_pos (Real.exp_pos x)) (pow_pos hs 3)⟩

theorem arcsinSqrtTwoExpSubExpSq_left_hasDerivAt {x : ℝ} (hx : x < 0) :
    HasDerivAt arcsinSqrtTwoExpSubExpSq (arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude x) x := by
  apply (arcsinSqrtTwoExpSubExpSqLeftBranch_hasDerivAt (hx.trans arcsinSqrtTwoExpSubExpSq_endpoint.1)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact arcsinSqrtTwoExpSubExpSq_left_branch hy.le

theorem arcsinSqrtTwoExpSubExpSq_right_hasDerivAt {x : ℝ}
    (hx : 0 < x) (hb : x < Real.log 2) :
    HasDerivAt arcsinSqrtTwoExpSubExpSq (-arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude x) x := by
  apply (arcsinSqrtTwoExpSubExpSqRightBranch_hasDerivAt hb).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact arcsinSqrtTwoExpSubExpSq_right_branch hy.le

theorem arcsinSqrtTwoExpSubExpSq_second_left {x : ℝ} (hx : x < 0) :
    HasDerivAt (deriv arcsinSqrtTwoExpSubExpSq) (arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude x) x := by
  apply (arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude_hasDerivAt (hx.trans arcsinSqrtTwoExpSubExpSq_endpoint.1)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact (arcsinSqrtTwoExpSubExpSq_left_hasDerivAt hy).deriv

theorem arcsinSqrtTwoExpSubExpSq_second_right {x : ℝ} (hx : 0 < x) (hb : x < Real.log 2) :
    HasDerivAt (deriv arcsinSqrtTwoExpSubExpSq) (-arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude x) x := by
  apply (arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude_hasDerivAt hb).fun_neg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx, Iio_mem_nhds hb] with y hy hyb
  exact (arcsinSqrtTwoExpSubExpSq_right_hasDerivAt hy hyb).deriv


theorem arcsinSqrtTwoExpSubExpSq_variation :
    StrictMonoOn arcsinSqrtTwoExpSubExpSq (Iic (0 : ℝ)) ∧
      StrictAntiOn arcsinSqrtTwoExpSubExpSq (Icc (0 : ℝ) (Real.log 2)) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Iic _) arcsinSqrtTwoExpSubExpSq_continuous.continuousOn
    intro x hx
    rw [interior_Iic] at hx
    rw [(arcsinSqrtTwoExpSubExpSq_left_hasDerivAt hx).deriv]
    exact (arcsinSqrtTwoExpSubExpSq_deriv_magnitudes_pos (hx.trans arcsinSqrtTwoExpSubExpSq_endpoint.1)).1
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _) arcsinSqrtTwoExpSubExpSq_continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(arcsinSqrtTwoExpSubExpSq_right_hasDerivAt hx.1 hx.2).deriv]
    exact neg_neg_of_pos (arcsinSqrtTwoExpSubExpSq_deriv_magnitudes_pos hx.2).1


theorem arcsinSqrtTwoExpSubExpSq_corner_slopes :
    HasLeftDerivativeAt arcsinSqrtTwoExpSubExpSq 0 1 ∧
      HasRightDerivativeAt arcsinSqrtTwoExpSubExpSq 0 (-1) := by
  have hs : arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude 0 = 1 := by
    norm_num [arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude, arcsinSqrtTwoExpSubExpSqRadicand]
  have hl := ((hasDerivAt_iff_left_right _ _ _).mp
    (arcsinSqrtTwoExpSubExpSqLeftBranch_hasDerivAt arcsinSqrtTwoExpSubExpSq_endpoint.1)).1
  have hr := ((hasDerivAt_iff_left_right _ _ _).mp
    (arcsinSqrtTwoExpSubExpSqRightBranch_hasDerivAt arcsinSqrtTwoExpSubExpSq_endpoint.1)).2
  rw [hs] at hl hr
  change Tendsto (fun x : ℝ ↦ (arcsinSqrtTwoExpSubExpSqLeftBranch x - arcsinSqrtTwoExpSubExpSqLeftBranch 0) / (x - 0))
    (𝓝[<] (0 : ℝ)) (𝓝 1) at hl
  change Tendsto (fun x : ℝ ↦ (arcsinSqrtTwoExpSubExpSqRightBranch x - arcsinSqrtTwoExpSubExpSqRightBranch 0) / (x - 0))
    (𝓝[>] (0 : ℝ)) (𝓝 (-1)) at hr
  constructor
  · apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
    rw [arcsinSqrtTwoExpSubExpSq_left_branch hx.le, arcsinSqrtTwoExpSubExpSq_left_branch le_rfl]
  · apply hr.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [arcsinSqrtTwoExpSubExpSq_right_branch hx.le, arcsinSqrtTwoExpSubExpSq_right_branch le_rfl]

theorem arcsinSqrtTwoExpSubExpSq_corner_not_differentiable :
    ¬ DifferentiableAt ℝ arcsinSqrtTwoExpSubExpSq 0 := by
  intro hd
  have hh := (hasDerivAt_iff_left_right _ _ _).mp hd.hasDerivAt
  have hl := tendsto_nhds_unique hh.1 arcsinSqrtTwoExpSubExpSq_corner_slopes.1
  have hr := tendsto_nhds_unique hh.2 arcsinSqrtTwoExpSubExpSq_corner_slopes.2
  linarith

theorem arcsinSqrtTwoExpSubExpSq_corner_not_infinite (a b : ℝ) (h0 : (0 : ℝ) ∈ Ioo a b) :
    ¬ HasInfiniteDerivativeWithinAt arcsinSqrtTwoExpSubExpSq (Ioo a b) 0 := by
  apply local_maximum_not_source_infinite_derivative h0
  apply Eventually.of_forall
  intro x
  rw [arcsinSqrtTwoExpSubExpSq_values.1]
  exact (arcsinSqrtTwoExpSubExpSq_bounds x).2


theorem arcsinSqrtTwoExpSubExpSq_branch_derivatives {x : ℝ}
    (hb : x < Real.log 2) (hx : x ≠ 0) :
    (if x < 0 then HasDerivAt arcsinSqrtTwoExpSubExpSq (arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude x) x ∧
        HasDerivAt (deriv arcsinSqrtTwoExpSubExpSq) (arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude x) x
      else HasDerivAt arcsinSqrtTwoExpSubExpSq (-arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude x) x ∧
        HasDerivAt (deriv arcsinSqrtTwoExpSubExpSq) (-arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude x) x) := by
  by_cases hn : x < 0
  · rw [if_pos hn]
    exact ⟨arcsinSqrtTwoExpSubExpSq_left_hasDerivAt hn, arcsinSqrtTwoExpSubExpSq_second_left hn⟩
  · rw [if_neg hn]
    have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx)
    exact ⟨arcsinSqrtTwoExpSubExpSq_right_hasDerivAt hp hb, arcsinSqrtTwoExpSubExpSq_second_right hp hb⟩

theorem arcsinSqrtTwoExpSubExpSq_first_second_derivs_nonzero {x : ℝ}
    (hb : x < Real.log 2) (hx : x ≠ 0) :
    DifferentiableAt ℝ arcsinSqrtTwoExpSubExpSq x ∧
      DifferentiableAt ℝ (deriv arcsinSqrtTwoExpSubExpSq) x ∧
      deriv arcsinSqrtTwoExpSubExpSq x ≠ 0 ∧ deriv (deriv arcsinSqrtTwoExpSubExpSq) x ≠ 0 := by
  have hs := arcsinSqrtTwoExpSubExpSq_deriv_magnitudes_pos hb
  have hd := arcsinSqrtTwoExpSubExpSq_branch_derivatives hb hx
  by_cases hn : x < 0
  · rw [if_pos hn] at hd
    exact ⟨hd.1.differentiableAt, hd.2.differentiableAt, by rw [hd.1.deriv]; exact hs.1.ne',
      by rw [hd.2.deriv]; exact hs.2.ne'⟩
  · rw [if_neg hn] at hd
    exact ⟨hd.1.differentiableAt, hd.2.differentiableAt,
      by rw [hd.1.deriv]; exact neg_ne_zero.mpr hs.1.ne',
      by rw [hd.2.deriv]; exact neg_ne_zero.mpr hs.2.ne'⟩


theorem arcsinSqrtTwoExpSubExpSq_extrema :
    (∀ x : ℝ, IsLocalMaximumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain x ↔ x = 0) ∧
      (∀ x : ℝ, IsLocalMinimumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain x ↔
        x = Real.log 2) := by
  have hmax : IsLocalMaximumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain 0 := by
    refine ⟨arcsinSqrtTwoExpSubExpSq_endpoint.1.le, 1, by norm_num, ?_⟩
    intro x _
    rw [arcsinSqrtTwoExpSubExpSq_values.1]
    exact (arcsinSqrtTwoExpSubExpSq_bounds x).2
  have hmin : IsLocalMinimumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain (Real.log 2) := by
    refine ⟨(by change Real.log 2 ≤ Real.log 2; exact le_rfl), 1, by norm_num, ?_⟩
    intro x _
    rw [arcsinSqrtTwoExpSubExpSq_values.2]
    exact (arcsinSqrtTwoExpSubExpSq_bounds x).1
  have hnmin : ¬ IsLocalMinimumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain 0 := by
    apply no_local_minimum_of_right_decrease (b := Real.log 2) arcsinSqrtTwoExpSubExpSq_endpoint.1
    · intro x hx; exact hx.2.le
    · intro x hx
      exact arcsinSqrtTwoExpSubExpSq_variation.2 ⟨le_rfl, arcsinSqrtTwoExpSubExpSq_endpoint.1.le⟩
        ⟨hx.1.le, hx.2.le⟩ hx.1
  have hnmax : ¬ IsLocalMaximumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain (Real.log 2) := by
    rintro ⟨_, δ, hδ, hbound⟩
    let t : ℝ := min (δ / 2) (Real.log 2 / 2)
    have ht : 0 < t := lt_min (by positivity) (by linarith [arcsinSqrtTwoExpSubExpSq_endpoint.1])
    have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htb : t < Real.log 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith [arcsinSqrtTwoExpSubExpSq_endpoint.1])
    have hc : Real.log 2 - t ∈ Icc (0 : ℝ) (Real.log 2) := ⟨by linarith, by linarith⟩
    have hstrict := arcsinSqrtTwoExpSubExpSq_variation.2 hc ⟨arcsinSqrtTwoExpSubExpSq_endpoint.1.le, le_rfl⟩
      (show Real.log 2 - t < Real.log 2 by linarith)
    have hnon := hbound (Real.log 2 - t) ⟨⟨by linarith, by linarith⟩, hc.2⟩
    linarith
  have hint {x : ℝ} (hb : x < Real.log 2) (hx : x ≠ 0)
      (he : IsLocalExtremumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain x) : False := by
    have hsmall : IsLocalExtremumOn arcsinSqrtTwoExpSubExpSq (Iio (Real.log 2)) x := by
      rcases he with ⟨_, δ, hδ, hbound⟩ | ⟨_, δ, hδ, hbound⟩
      · exact Or.inl ⟨hb, δ, hδ, fun y hy ↦ hbound y ⟨hy.1, (by change y ≤ Real.log 2; exact hy.2.le)⟩⟩
      · exact Or.inr ⟨hb, δ, hδ, fun y hy ↦ hbound y ⟨hy.1, (by change y ≤ Real.log 2; exact hy.2.le)⟩⟩
    have hd := arcsinSqrtTwoExpSubExpSq_first_second_derivs_nonzero hb hx
    exact hd.2.2.1 (fermat isOpen_Iio hsmall hd.1)
  constructor
  · intro x; constructor
    · intro he
      by_contra hx
      have hxe : x ≤ Real.log 2 := he.1
      rcases eq_or_lt_of_le hxe with hxend | hxend
      · subst x; exact hnmax he
      · exact hint hxend hx (Or.inr he)
    · rintro rfl; exact hmax
  · intro x; constructor
    · intro he
      by_contra hb
      by_cases hx : x = 0
      · subst x; exact hnmin he
      · have hxe : x ≤ Real.log 2 := he.1
        exact hint (lt_of_le_of_ne hxe hb) hx (Or.inl he)
    · rintro rfl; exact hmin


theorem arcsinSqrtTwoExpSubExpSq_convexity :
    ConvexOn ℝ (Iic (0 : ℝ)) arcsinSqrtTwoExpSubExpSq ∧
      ConcaveOn ℝ (Icc (0 : ℝ) (Real.log 2)) arcsinSqrtTwoExpSubExpSq := by
  constructor
  · apply (strictConvexOn_of_deriv2_pos (convex_Iic _)
      arcsinSqrtTwoExpSubExpSq_continuous.continuousOn ?_).convexOn
    intro x hx
    rw [interior_Iic] at hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      (arcsinSqrtTwoExpSubExpSq_second_left hx).deriv] using
      (arcsinSqrtTwoExpSubExpSq_deriv_magnitudes_pos (hx.trans arcsinSqrtTwoExpSubExpSq_endpoint.1)).2
  · apply (strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
      arcsinSqrtTwoExpSubExpSq_continuous.continuousOn ?_).concaveOn
    intro x hx
    rw [interior_Icc] at hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      (arcsinSqrtTwoExpSubExpSq_second_right hx.1 hx.2).deriv] using
      neg_neg_of_pos (arcsinSqrtTwoExpSubExpSq_deriv_magnitudes_pos hx.2).2


theorem arcsinSqrtTwoExpSubExpSq_no_inflection (a b c : ℝ)
    (hI : Ioo a b ⊆ arcsinSqrtTwoExpSubExpSqDomain) :
    ¬ SourceInflectionOn arcsinSqrtTwoExpSubExpSq a b c := by
  intro hu
  by_cases hc : c = 0
  · subst c
    rcases hu.2.2.1 with hd | hi
    · exact arcsinSqrtTwoExpSubExpSq_corner_not_differentiable hd
    · exact arcsinSqrtTwoExpSubExpSq_corner_not_infinite a b hu.1 hi
  · have hsub : Ioo a b ⊆ {x : ℝ | x < Real.log 2 ∧ x ≠ 0} := by
      intro x hx
      have hb : x < Real.log 2 := by
        have hmid := hI (show (x + b) / 2 ∈ Ioo a b by constructor <;> linarith [hx.1, hx.2])
        change (x + b) / 2 ≤ Real.log 2 at hmid
        linarith [hx.2]
      refine ⟨hb, ?_⟩
      intro he
      subst x
      exact arcsinSqrtTwoExpSubExpSq_corner_not_differentiable (hu.2.1 0 ⟨hx, Ne.symm hc⟩)
    have hcD := hsub hu.1
    have hcont : ContinuousAt (deriv (deriv arcsinSqrtTwoExpSubExpSq)) c := by
      have hp := arcsinSqrtTwoExpSubExpSq_radicand_positive hcD.1
      have hs : ContinuousAt arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude c := by
        unfold arcsinSqrtTwoExpSubExpSqSecondDerivMagnitude arcsinSqrtTwoExpSubExpSqRadicand
        fun_prop (disch := exact pow_ne_zero 3 (Real.sqrt_pos.mpr hp).ne')
      rcases lt_or_gt_of_ne hc with hn | hn
      · apply hs.congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds hn] with x hx
        exact (arcsinSqrtTwoExpSubExpSq_second_left hx).deriv
      · apply hs.neg.congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hn, Iio_mem_nhds hcD.1] with x hx hxb
        exact (arcsinSqrtTwoExpSubExpSq_second_right hx hxb).deriv
    have hz := second_zero_of_sourceInflection hsub
      (fun x hx ↦ (arcsinSqrtTwoExpSubExpSq_first_second_derivs_nonzero hx.1 hx.2).1)
      (fun x hx ↦ (arcsinSqrtTwoExpSubExpSq_first_second_derivs_nonzero hx.1 hx.2).2.1) hcont hu
    exact (arcsinSqrtTwoExpSubExpSq_first_second_derivs_nonzero hcD.1 hcD.2).2.2.2 hz


theorem arcsinSqrtTwoExpSubExpSq_endpoint_slope_limit :
    Tendsto (fun x : ℝ ↦
      (arcsinSqrtTwoExpSubExpSq x - arcsinSqrtTwoExpSubExpSq (Real.log 2)) /
        (x - Real.log 2)) (𝓝[<] (Real.log 2)) atBot := by
  have hq : Tendsto (fun x : ℝ ↦ Real.sqrt (arcsinSqrtTwoExpSubExpSqRadicand x))
      (𝓝[<] (Real.log 2)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous (fun x : ℝ ↦ Real.sqrt (arcsinSqrtTwoExpSubExpSqRadicand x)) := by
        unfold arcsinSqrtTwoExpSubExpSqRadicand; fun_prop
      simpa [arcsinSqrtTwoExpSubExpSqRadicand, arcsinSqrtTwoExpSubExpSq_endpoint.2] using
        (hcont.tendsto (Real.log 2)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x (hx : x < Real.log 2)
      exact Real.sqrt_pos.mpr (arcsinSqrtTwoExpSubExpSq_radicand_positive hx)
  have hexp : Tendsto Real.exp (𝓝[<] (Real.log 2)) (𝓝 (2 : ℝ)) := by
    simpa only [arcsinSqrtTwoExpSubExpSq_endpoint.2] using
      (Real.continuous_exp.tendsto (Real.log 2)).mono_left nhdsWithin_le_nhds
  have hder : Tendsto (fun x : ℝ ↦ -arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude x)
      (𝓝[<] (Real.log 2)) atBot := by
    simpa only [arcsinSqrtTwoExpSubExpSqFirstDerivMagnitude, div_eq_mul_inv, Function.comp_def, Pi.inv_apply] using
      tendsto_neg_atTop_atBot.comp (hexp.pos_mul_atTop (by norm_num) hq.inv_tendsto_nhdsGT_zero)
  have hn : Tendsto (fun x : ℝ ↦ arcsinSqrtTwoExpSubExpSq x -
      arcsinSqrtTwoExpSubExpSq (Real.log 2)) (𝓝[<] (Real.log 2)) (𝓝 0) := by
    simpa using ((arcsinSqrtTwoExpSubExpSq_continuous.tendsto (Real.log 2)).sub_const
      (arcsinSqrtTwoExpSubExpSq (Real.log 2))).mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun x : ℝ ↦ x - Real.log 2)
      (𝓝[<] (Real.log 2)) (𝓝 0) := by
    simpa using ((continuous_id.tendsto (Real.log 2)).sub_const (Real.log 2)).mono_left nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_left_on_Ioo arcsinSqrtTwoExpSubExpSq_endpoint.1
    (fun x hx ↦ (arcsinSqrtTwoExpSubExpSq_right_hasDerivAt hx.1 hx.2).sub_const
      (arcsinSqrtTwoExpSubExpSq (Real.log 2)))
    (fun x _ ↦ (hasDerivAt_id x).sub_const (Real.log 2))
    (fun _ _ ↦ one_ne_zero) hn hd
  simpa only [div_one] using hder

theorem arcsinSqrtTwoExpSubExpSq_endpoint_not_differentiable :
    ¬ DifferentiableAt ℝ arcsinSqrtTwoExpSubExpSq (Real.log 2) := by
  intro hd
  have hl := ((hasDerivAt_iff_left_right _ _ _).mp hd.hasDerivAt).1
  exact not_tendsto_atBot_of_tendsto_nhds hl arcsinSqrtTwoExpSubExpSq_endpoint_slope_limit


theorem arcsinSqrtTwoExpSubExpSq_differentiable_iff {x : ℝ} (hx : x ∈ arcsinSqrtTwoExpSubExpSqDomain) :
    DifferentiableAt ℝ arcsinSqrtTwoExpSubExpSq x ↔ x ≠ 0 ∧ x < Real.log 2 := by
  constructor
  · intro hd
    refine ⟨fun he ↦ arcsinSqrtTwoExpSubExpSq_corner_not_differentiable (he ▸ hd), ?_⟩
    apply lt_of_le_of_ne hx
    intro he
    exact arcsinSqrtTwoExpSubExpSq_endpoint_not_differentiable (he ▸ hd)
  · rintro ⟨hn, hb⟩
    exact (arcsinSqrtTwoExpSubExpSq_first_second_derivs_nonzero hb hn).1

theorem arcsinSqrtTwoExpSubExpSq_zero_iff {x : ℝ} (hx : x ∈ arcsinSqrtTwoExpSubExpSqDomain) :
    arcsinSqrtTwoExpSubExpSq x = 0 ↔ x = Real.log 2 := by
  rw [arcsinSqrtTwoExpSubExpSq_eq_arccos, Real.arccos_eq_zero]
  have hp := Real.exp_pos x
  have ht := (arcsinSqrtTwoExpSubExpSq_exp_bound x).1.mpr hx
  constructor
  · intro h
    rw [le_abs] at h
    have he : Real.exp x = 2 := by rcases h with h | h <;> linarith
    apply Real.exp_injective
    rw [arcsinSqrtTwoExpSubExpSq_endpoint.2]
    exact he
  · rintro rfl
    norm_num [arcsinSqrtTwoExpSubExpSq_endpoint.2]

theorem arcsinSqrtTwoExpSubExpSq_unique_maximum {x : ℝ} (hx : x ∈ arcsinSqrtTwoExpSubExpSqDomain) :
    arcsinSqrtTwoExpSubExpSq x = Real.pi / 2 ↔ x = 0 := by
  rw [arcsinSqrtTwoExpSubExpSq_eq_arccos, Real.arccos_eq_pi_div_two, abs_eq_zero, sub_eq_zero]
  constructor
  · intro he
    apply Real.exp_injective
    simpa only [Real.exp_zero] using he.symm
  · rintro rfl; simp

theorem arcsinSqrtTwoExpSubExpSq_range (y : ℝ) :
    (∃ x ∈ arcsinSqrtTwoExpSubExpSqDomain, arcsinSqrtTwoExpSubExpSq x = y) ↔
      0 ≤ y ∧ y ≤ Real.pi / 2 := by
  constructor
  · rintro ⟨x, _, rfl⟩; exact arcsinSqrtTwoExpSubExpSq_bounds x
  · intro hy
    have hmem : y ∈ Icc (arcsinSqrtTwoExpSubExpSq (Real.log 2)) (arcsinSqrtTwoExpSubExpSq 0) := by
      simpa only [arcsinSqrtTwoExpSubExpSq_values.1, arcsinSqrtTwoExpSubExpSq_values.2, mem_Icc] using hy
    obtain ⟨x, hx, he⟩ := intermediate_value_Icc' arcsinSqrtTwoExpSubExpSq_endpoint.1.le
      arcsinSqrtTwoExpSubExpSq_continuous.continuousOn hmem
    exact ⟨x, hx.2, he⟩


theorem arcsinSqrtTwoExpSubExpSq_graph_iff (x y : ℝ) :
    (x ∈ arcsinSqrtTwoExpSubExpSqDomain ∧ arcsinSqrtTwoExpSubExpSq x = y) ↔
      x ≤ Real.log 2 ∧ 0 ≤ y ∧ y ≤ Real.pi / 2 ∧
        Real.cos y = |1 - Real.exp x| := by
  constructor
  · rintro ⟨hx, rfl⟩
    refine ⟨hx, (arcsinSqrtTwoExpSubExpSq_bounds x).1, (arcsinSqrtTwoExpSubExpSq_bounds x).2, ?_⟩
    rw [arcsinSqrtTwoExpSubExpSq_eq_arccos]
    apply Real.cos_arccos
    · linarith [abs_nonneg (1 - Real.exp x)]
    · rw [abs_le]
      have hp := Real.exp_pos x
      have ht := (arcsinSqrtTwoExpSubExpSq_exp_bound x).1.mpr hx
      constructor <;> linarith
  · rintro ⟨hx, hy0, hyπ, he⟩
    refine ⟨hx, ?_⟩
    rw [arcsinSqrtTwoExpSubExpSq_eq_arccos, ← he, Real.arccos_cos hy0]
    linarith [Real.pi_pos]

theorem arcsinSqrtTwoExpSubExpSq_limit_bot :
    Tendsto arcsinSqrtTwoExpSubExpSq atBot (𝓝 0) := by
  have hArg : Tendsto (fun x : ℝ ↦ |1 - Real.exp x|) atBot (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero, abs_one] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub Real.tendsto_exp_atBot).abs
  have h := (Real.continuous_arccos.tendsto 1).comp hArg
  simpa only [sub_zero, abs_one, Real.arccos_one, Function.comp_def,
    ← arcsinSqrtTwoExpSubExpSq_eq_arccos] using h

theorem arcsinSqrtTwoExpSubExpSq_endpoint_limit :
    Tendsto arcsinSqrtTwoExpSubExpSq (𝓝[<] (Real.log 2)) (𝓝 0) := by
  simpa only [arcsinSqrtTwoExpSubExpSq_values.2] using
    (arcsinSqrtTwoExpSubExpSq_continuous.tendsto (Real.log 2)).mono_left nhdsWithin_le_nhds

theorem arcsinSqrtTwoExpSubExpSq_domain_tail_bot : ∀ᶠ x : ℝ in atBot, x ∈ arcsinSqrtTwoExpSubExpSqDomain :=
  (eventually_le_atBot (Real.log 2)).mono fun _ hx ↦ hx

theorem arcsinSqrtTwoExpSubExpSq_domain_tail_top_empty :
    atTop ⊓ 𝓟 arcsinSqrtTwoExpSubExpSqDomain = (⊥ : Filter ℝ) := by
  apply inf_principal_eq_bot.mpr
  filter_upwards [eventually_gt_atTop (Real.log 2)] with x hx
  exact not_le.mpr hx


theorem arcsinSqrtTwoExpSubExpSq_asymptotes :
    (∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain a) ∧
      (∀ b : ℝ, HasHorizontalAsymptoteWithin arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain b ↔ b = 0) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain m b) := by
  have hbot : atBot ⊓ 𝓟 arcsinSqrtTwoExpSubExpSqDomain = atBot :=
    inf_eq_left.mpr (le_principal_iff.mpr arcsinSqrtTwoExpSubExpSq_domain_tail_bot)
  refine ⟨fun a ↦ no_vertical_of_continuousAt (arcsinSqrtTwoExpSubExpSq_continuous.continuousAt), ?_, ?_⟩
  · intro b
    rw [hasHorizontalAsymptoteWithin_iff, arcsinSqrtTwoExpSubExpSq_domain_tail_top_empty, hbot]
    constructor
    · rintro (⟨hne, _⟩ | ⟨_, hb⟩)
      · exact False.elim (hne.ne rfl)
      · exact tendsto_nhds_unique hb arcsinSqrtTwoExpSubExpSq_limit_bot
    · rintro rfl; exact Or.inr ⟨inferInstance, arcsinSqrtTwoExpSubExpSq_limit_bot⟩
  · intro m b
    rw [hasObliqueAsymptoteWithin_filter_iff, arcsinSqrtTwoExpSubExpSq_domain_tail_top_empty, hbot]
    rintro ⟨hm, ⟨hne, _⟩ | ⟨_, hb⟩⟩
    · exact hne.ne rfl
    · have he := (affine_parameters_iff (m₀ := 0) (b₀ := 0) tendsto_inv_atBot_zero
        ((eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne)
        (by simpa only [zero_mul, zero_add, sub_zero] using arcsinSqrtTwoExpSubExpSq_limit_bot) m b).mp hb
      exact hm he.1


theorem source_arcsine_exponential_function_investigation :
    (∀ x : ℝ, x ∈ arcsinSqrtTwoExpSubExpSqDomain ↔
      0 ≤ 2 * Real.exp x - (Real.exp x) ^ 2 ∧
        -1 ≤ Real.sqrt (2 * Real.exp x - (Real.exp x) ^ 2) ∧
        Real.sqrt (2 * Real.exp x - (Real.exp x) ^ 2) ≤ 1) ∧
      arcsinSqrtTwoExpSubExpSq 0 = Real.pi / 2 ∧
      arcsinSqrtTwoExpSubExpSq (Real.log 2) = 0 ∧
      (∀ x : ℝ, x < Real.log 2 → x ≠ 0 →
        DifferentiableAt ℝ arcsinSqrtTwoExpSubExpSq x ∧
        DifferentiableAt ℝ (deriv arcsinSqrtTwoExpSubExpSq) x ∧
        deriv arcsinSqrtTwoExpSubExpSq x ≠ 0 ∧ deriv (deriv arcsinSqrtTwoExpSubExpSq) x ≠ 0) ∧
      StrictMonoOn arcsinSqrtTwoExpSubExpSq (Iic (0 : ℝ)) ∧
      StrictAntiOn arcsinSqrtTwoExpSubExpSq (Icc (0 : ℝ) (Real.log 2)) ∧
      (∀ x : ℝ, IsLocalMaximumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain x ↔ x = 0) ∧
      (∀ x : ℝ, IsLocalMinimumOn arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain x ↔ x = Real.log 2) ∧
      ConvexOn ℝ (Iic (0 : ℝ)) arcsinSqrtTwoExpSubExpSq ∧
      ConcaveOn ℝ (Icc (0 : ℝ) (Real.log 2)) arcsinSqrtTwoExpSubExpSq ∧
      (∀ a b c : ℝ, Ioo a b ⊆ arcsinSqrtTwoExpSubExpSqDomain →
        ¬ SourceInflectionOn arcsinSqrtTwoExpSubExpSq a b c) ∧
      HasLeftDerivativeAt arcsinSqrtTwoExpSubExpSq 0 1 ∧
      HasRightDerivativeAt arcsinSqrtTwoExpSubExpSq 0 (-1) ∧
      ¬ DifferentiableAt ℝ arcsinSqrtTwoExpSubExpSq 0 ∧
      Tendsto (fun x : ℝ ↦
        (arcsinSqrtTwoExpSubExpSq x - arcsinSqrtTwoExpSubExpSq (Real.log 2)) / (x - Real.log 2))
          (𝓝[<] (Real.log 2)) atBot ∧
      Tendsto arcsinSqrtTwoExpSubExpSq atBot (𝓝 0) ∧
      Tendsto arcsinSqrtTwoExpSubExpSq (𝓝[<] (Real.log 2)) (𝓝 0) ∧
      (∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain a) ∧
      (∀ b : ℝ, HasHorizontalAsymptoteWithin arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain b ↔ b = 0) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin arcsinSqrtTwoExpSubExpSq arcsinSqrtTwoExpSubExpSqDomain m b) ∧
      (∀ y : ℝ, (∃ x ∈ arcsinSqrtTwoExpSubExpSqDomain, arcsinSqrtTwoExpSubExpSq x = y) ↔ 0 ≤ y ∧ y ≤ Real.pi / 2) ∧
      (∀ x y : ℝ, (x ∈ arcsinSqrtTwoExpSubExpSqDomain ∧ arcsinSqrtTwoExpSubExpSq x = y) ↔
        x ≤ Real.log 2 ∧ 0 ≤ y ∧ y ≤ Real.pi / 2 ∧ Real.cos y = |1 - Real.exp x|) := by
  exact ⟨arcsinSqrtTwoExpSubExpSq_natural_domain_iff, arcsinSqrtTwoExpSubExpSq_values.1,
    arcsinSqrtTwoExpSubExpSq_values.2, fun _ hb hx ↦ arcsinSqrtTwoExpSubExpSq_first_second_derivs_nonzero hb hx,
    arcsinSqrtTwoExpSubExpSq_variation.1, arcsinSqrtTwoExpSubExpSq_variation.2,
    arcsinSqrtTwoExpSubExpSq_extrema.1, arcsinSqrtTwoExpSubExpSq_extrema.2,
    arcsinSqrtTwoExpSubExpSq_convexity.1, arcsinSqrtTwoExpSubExpSq_convexity.2,
    arcsinSqrtTwoExpSubExpSq_no_inflection, arcsinSqrtTwoExpSubExpSq_corner_slopes.1,
    arcsinSqrtTwoExpSubExpSq_corner_slopes.2, arcsinSqrtTwoExpSubExpSq_corner_not_differentiable,
    arcsinSqrtTwoExpSubExpSq_endpoint_slope_limit, arcsinSqrtTwoExpSubExpSq_limit_bot,
    arcsinSqrtTwoExpSubExpSq_endpoint_limit, arcsinSqrtTwoExpSubExpSq_asymptotes.1,
    arcsinSqrtTwoExpSubExpSq_asymptotes.2.1, arcsinSqrtTwoExpSubExpSq_asymptotes.2.2,
    arcsinSqrtTwoExpSubExpSq_range, arcsinSqrtTwoExpSubExpSq_graph_iff⟩

end calculus.Chapter04.Section04ArcsineExponentialFunctionInvestigationExercise
