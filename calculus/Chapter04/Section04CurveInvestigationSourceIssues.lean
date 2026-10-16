import calculus.Chapter04.Section04ConvexityAndInflection
import calculus.Chapter03.Section03Supplement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Các lỗi trong khảo sát hàm số và ví dụ tham số

Nguồn: dòng 1952–1957, dòng 2002–2052, dòng 2178, dòng 2247–2250, dòng 2653. Tiếp tuyến đứng tại điểm nhọn không đồng nghĩa với đạo hàm vô cùng hai phía.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04CurveInvestigationSourceIssues
open Set Filter calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section01Derivatives calculus.Chapter04.Section01Higher
open calculus.Chapter03.Section03Supplement
open scoped Topology


theorem one_sided_le_punctured_interval {a b x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) :
    (𝓝[<] x₀ ≤ 𝓝[(Ioo a b) \ {x₀}] x₀) ∧
      (𝓝[>] x₀ ≤ 𝓝[(Ioo a b) \ {x₀}] x₀) := by
  constructor
  · change 𝓝[<] x₀ ≤ 𝓝 x₀ ⊓ 𝓟 ((Ioo a b) \ {x₀})
    refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
    filter_upwards [Filter.Eventually.filter_mono
      (show 𝓝[<] x₀ ≤ 𝓝 x₀ from nhdsWithin_le_nhds)
      (show ∀ᶠ x in 𝓝 x₀, x ∈ Ioo a b from Ioo_mem_nhds hx₀.1 hx₀.2),
      self_mem_nhdsWithin] with x hx hlt
    exact ⟨hx, ne_of_lt hlt⟩
  · change 𝓝[>] x₀ ≤ 𝓝 x₀ ⊓ 𝓟 ((Ioo a b) \ {x₀})
    refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
    filter_upwards [Filter.Eventually.filter_mono
      (show 𝓝[>] x₀ ≤ 𝓝 x₀ from nhdsWithin_le_nhds)
      (show ∀ᶠ x in 𝓝 x₀, x ∈ Ioo a b from Ioo_mem_nhds hx₀.1 hx₀.2),
      self_mem_nhdsWithin] with x hx hgt
    exact ⟨hx, ne_of_gt hgt⟩


theorem local_minimum_not_source_infinite_derivative {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo a b) (hm : IsLocalMin f x₀) :
    ¬ HasInfiniteDerivativeWithinAt f (Ioo a b) x₀ := by
  have hs := one_sided_le_punctured_interval hx₀
  change ∀ᶠ x in 𝓝 x₀, f x₀ ≤ f x at hm
  rintro (ht | hb)
  · obtain ⟨x, ⟨hxq, hxm⟩, hxs⟩ :=
      (((ht.mono_left hs.1).eventually_gt_atTop 0).and
        (hm.filter_mono nhdsWithin_le_nhds) |>.and self_mem_nhdsWithin).exists
    have hnonpos : (f x - f x₀) / (x - x₀) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxm) (sub_nonpos.mpr hxs.le)
    linarith
  · obtain ⟨x, ⟨hxq, hxm⟩, hxs⟩ :=
      (((hb.mono_left hs.2).eventually_lt_atBot 0).and
        (hm.filter_mono nhdsWithin_le_nhds) |>.and self_mem_nhdsWithin).exists
    have hnonneg : 0 ≤ (f x - f x₀) / (x - x₀) :=
      div_nonneg (sub_nonneg.mpr hxm) (sub_nonneg.mpr hxs.le)
    linarith


theorem local_maximum_not_source_infinite_derivative {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo a b) (hm : IsLocalMax f x₀) :
    ¬ HasInfiniteDerivativeWithinAt f (Ioo a b) x₀ := by
  have hs := one_sided_le_punctured_interval hx₀
  change ∀ᶠ x in 𝓝 x₀, f x ≤ f x₀ at hm
  rintro (ht | hb)
  · obtain ⟨x, ⟨hxq, hxm⟩, hxs⟩ :=
      (((ht.mono_left hs.2).eventually_gt_atTop 0).and
        (hm.filter_mono nhdsWithin_le_nhds) |>.and self_mem_nhdsWithin).exists
    have hnonpos : (f x - f x₀) / (x - x₀) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxm) (sub_nonneg.mpr hxs.le)
    linarith
  · obtain ⟨x, ⟨hxq, hxm⟩, hxs⟩ :=
      (((hb.mono_left hs.1).eventually_lt_atBot 0).and
        (hm.filter_mono nhdsWithin_le_nhds) |>.and self_mem_nhdsWithin).exists
    have hnonneg : 0 ≤ (f x - f x₀) / (x - x₀) :=
      div_nonneg_of_nonpos (sub_nonpos.mpr hxm) (sub_nonpos.mpr hxs.le)
    linarith


def patchedCube (x : ℝ) : ℝ := if x = 0 then 1 else x ^ 3

theorem patchedCube_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt patchedCube (3 * x ^ 2) x := by
  have he : patchedCube =ᶠ[𝓝 x] (fun y : ℝ ↦ y ^ 3) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact if_neg hy
  simpa using (hasDerivAt_pow 3 x).congr_of_eventuallyEq he

theorem patchedCube_deriv {x : ℝ} (hx : x ≠ 0) : deriv patchedCube x = 3 * x ^ 2 :=
  (patchedCube_hasDerivAt hx).deriv

theorem patchedCube_second_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (deriv patchedCube) (6 * x) x := by
  have he : deriv patchedCube =ᶠ[𝓝 x] (fun y : ℝ ↦ 3 * y ^ 2) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact patchedCube_deriv hy
  have h : HasDerivAt (fun y : ℝ ↦ (3 : ℝ) * y ^ 2)
      ((3 : ℝ) * (((2 : ℕ) : ℝ) * x ^ ((2 : ℕ) - 1))) x :=
    HasDerivAt.const_mul (3 : ℝ) (hasDerivAt_pow 2 x)
  apply HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h he)
  norm_num; ring

theorem patchedCube_second_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv patchedCube) x = 6 * x := (patchedCube_second_hasDerivAt hx).deriv

theorem patchedCube_not_differentiable_zero : ¬ DifferentiableAt ℝ patchedCube 0 := by
  intro hd
  have hc := hd.continuousAt.tendsto.mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hp : Tendsto patchedCube (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ ↦ x ^ 3) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using
        ((continuousAt_pow (0 : ℝ) 3).tendsto.mono_left
          (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (if_neg (show x ≠ 0 from hx)).symm
  have he := tendsto_nhds_unique hc hp
  norm_num [patchedCube] at he

theorem patchedCube_local_maximum_zero : IsLocalMax patchedCube 0 := by
  change ∀ᶠ x in 𝓝 (0 : ℝ), patchedCube x ≤ patchedCube 0
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with x hx
  simp only [patchedCube]
  split_ifs with h
  · exact le_rfl
  · have ho : Odd (3 : ℕ) := by decide
    have hp : x ^ 3 < (1 : ℝ) ^ 3 := ho.pow_lt_pow.mpr hx.2
    norm_num at hp
    exact hp.le


theorem printed_inflection_test_counterexample :
    DifferentiableToOrderOn 2 patchedCube (Ioo (-1) 0) ∧
      DifferentiableToOrderOn 2 patchedCube (Ioo 0 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 0, deriv (deriv patchedCube) x < 0) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 0 < deriv (deriv patchedCube) x) ∧
      ¬ SourceInflectionOn patchedCube (-1) 1 0 := by
  have hleft : DifferentiableToOrderOn 2 patchedCube (Ioo (-1) 0) := by
    apply (differentiableToOrderOn_two patchedCube isOpen_Ioo).mpr
    constructor <;> intro x hx
    · exact (patchedCube_hasDerivAt (ne_of_lt hx.2)).differentiableAt.differentiableWithinAt
    · exact (patchedCube_second_hasDerivAt (ne_of_lt hx.2)).differentiableAt.differentiableWithinAt
  have hright : DifferentiableToOrderOn 2 patchedCube (Ioo 0 1) := by
    apply (differentiableToOrderOn_two patchedCube isOpen_Ioo).mpr
    constructor <;> intro x hx
    · exact (patchedCube_hasDerivAt (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
    · exact (patchedCube_second_hasDerivAt (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
  refine ⟨hleft, hright, ?_, ?_, ?_⟩
  · intro x hx
    rw [patchedCube_second_deriv (ne_of_lt hx.2)]
    linarith [hx.2]
  · intro x hx
    rw [patchedCube_second_deriv (ne_of_gt hx.1)]
    linarith [hx.1]
  · intro hi
    rcases hi.2.2.1 with hd | hinf
    · exact patchedCube_not_differentiable_zero hd
    · exact local_maximum_not_source_infinite_derivative (by norm_num)
        patchedCube_local_maximum_zero hinf


def cubeRootCubeSubThreeXAddTwo (x : ℝ) : ℝ := signedCubeRoot (x ^ 3 - 3 * x + 2)

theorem cubeRootCubeSubThreeXAddTwo_value_zero : cubeRootCubeSubThreeXAddTwo 0 = signedCubeRoot 2 := by
  norm_num [cubeRootCubeSubThreeXAddTwo]

theorem cubeRootCubeSubThreeXAddTwo_value_one : cubeRootCubeSubThreeXAddTwo 1 = 0 := by
  unfold cubeRootCubeSubThreeXAddTwo
  norm_num
  exact signedCubeRoot_unique (by norm_num)

/-- Dòng 2178: tung độ tại `x = 0` khác `∛4` ghi trong hình. -/
theorem printed_cube_root_y_intercept_false : cubeRootCubeSubThreeXAddTwo 0 ≠ signedCubeRoot 4 := by
  intro he
  rw [cubeRootCubeSubThreeXAddTwo_value_zero] at he
  have hp := congrArg (fun x : ℝ ↦ x ^ 3) he
  norm_num [signedCubeRoot_cube] at hp


theorem cubeRootCubeSubThreeXAddTwo_local_minimum_one : IsLocalMin cubeRootCubeSubThreeXAddTwo 1 := by
  change ∀ᶠ x in 𝓝 (1 : ℝ), cubeRootCubeSubThreeXAddTwo 1 ≤ cubeRootCubeSubThreeXAddTwo x
  rw [cubeRootCubeSubThreeXAddTwo_value_one]
  filter_upwards [Ioi_mem_nhds (by norm_num : (-2 : ℝ) < 1)] with x hx
  have hfactor : x ^ 3 - 3 * x + 2 = (x + 2) * (x - 1) ^ 2 := by ring
  have hp : 0 ≤ x ^ 3 - 3 * x + 2 := by
    change -2 < x at hx
    rw [hfactor]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have ho : Odd (3 : ℕ) := by decide
  apply ho.pow_le_pow.mp
  simpa [cubeRootCubeSubThreeXAddTwo, signedCubeRoot_cube] using hp

/-- Dòng 2052: tại 1 không có đạo hàm vô cùng hai phía, dù điểm nhọn có hướng tiếp tuyến đứng. -/
theorem printed_cube_root_infinite_derivative_at_one_false :
    ¬ HasInfiniteDerivativeWithinAt cubeRootCubeSubThreeXAddTwo (Ioo (-2) 2) 1 :=
  local_minimum_not_source_infinite_derivative (by norm_num) cubeRootCubeSubThreeXAddTwo_local_minimum_one


def astroidX (a t : ℝ) : ℝ := a * Real.cos t ^ 3
def astroidY (a t : ℝ) : ℝ := a * Real.sin t ^ 3

theorem astroidX_hasDerivAt (a t : ℝ) :
    HasDerivAt (astroidX a) (-3 * a * Real.cos t ^ 2 * Real.sin t) t := by
  have h : HasDerivAt (fun y : ℝ ↦ a * Real.cos y ^ 3)
      (a * (((3 : ℕ) : ℝ) * Real.cos t ^ ((3 : ℕ) - 1) * (-Real.sin t))) t :=
    HasDerivAt.const_mul a (HasDerivAt.fun_pow (Real.hasDerivAt_cos t) 3)
  apply HasDerivAt.congr_deriv
    (HasDerivAt.congr_of_eventuallyEq h (Eventually.of_forall fun _ ↦ rfl))
  norm_num; ring

theorem astroidY_hasDerivAt (a t : ℝ) :
    HasDerivAt (astroidY a) (3 * a * Real.sin t ^ 2 * Real.cos t) t := by
  have h : HasDerivAt (fun y : ℝ ↦ a * Real.sin y ^ 3)
      (a * (((3 : ℕ) : ℝ) * Real.sin t ^ ((3 : ℕ) - 1) * Real.cos t)) t :=
    HasDerivAt.const_mul a (HasDerivAt.fun_pow (Real.hasDerivAt_sin t) 3)
  apply HasDerivAt.congr_deriv
    (HasDerivAt.congr_of_eventuallyEq h (Eventually.of_forall fun _ ↦ rfl))
  norm_num; ring


theorem astroid_counterexample_regular :
    (0 : ℝ) < 1 ∧ deriv (astroidX 1) (Real.pi / 4) ≠ 0 ∧
      deriv (astroidY 1) (Real.pi / 4) ≠ 0 := by
  have hs : 0 < Real.sin (Real.pi / 4) := by rw [Real.sin_pi_div_four]; positivity
  have hc : 0 < Real.cos (Real.pi / 4) := by rw [Real.cos_pi_div_four]; positivity
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [(astroidX_hasDerivAt 1 (Real.pi / 4)).deriv]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc.ne')) hs.ne'
  · rw [(astroidY_hasDerivAt 1 (Real.pi / 4)).deriv]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs.ne')) hc.ne'

/-- Dòng 2247: phản ví dụ `a=1,t=π/4` bác bỏ dấu âm in trong sách. -/
theorem printed_astroid_y_derivative_false :
    deriv (astroidY 1) (Real.pi / 4) ≠
      -3 * (1 : ℝ) * Real.sin (Real.pi / 4) ^ 2 * Real.cos (Real.pi / 4) := by
  rw [(astroidY_hasDerivAt 1 (Real.pi / 4)).deriv]
  have hp : 0 < 3 * (1 : ℝ) * Real.sin (Real.pi / 4) ^ 2 * Real.cos (Real.pi / 4) := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    positivity
  intro he
  nlinarith


theorem astroid_actual_slope_pi_div_four :
    deriv (astroidY 1) (Real.pi / 4) / deriv (astroidX 1) (Real.pi / 4) = -1 := by
  rw [(astroidY_hasDerivAt 1 (Real.pi / 4)).deriv,
    (astroidX_hasDerivAt 1 (Real.pi / 4)).deriv,
    Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [hne]

/-- Dòng 2250: dấu của hệ số góc sai tại `a = 1`, `t = π/4`. -/
theorem printed_astroid_slope_false :
    deriv (astroidY 1) (Real.pi / 4) / deriv (astroidX 1) (Real.pi / 4) ≠ Real.tan (Real.pi / 4) := by
  rw [astroid_actual_slope_pi_div_four, Real.tan_pi_div_four]
  norm_num


def roseX (t : ℝ) : ℝ := Real.cos (2 * t) * Real.cos t
def roseY (t : ℝ) : ℝ := Real.cos (2 * t) * Real.sin t

theorem rose_pi_div_two_coordinates : roseX (Real.pi / 2) = 0 ∧ roseY (Real.pi / 2) = -1 := by
  have hangle : 2 * (Real.pi / 2) = Real.pi := by ring
  simp only [roseX, roseY, hangle]
  norm_num

/-- Dòng 2653: tại `π/2`, điểm là `(0,−1)`, thay cho `(0,1)` in trong sách. -/
theorem printed_rose_pi_div_two_point_false :
    ¬ (roseX (Real.pi / 2) = 0 ∧ roseY (Real.pi / 2) = 1) := by
  rw [rose_pi_div_two_coordinates.2]
  norm_num

end calculus.Chapter04.Section04CurveInvestigationSourceIssues
