import calculus.Chapter04.Section02
import calculus.Chapter04.Section01Parametric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# §4.2 Bài tập 4: đạo hàm đồ thị cycloid

Nguồn: dòng 854–862.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter04.Section02Cycloid
open calculus.Chapter04.Section01Parametric

noncomputable def cycloidX (r t : ℝ) : ℝ := r * (t - Real.sin t)
noncomputable def cycloidY (r t : ℝ) : ℝ := r * (1 - Real.cos t)


theorem abs_sin_difference_lt {x y : ℝ} (hxy : x ≠ y) : |Real.sin x - Real.sin y| < |x - y| := by
  have hh : (x - y) / 2 ≠ 0 := by intro h; exact hxy (by linarith)
  have hs := Real.abs_sin_lt_abs hh
  rw [Real.sin_sub_sin, abs_mul, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |Real.sin ((x - y) / 2)| * |Real.cos ((x + y) / 2)| ≤
        2 * |Real.sin ((x - y) / 2)| := by
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    _ < 2 * |(x - y) / 2| := mul_lt_mul_of_pos_left hs (by norm_num)
    _ = |x - y| := by rw [abs_div]; norm_num; ring


theorem cycloidX_injective {r : ℝ} (hr : r ≠ 0) : Function.Injective (cycloidX r) := by
  have hm : StrictMono (fun t : ℝ ↦ t - Real.sin t) := by
    intro x y hxy
    have hs := abs_sin_difference_lt (ne_of_gt hxy : y ≠ x)
    rw [abs_of_pos (sub_pos.mpr hxy)] at hs
    have hl := le_abs_self (Real.sin y - Real.sin x)
    linarith
  intro x y he
  apply hm.injective
  apply mul_left_cancel₀ hr
  exact he


noncomputable def cycloidParameterFromAbscissa (r : ℝ) : ℝ → ℝ := Function.invFun (cycloidX r)
noncomputable def cycloidGraphFunction (r : ℝ) : ℝ → ℝ := cycloidY r ∘ cycloidParameterFromAbscissa r

theorem cycloidParameterFromAbscissa_left_inverse {r : ℝ} (hr : r ≠ 0) :
    Function.LeftInverse (cycloidParameterFromAbscissa r) (cycloidX r) :=
  Function.leftInverse_invFun (cycloidX_injective hr)

theorem cycloidGraphFunction_apply_cycloidX {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    cycloidGraphFunction r (cycloidX r t) = cycloidY r t := by
  unfold cycloidGraphFunction
  rw [Function.comp_apply, cycloidParameterFromAbscissa_left_inverse hr t]


theorem cycloid_coordinate_derivatives (r t : ℝ) :
    HasDerivAt (cycloidX r) (r * (1 - Real.cos t)) t ∧
      HasDerivAt (cycloidY r) (r * Real.sin t) t := by
  constructor
  · exact ((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul r
  · convert! ((Real.hasDerivAt_cos t).const_sub 1).const_mul r using 1
    ring


theorem cycloid_regular_parameter_iff {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    deriv (cycloidX r) t ≠ 0 ↔ 1 - Real.cos t ≠ 0 := by
  rw [(cycloid_coordinate_derivatives r t).1.deriv, mul_ne_zero_iff]
  exact and_iff_right hr


theorem cycloidParameterFromAbscissa_hasDerivAt {r t : ℝ} (hr : r ≠ 0) (ht : 1 - Real.cos t ≠ 0) :
    HasDerivAt (cycloidParameterFromAbscissa r) (1 / (r * (1 - Real.cos t))) (cycloidX r t) := by
  have hφ : DifferentiableOn ℝ (cycloidX r) (Ioo (t - 1) (t + 1)) :=
    fun s _ ↦ (cycloid_coordinate_derivatives r s).1.differentiableAt.differentiableWithinAt
  have hgf : LeftInvOn (cycloidParameterFromAbscissa r) (cycloidX r) (Ioo (t - 1) (t + 1)) :=
    fun s _ ↦ cycloidParameterFromAbscissa_left_inverse hr s
  have hm : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hn : deriv (cycloidX r) t ≠ 0 := (cycloid_regular_parameter_iff hr t).mpr ht
  have hg := parametric_inverse_hasDerivAt hφ hgf hm hn
  simpa only [(cycloid_coordinate_derivatives r t).1.deriv] using hg

/-- Bài 4.2.4(a): đạo hàm của đồ thị tại điểm chính quy, với `r ≠ 0`. -/
theorem cycloidGraphFunction_hasDerivAt {r t : ℝ} (hr : r ≠ 0) (ht : 1 - Real.cos t ≠ 0) :
    HasDerivAt (cycloidGraphFunction r) (Real.sin t / (1 - Real.cos t)) (cycloidX r t) := by
  have hg := cycloidParameterFromAbscissa_hasDerivAt hr ht
  have hy : HasDerivAt (cycloidY r) (r * Real.sin t) (cycloidParameterFromAbscissa r (cycloidX r t)) := by
    rw [cycloidParameterFromAbscissa_left_inverse hr]
    exact (cycloid_coordinate_derivatives r t).2
  have hf := hy.comp (cycloidX r t) hg
  apply hf.congr_deriv
  field_simp [hr]


theorem cycloidParameterFromAbscissa_eventually_right_inverse {r t : ℝ} (hr : r ≠ 0) :
    ∀ᶠ x in 𝓝 (cycloidX r t), cycloidX r (cycloidParameterFromAbscissa r x) = x := by
  have hφ : ContinuousOn (cycloidX r) (Ioo (t - 1) (t + 1)) :=
    fun s _ ↦ (cycloid_coordinate_derivatives r s).1.continuousAt.continuousWithinAt
  have hi : InjOn (cycloidX r) (Ioo (t - 1) (t + 1)) := (cycloidX_injective hr).injOn
  have hm : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hJ := interval_image_mem_nhds hm hφ hi
  filter_upwards [hJ] with x hx
  obtain ⟨s, _, rfl⟩ := hx
  rw [cycloidParameterFromAbscissa_left_inverse hr]

/-- Bài 4.2.4(b): đạo hàm cấp hai của đồ thị cycloid, với mẫu chứa `(φ′)³`. -/
theorem cycloidGraphFunction_deriv_hasDerivAt {r t : ℝ} (hr : r ≠ 0) (ht : 1 - Real.cos t ≠ 0) :
    HasDerivAt (deriv (cycloidGraphFunction r)) (-1 / (r * (1 - Real.cos t) ^ 2)) (cycloidX r t) := by
  have hg := cycloidParameterFromAbscissa_hasDerivAt hr ht
  have hs : HasDerivAt (fun s : ℝ ↦ Real.sin s / (1 - Real.cos s))
      (-1 / (1 - Real.cos t)) t := by
    have hh := (Real.hasDerivAt_sin t).div ((Real.hasDerivAt_cos t).const_sub 1) ht
    apply hh.congr_deriv
    field_simp [ht]
    have hid := Real.sin_sq_add_cos_sq t
    nlinarith
  have hs' : HasDerivAt (fun s : ℝ ↦ Real.sin s / (1 - Real.cos s))
      (-1 / (1 - Real.cos t)) (cycloidParameterFromAbscissa r (cycloidX r t)) := by
    rw [cycloidParameterFromAbscissa_left_inverse hr]
    exact hs
  have hc : HasDerivAt ((fun s : ℝ ↦ Real.sin s / (1 - Real.cos s)) ∘ cycloidParameterFromAbscissa r)
      (-1 / (r * (1 - Real.cos t) ^ 2)) (cycloidX r t) := by
    have hh := hs'.comp (cycloidX r t) hg
    apply hh.congr_deriv
    field_simp [hr, ht]
  apply hc.congr_of_eventuallyEq
  have hreg : ∀ᶠ s in 𝓝 t, 1 - Real.cos s ≠ 0 :=
    (show ContinuousAt (fun s : ℝ ↦ 1 - Real.cos s) t from
      continuous_const.continuousAt.sub Real.continuous_cos.continuousAt).eventually_ne ht
  have hreg' : ∀ᶠ x in 𝓝 (cycloidX r t), 1 - Real.cos (cycloidParameterFromAbscissa r x) ≠ 0 := by
    have htc : Tendsto (cycloidParameterFromAbscissa r) (𝓝 (cycloidX r t)) (𝓝 t) := by
      simpa only [cycloidParameterFromAbscissa_left_inverse hr t] using hg.continuousAt.tendsto
    exact htc.eventually hreg
  filter_upwards [hreg', cycloidParameterFromAbscissa_eventually_right_inverse (t := t) hr] with x hx hright
  change deriv (cycloidGraphFunction r) x = Real.sin (cycloidParameterFromAbscissa r x) / (1 - Real.cos (cycloidParameterFromAbscissa r x))
  simpa only [hright] using (cycloidGraphFunction_hasDerivAt hr hx).deriv

end calculus.Chapter04.Section02Cycloid
