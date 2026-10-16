import calculus.Chapter04.Section02ParametricRepair
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Bài 29: đạo hàm của đồ thị cục bộ theo tham số

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 701–708.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01ParametricExercises
open Set Filter Function Asymptotics calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section01Parametric calculus.Chapter04.Section02ParametricRepair
open scoped Topology ContDiff


theorem exists_regular_parameter_interval {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (t : ℝ) (hne : deriv φ t ≠ 0) :
    ∃ a b : ℝ, ∃ g : ℝ → ℝ, t ∈ Ioo a b ∧ LeftInvOn g φ (Ioo a b) ∧
      (∀ u ∈ Ioo a b, deriv φ u ≠ 0) := by
  have hc : Continuous (deriv φ) := hφ.continuous_deriv (by norm_num)
  rcases lt_or_gt_of_ne hne with hn | hp
  · obtain ⟨a, b, ht, hs⟩ :=
      (hc.continuousAt.eventually (Iio_mem_nhds hn)).exists_Ioo_subset
    have hm : StrictAntiOn φ (Ioo a b) :=
      strictAntiOn_of_deriv_neg (convex_Ioo a b) hφ.continuous.continuousOn
        (fun u hu ↦ hs (interior_subset hu))
    exact ⟨a, b, invFunOn φ (Ioo a b), ht, hm.injOn.leftInvOn_invFunOn,
      fun u hu ↦ (hs hu).ne⟩
  · obtain ⟨a, b, ht, hs⟩ :=
      (hc.continuousAt.eventually (Ioi_mem_nhds hp)).exists_Ioo_subset
    have hm : StrictMonoOn φ (Ioo a b) :=
      strictMonoOn_of_deriv_pos (convex_Ioo a b) hφ.continuous.continuousOn
        (fun u hu ↦ hs (interior_subset hu))
    exact ⟨a, b, invFunOn φ (Ioo a b), ht, hm.injOn.leftInvOn_invFunOn,
      fun u hu ↦ (hs hu).ne'⟩


theorem exists_local_parametric_derivatives {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (t : ℝ) (hne : deriv φ t ≠ 0) :
    ∃ a b : ℝ, ∃ g : ℝ → ℝ, t ∈ Ioo a b ∧ LeftInvOn g φ (Ioo a b) ∧
      HasDerivAt (ψ ∘ g) (deriv ψ t / deriv φ t) (φ t) ∧
      HasDerivAt (deriv (ψ ∘ g))
        ((deriv φ t * deriv (deriv ψ) t - deriv (deriv φ) t * deriv ψ t) /
          (deriv φ t) ^ 3) (φ t) := by
  obtain ⟨a, b, g, ht, hg, hn⟩ := exists_regular_parameter_interval hφ t hne
  have hφ2 : DifferentiableToOrderOn 2 φ (Ioo a b) :=
    ((domainC_iff_contDiffOn 2 φ isOpen_Ioo).mpr hφ.contDiffOn).1
  have hψ2 : DifferentiableToOrderOn 2 ψ (Ioo a b) :=
    ((domainC_iff_contDiffOn 2 ψ isOpen_Ioo).mpr hψ.contDiffOn).1
  exact ⟨a, b, g, ht, hg,
    parametric_derivative (hφ.differentiable (by norm_num)).differentiableOn
      (hψ.differentiable (by norm_num)).differentiableOn hg hn ht,
    parametric_second_derivative hφ2 hψ2 hg hn ht⟩


def polynomialX (t : ℝ) : ℝ := 2 * t - t ^ 2
def polynomialY (t : ℝ) : ℝ := 3 * t - t ^ 3

theorem polynomialX_hasDerivAt (t : ℝ) : HasDerivAt polynomialX (2 - 2 * t) t := by
  change HasDerivAt (fun u : ℝ ↦ 2 * u - u ^ 2) (2 - 2 * t) t
  apply (((hasDerivAt_id t).const_mul (2 : ℝ)).sub (hasDerivAt_pow 2 t)).congr_deriv
  norm_num

theorem polynomialY_hasDerivAt (t : ℝ) : HasDerivAt polynomialY (3 - 3 * t ^ 2) t := by
  change HasDerivAt (fun u : ℝ ↦ 3 * u - u ^ 3) (3 - 3 * t ^ 2) t
  apply (((hasDerivAt_id t).const_mul (3 : ℝ)).sub (hasDerivAt_pow 3 t)).congr_deriv
  norm_num

theorem polynomialX_deriv : deriv polynomialX = fun t ↦ 2 - 2 * t := by
  funext t
  exact (polynomialX_hasDerivAt t).deriv

theorem polynomialY_deriv : deriv polynomialY = fun t ↦ 3 - 3 * t ^ 2 := by
  funext t
  exact (polynomialY_hasDerivAt t).deriv

theorem polynomialX_second_deriv (t : ℝ) : deriv (deriv polynomialX) t = -2 := by
  rw [polynomialX_deriv]
  simp

theorem polynomialY_second_deriv (t : ℝ) : deriv (deriv polynomialY) t = -6 * t := by
  rw [polynomialY_deriv]
  have h : HasDerivAt (fun u : ℝ ↦ 3 - 3 * u ^ 2) (-6 * t) t := by
    apply (((hasDerivAt_pow 2 t).const_mul (3 : ℝ)).const_sub 3).congr_deriv
    ring
  exact h.deriv

/-- Bài 29(a): công thức trên cả hai nhánh có đạo hàm tọa độ khác 0. -/
theorem polynomial_parametric_derivatives (t : ℝ) (ht : t ≠ 1) :
    ∃ a b : ℝ, ∃ g : ℝ → ℝ, t ∈ Ioo a b ∧ LeftInvOn g polynomialX (Ioo a b) ∧
      HasDerivAt (polynomialY ∘ g) ((3 / 2 : ℝ) * (t + 1)) (polynomialX t) ∧
      HasDerivAt (deriv (polynomialY ∘ g)) (3 / (4 * (1 - t))) (polynomialX t) := by
  have hφ : ContDiff ℝ 2 polynomialX := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ 2 * u - u ^ 2)
    exact ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ (2 : ℝ))).mul contDiff_id).sub
      (contDiff_id.pow 2)
  have hψ : ContDiff ℝ 2 polynomialY := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ 3 * u - u ^ 3)
    exact ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ (3 : ℝ))).mul contDiff_id).sub
      (contDiff_id.pow 3)
  have hn : deriv polynomialX t ≠ 0 := by rw [polynomialX_deriv]; intro h; apply ht; linarith
  obtain ⟨a, b, g, ha, hg, hd1, hd2⟩ := exists_local_parametric_derivatives hφ hψ t hn
  refine ⟨a, b, g, ha, hg, hd1.congr_deriv ?_, hd2.congr_deriv ?_⟩
  · rw [polynomialX_deriv, polynomialY_deriv]
    have hden : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have hd : 2 - 2 * t ≠ 0 := by simpa only [polynomialX_deriv] using hn
    field_simp [hden, hd]
    ring
  · rw [polynomialX_second_deriv, polynomialY_second_deriv,
      polynomialX_deriv, polynomialY_deriv]
    have hden : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have hd : 2 - 2 * t ≠ 0 := by simpa only [polynomialX_deriv] using hn
    field_simp [hden, hd]
    ring


theorem polynomial_curve_not_local_graph_at_one (δ : ℝ) (hδ : 0 < δ) :
    ∃ u ∈ Ioo (1 - δ) (1 + δ), ∃ v ∈ Ioo (1 - δ) (1 + δ),
      polynomialX u = polynomialX v ∧ polynomialY u ≠ polynomialY v := by
  let h := δ / 2
  have hh : 0 < h := by dsimp [h]; positivity
  refine ⟨1 - h, ⟨by dsimp [h]; linarith, by linarith⟩,
    1 + h, ⟨by linarith, by dsimp [h]; linarith⟩, ?_, ?_⟩
  · simp only [polynomialX]
    ring
  · intro he
    have hi : polynomialY (1 + h) - polynomialY (1 - h) = -2 * h ^ 3 := by
      simp only [polynomialY]
      ring
    rw [← he, sub_self] at hi
    have hp := pow_pos hh 3
    linarith

/-- Hai hàm tọa độ của cycloid trong Bài 29(b), với mọi dấu của `r`. -/
def cycloidX (r t : ℝ) : ℝ := r * (t - Real.sin t)
def cycloidY (r t : ℝ) : ℝ := r * (1 - Real.cos t)

theorem cycloidX_hasDerivAt (r t : ℝ) :
    HasDerivAt (cycloidX r) (r * (1 - Real.cos t)) t :=
  ((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul r

theorem cycloidY_hasDerivAt (r t : ℝ) : HasDerivAt (cycloidY r) (r * Real.sin t) t := by
  change HasDerivAt (fun u : ℝ ↦ r * (1 - Real.cos u)) (r * Real.sin t) t
  apply (((Real.hasDerivAt_cos t).const_sub 1).const_mul r).congr_deriv
  simp

theorem cycloidX_deriv (r : ℝ) : deriv (cycloidX r) = fun t ↦ r * (1 - Real.cos t) := by
  funext t
  exact (cycloidX_hasDerivAt r t).deriv

theorem cycloidY_deriv (r : ℝ) : deriv (cycloidY r) = fun t ↦ r * Real.sin t := by
  funext t
  exact (cycloidY_hasDerivAt r t).deriv

theorem cycloidX_second_deriv (r t : ℝ) :
    deriv (deriv (cycloidX r)) t = r * Real.sin t := by
  rw [cycloidX_deriv]
  simp

theorem cycloidY_second_deriv (r t : ℝ) :
    deriv (deriv (cycloidY r)) t = r * Real.cos t := by
  rw [cycloidY_deriv]
  exact ((Real.hasDerivAt_sin t).const_mul r).deriv

/-- Bài 29(b): đồ thị khả vi cục bộ tại mọi tham số có đạo hàm hoành độ khác 0. -/
theorem cycloid_parametric_derivatives (r t : ℝ) (hr : r ≠ 0) (ht : Real.cos t ≠ 1) :
    ∃ a b : ℝ, ∃ g : ℝ → ℝ, t ∈ Ioo a b ∧ LeftInvOn g (cycloidX r) (Ioo a b) ∧
      HasDerivAt (cycloidY r ∘ g) (Real.sin t / (1 - Real.cos t)) (cycloidX r t) ∧
      HasDerivAt (deriv (cycloidY r ∘ g))
        (-1 / (r * (1 - Real.cos t) ^ 2)) (cycloidX r t) := by
  have hφ : ContDiff ℝ 2 (cycloidX r) := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ r * (u - Real.sin u))
    exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ r)).mul
      (contDiff_id.sub Real.contDiff_sin)
  have hψ : ContDiff ℝ 2 (cycloidY r) := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ r * (1 - Real.cos u))
    exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ r)).mul
      ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ (1 : ℝ))).sub Real.contDiff_cos)
  have hc : 1 - Real.cos t ≠ 0 := sub_ne_zero.mpr ht.symm
  have hn : deriv (cycloidX r) t ≠ 0 := by rw [cycloidX_deriv]; exact mul_ne_zero hr hc
  obtain ⟨a, b, g, ha, hg, hd1, hd2⟩ := exists_local_parametric_derivatives hφ hψ t hn
  refine ⟨a, b, g, ha, hg, hd1.congr_deriv ?_, hd2.congr_deriv ?_⟩
  · rw [cycloidX_deriv, cycloidY_deriv]
    field_simp [hr, hc]
  · rw [cycloidX_second_deriv, cycloidY_second_deriv, cycloidX_deriv, cycloidY_deriv]
    field_simp [hr, hc]
    nlinarith [Real.sin_sq_add_cos_sq t]


theorem cycloid_coordinate_singular_iff (r t : ℝ) (hr : r ≠ 0) :
    deriv (cycloidX r) t = 0 ↔ ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = t := by
  rw [cycloidX_deriv, mul_eq_zero]
  simp only [hr, false_or]
  exact (sub_eq_zero.trans eq_comm).trans (Real.cos_eq_one_iff t)


theorem taylor_two_with_zero_first {η : ℝ → ℝ} {t : ℝ}
    (hη : deriv η t = 0) (u : ℝ) :
    taylorWithinEval η 2 univ t u = η t + deriv (deriv η) t / 2 * (u - t) ^ 2 := by
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, iteratedDerivWithin_univ, iteratedDeriv_succ, hη]
  ring


theorem second_order_parameter_no_differentiable_graph {φ ψ f : ℝ → ℝ} {t : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hφ1 : deriv φ t = 0) (hφ2 : deriv (deriv φ) t = 0)
    (hψ1 : deriv ψ t = 0) (hψ2 : deriv (deriv ψ) t ≠ 0)
    (hgraph : ψ =ᶠ[𝓝 t] f ∘ φ) : ¬ DifferentiableAt ℝ f (φ t) := by
  intro hf
  have hφo : (fun u : ℝ ↦ φ u - φ t) =o[𝓝 t] (fun u : ℝ ↦ (u - t) ^ 2) := by
    have ht := taylor_isLittleO_univ (x₀ := t) hφ
    exact ht.congr_left (fun u ↦ by rw [taylor_two_with_zero_first hφ1, hφ2]; ring)
  have hb : (fun u : ℝ ↦ f (φ u) - f (φ t)) =O[𝓝 t] (fun u : ℝ ↦ φ u - φ t) := by
    simpa only [Function.comp_def] using
      hf.hasDerivAt.isBigO_sub.comp_tendsto hφ.continuous.continuousAt.tendsto
  have he0 : ψ t = f (φ t) := hgraph.eq_of_nhds
  have he : (fun u : ℝ ↦ f (φ u) - f (φ t)) =ᶠ[𝓝 t] (fun u : ℝ ↦ ψ u - ψ t) := by
    filter_upwards [hgraph] with u hu
    simp only [Function.comp_apply] at hu
    rw [← hu, ← he0]
  have hψo := (hb.trans_isLittleO hφo).congr' he Filter.EventuallyEq.rfl
  have hz := hψo.tendsto_div_nhds_zero.mono_left
    (show 𝓝[≠] t ≤ 𝓝 t from nhdsWithin_le_nhds)
  have htψ := Real.taylor_tendsto convex_univ (mem_univ t) hψ.contDiffOn
  rw [nhdsWithin_univ] at htψ
  have hc := (htψ.mono_left
    (show 𝓝[≠] t ≤ 𝓝 t from nhdsWithin_le_nhds)).add_const (deriv (deriv ψ) t / 2)
  simp only [zero_add] at hc
  have hlim : Tendsto (fun u : ℝ ↦ (ψ u - ψ t) / (u - t) ^ 2) (𝓝[≠] t)
      (𝓝 (deriv (deriv ψ) t / 2)) := by
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [taylor_two_with_zero_first hψ1]
    have hne : u - t ≠ 0 := sub_ne_zero.mpr (show u ≠ t from hu)
    field_simp [hne]
    ring
  have hv := tendsto_nhds_unique hz hlim
  exact hψ2 (by linarith [hv])


theorem cycloid_singular_no_differentiable_graph (r t : ℝ) (hr : r ≠ 0)
    (ht : Real.cos t = 1) (f : ℝ → ℝ)
    (hgraph : cycloidY r =ᶠ[𝓝 t] f ∘ cycloidX r) :
    ¬ DifferentiableAt ℝ f (cycloidX r t) := by
  have hs : Real.sin t = 0 := by
    have hi := Real.sin_sq_add_cos_sq t
    rw [ht] at hi
    have hz : Real.sin t ^ 2 = 0 := by nlinarith
    exact sq_eq_zero_iff.mp hz
  have hφ : ContDiff ℝ 2 (cycloidX r) := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ r * (u - Real.sin u))
    exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ r)).mul
      (contDiff_id.sub Real.contDiff_sin)
  have hψ : ContDiff ℝ 2 (cycloidY r) := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ r * (1 - Real.cos u))
    exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ r)).mul
      ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ ↦ (1 : ℝ))).sub Real.contDiff_cos)
  exact second_order_parameter_no_differentiable_graph hφ hψ
    (by simp [cycloidX_deriv, ht]) (by simp [cycloidX_second_deriv, hs])
    (by simp [cycloidY_deriv, hs]) (by simpa [cycloidY_second_deriv, ht] using hr) hgraph


def spiralX (t : ℝ) : ℝ := t * Real.cos t
def spiralY (t : ℝ) : ℝ := t * Real.sin t

theorem spiralX_hasDerivAt (t : ℝ) :
    HasDerivAt spiralX (Real.cos t - t * Real.sin t) t := by
  change HasDerivAt (fun u : ℝ ↦ u * Real.cos u) (Real.cos t - t * Real.sin t) t
  apply ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)).congr_deriv
  change 1 * Real.cos t + t * -Real.sin t = Real.cos t - t * Real.sin t
  ring

theorem spiralY_hasDerivAt (t : ℝ) :
    HasDerivAt spiralY (Real.sin t + t * Real.cos t) t := by
  change HasDerivAt (fun u : ℝ ↦ u * Real.sin u) (Real.sin t + t * Real.cos t) t
  apply ((hasDerivAt_id t).mul (Real.hasDerivAt_sin t)).congr_deriv
  change 1 * Real.sin t + t * Real.cos t = Real.sin t + t * Real.cos t
  ring

theorem spiralX_deriv : deriv spiralX = fun t ↦ Real.cos t - t * Real.sin t := by
  funext t
  exact (spiralX_hasDerivAt t).deriv

theorem spiralY_deriv : deriv spiralY = fun t ↦ Real.sin t + t * Real.cos t := by
  funext t
  exact (spiralY_hasDerivAt t).deriv

theorem spiralX_second_deriv (t : ℝ) :
    deriv (deriv spiralX) t = -2 * Real.sin t - t * Real.cos t := by
  rw [spiralX_deriv]
  have h : HasDerivAt (fun u : ℝ ↦ Real.cos u - u * Real.sin u)
      (-2 * Real.sin t - t * Real.cos t) t := by
    apply ((Real.hasDerivAt_cos t).sub
      ((hasDerivAt_id t).mul (Real.hasDerivAt_sin t))).congr_deriv
    change -Real.sin t - (1 * Real.sin t + t * Real.cos t) =
      -2 * Real.sin t - t * Real.cos t
    ring
  exact h.deriv

theorem spiralY_second_deriv (t : ℝ) :
    deriv (deriv spiralY) t = 2 * Real.cos t - t * Real.sin t := by
  rw [spiralY_deriv]
  have h : HasDerivAt (fun u : ℝ ↦ Real.sin u + u * Real.cos u)
      (2 * Real.cos t - t * Real.sin t) t := by
    apply ((Real.hasDerivAt_sin t).add
      ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t))).congr_deriv
    change Real.cos t + (1 * Real.cos t + t * -Real.sin t) =
      2 * Real.cos t - t * Real.sin t
    ring
  exact h.deriv

/-- Bài 29(c): công thức trên miền `t > 0` khi đạo hàm hoành độ khác 0. -/
theorem spiral_parametric_derivatives (t : ℝ) (ht : 0 < t)
    (hne : Real.cos t - t * Real.sin t ≠ 0) :
    ∃ a b : ℝ, ∃ g : ℝ → ℝ, t ∈ Ioo a b ∧ Ioo a b ⊆ Ioi 0 ∧
      LeftInvOn g spiralX (Ioo a b) ∧
      HasDerivAt (spiralY ∘ g) ((Real.sin t + t * Real.cos t) /
        (Real.cos t - t * Real.sin t)) (spiralX t) ∧
      HasDerivAt (deriv (spiralY ∘ g)) ((t ^ 2 + 2) /
        (Real.cos t - t * Real.sin t) ^ 3) (spiralX t) := by
  have hφ : ContDiff ℝ 2 spiralX := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ u * Real.cos u)
    exact contDiff_id.mul Real.contDiff_cos
  have hψ : ContDiff ℝ 2 spiralY := by
    change ContDiff ℝ 2 (fun u : ℝ ↦ u * Real.sin u)
    exact contDiff_id.mul Real.contDiff_sin
  have hn : deriv spiralX t ≠ 0 := by rwa [spiralX_deriv]
  obtain ⟨a, b, g, ha, hg, hd1, hd2⟩ := exists_local_parametric_derivatives hφ hψ t hn
  let a' := max a (t / 2)
  have ha' : t ∈ Ioo a' b := by
    constructor
    · exact max_lt ha.1 (by linarith)
    · exact ha.2
  have hsub : Ioo a' b ⊆ Ioo a b := fun u hu ↦
    ⟨lt_of_le_of_lt (le_max_left _ _) hu.1, hu.2⟩
  have hpos : Ioo a' b ⊆ Ioi 0 := by
    intro u hu
    have he : t / 2 ≤ a' := le_max_right _ _
    change 0 < u
    linarith [hu.1]
  refine ⟨a', b, g, ha', hpos, hg.mono hsub, ?_, hd2.congr_deriv ?_⟩
  · simpa [spiralX_deriv, spiralY_deriv] using hd1
  · rw [spiralX_second_deriv, spiralY_second_deriv, spiralX_deriv, spiralY_deriv]
    have hi : (Real.cos t - t * Real.sin t) * (2 * Real.cos t - t * Real.sin t) -
        (-2 * Real.sin t - t * Real.cos t) * (Real.sin t + t * Real.cos t) = t ^ 2 + 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t,
        congrArg (fun z : ℝ ↦ t ^ 2 * z) (Real.sin_sq_add_cos_sq t)]
    rw [hi]


theorem vertical_parameter_no_differentiable_graph {φ ψ f : ℝ → ℝ} {t p : ℝ}
    (hφ : HasDerivAt φ 0 t) (hψ : HasDerivAt ψ p t) (hp : p ≠ 0)
    (hgraph : ψ =ᶠ[𝓝 t] f ∘ φ) : ¬ DifferentiableAt ℝ f (φ t) := by
  intro hf
  have hcomp := hf.hasDerivAt.comp t hφ
  have he : HasDerivAt ψ 0 t := by
    simpa using hcomp.congr_of_eventuallyEq hgraph
  exact hp (hψ.unique he)


theorem spiral_vertical_no_differentiable_graph (t : ℝ) (_ht : 0 < t)
    (hs : Real.cos t - t * Real.sin t = 0) (f : ℝ → ℝ)
    (hgraph : spiralY =ᶠ[𝓝 t] f ∘ spiralX) : ¬ DifferentiableAt ℝ f (spiralX t) := by
  have hp : Real.sin t + t * Real.cos t ≠ 0 := by
    intro hz
    have hi : (Real.cos t - t * Real.sin t) ^ 2 +
        (Real.sin t + t * Real.cos t) ^ 2 = 1 + t ^ 2 := by
      calc
        _ = (1 + t ^ 2) * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
        _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring
    rw [hs, hz] at hi
    nlinarith [sq_nonneg t]
  exact vertical_parameter_no_differentiable_graph
    (by simpa only [hs] using spiralX_hasDerivAt t) (spiralY_hasDerivAt t) hp hgraph

end calculus.Chapter04.Section01ParametricExercises
