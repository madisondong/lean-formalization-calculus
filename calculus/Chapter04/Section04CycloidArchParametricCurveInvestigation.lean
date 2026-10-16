import calculus.Chapter04.Section02Cycloid
import calculus.Chapter04.Section04
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 15(f): khảo sát cung cycloid

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2773–2781, `x=a(t−sin t)`, `y=a(1−cos t)`, `0≤t≤2π`, `a>0`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04CycloidArchParametricCurveInvestigation
open calculus.Chapter04.Section01Parametric
open calculus.Chapter04.Section02Cycloid
open calculus.Chapter04.Section04

def cycloidArchParameterDomain : Set ℝ := Icc 0 (2 * Real.pi)
def cycloidArch (a : ℝ) : Set (ℝ × ℝ) :=
  parametricCurve (cycloidX a) (cycloidY a) cycloidArchParameterDomain
def cycloidArchTangentEquationLocus (a t : ℝ) : Set (ℝ × ℝ) :=
  {p | Real.sin t * (p.1 - cycloidX a t) =
    (1 - Real.cos t) * (p.2 - cycloidY a t)}

theorem cycloid_arch_actual_coordinate_derivatives (a t : ℝ) :
    HasDerivAt (cycloidX a) (a * (1 - Real.cos t)) t ∧
      HasDerivAt (cycloidY a) (a * Real.sin t) t :=
  cycloid_coordinate_derivatives a t

theorem cycloid_arch_actual_second_derivatives (a t : ℝ) :
    HasDerivAt (deriv (cycloidX a)) (a * Real.sin t) t ∧
      HasDerivAt (deriv (cycloidY a)) (a * Real.cos t) t := by
  have hX : deriv (cycloidX a) = (fun u : ℝ ↦ a * (1 - Real.cos u)) :=
    funext (fun u ↦ (cycloid_coordinate_derivatives a u).1.deriv)
  have hY : deriv (cycloidY a) = (fun u : ℝ ↦ a * Real.sin u) :=
    funext (fun u ↦ (cycloid_coordinate_derivatives a u).2.deriv)
  rw [hX, hY]
  exact ⟨by simpa only [neg_neg] using! ((Real.hasDerivAt_cos t).const_sub 1).const_mul a,
    (Real.hasDerivAt_sin t).const_mul a⟩

theorem cycloid_arch_actual_third_derivatives (a t : ℝ) :
    HasDerivAt (deriv (deriv (cycloidX a))) (a * Real.cos t) t ∧
      HasDerivAt (deriv (deriv (cycloidY a))) (-a * Real.sin t) t := by
  have hX : deriv (deriv (cycloidX a)) = (fun u : ℝ ↦ a * Real.sin u) :=
    funext (fun u ↦ (cycloid_arch_actual_second_derivatives a u).1.deriv)
  have hY : deriv (deriv (cycloidY a)) = (fun u : ℝ ↦ a * Real.cos u) :=
    funext (fun u ↦ (cycloid_arch_actual_second_derivatives a u).2.deriv)
  rw [hX, hY]
  exact ⟨(Real.hasDerivAt_sin t).const_mul a,
    by simpa only [mul_neg, neg_mul] using! (Real.hasDerivAt_cos t).const_mul a⟩

theorem cycloid_arch_continuous_coordinates (a : ℝ) :
    Continuous (cycloidX a) ∧ Continuous (cycloidY a) :=
  ⟨continuous_iff_continuousAt.mpr (fun t ↦ (cycloid_coordinate_derivatives a t).1.continuousAt),
    continuous_iff_continuousAt.mpr (fun t ↦ (cycloid_coordinate_derivatives a t).2.continuousAt)⟩

theorem cycloid_arch_named_points (a : ℝ) :
    parametricPoint (cycloidX a) (cycloidY a) 0 = (0, 0) ∧
    parametricPoint (cycloidX a) (cycloidY a) Real.pi = (a * Real.pi, 2 * a) ∧
    parametricPoint (cycloidX a) (cycloidY a) (2 * Real.pi) = (2 * Real.pi * a, 0) := by
  constructor
  · simp only [parametricPoint, cycloidX, cycloidY, Real.sin_zero, Real.cos_zero,
      sub_self, mul_zero]
  · constructor
    · apply Prod.ext <;> simp only [parametricPoint, cycloidX, cycloidY, Real.sin_pi,
        Real.cos_pi, sub_zero]
      ring
    · apply Prod.ext <;> simp only [parametricPoint, cycloidX, cycloidY, Real.sin_two_pi,
        Real.cos_two_pi, sub_zero, sub_self, mul_zero]
      ring

theorem cycloid_arch_reflection (a t : ℝ) :
    cycloidX a (2 * Real.pi - t) = 2 * Real.pi * a - cycloidX a t ∧
      cycloidY a (2 * Real.pi - t) = cycloidY a t := by
  unfold cycloidX cycloidY
  rw [Real.sin_two_pi_sub, Real.cos_two_pi_sub]
  constructor <;> ring

theorem cycloid_arch_strictly_increasing_x {a : ℝ} (ha : 0 < a) :
    StrictMono (cycloidX a) := by
  intro s t hst
  have hs := abs_sin_difference_lt (ne_of_gt hst : t ≠ s)
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hb := le_abs_self (Real.sin t - Real.sin s)
  change a * (s - Real.sin s) < a * (t - Real.sin t)
  exact mul_lt_mul_of_pos_left (by linarith) ha

theorem cycloid_arch_no_self_intersection {a : ℝ} (ha : 0 < a) :
    Function.Injective (parametricPoint (cycloidX a) (cycloidY a)) := by
  intro s t he
  exact (cycloid_arch_strictly_increasing_x ha).injective (congrArg Prod.fst he)

theorem cycloid_arch_cosine_one_iff {t : ℝ} (ht : t ∈ cycloidArchParameterDomain) :
    Real.cos t = 1 ↔ t = 0 ∨ t = 2 * Real.pi := by
  constructor
  · intro hc
    by_cases h2 : t = 2 * Real.pi
    · exact Or.inr h2
    · left
      apply (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [ht.1, Real.pi_pos])
        (lt_of_le_of_ne ht.2 h2)).mp hc
  · rintro (rfl | rfl)
    · exact Real.cos_zero
    · exact Real.cos_two_pi

theorem cycloid_arch_positive_x_derivative {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ Ioo (0 : ℝ) (2 * Real.pi)) :
    0 < deriv (cycloidX a) t ∧ 0 < cycloidY a t := by
  have hcos : Real.cos t < 1 := lt_of_le_of_ne (Real.cos_le_one t) (by
    intro hc
    rcases (cycloid_arch_cosine_one_iff ⟨ht.1.le, ht.2.le⟩).mp hc with h | h
    · exact ht.1.ne' h
    · exact ht.2.ne h)
  have hpos : 0 < a * (1 - Real.cos t) := mul_pos ha (by linarith)
  exact ⟨by rw [(cycloid_coordinate_derivatives a t).1.deriv]; exact hpos, hpos⟩

theorem cycloid_arch_singular_parameters_iff {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ cycloidArchParameterDomain) :
    (deriv (cycloidX a) t = 0 ∧ deriv (cycloidY a) t = 0) ↔ t = 0 ∨ t = 2 * Real.pi := by
  rw [(cycloid_coordinate_derivatives a t).1.deriv, (cycloid_coordinate_derivatives a t).2.deriv]
  constructor
  · rintro ⟨hX, _⟩
    apply (cycloid_arch_cosine_one_iff ht).mp
    rcases mul_eq_zero.mp hX with h | h
    · exact False.elim (ha.ne' h)
    · linarith
  · rintro (rfl | rfl) <;> simp only [Real.sin_zero, Real.cos_zero, Real.sin_two_pi,
      Real.cos_two_pi, sub_self, mul_zero, and_self]

theorem cycloid_arch_y_monotonic_branches {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (cycloidY a) (Icc (0 : ℝ) Real.pi) ∧
      StrictAntiOn (cycloidY a) (Icc Real.pi (2 * Real.pi)) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) Real.pi)
      (cycloid_arch_continuous_coordinates a).2.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(cycloid_coordinate_derivatives a t).2.deriv]
    exact mul_pos ha (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  · apply strictAntiOn_of_deriv_neg (convex_Icc Real.pi (2 * Real.pi))
      (cycloid_arch_continuous_coordinates a).2.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(cycloid_coordinate_derivatives a t).2.deriv]
    have hs : 0 < Real.sin (2 * Real.pi - t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])
    rw [Real.sin_two_pi_sub] at hs
    exact mul_neg_of_pos_of_neg ha (by linarith)

theorem cycloid_arch_coordinate_bounds {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ cycloidArchParameterDomain) :
    0 ≤ cycloidX a t ∧ cycloidX a t ≤ 2 * Real.pi * a ∧
      0 ≤ cycloidY a t ∧ cycloidY a t ≤ 2 * a := by
  have hM := (cycloid_arch_strictly_increasing_x ha).monotone
  have h0 := hM ht.1
  have h2 := hM ht.2
  have hp := cycloid_arch_named_points a
  have hX0 := congrArg Prod.fst hp.1
  have hX2 := congrArg Prod.fst hp.2.2
  change cycloidX a 0 = 0 at hX0
  change cycloidX a (2 * Real.pi) = 2 * Real.pi * a at hX2
  rw [hX0] at h0
  rw [hX2] at h2
  refine ⟨h0, h2, ?_, ?_⟩
  · exact mul_nonneg ha.le (by linarith [Real.cos_le_one t])
  · have hb := mul_le_mul_of_nonneg_left (by linarith [Real.neg_one_le_cos t] : 1 - Real.cos t ≤ 2) ha.le
    change a * (1 - Real.cos t) ≤ 2 * a
    nlinarith


theorem cycloid_arch_complete_graph_image {a : ℝ} (ha : 0 < a) :
    cycloidArch a = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 2 * Real.pi * a ∧
      p.2 = cycloidGraphFunction a p.1} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hb := cycloid_arch_coordinate_bounds ha ht
    exact ⟨hb.1, hb.2.1, (cycloidGraphFunction_apply_cycloidX ha.ne' t).symm⟩
  · rintro ⟨hx0, hx2, hy⟩
    have h0 := congrArg Prod.fst (cycloid_arch_named_points a).1
    have h2 := congrArg Prod.fst (cycloid_arch_named_points a).2.2
    change cycloidX a 0 = 0 at h0
    change cycloidX a (2 * Real.pi) = 2 * Real.pi * a at h2
    have hx : p.1 ∈ Icc (cycloidX a 0) (cycloidX a (2 * Real.pi)) := by
      rw [h0, h2]
      exact ⟨hx0, hx2⟩
    obtain ⟨t, ht, hX⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (cycloid_arch_continuous_coordinates a).1.continuousOn hx
    refine ⟨t, ht, Prod.ext hX ?_⟩
    rw [hy, ← hX]
    exact (cycloidGraphFunction_apply_cycloidX ha.ne' t).symm

theorem cycloid_arch_compact (a : ℝ) : IsCompact (cycloidArch a) := by
  have hp : Continuous (parametricPoint (cycloidX a) (cycloidY a)) :=
    (cycloid_arch_continuous_coordinates a).1.prodMk (cycloid_arch_continuous_coordinates a).2
  exact isCompact_Icc.image hp

theorem cycloid_arch_actual_graph_derivatives {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ Ioo (0 : ℝ) (2 * Real.pi)) :
    HasDerivAt (cycloidGraphFunction a) (Real.sin t / (1 - Real.cos t)) (cycloidX a t) ∧
      HasDerivAt (deriv (cycloidGraphFunction a)) (-1 / (a * (1 - Real.cos t) ^ 2)) (cycloidX a t) ∧
      -1 / (a * (1 - Real.cos t) ^ 2) < 0 := by
  have hD : 1 - Real.cos t ≠ 0 := by
    intro hc
    have hX := (cycloid_arch_positive_x_derivative ha ht).1
    rw [(cycloid_coordinate_derivatives a t).1.deriv, hc, mul_zero] at hX
    exact lt_irrefl 0 hX
  exact ⟨cycloidGraphFunction_hasDerivAt ha.ne' hD, cycloidGraphFunction_deriv_hasDerivAt ha.ne' hD,
    div_neg_of_neg_of_pos (by norm_num) (mul_pos ha (sq_pos_of_ne_zero hD))⟩

theorem cycloid_arch_plane_curvature_numerator {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ Ioo (0 : ℝ) (2 * Real.pi)) :
    deriv (cycloidX a) t * deriv (deriv (cycloidY a)) t -
      deriv (deriv (cycloidX a)) t * deriv (cycloidY a) t = a ^ 2 * (Real.cos t - 1) ∧
      a ^ 2 * (Real.cos t - 1) < 0 := by
  rw [(cycloid_coordinate_derivatives a t).1.deriv, (cycloid_coordinate_derivatives a t).2.deriv,
    (cycloid_arch_actual_second_derivatives a t).1.deriv,
    (cycloid_arch_actual_second_derivatives a t).2.deriv]
  have htrig := congrArg (fun z : ℝ ↦ a ^ 2 * z) (Real.sin_sq_add_cos_sq t)
  constructor
  · nlinarith [htrig]
  · have hp := (cycloid_arch_positive_x_derivative ha ht).2
    change 0 < a * (1 - Real.cos t) at hp
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos ha) (by nlinarith)

theorem cycloid_arch_top_horizontal_tangent {a : ℝ} (ha : 0 < a) (p : ℝ × ℝ) :
    p ∈ cycloidArchTangentEquationLocus a Real.pi ↔ p.2 = 2 * a := by
  simp only [cycloidArchTangentEquationLocus, mem_ofPred_eq, Real.sin_pi, Real.cos_pi, zero_mul, cycloidY]
  constructor
  · intro h
    have he : a * p.2 = a * (2 * a) := by nlinarith [h]
    exact mul_left_cancel₀ ha.ne' he
  · intro h
    rw [h]
    ring

theorem cycloid_arch_unique_highest_point {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ cycloidArchParameterDomain) :
    cycloidY a t = 2 * a ↔ t = Real.pi := by
  have hpeak := congrArg Prod.snd (cycloid_arch_named_points a).2.1
  change cycloidY a Real.pi = 2 * a at hpeak
  constructor
  · intro hy
    rcases lt_trichotomy t Real.pi with hl | he | hr
    · have hm := (cycloid_arch_y_monotonic_branches ha).1
        ⟨ht.1, hl.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hl
      rw [hy, hpeak] at hm
      exact False.elim (lt_irrefl _ hm)
    · exact he
    · have hm := (cycloid_arch_y_monotonic_branches ha).2
        ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨hr.le, ht.2⟩ hr
      rw [hy, hpeak] at hm
      exact False.elim (lt_irrefl _ hm)
  · rintro rfl
    exact hpeak

theorem cycloid_arch_height_zero_iff {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ cycloidArchParameterDomain) :
    cycloidY a t = 0 ↔ t = 0 ∨ t = 2 * Real.pi := by
  constructor
  · intro hy
    apply (cycloid_arch_cosine_one_iff ht).mp
    change a * (1 - Real.cos t) = 0 at hy
    rcases mul_eq_zero.mp hy with h | h
    · exact False.elim (ha.ne' h)
    · linarith
  · rintro (rfl | rfl) <;> simp only [cycloidY, Real.cos_zero, Real.cos_two_pi,
      sub_self, mul_zero]


theorem cycloid_arch_endpoint_cusp_jets (a : ℝ) :
    ∀ t : ℝ, t = 0 ∨ t = 2 * Real.pi →
      deriv (cycloidX a) t = 0 ∧ deriv (cycloidY a) t = 0 ∧
      deriv (deriv (cycloidX a)) t = 0 ∧ deriv (deriv (cycloidY a)) t = a ∧
      deriv (deriv (deriv (cycloidX a))) t = a ∧
      deriv (deriv (deriv (cycloidY a))) t = 0 := by
  intro t ht
  have hc : Real.cos t = 1 := by rcases ht with rfl | rfl <;> simp only [Real.cos_zero, Real.cos_two_pi]
  have hs : Real.sin t = 0 := by rcases ht with rfl | rfl <;> simp only [Real.sin_zero, Real.sin_two_pi]
  rw [(cycloid_coordinate_derivatives a t).1.deriv,
    (cycloid_coordinate_derivatives a t).2.deriv,
    (cycloid_arch_actual_second_derivatives a t).1.deriv,
    (cycloid_arch_actual_second_derivatives a t).2.deriv,
    (cycloid_arch_actual_third_derivatives a t).1.deriv,
    (cycloid_arch_actual_third_derivatives a t).2.deriv]
  simp only [hc, hs, sub_self, mul_zero, mul_one, and_self]

theorem cycloid_arch_endpoint_cusp_jet_determinant {a : ℝ} (ha : 0 < a) :
    0 * 0 - a * a = -(a ^ 2) ∧ -(a ^ 2) < 0 := by
  exact ⟨by ring, by nlinarith [sq_pos_of_pos ha]⟩

theorem cycloid_arch_initial_vertical_secant {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ ↦ cycloidX a t / cycloidY a t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hf (t : ℝ) : HasDerivAt (fun u : ℝ ↦ u - Real.sin u) (1 - Real.cos t) t := by
    simpa only [id_eq] using! (hasDerivAt_id t).fun_sub (Real.hasDerivAt_sin t)
  have hg (t : ℝ) : HasDerivAt (fun u : ℝ ↦ 1 - Real.cos u) (Real.sin t) t := by
    simpa only [neg_neg] using! (Real.hasDerivAt_cos t).const_sub 1
  have hderiv : Tendsto (fun t : ℝ ↦ (1 - Real.cos t) / Real.sin t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh := (one_sub_cosine_div_square_right.mul hi).div sine_quotient_right one_ne_zero
    have hh' : Tendsto (fun t : ℝ ↦ (((1 - Real.cos t) / t ^ 2) * t) / (Real.sin t / t))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa only [mul_zero, zero_div] using! hh
    apply hh'.congr'
    have hpi : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < Real.pi :=
      hi.eventually (eventually_lt_nhds Real.pi_pos)
    filter_upwards [self_mem_nhdsWithin, hpi] with t (ht : 0 < t) htp
    field_simp [ht.ne', (Real.sin_pos_of_pos_of_lt_pi ht htp).ne']
  have hbare : Tendsto (fun t : ℝ ↦ (t - Real.sin t) / (1 - Real.cos t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply HasDerivAt.lhopital_zero_right_on_Ioo (a := 0) (b := Real.pi) Real.pi_pos
      (fun t _ ↦ hf t) (fun t _ ↦ hg t)
      (fun t ht ↦ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne')
    · simpa only [Real.sin_zero, sub_zero] using!
        (hf 0).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · simpa only [Real.cos_zero, sub_self] using!
        (hg 0).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · exact hderiv
  apply hbare.congr'
  filter_upwards with t
  exact (mul_div_mul_left (t - Real.sin t) (1 - Real.cos t) ha.ne').symm

theorem cycloid_arch_final_vertical_secant {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ ↦ (cycloidX a t - 2 * Real.pi * a) / cycloidY a t)
      (𝓝[<] (2 * Real.pi)) (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ ↦ 2 * Real.pi - t)
      (𝓝[<] (2 * Real.pi)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [sub_self] using!
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[<] (2 * Real.pi) ≤ 𝓝 (2 * Real.pi))).const_sub (2 * Real.pi)
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < 2 * Real.pi)
      exact sub_pos.mpr ht
  have h := ((cycloid_arch_initial_vertical_secant ha).comp hs).neg
  apply (show Tendsto (fun t : ℝ ↦ -(cycloidX a (2 * Real.pi - t) / cycloidY a (2 * Real.pi - t)))
    (𝓝[<] (2 * Real.pi)) (𝓝 0) from by simpa only [Function.comp_def, neg_zero] using! h).congr'
  filter_upwards with t
  rw [(cycloid_arch_reflection a t).1, (cycloid_arch_reflection a t).2]
  ring


theorem source_cycloid_arch_parametric_curve_investigation {a : ℝ} (ha : 0 < a) :
    (cycloidArch a = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 2 * Real.pi * a ∧
      p.2 = cycloidGraphFunction a p.1}) ∧
    IsCompact (cycloidArch a) ∧
    Function.Injective (parametricPoint (cycloidX a) (cycloidY a)) ∧
    StrictMono (cycloidX a) ∧
    (StrictMonoOn (cycloidY a) (Icc (0 : ℝ) Real.pi) ∧
      StrictAntiOn (cycloidY a) (Icc Real.pi (2 * Real.pi))) ∧
    (∀ t ∈ cycloidArchParameterDomain, 0 ≤ cycloidX a t ∧ cycloidX a t ≤ 2 * Real.pi * a ∧
      0 ≤ cycloidY a t ∧ cycloidY a t ≤ 2 * a) ∧
    (∀ t ∈ cycloidArchParameterDomain, cycloidY a t = 2 * a ↔ t = Real.pi) ∧
    (∀ t ∈ cycloidArchParameterDomain,
      (deriv (cycloidX a) t = 0 ∧ deriv (cycloidY a) t = 0) ↔ t = 0 ∨ t = 2 * Real.pi) ∧
    (∀ t ∈ Ioo (0 : ℝ) (2 * Real.pi), HasDerivAt (cycloidGraphFunction a)
      (Real.sin t / (1 - Real.cos t)) (cycloidX a t) ∧
      HasDerivAt (deriv (cycloidGraphFunction a)) (-1 / (a * (1 - Real.cos t) ^ 2)) (cycloidX a t) ∧
      -1 / (a * (1 - Real.cos t) ^ 2) < 0) ∧
    (Tendsto (fun t : ℝ ↦ cycloidX a t / cycloidY a t) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun t : ℝ ↦ (cycloidX a t - 2 * Real.pi * a) / cycloidY a t)
        (𝓝[<] (2 * Real.pi)) (𝓝 0)) := by
  exact ⟨cycloid_arch_complete_graph_image ha, cycloid_arch_compact a,
    cycloid_arch_no_self_intersection ha, cycloid_arch_strictly_increasing_x ha,
    cycloid_arch_y_monotonic_branches ha, fun _ ht ↦ cycloid_arch_coordinate_bounds ha ht,
    fun _ ht ↦ cycloid_arch_unique_highest_point ha ht,
    fun _ ht ↦ cycloid_arch_singular_parameters_iff ha ht,
    fun _ ht ↦ cycloid_arch_actual_graph_derivatives ha ht,
    cycloid_arch_initial_vertical_secant ha, cycloid_arch_final_vertical_secant ha⟩

end calculus.Chapter04.Section04CycloidArchParametricCurveInvestigation
