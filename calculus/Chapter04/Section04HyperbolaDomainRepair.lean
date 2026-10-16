import calculus.Chapter04.Section01Parametric
import calculus.Chapter04.Section01ElementaryDerivatives
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Miền xác định của biểu diễn tham số hypebol

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2779, `C04-S04-exercise-015.p04`. Xét `0 ≤ t < 2π`, `cos t ≠ 0` và `a, b > 0`.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04HyperbolaDomainRepair
open calculus.Chapter04.Section01Parametric

def hyperbolaX (a t : ℝ) : ℝ := a / Real.cos t
def hyperbolaY (b t : ℝ) : ℝ := b * Real.tan t
def hyperbolaDomain : Set ℝ :=
  {t | 0 ≤ t ∧ t < 2 * Real.pi ∧ Real.cos t ≠ 0}
def hyperbolaCurve (a b : ℝ) : Set (ℝ × ℝ) :=
  parametricCurve (hyperbolaX a) (hyperbolaY b) hyperbolaDomain
def hyperbolaImplicit (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | (p.1 / a) ^ 2 - (p.2 / b) ^ 2 = 1}

theorem hyperbola_locus_identity (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : Real.cos t ≠ 0) :
    (hyperbolaX a t / a) ^ 2 - (hyperbolaY b t / b) ^ 2 = 1 := by
  have hx : hyperbolaX a t / a = 1 / Real.cos t := by
    unfold hyperbolaX
    field_simp
  have hy : hyperbolaY b t / b = Real.sin t / Real.cos t := by
    unfold hyperbolaY
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [hx, hy]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem hyperbola_complete_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    hyperbolaCurve a b = hyperbolaImplicit a b := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact hyperbola_locus_identity a b t ha.ne' hb.ne' ht.2.2
  · intro hp
    change (p.1 / a) ^ 2 - (p.2 / b) ^ 2 = 1 at hp
    have hx : p.1 ≠ 0 := by
      intro h
      rw [h, zero_div, zero_pow (by decide : 2 ≠ 0)] at hp
      nlinarith [sq_nonneg (p.2 / b)]
    have hu : (a / p.1) ^ 2 + (a * p.2 / (b * p.1)) ^ 2 = 1 := by
      field_simp [ha.ne', hb.ne'] at hp ⊢
      nlinarith [hp]
    obtain ⟨t, ht, hc, hs⟩ := unit_circle_parameter hu
    have htcos : Real.cos t ≠ 0 := by rw [hc]; exact div_ne_zero ha.ne' hx
    have hpoint : parametricPoint (hyperbolaX a) (hyperbolaY b) t = p := by
      apply Prod.ext
      · change a / Real.cos t = p.1
        rw [hc]
        field_simp
      · change b * Real.tan t = p.2
        rw [Real.tan_eq_sin_div_cos, hs, hc]
        field_simp
    by_cases hend : t = 2 * Real.pi
    · refine ⟨0, ⟨le_rfl, by linarith [Real.pi_pos], by simp⟩, ?_⟩
      simpa [hend, parametricPoint, hyperbolaX, hyperbolaY, Real.tan_eq_sin_div_cos] using hpoint
    · exact ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 hend, htcos⟩, hpoint⟩

theorem hyperbola_actual_derivatives (a b t : ℝ) (hc : Real.cos t ≠ 0) :
    HasDerivAt (hyperbolaX a) (a * Real.sin t / Real.cos t ^ 2) t ∧
    HasDerivAt (hyperbolaY b) (b / Real.cos t ^ 2) t := by
  constructor
  · have h := ((hasDerivAt_const t a).div (Real.hasDerivAt_cos t) hc)
    apply h.congr_deriv
    ring
  · simpa only [hyperbolaY, div_eq_mul_inv, one_mul] using! (Real.hasDerivAt_tan hc).const_mul b

theorem hyperbola_regular {a b t : ℝ} (hb : 0 < b) (hc : Real.cos t ≠ 0) :
    0 < deriv (hyperbolaY b) t := by
  rw [(hyperbola_actual_derivatives a b t hc).2.deriv]
  exact div_pos hb (sq_pos_of_ne_zero hc)

theorem hyperbola_vertex_tangents (a b : ℝ) :
    hyperbolaX a 0 = a ∧ hyperbolaY b 0 = 0 ∧
    hyperbolaX a Real.pi = -a ∧ hyperbolaY b Real.pi = 0 ∧
    deriv (hyperbolaX a) 0 = 0 ∧ deriv (hyperbolaX a) Real.pi = 0 ∧
    deriv (hyperbolaY b) 0 = b ∧ deriv (hyperbolaY b) Real.pi = b := by
  simp [hyperbolaX, hyperbolaY, div_neg, div_one,
    (hyperbola_actual_derivatives a b 0 (by simp)).1.deriv,
    (hyperbola_actual_derivatives a b Real.pi (by simp)).1.deriv,
    (hyperbola_actual_derivatives a b 0 (by simp)).2.deriv,
    (hyperbola_actual_derivatives a b Real.pi (by simp)).2.deriv]

theorem hyperbola_regular_slope (a b t : ℝ) (ha : a ≠ 0)
    (hc : Real.cos t ≠ 0) (hs : Real.sin t ≠ 0) :
    deriv (hyperbolaY b) t / deriv (hyperbolaX a) t = b / (a * Real.sin t) := by
  rw [(hyperbola_actual_derivatives a b t hc).1.deriv,
    (hyperbola_actual_derivatives a b t hc).2.deriv]
  field_simp

theorem hyperbola_branch_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {p : ℝ × ℝ} (hp : p ∈ hyperbolaCurve a b) : a ≤ |p.1| := by
  rw [hyperbola_complete_image ha hb] at hp
  change (p.1 / a) ^ 2 - (p.2 / b) ^ 2 = 1 at hp
  have hsq : 1 ≤ (p.1 / a) ^ 2 := by nlinarith [sq_nonneg (p.2 / b)]
  have habs : 1 ≤ |p.1 / a| := by
    by_contra h
    have hlt := lt_of_not_ge h
    have hnn := abs_nonneg (p.1 / a)
    nlinarith [sq_abs (p.1 / a)]
  rw [abs_div, abs_of_pos ha] at habs
  simpa using (le_div_iff₀ ha).mp habs

theorem hyperbola_residual_plus (a b t : ℝ) (ha : a ≠ 0)
    (hc : Real.cos t ≠ 0) (hs : 1 + Real.sin t ≠ 0) :
    hyperbolaY b t - (b / a) * hyperbolaX a t =
      -b * Real.cos t / (1 + Real.sin t) := by
  unfold hyperbolaX hyperbolaY
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith only [congrArg (fun u : ℝ => b * u) (Real.sin_sq_add_cos_sq t)]

theorem hyperbola_residual_minus (a b t : ℝ) (ha : a ≠ 0)
    (hc : Real.cos t ≠ 0) (hs : 1 - Real.sin t ≠ 0) :
    hyperbolaY b t + (b / a) * hyperbolaX a t =
      b * Real.cos t / (1 - Real.sin t) := by
  unfold hyperbolaX hyperbolaY
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith only [congrArg (fun u : ℝ => b * u) (Real.sin_sq_add_cos_sq t)]

theorem hyperbola_unbounded_at_pole {a t₀ : ℝ} (ha : 0 < a)
    (hzero : Real.cos t₀ = 0) :
    Tendsto (fun t => |hyperbolaX a t|)
      (𝓝[{t | Real.cos t ≠ 0}] t₀) atTop := by
  have hlim : Tendsto (fun t => |Real.cos t|)
      (𝓝[{t | Real.cos t ≠ 0}] t₀) (𝓝 0) := by
    simpa [hzero] using ((Real.continuous_cos.abs.continuousAt : ContinuousAt (fun t => |Real.cos t|) t₀).tendsto.mono_left nhdsWithin_le_nhds)
  have hpos : Tendsto (fun t => |Real.cos t|)
      (𝓝[{t | Real.cos t ≠ 0}] t₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hlim, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact abs_pos.mpr ht
  have hi := hpos.inv_tendsto_nhdsGT_zero.const_mul_atTop ha
  simpa [hyperbolaX, abs_div, abs_of_pos ha, div_eq_mul_inv] using hi

theorem hyperbola_plus_asymptote {a b : ℝ} (ha : 0 < a) :
    Tendsto (fun t => hyperbolaY b t - (b / a) * hyperbolaX a t)
      (𝓝[{t | Real.cos t ≠ 0}] (Real.pi / 2)) (𝓝 0) := by
  have hs : 1 + Real.sin (Real.pi / 2) ≠ 0 := by simp
  have hlim := ((Real.continuous_cos.continuousAt.const_mul (-b)).div
    (continuous_const.add Real.continuous_sin).continuousAt hs).tendsto
  have hgood : ∀ᶠ t in 𝓝 (Real.pi / 2), 1 + Real.sin t ≠ 0 :=
    (continuous_const.add Real.continuous_sin).continuousAt.eventually_ne hs
  apply Tendsto.congr' ?_ (by simpa using hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, hgood.filter_mono nhdsWithin_le_nhds] with t hc hs
  simpa [neg_mul] using (hyperbola_residual_plus a b t ha.ne' hc hs).symm

theorem hyperbola_minus_asymptote {a b : ℝ} (ha : 0 < a) :
    Tendsto (fun t => hyperbolaY b t + (b / a) * hyperbolaX a t)
      (𝓝[{t | Real.cos t ≠ 0}] (-(Real.pi / 2))) (𝓝 0) := by
  have hs : 1 - Real.sin (-(Real.pi / 2)) ≠ 0 := by simp
  have hlim := ((Real.continuous_cos.continuousAt.const_mul b).div
    (continuous_const.sub Real.continuous_sin).continuousAt hs).tendsto
  have hgood : ∀ᶠ t in 𝓝 (-(Real.pi / 2)), 1 - Real.sin t ≠ 0 :=
    (continuous_const.sub Real.continuous_sin).continuousAt.eventually_ne hs
  apply Tendsto.congr' ?_ (by simpa using hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, hgood.filter_mono nhdsWithin_le_nhds] with t hc hs
  exact (hyperbola_residual_minus a b t ha.ne' hc hs).symm



theorem hyperbola_y_strictMonoOn {a b : ℝ} (hb : 0 < b) {D : Set ℝ}
    (hD : Convex ℝ D) (hc : ∀ t ∈ D, Real.cos t ≠ 0) :
    StrictMonoOn (hyperbolaY b) D := by
  apply strictMonoOn_of_deriv_pos hD
  · intro t ht
    exact (hyperbola_actual_derivatives a b t (hc t ht)).2.continuousAt.continuousWithinAt
  · intro t ht
    exact hyperbola_regular (a := a) hb (hc t (interior_subset ht))


theorem hyperbola_minus_asymptote_source {a b : ℝ} (ha : 0 < a) :
    Tendsto (fun t => hyperbolaY b t + (b / a) * hyperbolaX a t)
      (𝓝[{t | Real.cos t ≠ 0}] (3 * Real.pi / 2)) (𝓝 0) := by
  have he : 3 * Real.pi / 2 = 2 * Real.pi - Real.pi / 2 := by ring
  have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [he, Real.sin_two_pi_sub, Real.sin_pi_div_two]
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [he, Real.cos_two_pi_sub, Real.cos_pi_div_two]
  have hs : 1 - Real.sin (3 * Real.pi / 2) ≠ 0 := by rw [hsin]; norm_num
  have hlim := ((Real.continuous_cos.continuousAt.const_mul b).div
    (continuous_const.sub Real.continuous_sin).continuousAt hs).tendsto
  have hgood : ∀ᶠ t in 𝓝 (3 * Real.pi / 2), 1 - Real.sin t ≠ 0 :=
    (continuous_const.sub Real.continuous_sin).continuousAt.eventually_ne hs
  apply Tendsto.congr' ?_ (by simpa [hcos, hsin] using hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, hgood.filter_mono nhdsWithin_le_nhds] with t hc hs
  exact (hyperbola_residual_minus a b t ha.ne' hc hs).symm


theorem hyperbola_source_pole_escape {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t => |hyperbolaX a t|)
      (𝓝[{t | Real.cos t ≠ 0}] (Real.pi / 2)) atTop ∧
    Tendsto (fun t => |hyperbolaX a t|)
      (𝓝[{t | Real.cos t ≠ 0}] (3 * Real.pi / 2)) atTop := by
  constructor
  · exact hyperbola_unbounded_at_pole ha (by simp)
  · apply hyperbola_unbounded_at_pole ha
    rw [show 3 * Real.pi / 2 = 2 * Real.pi - Real.pi / 2 by ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_two]



theorem hyperbola_actual_second_derivatives (a b t : ℝ) (hc : Real.cos t ≠ 0) :
    HasDerivAt (deriv (hyperbolaX a))
      (a * (1 + Real.sin t ^ 2) / Real.cos t ^ 3) t ∧
    HasDerivAt (deriv (hyperbolaY b))
      (2 * b * Real.sin t / Real.cos t ^ 3) t := by
  have hnear : ∀ᶠ u in 𝓝 t, Real.cos u ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hc
  have hden := (Real.hasDerivAt_cos t).fun_pow 2
  constructor
  · have hraw := ((Real.hasDerivAt_sin t).const_mul a).div hden (pow_ne_zero 2 hc)
    have hfirst : HasDerivAt (fun u => a * Real.sin u / Real.cos u ^ 2)
        (a * Real.cos t / Real.cos t ^ 2 +
          2 * a * Real.sin t ^ 2 / Real.cos t ^ 3) t := by
      apply hraw.congr_deriv
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      field_simp
      ring
    have htrig : Real.cos t ^ 2 + 2 * Real.sin t ^ 2 = 1 + Real.sin t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    have hsimple : HasDerivAt (fun u => a * Real.sin u / Real.cos u ^ 2)
        (a * (1 + Real.sin t ^ 2) / Real.cos t ^ 3) t := by
      apply hfirst.congr_deriv
      calc
        a * Real.cos t / Real.cos t ^ 2 +
            2 * a * Real.sin t ^ 2 / Real.cos t ^ 3 =
          a * (Real.cos t ^ 2 + 2 * Real.sin t ^ 2) / Real.cos t ^ 3 := by
            field_simp
        _ = a * (1 + Real.sin t ^ 2) / Real.cos t ^ 3 := by rw [htrig]
    apply hsimple.congr_of_eventuallyEq
    filter_upwards [hnear] with u hu
    exact (hyperbola_actual_derivatives a b u hu).1.deriv
  · have hraw := (hasDerivAt_const t b).div hden (pow_ne_zero 2 hc)
    have hsimple : HasDerivAt (fun u => b / Real.cos u ^ 2)
        (2 * b * Real.sin t / Real.cos t ^ 3) t := by
      apply hraw.congr_deriv
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      field_simp
      ring
    apply hsimple.congr_of_eventuallyEq
    filter_upwards [hnear] with u hu
    exact (hyperbola_actual_derivatives a b u hu).2.deriv


theorem hyperbola_curvature_determinant (a b t : ℝ) (hc : Real.cos t ≠ 0) :
    deriv (hyperbolaX a) t * deriv (deriv (hyperbolaY b)) t -
      deriv (hyperbolaY b) t * deriv (deriv (hyperbolaX a)) t =
        -a * b / Real.cos t ^ 3 := by
  rw [(hyperbola_actual_derivatives a b t hc).1.deriv,
    (hyperbola_actual_derivatives a b t hc).2.deriv,
    (hyperbola_actual_second_derivatives a b t hc).1.deriv,
    (hyperbola_actual_second_derivatives a b t hc).2.deriv]
  have htrig : Real.sin t ^ 2 - 1 = -Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  calc
    a * Real.sin t / Real.cos t ^ 2 * (2 * b * Real.sin t / Real.cos t ^ 3) -
        b / Real.cos t ^ 2 * (a * (1 + Real.sin t ^ 2) / Real.cos t ^ 3) =
      a * b * (Real.sin t ^ 2 - 1) / Real.cos t ^ 5 := by field_simp; ring
    _ = -a * b / Real.cos t ^ 3 := by rw [htrig]; field_simp


theorem hyperbola_no_zero_curvature_or_horizontal {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : Real.cos t ≠ 0) :
    deriv (hyperbolaY b) t ≠ 0 ∧
      deriv (hyperbolaX a) t * deriv (deriv (hyperbolaY b)) t -
        deriv (hyperbolaY b) t * deriv (deriv (hyperbolaX a)) t ≠ 0 := by
  constructor
  · exact (hyperbola_regular (a := a) hb hc).ne'
  · rw [hyperbola_curvature_determinant a b t hc]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha.ne') hb.ne') (pow_ne_zero 3 hc)


theorem hyperbola_vertical_tangent_iff {a b t : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : Real.cos t ≠ 0) :
    (deriv (hyperbolaX a) t = 0 ∧ deriv (hyperbolaY b) t ≠ 0) ↔ Real.sin t = 0 := by
  rw [(hyperbola_actual_derivatives a b t hc).1.deriv]
  simp [div_eq_zero_iff, mul_eq_zero, ha.ne', hc,
    (hyperbola_regular (a := a) hb hc).ne']


theorem hyperbola_cos_eventually_nonzero_at_pole {t₀ : ℝ} (hzero : Real.cos t₀ = 0) :
    ∀ᶠ t in 𝓝[≠] t₀, Real.cos t ≠ 0 := by
  have hI0 : ∀ᶠ t in 𝓝 t₀, t ∈ Ioo (t₀ - Real.pi) (t₀ + Real.pi) :=
    Ioo_mem_nhds (sub_lt_self _ Real.pi_pos) (lt_add_of_pos_right _ Real.pi_pos)
  have hI := hI0.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
  filter_upwards [hI, self_mem_nhdsWithin] with t ht hne
  have hn : t ≠ t₀ := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  intro hcos
  have hsin : Real.sin (t - t₀) = 0 := by rw [Real.sin_sub, hzero, hcos]; ring
  have he := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [ht.1] : -Real.pi < t - t₀)
    (by linarith [ht.2] : t - t₀ < Real.pi)).mp hsin
  exact hn (by linarith)


theorem hyperbola_pole_filter_neBot {t₀ : ℝ} (hzero : Real.cos t₀ = 0) :
    NeBot (𝓝[{t | Real.cos t ≠ 0}] t₀) := by
  have hle : 𝓝[≠] t₀ ≤ 𝓝[{t | Real.cos t ≠ 0}] t₀ :=
    le_inf nhdsWithin_le_nhds
      (le_principal_iff.mpr (hyperbola_cos_eventually_nonzero_at_pole hzero))
  exact Filter.neBot_of_le hle



theorem hyperbola_cos_four_end_limits :
    Tendsto Real.cos (𝓝[<] (Real.pi/2)) (𝓝[>] 0) ∧
    Tendsto Real.cos (𝓝[>] (Real.pi/2)) (𝓝[<] 0) ∧
    Tendsto Real.cos (𝓝[<] (3*Real.pi/2)) (𝓝[<] 0) ∧
    Tendsto Real.cos (𝓝[>] (3*Real.pi/2)) (𝓝[>] 0) := by
  have hc : Real.cos (3*Real.pi/2)=0 := by
    rw [show 3*Real.pi/2=2*Real.pi-Real.pi/2 by ring,Real.cos_two_pi_sub,Real.cos_pi_div_two]
  refine ⟨Real.tendsto_cos_pi_div_two,?_,?_,?_⟩
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using Real.continuous_cos.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (Real.pi/2) ≤ 𝓝 (Real.pi/2))
    · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : Real.pi/2<Real.pi+Real.pi/2)] with t ht
      exact Real.cos_neg_of_pi_div_two_lt_of_lt ht.1 ht.2
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa [hc] using Real.continuous_cos.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (3*Real.pi/2) ≤ 𝓝 (3*Real.pi/2))
    · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : Real.pi/2<3*Real.pi/2)] with t ht
      exact Real.cos_neg_of_pi_div_two_lt_of_lt ht.1 (by linarith [ht.2])
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa [hc] using Real.continuous_cos.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (3*Real.pi/2) ≤ 𝓝 (3*Real.pi/2))
    · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : 3*Real.pi/2<5*Real.pi/2)] with t ht
      rw [← Real.cos_two_pi_sub t]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.2],by linarith [ht.1]⟩

theorem hyperbola_four_coordinate_end_limits {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Tendsto (hyperbolaX a) (𝓝[<] (Real.pi/2)) atTop ∧
    Tendsto (hyperbolaY b) (𝓝[<] (Real.pi/2)) atTop ∧
    Tendsto (hyperbolaX a) (𝓝[>] (Real.pi/2)) atBot ∧
    Tendsto (hyperbolaY b) (𝓝[>] (Real.pi/2)) atBot ∧
    Tendsto (hyperbolaX a) (𝓝[<] (3*Real.pi/2)) atBot ∧
    Tendsto (hyperbolaY b) (𝓝[<] (3*Real.pi/2)) atTop ∧
    Tendsto (hyperbolaX a) (𝓝[>] (3*Real.pi/2)) atTop ∧
    Tendsto (hyperbolaY b) (𝓝[>] (3*Real.pi/2)) atBot := by
  obtain ⟨h1,h2,h3,h4⟩ := hyperbola_cos_four_end_limits
  have i1 := h1.inv_tendsto_nhdsGT_zero
  have i2 := h2.inv_tendsto_nhdsLT_zero
  have i3 := h3.inv_tendsto_nhdsLT_zero
  have i4 := h4.inv_tendsto_nhdsGT_zero
  have hs3 : Real.sin (3*Real.pi/2)=-1 := by
    rw [show 3*Real.pi/2=2*Real.pi-Real.pi/2 by ring,Real.sin_two_pi_sub,Real.sin_pi_div_two]
  have s1 : Tendsto (fun t => b*Real.sin t) (𝓝[<] (Real.pi/2)) (𝓝 b) := by
    simpa using (Real.continuous_sin.continuousAt.const_mul b).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (Real.pi/2) ≤ 𝓝 (Real.pi/2))
  have s2 : Tendsto (fun t => b*Real.sin t) (𝓝[>] (Real.pi/2)) (𝓝 b) := by
    simpa using (Real.continuous_sin.continuousAt.const_mul b).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (Real.pi/2) ≤ 𝓝 (Real.pi/2))
  have s3 : Tendsto (fun t => b*Real.sin t) (𝓝[<] (3*Real.pi/2)) (𝓝 (-b)) := by
    simpa [hs3] using (Real.continuous_sin.continuousAt.const_mul b).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (3*Real.pi/2) ≤ 𝓝 (3*Real.pi/2))
  have s4 : Tendsto (fun t => b*Real.sin t) (𝓝[>] (3*Real.pi/2)) (𝓝 (-b)) := by
    simpa [hs3] using (Real.continuous_sin.continuousAt.const_mul b).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (3*Real.pi/2) ≤ 𝓝 (3*Real.pi/2))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change Tendsto (fun t => a/Real.cos t) _ _
    simpa only [div_eq_mul_inv] using! i1.const_mul_atTop ha
  · change Tendsto (fun t => b*Real.tan t) _ _
    simpa only [Real.tan_eq_sin_div_cos,div_eq_mul_inv,mul_assoc] using! s1.pos_mul_atTop hb i1
  · change Tendsto (fun t => a/Real.cos t) _ _
    simpa only [div_eq_mul_inv] using! (tendsto_const_mul_atBot_of_pos ha).mpr i2
  · change Tendsto (fun t => b*Real.tan t) _ _
    simpa only [Real.tan_eq_sin_div_cos,div_eq_mul_inv,mul_assoc] using! s2.pos_mul_atBot hb i2
  · change Tendsto (fun t => a/Real.cos t) _ _
    simpa only [div_eq_mul_inv] using! (tendsto_const_mul_atBot_of_pos ha).mpr i3
  · change Tendsto (fun t => b*Real.tan t) _ _
    simpa only [Real.tan_eq_sin_div_cos,div_eq_mul_inv,mul_assoc] using! s3.neg_mul_atBot (neg_lt_zero.mpr hb) i3
  · change Tendsto (fun t => a/Real.cos t) _ _
    simpa only [div_eq_mul_inv] using! i4.const_mul_atTop ha
  · change Tendsto (fun t => b*Real.tan t) _ _
    simpa only [Real.tan_eq_sin_div_cos,div_eq_mul_inv,mul_assoc] using! s4.neg_mul_atTop (neg_lt_zero.mpr hb) i4

theorem hyperbola_x_strictMonoOn {a b : ℝ} (ha : 0<a) {D : Set ℝ}
    (hD : Convex ℝ D) (hc : ∀ t∈D,Real.cos t≠0) (hs : ∀ t∈D,0<Real.sin t) :
    StrictMonoOn (hyperbolaX a) D := by
  apply strictMonoOn_of_deriv_pos hD
  · intro t ht
    exact (hyperbola_actual_derivatives a b t (hc t ht)).1.continuousAt.continuousWithinAt
  · intro t ht
    rw [(hyperbola_actual_derivatives a b t (hc t (interior_subset ht))).1.deriv]
    exact div_pos (mul_pos ha (hs t (interior_subset ht))) (sq_pos_of_ne_zero (hc t (interior_subset ht)))

theorem hyperbola_x_strictAntiOn {a b : ℝ} (ha : 0<a) {D : Set ℝ}
    (hD : Convex ℝ D) (hc : ∀ t∈D,Real.cos t≠0) (hs : ∀ t∈D,Real.sin t<0) :
    StrictAntiOn (hyperbolaX a) D := by
  apply strictAntiOn_of_deriv_neg hD
  · intro t ht
    exact (hyperbola_actual_derivatives a b t (hc t ht)).1.continuousAt.continuousWithinAt
  · intro t ht
    rw [(hyperbola_actual_derivatives a b t (hc t (interior_subset ht))).1.deriv]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha (hs t (interior_subset ht)))
      (sq_pos_of_ne_zero (hc t (interior_subset ht)))

theorem hyperbola_branch_coordinate_signs {a b t : ℝ} (ha : 0<a) (hb : 0<b)
    :
    (0<hyperbolaX a t ↔ 0<Real.cos t) ∧
    (hyperbolaX a t<0 ↔ Real.cos t<0) ∧
    (0<hyperbolaY b t ↔ 0<Real.sin t/Real.cos t) ∧
    (hyperbolaY b t<0 ↔ Real.sin t/Real.cos t<0) := by
  unfold hyperbolaX hyperbolaY
  rw [Real.tan_eq_sin_div_cos]
  constructor
  · exact div_pos_iff_of_pos_left ha
  · constructor
    · simpa [ha,not_lt_of_ge ha.le] using (div_neg_iff : a/Real.cos t<0 ↔ 0<a ∧ Real.cos t<0 ∨ a<0 ∧ 0<Real.cos t)
    · refine ⟨mul_pos_iff_of_pos_left hb,?_⟩
      simp only [mul_neg_iff,hb,not_lt_of_ge hb.le,true_and,false_and,or_false]

end calculus.Chapter04.Section04HyperbolaDomainRepair
