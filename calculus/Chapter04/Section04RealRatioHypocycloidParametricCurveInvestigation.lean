import calculus.Chapter04.Section04SinePerturbedCircleParametricCurveInvestigation
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hypocycloid với tỉ số thực trên khoảng tham số hữu hạn

Nguồn: `C04-S04-exercise-015.p10`, Ch4 dòng 2785. Xét `a > b > 0`, tỉ số thực `(a−b)/b` và khoảng `[0, 2π]`.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04RealRatioHypocycloidParametricCurveInvestigation
open calculus.Chapter04.Section01Parametric

def hypocycloidX (b k t : ℝ) : ℝ := b*k*Real.cos t+b*Real.cos (k*t)
def hypocycloidY (b k t : ℝ) : ℝ := b*k*Real.sin t-b*Real.sin (k*t)
def hypocycloidDomain : Set ℝ := Icc 0 (2*Real.pi)
def hypocycloidCurve (b k : ℝ) : Set (ℝ × ℝ) :=
  parametricCurve (hypocycloidX b k) (hypocycloidY b k) hypocycloidDomain

theorem hypocycloid_printed_parameter_bridge {a b : ℝ} (hab : b<a) (hb : 0<b) :
    0<(a-b)/b ∧ ∀ t : ℝ,
      hypocycloidX b ((a-b)/b) t = (a-b)*Real.cos t+b*Real.cos (((a-b)/b)*t) ∧
      hypocycloidY b ((a-b)/b) t = (a-b)*Real.sin t-b*Real.sin (((a-b)/b)*t) := by
  refine ⟨div_pos (sub_pos.mpr hab) hb, fun t => ?_⟩
  unfold hypocycloidX hypocycloidY
  have he : b*((a-b)/b)=a-b := by field_simp
  rw [he]
  exact ⟨rfl,rfl⟩

theorem hypocycloid_actual_derivatives (b k t : ℝ) :
    HasDerivAt (hypocycloidX b k) (-b*k*(Real.sin t+Real.sin (k*t))) t ∧
    HasDerivAt (hypocycloidY b k) (b*k*(Real.cos t-Real.cos (k*t))) t := by
  constructor
  · unfold hypocycloidX
    convert! ((Real.hasDerivAt_cos t).const_mul (b*k)).add
      (((Real.hasDerivAt_cos (k*t)).comp t ((hasDerivAt_id t).const_mul k)).const_mul b) using 1
    ring
  · unfold hypocycloidY
    convert! ((Real.hasDerivAt_sin t).const_mul (b*k)).sub
      (((Real.hasDerivAt_sin (k*t)).comp t ((hasDerivAt_id t).const_mul k)).const_mul b) using 1
    ring

theorem hypocycloid_actual_second_derivatives (b k t : ℝ) :
    HasDerivAt (deriv (hypocycloidX b k)) (-b*k*(Real.cos t+k*Real.cos (k*t))) t ∧
    HasDerivAt (deriv (hypocycloidY b k)) (-b*k*(Real.sin t-k*Real.sin (k*t))) t := by
  have hx : deriv (hypocycloidX b k) = fun u => -b*k*(Real.sin u+Real.sin (k*u)) :=
    funext (fun u => (hypocycloid_actual_derivatives b k u).1.deriv)
  have hy : deriv (hypocycloidY b k) = fun u => b*k*(Real.cos u-Real.cos (k*u)) :=
    funext (fun u => (hypocycloid_actual_derivatives b k u).2.deriv)
  rw [hx,hy]
  constructor
  · convert! ((Real.hasDerivAt_sin t).add
      ((Real.hasDerivAt_sin (k*t)).comp t ((hasDerivAt_id t).const_mul k))).const_mul (-b*k) using 1
    ring
  · convert! ((Real.hasDerivAt_cos t).sub
      ((Real.hasDerivAt_cos (k*t)).comp t ((hasDerivAt_id t).const_mul k))).const_mul (b*k) using 1
    ring

theorem hypocycloid_factored_velocity (b k t : ℝ) :
    deriv (hypocycloidX b k) t = -2*b*k*Real.sin ((1+k)*t/2)*Real.cos ((1-k)*t/2) ∧
    deriv (hypocycloidY b k) t = -2*b*k*Real.sin ((1+k)*t/2)*Real.sin ((1-k)*t/2) := by
  rw [(hypocycloid_actual_derivatives b k t).1.deriv,
    (hypocycloid_actual_derivatives b k t).2.deriv]
  have hs := Real.sin_add_sin t (k*t)
  have hc := Real.cos_sub_cos t (k*t)
  have he1 : (t+k*t)/2=(1+k)*t/2 := by ring
  have he2 : (t-k*t)/2=(1-k)*t/2 := by ring
  rw [he1,he2] at hs hc
  rw [hs,hc]
  constructor <;> ring

theorem hypocycloid_speed_square (b k t : ℝ) :
    deriv (hypocycloidX b k) t ^ 2 + deriv (hypocycloidY b k) t ^ 2 =
      4*(b*k)^2*Real.sin ((1+k)*t/2)^2 := by
  rw [(hypocycloid_factored_velocity b k t).1,(hypocycloid_factored_velocity b k t).2]
  nlinarith [congrArg (fun u : ℝ => 4*(b*k)^2*Real.sin ((1+k)*t/2)^2*u)
    (Real.sin_sq_add_cos_sq ((1-k)*t/2))]

theorem hypocycloid_singular_parameters {b k : ℝ} (hb : 0<b) (hk : 0<k) (t : ℝ) :
    (deriv (hypocycloidX b k) t = 0 ∧ deriv (hypocycloidY b k) t = 0) ↔
      ∃ j : ℤ, (j:ℝ)*Real.pi=(1+k)*t/2 := by
  have hp : 0<4*(b*k)^2 := mul_pos (by norm_num) (sq_pos_of_pos (mul_pos hb hk))
  rw [← Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨hx,hy⟩
    have h := hypocycloid_speed_square b k t
    rw [hx,hy] at h
    have hs : Real.sin ((1+k)*t/2)^2=0 := by nlinarith
    nlinarith [sq_nonneg (Real.sin ((1+k)*t/2))]
  · intro hs
    rw [(hypocycloid_factored_velocity b k t).1,(hypocycloid_factored_velocity b k t).2,hs]
    simp

theorem hypocycloid_curvature_determinant (b k t : ℝ) :
    deriv (hypocycloidX b k) t * deriv (deriv (hypocycloidY b k)) t -
      deriv (hypocycloidY b k) t * deriv (deriv (hypocycloidX b k)) t =
        (b*k)^2*(1-k)*(1-Real.cos ((1+k)*t)) := by
  rw [(hypocycloid_actual_derivatives b k t).1.deriv,
    (hypocycloid_actual_derivatives b k t).2.deriv,
    (hypocycloid_actual_second_derivatives b k t).1.deriv,
    (hypocycloid_actual_second_derivatives b k t).2.deriv]
  rw [show (1+k)*t=t+k*t by ring,Real.cos_add]
  nlinarith [congrArg (fun u : ℝ => (b*k)^2*u) (Real.sin_sq_add_cos_sq t),
    congrArg (fun u : ℝ => (b*k)^2*k*u) (Real.sin_sq_add_cos_sq (k*t))]


theorem hypocycloid_tangent_conditions {b k : ℝ} (hb : 0<b) (hk : 0<k) (t : ℝ) :
    (deriv (hypocycloidX b k) t=0 ↔
      Real.sin ((1+k)*t/2)=0 ∨ Real.cos ((1-k)*t/2)=0) ∧
    (deriv (hypocycloidY b k) t=0 ↔
      Real.sin ((1+k)*t/2)=0 ∨ Real.sin ((1-k)*t/2)=0) := by
  rw [(hypocycloid_factored_velocity b k t).1,(hypocycloid_factored_velocity b k t).2]
  simp [mul_eq_zero,hb.ne',hk.ne']

theorem hypocycloid_regular_tangent_slope (b k t : ℝ) (hb : b≠0) (hk : k≠0)
    (hs : Real.sin ((1+k)*t/2)≠0) :
    deriv (hypocycloidY b k) t / deriv (hypocycloidX b k) t = Real.tan ((1-k)*t/2) := by
  rw [(hypocycloid_factored_velocity b k t).1,(hypocycloid_factored_velocity b k t).2,
    Real.tan_eq_sin_div_cos]
  field_simp


theorem hypocycloid_variation_signs {b k : ℝ} (hb : 0<b) (hk : 0<k) (t : ℝ) :
    (0<deriv (hypocycloidX b k) t ↔
      Real.sin ((1+k)*t/2)*Real.cos ((1-k)*t/2)<0) ∧
    (0<deriv (hypocycloidY b k) t ↔
      Real.sin ((1+k)*t/2)*Real.sin ((1-k)*t/2)<0) := by
  have hp : 0<2*b*k := mul_pos (mul_pos (by norm_num) hb) hk
  rw [(hypocycloid_factored_velocity b k t).1,(hypocycloid_factored_velocity b k t).2]
  have he (u : ℝ) : 0 < -(2*b*k)*u ↔ u < 0 := by
    rw [neg_mul,neg_pos]
    simp only [mul_neg_iff,hp,not_lt_of_ge hp.le,true_and,false_and,or_false]
  constructor
  · rw [show -2*b*k*Real.sin ((1+k)*t/2)*Real.cos ((1-k)*t/2)=
        -(2*b*k)*(Real.sin ((1+k)*t/2)*Real.cos ((1-k)*t/2)) by ring]
    exact he _
  · rw [show -2*b*k*Real.sin ((1+k)*t/2)*Real.sin ((1-k)*t/2)=
        -(2*b*k)*(Real.sin ((1+k)*t/2)*Real.sin ((1-k)*t/2)) by ring]
    exact he _

theorem hypocycloid_radius_square (b k t : ℝ) :
    hypocycloidX b k t ^ 2 + hypocycloidY b k t ^ 2 =
      (b*k)^2+b^2+2*b^2*k*Real.cos ((1+k)*t) := by
  unfold hypocycloidX hypocycloidY
  rw [show (1+k)*t=t+k*t by ring,Real.cos_add]
  nlinarith [congrArg (fun u : ℝ => (b*k)^2*u) (Real.sin_sq_add_cos_sq t),
    congrArg (fun u : ℝ => b^2*u) (Real.sin_sq_add_cos_sq (k*t))]

theorem hypocycloid_exact_radial_bounds {b k : ℝ} (hb : 0<b) (hk : 0<k) (t : ℝ) :
    (b*k-b)^2 ≤ hypocycloidX b k t^2+hypocycloidY b k t^2 ∧
      hypocycloidX b k t^2+hypocycloidY b k t^2 ≤ (b*k+b)^2 := by
  rw [hypocycloid_radius_square]
  have hp : 0≤2*b^2*k := by positivity
  have hlo := mul_nonneg hp (show 0≤Real.cos ((1+k)*t)+1 by linarith [Real.neg_one_le_cos ((1+k)*t)])
  have hhi := mul_nonneg hp (show 0≤1-Real.cos ((1+k)*t) by linarith [Real.cos_le_one ((1+k)*t)])
  constructor <;> nlinarith

theorem hypocycloid_radial_extreme_parameters {b k : ℝ} (hk : 0<k) :
    0∈hypocycloidDomain ∧ Real.pi/(1+k)∈hypocycloidDomain ∧
    hypocycloidX b k 0^2+hypocycloidY b k 0^2=(b*k+b)^2 ∧
    hypocycloidX b k (Real.pi/(1+k))^2+hypocycloidY b k (Real.pi/(1+k))^2=(b*k-b)^2 := by
  have hp : 0<1+k := by linarith
  have he : (1+k)*(Real.pi/(1+k))=Real.pi := by field_simp
  refine ⟨⟨le_rfl,by positivity⟩,⟨(div_pos Real.pi_pos hp).le,?_⟩,?_,?_⟩
  · apply (div_le_iff₀ hp).mpr
    nlinarith [Real.pi_pos,mul_pos Real.pi_pos hk]
  · rw [hypocycloid_radius_square]
    simp
    ring
  · rw [hypocycloid_radius_square,he,Real.cos_pi]
    ring

theorem hypocycloid_continuous_compact (b k : ℝ) :
    Continuous (hypocycloidX b k) ∧ Continuous (hypocycloidY b k) ∧ IsCompact (hypocycloidCurve b k) := by
  have hx : Continuous (hypocycloidX b k) := (Real.continuous_cos.const_mul (b*k)).add
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul b)
  have hy : Continuous (hypocycloidY b k) := (Real.continuous_sin.const_mul (b*k)).sub
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul b)
  exact ⟨hx,hy,isCompact_Icc.image (hx.prodMk hy)⟩


theorem hypocycloid_parameter_reflection (b k t : ℝ) :
    hypocycloidX b k (-t)=hypocycloidX b k t ∧ hypocycloidY b k (-t)=-hypocycloidY b k t := by
  simp [hypocycloidX,hypocycloidY,show k*(-t)=-(k*t) by ring]
  ring

theorem hypocycloid_segment_degeneracy (b t : ℝ) :
    hypocycloidX b 1 t=2*b*Real.cos t ∧ hypocycloidY b 1 t=0 := by
  simp [hypocycloidX,hypocycloidY]
  ring


theorem hypocycloid_endpoint_closure_iff {b k : ℝ} (hb : b≠0) :
    (hypocycloidX b k (2*Real.pi)=hypocycloidX b k 0 ∧
      hypocycloidY b k (2*Real.pi)=hypocycloidY b k 0) ↔ ∃ j : ℤ, (j:ℝ)=k := by
  constructor
  · rintro ⟨hx,_⟩
    simp only [hypocycloidX,Real.cos_two_pi,Real.cos_zero,mul_one,mul_zero] at hx
    have hc : Real.cos (k*(2*Real.pi))=1 := by
      apply (mul_left_cancel₀ hb)
      linarith
    obtain ⟨j,hj⟩ := (Real.cos_eq_one_iff _).mp hc
    refine ⟨j,?_⟩
    exact (mul_right_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero)) hj
  · rintro ⟨j,rfl⟩
    have hs : Real.sin ((j:ℝ)*(2*Real.pi))=0 := by
      simpa using Real.sin_add_int_mul_two_pi 0 j
    simp [hypocycloidX,hypocycloidY,Real.cos_int_mul_two_pi,hs]


theorem hypocycloid_self_intersection_criterion {b k u v : ℝ} (hb : b≠0) :
    (hypocycloidX b k u=hypocycloidX b k v ∧ hypocycloidY b k u=hypocycloidY b k v) ↔
      (k*(Real.cos u-Real.cos v)=-(Real.cos (k*u)-Real.cos (k*v)) ∧
       k*(Real.sin u-Real.sin v)=Real.sin (k*u)-Real.sin (k*v)) := by
  unfold hypocycloidX hypocycloidY
  constructor <;> rintro ⟨hx,hy⟩ <;> constructor
  · apply (mul_left_cancel₀ hb); nlinarith
  · apply (mul_left_cancel₀ hb); nlinarith
  · nlinarith [congrArg (fun z : ℝ => b*z) hx]
  · nlinarith [congrArg (fun z : ℝ => b*z) hy]

/-!
## Dây cung tại điểm suy biến, tử số độ cong và trường hợp đoạn thẳng
-/
open calculus.Chapter03.Section02


theorem zero_velocity_normalized_secant_limit {f f' f'' : ℝ → ℝ} {t₀ : ℝ}
    (h1 : ∀ t, HasDerivAt f (f' t) t)
    (h2 : ∀ t, HasDerivAt f' (f'' t) t)
    (hcont : Continuous f'') (hv : f' t₀ = 0) :
    Tendsto (fun t : ℝ ↦ (f t - f t₀) / (t - t₀) ^ 2)
      (𝓝[≠] t₀) (𝓝 (f'' t₀ / 2)) := by
  have hlin (t : ℝ) : HasDerivAt (fun u : ℝ ↦ 2 * (u - t₀)) 2 t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).sub_const t₀).const_mul 2
  have hpow (t : ℝ) : HasDerivAt (fun u : ℝ ↦ (u - t₀) ^ 2) (2 * (t - t₀)) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq] using
      ((hasDerivAt_id t).sub_const t₀).fun_pow 2
  have hlinear : Tendsto (fun t : ℝ ↦ 2 * (t - t₀)) (𝓝[≠] t₀) (𝓝 0) := by
    have h := (hlin t₀).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
    simpa only [sub_self, mul_zero] using h
  have hvelocity : Tendsto f' (𝓝[≠] t₀) (𝓝 0) := by
    simpa only [hv] using (h2 t₀).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
  have hinner : Tendsto (fun t : ℝ ↦ f' t / (2 * (t - t₀)))
      (𝓝[≠] t₀) (𝓝 (f'' t₀ / 2)) := by
    apply calculus.Chapter04.Section04.lhopital_zero_punctured
      (Eventually.of_forall h2) (Eventually.of_forall hlin)
      (Eventually.of_forall (fun _ ↦ by norm_num)) hvelocity hlinear
    exact ((hcont.continuousAt (x := t₀)).tendsto.div tendsto_const_nhds
      (by norm_num : (2 : ℝ) ≠ 0)).mono_left nhdsWithin_le_nhds
  apply calculus.Chapter04.Section04.lhopital_zero_punctured
    (Eventually.of_forall (fun t ↦ (h1 t).sub_const (f t₀)))
    (Eventually.of_forall hpow)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hn : t ≠ t₀ := by simpa only [mem_compl_iff, mem_singleton_iff] using ht
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hn)
  · simpa only [sub_self] using ((h1 t₀).sub_const (f t₀)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
  · simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (hpow t₀).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
  · exact hinner


theorem hypocycloid_domain_accumulation {t₀ : ℝ} (ht : t₀ ∈ hypocycloidDomain) :
    AccumulationPointOf hypocycloidDomain t₀ := by
  change t₀ ∈ Icc 0 (2 * Real.pi) at ht
  intro δ hδ
  by_cases htop : t₀ = 2 * Real.pi
  · subst t₀
    have hm : 0 < min δ (2 * Real.pi) := lt_min hδ (by positivity)
    refine ⟨2 * Real.pi - min δ (2 * Real.pi) / 2, ?_, ?_, ?_, ?_⟩
    · change 0 ≤ _ ∧ _ ≤ 2 * Real.pi
      constructor <;> linarith [min_le_right δ (2 * Real.pi)]
    · linarith
    · linarith [min_le_left δ (2 * Real.pi)]
    · linarith
  · have hright : t₀ < 2 * Real.pi := lt_of_le_of_ne ht.2 htop
    have hm : 0 < min δ (2 * Real.pi - t₀) := lt_min hδ (by linarith)
    refine ⟨t₀ + min δ (2 * Real.pi - t₀) / 2, ?_, ?_, ?_, ?_⟩
    · change 0 ≤ _ ∧ _ ≤ 2 * Real.pi
      constructor <;> linarith [ht.1, min_le_right δ (2 * Real.pi - t₀)]
    · linarith
    · linarith
    · linarith [min_le_left δ (2 * Real.pi - t₀)]


theorem normalized_secant_domain_accumulation {D : Set ℝ} {f : ℝ → ℝ} {t₀ L : ℝ}
    (ha : AccumulationPointOf D t₀)
    (hlim : Tendsto (fun t : ℝ ↦ (f t - f t₀) / (t - t₀) ^ 2) (𝓝[≠] t₀) (𝓝 L))
    (hL : L ≠ 0) : AccumulationPointOf {t | t ∈ D ∧ f t - f t₀ ≠ 0} t₀ := by
  let : (𝓝[D \ {t₀}] t₀).NeBot := accumulationPointOf_iff_neBot.mp ha
  have hp : 𝓝[D \ {t₀}] t₀ ≤ 𝓝[≠] t₀ := nhdsWithin_mono _ (by
    intro t ht
    exact ht.2)
  have hne : ∀ᶠ t in 𝓝[D \ {t₀}] t₀, f t - f t₀ ≠ 0 := by
    filter_upwards [(hlim.eventually_ne hL).filter_mono hp] with t ht
    exact (div_ne_zero_iff.mp ht).1
  apply accumulationPointOf_iff_neBot.mpr
  apply Filter.neBot_of_le (f := 𝓝[D \ {t₀}] t₀)
  apply nhdsWithin_le_iff.mpr
  filter_upwards [self_mem_nhdsWithin, hne] with t ht hn
  exact ⟨⟨ht.1, hn⟩, ht.2⟩


theorem hypocycloid_singular_acceleration {b k t₀ : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hs : Real.sin ((1 + k) * t₀ / 2) = 0) :
    deriv (hypocycloidX b k) t₀ = 0 ∧ deriv (hypocycloidY b k) t₀ = 0 ∧
      deriv (deriv (hypocycloidX b k)) t₀ = -b * k * (1 + k) * Real.cos t₀ ∧
      deriv (deriv (hypocycloidY b k)) t₀ = -b * k * (1 + k) * Real.sin t₀ ∧
      0 < deriv (deriv (hypocycloidX b k)) t₀ ^ 2 +
        deriv (deriv (hypocycloidY b k)) t₀ ^ 2 := by
  have hx0 : deriv (hypocycloidX b k) t₀ = 0 := by
    rw [(hypocycloid_factored_velocity b k t₀).1, hs]
    ring
  have hy0 : deriv (hypocycloidY b k) t₀ = 0 := by
    rw [(hypocycloid_factored_velocity b k t₀).2, hs]
    ring
  have hbk : b * k ≠ 0 := (mul_pos hb hk).ne'
  have hs' : Real.sin (k * t₀) = -Real.sin t₀ := by
    have he := hx0
    rw [(hypocycloid_actual_derivatives b k t₀).1.deriv] at he
    have hh : Real.sin t₀ + Real.sin (k * t₀) = 0 :=
      (mul_eq_zero.mp he).resolve_left (mul_ne_zero (neg_ne_zero.mpr hb.ne') hk.ne')
    linarith
  have hc' : Real.cos (k * t₀) = Real.cos t₀ := by
    have he := hy0
    rw [(hypocycloid_actual_derivatives b k t₀).2.deriv] at he
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hbk)).symm
  have hx2 : deriv (deriv (hypocycloidX b k)) t₀ = -b * k * (1 + k) * Real.cos t₀ := by
    rw [(hypocycloid_actual_second_derivatives b k t₀).1.deriv, hc']
    ring
  have hy2 : deriv (deriv (hypocycloidY b k)) t₀ = -b * k * (1 + k) * Real.sin t₀ := by
    rw [(hypocycloid_actual_second_derivatives b k t₀).2.deriv, hs']
    ring
  refine ⟨hx0, hy0, hx2, hy2, ?_⟩
  rw [hx2, hy2]
  have he : (-b * k * (1 + k) * Real.cos t₀) ^ 2 +
      (-b * k * (1 + k) * Real.sin t₀) ^ 2 = (b * k * (1 + k)) ^ 2 := by
    nlinarith [congrArg (fun q : ℝ ↦ (b * k * (1 + k)) ^ 2 * q)
      (Real.sin_sq_add_cos_sq t₀)]
  rw [he]
  exact sq_pos_of_pos (mul_pos (mul_pos hb hk) (by linarith))


theorem hypocycloid_singular_normalized_secants {b k t₀ : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hs : Real.sin ((1 + k) * t₀ / 2) = 0) :
    Tendsto (fun t : ℝ ↦ (hypocycloidX b k t - hypocycloidX b k t₀) / (t - t₀) ^ 2)
      (𝓝[≠] t₀) (𝓝 (-b * k * (1 + k) * Real.cos t₀ / 2)) ∧
      Tendsto (fun t : ℝ ↦ (hypocycloidY b k t - hypocycloidY b k t₀) / (t - t₀) ^ 2)
      (𝓝[≠] t₀) (𝓝 (-b * k * (1 + k) * Real.sin t₀ / 2)) := by
  have hj := hypocycloid_singular_acceleration hb hk hs
  have hcX : Continuous (deriv (deriv (hypocycloidX b k))) := by
    rw [show deriv (deriv (hypocycloidX b k)) =
        fun u ↦ -b * k * (Real.cos u + k * Real.cos (k * u)) from
      funext (fun u ↦ (hypocycloid_actual_second_derivatives b k u).1.deriv)]
    fun_prop
  have hcY : Continuous (deriv (deriv (hypocycloidY b k))) := by
    rw [show deriv (deriv (hypocycloidY b k)) =
        fun u ↦ -b * k * (Real.sin u - k * Real.sin (k * u)) from
      funext (fun u ↦ (hypocycloid_actual_second_derivatives b k u).2.deriv)]
    fun_prop
  constructor
  · have h := zero_velocity_normalized_secant_limit
      (fun t ↦ (hypocycloid_actual_derivatives b k t).1.differentiableAt.hasDerivAt)
      (fun t ↦ (hypocycloid_actual_second_derivatives b k t).1.differentiableAt.hasDerivAt)
      hcX hj.1
    simpa only [hj.2.2.1] using h
  · have h := zero_velocity_normalized_secant_limit
      (fun t ↦ (hypocycloid_actual_derivatives b k t).2.differentiableAt.hasDerivAt)
      (fun t ↦ (hypocycloid_actual_second_derivatives b k t).2.differentiableAt.hasDerivAt)
      hcY hj.2.1
    simpa only [hj.2.2.2.1] using h


theorem hypocycloid_singular_tangent_slopes {b k t₀ : ℝ} (hb : 0 < b) (hk : 0 < k)
    (ht : t₀ ∈ hypocycloidDomain) (hs : Real.sin ((1 + k) * t₀ / 2) = 0) :
    (Real.cos t₀ ≠ 0 →
      DomainLimit {t | t ∈ hypocycloidDomain ∧ hypocycloidX b k t - hypocycloidX b k t₀ ≠ 0}
        (fun t ↦ (hypocycloidY b k t - hypocycloidY b k t₀) /
          (hypocycloidX b k t - hypocycloidX b k t₀)) t₀ (Real.sin t₀ / Real.cos t₀)) ∧
    (Real.sin t₀ ≠ 0 →
      DomainLimit {t | t ∈ hypocycloidDomain ∧ hypocycloidY b k t - hypocycloidY b k t₀ ≠ 0}
        (fun t ↦ (hypocycloidX b k t - hypocycloidX b k t₀) /
          (hypocycloidY b k t - hypocycloidY b k t₀)) t₀ (Real.cos t₀ / Real.sin t₀)) := by
  have hn := hypocycloid_singular_normalized_secants hb hk hs
  have hm : -b * k * (1 + k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hb.ne') hk.ne') (by linarith)
  have hp : ∀ᶠ t : ℝ in 𝓝[≠] t₀, (t - t₀) ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact pow_ne_zero 2 (sub_ne_zero.mpr (by
      simpa only [mem_compl_iff, mem_singleton_iff] using ht))
  constructor
  · intro hc
    have hx : -b * k * (1 + k) * Real.cos t₀ / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hm hc) (by norm_num)
    have ha := normalized_secant_domain_accumulation (hypocycloid_domain_accumulation ht) hn.1 hx
    have hratio := hn.2.div hn.1 hx
    have hv : (-b * k * (1 + k) * Real.sin t₀ / 2) /
        (-b * k * (1 + k) * Real.cos t₀ / 2) = Real.sin t₀ / Real.cos t₀ := by
      rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0), mul_div_mul_left _ _ hm]
    rw [hv] at hratio
    have h : Tendsto (fun t ↦ (hypocycloidY b k t - hypocycloidY b k t₀) /
        (hypocycloidX b k t - hypocycloidX b k t₀)) (𝓝[≠] t₀)
        (𝓝 (Real.sin t₀ / Real.cos t₀)) := by
      apply hratio.congr'
      filter_upwards [hp] with t ht
      exact div_div_div_cancel_right₀ ht _ _
    apply (domainLimit_iff_tendsto ha).mpr
    exact h.mono_left (nhdsWithin_mono _ (by intro t ht; exact ht.2))
  · intro hsin
    have hy : -b * k * (1 + k) * Real.sin t₀ / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hm hsin) (by norm_num)
    have ha := normalized_secant_domain_accumulation (hypocycloid_domain_accumulation ht) hn.2 hy
    have hratio := hn.1.div hn.2 hy
    have hv : (-b * k * (1 + k) * Real.cos t₀ / 2) /
        (-b * k * (1 + k) * Real.sin t₀ / 2) = Real.cos t₀ / Real.sin t₀ := by
      rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0), mul_div_mul_left _ _ hm]
    rw [hv] at hratio
    have h : Tendsto (fun t ↦ (hypocycloidX b k t - hypocycloidX b k t₀) /
        (hypocycloidY b k t - hypocycloidY b k t₀)) (𝓝[≠] t₀)
        (𝓝 (Real.cos t₀ / Real.sin t₀)) := by
      apply hratio.congr'
      filter_upwards [hp] with t ht
      exact div_div_div_cancel_right₀ ht _ _
    apply (domainLimit_iff_tendsto ha).mpr
    exact h.mono_left (nhdsWithin_mono _ (by intro t ht; exact ht.2))


theorem hypocycloid_segment_full_image {b : ℝ} (hb : 0 < b) :
    hypocycloidCurve b 1 = {p : ℝ × ℝ | -2 * b ≤ p.1 ∧ p.1 ≤ 2 * b ∧ p.2 = 0} := by
  ext p
  constructor
  · rintro ⟨t, _ht, rfl⟩
    change -2 * b ≤ hypocycloidX b 1 t ∧ hypocycloidX b 1 t ≤ 2 * b ∧ hypocycloidY b 1 t = 0
    rw [(hypocycloid_segment_degeneracy b t).1, (hypocycloid_segment_degeneracy b t).2]
    refine ⟨?_, ?_, rfl⟩
    · nlinarith [mul_nonneg hb.le (show 0 ≤ Real.cos t + 1 by linarith [Real.neg_one_le_cos t])]
    · nlinarith [mul_nonneg hb.le (show 0 ≤ 1 - Real.cos t by linarith [Real.cos_le_one t])]
  · rintro ⟨hlo, hhi, hy⟩
    have hpos : 0 < 2 * b := by positivity
    have hclo : -1 ≤ p.1 / (2 * b) := (le_div_iff₀ hpos).mpr (by linarith)
    have hchi : p.1 / (2 * b) ≤ 1 := (div_le_iff₀ hpos).mpr (by linarith)
    refine ⟨Real.arccos (p.1 / (2 * b)), ?_, ?_⟩
    · change 0 ≤ _ ∧ _ ≤ 2 * Real.pi
      exact ⟨Real.arccos_nonneg _, by linarith [Real.arccos_le_pi (p.1 / (2 * b)), Real.pi_pos]⟩
    · apply Prod.ext
      · change hypocycloidX b 1 _ = p.1
        rw [(hypocycloid_segment_degeneracy b _).1, Real.cos_arccos hclo hchi]
        exact mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hb.ne')
      · change hypocycloidY b 1 _ = p.2
        rw [(hypocycloid_segment_degeneracy b _).2]
        exact hy.symm


theorem hypocycloid_regular_curvature_numerator_sign {b k t : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hs : Real.sin ((1 + k) * t / 2) ≠ 0) :
    (0 < deriv (hypocycloidX b k) t * deriv (deriv (hypocycloidY b k)) t -
      deriv (hypocycloidY b k) t * deriv (deriv (hypocycloidX b k)) t ↔ k < 1) ∧
    (deriv (hypocycloidX b k) t * deriv (deriv (hypocycloidY b k)) t -
      deriv (hypocycloidY b k) t * deriv (deriv (hypocycloidX b k)) t = 0 ↔ k = 1) ∧
    (deriv (hypocycloidX b k) t * deriv (deriv (hypocycloidY b k)) t -
      deriv (hypocycloidY b k) t * deriv (deriv (hypocycloidX b k)) t < 0 ↔ 1 < k) := by
  have hc : 0 < 1 - Real.cos ((1 + k) * t) := by
    have he := Real.cos_two_mul ((1 + k) * t / 2)
    rw [show 2 * ((1 + k) * t / 2) = (1 + k) * t by ring] at he
    nlinarith [Real.sin_sq_add_cos_sq ((1 + k) * t / 2), sq_pos_of_ne_zero hs]
  have hp : 0 < (b * k) ^ 2 * (1 - Real.cos ((1 + k) * t)) :=
    mul_pos (sq_pos_of_pos (mul_pos hb hk)) hc
  rw [hypocycloid_curvature_determinant]
  have he : (b * k) ^ 2 * (1 - k) * (1 - Real.cos ((1 + k) * t)) =
      ((b * k) ^ 2 * (1 - Real.cos ((1 + k) * t))) * (1 - k) := by ring
  rw [he]
  constructor
  · exact (mul_pos_iff_of_pos_left hp).trans sub_pos
  · constructor
    · rw [mul_eq_zero]
      simp only [hp.ne', false_or]
      constructor <;> intro h <;> linarith
    · rw [mul_neg_iff]
      simp [hp, not_lt_of_ge hp.le, sub_neg]


theorem hypocycloid_regular_slope_derivative {b k t : ℝ}
    (hx : deriv (hypocycloidX b k) t ≠ 0) :
    HasDerivAt (fun u ↦ deriv (hypocycloidY b k) u / deriv (hypocycloidX b k) u)
      ((deriv (hypocycloidX b k) t * deriv (deriv (hypocycloidY b k)) t -
        deriv (hypocycloidY b k) t * deriv (deriv (hypocycloidX b k)) t) /
        deriv (hypocycloidX b k) t ^ 2) t := by
  have h := ((hypocycloid_actual_second_derivatives b k t).2.differentiableAt.hasDerivAt).div
    ((hypocycloid_actual_second_derivatives b k t).1.differentiableAt.hasDerivAt) hx
  apply h.congr_deriv
  ring


theorem hypocycloid_coordinate_variation {b k : ℝ} (hb : 0 < b) (hk : 0 < k)
    {D : Set ℝ} (hD : Convex ℝ D) :
    ((∀ t ∈ interior D, Real.sin ((1 + k) * t / 2) * Real.cos ((1 - k) * t / 2) < 0) →
      StrictMonoOn (hypocycloidX b k) D) ∧
    ((∀ t ∈ interior D, 0 < Real.sin ((1 + k) * t / 2) * Real.cos ((1 - k) * t / 2)) →
      StrictAntiOn (hypocycloidX b k) D) ∧
    ((∀ t ∈ interior D, Real.sin ((1 + k) * t / 2) * Real.sin ((1 - k) * t / 2) < 0) →
      StrictMonoOn (hypocycloidY b k) D) ∧
    ((∀ t ∈ interior D, 0 < Real.sin ((1 + k) * t / 2) * Real.sin ((1 - k) * t / 2)) →
      StrictAntiOn (hypocycloidY b k) D) := by
  have hC := hypocycloid_continuous_compact b k
  have hn : -2 * b * k < 0 := by nlinarith [mul_pos hb hk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply strictMonoOn_of_deriv_pos hD hC.1.continuousOn
    intro t ht
    exact (hypocycloid_variation_signs hb hk t).1.mpr (h t ht)
  · intro h
    apply strictAntiOn_of_deriv_neg hD hC.1.continuousOn
    intro t ht
    rw [(hypocycloid_factored_velocity b k t).1]
    have he : -2 * b * k * Real.sin ((1 + k) * t / 2) * Real.cos ((1 - k) * t / 2) =
        (-2 * b * k) * (Real.sin ((1 + k) * t / 2) * Real.cos ((1 - k) * t / 2)) := by ring
    rw [he]
    exact mul_neg_of_neg_of_pos hn (h t ht)
  · intro h
    apply strictMonoOn_of_deriv_pos hD hC.2.1.continuousOn
    intro t ht
    exact (hypocycloid_variation_signs hb hk t).2.mpr (h t ht)
  · intro h
    apply strictAntiOn_of_deriv_neg hD hC.2.1.continuousOn
    intro t ht
    rw [(hypocycloid_factored_velocity b k t).2]
    have he : -2 * b * k * Real.sin ((1 + k) * t / 2) * Real.sin ((1 - k) * t / 2) =
        (-2 * b * k) * (Real.sin ((1 + k) * t / 2) * Real.sin ((1 - k) * t / 2)) := by ring
    rw [he]
    exact mul_neg_of_neg_of_pos hn (h t ht)


theorem hypocycloid_regular_secant_slopes (b k : ℝ) {t₀ : ℝ} (ht : t₀ ∈ hypocycloidDomain) :
    (deriv (hypocycloidX b k) t₀ ≠ 0 →
      DomainLimit {t | t ∈ hypocycloidDomain ∧ hypocycloidX b k t - hypocycloidX b k t₀ ≠ 0}
        (fun t ↦ (hypocycloidY b k t - hypocycloidY b k t₀) /
          (hypocycloidX b k t - hypocycloidX b k t₀)) t₀
        (deriv (hypocycloidY b k) t₀ / deriv (hypocycloidX b k) t₀)) ∧
    (deriv (hypocycloidY b k) t₀ ≠ 0 →
      DomainLimit {t | t ∈ hypocycloidDomain ∧ hypocycloidY b k t - hypocycloidY b k t₀ ≠ 0}
        (fun t ↦ (hypocycloidX b k t - hypocycloidX b k t₀) /
          (hypocycloidY b k t - hypocycloidY b k t₀)) t₀
        (deriv (hypocycloidX b k) t₀ / deriv (hypocycloidY b k) t₀)) := by
  have hacc (f : ℝ → ℝ) (hf : HasDerivAt f (deriv f t₀) t₀) (hne : deriv f t₀ ≠ 0) :
      AccumulationPointOf {t | t ∈ hypocycloidDomain ∧ f t - f t₀ ≠ 0} t₀ := by
    let : (𝓝[hypocycloidDomain \ {t₀}] t₀).NeBot :=
      accumulationPointOf_iff_neBot.mp (hypocycloid_domain_accumulation ht)
    have hp : 𝓝[hypocycloidDomain \ {t₀}] t₀ ≤ 𝓝[≠] t₀ :=
      nhdsWithin_mono _ (by intro t ht; exact ht.2)
    have hev : ∀ᶠ t in 𝓝[≠] t₀, f t ≠ f t₀ := hf.eventually_ne hne
    apply accumulationPointOf_iff_neBot.mpr
    apply Filter.neBot_of_le (f := 𝓝[hypocycloidDomain \ {t₀}] t₀)
    apply nhdsWithin_le_iff.mpr
    filter_upwards [self_mem_nhdsWithin, hev.filter_mono hp] with t ht hn
    exact ⟨⟨ht.1, sub_ne_zero.mpr hn⟩, ht.2⟩
  have hx := (hypocycloid_actual_derivatives b k t₀).1.differentiableAt.hasDerivAt
  have hy := (hypocycloid_actual_derivatives b k t₀).2.differentiableAt.hasDerivAt
  constructor
  · intro hnx
    exact calculus.Chapter03.Section03Exercises.ratio_of_derivative_slopes
      (hacc _ hx hnx) (hy.sub_const _) (hx.sub_const _) (sub_self _) (sub_self _) hnx
  · intro hny
    exact calculus.Chapter03.Section03Exercises.ratio_of_derivative_slopes
      (hacc _ hy hny) (hx.sub_const _) (hy.sub_const _) (sub_self _) (sub_self _) hny


theorem hypocycloid_actual_third_derivatives (b k t : ℝ) :
    HasDerivAt (deriv (deriv (hypocycloidX b k)))
      (b * k * (Real.sin t + k ^ 2 * Real.sin (k * t))) t ∧
    HasDerivAt (deriv (deriv (hypocycloidY b k)))
      (-b * k * (Real.cos t - k ^ 2 * Real.cos (k * t))) t := by
  have hx : deriv (deriv (hypocycloidX b k)) =
      fun u ↦ -b * k * (Real.cos u + k * Real.cos (k * u)) :=
    funext (fun u ↦ (hypocycloid_actual_second_derivatives b k u).1.deriv)
  have hy : deriv (deriv (hypocycloidY b k)) =
      fun u ↦ -b * k * (Real.sin u - k * Real.sin (k * u)) :=
    funext (fun u ↦ (hypocycloid_actual_second_derivatives b k u).2.deriv)
  rw [hx, hy]
  constructor
  · have h := ((Real.hasDerivAt_cos t).fun_add
      (((hasDerivAt_id t).const_mul k).cos.const_mul k)).const_mul (-b * k)
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring
  · have h := ((Real.hasDerivAt_sin t).fun_sub
      (((hasDerivAt_id t).const_mul k).sin.const_mul k)).const_mul (-b * k)
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring


theorem hypocycloid_singular_jet_determinant {b k t₀ : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hs : Real.sin ((1 + k) * t₀ / 2) = 0) :
    deriv (deriv (hypocycloidX b k)) t₀ * deriv (deriv (deriv (hypocycloidY b k))) t₀ -
      deriv (deriv (hypocycloidY b k)) t₀ * deriv (deriv (deriv (hypocycloidX b k))) t₀ =
      (b * k) ^ 2 * (1 + k) ^ 2 * (1 - k) := by
  have hj := hypocycloid_singular_acceleration hb hk hs
  have hs' : Real.sin (k * t₀) = -Real.sin t₀ := by
    have he := hj.1
    rw [(hypocycloid_actual_derivatives b k t₀).1.deriv] at he
    have hh : Real.sin t₀ + Real.sin (k * t₀) = 0 :=
      (mul_eq_zero.mp he).resolve_left (mul_ne_zero (neg_ne_zero.mpr hb.ne') hk.ne')
    linarith
  have hc' : Real.cos (k * t₀) = Real.cos t₀ := by
    have he := hj.2.1
    rw [(hypocycloid_actual_derivatives b k t₀).2.deriv] at he
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_pos hb hk).ne')).symm
  rw [hj.2.2.1, hj.2.2.2.1,
    (hypocycloid_actual_third_derivatives b k t₀).1.deriv,
    (hypocycloid_actual_third_derivatives b k t₀).2.deriv, hs', hc']
  nlinarith [congrArg (fun q : ℝ ↦ (b * k) ^ 2 * (1 + k) ^ 2 * (1 - k) * q)
    (Real.sin_sq_add_cos_sq t₀)]

end calculus.Chapter04.Section04RealRatioHypocycloidParametricCurveInvestigation
