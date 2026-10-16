import calculus.Chapter04.Section01Derivatives
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Bài 14–16,18: giới hạn từ đạo hàm và hàm Lipschitz

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 600–616, dòng 631–638.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01LimitExercises
open Filter Set
open scoped Topology


theorem difference_quotient_limit {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) :
    Tendsto (fun y : ℝ ↦ (f y - f x) / (y - x)) (𝓝[≠] x) (𝓝 d) := by
  have h := hf.tendsto_slope
  rw [calculus.Chapter04.Section01Derivatives.slope_eq_difference_quotient] at h
  exact h

/-- Bài 14(a): giới hạn của thương hiệu hai tích với `x`. -/
theorem coordinate_difference_limit {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    Tendsto (fun y : ℝ ↦ (y * f x - x * f y) / (y - x)) (𝓝[≠] x)
      (𝓝 (f x - x * deriv f x)) := by
  have h := ((hasDerivAt_id x).mul_const (f x)).sub (hf.hasDerivAt.const_mul x)
  have hd : HasDerivAt (fun y : ℝ ↦ y * f x - x * f y) (f x - x * deriv f x) x := by
    apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
    simp only [one_mul]
  have hlim := difference_quotient_limit hd
  simpa only [sub_self, sub_zero] using hlim

/-- Bài 14(b): tử là hiệu hai tích, với các giá trị hàm cố định tại `x₀`. -/
theorem crossed_difference_limit {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    Tendsto (fun y : ℝ ↦ (f y * g x - f x * g y) / (y - x)) (𝓝[≠] x)
      (𝓝 (g x * deriv f x - f x * deriv g x)) := by
  have h := (hf.hasDerivAt.mul_const (g x)).sub (hg.hasDerivAt.const_mul (f x))
  have hd : HasDerivAt (fun y : ℝ ↦ f y * g x - f x * g y)
      (g x * deriv f x - f x * deriv g x) x := by
    apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
    ring
  have hlim := difference_quotient_limit hd
  simpa only [sub_self, sub_zero] using hlim


theorem affine_parameter_hasDerivAt {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    HasDerivAt (fun h : ℝ ↦ f (x + c * h)) (c * deriv f x) 0 := by
  have hi : HasDerivAt (fun h : ℝ ↦ x + c * h) c 0 := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id (0 : ℝ)).const_mul c).const_add x
  apply (hf.hasDerivAt.comp_of_eq 0 hi (by ring)).congr_deriv
  ring

/-- Bài 18(b): giới hạn số gia theo bước `ch`, kể cả `c = 0`. -/
theorem scaled_increment_limit {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    Tendsto (fun h : ℝ ↦ (f (x + c * h) - f x) / h) (𝓝[≠] (0 : ℝ))
      (𝓝 (c * deriv f x)) := by
  have hlim := difference_quotient_limit (affine_parameter_hasDerivAt hf c)
  simpa only [mul_zero, add_zero, sub_zero] using hlim

/-- Bài 14(c): giới hạn sai phân đối xứng theo bước `ch`, kể cả `c = 0`. -/
theorem symmetric_increment_limit {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    Tendsto (fun h : ℝ ↦ (f (x + c * h) - f (x - c * h)) / h)
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 * c * deriv f x)) := by
  have hp := affine_parameter_hasDerivAt hf c
  have hm := affine_parameter_hasDerivAt hf (-c)
  have h := hp.sub hm
  have hd : HasDerivAt (fun h : ℝ ↦ f (x + c * h) - f (x - c * h))
      (2 * c * deriv f x) 0 := by
    apply (h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ by
      have heq : x + (-c) * y = x - c * y := by ring
      simp only [Pi.sub_apply, heq])).congr_deriv
    ring
  have hlim := difference_quotient_limit hd
  simpa only [mul_zero, add_zero, sub_zero, sub_self] using hlim


theorem reciprocal_natural_tendsto_punctured_zero :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝[≠] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact one_div_ne_zero hn0

/-- Bài 18(a): giới hạn dãy số gia. -/
theorem natural_increment_limit {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (f (x + 1 / (n : ℝ)) - f x)) atTop
      (𝓝 (deriv f x)) := by
  have hinc := (calculus.Chapter04.Section01Derivatives.hasDerivAt_iff_increment_limit f x _).mp hf.hasDerivAt
  have hlim := hinc.comp reciprocal_natural_tendsto_punctured_zero
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change (f (x + 1 / (n : ℝ)) - f x) / (1 / (n : ℝ)) =
    (n : ℝ) * (f (x + 1 / (n : ℝ)) - f x)
  field_simp

/-- Bài 15: bình phương số gia của hàm Lipschitz có đạo hàm 0 tại điểm gốc. -/
theorem lipschitz_square_hasDerivAt_zero {f : ℝ → ℝ} {I : Set ℝ} {x : ℝ} {K : NNReal}
    (hI : IsOpen I) (hx : x ∈ I) (hf : LipschitzOnWith K f I) :
    HasDerivAt (fun y : ℝ ↦ (f y - f x) ^ 2) 0 x := by
  have hb : Tendsto (fun y : ℝ ↦ (K : ℝ) ^ 2 * |y - x|) (𝓝[≠] x) (𝓝 (0 : ℝ)) := by
    have habs : Tendsto (fun y : ℝ ↦ |y - x|) (𝓝[≠] x) (𝓝 (0 : ℝ)) := by
      have hsub : Tendsto (fun y : ℝ ↦ y - x) (𝓝[≠] x) (𝓝 (0 : ℝ)) := by
        simpa only [id_eq, sub_self] using
          ((tendsto_id.mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds :
            Tendsto (fun y : ℝ ↦ id y - x) (𝓝[≠] x) (𝓝 (x - x)))
      have ht := (continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt.tendsto.comp hsub
      simpa only [Function.comp_def, abs_zero] using ht
    simpa only [mul_zero] using (tendsto_const_nhds (x := (K : ℝ) ^ 2)).mul habs
  have hbound : ∀ᶠ y : ℝ in 𝓝[≠] x,
      |((f y - f x) ^ 2 - (f x - f x) ^ 2) / (y - x)| ≤ (K : ℝ) ^ 2 * |y - x| := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hI.mem_nhds hx)] with y hy hyI
    have hden : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hy)
    have hLip : |f y - f x| ≤ (K : ℝ) * |y - x| := by
      simpa only [Real.dist_eq] using hf.dist_le_mul y hyI x hx
    have hprod := mul_nonneg (sub_nonneg.mpr hLip)
      (add_nonneg (mul_nonneg K.coe_nonneg (abs_nonneg (y - x))) (abs_nonneg (f y - f x)))
    have hsq : |f y - f x| ^ 2 ≤ (K : ℝ) ^ 2 * |y - x| ^ 2 := by nlinarith
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), sub_zero, abs_div, abs_pow]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hnorm : Tendsto (fun y : ℝ ↦ |((f y - f x) ^ 2 - (f x - f x) ^ 2) / (y - x)|)
      (𝓝[≠] x) (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound hb
  have hlim : Tendsto (fun y : ℝ ↦ ((f y - f x) ^ 2 - (f x - f x) ^ 2) / (y - x))
      (𝓝[≠] x) (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs, sub_zero] using hnorm)
  apply hasDerivAt_iff_tendsto_slope.mpr
  rw [calculus.Chapter04.Section01Derivatives.slope_eq_difference_quotient]
  exact hlim

/-- Bài 16: giới hạn lũy thừa của các giá trị hàm tại `x + 1/n`. -/
theorem sampled_power_limit {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hx : 0 < f x) :
    Tendsto (fun n : ℕ ↦ (f (x + 1 / (n : ℝ)) / f x) ^ n) atTop
      (𝓝 (Real.exp (deriv f x / f x))) := by
  have hnormal : HasDerivAt (fun y : ℝ ↦ f y / f x) (deriv f x / f x) x :=
    hf.hasDerivAt.div_const (f x)
  have hratio0 : f x / f x ≠ 0 := by rw [div_self hx.ne']; norm_num
  have hlog := hnormal.log hratio0
  have hg : HasDerivAt (fun y : ℝ ↦ Real.log (f y / f x)) (deriv f x / f x) x := by
    apply hlog.congr_deriv
    rw [div_self hx.ne', div_one]
  have hinc := natural_increment_limit hg.differentiableAt
  have hloglim : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log (f (x + 1 / (n : ℝ)) / f x)) atTop
      (𝓝 (deriv f x / f x)) := by
    simpa only [div_self hx.ne', Real.log_one, sub_zero, hg.deriv] using hinc
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hloglim
  have hsample : Tendsto (fun n : ℕ ↦ f (x + 1 / (n : ℝ)) / f x) atTop (𝓝 (1 : ℝ)) := by
    have hp : Tendsto (fun n : ℕ ↦ x + 1 / (n : ℝ)) atTop (𝓝 x) := by
      simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Function.comp_apply, div_self hx.ne'] using (hf.continuousAt.tendsto.comp hp).div_const (f x)
  apply hexp.congr'
  filter_upwards [hsample.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  change Real.exp ((n : ℝ) * Real.log (f (x + 1 / (n : ℝ)) / f x)) =
    (f (x + 1 / (n : ℝ)) / f x) ^ n
  rw [Real.exp_nat_mul, Real.exp_log (show 0 < f (x + 1 / (n : ℝ)) / f x from hn)]

end calculus.Chapter04.Section01LimitExercises
