import calculus.Chapter03.Section07AlgebraSupplement
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# §3.7 — ba giới hạn từ phần chính tuyến tính

Nguồn: `Ch3_gioihanhamso.tex`, Bài tập 3.7.11(b), dòng 3684; Bài tập 3.7.14(c,f), dòng 3751 và dòng 3754.
-/

set_option autoImplicit false

open Set Filter Topology

namespace calculus.Chapter03.Section07ExercisesDerivativeRatios

open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section07AlgebraSupplement


def polynomialRatioDomain : Set ℝ := {x | x ^ 2 - x - 2 ≠ 0}


def powerLogRatioDomain : Set ℝ := {x | 0 < x ∧ Real.log x ≠ 0}


def sineLogRatioDomain : Set ℝ := {x | 0 < 1 + 4 * x ∧ Real.log (1 + 4 * x) ≠ 0}


theorem nonvanishingAsymptoticEquivalenceAlong_linear_of_hasDerivAt {D : Set ℝ} {f : ℝ → ℝ} {a f' : ℝ}
    (ha : AccumulationPointOf D a) (hf : HasDerivAt f f' a)
    (hf0 : f a = 0) (hf' : f' ≠ 0) :
    NonvanishingAsymptoticEquivalenceAlong D (.point a) f (fun x ↦ f' * (x - a)) := by
  have hs := domainLimit_restrict (hasDerivAt_domainLimit_slope hf) ha
    (fun _ _ ↦ mem_univ _)
  have ht : Tendsto (fun x ↦ slope f a x / f') (𝓝[D \ {a}] a) (𝓝 1) := by
    simpa only [div_self hf'] using ((domainLimit_iff_tendsto ha).mp hs).div_const f'
  refine ⟨(properLimitApproach_point_iff D a).mpr ha, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero hf' (sub_ne_zero.mpr (by simpa using hx.2))
  · apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x _hx
    rw [slope_def_field, hf0, sub_zero, div_div]
    rw [mul_comm (x - a) f']


theorem domainLimit_ratio_of_equivalent_linear_parts
    {D : Set ℝ} {f g : ℝ → ℝ} {a f' g' : ℝ}
    (ha : AccumulationPointOf D a) (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a)
    (hf0 : f a = 0) (hg0 : g a = 0) (hf' : f' ≠ 0) (hg' : g' ≠ 0) :
    DomainLimit D (fun x ↦ f x / g x) a (f' / g') := by
  have hp := (properLimitApproach_point_iff D a).mpr ha
  have hfe := nonvanishingAsymptoticEquivalenceAlong_linear_of_hasDerivAt ha hf hf0 hf'
  have hge := nonvanishingAsymptoticEquivalenceAlong_linear_of_hasDerivAt ha hg hg0 hg'
  have hfs : InfinitesimalAlong D (.point a) f := by
    refine ⟨hp, ?_⟩
    simpa only [domainApproachFilter, hf0] using hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgs : InfinitesimalAlong D (.point a) g := by
    refine ⟨hp, ?_⟩
    simpa only [domainApproachFilter, hg0] using hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hi : Tendsto (fun x : ℝ ↦ x - a) (domainApproachFilter D (.point a)) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x - a) a :=
      continuous_id.continuousAt.sub continuous_const.continuousAt
    simpa only [domainApproachFilter, sub_self] using
      hc.tendsto.mono_left (nhdsWithin_le_nhds (s := D \ {a}))
  have hlsf : InfinitesimalAlong D (.point a) (fun x ↦ f' * (x - a)) :=
    ⟨hp, by simpa only [mul_zero] using hi.const_mul f'⟩
  have hlsg : InfinitesimalAlong D (.point a) (fun x ↦ g' * (x - a)) :=
    ⟨hp, by simpa only [mul_zero] using hi.const_mul g'⟩
  apply (domainLimit_iff_tendsto ha).mpr
  apply ((equivalent_quotients_limit_iff hfs hgs hlsf hlsg hfe hge).1 (f' / g')).mpr
  apply (tendsto_const_nhds (x := f' / g')).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (mul_div_mul_right f' g' (sub_ne_zero.mpr (by simpa using hx.2))).symm

/-- Bài tập 3.7.14(c): (x²−4)/(x²−x−2) → 4/3 khi x → 2 trên miền tự nhiên. -/
theorem polynomial_ratio_at_two :
    DomainLimit polynomialRatioDomain (fun x ↦ (x ^ 2 - 4) / (x ^ 2 - x - 2)) 2 (4 / 3) := by
  have hf : HasDerivAt (fun x : ℝ ↦ x ^ 2 - 4) 4 2 := by
    convert! ((hasDerivAt_id (2 : ℝ)).pow 2).sub_const 4 using 1
    norm_num [id_eq, Pi.pow_apply]
  have hg : HasDerivAt (fun x : ℝ ↦ x ^ 2 - x - 2) 3 2 := by
    convert! (((hasDerivAt_id (2 : ℝ)).pow 2).sub (hasDerivAt_id (2 : ℝ))).sub_const 2 using 1
    norm_num [id_eq, Pi.pow_apply, Pi.sub_apply]
  have ha : AccumulationPointOf polynomialRatioDomain 2 :=
    derivative_quotient_domain_accumulation hg (by norm_num) (by norm_num)
  exact domainLimit_ratio_of_equivalent_linear_parts ha hf hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Bài tập 3.7.14(f): (x²⁰²⁵−1)/ln x → 2025 khi x → 1, x>0 và ln x≠0. -/
theorem power_log_ratio_at_one :
    DomainLimit powerLogRatioDomain (fun x ↦ (x ^ 2025 - 1) / Real.log x) 1 2025 := by
  have hf : HasDerivAt (fun x : ℝ ↦ x ^ 2025 - 1) 2025 1 := by
    simpa only [id_eq, Pi.pow_apply, one_pow, mul_one, Nat.cast_ofNat] using
      ((hasDerivAt_id (1 : ℝ)).pow 2025).sub_const 1
  have hg : HasDerivAt Real.log 1 1 := by
    simpa only [inv_one] using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have ha0 := derivative_quotient_domain_accumulation hg (by simp) (by norm_num)
  have ha : AccumulationPointOf powerLogRatioDomain 1 :=
    accumulationPointOf_mono (accumulationPointOf_inter_Ioi ha0 (by norm_num : (0 : ℝ) < 1))
      (fun _ hx ↦ ⟨hx.2, hx.1⟩)
  simpa only [div_one] using domainLimit_ratio_of_equivalent_linear_parts ha hf hg
    (by simp) (by simp) (by norm_num) (by norm_num)

/-- Bài tập 3.7.11(b): sin(5x)/ln(1+4x)→5/4 khi x→0 trên miền xác định của thương. -/
theorem sine_log_ratio_at_zero :
    DomainLimit sineLogRatioDomain (fun x ↦ Real.sin (5 * x) / Real.log (1 + 4 * x))
      0 (5 / 4) := by
  have hf : HasDerivAt (fun x : ℝ ↦ Real.sin (5 * x)) 5 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul 5).sin using 1
    norm_num [id_eq]
  have harg : HasDerivAt (fun x : ℝ ↦ 1 + 4 * x) 4 0 := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_mul 4).const_add 1
  have hg : HasDerivAt (fun x : ℝ ↦ Real.log (1 + 4 * x)) 4 0 := by
    convert! harg.log (by norm_num : (1 : ℝ) + 4 * 0 ≠ 0) using 1
    norm_num
  have ha0 := derivative_quotient_domain_accumulation hg (by norm_num) (by norm_num)
  have ha : AccumulationPointOf sineLogRatioDomain 0 :=
    accumulationPointOf_mono
      (accumulationPointOf_inter_Ioi ha0 (by norm_num : (-1 / 4 : ℝ) < 0)) (by
        intro x hx
        refine ⟨?_, hx.1⟩
        have hxl : (-1 / 4 : ℝ) < x := hx.2
        linarith)
  exact domainLimit_ratio_of_equivalent_linear_parts ha hf hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end calculus.Chapter03.Section07ExercisesDerivativeRatios
