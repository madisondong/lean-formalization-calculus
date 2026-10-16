import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# §3.6 — Bài tập 7(c,e): giới hạn tại biên và lũy thừa hyperbol

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3170 và dòng 3172.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter03.Section06EndpointHyperbolicExercises
open Set Filter Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises


theorem arccosine_one_sub_half_angle {x : ℝ} (hx : x ∈ Icc 0 2) :
    Real.arccos (1 - x) = 2 * Real.arcsin (Real.sqrt (x / 2)) := by
  have hv0 : 0 ≤ Real.sqrt (x / 2) := Real.sqrt_nonneg _
  have hv1 : Real.sqrt (x / 2) ≤ 1 := by
    have hq : x / 2 ≤ 1 := by linarith [hx.2]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  have hsin := Real.sin_arcsin (by linarith : -(1 : ℝ) ≤ Real.sqrt (x / 2)) hv1
  have hsq := Real.sq_sqrt (show 0 ≤ x / 2 by linarith [hx.1])
  have hc : Real.cos (2 * Real.arcsin (Real.sqrt (x / 2))) = 1 - x := by
    rw [Real.cos_two_mul_eq_one_sub, hsin, hsq]
    ring
  have hangle0 : 0 ≤ 2 * Real.arcsin (Real.sqrt (x / 2)) :=
    mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr hv0)
  have hangleπ : 2 * Real.arcsin (Real.sqrt (x / 2)) ≤ Real.pi := by
    linarith [Real.arcsin_le_pi_div_two (Real.sqrt (x / 2))]
  rw [← hc, Real.arccos_cos hangle0 hangleπ]

/-- Bài tập 7(c): giới hạn phải tại 0 trên miền 0<x≤2. -/
theorem exercise07_arccosine_endpoint_ratio :
    calculus.Chapter03.Section02OneSided.DomainRightLimit (Ioc (0 : ℝ) 2)
      (fun x : ℝ ↦ Real.arccos (1 - x) / Real.sqrt x) 0 (Real.sqrt 2) := by
  have ha : calculus.Chapter03.Section02.RightAccumulationPointOf (Ioc (0 : ℝ) 2) 0 := by
    intro δ hδ
    have hη : 0 < min δ 1 := lt_min hδ zero_lt_one
    have hm := min_le_right δ (1 : ℝ)
    have hδm := min_le_left δ (1 : ℝ)
    exact ⟨min δ 1 / 2, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  apply (calculus.Chapter03.Section02OneSided.domainRightLimit_iff_tendsto ha).mpr
  let l : Filter ℝ := 𝓝[Ioc (0 : ℝ) 2 ∩ Ioi 0] 0
  have hv : Tendsto (fun x : ℝ ↦ Real.sqrt (x / 2)) l (𝓝 0) := by
    have hc : Continuous (fun x : ℝ ↦ Real.sqrt (x / 2)) :=
      Real.continuous_sqrt.comp (continuous_id.div_const 2)
    simpa only [zero_div, Real.sqrt_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioc (0 : ℝ) 2 ∩ Ioi 0))
  have hvNE : Tendsto (fun x : ℝ ↦ Real.sqrt (x / 2)) l (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hv, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Real.sqrt_pos.mpr (div_pos hx.2 (by norm_num : (0 : ℝ) < 2))).ne'
  have hd : HasDerivAt Real.arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1)
  have hs : Tendsto (fun u : ℝ ↦ Real.arcsin u / u) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [slope_fun_def_field, Real.arcsin_zero, sub_zero] using hd.tendsto_slope
  have ht := (hs.comp hvNE).const_mul (Real.sqrt 2)
  have ht' : Tendsto (fun x : ℝ ↦ Real.sqrt 2 *
      (Real.arcsin (Real.sqrt (x / 2)) / Real.sqrt (x / 2))) l (𝓝 (Real.sqrt 2)) := by
    simpa only [mul_one, Function.comp_def] using ht
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hvp : 0 < Real.sqrt (x / 2) := Real.sqrt_pos.mpr (div_pos hx.2 (by norm_num))
  have htwo : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hmul : Real.sqrt x = Real.sqrt 2 * Real.sqrt (x / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [arccosine_one_sub_half_angle ⟨hx.1.1.le, hx.1.2⟩, hmul]
  field_simp [hvp.ne', htwo.ne']
  nlinarith [congrArg (fun z : ℝ ↦ z * Real.arcsin (Real.sqrt (x / 2)))
    (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))]


theorem cosh_sub_one_half_sinh_square (x : ℝ) :
    Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
  have hc := Real.cosh_two_mul (x / 2)
  have hs := Real.cosh_sq_sub_sinh_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc
  linarith


theorem cosh_ne_one_of_ne_zero {x : ℝ} (hx : x ≠ 0) : Real.cosh x ≠ 1 := by
  have hs : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero hx (by norm_num))
  have hp : 0 < Real.sinh (x / 2) ^ 2 := sq_pos_of_ne_zero hs
  have he := cosh_sub_one_half_sinh_square x
  linarith

/-- Bài tập 7(e): giới hạn với số mũ α thực tùy ý. -/
theorem exercise07_hyperbolic_power_increment (α : ℝ) :
    DomainLimit (univ \ {(0 : ℝ)})
      (fun x : ℝ ↦ ((Real.cosh x) ^ α - 1) / x ^ 2) 0 (α / 2) := by
  apply (domainLimit_iff_tendsto (univ_diff_accumulation 0)).mpr
  have hsd : HasDerivAt (fun x : ℝ ↦ Real.sinh (x / 2)) (1 / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).sinh
  have hs : Tendsto (fun x : ℝ ↦ Real.sinh (x / 2) / x) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    simpa only [slope_fun_def_field, zero_div, Real.sinh_zero, sub_zero] using hsd.tendsto_slope
  have hb : Tendsto (fun x : ℝ ↦ (Real.cosh x - 1) / x ^ 2)
      (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have ht := (hs.pow 2).const_mul (2 : ℝ)
    have ht' : Tendsto (fun x : ℝ ↦ 2 * (Real.sinh (x / 2) / x) ^ 2)
        (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
      convert ht using 1
      norm_num
    apply ht'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [cosh_sub_one_half_sinh_square]
    field_simp [show x ≠ 0 from hx]
  have hc : Tendsto Real.cosh (𝓝[≠] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [Real.cosh_zero] using (Real.continuous_cosh.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact cosh_ne_one_of_ne_zero (show x ≠ 0 from hx)
  have hpd : HasDerivAt (fun u : ℝ ↦ u ^ α) α 1 := by
    simpa only [Real.one_rpow, mul_one] using Real.hasDerivAt_rpow_const
      (p := α) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hp : Tendsto (fun x : ℝ ↦ ((Real.cosh x) ^ α - 1) / (Real.cosh x - 1))
      (𝓝[≠] 0) (𝓝 α) := by
    simpa only [slope_fun_def_field, Function.comp_def, Real.one_rpow] using hpd.tendsto_slope.comp hc
  have ht := hp.mul hb
  have hquot : Tendsto (fun x : ℝ ↦ ((Real.cosh x) ^ α - 1) / x ^ 2)
      (𝓝[≠] 0) (𝓝 (α / 2)) := by
    have ht' : Tendsto (fun x : ℝ ↦
        (((Real.cosh x) ^ α - 1) / (Real.cosh x - 1)) * ((Real.cosh x - 1) / x ^ 2))
        (𝓝[≠] 0) (𝓝 (α / 2)) := by
      simpa only [mul_one_div] using ht
    apply ht'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    field_simp [sub_ne_zero.mpr (cosh_ne_one_of_ne_zero (show x ≠ 0 from hx)),
      show x ≠ 0 from hx]
  exact hquot.mono_left (nhdsWithin_mono 0 (fun _ hx ↦ hx.2))

end calculus.Chapter03.Section06EndpointHyperbolicExercises
