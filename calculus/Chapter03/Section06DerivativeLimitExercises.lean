import calculus.Chapter03.Section06Limits
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# §3.6 — bốn giới hạn bậc nhất

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3157, dòng 3168–3169, dòng 3173.
-/

set_option autoImplicit false
noncomputable section

namespace calculus.Chapter03.Section06DerivativeLimitExercises

open Set Filter
open scoped Topology
open calculus.Chapter03.Section02
open calculus.Chapter03.Section06Limits


theorem inverse_trig_quotient_domain_accumulation :
    AccumulationPointOf (Icc (-1 : ℝ) 1 \ {(0 : ℝ)}) 0 := by
  intro δ hδ
  have hm : 0 < min δ (1 : ℝ) := lt_min hδ zero_lt_one
  have hx : 0 < min δ (1 : ℝ) / 2 := by linarith
  refine ⟨min δ (1 : ℝ) / 2, ?_, ne_of_gt hx, ?_, ?_⟩
  · refine ⟨⟨by linarith, by linarith [min_le_right δ (1 : ℝ)]⟩, ?_⟩
    simpa only [mem_singleton_iff] using (ne_of_gt hx)
  · linarith
  · linarith [min_le_left δ (1 : ℝ)]

/-- Bài tập 3.6.7(a): giới hạn hai phía tại 0 trên miền arcsin xác định. -/
theorem exercise07_arcsine_quotient :
    DomainLimit (Icc (-1 : ℝ) 1 \ {(0 : ℝ)})
      (fun x : ℝ ↦ Real.arcsin x / x) 0 1 := by
  apply (domainLimit_iff_tendsto inverse_trig_quotient_domain_accumulation).mpr
  have hd : HasDerivAt Real.arcsin 1 (0 : ℝ) := by
    simpa using (Real.hasDerivAt_arcsin (x := (0 : ℝ)) (by norm_num) (by norm_num))
  have ht : Tendsto (fun x : ℝ ↦ Real.arcsin x / x)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [slope_fun_def_field, Real.arcsin_zero, sub_zero] using
      hd.tendsto_slope
  exact ht.mono_left (nhdsWithin_mono (0 : ℝ)
    (show (Icc (-1 : ℝ) 1 \ {(0 : ℝ)}) \ {(0 : ℝ)} ⊆ {(0 : ℝ)}ᶜ from
      fun _ hx ↦ hx.2))

/-- Bài tập 3.6.7(b): giới hạn thương sai phân của arccos tại 0. -/
theorem exercise07_arccosine_quotient :
    DomainLimit (Icc (-1 : ℝ) 1 \ {(0 : ℝ)})
      (fun x : ℝ ↦ (Real.arccos x - Real.pi / 2) / x) 0 (-1) := by
  apply (domainLimit_iff_tendsto inverse_trig_quotient_domain_accumulation).mpr
  have hd : HasDerivAt Real.arccos (-1) (0 : ℝ) := by
    simpa using (Real.hasDerivAt_arccos (x := (0 : ℝ)) (by norm_num) (by norm_num))
  have ht : Tendsto (fun x : ℝ ↦ (Real.arccos x - Real.pi / 2) / x)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 : ℝ)) := by
    simpa only [slope_fun_def_field, Real.arccos_zero, sub_zero] using
      hd.tendsto_slope
  exact ht.mono_left (nhdsWithin_mono (0 : ℝ)
    (show (Icc (-1 : ℝ) 1 \ {(0 : ℝ)}) \ {(0 : ℝ)} ⊆ {(0 : ℝ)}ᶜ from
      fun _ hx ↦ hx.2))

/-- Bài tập 3.6.7(f): giới hạn thương logarit. -/
theorem exercise07_logarithm_quotient_at_euler :
    DomainLimit (Ioi (0 : ℝ) \ {Real.exp 1})
      (fun x : ℝ ↦ (Real.log x - 1) / (x - Real.exp 1))
      (Real.exp 1) ((Real.exp 1)⁻¹) := by
  apply (domainLimit_iff_tendsto
    (positive_halfline_punctured_accumulation (Real.exp_pos 1))).mpr
  have hd : HasDerivAt Real.log ((Real.exp 1)⁻¹) (Real.exp 1) :=
    Real.hasDerivAt_log (Real.exp_pos 1).ne'
  have ht : Tendsto (fun x : ℝ ↦ (Real.log x - 1) / (x - Real.exp 1))
      (𝓝[≠] (Real.exp 1)) (𝓝 ((Real.exp 1)⁻¹)) := by
    simpa only [slope_fun_def_field, Real.log_exp] using hd.tendsto_slope
  exact ht.mono_left (nhdsWithin_mono (Real.exp 1)
    (show (Ioi (0 : ℝ) \ {Real.exp 1}) \ {Real.exp 1} ⊆ {Real.exp 1}ᶜ from
      fun _ hx ↦ hx.2))

/-- Bài tập 3.6.6(a): giới hạn lũy thừa, với α thực tùy ý. -/
theorem exercise06_shifted_real_power_quotient (α : ℝ) :
    DomainLimit (Ioi (-1 : ℝ) \ {(0 : ℝ)})
      (fun x : ℝ ↦ ((1 + x) ^ α - 1) / x) 0 α := by
  apply (domainLimit_iff_tendsto
    (positive_halfline_punctured_accumulation (by norm_num : (-1 : ℝ) < 0))).mpr
  have hd : HasDerivAt (fun y : ℝ ↦ y ^ α) α (1 : ℝ) := by
    simpa only [Real.one_rpow, mul_one] using
      (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := α)
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0)))
  have ht : Tendsto (fun x : ℝ ↦ ((1 + x) ^ α - 1) / x)
      (𝓝[≠] (0 : ℝ)) (𝓝 α) := by
    simpa only [Real.one_rpow, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hd.tendsto_slope_zero
  exact ht.mono_left (nhdsWithin_mono (0 : ℝ)
    (show (Ioi (-1 : ℝ) \ {(0 : ℝ)}) \ {(0 : ℝ)} ⊆ {(0 : ℝ)}ᶜ from
      fun _ hx ↦ hx.2))

end calculus.Chapter03.Section06DerivativeLimitExercises
