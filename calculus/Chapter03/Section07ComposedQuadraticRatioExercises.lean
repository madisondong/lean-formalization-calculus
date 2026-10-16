import calculus.Chapter03.Section07CosineRatioExercises
import calculus.Chapter03.Section07LogarithmicRatioExercises
import calculus.Chapter03.Section07Fundamental
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
§3.7 — Bài tập 3.7.11(i,j)

Nguồn: dòng 3691–3692.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07ComposedQuadraticRatioExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises calculus.Chapter03.Section07
open calculus.Chapter03.Section07Examples calculus.Chapter03.Section07Fundamental
open calculus.Chapter03.Section07CosineRatioExercises
open calculus.Chapter03.Section07LogarithmicRatioExercises


def fifthRootLogarithmDomain : Set ℝ :=
  {x | 1 - 15 * x * Real.sin (2 * x) ∈ nthRootDomain 5 ∧
    0 < Real.cos (4 * x) ∧ Real.log (Real.cos (4 * x)) ≠ 0}


def exponentialArctangentRootDomain : Set ℝ :=
  {x | 0 ≤ 1 - 4 * x * Real.arctan x ∧ x ^ 2 ≠ 0}


theorem normalized_composition_increment {ψ u : ℝ → ℝ} {d A : ℝ} (n : ℕ)
    (hψ : HasDerivAt ψ d 0) (hψ0 : ψ 0 = 0)
    (hu : Tendsto u (domainApproachFilter univ (.point 0)) (𝓝 0))
    (hn : Tendsto (fun x ↦ u x / x ^ n)
      (domainApproachFilter univ (.point 0)) (𝓝 A)) (hA : A ≠ 0) :
    Tendsto (fun x ↦ ψ (u x) / x ^ n)
      (domainApproachFilter univ (.point 0)) (𝓝 (d * A)) := by
  have hune : ∀ᶠ x in domainApproachFilter univ (.point 0), u x ≠ 0 :=
    (hn.eventually_ne hA).mono fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  have hup : Tendsto u (domainApproachFilter univ (.point 0))
      (domainApproachFilter univ (.point 0)) := by
    change Tendsto u (domainApproachFilter univ (.point 0)) (𝓝[univ \ {0}] 0)
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hu, ?_⟩
    filter_upwards [hune] with x hx
    exact ⟨mem_univ _, by simpa using hx⟩
  have hs : Tendsto (fun x ↦ ψ (u x) / u x)
      (domainApproachFilter univ (.point 0)) (𝓝 d) := by
    simpa only [Function.comp_def, hψ0, sub_zero] using!
      (derivative_quotient_zero hψ).comp hup
  apply (show Tendsto (fun x ↦ (ψ (u x) / u x) * (u x / x ^ n))
      (domainApproachFilter univ (.point 0)) (𝓝 (d * A)) from by
        simpa only [Pi.mul_apply] using! hs.mul hn).congr'
  filter_upwards [hune] with x hx
  exact div_mul_div_cancel₀ hx


theorem scaled_sine_normalized_at_zero (c : ℝ) :
    Tendsto (fun x : ℝ ↦ Real.sin (c * x) / x)
      (domainApproachFilter univ (.point 0)) (𝓝 c) := by
  have hd : HasDerivAt (fun x : ℝ ↦ Real.sin (c * x)) c 0 := by
    simpa only [id_eq, mul_zero, Real.cos_zero, one_mul, mul_one] using!
      ((hasDerivAt_id (0 : ℝ)).const_mul c).sin
  simpa only [mul_zero, Real.sin_zero, sub_zero] using! derivative_quotient_zero hd


theorem normalized_log_cosine_at_zero {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun x : ℝ ↦ Real.log (Real.cos (c * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-(c ^ 2 / 2))) := by
  have hcos : Tendsto (fun x : ℝ ↦ Real.cos (c * x))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ Real.cos (c * x)) 0 := by fun_prop
    simpa only [mul_zero, Real.cos_zero] using! hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ Real.cos (c * x) - 1)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using! hcos.sub_const 1
  have hn : Tendsto (fun x : ℝ ↦ (Real.cos (c * x) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-(c ^ 2 / 2))) := by
    have ht := (normalized_scaled_cosine c).neg
    apply ht.congr
    intro x
    ring
  have hA : -(c ^ 2 / 2) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hc) (by norm_num))
  apply (normalized_log_of_quadratic hu hn hA).congr
  intro x
  rw [show 1 + (Real.cos (c * x) - 1) = Real.cos (c * x) by ring]

/-- Bài tập 3.7.11(i): giới hạn bằng −3/4. -/
theorem fifth_root_logarithm_ratio_at_zero :
    DomainLimit fifthRootLogarithmDomain
      (fun x ↦ (1 - realNthRoot 5 (1 - 15 * x * Real.sin (2 * x))) /
        Real.log (Real.cos (4 * x))) 0 (-3 / 4) := by
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hsin : Tendsto (fun x : ℝ ↦ Real.sin (2 * x))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ Real.sin (2 * x)) 0 := by fun_prop
    simpa only [mul_zero, Real.sin_zero] using! hc.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ -15 * x * Real.sin (2 * x))
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using! (hi.const_mul (-15)).mul hsin
  have hun : Tendsto (fun x : ℝ ↦ (-15 * x * Real.sin (2 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-30 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ -15 * (Real.sin (2 * x) / x))
        (domainApproachFilter univ (.point 0)) (𝓝 (-30 : ℝ)) := by
      simpa only [show (-15 : ℝ) * 2 = -30 by norm_num] using!
        (scaled_sine_normalized_at_zero 2).const_mul (-15)
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have harg : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 0 := by
    simpa only [id_eq] using! (hasDerivAt_id (0 : ℝ)).const_add 1
  have hout : HasDerivAt (realNthRoot 5) (1 / 5) (1 + (0 : ℝ)) := by
    simpa only [add_zero, Nat.cast_ofNat, one_div] using
      realNthRoot_hasDerivAt_one (by norm_num : (1 : ℕ) ≤ 5)
  have hψ : HasDerivAt (fun t : ℝ ↦ realNthRoot 5 (1 + t) - 1) (1 / 5) 0 := by
    simpa only [Function.comp_def, mul_one] using! (hout.comp 0 harg).sub_const 1
  have hroot : Tendsto (fun x : ℝ ↦ (realNthRoot 5 (1 - 15 * x * Real.sin (2 * x)) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-6 : ℝ)) := by
    simpa only [neg_mul, ← sub_eq_add_neg, show (1 / 5 : ℝ) * (-30) = -6 by norm_num] using!
      normalized_composition_increment 2 hψ
        (by simp only [add_zero, realNthRoot_one, sub_self]) hu hun (by norm_num : (-30 : ℝ) ≠ 0)
  have hf : Tendsto (fun x : ℝ ↦ (1 - realNthRoot 5 (1 - 15 * x * Real.sin (2 * x))) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (6 : ℝ)) := by
    have ht := hroot.neg
    simp only [neg_neg] at ht
    apply ht.congr
    intro x
    ring
  have hg : Tendsto (fun x : ℝ ↦ Real.log (Real.cos (4 * x)) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-8 : ℝ)) := by
    convert! normalized_log_cosine_at_zero (by norm_num : (4 : ℝ) ≠ 0) using 1; norm_num
  have hcos : Tendsto (fun x : ℝ ↦ Real.cos (4 * x))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ Real.cos (4 * x)) 0 := by fun_prop
    simpa only [mul_zero, Real.cos_zero] using! hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlogne : ∀ᶠ x in domainApproachFilter univ (.point 0), Real.log (Real.cos (4 * x)) ≠ 0 :=
    (hg.eventually_ne (by norm_num : (-8 : ℝ) ≠ 0)).mono fun _ hx ↦ (div_ne_zero_iff.mp hx).1
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ fifthRootLogarithmDomain := by
    filter_upwards [hcos.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)), hlogne] with x hp hn
    exact ⟨Or.inl ⟨2, by norm_num⟩, hp, hn⟩
  apply domainLimit_of_eventually_domain hD
  apply (show Tendsto (fun x : ℝ ↦ ((1 - realNthRoot 5 (1 - 15 * x * Real.sin (2 * x))) / x ^ 2) /
      (Real.log (Real.cos (4 * x)) / x ^ 2)) (domainApproachFilter univ (.point 0)) (𝓝 (-3 / 4 : ℝ)) from by
        simpa only [Pi.div_apply, show (6 : ℝ) / (-8) = -3 / 4 by norm_num] using!
          hf.div hg (by norm_num : (-8 : ℝ) ≠ 0)).congr'
  filter_upwards [punctured_zero_eventually_ne] with x hx
  exact div_div_div_cancel_right₀ (pow_ne_zero 2 hx) _ _

/-- Bài tập 3.7.11(j): giới hạn bằng 3. -/
theorem exponential_arctangent_root_ratio_at_zero :
    DomainLimit exponentialArctangentRootDomain
      (fun x ↦ (Real.exp (x ^ 2) - Real.sqrt (1 - 4 * x * Real.arctan x)) / x ^ 2) 0 3 := by
  have hi : Tendsto (fun x : ℝ ↦ x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, id_eq] using!
      (continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using! hi.pow 2
  have hun : Tendsto (fun x : ℝ ↦ x ^ 2 / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    exact (div_self (pow_ne_zero 2 hx)).symm
  have hψ : HasDerivAt (fun t : ℝ ↦ Real.exp t - 1) 1 0 := by
    simpa only [Real.exp_zero] using! (Real.hasDerivAt_exp 0).sub_const 1
  have hexp : Tendsto (fun x : ℝ ↦ (Real.exp (x ^ 2) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [mul_one] using! normalized_composition_increment 2 hψ
      (by simp only [Real.exp_zero, sub_self]) hu hun one_ne_zero
  have hatan : Tendsto Real.arctan (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [domainApproachFilter, Real.arctan_zero] using!
      (Real.continuous_arctan.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun x : ℝ ↦ -4 * x * Real.arctan x)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using! (hi.const_mul (-4)).mul hatan
  have hvn : Tendsto (fun x : ℝ ↦ (-4 * x * Real.arctan x) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-4 : ℝ)) := by
    have hd : HasDerivAt Real.arctan 1 0 := by
      simpa using Real.hasDerivAt_arctan (0 : ℝ)
    have hatn : Tendsto (fun x : ℝ ↦ Real.arctan x / x)
        (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
      simpa only [Real.arctan_zero, sub_zero] using! derivative_quotient_zero hd
    have ht : Tendsto (fun x : ℝ ↦ -4 * (Real.arctan x / x))
        (domainApproachFilter univ (.point 0)) (𝓝 (-4 : ℝ)) := by
      simpa only [mul_one] using! hatn.const_mul (-4)
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
  have harg : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 0 := by
    simpa only [id_eq] using! (hasDerivAt_id (0 : ℝ)).const_add 1
  have hsqrt : HasDerivAt (fun t : ℝ ↦ Real.sqrt (1 + t) - 1) (1 / 2) 0 := by
    simpa only [add_zero, Real.sqrt_one, mul_one] using!
      (harg.sqrt (by norm_num : (1 : ℝ) + 0 ≠ 0)).sub_const 1
  have hroot : Tendsto (fun x : ℝ ↦ (Real.sqrt (1 - 4 * x * Real.arctan x) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-2 : ℝ)) := by
    simpa only [neg_mul, ← sub_eq_add_neg, show (1 / 2 : ℝ) * (-4) = -2 by norm_num] using!
      normalized_composition_increment 2 hsqrt
        (by simp only [add_zero, Real.sqrt_one, sub_self]) hv hvn (by norm_num : (-4 : ℝ) ≠ 0)
  have hD : ∀ᶠ x in domainApproachFilter univ (.point 0), x ∈ exponentialArctangentRootDomain := by
    have hb : Tendsto (fun x : ℝ ↦ 1 - 4 * x * Real.arctan x)
        (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
      simpa only [neg_mul, ← sub_eq_add_neg, add_zero] using! hv.const_add 1
    filter_upwards [hb.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)), punctured_zero_eventually_ne] with x hp hx
    exact ⟨hp.le, pow_ne_zero 2 hx⟩
  apply domainLimit_of_eventually_domain hD
  apply (show Tendsto (fun x : ℝ ↦ (Real.exp (x ^ 2) - 1) / x ^ 2 -
      (Real.sqrt (1 - 4 * x * Real.arctan x) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (3 : ℝ)) from by
        simpa only [Pi.sub_apply, show (1 : ℝ) - (-2) = 3 by norm_num] using! hexp.sub hroot).congr
  intro x
  ring

end calculus.Chapter03.Section07ComposedQuadraticRatioExercises
