import calculus.Chapter04.Section04TaylorLimitCoefficients
import calculus.Chapter04.Section04ElementaryLimitExamples
import calculus.Chapter04.Section04InfiniteExtensions
import calculus.Chapter03.Section02OneSided
import calculus.Chapter03.Section01Powers
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# §4.4 Bài 1: tính giới hạn bằng L'Hospital

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1662–1676.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04LHospitalLimitCalculations
open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section02OneSided calculus.Chapter03.Section01Powers
open calculus.Chapter04.Section04TaylorLimitCoefficients
open calculus.Chapter04.Section04ElementaryLimitExamples

theorem source_right_limit_of_eventual_natural_domain {D : Set ℝ} {f : ℝ → ℝ}
    {a L : ℝ} (hD : ∀ᶠ x in 𝓝[>] a, x ∈ D)
    (hf : Tendsto f (𝓝[>] a) (𝓝 L)) : DomainRightLimit D f a L := by
  have hfilter : 𝓝[D ∩ Ioi a] a = 𝓝[>] a := nhdsWithin_inter_of_mem hD
  have hacc : RightAccumulationPointOf D a := by
    apply rightAccumulation_iff_restricted.mpr
    apply accumulationPointOf_iff_neBot.mpr
    have hset : (D ∩ Ioi a) \ {a} = D ∩ Ioi a := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff, mem_singleton_iff, mem_Ioi]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, ne_of_gt h.2⟩⟩
    rw [hset, hfilter]
    infer_instance
  apply (domainRightLimit_iff_tendsto hacc).mpr
  rw [hfilter]
  exact hf

theorem exp_difference_div_sine_cosine_lhospital :
    Tendsto (fun x : ℝ ↦ (Real.exp x - Real.exp (-x)) / (Real.sin x * Real.cos x))
      (𝓝[≠] (0 : ℝ)) (𝓝 2) := by
  have hf (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.exp y - Real.exp (-y))
      (Real.exp x + Real.exp (-x)) x := by
    simpa only [sub_neg_eq_add] using!
      (Real.hasDerivAt_exp x).fun_sub (exp_neg_hasDerivAt x)
  have hg (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.sin y * Real.cos y)
      (Real.cos x ^ 2 - Real.sin x ^ 2) x := by
    convert! (Real.hasDerivAt_sin x).fun_mul (Real.hasDerivAt_cos x) using 1; ring
  have hq : Tendsto (fun x : ℝ ↦ (Real.exp x + Real.exp (-x)) /
      (Real.cos x ^ 2 - Real.sin x ^ 2)) (𝓝[≠] (0 : ℝ)) (𝓝 2) := by
    have hc : ContinuousAt (fun x : ℝ ↦ (Real.exp x + Real.exp (-x)) /
        (Real.cos x ^ 2 - Real.sin x ^ 2)) 0 := by
      fun_prop (disch := norm_num)
    have ht := hc.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    norm_num at ht
    exact ht
  apply calculus.Chapter04.Section04.lhopital_zero_punctured
    (Eventually.of_forall hf) (Eventually.of_forall hg)
  · have hc : ContinuousAt (fun x : ℝ ↦ Real.cos x ^ 2 - Real.sin x ^ 2) 0 := by
      fun_prop
    exact (hc.tendsto.eventually_ne (by norm_num)).filter_mono nhdsWithin_le_nhds
  · simpa using (hf 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (hg 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact hq

theorem log_one_add_reciprocal_cancellation_lhospital_right :
    Tendsto (fun x : ℝ ↦ 1 / Real.log (1 + x) - 1 / x)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log (1 + x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using! (((hasDerivAt_id (0 : ℝ)).const_add 1).log
      (by norm_num)).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hid : Tendsto (fun x : ℝ ↦ x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hrec : Tendsto (fun x : ℝ ↦ 1 / (1 + x)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ ↦ 1 / (1 + x)) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlinear := logarithm_linear_quotient_tendsto.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hnormalized := hlinear.add hrec
  norm_num at hnormalized
  have hderivative : Tendsto (fun x : ℝ ↦ (1 - 1 / (1 + x)) /
      (Real.log (1 + x) + x / (1 + x))) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    have ht := hrec.div hnormalized (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin, hnormalized.eventually_ne
      (by norm_num : (2 : ℝ) ≠ 0)] with x (hx : 0 < x) hq
    have hbase : 1 + x ≠ 0 := by linarith
    have hden : Real.log (1 + x) + x / (1 + x) ≠ 0 := by
      intro he
      apply hq
      calc
        Real.log (1 + x) / x + (1 + x)⁻¹ =
            (Real.log (1 + x) + x / (1 + x)) / x := by
              field_simp [hx.ne', hbase]
        _ = 0 := by rw [he, zero_div]
    dsimp only [Pi.div_apply]
    field_simp [hx.ne', hbase, hden]
    ring
  have hf : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt (fun y : ℝ ↦ y - Real.log (1 + y))
      (1 - 1 / (1 + x)) x := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    simpa using! (hasDerivAt_id x).fun_sub (((hasDerivAt_id x).const_add 1).log
      (by linarith : 1 + x ≠ 0))
  have hg : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt (fun y : ℝ ↦ y * Real.log (1 + y))
      (Real.log (1 + x) + x / (1 + x)) x := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    convert! (hasDerivAt_id x).fun_mul (((hasDerivAt_id x).const_add 1).log
      (by linarith : 1 + x ≠ 0)) using 1; (simp only [id_eq]; ring)
  have hne : ∀ᶠ x in 𝓝[>] (0 : ℝ), Real.log (1 + x) + x / (1 + x) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, hnormalized.eventually_ne
      (by norm_num : (2 : ℝ) ≠ 0)] with x (hx : 0 < x) hq
    intro he
    apply hq
    calc
      Real.log (1 + x) / x + (1 + x)⁻¹ =
          (Real.log (1 + x) + x / (1 + x)) / x := by
            field_simp [hx.ne', (by linarith : 1 + x ≠ 0)]
      _ = 0 := by rw [he, zero_div]
  have ht := HasDerivAt.lhopital_zero_nhdsGT hf hg hne
    (by simpa only [sub_self] using hid.sub hlog)
    (by simpa only [mul_zero] using hid.mul hlog) hderivative
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  have hl : Real.log (1 + x) ≠ 0 := ne_of_gt (Real.log_pos (by linarith : 1 < 1 + x))
  field_simp [hx.ne', hl]

theorem one_sub_cosine_double_div_identity_sine_lhospital :
    Tendsto (fun x : ℝ ↦ (1 - Real.cos (2 * x)) / (x * Real.sin x))
      (𝓝[≠] (0 : ℝ)) (𝓝 2) := by
  have hd : HasDerivAt (fun x : ℝ ↦ Real.sin (2 * x)) 2 0 := by
    simpa using! ((hasDerivAt_id (0 : ℝ)).const_mul 2).sin
  have hsin : Tendsto (fun x : ℝ ↦ Real.sin (2 * x) / x)
      (𝓝[≠] (0 : ℝ)) (𝓝 2) := by
    simpa only [slope_fun_def_field, sub_zero, mul_zero, Real.sin_zero] using! hd.tendsto_slope
  have hnormalized := sine_linear_quotient_tendsto.add cosine_tendsto_one
  norm_num at hnormalized
  have hq : Tendsto (fun x : ℝ ↦ 2 * Real.sin (2 * x) / (Real.sin x + x * Real.cos x))
      (𝓝[≠] (0 : ℝ)) (𝓝 2) := by
    have ht := (hsin.const_mul 2).div hnormalized (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at ht
    apply ht.congr'
    filter_upwards [basic_natural_domains_eventually, hnormalized.eventually_ne
      (by norm_num : (2 : ℝ) ≠ 0)] with x hx he
    have hg : Real.sin x + x * Real.cos x ≠ 0 := by
      intro hg
      apply he
      calc
        Real.sin x / x + Real.cos x = (Real.sin x + x * Real.cos x) / x := by
          field_simp [hx.1]
        _ = 0 := by rw [hg, zero_div]
    dsimp only [Pi.div_apply]
    field_simp [hx.1, hg]
  have hf (x : ℝ) : HasDerivAt (fun y : ℝ ↦ 1 - Real.cos (2 * y))
      (2 * Real.sin (2 * x)) x := by
    convert! (((hasDerivAt_id x).const_mul 2).cos).const_sub 1 using 1;
      (simp only [id_eq]; ring)
  have hg (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y * Real.sin y)
      (Real.sin x + x * Real.cos x) x := by
    simpa using! (hasDerivAt_id x).fun_mul (Real.hasDerivAt_sin x)
  apply calculus.Chapter04.Section04.lhopital_zero_punctured
    (Eventually.of_forall hf) (Eventually.of_forall hg)
  · filter_upwards [basic_natural_domains_eventually, hnormalized.eventually_ne
      (by norm_num : (2 : ℝ) ≠ 0)] with x hx he
    intro hz
    apply he
    calc
      Real.sin x / x + Real.cos x = (Real.sin x + x * Real.cos x) / x := by
        field_simp [hx.1]
      _ = 0 := by rw [hz, zero_div]
  · simpa using (hf 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (hg 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact hq

theorem identity_sub_arctangent_cubic_lhospital :
    Tendsto (fun x : ℝ ↦ (x - Real.arctan x) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
  have hf (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y - Real.arctan y)
      (1 - 1 / (1 + x ^ 2)) x := by
    simpa using! (hasDerivAt_id x).fun_sub (Real.hasDerivAt_arctan x)
  have hg (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ 3) (3 * x ^ 2) x := by
    simpa using! (hasDerivAt_id x).fun_pow 3
  have hq : Tendsto (fun x : ℝ ↦ (1 - 1 / (1 + x ^ 2)) / (3 * x ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ 1 / (3 * (1 + x ^ 2))) 0 := by
      fun_prop (disch := norm_num)
    have ht : Tendsto (fun x : ℝ ↦ 1 / (3 * (1 + x ^ 2)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hp : 1 + x ^ 2 ≠ 0 := by positivity
    field_simp [hx0, hp]
    ring
  apply calculus.Chapter04.Section04.lhopital_zero_punctured
    (Eventually.of_forall hf) (Eventually.of_forall hg)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0)
  · simpa using (hf 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (hg 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact hq

theorem identity_sine_tangent_ratio_lhospital :
    Tendsto (fun x : ℝ ↦ (x - Real.sin x) / (x - Real.tan x))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ)) := by
  have hf (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y - Real.sin y) (1 - Real.cos x) x := by
    simpa using! (hasDerivAt_id x).fun_sub (Real.hasDerivAt_sin x)
  have hg {x : ℝ} (hx : Real.cos x ≠ 0) :
      HasDerivAt (fun y : ℝ ↦ y - Real.tan y) (1 - 1 / Real.cos x ^ 2) x := by
    simpa using! (hasDerivAt_id x).fun_sub (Real.hasDerivAt_tan hx)
  have hcn : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 1 + Real.cos x ≠ 0 := by
    have ht := cosine_tendsto_one.const_add 1
    norm_num at ht
    exact ht.eventually_ne (by norm_num : (2 : ℝ) ≠ 0)
  have hsq : ∀ᶠ x in 𝓝[≠] (0 : ℝ), Real.cos x ^ 2 ≠ 1 := by
    filter_upwards [basic_natural_domains_eventually] with x hx
    intro he
    have hs : Real.sin x ^ 2 = 0 := by nlinarith [Real.sin_sq_add_cos_sq x]
    exact hx.2.1 (sq_eq_zero_iff.mp hs)
  have hq : Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / (1 - 1 / Real.cos x ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ -(Real.cos x ^ 2) / (1 + Real.cos x)) 0 := by
      fun_prop (disch := norm_num)
    have ht : Tendsto (fun x : ℝ ↦ -(Real.cos x ^ 2) / (1 + Real.cos x))
        (𝓝[≠] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ)) := by
      have ht := hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
      norm_num at ht ⊢
      exact ht
    apply ht.congr'
    filter_upwards [basic_natural_domains_eventually, hcn, hsq] with x hx hc he
    have hd : 1 - 1 / Real.cos x ^ 2 ≠ 0 := by
      intro hz
      have ht : Real.cos x ^ 2 = 1 := by
        field_simp [hx.2.2.1] at hz
        linarith
      exact he ht
    field_simp [hx.2.2.1, hc, hd]
    ring
  apply calculus.Chapter04.Section04.lhopital_zero_punctured
    (Eventually.of_forall hf)
  · filter_upwards [basic_natural_domains_eventually] with x hx
    exact hg hx.2.2.1
  · filter_upwards [basic_natural_domains_eventually, hsq] with x hx he
    intro hz
    apply he
    field_simp [hx.2.2.1] at hz
    linarith
  · simpa using (hf 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (hg (x := 0) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact hq

theorem logarithm_div_cotangent_lhospital_right :
    Tendsto (fun x : ℝ ↦ Real.log x / Real.cot x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have htan : Tendsto (fun x : ℝ ↦ Real.tan x / x)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have ht := sine_linear_quotient_tendsto.div cosine_tendsto_one
      (by norm_num : (1 : ℝ) ≠ 0)
    norm_num only [div_one] at ht
    apply ht.congr'
    filter_upwards [basic_natural_domains_eventually] with x hx
    dsimp only [Pi.div_apply]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hx.1, hx.2.2.1]
  have ht := logarithm_div_reciprocal_right.mul (htan.mono_left (nhdsGT_le_nhdsNE (0 : ℝ)))
  norm_num only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [basic_natural_domains_eventually.filter_mono (nhdsGT_le_nhdsNE (0 : ℝ))]
    with x hx
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
  field_simp [hx.1, hx.2.1, hx.2.2.1]

theorem arctangent_tail_div_log_reciprocal_lhospital :
    Tendsto (fun x : ℝ ↦ (Real.pi / 2 - Real.arctan x) / Real.log (1 + 1 / x))
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hf (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.pi / 2 - Real.arctan y)
      (-1 / (1 + x ^ 2)) x := by
    simpa only [neg_div] using! (Real.hasDerivAt_arctan x).const_sub (Real.pi / 2)
  have hg {x : ℝ} (hx : 0 < x) : HasDerivAt (fun y : ℝ ↦ Real.log (1 + 1 / y))
      (-1 / (x * (x + 1))) x := by
    have ht := ((hasDerivAt_inv hx.ne').const_add 1).log
      (by positivity : 1 + x⁻¹ ≠ 0)
    convert! ht using 1
    · simp only [one_div]
    · field_simp [hx.ne', (by linarith : x + 1 ≠ 0)]
  have hq : Tendsto (fun x : ℝ ↦ (-1 / (1 + x ^ 2)) / (-1 / (x * (x + 1))))
      atTop (𝓝 1) := by
    have ht := (hinv.const_add 1).div
      ((hinv.pow 2).const_add 1) (by norm_num : (1 + (0 : ℝ) ^ 2) ≠ 0)
    have ht' : Tendsto (fun x : ℝ ↦ (1 + 1 / x) / (1 + (1 / x) ^ 2)) atTop (𝓝 1) := by
      simpa using! ht
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hp : 1 + x ^ 2 ≠ 0 := by positivity
    have hu : 1 + (1 / x) ^ 2 ≠ 0 := by positivity
    field_simp [hx.ne', (by linarith : x + 1 ≠ 0), hp, hu]
    ring
  apply HasDerivAt.lhopital_zero_atTop (Eventually.of_forall hf)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hg hx
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_ne_zero (by norm_num) (mul_ne_zero hx.ne' (by linarith))
  · have ht := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_sub (Real.pi / 2)
    simpa only [sub_self] using! ht
  · have hb : Tendsto (fun x : ℝ ↦ 1 + 1 / x) atTop (𝓝 1) := by
      simpa using! hinv.const_add 1
    simpa only [Real.log_one, Function.comp_def] using!
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hb
  · exact hq

theorem square_root_exp_negative_lhospital :
    Tendsto (fun x : ℝ ↦ Real.sqrt x * Real.exp (-x)) atTop (𝓝 0) := by
  have hrec : Tendsto (fun x : ℝ ↦ 1 / (2 * Real.sqrt x)) atTop (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).div_const 2
    simp only [zero_div] at ht
    apply ht.congr'
    filter_upwards with x
    dsimp only [Function.comp_def]
    ring
  have hq : Tendsto (fun x : ℝ ↦ (1 / (2 * Real.sqrt x)) / Real.exp x)
      atTop (𝓝 0) := by
    have ht := hrec.mul Real.tendsto_exp_neg_atTop_nhds_zero
    simp only [mul_zero] at ht
    simpa only [Real.exp_neg, div_eq_mul_inv] using! ht
  have ht := calculus.Chapter04.Section04InfiniteExtensions.source_lhopital_infinite_atTop
    (a := 0)
    (fun x hx ↦ Real.hasDerivAt_sqrt (ne_of_gt hx))
    (fun x _ ↦ Real.hasDerivAt_exp x)
    (fun x _ ↦ Real.exp_ne_zero x)
    (Or.inl Real.tendsto_sqrt_atTop) (Or.inl Real.tendsto_exp_atTop) hq
    (Or.inl ⟨0, rfl⟩)
  simpa only [Real.exp_neg, div_eq_mul_inv] using! ht

theorem affine_power_second_coefficient_lhospital (n : ℝ) :
    Tendsto (fun x : ℝ ↦ ((1 + x) ^ n - 1 - n * x) / x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (n * (n - 1) / 2)) := by
  have hbase : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 1 + x ≠ 0 := by
    filter_upwards [basic_natural_domains_eventually] with x hx
    exact ne_of_gt hx.2.2.2.1
  have hfirst {x : ℝ} (hx : 1 + x ≠ 0) :
      HasDerivAt (fun y : ℝ ↦ (1 + y) ^ n - 1 - n * y)
        (n * (1 + x) ^ (n - 1) - n) x := by
    simpa using! ((((hasDerivAt_id x).const_add 1).rpow_const (p := n)
      (Or.inl hx)).sub_const 1).fun_sub ((hasDerivAt_id x).const_mul n)
  have hsecond {x : ℝ} (hx : 1 + x ≠ 0) :
      HasDerivAt (fun y : ℝ ↦ n * (1 + y) ^ (n - 1) - n)
        (n * (n - 1) * (1 + x) ^ (n - 2)) x := by
    have ht := (((hasDerivAt_id x).const_add 1).rpow_const (p := n - 1)
      (Or.inl hx)).const_mul n
    have he : n - 1 - 1 = n - 2 := by ring
    simpa only [he, mul_one, one_mul, id_eq, mul_assoc] using! ht.sub_const n
  have hden (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    simpa using! (hasDerivAt_id x).fun_pow 2
  have hden' (x : ℝ) : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
    simpa using! (hasDerivAt_id x).const_mul 2
  have hq : Tendsto (fun x : ℝ ↦ (n * (1 + x) ^ (n - 1) - n) / (2 * x))
      (𝓝[≠] (0 : ℝ)) (𝓝 (n * (n - 1) / 2)) := by
    apply calculus.Chapter04.Section04.lhopital_zero_punctured
    · filter_upwards [hbase] with x hx
      exact hsecond hx
    · exact Eventually.of_forall hden'
    · exact Eventually.of_forall (fun (_ : ℝ) ↦ by norm_num)
    · simpa using (hsecond (x := 0) (by norm_num)).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    · simpa using (hden' 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    · have hc : ContinuousAt (fun x : ℝ ↦ (n * (n - 1) * (1 + x) ^ (n - 2)) / 2) 0 := by
        have hp : ContinuousAt (fun x : ℝ ↦ (1 + x) ^ (n - 2)) 0 :=
          (((hasDerivAt_id (0 : ℝ)).const_add 1).rpow_const (p := n - 2)
            (Or.inl (by norm_num))).continuousAt
        exact (hp.const_mul (n * (n - 1))).div_const 2
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply calculus.Chapter04.Section04.lhopital_zero_punctured
  · filter_upwards [hbase] with x hx
    exact hfirst hx
  · exact Eventually.of_forall hden
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero (by norm_num) hx0
  · simpa using (hfirst (x := 0) (by norm_num)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  · simpa using (hden 0).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  · exact hq

end calculus.Chapter04.Section04LHospitalLimitCalculations
