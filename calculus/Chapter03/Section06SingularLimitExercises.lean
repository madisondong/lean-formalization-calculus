import calculus.Chapter03.Section03Exercises
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# §3.6 — Bài tập 6(d,e): giới hạn vô hạn và giới hạn hai phía không tồn tại

Nguồn: dòng 3161–3162.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter03.Section06SingularLimitExercises
open Set Filter Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02Infinite


def logarithmicSqrtRatioDomain : Set ℝ :=
  {x | 0 ≤ 1 + x ∧ x ≠ 3 ∧ 0 < (3 - Real.sqrt (1 + x)) / (3 - x)}


theorem near_three_mem_logarithmic_sqrt_domain {x : ℝ} (hx : x ∈ Ioo 2 3) :
    x ∈ logarithmicSqrtRatioDomain := by
  have hrad : 0 ≤ 1 + x := by linarith [hx.1]
  have hs : Real.sqrt (1 + x) < 2 :=
    (Real.sqrt_lt hrad (by norm_num : (0 : ℝ) ≤ 2)).mpr (by nlinarith [hx.2])
  exact ⟨hrad, hx.2.ne, div_pos (by linarith) (by linarith [hx.2])⟩

theorem logarithmic_sqrt_domain_left_accumulation :
    LeftAccumulationPointOf logarithmicSqrtRatioDomain 3 := by
  intro δ hδ
  have hη : 0 < min δ 1 := lt_min hδ zero_lt_one
  have hm := min_le_right δ (1 : ℝ)
  have hδm := min_le_left δ (1 : ℝ)
  refine ⟨3 - min δ 1 / 2, near_three_mem_logarithmic_sqrt_domain
    ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Bài tập 6(d): giới hạn bằng +∞ khi x→3⁻ trên miền tự nhiên của logarit và căn. -/
theorem exercise06_logarithmic_sqrt_left_top :
    DomainLeftTopLimit logarithmicSqrtRatioDomain
      (fun x : ℝ ↦ Real.log ((3 - Real.sqrt (1 + x)) / (3 - x))) 3 := by
  refine ⟨logarithmic_sqrt_domain_left_accumulation, ?_⟩
  let l : Filter ℝ := 𝓝[logarithmicSqrtRatioDomain ∩ Iio 3] 3
  have hnum : Tendsto (fun x : ℝ ↦ 3 - Real.sqrt (1 + x)) l (𝓝 1) := by
    have hc : Continuous (fun x : ℝ ↦ 3 - Real.sqrt (1 + x)) :=
      continuous_const.sub (Real.continuous_sqrt.comp (continuous_const.add continuous_id))
    have ht := (hc.continuousAt (x := (3 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds
      (s := logarithmicSqrtRatioDomain ∩ Iio 3))
    have hs4 : Real.sqrt (4 : ℝ) = 2 :=
      (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
    simpa only [show (1 : ℝ) + 3 = 4 by norm_num, hs4, show (3 : ℝ) - 2 = 1 by norm_num] using ht
  have hden : Tendsto (fun x : ℝ ↦ 3 - x) l (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ 3 - x) 3 :=
      continuous_const.continuousAt.sub continuous_id.continuousAt
    simpa only [sub_self] using hc.tendsto.mono_left
      (nhdsWithin_le_nhds (s := logarithmicSqrtRatioDomain ∩ Iio 3))
  have hpos : ∀ᶠ x in l, 0 < 3 - x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact sub_pos.mpr hx.2
  have hdenGT : Tendsto (fun x : ℝ ↦ 3 - x) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hden, hpos⟩
  have hratio : Tendsto (fun x : ℝ ↦ (3 - Real.sqrt (1 + x)) / (3 - x)) l atTop := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using
      hnum.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hdenGT.inv_tendsto_nhdsGT_zero
  exact Real.tendsto_log_atTop.comp hratio


def exponentialSqrtSquareDomain : Set ℝ := {x | -2 ≤ x ∧ x ≠ 1}

def exponentialSqrtSquareQuotient (x : ℝ) : ℝ :=
  (Real.exp (Real.sqrt (2 + x)) - Real.exp (Real.sqrt 3)) / (x - 1) ^ 2


theorem exponential_sqrt_square_domain_sides :
    LeftAccumulationPointOf exponentialSqrtSquareDomain 1 ∧
      RightAccumulationPointOf exponentialSqrtSquareDomain 1 := by
  constructor <;> intro δ hδ
  · have hη : 0 < min δ 1 := lt_min hδ zero_lt_one
    have hm := min_le_right δ (1 : ℝ)
    have hδm := min_le_left δ (1 : ℝ)
    exact ⟨1 - min δ 1 / 2, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · exact ⟨1 + δ / 2, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩


theorem exponential_sqrt_derivative_at_one :
    HasDerivAt (fun x : ℝ ↦ Real.exp (Real.sqrt (2 + x)))
      (Real.exp (Real.sqrt 3) / (2 * Real.sqrt 3)) 1 := by
  have hs : HasDerivAt (fun x : ℝ ↦ Real.sqrt (2 + x)) (1 / (2 * Real.sqrt 3)) 1 := by
    have ho : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt 3)) (2 + (1 : ℝ)) := by
      convert Real.hasDerivAt_sqrt (by norm_num : (3 : ℝ) ≠ 0) using 1
      norm_num
    simpa only [mul_one, id_eq, Function.comp_def] using ho.comp 1 ((hasDerivAt_id (1 : ℝ)).const_add 2)
  simpa only [show (2 : ℝ) + 1 = 3 by norm_num, mul_one_div] using hs.exp

/-- Bài tập 6(e): giới hạn trái −∞, giới hạn phải +∞; mẫu bình phương. -/
theorem exercise06_exponential_sqrt_opposite_side_limits :
    DomainLeftBotLimit exponentialSqrtSquareDomain exponentialSqrtSquareQuotient 1 ∧
      DomainRightTopLimit exponentialSqrtSquareDomain exponentialSqrtSquareQuotient 1 := by
  have hL : 0 < Real.exp (Real.sqrt 3) / (2 * Real.sqrt 3) := by positivity
  have hs : Tendsto (fun x : ℝ ↦
      (Real.exp (Real.sqrt (2 + x)) - Real.exp (Real.sqrt 3)) / (x - 1))
      (𝓝[≠] 1) (𝓝 (Real.exp (Real.sqrt 3) / (2 * Real.sqrt 3))) := by
    simpa only [slope_fun_def_field, show (2 : ℝ) + 1 = 3 by norm_num] using
      exponential_sqrt_derivative_at_one.tendsto_slope
  have hl := reciprocal_odd_power_left_bot 1 1 (by norm_num) (by decide)
  have hr := reciprocal_power_right_top 1 1 (by norm_num)
  have hEq (x : ℝ) :
      ((Real.exp (Real.sqrt (2 + x)) - Real.exp (Real.sqrt 3)) / (x - 1)) *
        (1 / (x - 1)) = exponentialSqrtSquareQuotient x := by
    simp only [exponentialSqrtSquareQuotient, div_mul_div_comm, mul_one, pow_two]
  constructor
  · refine ⟨exponential_sqrt_square_domain_sides.1, ?_⟩
    have hsL := hs.mono_left (nhdsWithin_mono 1
      (show exponentialSqrtSquareDomain ∩ Iio 1 ⊆ {1}ᶜ from fun _ hx ↦ hx.1.2))
    have hpL : Tendsto (fun x : ℝ ↦ 1 / (x - 1))
        (𝓝[exponentialSqrtSquareDomain ∩ Iio 1] 1) atBot := by
      simpa only [pow_one] using hl.2.mono_left (nhdsWithin_mono 1
        (show exponentialSqrtSquareDomain ∩ Iio 1 ⊆ (univ \ {1}) ∩ Iio 1 from
          fun _ hx ↦ ⟨⟨mem_univ _, hx.1.2⟩, hx.2⟩))
    exact (hsL.pos_mul_atBot hL hpL).congr hEq
  · refine ⟨exponential_sqrt_square_domain_sides.2, ?_⟩
    have hsR := hs.mono_left (nhdsWithin_mono 1
      (show exponentialSqrtSquareDomain ∩ Ioi 1 ⊆ {1}ᶜ from fun _ hx ↦ hx.1.2))
    have hpR : Tendsto (fun x : ℝ ↦ 1 / (x - 1))
        (𝓝[exponentialSqrtSquareDomain ∩ Ioi 1] 1) atTop := by
      simpa only [pow_one] using hr.2.mono_left (nhdsWithin_mono 1
        (show exponentialSqrtSquareDomain ∩ Ioi 1 ⊆ (univ \ {1}) ∩ Ioi 1 from
          fun _ hx ↦ ⟨⟨mem_univ _, hx.1.2⟩, hx.2⟩))
    exact (hsR.pos_mul_atTop hL hpR).congr hEq


theorem left_domain_filter_neBot {D : Set ℝ} {a : ℝ} (hl : LeftAccumulationPointOf D a) :
    (𝓝[D ∩ Iio a] a).NeBot := by
  have hn := accumulationPointOf_iff_neBot.mp (leftAccumulation_iff_restricted.mp hl)
  have he : (D ∩ Iio a) \ {a} = D ∩ Iio a := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_Iio, mem_singleton_iff]
    exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, hx.2.ne⟩⟩
  rwa [he] at hn


theorem right_domain_filter_neBot {D : Set ℝ} {a : ℝ} (hr : RightAccumulationPointOf D a) :
    (𝓝[D ∩ Ioi a] a).NeBot := by
  have hn := accumulationPointOf_iff_neBot.mp (rightAccumulation_iff_restricted.mp hr)
  have he : (D ∩ Ioi a) \ {a} = D ∩ Ioi a := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_Ioi, mem_singleton_iff]
    exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, hx.2.ne'⟩⟩
  rwa [he] at hn

/-- Bài tập 6(e): không có giới hạn hai phía hữu hạn, bằng +∞ hoặc bằng −∞. -/
theorem exercise06_exponential_sqrt_no_two_sided_limits :
    ¬HasDomainLimit exponentialSqrtSquareDomain exponentialSqrtSquareQuotient 1 ∧
      ¬DomainPointTopLimit exponentialSqrtSquareDomain exponentialSqrtSquareQuotient 1 ∧
      ¬DomainPointBotLimit exponentialSqrtSquareDomain exponentialSqrtSquareQuotient 1 := by
  have hl := exercise06_exponential_sqrt_opposite_side_limits.1
  have hr := exercise06_exponential_sqrt_opposite_side_limits.2
  let := left_domain_filter_neBot hl.1
  let := right_domain_filter_neBot hr.1
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨L, h⟩
    have hs := ((domainLimit_iff_left_right hl.1 hr.1).mp h).1
    have hf := (domainLeftLimit_iff_tendsto hl.1).mp hs
    exact not_tendsto_nhds_of_tendsto_atBot hl.2 L hf
  · intro h
    have ht := ((domainPointTopLimit_iff_sides hl.1 hr.1).mp h).1.2
    exact hl.2.not_tendsto disjoint_atBot_atTop ht
  · intro h
    have hb := ((domainPointBotLimit_iff_sides hl.1 hr.1).mp h).2.2
    exact hr.2.not_tendsto disjoint_atTop_atBot hb

end calculus.Chapter03.Section06SingularLimitExercises
