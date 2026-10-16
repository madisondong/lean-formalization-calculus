import calculus.Chapter03.Section04
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Bài tập 3.6.4(a). -/
namespace calculus.Chapter03.Section06PowerSequenceExercises
open Set Filter Topology
open calculus.Chapter02.Section03 calculus.Chapter03.Section04

noncomputable def powerSequenceTerm (x : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ)^x - (n : ℝ)^(-x)) / ((n : ℝ)^x + (n : ℝ)^(-x))

noncomputable def powerSequenceLimit (x : ℝ) : ℝ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

theorem power_sequence_terms_defined (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    0 < (n : ℝ)^x ∧ 0 < (n : ℝ)^(-x) ∧
      (n : ℝ)^x + (n : ℝ)^(-x) ≠ 0 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h1 := Real.rpow_pos_of_pos hnpos x
  have h2 := Real.rpow_pos_of_pos hnpos (-x)
  exact ⟨h1, h2, (add_pos h1 h2).ne'⟩

theorem positive_power_quotient_limit (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ ↦ (t^x-t^(-x))/(t^x+t^(-x))) atTop (𝓝 (1 : ℝ)) := by
  have hu : Tendsto (fun t : ℝ ↦ t^x) atTop atTop := tendsto_rpow_atTop hx
  have hv : Tendsto (fun t : ℝ ↦ t^(-x)) atTop (𝓝 (0 : ℝ)) := tendsto_rpow_neg_atTop hx
  have hratio : Tendsto (fun t : ℝ ↦ t^(-x)/t^x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using hv.mul hu.inv_tendsto_atTop
  have hc : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have ht := (hc.sub hratio).div
    (hc.add hratio) (by norm_num : (1 : ℝ)+0 ≠ 0)
  have ht' : Tendsto (fun t : ℝ ↦ (1-t^(-x)/t^x)/(1+t^(-x)/t^x))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_apply, sub_zero, add_zero, div_one] using! ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hpow := (Real.rpow_pos_of_pos ht x).ne'
  have hsum := (add_pos (Real.rpow_pos_of_pos ht x)
    (Real.rpow_pos_of_pos ht (-x))).ne'
  have hnorm : 1+t^(-x)/t^x ≠ 0 := by
    have hh : 1+t^(-x)/t^x = (t^x+t^(-x))/t^x := by field_simp
    rw [hh]; exact div_ne_zero hsum hpow
  field_simp [hpow, hsum, hnorm]

theorem power_sequence_converges (x : ℝ) :
    ConvergesTo (powerSequenceTerm x) (powerSequenceLimit x) := by
  apply convergesTo_iff_tendsto.mpr
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have ht := ((positive_power_quotient_limit (-x) (neg_pos.mpr hx)).comp
      tendsto_natCast_atTop_atTop).neg
    have ht' : Tendsto (fun n : ℕ ↦
        -(((n : ℝ)^(-x)-(n : ℝ)^x)/((n : ℝ)^(-x)+(n : ℝ)^x)))
        atTop (𝓝 (powerSequenceLimit x)) := by
      simpa [powerSequenceLimit, not_lt.mpr hx.le, hx] using ht
    apply ht'.congr'
    filter_upwards [] with n
    simp only [powerSequenceTerm]
    rw [add_comm ((n : ℝ)^(-x))]
    simp only [div_eq_mul_inv]
    ring
  · have he : powerSequenceTerm 0 = (fun _ : ℕ ↦ (0 : ℝ)) := by
      funext n
      simp [powerSequenceTerm]
    rw [he]
    simp [powerSequenceLimit]
  · change Tendsto (fun n : ℕ ↦
      ((n : ℝ)^x-(n : ℝ)^(-x))/((n : ℝ)^x+(n : ℝ)^(-x)))
      atTop (𝓝 (powerSequenceLimit x))
    simpa only [Function.comp_def, powerSequenceLimit, if_pos hx] using
      (positive_power_quotient_limit x hx).comp tendsto_natCast_atTop_atTop

theorem power_sequence_limit_continuity (x : ℝ) :
    DomainContinuousAt univ powerSequenceLimit x ↔ x ≠ 0 := by
  rw [domainContinuousAt_univ]
  constructor
  · intro hc hx
    subst x
    have hr : Tendsto powerSequenceLimit (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp [powerSequenceLimit, show 0 < y from hy]
    have h0 : Tendsto powerSequenceLimit (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa [powerSequenceLimit] using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact (by norm_num : (1 : ℝ) ≠ 0) (tendsto_nhds_unique hr h0)
  · intro hx
    rcases lt_or_gt_of_ne hx with h | h
    · have he : powerSequenceLimit =ᶠ[𝓝 x] (fun _ ↦ (-1 : ℝ)) := by
        filter_upwards [eventually_lt_nhds h] with y hy
        simp [powerSequenceLimit, hy, not_lt.mpr hy.le]
      exact continuousAt_const.congr_of_eventuallyEq he
    · have he : powerSequenceLimit =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
        filter_upwards [eventually_gt_nhds h] with y hy
        simp [powerSequenceLimit, hy]
      exact continuousAt_const.congr_of_eventuallyEq he

/-- Bài tập 4(a): giới hạn dãy là sign(x), liên tục khi và chỉ khi x≠0. -/
theorem exercise04_power_sequence_classification :
    (∀ x : ℝ, (∀ n : ℕ, 1 ≤ n →
      0 < (n : ℝ)^x ∧ 0 < (n : ℝ)^(-x) ∧ (n : ℝ)^x+(n : ℝ)^(-x) ≠ 0) ∧
      ConvergesTo (powerSequenceTerm x) (powerSequenceLimit x)) ∧
    (∀ x : ℝ, DomainContinuousAt univ powerSequenceLimit x ↔ x ≠ 0) := by
  exact ⟨fun x ↦ ⟨power_sequence_terms_defined x, power_sequence_converges x⟩,
    power_sequence_limit_continuity⟩

end calculus.Chapter03.Section06PowerSequenceExercises
