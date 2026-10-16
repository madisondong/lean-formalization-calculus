import calculus.Chapter03.Section04
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Bài tập 3.6.3: giới hạn dãy lượng giác. -/
namespace calculus.Chapter03.Section06TrigonometricSequenceExercises
open Set Filter Topology
open calculus.Chapter02.Section03 calculus.Chapter03.Section04

def printedTrigSequenceDomain : Set ℝ :=
  {x | ∀ k : ℤ, x ≠ -Real.pi / 2 + 2 * (k : ℝ) * Real.pi}

noncomputable def trigonometricSequenceTerm (a x : ℝ) (n : ℕ) : ℝ :=
  x / (1 + a * Real.sin x ^ n)

noncomputable def trigonometricSequenceLimit (a x : ℝ) : ℝ :=
  if Real.sin x = 1 then x / (1 + a) else x

theorem printed_trig_domain_iff (x : ℝ) :
    x ∈ printedTrigSequenceDomain ↔ Real.sin x ≠ -1 := by
  constructor
  · intro hx hs
    have hc : Real.cos (x + Real.pi / 2) = 1 := by
      rw [Real.cos_add_pi_div_two, hs]; norm_num
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hc
    exact hx k (by nlinarith [hk])
  · intro hs k hx
    apply hs
    rw [hx, show -Real.pi / 2 + 2 * (k : ℝ) * Real.pi =
      -Real.pi / 2 + (k : ℝ) * (2 * Real.pi) by ring,
      Real.sin_add_int_mul_two_pi]
    simp [neg_div, Real.sin_neg, Real.sin_pi_div_two]

theorem printed_trig_domain_open : IsOpen printedTrigSequenceDomain := by
  have he : printedTrigSequenceDomain = {x : ℝ | Real.sin x ≠ -1} := by
    ext x; exact printed_trig_domain_iff x
  rw [he]
  exact isOpen_ne_fun Real.continuous_sin continuous_const


theorem trigonometric_sequence_converges (a x : ℝ) (ha : a ≠ -1)
    (hx : x ∈ printedTrigSequenceDomain) :
    (∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 1 + a * Real.sin x ^ n ≠ 0) ∧
      ConvergesTo (trigonometricSequenceTerm a x) (trigonometricSequenceLimit a x) := by
  by_cases hs : Real.sin x = 1
  · have hd : 1 + a ≠ 0 := by intro hz; apply ha; linarith
    refine ⟨?_, convergesTo_iff_tendsto.mpr ?_⟩
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact ⟨hn, by simpa [hs] using hd⟩
    · change Tendsto (fun n : ℕ ↦ x/(1+a*Real.sin x^n)) atTop (𝓝 (trigonometricSequenceLimit a x))
      simp [trigonometricSequenceLimit, hs]
  · have hneg := (printed_trig_domain_iff x).mp hx
    have habs : |Real.sin x| < 1 := by
      rw [abs_lt]
      exact ⟨lt_of_le_of_ne (Real.neg_one_le_sin x) (Ne.symm hneg),
        lt_of_le_of_ne (Real.sin_le_one x) hs⟩
    have hp : Tendsto (fun n : ℕ ↦ Real.sin x ^ n) atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_iff.mpr habs
    have hd : Tendsto (fun n : ℕ ↦ 1 + a * Real.sin x ^ n) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (hp.const_mul a)
    refine ⟨?_, convergesTo_iff_tendsto.mpr ?_⟩
    · filter_upwards [eventually_ge_atTop 1, hd.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)]
        with n hn hdne
      exact ⟨hn, hdne⟩
    · rw [trigonometricSequenceLimit, if_neg hs]
      change Tendsto ((fun _ : ℕ ↦ x)/(fun n : ℕ ↦ 1+a*Real.sin x^n)) atTop (𝓝 x)
      simpa only [div_one] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x)).div hd
          (by norm_num : (1 : ℝ) ≠ 0)


theorem trigonometric_sequence_extension_independent (a x : ℝ) (ha : a ≠ -1)
    (hx : x ∈ printedTrigSequenceDomain) (u : ℕ → ℝ)
    (hu : ∀ᶠ n : ℕ in atTop,
      1 ≤ n → 1 + a * Real.sin x ^ n ≠ 0 → u n = trigonometricSequenceTerm a x n) :
    ConvergesTo u (trigonometricSequenceLimit a x) := by
  obtain ⟨hd, hl⟩ := trigonometric_sequence_converges a x ha hx
  apply convergesTo_iff_tendsto.mpr
  apply (convergesTo_iff_tendsto.mp hl).congr'
  filter_upwards [hd, hu] with n hn hune
  exact (hune hn.1 hn.2).symm


theorem sine_maximum_punctured_ne (s : ℝ) (hs : Real.sin s = 1) :
    ∀ᶠ x : ℝ in 𝓝[≠] s, Real.sin x ≠ 1 := by
  have hcs : Real.cos s = 0 := by
    apply sq_eq_zero_iff.mp
    nlinarith [Real.sin_sq_add_cos_sq s]
  have hb : {x : ℝ | |x-s| < 2*Real.pi} ∈ 𝓝 s :=
    (isOpen_lt (continuous_id.sub continuous_const).abs continuous_const).mem_nhds
      (by simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hb,
    self_mem_nhdsWithin] with x hx hxne
  intro hsin
  have hcos : Real.cos (x-s) = 1 := by
    rw [Real.cos_sub, hcs, hs, hsin]; ring
  have he : x-s = 0 := (Real.cos_eq_one_iff_of_lt_of_lt
    (abs_lt.mp hx).1 (abs_lt.mp hx).2).mp hcos
  exact hxne (sub_eq_zero.mp he)

theorem trigonometric_sequence_continuity (a x : ℝ) (ha : a ≠ -1)
    (hx : x ∈ printedTrigSequenceDomain) :
    DomainContinuousAt printedTrigSequenceDomain (trigonometricSequenceLimit a) x ↔
      a = 0 ∨ Real.sin x ≠ 1 := by
  have hbridge : DomainContinuousAt printedTrigSequenceDomain (trigonometricSequenceLimit a) x ↔
      ContinuousAt (trigonometricSequenceLimit a) x := by
    rw [domainContinuousAt_iff_within hx]
    exact ⟨fun h ↦ h.continuousAt (printed_trig_domain_open.mem_nhds hx),
      fun h ↦ h.continuousWithinAt⟩
  rw [hbridge]
  by_cases hs : Real.sin x = 1
  · have hx0 : x ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have hl : Tendsto (trigonometricSequenceLimit a) (𝓝[≠] x) (𝓝 x) := by
      apply (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [sine_maximum_punctured_ne x hs] with y hy
      simp [trigonometricSequenceLimit, hy]
    have hden : 1+a ≠ 0 := by intro h; apply ha; linarith
    constructor
    · intro hc
      have he : x / (1+a) = x := by
        simpa [trigonometricSequenceLimit, hs] using
          tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hl
      have hm := (div_eq_iff hden).mp he
      exact Or.inl (by apply (mul_eq_zero.mp (show x*a=0 by nlinarith [hm])).resolve_left hx0)
    · rintro (rfl | h)
      · have he : trigonometricSequenceLimit 0 = id := by
          funext y
          unfold trigonometricSequenceLimit
          split_ifs <;> simp
        rw [he]
        exact continuousAt_id
      · exact (h hs).elim
  · have he : trigonometricSequenceLimit a =ᶠ[𝓝 x] (fun y : ℝ ↦ y) := by
      filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hs] with y hy
      simp [trigonometricSequenceLimit, hy]
    exact ⟨fun _ ↦ Or.inr hs, fun _ ↦ continuousAt_id.congr_of_eventuallyEq he⟩

/-- Bài tập 3(a): giới hạn và tính gián đoạn tại π/2 khi a=1. -/
theorem exercise03_at_pi_div_two :
    (∀ x ∈ printedTrigSequenceDomain,
      ConvergesTo (trigonometricSequenceTerm 1 x) (trigonometricSequenceLimit 1 x)) ∧
    trigonometricSequenceLimit 1 (Real.pi/2) = Real.pi/4 ∧
    NotDomainContinuousAt printedTrigSequenceDomain (trigonometricSequenceLimit 1) (Real.pi/2) := by
  have hx : Real.pi/2 ∈ printedTrigSequenceDomain :=
    (printed_trig_domain_iff _).mpr (by rw [Real.sin_pi_div_two]; norm_num)
  refine ⟨fun x hx ↦ (trigonometric_sequence_converges 1 x (by norm_num) hx).2, ?_, ?_⟩
  · simp only [trigonometricSequenceLimit, Real.sin_pi_div_two, if_true]; ring
  · intro hc
    have h := (trigonometric_sequence_continuity 1 (Real.pi/2) (by norm_num) hx).mp hc
    simp [Real.sin_pi_div_two] at h

/-- Bài tập 3(b): miền tham số và các điểm liên tục. -/
theorem exercise03_continuity_classification (a : ℝ) (ha : a ≠ -1) :
    ∀ x ∈ printedTrigSequenceDomain,
      ((∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 1+a*Real.sin x^n ≠ 0) ∧
        ConvergesTo (trigonometricSequenceTerm a x) (trigonometricSequenceLimit a x)) ∧
      (DomainContinuousAt printedTrigSequenceDomain (trigonometricSequenceLimit a) x ↔
        a=0 ∨ Real.sin x≠1) := by
  intro x hx
  exact ⟨trigonometric_sequence_converges a x ha hx,
    trigonometric_sequence_continuity a x ha hx⟩

end calculus.Chapter03.Section06TrigonometricSequenceExercises
