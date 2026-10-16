import calculus.Chapter03.Section04
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Bài tập 3.6.4(b): giới hạn dãy logarit trên miền x>−e. -/
namespace calculus.Chapter03.Section06LogarithmicSequenceExercises
open Set Filter Topology
open calculus.Chapter02.Section03 calculus.Chapter03.Section04

def LogarithmicSequenceTermsDefined (x : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → 0 < (Real.exp 1)^n+x^n

noncomputable def logarithmicSequenceTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.log ((Real.exp 1)^n+x^n)/(n : ℝ)

noncomputable def logarithmicSequenceLimit (x : ℝ) : ℝ :=
  Real.log (max (Real.exp 1) x)

theorem logarithmic_sequence_natural_domain (x : ℝ) :
    LogarithmicSequenceTermsDefined x ↔ -Real.exp 1 < x := by
  constructor
  · intro h
    have h1 := h 1 (by omega)
    norm_num at h1
    linarith
  · intro hx n hn
    have he : 0 < (Real.exp 1)^n := pow_pos (Real.exp_pos 1) n
    by_cases hx0 : 0 ≤ x
    · exact add_pos_of_pos_of_nonneg he (pow_nonneg hx0 n)
    · have hneg : x < 0 := lt_of_not_ge hx0
      have habs : |x| < Real.exp 1 := by rw [abs_of_neg hneg]; linarith
      have hpow : |x|^n < (Real.exp 1)^n :=
        pow_lt_pow_left₀ habs (abs_nonneg x) (by omega)
      have hbound : -|x|^n ≤ x^n := by
        simpa only [abs_pow] using neg_abs_le (x^n)
      linarith


theorem logarithmic_sequence_eventual_domain (x : ℝ) :
    (∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 0 < (Real.exp 1)^n+x^n) ↔ -Real.exp 1 < x := by
  constructor
  · intro h
    by_contra hx
    have hxe : Real.exp 1 ≤ -x := by linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    let n := 2*N+1
    have hnN : N ≤ n := by dsimp [n]; omega
    have hodd : Odd n := ⟨N, rfl⟩
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le hxe n
    have hv : x^n = -((-x)^n) := by
      simpa only [neg_neg] using hodd.neg_pow (-x)
    have hh := (hN n hnN).2
    rw [hv] at hh
    linarith
  · intro hx
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ⟨hn, (logarithmic_sequence_natural_domain x).mpr hx n hn⟩

theorem logarithmic_factored_power_limit (b c : ℝ) (hb : 0 < b) (hr : |c/b| < 1) :
    Tendsto (fun n : ℕ ↦ Real.log (b^n+c^n)/(n : ℝ)) atTop (𝓝 (Real.log b)) := by
  have hp : Tendsto (fun n : ℕ ↦ (c/b)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr hr
  have hi : Tendsto (fun n : ℕ ↦ 1+(c/b)^n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hp
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (1+(c/b)^n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.log_one] using hi.log (by norm_num : (1 : ℝ) ≠ 0)
  have hni : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).inv_tendsto_atTop
  have herr := hlog.mul hni
  have ht : Tendsto (fun n : ℕ ↦ Real.log b+Real.log (1+(c/b)^n)/(n : ℝ))
      atTop (𝓝 (Real.log b)) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using tendsto_const_nhds.add herr
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1, hi.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)]
      with n hn hinc
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hf : b^n+c^n = b^n*(1+(c/b)^n) := by
    rw [mul_add, mul_one, ← mul_pow]
    have hbc : b*(c/b)=c := by field_simp [hb.ne']
    rw [hbc]
  rw [hf, Real.log_mul (pow_ne_zero n hb.ne') hinc, Real.log_pow]
  field_simp [hnn]

theorem logarithmic_sequence_converges (x : ℝ) (hx : -Real.exp 1 < x) :
    ConvergesTo (logarithmicSequenceTerm x) (logarithmicSequenceLimit x) := by
  apply convergesTo_iff_tendsto.mpr
  change Tendsto (fun n : ℕ ↦ Real.log ((Real.exp 1)^n+x^n)/(n : ℝ))
    atTop (𝓝 (logarithmicSequenceLimit x))
  rcases lt_trichotomy x (Real.exp 1) with hxe | rfl | hex
  · have hr : |x / Real.exp 1| < 1 := by
      rw [abs_div, abs_of_pos (Real.exp_pos 1), div_lt_one (Real.exp_pos 1)]
      exact abs_lt.mpr ⟨by linarith, hxe⟩
    simpa only [logarithmicSequenceLimit, max_eq_left hxe.le,
      Real.log_exp] using logarithmic_factored_power_limit (Real.exp 1) x (Real.exp_pos 1) hr
  · have hni : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).inv_tendsto_atTop
    have ht : Tendsto (fun n : ℕ ↦ (1 : ℝ)+Real.log 2/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [div_eq_mul_inv, mul_zero, add_zero] using
        tendsto_const_nhds.add (hni.const_mul (Real.log 2))
    have ht' : Tendsto (fun n : ℕ ↦ logarithmicSequenceTerm (Real.exp 1) n) atTop (𝓝 (1 : ℝ)) := by
      apply ht.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [logarithmicSequenceTerm, show (Real.exp 1)^n+(Real.exp 1)^n =
        2*(Real.exp 1)^n by ring, Real.log_mul (by norm_num) (pow_ne_zero _ (Real.exp_ne_zero _)),
        Real.log_pow, Real.log_exp]
      field_simp [hnn]
      ring
    simpa [logarithmicSequenceTerm, logarithmicSequenceLimit, Real.log_exp] using! ht'
  · have hxpos : 0 < x := (Real.exp_pos 1).trans hex
    have hr : |Real.exp 1/x| < 1 := by
      rw [abs_of_pos (div_pos (Real.exp_pos 1) hxpos)]
      exact (div_lt_one hxpos).mpr hex
    simpa only [logarithmicSequenceLimit, max_eq_right hex.le,
      add_comm] using logarithmic_factored_power_limit x (Real.exp 1) hxpos hr

theorem logarithmic_sequence_limit_continuous : Continuous logarithmicSequenceLimit := by
  apply (continuous_const.max continuous_id).log
  intro x
  exact (lt_of_lt_of_le (Real.exp_pos 1) (le_max_left _ _)).ne'

theorem logarithmic_sequence_limit_cases (x : ℝ) :
    logarithmicSequenceLimit x = if x ≤ Real.exp 1 then 1 else Real.log x := by
  by_cases hx : x ≤ Real.exp 1
  · simp only [logarithmicSequenceLimit, max_eq_left hx, Real.log_exp, if_pos hx]
  · simp only [logarithmicSequenceLimit, max_eq_right (le_of_not_ge hx), if_neg hx]

/-- Bài tập 4(b): miền xác định, giới hạn dãy và các điểm liên tục. -/
theorem exercise04_logarithmic_sequence_classification :
    (∀ x : ℝ, LogarithmicSequenceTermsDefined x ↔ -Real.exp 1 < x) ∧
    (∀ x : ℝ, (∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 0 < (Real.exp 1)^n+x^n) ↔
      -Real.exp 1 < x) ∧
    (∀ x ∈ Ioi (-Real.exp 1),
      ConvergesTo (logarithmicSequenceTerm x) (logarithmicSequenceLimit x)) ∧
    DomainContinuousOn (Ioi (-Real.exp 1)) logarithmicSequenceLimit := by
  exact ⟨logarithmic_sequence_natural_domain, logarithmic_sequence_eventual_domain,
    fun x hx ↦ logarithmic_sequence_converges x hx,
    fun x hx ↦ (domainContinuousAt_iff_within hx).mpr
      logarithmic_sequence_limit_continuous.continuousAt.continuousWithinAt⟩

end calculus.Chapter03.Section06LogarithmicSequenceExercises
