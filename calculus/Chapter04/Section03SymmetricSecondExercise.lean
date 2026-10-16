import calculus.Chapter04.Section01Higher
import calculus.Chapter04.Section04
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bài 33: sai phân đối xứng bậc hai

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1384–1387, Bài 4.3.33. Hàm chỉ cần khả vi hai lần trên khoảng mở; giới hạn xét trên lân cận thủng của 0.
-/
namespace calculus.Chapter04.Section03SymmetricSecondExercise
open Set Filter calculus.Chapter04.Section01Higher
open scoped Topology


theorem symmetric_second_quotient_limit_of_eventually_differentiable
    {f : ℝ → ℝ} {x : ℝ}
    (hf : ∀ᶠ u in 𝓝 x, DifferentiableAt ℝ f u)
    (hdf : DifferentiableAt ℝ (deriv f) x) :
    Tendsto (fun h : ℝ ↦ (f (x + h) + f (x - h) - 2 * f x) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (deriv (deriv f) x)) := by
  have hplus (h : ℝ) : HasDerivAt (fun u : ℝ ↦ x + u) 1 h := by
    simpa only [zero_add, id_eq] using (hasDerivAt_const h x).fun_add (hasDerivAt_id h)
  have hminus (h : ℝ) : HasDerivAt (fun u : ℝ ↦ x - u) (-1) h := by
    simpa only [zero_sub, id_eq] using (hasDerivAt_const h x).fun_sub (hasDerivAt_id h)
  have hplus_limit : Tendsto (fun h : ℝ ↦ x + h) (𝓝 0) (𝓝 x) := by
    simpa only [add_zero] using (hplus 0).continuousAt.tendsto
  have hminus_limit : Tendsto (fun h : ℝ ↦ x - h) (𝓝 0) (𝓝 x) := by
    simpa only [sub_zero] using (hminus 0).continuousAt.tendsto
  have hfp : ∀ᶠ h in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (x + h) := by
    exact hplus_limit.eventually hf
  have hfm : ∀ᶠ h in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (x - h) := by
    exact hminus_limit.eventually hf
  have hdf_plus : HasDerivAt (deriv f) (deriv (deriv f) x) (x + 0) := by
    simpa only [add_zero] using hdf.hasDerivAt
  have hdf_minus : HasDerivAt (deriv f) (deriv (deriv f) x) (x - 0) := by
    simpa only [sub_zero] using hdf.hasDerivAt
  have hp : HasDerivAt (fun h : ℝ ↦ deriv f (x + h)) (deriv (deriv f) x) 0 := by
    simpa only [add_zero, mul_one, Function.comp_def] using
      hdf_plus.comp 0 (hplus 0)
  have hm : HasDerivAt (fun h : ℝ ↦ deriv f (x - h)) (-(deriv (deriv f) x)) 0 := by
    simpa only [sub_zero, mul_neg_one, Function.comp_def] using
      hdf_minus.comp 0 (hminus 0)
  have hp_limit : Tendsto
      (fun h : ℝ ↦ (deriv f (x + h) - deriv f x) / h)
      (𝓝[≠] 0) (𝓝 (deriv (deriv f) x)) := by
    simpa only [zero_add, add_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hp.tendsto_slope_zero
  have hm_limit : Tendsto
      (fun h : ℝ ↦ (deriv f (x - h) - deriv f x) / h)
      (𝓝[≠] 0) (𝓝 (-(deriv (deriv f) x))) := by
    simpa only [zero_add, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hm.tendsto_slope_zero
  have hquot : Tendsto
      (fun h : ℝ ↦ (deriv f (x + h) - deriv f (x - h)) / (2 * h))
      (𝓝[≠] 0) (𝓝 (deriv (deriv f) x)) := by
    have ht := (hp_limit.sub hm_limit).div_const 2
    have hd : (deriv (deriv f) x - -(deriv (deriv f) x)) / 2 =
        deriv (deriv f) x := by ring
    rw [hd] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    field_simp [hne]
    ring
  have hn : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ f (x + u) + f (x - u) - 2 * f x)
        (deriv f (x + h) - deriv f (x - h)) h := by
    filter_upwards [hfp.filter_mono nhdsWithin_le_nhds,
      hfm.filter_mono nhdsWithin_le_nhds] with h hph hmh
    have ha : HasDerivAt (fun u : ℝ ↦ f (x + u)) (deriv f (x + h)) h := by
      simpa only [mul_one, Function.comp_def] using hph.hasDerivAt.comp h (hplus h)
    have hb : HasDerivAt (fun u : ℝ ↦ f (x - u)) (-(deriv f (x - h))) h := by
      simpa only [mul_neg_one, Function.comp_def] using hmh.hasDerivAt.comp h (hminus h)
    simpa only [sub_eq_add_neg] using (ha.fun_add hb).sub_const (2 * f x)
  have hsquare (h : ℝ) : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * h) h := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq] using
      (hasDerivAt_id h).fun_pow 2
  have hden : ∀ᶠ h in 𝓝[≠] (0 : ℝ), (2 : ℝ) * h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_ne_zero (by norm_num) (show h ≠ 0 from hh)
  have hzero : f x + f x - 2 * f x = 0 := by ring
  have hn_limit : Tendsto (fun h : ℝ ↦ f (x + h) + f (x - h) - 2 * f x)
      (𝓝[≠] 0) (𝓝 0) := by
    have hc := ((hf.self_of_nhds.continuousAt.tendsto.comp hplus_limit).add
      (hf.self_of_nhds.continuousAt.tendsto.comp hminus_limit)).sub
        (tendsto_const_nhds (x := 2 * f x))
    simpa only [Function.comp_def, hzero] using
      hc.mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hg_limit : Tendsto (fun h : ℝ ↦ h ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hsquare 0).continuousAt.tendsto.mono_left
        (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  exact calculus.Chapter04.Section04.lhopital_zero_punctured hn
    (Filter.Eventually.of_forall hsquare) hden hn_limit hg_limit hquot


theorem symmetric_second_quotient_limit {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f)) (x : ℝ) :
    Tendsto (fun h : ℝ ↦ (f (x + h) + f (x - h) - 2 * f x) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (deriv (deriv f) x)) :=
  symmetric_second_quotient_limit_of_eventually_differentiable
    (Filter.Eventually.of_forall hf) (hdf x)

/-- Bài 33 tại mọi điểm trong khoảng mở, dưới giả thiết khả vi hai lần. -/
theorem source_symmetric_second_quotient_limit {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DifferentiableToOrderOn 2 f (Ioo a b)) (hx : x ∈ Ioo a b) :
    Tendsto (fun h : ℝ ↦ (f (x + h) + f (x - h) - 2 * f x) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (deriv (deriv f) x)) := by
  obtain ⟨hfirst, hsecond⟩ := (differentiableToOrderOn_two f isOpen_Ioo).mp hf
  have hlocal : ∀ᶠ u in 𝓝 x, DifferentiableAt ℝ f u := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu
    exact (hfirst u hu).differentiableAt (isOpen_Ioo.mem_nhds hu)
  exact symmetric_second_quotient_limit_of_eventually_differentiable hlocal
    ((hsecond x hx).differentiableAt (isOpen_Ioo.mem_nhds hx))

end calculus.Chapter04.Section03SymmetricSecondExercise
