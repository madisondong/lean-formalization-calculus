import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Taylor và tiêu chuẩn cực trị theo đạo hàm cấp cao

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1781–1804, Định lí 4.4.12. Với `n ≥ 1`, giả sử `f(x₀) = 0` và các đạo hàm cấp `1 ≤ k < n` tại `x₀` bằng 0.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04HigherExtremumTests
open Set Filter calculus.Chapter04.Section01Higher
open scoped Topology ContDiff


theorem taylor_polynomial_single_coefficient {f : ℝ → ℝ} {a b x₀ : ℝ} (n : ℕ)
    (hx₀ : x₀ ∈ Ioo a b) (hz : ∀ k : ℕ, k < n → iteratedDeriv k f x₀ = 0) (x : ℝ) :
    taylorWithinEval f n (Ioo a b) x₀ x =
      (iteratedDeriv n f x₀ / (n.factorial : ℝ)) * (x - x₀) ^ n := by
  rw [taylor_within_apply]
  simp only [smul_eq_mul]
  rw [Finset.sum_eq_single n]
  · rw [iteratedDerivWithin_of_isOpen isOpen_Ioo hx₀]
    ring
  · intro k hk hkn
    have hl : k < n := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hkn
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioo hx₀, hz k hl, mul_zero]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim


theorem source_higher_leading_quotient_limit {f : ℝ → ℝ} {a b x₀ : ℝ} (n : ℕ)
    (hf : DomainC n f (Ioo a b)) (hx₀ : x₀ ∈ Ioo a b)
    (hz : ∀ k : ℕ, k < n → iteratedDeriv k f x₀ = 0) :
    Tendsto (fun x : ℝ ↦ f x / (x - x₀) ^ n) (𝓝[≠] x₀)
      (𝓝 (iteratedDeriv n f x₀ / (n.factorial : ℝ))) := by
  have ht := Real.taylor_tendsto (convex_Ioo a b) hx₀
    ((domainC_iff_contDiffOn n f isOpen_Ioo).mp hf)
  rw [nhdsWithin_eq_nhds.mpr (isOpen_Ioo.mem_nhds hx₀)] at ht
  have hp := (ht.mono_left
    (show 𝓝[≠] x₀ ≤ 𝓝 x₀ from nhdsWithin_le_nhds)).add_const
    (iteratedDeriv n f x₀ / (n.factorial : ℝ))
  simp only [zero_add] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [taylor_polynomial_single_coefficient n hx₀ hz]
  have hne : x - x₀ ≠ 0 := sub_ne_zero.mpr (show x ≠ x₀ from hx)
  field_simp [hne]
  ring


theorem higher_even_positive_local_min {f : ℝ → ℝ} {a b x₀ : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (hf : DomainC n f (Ioo a b)) (hx₀ : x₀ ∈ Ioo a b)
    (hz : ∀ k : ℕ, k < n → iteratedDeriv k f x₀ = 0)
    (_hne : iteratedDeriv n f x₀ ≠ 0) (he : Even n) (hp : 0 < iteratedDeriv n f x₀) :
    IsLocalMin f x₀ := by
  have hzero : f x₀ = 0 := by simpa only [iteratedDeriv_zero] using hz 0 (by omega)
  have hc : 0 < iteratedDeriv n f x₀ / (n.factorial : ℝ) := div_pos hp (by positivity)
  have hlim := source_higher_leading_quotient_limit n hf hx₀ hz
  have hq := hlim.eventually (eventually_gt_nhds hc)
  change ∀ᶠ x in 𝓝 x₀, f x₀ ≤ f x
  rw [← nhdsNE_sup_pure x₀, eventually_sup]
  refine ⟨?_, by simp⟩
  filter_upwards [hq, self_mem_nhdsWithin] with x hx hneq
  have hpow : 0 < (x - x₀) ^ n := he.pow_pos (sub_ne_zero.mpr (show x ≠ x₀ from hneq))
  rw [hzero]
  exact ((div_pos_iff_of_pos_right hpow).mp hx).le


theorem higher_even_negative_local_max {f : ℝ → ℝ} {a b x₀ : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (hf : DomainC n f (Ioo a b)) (hx₀ : x₀ ∈ Ioo a b)
    (hz : ∀ k : ℕ, k < n → iteratedDeriv k f x₀ = 0)
    (_hne : iteratedDeriv n f x₀ ≠ 0) (he : Even n) (hp : iteratedDeriv n f x₀ < 0) :
    IsLocalMax f x₀ := by
  have hzero : f x₀ = 0 := by simpa only [iteratedDeriv_zero] using hz 0 (by omega)
  have hc : iteratedDeriv n f x₀ / (n.factorial : ℝ) < 0 := div_neg_of_neg_of_pos hp (by positivity)
  have hlim := source_higher_leading_quotient_limit n hf hx₀ hz
  have hq := hlim.eventually (eventually_lt_nhds hc)
  change ∀ᶠ x in 𝓝 x₀, f x ≤ f x₀
  rw [← nhdsNE_sup_pure x₀, eventually_sup]
  refine ⟨?_, by simp⟩
  filter_upwards [hq, self_mem_nhdsWithin] with x hx hneq
  have hpow : 0 < (x - x₀) ^ n := he.pow_pos (sub_ne_zero.mpr (show x ≠ x₀ from hneq))
  have heq : f x = (f x / (x - x₀) ^ n) * (x - x₀) ^ n :=
    (div_mul_cancel₀ _ hpow.ne').symm
  rw [hzero, heq]
  exact (mul_neg_of_neg_of_pos hx hpow).le


theorem odd_positive_quotient_side_signs {f : ℝ → ℝ} {x₀ : ℝ} (n : ℕ) (ho : Odd n)
    (hq : ∀ᶠ x in 𝓝[≠] x₀, 0 < f x / (x - x₀) ^ n) :
    (∀ᶠ x in 𝓝[<] x₀, f x < 0) ∧ (∀ᶠ x in 𝓝[>] x₀, 0 < f x) := by
  constructor
  · filter_upwards [hq.filter_mono (nhdsLT_le_nhdsNE x₀), self_mem_nhdsWithin] with x hx hside
    have hpow : (x - x₀) ^ n < 0 := ho.pow_neg_iff.mpr (sub_neg.mpr hside)
    have heq : f x = (f x / (x - x₀) ^ n) * (x - x₀) ^ n :=
      (div_mul_cancel₀ _ hpow.ne).symm
    rw [heq]
    exact mul_neg_of_pos_of_neg hx hpow
  · filter_upwards [hq.filter_mono (nhdsGT_le_nhdsNE x₀), self_mem_nhdsWithin] with x hx hside
    have hpow : 0 < (x - x₀) ^ n := ho.pow_pos_iff.mpr (sub_pos.mpr hside)
    exact (div_pos_iff_of_pos_right hpow).mp hx


theorem odd_negative_quotient_side_signs {f : ℝ → ℝ} {x₀ : ℝ} (n : ℕ) (ho : Odd n)
    (hq : ∀ᶠ x in 𝓝[≠] x₀, f x / (x - x₀) ^ n < 0) :
    (∀ᶠ x in 𝓝[<] x₀, 0 < f x) ∧ (∀ᶠ x in 𝓝[>] x₀, f x < 0) := by
  constructor
  · filter_upwards [hq.filter_mono (nhdsLT_le_nhdsNE x₀), self_mem_nhdsWithin] with x hx hside
    have hpow : (x - x₀) ^ n < 0 := ho.pow_neg_iff.mpr (sub_neg.mpr hside)
    have heq : f x = (f x / (x - x₀) ^ n) * (x - x₀) ^ n :=
      (div_mul_cancel₀ _ hpow.ne).symm
    rw [heq]
    exact mul_pos_of_neg_of_neg hx hpow
  · filter_upwards [hq.filter_mono (nhdsGT_le_nhdsNE x₀), self_mem_nhdsWithin] with x hx hside
    have hpow : 0 < (x - x₀) ^ n := ho.pow_pos_iff.mpr (sub_pos.mpr hside)
    have heq : f x = (f x / (x - x₀) ^ n) * (x - x₀) ^ n :=
      (div_mul_cancel₀ _ hpow.ne').symm
    rw [heq]
    exact mul_neg_of_neg_of_pos hx hpow

/-- Định lí 4.4.12(iii): cấp `n` lẻ, kể cả `n = 1`, với `f(x₀) = 0`. -/
theorem higher_odd_no_local_extremum {f : ℝ → ℝ} {a b x₀ : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (hf : DomainC n f (Ioo a b)) (hx₀ : x₀ ∈ Ioo a b)
    (hz : ∀ k : ℕ, k < n → iteratedDeriv k f x₀ = 0)
    (hne : iteratedDeriv n f x₀ ≠ 0) (ho : Odd n) : ¬ IsLocalExtr f x₀ := by
  have hzero : f x₀ = 0 := by simpa only [iteratedDeriv_zero] using hz 0 (by omega)
  have hC : iteratedDeriv n f x₀ / (n.factorial : ℝ) ≠ 0 := div_ne_zero hne (by positivity)
  have hlim := source_higher_leading_quotient_limit n hf hx₀ hz
  rcases lt_or_gt_of_ne hC with hc | hc
  · have hs := odd_negative_quotient_side_signs n ho
      (hlim.eventually (eventually_lt_nhds hc))
    rintro (hm | hm)
    · change ∀ᶠ x in 𝓝 x₀, f x₀ ≤ f x at hm
      obtain ⟨x, hx, hneg⟩ := (hm.filter_mono nhdsWithin_le_nhds).and hs.2 |>.exists
      rw [hzero] at hx
      exact hneg.not_ge hx
    · change ∀ᶠ x in 𝓝 x₀, f x ≤ f x₀ at hm
      obtain ⟨x, hx, hpos⟩ := (hm.filter_mono nhdsWithin_le_nhds).and hs.1 |>.exists
      rw [hzero] at hx
      exact hpos.not_ge hx
  · have hs := odd_positive_quotient_side_signs n ho
      (hlim.eventually (eventually_gt_nhds hc))
    rintro (hm | hm)
    · change ∀ᶠ x in 𝓝 x₀, f x₀ ≤ f x at hm
      obtain ⟨x, hx, hneg⟩ := (hm.filter_mono nhdsWithin_le_nhds).and hs.1 |>.exists
      rw [hzero] at hx
      exact hneg.not_ge hx
    · change ∀ᶠ x in 𝓝 x₀, f x ≤ f x₀ at hm
      obtain ⟨x, hx, hpos⟩ := (hm.filter_mono nhdsWithin_le_nhds).and hs.2 |>.exists
      rw [hzero] at hx
      exact hpos.not_ge hx

end calculus.Chapter04.Section04HigherExtremumTests
