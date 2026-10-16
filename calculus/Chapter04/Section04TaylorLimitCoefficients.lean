import calculus.Chapter03.Section02
import calculus.Chapter03.Section03
import calculus.Chapter03.Section02Infinite
import calculus.Chapter04.Section03TaylorElementary
import calculus.Chapter04.Section03TrigonometricMaclaurin
import calculus.Chapter04.Section03ReciprocalLogMaclaurin
import calculus.Chapter04.Section01HigherArctangentExercise
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 4: hệ số Taylor và giới hạn phần dư

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1700–1718.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Finset
open scoped BigOperators
namespace calculus.Chapter04.Section04TaylorLimitCoefficients
open calculus.Chapter03.Section02 calculus.Chapter03.Section03
open calculus.Chapter03.Section02Infinite
open calculus.Chapter04.Section03TaylorElementary
open calculus.Chapter04.Section03TrigonometricMaclaurin
open calculus.Chapter04.Section03ReciprocalLogMaclaurin
open calculus.Chapter04.Section01HigherArctangentExercise

theorem source_limit_of_eventual_natural_domain {D : Set ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hD : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x ∈ D)
    (hf : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 L)) : DomainLimit D f 0 L := by
  have hfilter : 𝓝[D \ {(0 : ℝ)}] 0 = 𝓝[≠] (0 : ℝ) := by
    simpa only [sdiff_eq, Set.ofPred_mem_eq] using nhdsWithin_inter_of_mem hD
  have hacc : AccumulationPointOf D 0 := accumulationPointOf_iff_neBot.mpr (by
    rw [hfilter]
    infer_instance)
  apply (domainLimit_iff_tendsto hacc).mpr
  rw [hfilter]
  exact hf

/-- Bài 4: với hàm `Cⁿ` gần 0, phần dư Taylor là `o(xⁿ)` khi `x → 0`. -/
theorem taylor_remainder_quotient_at_zero {f : ℝ → ℝ} (n : ℕ) {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (hf : ContDiffOn ℝ n f (Ioo a b)) :
    Tendsto (fun x : ℝ ↦
      (f x - (∑ k ∈ range (n + 1),
        iteratedDeriv k f 0 / (k.factorial : ℝ) * x ^ k)) / x ^ n)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hcenter : (0 : ℝ) ∈ Ioo a b := ⟨ha, hb⟩
  have hdiff : ContDiffAt ℝ n f 0 := hf.contDiffAt (Ioo_mem_nhds ha hb)
  have hpoly (x : ℝ) : taylorWithinEval f n (Ioo a b) 0 x =
      ∑ k ∈ range (n + 1), iteratedDeriv k f 0 / (k.factorial : ℝ) * x ^ k := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b)
      (hdiff.of_le (by exact_mod_cast hkn)) hcenter]
    simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have ht := Real.taylor_tendsto (convex_Ioo a b) hcenter hf
  simp_rw [hpoly, sub_zero] at ht
  rw [nhdsWithin_eq_nhds.mpr (Ioo_mem_nhds ha hb)] at ht
  exact ht.mono_left nhdsWithin_le_nhds

theorem sine_taylor_remainder_three :
    Tendsto (fun x : ℝ ↦ (Real.sin x - (x - x ^ 3 / 6)) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have ht := taylor_remainder_quotient_at_zero 3 (a := -1) (b := 1)
    (by norm_num) (by norm_num) Real.contDiff_sin.contDiffOn
  have hp (x : ℝ) :
      (∑ k ∈ range 4, iteratedDeriv k Real.sin 0 / (k.factorial : ℝ) * x ^ k) =
        x - x ^ 3 / 6 := by
    rw [sine_taylor_polynomial_odd 2 x]
    norm_num [sum_range_succ, Nat.factorial]
    ring
  simpa only [hp] using ht

theorem sine_taylor_remainder_five :
    Tendsto (fun x : ℝ ↦
      (Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)) / x ^ 5)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have ht := taylor_remainder_quotient_at_zero 5 (a := -1) (b := 1)
    (by norm_num) (by norm_num) Real.contDiff_sin.contDiffOn
  have hp (x : ℝ) :
      (∑ k ∈ range 6, iteratedDeriv k Real.sin 0 / (k.factorial : ℝ) * x ^ k) =
        x - x ^ 3 / 6 + x ^ 5 / 120 := by
    rw [sine_taylor_polynomial_odd 3 x]
    norm_num [sum_range_succ, Nat.factorial]
    ring
  simpa only [hp] using ht

theorem cosine_taylor_remainder_two :
    Tendsto (fun x : ℝ ↦ (Real.cos x - (1 - x ^ 2 / 2)) / x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have ht := taylor_remainder_quotient_at_zero 2 (a := -1) (b := 1)
    (by norm_num) (by norm_num) Real.contDiff_cos.contDiffOn
  have hp (x : ℝ) :
      (∑ k ∈ range 3, iteratedDeriv k Real.cos 0 / (k.factorial : ℝ) * x ^ k) =
        1 - x ^ 2 / 2 := by
    rw [cosine_taylor_polynomial_even 1 x]
    norm_num [sum_range_succ, Nat.factorial]
    ring
  simpa only [hp] using ht

theorem cosine_taylor_remainder_four :
    Tendsto (fun x : ℝ ↦
      (Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)) / x ^ 4)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have ht := taylor_remainder_quotient_at_zero 4 (a := -1) (b := 1)
    (by norm_num) (by norm_num) Real.contDiff_cos.contDiffOn
  have hp (x : ℝ) :
      (∑ k ∈ range 5, iteratedDeriv k Real.cos 0 / (k.factorial : ℝ) * x ^ k) =
        1 - x ^ 2 / 2 + x ^ 4 / 24 := by
    rw [cosine_taylor_polynomial_even 2 x]
    norm_num [sum_range_succ, Nat.factorial]
    ring
  simpa only [hp] using ht

theorem exponential_taylor_remainder_three :
    Tendsto (fun x : ℝ ↦
      (Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have ht := taylor_remainder_quotient_at_zero 3 (a := -1) (b := 1)
    (by norm_num) (by norm_num) Real.contDiff_exp.contDiffOn
  have hp (x : ℝ) :
      (∑ k ∈ range 4, iteratedDeriv k Real.exp 0 / (k.factorial : ℝ) * x ^ k) =
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    simp_rw [iteratedDeriv_exponential]
    norm_num [sum_range_succ, Nat.factorial]
    ring
  simpa only [hp] using ht

theorem logarithm_taylor_remainder_two :
    Tendsto (fun x : ℝ ↦ (Real.log (1 + x) - (x - x ^ 2 / 2)) / x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hf : ContDiffOn ℝ 2 logOneAdd (Ioo (-1 / 2 : ℝ) (1 / 2)) := by
    intro x hx
    exact (logOneAdd_contDiffAt 2 x (by linarith [hx.1])).contDiffWithinAt
  have ht := taylor_remainder_quotient_at_zero 2 (by norm_num) (by norm_num) hf
  have h₁ : iteratedDeriv 1 logOneAdd 0 / ((1 : ℕ).factorial : ℝ) = 1 := by
    simpa using logOneAdd_derivative_coefficient 0
  have h₂ : iteratedDeriv 2 logOneAdd 0 / ((2 : ℕ).factorial : ℝ) = -1 / 2 := by
    simpa using logOneAdd_derivative_coefficient 1
  have hp (x : ℝ) :
      (∑ k ∈ range 3, iteratedDeriv k logOneAdd 0 / (k.factorial : ℝ) * x ^ k) =
        x - x ^ 2 / 2 := by
    simp only [sum_range_succ, sum_range_zero, iteratedDeriv_zero, h₁, h₂]
    norm_num [logOneAdd]
    ring
  simpa only [hp, logOneAdd] using ht

theorem arctangent_taylor_remainder_three :
    Tendsto (fun x : ℝ ↦ (Real.arctan x - (x - x ^ 3 / 3)) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have ht := taylor_remainder_quotient_at_zero 3 (a := -1) (b := 1)
    (by norm_num) (by norm_num) Real.contDiff_arctan.contDiffOn
  have h₀ : iteratedDeriv 0 Real.arctan 0 = 0 := by simp
  have h₁ : iteratedDeriv 1 Real.arctan 0 = 1 := by
    simp
  have h₂ : iteratedDeriv 2 Real.arctan 0 = 0 := by
    simpa using arctangent_even_derivative 1
  have h₃ : iteratedDeriv 3 Real.arctan 0 = -2 := by
    simpa using arctangent_odd_derivative 1
  have hp (x : ℝ) :
      (∑ k ∈ range 4, iteratedDeriv k Real.arctan 0 / (k.factorial : ℝ) * x ^ k) =
        x - x ^ 3 / 3 := by
    norm_num [sum_range_succ, h₀, h₁, h₂, h₃, Nat.factorial]
    ring
  simpa only [hp] using ht

theorem sine_linear_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  simpa only [slope_fun_def_field, sub_zero, Real.sin_zero, Real.cos_zero] using!
    (Real.hasDerivAt_sin 0).tendsto_slope

theorem logarithm_linear_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ Real.log (1 + x) / x) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hd : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)
  simpa only [slope_fun_def_field, sub_zero, add_zero, Real.log_one] using! hd.tendsto_slope

theorem sine_cubic_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.sin x - x) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 / 6 : ℝ)) := by
  have ht := sine_taylor_remainder_three.add_const (-1 / 6 : ℝ)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

theorem sine_fifth_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.sin x - x + x ^ 3 / 6) / x ^ 5)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 120 : ℝ)) := by
  have ht := sine_taylor_remainder_five.add_const (1 / 120 : ℝ)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

theorem cosine_quadratic_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have ht := cosine_taylor_remainder_two.neg.add_const (1 / 2 : ℝ)
  simp only [neg_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

theorem cosine_fourth_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.cos x - 1 + x ^ 2 / 2) / x ^ 4)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 24 : ℝ)) := by
  have ht := cosine_taylor_remainder_four.add_const (1 / 24 : ℝ)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

theorem exponential_cubic_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.exp x - 1 - x - x ^ 2 / 2) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 6 : ℝ)) := by
  have ht := exponential_taylor_remainder_three.add_const (1 / 6 : ℝ)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

theorem logarithm_quadratic_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.log (1 + x) - x) / x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ)) := by
  have ht := logarithm_taylor_remainder_two.add_const (-1 / 2 : ℝ)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

theorem arctangent_cubic_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.arctan x - x) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 / 3 : ℝ)) := by
  have ht := arctangent_taylor_remainder_three.add_const (-1 / 3 : ℝ)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

theorem arcsine_cubic_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.arcsin x - x) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 6 : ℝ)) := by
  have hd : HasDerivAt Real.arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (x := (0 : ℝ)) (by norm_num) (by norm_num)
  have hlinear : Tendsto (fun x : ℝ ↦ Real.arcsin x / x)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [slope_fun_def_field, sub_zero, Real.arcsin_zero] using! hd.tendsto_slope
  have harg : Tendsto Real.arcsin (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.arcsin_zero] using hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      simpa only [mem_compl_iff, mem_singleton_iff, Real.arcsin_eq_zero_iff] using hx0
  have ht := (sine_cubic_quotient_tendsto.comp harg).neg.mul (hlinear.pow 3)
  norm_num only [neg_div, neg_neg, one_pow, mul_one] at ht
  apply ht.congr'
  have hinside : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), x ∈ Ioo (-1 : ℝ) 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin,
    hinside] with x hx hinside
  have hx0 : x ≠ 0 := by simpa using hx
  have hax : Real.arcsin x ≠ 0 := mt Real.arcsin_eq_zero_iff.mp hx0
  dsimp only [Function.comp_def]
  rw [Real.sin_arcsin hinside.1.le hinside.2.le]
  field_simp [hx0, hax]
  ring

theorem basic_natural_domains_eventually :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      x ≠ 0 ∧ Real.sin x ≠ 0 ∧ Real.cos x ≠ 0 ∧ 0 < 1 + x ∧ x ∈ Ioo (-1 : ℝ) 1 := by
  have hs := sine_linear_quotient_tendsto.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  have hc := (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.eventually_ne
    (by norm_num : Real.cos (0 : ℝ) ≠ 0)
  have hinside : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), x ∈ Ioo (-1 : ℝ) 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hs, hc.filter_mono nhdsWithin_le_nhds,
    hinside] with x hx hs hc hi
  have hx0 : x ≠ 0 := by simpa using hx
  refine ⟨hx0, ?_, hc, by linarith [hi.1], hi⟩
  intro hsin
  exact hs (by simp only [hsin, zero_div])

theorem cosine_tendsto_one :
    Tendsto Real.cos (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  simpa only [Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))

theorem tangent_sub_sine_cubic_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.tan x - Real.sin x) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have ht := (sine_linear_quotient_tendsto.mul cosine_quadratic_quotient_tendsto).div
    cosine_tendsto_one (by norm_num : (1 : ℝ) ≠ 0)
  norm_num only [one_mul, div_one] at ht
  apply ht.congr'
  filter_upwards [basic_natural_domains_eventually] with x hx
  dsimp only [Pi.div_apply]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hx.1, hx.2.2.1]

theorem tangent_cubic_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.tan x - x) / x ^ 3)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
  have ht := tangent_sub_sine_cubic_quotient_tendsto.add sine_cubic_quotient_tendsto
  norm_num at ht ⊢
  apply ht.congr'
  filter_upwards with x
  ring

theorem tangent_fifth_quotient_tendsto :
    Tendsto (fun x : ℝ ↦ (Real.tan x - x - x ^ 3 / 3) / x ^ 5)
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 / 15 : ℝ)) := by
  have hx₂ : Tendsto (fun x : ℝ ↦ x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using!
      (continuousAt_id.pow 2).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have ht := ((sine_fifth_quotient_tendsto.sub cosine_fourth_quotient_tendsto).add_const
    (1 / 6 : ℝ)).sub ((hx₂.mul cosine_fourth_quotient_tendsto).div_const 3)
  have ht' := ht.div cosine_tendsto_one (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at ht' ⊢
  apply ht'.congr'
  filter_upwards [basic_natural_domains_eventually] with x hx
  dsimp only [Pi.div_apply]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hx.1, hx.2.2.1]
  ring

theorem cotangent_first_cancellation_tendsto :
    Tendsto (fun x : ℝ ↦ (1 / x) * (1 / x - Real.cot x))
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
  have ht := (sine_cubic_quotient_tendsto.add cosine_quadratic_quotient_tendsto).div
    sine_linear_quotient_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at ht ⊢
  apply ht.congr'
  filter_upwards [basic_natural_domains_eventually] with x hx
  dsimp only [Pi.div_apply]
  rw [Real.cot_eq_cos_div_sin]
  field_simp [hx.1, hx.2.1]
  ring

theorem sine_minus_identity_cubic_eventually_ne :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ), Real.sin x - x ≠ 0 := by
  filter_upwards [sine_cubic_quotient_tendsto.eventually_ne
    (by norm_num : (-1 / 6 : ℝ) ≠ 0)] with x hx
  intro he
  exact hx (by simp only [he, zero_div])

theorem sine_fifth_residual_eventually_ne :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ), Real.sin x - x + x ^ 3 / 6 ≠ 0 := by
  filter_upwards [sine_fifth_quotient_tendsto.eventually_ne
    (by norm_num : (1 / 120 : ℝ) ≠ 0)] with x hx
  intro he
  exact hx (by simp only [he, zero_div])

theorem exponential_square_denominator_tendsto :
    Tendsto (fun x : ℝ ↦ (1 - Real.exp (-(x ^ 2))) / x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hd : HasDerivAt (fun t : ℝ ↦ 1 - Real.exp (-t)) 1 0 := by
    simpa using! ((hasDerivAt_id (0 : ℝ)).neg.exp).const_sub 1
  have hq : Tendsto (fun t : ℝ ↦ (1 - Real.exp (-t)) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [slope_fun_def_field, sub_zero, neg_zero, Real.exp_zero, sub_self] using! hd.tendsto_slope
  have harg : Tendsto (fun x : ℝ ↦ x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using!
        (continuousAt_id.pow 2).tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      exact pow_ne_zero 2 hx0
  exact hq.comp harg

theorem source_at_top_limit_of_eventual_natural_domain {D : Set ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) (hf : Tendsto f atTop (𝓝 L)) :
    DomainAtTopLimit D f L := by
  have hunbounded : ¬BddAbove D := by
    rw [not_bddAbove_iff]
    intro M
    exact (hD.and (eventually_gt_atTop M)).exists
  exact (domainAtTopLimit_iff_tendsto hunbounded).mpr (hf.mono_left inf_le_left)

/-- Bài 4(l): Taylor–Peano bậc một cho hai lũy thừa của hàm afin gần 0. -/
theorem sixth_root_affine_difference_taylor_tendsto :
    Tendsto (fun x : ℝ ↦
      ((1 + x) ^ (1 / 6 : ℝ) - (1 - x) ^ (1 / 6 : ℝ)) / x)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
  let f : ℝ → ℝ := fun x ↦ (1 + x) ^ (1 / 6 : ℝ) - (1 - x) ^ (1 / 6 : ℝ)
  have hd : HasDerivAt f (1 / 3) 0 := by
    have hp := ((hasDerivAt_id (0 : ℝ)).const_add 1).rpow_const
      (p := (1 / 6 : ℝ)) (Or.inl (by norm_num))
    have hm := ((hasDerivAt_id (0 : ℝ)).const_sub 1).rpow_const
      (p := (1 / 6 : ℝ)) (Or.inl (by norm_num))
    convert! hp.fun_sub hm using 1; norm_num [f]
  have hf : ContDiffOn ℝ 1 f (Ioo (-1 / 2 : ℝ) (1 / 2)) := by
    intro x hx
    have hp : ContDiffAt ℝ 1 (fun y : ℝ ↦ (1 + y) ^ (1 / 6 : ℝ)) x :=
      (Real.contDiffAt_rpow_const_of_ne (x := 1 + x) (p := (1 / 6 : ℝ))
        (by linarith [hx.1])).comp x (contDiffAt_const.add contDiffAt_id)
    have hm : ContDiffAt ℝ 1 (fun y : ℝ ↦ (1 - y) ^ (1 / 6 : ℝ)) x :=
      (Real.contDiffAt_rpow_const_of_ne (x := 1 - x) (p := (1 / 6 : ℝ))
        (by linarith [hx.2])).comp x (contDiffAt_const.sub contDiffAt_id)
    exact (hp.sub hm).contDiffWithinAt
  have ht := taylor_remainder_quotient_at_zero 1 (by norm_num) (by norm_num) hf
  have hp (x : ℝ) :
      (∑ k ∈ range 2, iteratedDeriv k f 0 / (k.factorial : ℝ) * x ^ k) = x / 3 := by
    norm_num [sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, hd.deriv, f]
    ring
  simp_rw [hp] at ht
  have ht' := ht.add_const (1 / 3 : ℝ)
  simp only [zero_add] at ht'
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  dsimp only [f]
  field_simp [hx0]
  ring

end calculus.Chapter04.Section04TaylorLimitCoefficients
