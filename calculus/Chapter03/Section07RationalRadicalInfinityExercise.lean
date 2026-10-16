import calculus.Chapter03.Section07QuadraticRadicalInfinityExercises

/-!
§3.7 — Bài tập 3.7.13(h)

Nguồn: dòng 3737.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07RationalRadicalInfinityExercise
open calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section07QuadraticRadicalInfinityExercises


def rationalRadicalDomain : Set ℝ :=
  {x | x + 1 ≠ 0 ∧ 0 ≤ (x ^ 3 + 2 * x ^ 2) / (x + 1)}


theorem rationalRadicalDomain_eventually_atBot :
    ∀ᶠ x : ℝ in atBot, x ∈ rationalRadicalDomain := by
  filter_upwards [eventually_lt_atBot (-2 : ℝ)] with x hx
  have hden : x + 1 < 0 := by linarith
  have hnum : x ^ 3 + 2 * x ^ 2 ≤ 0 := by
    calc
      x ^ 3 + 2 * x ^ 2 = x ^ 2 * (x + 2) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (by linarith)
  exact ⟨hden.ne, div_nonneg_of_nonpos hnum hden.le⟩


theorem normalized_rational_radicand_atBot :
    Tendsto (fun x : ℝ ↦ ((x ^ 3 + 2 * x ^ 2) / (x + 1)) / x ^ 2)
      atBot (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have hn : Tendsto (fun x : ℝ ↦ 1 + 2 * x⁻¹) atBot (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using! (hi.const_mul 2).const_add 1
  have hd : Tendsto (fun x : ℝ ↦ 1 + x⁻¹) atBot (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using! hi.const_add 1
  have ht : Tendsto (fun x : ℝ ↦ (1 + 2 * x⁻¹) / (1 + x⁻¹)) atBot (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_apply, div_one] using! hn.div hd one_ne_zero
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (-2 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hnumeq : 1 + 2 * x⁻¹ = (x + 2) / x := by
    rw [add_div, div_self hx0, div_eq_mul_inv]
  have hdeneq : 1 + x⁻¹ = (x + 1) / x := by
    rw [add_div, div_self hx0, one_div]
  rw [hnumeq, hdeneq, div_div_div_cancel_right₀ hx0]
  rw [show x ^ 3 + 2 * x ^ 2 = x ^ 2 * (x + 2) by ring, mul_div_assoc,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hx0)]


theorem normalized_rational_sqrt_atBot :
    Tendsto (fun x : ℝ ↦ Real.sqrt ((x ^ 3 + 2 * x ^ 2) / (x + 1)) / x)
      atBot (𝓝 (-1 : ℝ)) := by
  have hs : Tendsto
      (fun x : ℝ ↦ -Real.sqrt (((x ^ 3 + 2 * x ^ 2) / (x + 1)) / x ^ 2))
      atBot (𝓝 (-1 : ℝ)) := by
    simpa only [Function.comp_def, Pi.neg_apply, Real.sqrt_one] using!
      (Real.continuous_sqrt.continuousAt.tendsto.comp normalized_rational_radicand_atBot).neg
  apply hs.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  have hx0 := hx.ne
  have he : (x ^ 3 + 2 * x ^ 2) / (x + 1) =
      x ^ 2 * (((x ^ 3 + 2 * x ^ 2) / (x + 1)) / x ^ 2) :=
    (mul_div_cancel₀ _ (pow_ne_zero 2 hx0)).symm
  have hsqrt : Real.sqrt ((x ^ 3 + 2 * x ^ 2) / (x + 1)) =
      -x * Real.sqrt (((x ^ 3 + 2 * x ^ 2) / (x + 1)) / x ^ 2) := by
    conv_lhs => rw [he]
    rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_neg hx]
  rw [hsqrt]
  field_simp [hx0]


theorem rational_radicand_linear_increment_atBot :
    Tendsto (fun x : ℝ ↦ (((x ^ 3 + 2 * x ^ 2) / (x + 1)) - x ^ 2) / x)
      atBot (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have hd : Tendsto (fun x : ℝ ↦ 1 + x⁻¹) atBot (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using! hi.const_add 1
  have ht : Tendsto (fun x : ℝ ↦ 1 / (1 + x⁻¹)) atBot (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_apply, div_one] using!
      (tendsto_const_nhds (x := (1 : ℝ))).div hd one_ne_zero
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (-2 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hdeneq : 1 + x⁻¹ = (x + 1) / x := by
    rw [add_div, div_self hx0, one_div]
  have hdiff : (x ^ 3 + 2 * x ^ 2) / (x + 1) - x ^ 2 = x ^ 2 / (x + 1) := by
    apply (eq_div_iff hx1).mpr
    rw [sub_mul, div_mul_cancel₀ _ hx1]
    ring
  rw [hdeneq, one_div_div, hdiff, div_div]
  rw [pow_two, mul_comm (x + 1) x, mul_div_mul_left _ _ hx0]

/-- Bài tập 3.7.13(h): x+√((x³+2x²)/(x+1))→−1/2 khi x→−∞. -/
theorem rational_radical_at_negative_infinity :
    DomainAtBotLimit rationalRadicalDomain
      (fun x ↦ x + Real.sqrt ((x ^ 3 + 2 * x ^ 2) / (x + 1))) (-1 / 2) := by
  apply domainAtBotLimit_of_eventually_domain rationalRadicalDomain_eventually_atBot
  have hd : Tendsto
      (fun x : ℝ ↦ Real.sqrt ((x ^ 3 + 2 * x ^ 2) / (x + 1)) / x - 1)
      atBot (𝓝 (-2 : ℝ)) := by
    simpa only [Pi.sub_apply, show (-1 : ℝ) - 1 = -2 by norm_num] using!
      normalized_rational_sqrt_atBot.sub_const 1
  have ht : Tendsto
      (fun x : ℝ ↦ ((((x ^ 3 + 2 * x ^ 2) / (x + 1)) - x ^ 2) / x) /
        (Real.sqrt ((x ^ 3 + 2 * x ^ 2) / (x + 1)) / x - 1))
      atBot (𝓝 (-1 / 2 : ℝ)) := by
    simpa only [Pi.div_apply, show (1 : ℝ) / (-2) = -1 / 2 by norm_num] using!
      rational_radicand_linear_increment_atBot.div hd (by norm_num : (-2 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (-2 : ℝ), rationalRadicalDomain_eventually_atBot] with x hx hD
  have hx0 : x ≠ 0 := by linarith
  have hs0 := Real.sqrt_nonneg ((x ^ 3 + 2 * x ^ 2) / (x + 1))
  have hsq := Real.sq_sqrt hD.2
  have hden : Real.sqrt ((x ^ 3 + 2 * x ^ 2) / (x + 1)) - x ≠ 0 := by linarith
  have hdeneq : Real.sqrt ((x ^ 3 + 2 * x ^ 2) / (x + 1)) / x - 1 =
      (Real.sqrt ((x ^ 3 + 2 * x ^ 2) / (x + 1)) - x) / x := by
    rw [sub_div, div_self hx0]
  rw [hdeneq, div_div_div_cancel_right₀ hx0]
  apply (div_eq_iff hden).mpr
  nlinarith

end calculus.Chapter03.Section07RationalRadicalInfinityExercise
