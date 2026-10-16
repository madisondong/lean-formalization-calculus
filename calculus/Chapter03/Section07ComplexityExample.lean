import calculus.Chapter03.Section07
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# §3.7 — ví dụ độ phức tạp bậc hai

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3390.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07ComplexityExample
open calculus.Chapter03.Section07


theorem quadratic_cost_ratio_atTop :
    Tendsto (fun x : ℝ ↦ (4 * x ^ 2 - 2 * x + 2) / x ^ 2)
      atTop (𝓝 4) := by
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have ht : Tendsto (fun x : ℝ ↦ 4 - 2 * x⁻¹ + 2 * (x⁻¹) ^ 2)
      atTop (𝓝 4) := by
    simpa using ((tendsto_const_nhds (x := (4 : ℝ))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hi)).add
      ((tendsto_const_nhds (x := (2 : ℝ))).mul (hi.pow 2))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith
  field_simp [hx0]


theorem quadratic_cost_nonzero_ratio_limit_along :
    NonzeroRatioLimitAlong univ .positiveInfinity
      (fun x : ℝ ↦ 4 * x ^ 2 - 2 * x + 2) (fun x ↦ x ^ 2) := by
  refine ⟨(properLimitApproach_positiveInfinity_iff univ).mpr not_bddAbove_univ, ?_,
    4, by norm_num, ?_⟩
  · have he : ∀ᶠ x : ℝ in atTop, x ^ 2 ≠ 0 := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact pow_ne_zero 2 (by linarith)
    simpa only [domainApproachFilter, principal_univ, inf_top_eq] using he
  · simpa only [domainApproachFilter, principal_univ, inf_top_eq] using quadratic_cost_ratio_atTop

/-- Dòng 3390: thương với n² tiến đến 4. -/
theorem quadratic_cost_natural_ratio :
    Tendsto (fun n : ℕ ↦ (4 * (n : ℝ) ^ 2 - 2 * (n : ℝ) + 2) / (n : ℝ) ^ 2)
      atTop (𝓝 4) := by
  exact quadratic_cost_ratio_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

end calculus.Chapter03.Section07ComplexityExample
