import calculus.Chapter03.Section03Exercises
import calculus.Chapter03.Section01Powers
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# §3.6 — Bài tập 6(b,f): căn bậc n và thương lũy thừa

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3158, dòng 3163.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter03.Section06RootRatioExercises
open Set Filter Topology
open calculus.Chapter03.Section01Powers
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises


theorem positive_mem_power_domain (α : ℝ) {u : ℝ} (hu : 0 < u) :
    u ∈ realPowerDomain α := by
  classical
  unfold realPowerDomain
  split_ifs <;> first | exact mem_univ u | exact hu.ne' | exact hu


def rootIncrementDomain (n : ℕ) (α : ℝ) : Set ℝ :=
  {x | 1 + α * x ∈ nthRootDomain n ∧ x ≠ 0}

theorem root_increment_domain_accumulation (n : ℕ) {α : ℝ} (hα : 0 < α) :
    AccumulationPointOf (rootIncrementDomain n α) 0 := by
  intro δ hδ
  have hp : 0 < α * (δ / 2) := mul_pos hα (by linarith)
  refine ⟨δ / 2, ⟨Or.inr (by linarith), by linarith⟩,
    by linarith, by linarith, by linarith⟩

/-- Bài tập 6(b): giới hạn với n≥2 và α>0. -/
theorem exercise06_root_increment (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) :
    DomainLimit (rootIncrementDomain n α)
      (fun x : ℝ ↦ (realNthRoot n (1 + α * x) - 1) / x) 0 (α / (n : ℝ)) := by
  apply (domainLimit_iff_tendsto (root_increment_domain_accumulation n hα)).mpr
  have harg : HasDerivAt (fun x : ℝ ↦ 1 + α * x) α 0 := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_mul α).const_add 1
  have houter : HasDerivAt (realNthRoot n) ((n : ℝ)⁻¹) (1 + α * (0 : ℝ)) := by
    simpa only [mul_zero, add_zero] using
      realNthRoot_hasDerivAt_one (show 1 ≤ n by omega)
  have ht : Tendsto (fun x : ℝ ↦ (realNthRoot n (1 + α * x) - 1) / x)
      (𝓝[≠] 0) (𝓝 (α / (n : ℝ))) := by
    simpa only [slope_fun_def_field, Function.comp_def, mul_zero, add_zero, realNthRoot_one, sub_zero,
      div_eq_mul_inv, mul_comm] using (houter.comp 0 harg).tendsto_slope
  exact ht.mono_left (nhdsWithin_mono 0 (fun _ hx ↦ hx.2))


def fractionalPowerRatioDomain (m n p q : ℕ) : Set ℝ :=
  {x | x ∈ realPowerDomain (1 / (m : ℝ)) ∧
    x ∈ realPowerDomain (1 / (n : ℝ)) ∧
    x ∈ realPowerDomain (1 / (p : ℝ)) ∧
    x ∈ realPowerDomain (1 / (q : ℝ)) ∧
    x ^ (1 / (p : ℝ)) - x ^ (1 / (q : ℝ)) ≠ 0}

/-- Bài tập 6(f): giới hạn thương, với m<n và p<q. -/
theorem exercise06_fractional_power_ratio (m n p q : ℕ)
    (_hm : 1 ≤ m) (_hn : 1 ≤ n) (hp : 1 ≤ p) (_hq : 1 ≤ q)
    (_hmn : m < n) (hpq : p < q) :
    DomainLimit (fractionalPowerRatioDomain m n p q)
      (fun x : ℝ ↦ (x ^ (1 / (m : ℝ)) - x ^ (1 / (n : ℝ))) /
        (x ^ (1 / (p : ℝ)) - x ^ (1 / (q : ℝ)))) 1
      ((1 / (m : ℝ) - 1 / (n : ℝ)) / (1 / (p : ℝ) - 1 / (q : ℝ))) := by
  have hpow (r : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ r) r 1 := by
    simpa only [Real.one_rpow, mul_one] using
      Real.hasDerivAt_rpow_const (p := r) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hf := (hpow (1 / (m : ℝ))).fun_sub (hpow (1 / (n : ℝ)))
  have hg := (hpow (1 / (p : ℝ))).fun_sub (hpow (1 / (q : ℝ)))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have hgp : 0 < 1 / (p : ℝ) - 1 / (q : ℝ) :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hp0 hpq')
  have ha₀ := derivative_quotient_domain_accumulation hg
    (by simp only [Real.one_rpow, sub_self]) hgp.ne'
  have ha : AccumulationPointOf (fractionalPowerRatioDomain m n p q) 1 :=
    accumulationPointOf_mono (accumulationPointOf_inter_Ioi ha₀ (by norm_num : (0 : ℝ) < 1))
      (fun x hx ↦ ⟨positive_mem_power_domain _ hx.2, positive_mem_power_domain _ hx.2,
        positive_mem_power_domain _ hx.2, positive_mem_power_domain _ hx.2, hx.1⟩)
  exact ratio_of_derivative_slopes ha hf hg (by simp only [Real.one_rpow, sub_self])
    (by simp only [Real.one_rpow, sub_self]) hgp.ne'

end calculus.Chapter03.Section06RootRatioExercises
