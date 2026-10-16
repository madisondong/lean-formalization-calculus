import calculus.Chapter03.Section03Exercises
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.Monoid

/-!
§3.7 — Bài tập 3.7.14(d,e)

Nguồn: dòng 3752–3753.
-/
set_option autoImplicit false
open Set Filter Topology
open scoped BigOperators
namespace calculus.Chapter03.Section07CotangentRootProductExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises


def cotangentQuarterProductDomain : Set ℝ :=
  {x | Real.sin (2 * x) ≠ 0 ∧ Real.sin (Real.pi / 4 - x) ≠ 0}

/-- Trong tích, chỉ số căn chạy từ 2 đến n. -/
def nthRootProductDomain (n : ℕ) : Set ℝ :=
  {x | (1 - x) ^ (n - 1) ≠ 0 ∧ ∀ k ∈ Finset.Icc 2 n, x ∈ nthRootDomain k}

/-- Bài tập 3.7.14(d): giới hạn bằng 2. -/
theorem cotangent_quarter_product_limit :
    DomainLimit cotangentQuarterProductDomain
      (fun x ↦ Real.cot (2 * x) * Real.cot (Real.pi / 4 - x)) (Real.pi / 4) 2 := by
  have hangle : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  have hf : HasDerivAt (fun x : ℝ ↦ Real.cos (2 * x)) (-2) (Real.pi / 4) := by
    simpa only [id_eq, hangle, Real.sin_pi_div_two, neg_mul, one_mul, mul_one] using!
      ((hasDerivAt_id (Real.pi / 4)).const_mul 2).cos
  have hg : HasDerivAt (fun x : ℝ ↦ Real.sin (Real.pi / 4 - x)) (-1) (Real.pi / 4) := by
    simpa only [id_eq, sub_self, Real.cos_zero, one_mul] using!
      ((hasDerivAt_id (Real.pi / 4)).const_sub (Real.pi / 4)).sin
  have hsin : ContinuousAt (fun x : ℝ ↦ Real.sin (2 * x)) (Real.pi / 4) := by fun_prop
  have hs : Tendsto (fun x : ℝ ↦ Real.sin (2 * x)) (𝓝 (Real.pi / 4)) (𝓝 (1 : ℝ)) := by
    simpa only [hangle, Real.sin_pi_div_two] using! hsin.tendsto
  have hE : {x : ℝ | Real.sin (2 * x) ≠ 0} ∈ 𝓝 (Real.pi / 4) := hs.eventually_ne one_ne_zero
  have hacc : AccumulationPointOf cotangentQuarterProductDomain (Real.pi / 4) := by
    have hden := derivative_quotient_domain_accumulation hg
      (by simp only [sub_self, Real.sin_zero]) (by norm_num : (-1 : ℝ) ≠ 0)
    apply accumulationPointOf_mono (accumulationPointOf_inter_nhds hden hE)
    intro x hx
    exact ⟨hx.2, hx.1⟩
  have hr : DomainLimit cotangentQuarterProductDomain
      (fun x ↦ Real.cos (2 * x) / Real.sin (Real.pi / 4 - x)) (Real.pi / 4) 2 := by
    simpa only [show (-2 : ℝ) / (-1) = 2 by norm_num] using!
      ratio_of_derivative_slopes hacc hf hg
        (by rw [hangle, Real.cos_pi_div_two])
        (by simp only [sub_self, Real.sin_zero]) (by norm_num : (-1 : ℝ) ≠ 0)
  have hrat := (domainLimit_iff_tendsto hacc).mp hr
  have hcos : ContinuousAt (fun x : ℝ ↦ Real.cos (Real.pi / 4 - x)) (Real.pi / 4) := by fun_prop
  have hc : Tendsto (fun x : ℝ ↦ Real.cos (Real.pi / 4 - x))
      (𝓝[cotangentQuarterProductDomain \ {Real.pi / 4}] (Real.pi / 4)) (𝓝 (1 : ℝ)) := by
    simpa only [sub_self, Real.cos_zero] using! hcos.tendsto.mono_left nhdsWithin_le_nhds
  have hs2 : Tendsto (fun x : ℝ ↦ Real.sin (2 * x))
      (𝓝[cotangentQuarterProductDomain \ {Real.pi / 4}] (Real.pi / 4)) (𝓝 (1 : ℝ)) :=
    hs.mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun x : ℝ ↦ Real.cos (Real.pi / 4 - x) / Real.sin (2 * x))
      (𝓝[cotangentQuarterProductDomain \ {Real.pi / 4}] (Real.pi / 4)) (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_apply, div_one] using! hc.div hs2 one_ne_zero
  have hp : Tendsto (fun x : ℝ ↦ (Real.cos (2 * x) / Real.sin (Real.pi / 4 - x)) *
      (Real.cos (Real.pi / 4 - x) / Real.sin (2 * x)))
      (𝓝[cotangentQuarterProductDomain \ {Real.pi / 4}] (Real.pi / 4)) (𝓝 (2 : ℝ)) := by
    simpa only [Pi.mul_apply, mul_one] using! hrat.mul hq
  apply (domainLimit_iff_tendsto hacc).mpr
  apply hp.congr
  intro x
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  ring


theorem product_two_through_n_eq_factorial (n : ℕ) (hn : 1 ≤ n) :
    (∏ k ∈ Finset.Icc 2 n, (k : ℝ)) = (n.factorial : ℝ) := by
  have hall : ∀ m : ℕ, (∏ k ∈ Finset.Icc 2 (m + 1), (k : ℝ)) = ((m + 1).factorial : ℝ) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 1 + 1), ih,
        Nat.factorial_succ (m + 1), Nat.cast_mul]
      ring
  have he : n - 1 + 1 = n := by omega
  simpa only [he] using hall (n - 1)

/-- Bài tập 3.7.14(e): giới hạn bằng 1/n! với mọi n≥2. -/
theorem nth_root_product_limit_at_one (n : ℕ) (hn : 2 ≤ n) :
    DomainLimit (nthRootProductDomain n)
      (fun x ↦ (∏ k ∈ Finset.Icc 2 n, (1 - realNthRoot k x)) / (1 - x) ^ (n - 1))
      1 (1 / (n.factorial : ℝ)) := by
  have hacc : AccumulationPointOf (nthRootProductDomain n) 1 := by
    apply accumulationPointOf_mono
      (accumulationPointOf_inter_Ioi (univ_diff_accumulation 1) (by norm_num : (0 : ℝ) < 1))
    intro x hx
    have hxne : x ≠ 1 := by simpa using hx.1.2
    exact ⟨pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hxne)), fun _ _ ↦ Or.inr hx.2.le⟩
  have hfactor : ∀ k ∈ Finset.Icc 2 n,
      Tendsto (fun x : ℝ ↦ (1 - realNthRoot k x) / (1 - x))
        (𝓝[nthRootProductDomain n \ {1}] 1) (𝓝 ((k : ℝ)⁻¹)) := by
    intro k hk
    have hk1 : 1 ≤ k := by have h := (Finset.mem_Icc.mp hk).1; omega
    have hf := (realNthRoot_hasDerivAt_one hk1).const_sub 1
    have hg : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) 1 := by
      simpa only [id_eq] using! (hasDerivAt_id (1 : ℝ)).const_sub 1
    have hr : DomainLimit (nthRootProductDomain n)
        (fun x ↦ (1 - realNthRoot k x) / (1 - x)) 1 ((k : ℝ)⁻¹) := by
      simpa only [neg_div_neg_eq, div_one] using!
        ratio_of_derivative_slopes hacc hf hg (by rw [realNthRoot_one, sub_self])
          (by norm_num) (by norm_num : (-1 : ℝ) ≠ 0)
    exact (domainLimit_iff_tendsto hacc).mp hr
  have hprod : Tendsto (fun x : ℝ ↦ ∏ k ∈ Finset.Icc 2 n, (1 - realNthRoot k x) / (1 - x))
      (𝓝[nthRootProductDomain n \ {1}] 1) (𝓝 (∏ k ∈ Finset.Icc 2 n, (k : ℝ)⁻¹)) :=
    tendsto_finsetProd (Finset.Icc 2 n) hfactor
  have hvalue : (∏ k ∈ Finset.Icc 2 n, (k : ℝ)⁻¹) = 1 / (n.factorial : ℝ) := by
    rw [Finset.prod_inv_distrib, product_two_through_n_eq_factorial n (by omega), one_div]
  have hcard : (Finset.Icc 2 n).card = n - 1 := by rw [Nat.card_Icc]; omega
  apply (domainLimit_iff_tendsto hacc).mpr
  rw [hvalue] at hprod
  apply hprod.congr
  intro x
  rw [Finset.prod_div_distrib, Finset.prod_const, hcard]

end calculus.Chapter03.Section07CotangentRootProductExercises
