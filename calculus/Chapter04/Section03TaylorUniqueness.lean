import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Basic

/-!
# Tính duy nhất của hệ số khai triển Peano

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1258–1266. Giới hạn một bên của phần dư Peano đủ xác định hệ số; không lấy đạo hàm của phần dư.
-/
namespace calculus.Chapter04.Section03TaylorUniqueness
open Filter Finset
open scoped Topology BigOperators


noncomputable def powerPolynomial (a : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), a k * t ^ k


theorem powerPolynomial_succ (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    powerPolynomial a (n + 1) t =
      a 0 + t * powerPolynomial (fun k ↦ a (k + 1)) n t := by
  unfold powerPolynomial
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ]
  ring


theorem powerPolynomial_zero (a : ℕ → ℝ) (n : ℕ) : powerPolynomial a n 0 = a 0 := by
  unfold powerPolynomial
  rw [Finset.sum_range_succ']
  simp only [zero_pow (Nat.succ_ne_zero _), mul_zero, sum_const_zero,
    pow_zero, mul_one, zero_add]


theorem constant_coefficient_zero_of_littleO (n : ℕ) (a : ℕ → ℝ)
    (h : powerPolynomial a n =o[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ n)) :
    a 0 = 0 := by
  have hp : Continuous (powerPolynomial a n) := by unfold powerPolynomial; fun_prop
  have hlim := hp.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  rw [powerPolynomial_zero] at hlim
  have hsmall := h.tendsto_zero_of_tendsto
    ((tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).pow n)
  exact tendsto_nhds_unique hlim hsmall


theorem coefficients_zero_of_littleO (n : ℕ) (a : ℕ → ℝ)
    (h : powerPolynomial a n =o[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ n)) :
    ∀ k ≤ n, a k = 0 := by
  induction n generalizing a with
  | zero =>
      intro k hk
      have he : k = 0 := by omega
      simpa only [he] using constant_coefficient_zero_of_littleO 0 a h
  | succ n ih =>
      have hzero := constant_coefficient_zero_of_littleO (n + 1) a h
      have hm : (fun t : ℝ ↦ t * powerPolynomial (fun k ↦ a (k + 1)) n t)
          =o[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ (n + 1)) :=
        h.congr_left (fun t ↦ by rw [powerPolynomial_succ, hzero, zero_add])
      have hnz : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≠ 0 := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact ht.ne'
      have hdiv := (Asymptotics.isLittleO_mul_iff_isLittleO_div hnz).mp hm
      have hshift : powerPolynomial (fun k ↦ a (k + 1)) n
          =o[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ n) := by
        apply hdiv.congr' (Eventually.of_forall fun _ ↦ rfl)
        filter_upwards [hnz] with t ht
        rw [pow_succ, mul_div_cancel_right₀ _ ht]
      have hs := ih (fun k ↦ a (k + 1)) hshift
      intro k hk
      rcases k with _ | k
      · exact hzero
      · exact hs k (Nat.le_of_succ_le_succ hk)


theorem coefficients_eq_of_difference_littleO (n : ℕ) (a b : ℕ → ℝ)
    (h : (fun t ↦ powerPolynomial a n t - powerPolynomial b n t)
      =o[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ n)) : ∀ k ≤ n, a k = b k := by
  have hz : powerPolynomial (fun k ↦ a k - b k) n
      =o[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ n) := by
    apply h.congr_left
    intro t
    simp only [powerPolynomial, sub_mul, sum_sub_distrib]
  intro k hk
  exact sub_eq_zero.mp (coefficients_zero_of_littleO n (fun k ↦ a k - b k) hz k hk)


theorem powerPolynomial_mul (a : ℕ → ℝ) (n : ℕ) (σ t : ℝ) :
    powerPolynomial a n (σ * t) = powerPolynomial (fun k ↦ a k * σ ^ k) n t := by
  unfold powerPolynomial
  apply sum_congr rfl
  intro k _
  rw [mul_pow]
  ring


theorem coefficients_eq_of_two_expansions {I : Set ℝ} {x₀ σ : ℝ}
    {f : ℝ → ℝ} (n : ℕ) (a b : ℕ → ℝ) (hσ : σ ≠ 0)
    (hdir : Tendsto (fun t : ℝ ↦ x₀ + σ * t) (𝓝[>] 0) (𝓝[I] x₀))
    (ha : (fun x ↦ f x - powerPolynomial a n (x - x₀))
      =o[𝓝[I] x₀] (fun x ↦ (x - x₀) ^ n))
    (hb : (fun x ↦ f x - powerPolynomial b n (x - x₀))
      =o[𝓝[I] x₀] (fun x ↦ (x - x₀) ^ n)) :
    ∀ k ≤ n, a k = b k := by
  have h := (ha.sub hb).comp_tendsto hdir
  have hpoly : (fun t ↦ powerPolynomial (fun k ↦ b k * σ ^ k) n t -
      powerPolynomial (fun k ↦ a k * σ ^ k) n t)
      =o[𝓝[>] (0 : ℝ)] (fun t ↦ σ ^ n * t ^ n) := by
    apply h.congr
    · intro t
      simp only [Function.comp_apply]
      rw [show x₀ + σ * t - x₀ = σ * t by ring, powerPolynomial_mul,
        powerPolynomial_mul]
      ring
    · intro t
      simp only [Function.comp_apply]
      rw [show x₀ + σ * t - x₀ = σ * t by ring, mul_pow]
  have he := coefficients_eq_of_difference_littleO n
    (fun k ↦ b k * σ ^ k) (fun k ↦ a k * σ ^ k) hpoly.of_const_mul_right
  intro k hk
  exact (mul_right_cancel₀ (pow_ne_zero k hσ) (he k hk)).symm


theorem coefficients_eq_on_closed_interval {f : ℝ → ℝ} {l r x₀ : ℝ}
    (hlr : l < r) (hx₀ : x₀ ∈ Set.Icc l r) (n : ℕ) (a b : ℕ → ℝ)
    (ha : (fun x ↦ f x - powerPolynomial a n (x - x₀))
      =o[𝓝[Set.Icc l r] x₀] (fun x ↦ (x - x₀) ^ n))
    (hb : (fun x ↦ f x - powerPolynomial b n (x - x₀))
      =o[𝓝[Set.Icc l r] x₀] (fun x ↦ (x - x₀) ^ n)) :
    ∀ k ≤ n, a k = b k := by
  by_cases hr : x₀ < r
  · apply coefficients_eq_of_two_expansions n a b (σ := 1) one_ne_zero _ ha hb
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · simpa only [one_mul, add_zero, id_eq] using
        (tendsto_const_nhds.add (tendsto_id.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)))
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hr)] with t ht
      simp only [one_mul, Set.mem_Icc]
      constructor <;> linarith [hx₀.1, ht.1, ht.2]
  · have he : x₀ = r := le_antisymm hx₀.2 (le_of_not_gt hr)
    have hl : l < x₀ := by simpa only [he] using hlr
    apply coefficients_eq_of_two_expansions n a b (σ := -1) (by norm_num) _ ha hb
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · simpa only [mul_zero, add_zero, id_eq] using
        (tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_id.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))))
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hl)] with t ht
      simp only [neg_one_mul, Set.mem_Icc]
      constructor <;> linarith [hx₀.2, ht.1, ht.2]

end calculus.Chapter04.Section03TaylorUniqueness
