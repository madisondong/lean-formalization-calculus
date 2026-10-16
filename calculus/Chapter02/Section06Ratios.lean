import calculus.Chapter02.Section05
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import calculus.Chapter02.Section07

/-!
# 2.6.17. Tiêu chuẩn tỉ số và áp dụng

Nguồn: `source/Ch2_dayso.tex`, dòng 2089–2097.
Các tiêu chuẩn tỉ số giả thiết xₙ≠0 tại n≥1.
-/

namespace calculus.Chapter02.Section06Ratios

open Filter
open scoped Topology

/-- Bài 2.6.17(a): giới hạn tỉ số trị tuyệt đối nhỏ hơn 1 thì xₙ→0. -/
theorem ratio_abs_lt_one_converges_zero {u : ℕ → ℝ} {L : ℝ}
    (hne : ∀ n : ℕ, 1 ≤ n → u n ≠ 0)
    (hlim : Section03.ConvergesTo (fun n ↦ |u (n + 1) / u n|) L)
    (hL : L < 1) : Section03.ConvergesTo u 0 := by
  have hr : Tendsto (fun n ↦ ‖u (n + 1)‖ / ‖u n‖) atTop (𝓝 L) := by
    simpa only [Real.norm_eq_abs, abs_div] using Section03.convergesTo_iff_tendsto.mp hlim
  exact Section03.convergesTo_iff_tendsto.mpr
    (summable_of_ratio_test_tendsto_lt_one hL (eventually_atTop.2 ⟨1, hne⟩) hr).tendsto_atTop_zero

/-- Bài 2.6.17(b): giới hạn tỉ số trị tuyệt đối lớn hơn 1 thì |xₙ|→+∞. -/
theorem ratio_abs_gt_one_abs_tendsto_atTop {u : ℕ → ℝ} {L : ℝ}
    (hne : ∀ n : ℕ, 1 ≤ n → u n ≠ 0)
    (hlim : Section03.ConvergesTo (fun n ↦ |u (n + 1) / u n|) L)
    (hL : 1 < L) : Tendsto (fun n ↦ |u n|) atTop atTop := by
  obtain ⟨r, hr1, hrL⟩ := exists_between hL
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Section03.convergesTo_iff_tendsto.mp hlim).eventually_const_le hrL)
  let K := max N 1
  have hK : 1 ≤ K := le_max_right _ _
  have hgeom : Tendsto (fun n : ℕ ↦ |u (n + K)|) atTop atTop := by
    apply tendsto_atTop_of_geom_le (by simpa using abs_pos.mpr (hne K hK)) hr1
    intro n
    have hk : N ≤ n + K := (le_max_left N 1).trans (Nat.le_add_left K n)
    have hp : 0 < |u (n + K)| := abs_pos.mpr (hne (n + K) (hK.trans (Nat.le_add_left K n)))
    have hg := hN (n + K) hk
    rw [abs_div] at hg
    have hb := (le_div_iff₀ hp).mp hg
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
  exact (tendsto_add_atTop_iff_nat K).mp hgeom

/-- Bài 2.6.17(b): dãy không có giới hạn thực hữu hạn. -/
theorem ratio_abs_gt_one_divergent {u : ℕ → ℝ} {L : ℝ}
    (hne : ∀ n : ℕ, 1 ≤ n → u n ≠ 0)
    (hlim : Section03.ConvergesTo (fun n ↦ |u (n + 1) / u n|) L)
    (hL : 1 < L) : Section03.IsDivergent u := by
  rintro ⟨a, ha⟩
  exact not_tendsto_atTop_of_tendsto_nhds
    ((Section03.convergesTo_iff_tendsto.mp ha).abs)
    (ratio_abs_gt_one_abs_tendsto_atTop hne hlim hL)

/-- Tỉ số của dãy hằng 1 bằng 1. -/
theorem constant_one_abs_ratio_converges :
    Section03.ConvergesTo (fun _ : ℕ ↦ |(1 : ℝ) / 1|) 1 := by
  simpa using Section03.constant_converges (1 : ℝ)


theorem alternating_abs_ratio_converges :
    Section03.ConvergesTo (fun n : ℕ ↦ |(-1 : ℝ) ^ (n + 1) / (-1 : ℝ) ^ n|) 1 := by
  have heq : (fun n : ℕ ↦ |(-1 : ℝ) ^ (n + 1) / (-1 : ℝ) ^ n|) = (fun _ ↦ (1 : ℝ)) := by
    funext n
    simp [abs_div, abs_pow]
  rw [heq]
  exact Section03.constant_converges 1

/-- Bài 2.6.17(c): cùng L=1, một dãy hội tụ và một dãy phân kì. -/
theorem ratio_one_does_not_decide_convergence :
    Section03.IsConvergent (fun _ : ℕ ↦ (1 : ℝ)) ∧
      Section03.IsDivergent (fun n : ℕ ↦ (-1 : ℝ) ^ n) ∧
      (∀ n : ℕ, 1 ≤ n → (-1 : ℝ) ^ n ≠ 0) ∧
      Section03.ConvergesTo (fun n : ℕ ↦ |(-1 : ℝ) ^ (n + 1) / (-1 : ℝ) ^ n|) 1 :=
  ⟨⟨1, Section03.constant_converges 1⟩, Section03.alternating_isDivergent,
    fun _ _ ↦ pow_ne_zero _ (by norm_num), alternating_abs_ratio_converges⟩

/-- Áp dụng thứ nhất: αⁿ/n!→0 với mọi α∈ℝ. -/
theorem pow_div_factorial_converges (α : ℝ) :
    Section03.ConvergesTo (fun n : ℕ ↦ α ^ n / n.factorial) 0 :=
  Section05.pow_div_factorial_converges α

/-- Áp dụng thứ ba: n^k/αⁿ→0 với k>0 và |α|>1. -/
theorem rpow_div_signed_pow_converges (α k : ℝ) (hα : 1 < |α|) (_hk : 0 < k) :
    Section03.ConvergesTo (fun n : ℕ ↦ Real.rpow (n : ℝ) k / α ^ n) 0 := by
  have hb : 0 < Real.log |α| := Real.log_pos hα
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k (Real.log |α|) hb).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : ∀ n : ℕ, Real.rpow (n : ℝ) k * Real.exp (-(Real.log |α|) * n) =
      Real.rpow (n : ℝ) k / |α| ^ n := by
    intro n
    rw [neg_mul, Real.exp_neg, mul_comm (Real.log |α|) (n : ℝ), Real.exp_nat_mul,
      Real.exp_log (by linarith : 0 < |α|)]
    exact (div_eq_mul_inv _ _).symm
  have ht' : Tendsto (fun n : ℕ ↦ Real.rpow (n : ℝ) k / |α| ^ n) atTop (𝓝 0) :=
    ht.congr heq
  apply Section03.convergesTo_zero_iff_abs.mpr
  apply Section03.convergesTo_iff_tendsto.mpr
  have habs : (fun n : ℕ ↦ |Real.rpow (n : ℝ) k / α ^ n|) =
      (fun n : ℕ ↦ Real.rpow (n : ℝ) k / |α| ^ n) := by
    funext n
    simp only [Real.rpow_eq_pow, abs_div, abs_pow,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) k)]
  rw [habs]
  exact ht'

/-- Áp dụng thứ hai: 2ⁿ/n⁴ tiến về +∞. -/
theorem two_pow_div_fourth_power_tendsToPosInfinity :
    Section07.SequenceTendsToPosInfinity (fun n : ℕ ↦ (2 : ℝ) ^ n / (n : ℝ) ^ 4) :=
  Section07.geometric_div_power_tendsToPosInfinity 2 (by norm_num) 4

/-- Áp dụng thứ hai không có giới hạn thực hữu hạn. -/
theorem two_pow_div_fourth_power_divergent :
    Section03.IsDivergent (fun n : ℕ ↦ (2 : ℝ) ^ n / (n : ℝ) ^ 4) := by
  rintro ⟨a, ha⟩
  exact not_tendsto_atTop_of_tendsto_nhds (Section03.convergesTo_iff_tendsto.mp ha)
    ((Section07.sequenceTendsToPosInfinity_iff_tendsto _).mp two_pow_div_fourth_power_tendsToPosInfinity)

end calculus.Chapter02.Section06Ratios
