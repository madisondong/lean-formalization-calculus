import calculus.Chapter02.Section09
import calculus.Chapter02.Section06

/-!
# Mục 2.9: truy hồi và dãy co

Nguồn: `source/Ch2_dayso.tex`, dòng 2889–2929; Bài 2.9.15–20.
-/
namespace calculus.Chapter02.Section09Supplement
open Filter Set
open scoped Topology BigOperators
open calculus.Chapter02.Section03 calculus.Chapter02.Section04 calculus.Chapter02.Section06
open calculus.Chapter02.Section09

/-- Bài 2.9.17: định nghĩa dãy co với 0≤α<1. -/
def SequenceHasContractiveDifferences (u : ℕ → ℝ) : Prop :=
  ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
    ∀ n : ℕ, 1 ≤ n → |u (n + 2) - u (n + 1)| ≤ α * |u (n + 1) - u n|

/-- Cận hình học của sai phân theo số hạng đầu. -/
theorem successive_differences_geometric_bound (u : ℕ → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hstep : ∀ n, 1 ≤ n → |u (n + 2) - u (n + 1)| ≤ α * |u (n + 1) - u n|) :
    ∀ n : ℕ, |u (n + 2) - u (n + 1)| ≤ |u 2 - u 1| * α ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      |u (n + 1 + 2) - u (n + 1 + 1)| ≤ α * |u (n + 1 + 1) - u (n + 1)| :=
        hstep (n + 1) (by omega)
      _ ≤ α * (|u 2 - u 1| * α ^ n) := mul_le_mul_of_nonneg_left ih hα
      _ = |u 2 - u 1| * α ^ (n + 1) := by rw [pow_succ]; ring

/-- Bài 2.9.17: dãy co là dãy Cauchy, với 0≤α<1. -/
theorem sequenceCauchy_of_contractive_differences (u : ℕ → ℝ) (hu : SequenceHasContractiveDifferences u) :
    SequenceCauchy u := by
  obtain ⟨α, hα0, hα1, hstep⟩ := hu
  have hb := successive_differences_geometric_bound u α hα0 hstep
  have hd : Summable (fun n : ℕ => |u 2 - u 1| * α ^ n) :=
    (summable_geometric_of_lt_one hα0 hα1).mul_left _
  have hshift : SequenceCauchy (fun n => u (n + 1)) :=
    sequenceCauchy_of_summable_increments hd (fun n _ => by simpa only [Nat.add_assoc] using hb n)
  exact sequenceCauchy_iff.mpr ((cauchySeq_shift 1).mp (sequenceCauchy_iff.mp hshift))

/-- Bài 2.9.17: dãy co thực hội tụ. -/
theorem convergent_of_contractive_differences (u : ℕ → ℝ) (hu : SequenceHasContractiveDifferences u) :
    IsConvergent u := sequenceCauchy_iff_convergent.mp (sequenceCauchy_of_contractive_differences u hu)


theorem abs_reciprocal_difference (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    |1 / p - 1 / q| = |p - q| / (p * q) := by
  have heq : 1 / p - 1 / q = -(p - q) / (p * q) := by
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos (mul_pos hp hq)]


theorem reciprocal_affine_recurrence_hasContractiveDifferences (u : ℕ → ℝ) (c d b : ℝ) (hb : 1 < b)
    (hden : ∀ n, 1 ≤ n → b ≤ c + u n)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = d + 1 / (c + u n)) :
    SequenceHasContractiveDifferences u := by
  have hb0 : 0 < b := by linarith
  have hb2 : 1 < b ^ 2 := by nlinarith
  refine ⟨1 / b ^ 2, by positivity, (div_lt_iff₀ (by positivity)).2 (by simpa using hb2), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n + 1 := by omega
  have hp : 0 < c + u n := hb0.trans_le (hden n hn)
  have hq : 0 < c + u (n + 1) := hb0.trans_le (hden (n + 1) hn1)
  have hprod : b ^ 2 ≤ (c + u (n + 1)) * (c + u n) := by
    simpa only [pow_two] using mul_le_mul (hden (n + 1) hn1) (hden n hn) hb0.le hq.le
  have heq : u (n + 2) - u (n + 1) =
      1 / (c + u (n + 1)) - 1 / (c + u n) := by
    linarith only [hnext (n + 1) hn1, hnext n hn]
  rw [heq, abs_reciprocal_difference _ _ hq hp]
  rw [show c + u (n + 1) - (c + u n) = u (n + 1) - u n by ring]
  calc
    |u (n + 1) - u n| / ((c + u (n + 1)) * (c + u n)) ≤ |u (n + 1) - u n| / b ^ 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hprod
    _ = 1 / b ^ 2 * |u (n + 1) - u n| := by ring

/-- Bài 2.9.16: công thức dãy với x₁=1, x₂=2. -/
theorem second_order_average_formula (u : ℕ → ℝ) (h1 : u 1 = 1) (h2 : u 2 = 2)
    (hnext : ∀ n, 1 ≤ n → u (n + 2) = (u (n + 1) + u n) / 2) :
    ∀ n, 1 ≤ n → u n = 5 / 3 + (4 / 3) * (-1 / 2 : ℝ) ^ n := by
  have hs : ∀ n : ℕ, u (n + 1) = 5 / 3 + (4 / 3) * (-1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => norm_num [h1]
    | one => norm_num [h2]
    | more n ih ih1 =>
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, hnext (n + 1) (by omega), ih, ih1]
      rw [pow_succ, pow_succ]
      ring
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  exact hs k

/-- Bài 2.9.16(a): khoảng [1,2] bảo toàn qua trung bình cộng. -/
theorem second_order_average_bounds (u : ℕ → ℝ) (h1 : u 1 = 1) (h2 : u 2 = 2)
    (hnext : ∀ n, 1 ≤ n → u (n + 2) = (u (n + 1) + u n) / 2) :
    SequenceBounded u := by
  have hs : ∀ n : ℕ, 1 ≤ u (n + 1) ∧ u (n + 1) ≤ 2 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => norm_num [h1]
    | one => norm_num [h2]
    | more n ih ih1 =>
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, hnext (n + 1) (by omega)]
      constructor <;> linarith [ih.1, ih.2, ih1.1, ih1.2]
  constructor
  · refine ⟨2, ?_⟩
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    exact (hs k).2
  · refine ⟨1, ?_⟩
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    exact (hs k).1

/-- Bài 2.9.16(b): x₁<x₂ và x₃<x₂ nên dãy không đơn điệu. -/
theorem second_order_average_not_monotone (u : ℕ → ℝ) (h1 : u 1 = 1) (h2 : u 2 = 2)
    (hnext : ∀ n, 1 ≤ n → u (n + 2) = (u (n + 1) + u n) / 2) :
    ¬ SequenceMonotonic u := by
  have h3 : u 3 = 3 / 2 := by norm_num [hnext 1 (by omega), h1, h2]
  rintro (hi | hd)
  · have h := hi 2 (by omega); rw [h2, h3] at h; norm_num at h
  · have h := hd 1 (by omega); rw [h1, h2] at h; norm_num at h

/-- Bài 2.9.16(e): giới hạn bằng 5/3. -/
theorem second_order_average_converges (u : ℕ → ℝ) (h1 : u 1 = 1) (h2 : u 2 = 2)
    (hnext : ∀ n, 1 ≤ n → u (n + 2) = (u (n + 1) + u n) / 2) :
    ConvergesTo u (5 / 3) := by
  apply convergesTo_iff_tendsto.mpr
  have hpow : Tendsto (fun n : ℕ => (-1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have h : Tendsto (fun n : ℕ => 5 / 3 + (4 / 3) * (-1 / 2 : ℝ) ^ n) atTop (𝓝 (5 / 3)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hpow)
  apply h.congr'
  exact eventually_atTop.2 ⟨1, fun n hn => (second_order_average_formula u h1 h2 hnext n hn).symm⟩

/-- Bài 2.9.16(c). -/
theorem second_order_average_sequenceCauchy (u : ℕ → ℝ) (h1 : u 1 = 1) (h2 : u 2 = 2)
    (hnext : ∀ n, 1 ≤ n → u (n + 2) = (u (n + 1) + u n) / 2) : SequenceCauchy u :=
  converges_sequenceCauchy (second_order_average_converges u h1 h2 hnext)

/-- Bài 2.9.16(d): dãy con dùng đúng chỉ số 2n+1, với n≥1. -/
theorem second_order_average_odd_converges (u : ℕ → ℝ) (h1 : u 1 = 1) (h2 : u 2 = 2)
    (hnext : ∀ n, 1 ≤ n → u (n + 2) = (u (n + 1) + u n) / 2) :
    ConvergesTo (fun n : ℕ => u (2 * n + 1)) (5 / 3) := by
  apply convergesTo_iff_tendsto.mpr
  have hi : StrictMono (fun n : ℕ => 2 * n + 1) := strictMono_nat_of_lt_succ (fun n => by omega)
  exact (convergesTo_iff_tendsto.mp (second_order_average_converges u h1 h2 hnext)).comp hi.tendsto_atTop

/-- Bài 2.9.15: mọi số hạng dương; từ số hạng thứ hai lớn hơn 2. -/
theorem two_add_inv_recurrence_positive (u : ℕ → ℝ) (h1 : 0 < u 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = 2 + 1 / u n) :
    (∀ n, 1 ≤ n → 0 < u n) ∧ (∀ n, 1 ≤ n → 2 < u (n + 1)) := by
  have hp : ∀ n, 1 ≤ n → 0 < u n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact h1
    | succ n hn ih => rw [hnext n hn]; positivity
  refine ⟨hp, ?_⟩
  intro n hn
  rw [hnext n hn]
  have h := one_div_pos.mpr (hp n hn)
  linarith

/-- Bài 2.9.15: dãy là Cauchy. -/
theorem two_add_inv_recurrence_sequenceCauchy (u : ℕ → ℝ) (h1 : 0 < u 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = 2 + 1 / u n) : SequenceCauchy u := by
  have hb := two_add_inv_recurrence_positive u h1 hnext
  have hc : SequenceHasContractiveDifferences (fun n => u (n + 1)) := by
    apply reciprocal_affine_recurrence_hasContractiveDifferences (fun n => u (n + 1)) 0 2 2 (by norm_num)
    · intro n hn; simpa only [zero_add] using (hb.2 n hn).le
    · intro n hn; simpa only [zero_add] using hnext (n + 1) (by omega)
  exact sequenceCauchy_iff.mpr ((cauchySeq_shift 1).mp
    (sequenceCauchy_iff.mp (sequenceCauchy_of_contractive_differences _ hc)))

/-- Bài 2.9.15: giới hạn bằng 1+√2. -/
theorem two_add_inv_recurrence_converges (u : ℕ → ℝ) (h1 : 0 < u 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = 2 + 1 / u n) :
    ConvergesTo u (1 + Real.sqrt 2) := by
  obtain ⟨a, ha⟩ := sequenceCauchy_iff_convergent.mp (two_add_inv_recurrence_sequenceCauchy u h1 hnext)
  have hb := two_add_inv_recurrence_positive u h1 hnext
  have hshift := successor_converges ha
  have ha2 : 2 ≤ a := limit_le_of_converges (fun _ => 2) (fun n => u (n + 1)) 2 a
    (constant_converges 2) hshift (fun n hn => (hb.2 n hn).le)
  have ht : Tendsto (fun n : ℕ => (u (n + 1) - 2) * u n) atTop (𝓝 ((a - 2) * a)) :=
    ((convergesTo_iff_tendsto.mp hshift).sub tendsto_const_nhds).mul (convergesTo_iff_tendsto.mp ha)
  have hone : Tendsto (fun n => (u (n + 1) - 2) * u n) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hnext n hn]
    field_simp [(hb.1 n hn).ne']
    ring
  have heq : (a - 2) * a = 1 := tendsto_nhds_unique ht hone
  have hsquare : (a - 1) ^ 2 = 2 := by nlinarith
  have hsqrt := Real.sqrt_sq (show 0 ≤ a - 1 by linarith)
  rw [hsquare] at hsqrt
  have hae : a = 1 + Real.sqrt 2 := by linarith
  simpa only [hae] using ha

/-- Bài 2.9.18: khoảng [1,2] bảo toàn, nên mọi mẫu ít nhất 2. -/
theorem fractional_linear_recurrence_bounds (u : ℕ → ℝ) (h1 : u 1 = 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = (2 + u n) / (1 + u n)) :
    ∀ n, 1 ≤ n → 1 ≤ u n ∧ u n ≤ 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih =>
    have hden : 0 < 1 + u n := by linarith
    rw [hnext n hn]
    constructor
    · apply (le_div_iff₀ hden).2; linarith
    · apply (div_le_iff₀ hden).2; linarith

/-- Bài 2.9.18: dãy co với hệ số 1/4. -/
theorem fractional_linear_recurrence_hasContractiveDifferences (u : ℕ → ℝ) (h1 : u 1 = 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = (2 + u n) / (1 + u n)) : SequenceHasContractiveDifferences u := by
  have hb := fractional_linear_recurrence_bounds u h1 hnext
  apply reciprocal_affine_recurrence_hasContractiveDifferences u 1 1 2 (by norm_num)
  · intro n hn; linarith [(hb n hn).1]
  · intro n hn
    rw [hnext n hn]
    have hden : 1 + u n ≠ 0 := by linarith [(hb n hn).1]
    field_simp
    ring

/-- Bài 2.9.18: giới hạn bằng √2. -/
theorem fractional_linear_recurrence_converges (u : ℕ → ℝ) (h1 : u 1 = 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = (2 + u n) / (1 + u n)) :
    ConvergesTo u (Real.sqrt 2) := by
  obtain ⟨a, ha⟩ := convergent_of_contractive_differences u (fractional_linear_recurrence_hasContractiveDifferences u h1 hnext)
  have hb := fractional_linear_recurrence_bounds u h1 hnext
  have hap : 1 ≤ a := limit_le_of_converges (fun _ => 1) u 1 a
    (constant_converges 1) ha (fun n hn => (hb n hn).1)
  have ht : Tendsto (fun n : ℕ => u (n + 1) * (1 + u n)) atTop (𝓝 (a * (1 + a))) :=
    (convergesTo_iff_tendsto.mp (successor_converges ha)).mul
      (tendsto_const_nhds.add (convergesTo_iff_tendsto.mp ha))
  have heqseq : Tendsto (fun n => u (n + 1) * (1 + u n)) atTop (𝓝 (2 + a)) := by
    apply (tendsto_const_nhds.add (convergesTo_iff_tendsto.mp ha)).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hnext n hn]
    have hden : 1 + u n ≠ 0 := by linarith [(hb n hn).1]
    field_simp
  have heq : a * (1 + a) = 2 + a := tendsto_nhds_unique ht heqseq
  have hsquare : a ^ 2 = 2 := by nlinarith
  have hsqrt := Real.sqrt_sq (show 0 ≤ a by linarith)
  rw [hsquare] at hsqrt
  simpa only [hsqrt] using ha

/-- Bài 2.9.20: mọi số hạng thuộc (0,1]. -/
theorem reciprocal_add_two_recurrence_bounds (u : ℕ → ℝ) (h1 : u 1 = 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = 1 / (u n + 2)) :
    ∀ n, 1 ≤ n → 0 < u n ∧ u n ≤ 1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1]
  | succ n hn ih =>
    rw [hnext n hn]
    have hd : 0 < u n + 2 := by linarith
    constructor
    · exact one_div_pos.mpr hd
    · apply (div_le_iff₀ hd).2; linarith

/-- Bài 2.9.20: dãy có tính co. -/
theorem reciprocal_add_two_recurrence_hasContractiveDifferences (u : ℕ → ℝ) (h1 : u 1 = 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = 1 / (u n + 2)) : SequenceHasContractiveDifferences u := by
  have hb := reciprocal_add_two_recurrence_bounds u h1 hnext
  apply reciprocal_affine_recurrence_hasContractiveDifferences u 2 0 2 (by norm_num)
  · intro n hn; linarith [(hb n hn).1]
  · intro n hn; simpa only [zero_add, add_comm] using hnext n hn

/-- Bài 2.9.20: giới hạn dương là √2−1. -/
theorem reciprocal_add_two_recurrence_converges (u : ℕ → ℝ) (h1 : u 1 = 1)
    (hnext : ∀ n, 1 ≤ n → u (n + 1) = 1 / (u n + 2)) :
    ConvergesTo u (Real.sqrt 2 - 1) := by
  obtain ⟨a, ha⟩ := convergent_of_contractive_differences u (reciprocal_add_two_recurrence_hasContractiveDifferences u h1 hnext)
  have hb := reciprocal_add_two_recurrence_bounds u h1 hnext
  have hap : 0 ≤ a := limit_le_of_converges (fun _ => 0) u 0 a
    (constant_converges 0) ha (fun n hn => (hb n hn).1.le)
  have ht : Tendsto (fun n : ℕ => u (n + 1) * (u n + 2)) atTop (𝓝 (a * (a + 2))) :=
    (convergesTo_iff_tendsto.mp (successor_converges ha)).mul
      ((convergesTo_iff_tendsto.mp ha).add tendsto_const_nhds)
  have hone : Tendsto (fun n => u (n + 1) * (u n + 2)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hnext n hn]
    have hd : u n + 2 ≠ 0 := by linarith [(hb n hn).1]
    field_simp
  have heq : a * (a + 2) = 1 := tendsto_nhds_unique ht hone
  have hsquare : (a + 1) ^ 2 = 2 := by nlinarith
  have hsqrt := Real.sqrt_sq (show 0 ≤ a + 1 by linarith)
  rw [hsquare] at hsqrt
  have hae : a = Real.sqrt 2 - 1 := by linarith
  simpa only [hae] using ha

/-- Bài 2.9.19: cận Fibonacci với x₁=x₂=1. -/
theorem fibonacci_recurrence_bounds (F : ℕ → ℝ) (h1 : F 1 = 1) (h2 : F 2 = 1)
    (hnext : ∀ n, 1 ≤ n → F (n + 2) = F (n + 1) + F n) :
    ∀ n, 1 ≤ n → 0 < F n ∧ F n ≤ F (n + 1) ∧ F (n + 1) ≤ 2 * F n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [h1, h2]
  | succ n hn ih =>
    have hp : 0 < F (n + 1) := ih.1.trans_le ih.2.1
    rw [show n + 1 + 1 = n + 2 by omega, hnext n hn]
    exact ⟨hp, by linarith [ih.1], by linarith [ih.2.1]⟩

/-- Tỉ số Fibonacci nằm trong [1/2,1]. -/
theorem fibonacci_ratio_bounds (F : ℕ → ℝ) (h1 : F 1 = 1) (h2 : F 2 = 1)
    (hnext : ∀ n, 1 ≤ n → F (n + 2) = F (n + 1) + F n) :
    ∀ n, 1 ≤ n → 1 / 2 ≤ F n / F (n + 1) ∧ F n / F (n + 1) ≤ 1 := by
  have hb := fibonacci_recurrence_bounds F h1 h2 hnext
  intro n hn
  have hpos : 0 < F (n + 1) := (hb n hn).1.trans_le (hb n hn).2.1
  constructor
  · apply (le_div_iff₀ hpos).2; linarith [(hb n hn).2.2]
  · apply (div_le_iff₀ hpos).2; simpa using (hb n hn).2.1

/-- Bài 2.9.19: truy hồi của yₙ=xₙ/xₙ₊₁. -/
theorem fibonacci_ratio_recurrence (F : ℕ → ℝ) (h1 : F 1 = 1) (h2 : F 2 = 1)
    (hnext : ∀ n, 1 ≤ n → F (n + 2) = F (n + 1) + F n) :
    ∀ n, 1 ≤ n → F (n + 1) / F (n + 1 + 1) = 1 / (1 + F n / F (n + 1)) := by
  have hb := fibonacci_recurrence_bounds F h1 h2 hnext
  intro n hn
  have hnp : 0 < F n := (hb n hn).1
  have hn1p : 0 < F (n + 1) := (hb n hn).1.trans_le (hb n hn).2.1
  rw [show n + 1 + 1 = n + 2 by omega, hnext n hn]
  field_simp

/-- Bài 2.9.19(a): dãy tỉ số là dãy co. -/
theorem fibonacci_ratio_hasContractiveDifferences (F : ℕ → ℝ) (h1 : F 1 = 1) (h2 : F 2 = 1)
    (hnext : ∀ n, 1 ≤ n → F (n + 2) = F (n + 1) + F n) :
    SequenceHasContractiveDifferences (fun n => F n / F (n + 1)) := by
  have hb := fibonacci_ratio_bounds F h1 h2 hnext
  apply reciprocal_affine_recurrence_hasContractiveDifferences (fun n => F n / F (n + 1)) 1 0 (3 / 2) (by norm_num)
  · intro n hn; linarith [(hb n hn).1]
  · intro n hn
    simpa only [zero_add] using fibonacci_ratio_recurrence F h1 h2 hnext n hn

/-- Bài 2.9.19(b): giới hạn của xₙ/xₙ₊₁ là (√5−1)/2. -/
theorem fibonacci_ratio_converges (F : ℕ → ℝ) (h1 : F 1 = 1) (h2 : F 2 = 1)
    (hnext : ∀ n, 1 ≤ n → F (n + 2) = F (n + 1) + F n) :
    ConvergesTo (fun n => F n / F (n + 1)) ((Real.sqrt 5 - 1) / 2) := by
  let y := fun n => F n / F (n + 1)
  obtain ⟨a, ha⟩ := convergent_of_contractive_differences y (fibonacci_ratio_hasContractiveDifferences F h1 h2 hnext)
  have hb := fibonacci_ratio_bounds F h1 h2 hnext
  have hap : 1 / 2 ≤ a := limit_le_of_converges (fun _ => 1 / 2) y (1 / 2) a
    (constant_converges (1 / 2)) ha (fun n hn => (hb n hn).1)
  have hr : ∀ n, 1 ≤ n → y (n + 1) = 1 / (1 + y n) :=
    fibonacci_ratio_recurrence F h1 h2 hnext
  have ht : Tendsto (fun n : ℕ => y (n + 1) * (1 + y n)) atTop (𝓝 (a * (1 + a))) :=
    (convergesTo_iff_tendsto.mp (successor_converges ha)).mul
      (tendsto_const_nhds.add (convergesTo_iff_tendsto.mp ha))
  have hone : Tendsto (fun n => y (n + 1) * (1 + y n)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hr n hn]
    have hden : 1 + y n ≠ 0 := by dsimp [y]; linarith [(hb n hn).1]
    field_simp
  have heq : a * (1 + a) = 1 := tendsto_nhds_unique ht hone
  have hsquare : (2 * a + 1) ^ 2 = 5 := by nlinarith
  have hsqrt := Real.sqrt_sq (show 0 ≤ 2 * a + 1 by linarith)
  rw [hsquare] at hsqrt
  have hae : a = (Real.sqrt 5 - 1) / 2 := by linarith
  simpa only [hae] using ha

end calculus.Chapter02.Section09Supplement
