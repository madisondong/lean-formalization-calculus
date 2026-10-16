import calculus.Chapter02.Section06
import calculus.Chapter02.Section05

/-!
# Bài 2.6.8–11 và 15: truy hồi phi tuyến

Nguồn: `source/Ch2_dayso.tex`, dòng 2044–2054 và 2081–2083.
-/

namespace calculus.Chapter02.Section06Recurrences

open Filter Set
open scoped Topology


theorem recurrence_limit_equation {u : ℕ → ℝ} {a : ℝ} {f : ℝ → ℝ}
    (hu : Section03.ConvergesTo u a) (hf : Continuous f)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = f (u n)) : a = f a := by
  have hleft := Section03.convergesTo_iff_tendsto.mp (Section03.successor_converges hu)
  have hright := (hf.tendsto a).comp (Section03.convergesTo_iff_tendsto.mp hu)
  exact tendsto_nhds_unique
    (hleft.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ hnext n hn⟩)) hright

/-- Bài 2.6.8: bất đẳng thức tích buộc từng bước giảm ngặt. -/
theorem product_gap_strict_decrease (u : ℕ → ℝ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < u n)
    (hgap : ∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 4 < u n * (1 - u (n + 1))) :
    ∀ n : ℕ, 1 ≤ n → u (n + 1) < u n := by
  intro n hn
  have hm : u n * u (n + 1) < u n * u n := by
    nlinarith [hgap n hn, sq_nonneg (u n - 1 / 2)]
  exact (mul_lt_mul_iff_right₀ (hpos n hn)).mp (by simpa [mul_comm] using hm)

/-- Bài 2.6.8: giới hạn bằng 1/2. -/
theorem product_gap_converges_half (u : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → 0 < u n ∧ u n < 1)
    (hgap : ∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 4 < u n * (1 - u (n + 1))) :
    Section03.ConvergesTo u (1 / 2) := by
  have hdec : Section06.SequenceDecreasing u :=
    fun n hn ↦ (product_gap_strict_decrease u (fun n hn ↦ (hbound n hn).1) hgap n hn).le
  obtain ⟨a, ha⟩ := Section06.decreasing_bounded_convergent u hdec
    ⟨0, fun n hn ↦ (hbound n hn).1.le⟩
  have ht := Section03.convergesTo_iff_tendsto.mp ha
  have hs := Section03.convergesTo_iff_tendsto.mp (Section03.successor_converges ha)
  have hp : Section03.ConvergesTo (fun n ↦ u n * (1 - u (n + 1))) (a * (1 - a)) :=
    Section03.convergesTo_iff_tendsto.mpr (ht.mul (tendsto_const_nhds.sub hs))
  have hb := Section04.limit_le_of_converges (fun _ ↦ (1 : ℝ) / 4)
    (fun n ↦ u n * (1 - u (n + 1))) (1 / 4) (a * (1 - a))
    (Section03.constant_converges _) hp (fun n hn ↦ (hgap n hn).le)
  have heq : a = 1 / 2 := by nlinarith [sq_nonneg (a - 1 / 2)]
  simpa only [heq] using ha

/-- Bài 2.6.9: mọi số hạng thuộc (0,1). -/
theorem one_sub_sqrt_bounds (u : ℕ → ℝ) (hfirst : 0 < u 1 ∧ u 1 < 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 - √(1 - u n)) :
    ∀ n : ℕ, 1 ≤ n → 0 < u n ∧ u n < 1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hfirst
  | succ n hn ih =>
    rw [hnext n hn]
    have hs := Real.sqrt_pos.mpr (by linarith [ih.2] : 0 < 1 - u n)
    have hu := (Real.sqrt_lt (by linarith [ih.2] : 0 ≤ 1 - u n)
      (by norm_num : (0 : ℝ) ≤ 1)).mpr (by linarith [ih.1] : 1 - u n < 1 ^ 2)
    constructor <;> linarith

/-- Bài 2.6.9: dãy giảm. -/
theorem one_sub_sqrt_decreasing (u : ℕ → ℝ) (hfirst : 0 < u 1 ∧ u 1 < 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 - √(1 - u n)) :
    Section06.SequenceDecreasing u := by
  intro n hn
  obtain ⟨hp, hu⟩ := one_sub_sqrt_bounds u hfirst hnext n hn
  have hs : 1 - u n ≤ √(1 - u n) := Real.le_sqrt_of_sq_le (by
    nlinarith [mul_nonneg hp.le (by linarith : 0 ≤ 1 - u n)])
  rw [hnext n hn]
  linarith

/-- Bài 2.6.9: giới hạn số hạng bằng 0. -/
theorem one_sub_sqrt_converges_zero (u : ℕ → ℝ) (hfirst : 0 < u 1 ∧ u 1 < 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 - √(1 - u n)) :
    Section03.ConvergesTo u 0 := by
  have hb := one_sub_sqrt_bounds u hfirst hnext
  have hd := one_sub_sqrt_decreasing u hfirst hnext
  obtain ⟨a, ha⟩ := Section06.decreasing_bounded_convergent u hd
    ⟨0, fun n hn ↦ (hb n hn).1.le⟩
  have hm := (Section06.sequenceDecreasing_iff_antitoneOn u).mp hd
  have hau : a ≤ u 1 := Section04.limit_le_of_converges u (fun _ ↦ u 1) a (u 1)
    ha (Section03.constant_converges _) (fun n hn ↦ hm (by simp) hn hn)
  have heq := recurrence_limit_equation ha (by fun_prop : Continuous (fun x : ℝ ↦ 1 - √(1 - x))) hnext
  have hs := Real.sq_sqrt (by linarith [hfirst.2] : 0 ≤ 1 - a)
  have hr : √(1 - a) = 1 - a := by linarith
  rw [hr] at hs
  have hfactor : a * (a - 1) = 0 := by nlinarith
  have ha0 : a = 0 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact h
    · linarith [hfirst.2]
  simpa only [ha0] using ha

/-- Bài 2.6.9: dạng hữu tỉ hóa của tỉ số liên tiếp. -/
theorem one_sub_sqrt_ratio_eq (u : ℕ → ℝ) (hfirst : 0 < u 1 ∧ u 1 < 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 - √(1 - u n))
    (n : ℕ) (hn : 1 ≤ n) : u (n + 1) / u n = 1 / (1 + √(1 - u n)) := by
  obtain ⟨hp, hu⟩ := one_sub_sqrt_bounds u hfirst hnext n hn
  apply (div_eq_div_iff (ne_of_gt hp) (by positivity : 1 + √(1 - u n) ≠ 0)).mpr
  rw [hnext n hn]
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - u n)
  nlinarith

/-- Bài 2.6.9: giới hạn tỉ số bằng 1/2 dù giới hạn số hạng là 0. -/
theorem one_sub_sqrt_ratio_converges (u : ℕ → ℝ) (hfirst : 0 < u 1 ∧ u 1 < 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 - √(1 - u n)) :
    Section03.ConvergesTo (fun n ↦ u (n + 1) / u n) (1 / 2) := by
  have ht := Section03.convergesTo_iff_tendsto.mp (one_sub_sqrt_converges_zero u hfirst hnext)
  have hr : Tendsto (fun n ↦ 1 / (1 + √(1 - u n))) atTop (𝓝 (1 / 2 : ℝ)) := by
    convert! (tendsto_const_nhds (x := (1 : ℝ))).div
      (tendsto_const_nhds.add (tendsto_const_nhds.sub ht).sqrt) (by norm_num : 1 + √(1 - (0 : ℝ)) ≠ 0)
    norm_num
  exact Section03.convergesTo_iff_tendsto.mpr
    (hr.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ (one_sub_sqrt_ratio_eq u hfirst hnext n hn).symm⟩))

/-- Bài 2.6.10: 0<xₙ≤3. -/
theorem sqrt_twice_add_three_bounds (u : ℕ → ℝ) (hfirst : 0 < u 1 ∧ u 1 ≤ 3)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(2 * u n + 3)) :
    ∀ n : ℕ, 1 ≤ n → 0 < u n ∧ u n ≤ 3 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hfirst
  | succ n hn ih =>
    rw [hnext n hn]
    exact ⟨Real.sqrt_pos.mpr (by linarith [ih.1]),
      (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3)).mpr (by linarith [ih.2])⟩

/-- Bài 2.6.10: dãy tăng. -/
theorem sqrt_twice_add_three_increasing (u : ℕ → ℝ) (hfirst : 0 < u 1 ∧ u 1 ≤ 3)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(2 * u n + 3)) :
    Section06.SequenceIncreasing u := by
  intro n hn
  obtain ⟨hp, hu⟩ := sqrt_twice_add_three_bounds u hfirst hnext n hn
  rw [hnext n hn]
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_nonneg (by linarith : 0 ≤ 3 - u n) (by linarith : 0 ≤ u n + 1)]

/-- Bài 2.6.10: giới hạn bằng 3. -/
theorem sqrt_twice_add_three_converges (u : ℕ → ℝ) (hfirst : 0 < u 1 ∧ u 1 ≤ 3)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(2 * u n + 3)) :
    Section03.ConvergesTo u 3 := by
  have hb := sqrt_twice_add_three_bounds u hfirst hnext
  obtain ⟨a, ha⟩ := Section06.increasing_bounded_convergent u
    (sqrt_twice_add_three_increasing u hfirst hnext) ⟨3, fun n hn ↦ (hb n hn).2⟩
  have hn : 0 ≤ a := Section04.limit_le_of_converges (fun _ ↦ 0) u 0 a
    (Section03.constant_converges _) ha (fun n hn ↦ (hb n hn).1.le)
  have heq := recurrence_limit_equation ha (by fun_prop : Continuous (fun x : ℝ ↦ √(2 * x + 3))) hnext
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 2 * a + 3)
  rw [← heq] at hs
  have hfactor : (a - 3) * (a + 1) = 0 := by nlinarith
  have he : a = 3 := by rcases mul_eq_zero.mp hfactor with h | h <;> linarith
  simpa only [he] using ha

/-- Bài 2.6.11: dãy giảm và có số hạng trong [2,+∞). -/
theorem one_add_sqrt_above_two (u : ℕ → ℝ) (hfirst : 2 ≤ u 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 + √(u n - 1)) :
    (∀ n : ℕ, 1 ≤ n → 2 ≤ u n) ∧ Section06.SequenceDecreasing u := by
  have hb : ∀ n : ℕ, 1 ≤ n → 2 ≤ u n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hfirst
    | succ n hn ih =>
      rw [hnext n hn]
      have hs : 1 ≤ √(u n - 1) := Real.le_sqrt_of_sq_le (by linarith)
      linarith
  refine ⟨hb, fun n hn ↦ ?_⟩
  rw [hnext n hn]
  have hs : √(u n - 1) ≤ u n - 1 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [hb n hn]))
  linarith

/-- Bài 2.6.11: với x₁≥2, giới hạn bằng 2. -/
theorem one_add_sqrt_above_two_converges (u : ℕ → ℝ) (hfirst : 2 ≤ u 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 + √(u n - 1)) :
    Section03.ConvergesTo u 2 := by
  obtain ⟨hb, hd⟩ := one_add_sqrt_above_two u hfirst hnext
  obtain ⟨a, ha⟩ := Section06.decreasing_bounded_convergent u hd ⟨2, hb⟩
  have hlow : 2 ≤ a := Section04.limit_le_of_converges (fun _ ↦ 2) u 2 a
    (Section03.constant_converges _) ha hb
  have heq := recurrence_limit_equation ha (by fun_prop : Continuous (fun x : ℝ ↦ 1 + √(x - 1))) hnext
  have hs := Real.sq_sqrt (by linarith : 0 ≤ a - 1)
  have hr : √(a - 1) = a - 1 := by linarith
  rw [hr] at hs
  have hfactor : (a - 1) * (a - 2) = 0 := by nlinarith
  have he : a = 2 := by rcases mul_eq_zero.mp hfactor with h | h <;> linarith
  simpa only [he] using ha

/-- Bài 2.6.11: tại x₁=1, mọi số hạng đều bằng 1. -/
theorem one_add_sqrt_initial_one_constant (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 + √(u n - 1)) :
    ∀ n : ℕ, 1 ≤ n → u n = 1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hfirst
  | succ n hn ih => rw [hnext n hn, ih]; norm_num

/-- Bài 2.6.11: dãy tăng và có số hạng trong (1,2). -/
theorem one_add_sqrt_below_two (u : ℕ → ℝ) (hfirst : 1 < u 1 ∧ u 1 < 2)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 + √(u n - 1)) :
    (∀ n : ℕ, 1 ≤ n → 1 < u n ∧ u n < 2) ∧ Section06.SequenceIncreasing u := by
  have hb : ∀ n : ℕ, 1 ≤ n → 1 < u n ∧ u n < 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hfirst
    | succ n hn ih =>
      rw [hnext n hn]
      have hp := Real.sqrt_pos.mpr (by linarith [ih.1] : 0 < u n - 1)
      have hu := (Real.sqrt_lt (by linarith [ih.1] : 0 ≤ u n - 1)
        (by norm_num : (0 : ℝ) ≤ 1)).mpr (by linarith [ih.2] : u n - 1 < 1 ^ 2)
      constructor <;> linarith
  refine ⟨hb, fun n hn ↦ ?_⟩
  rw [hnext n hn]
  obtain ⟨hl, hu⟩ := hb n hn
  have hs : u n - 1 ≤ √(u n - 1) := Real.le_sqrt_of_sq_le (by
    nlinarith [mul_nonneg (by linarith : 0 ≤ u n - 1) (by linarith : 0 ≤ 2 - u n)])
  linarith

/-- Bài 2.6.11: với 1<x₁<2, giới hạn bằng 2. -/
theorem one_add_sqrt_below_two_converges (u : ℕ → ℝ) (hfirst : 1 < u 1 ∧ u 1 < 2)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 + √(u n - 1)) :
    Section03.ConvergesTo u 2 := by
  obtain ⟨hb, hi⟩ := one_add_sqrt_below_two u hfirst hnext
  obtain ⟨a, ha⟩ := Section06.increasing_bounded_convergent u hi
    ⟨2, fun n hn ↦ (hb n hn).2.le⟩
  have hm := (Section06.sequenceIncreasing_iff_monotoneOn u).mp hi
  have hlow : u 1 ≤ a := Section04.limit_le_of_converges (fun _ ↦ u 1) u (u 1) a
    (Section03.constant_converges _) ha (fun n hn ↦ hm (by simp) hn hn)
  have heq := recurrence_limit_equation ha (by fun_prop : Continuous (fun x : ℝ ↦ 1 + √(x - 1))) hnext
  have hs := Real.sq_sqrt (by linarith [hfirst.1] : 0 ≤ a - 1)
  have hr : √(a - 1) = a - 1 := by linarith
  rw [hr] at hs
  have hfactor : (a - 1) * (a - 2) = 0 := by nlinarith
  have he : a = 2 := by rcases mul_eq_zero.mp hfactor with h | h <;> linarith [hfirst.1]
  simpa only [he] using ha

/-- Bài 2.6.11: giới hạn theo giá trị đầu x₁∈[1,2). -/
theorem one_add_sqrt_initial_below_two_converges (u : ℕ → ℝ)
    (hfirst : 1 ≤ u 1 ∧ u 1 < 2)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = 1 + √(u n - 1)) :
    Section03.ConvergesTo u (if u 1 = 1 then 1 else 2) := by
  split_ifs with h
  · exact (Section03.convergesTo_eventually_congr 1
      (one_add_sqrt_initial_one_constant u h hnext)).mpr (Section03.constant_converges 1)
  · exact one_add_sqrt_below_two_converges u ⟨lt_of_le_of_ne hfirst.1 (Ne.symm h), hfirst.2⟩ hnext

/-- Bài 2.6.15: mọi số hạng thuộc [√2,2]. -/
theorem nested_sqrt_bounds (u : ℕ → ℝ) (hfirst : u 1 = √(2 : ℝ))
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(2 + √(u n))) :
    ∀ n : ℕ, 1 ≤ n → √(2 : ℝ) ≤ u n ∧ u n ≤ 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [hfirst]
    exact ⟨le_rfl, (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num)⟩
  | succ n hn ih =>
    rw [hnext n hn]
    constructor
    · exact Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg (u n)])
    · have hs : √(u n) ≤ 2 :=
        (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr (by linarith [ih.2])
      exact (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr (by linarith)

/-- Bài 2.6.15: dãy căn lồng tăng. -/
theorem nested_sqrt_increasing (u : ℕ → ℝ) (hfirst : u 1 = √(2 : ℝ))
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(2 + √(u n))) :
    Section06.SequenceIncreasing u := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [hnext 1 le_rfl, hfirst]
    exact Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg (√(2 : ℝ))])
  | succ n hn ih =>
    calc
      u (n + 1) = √(2 + √(u n)) := hnext n hn
      _ ≤ √(2 + √(u (n + 1))) :=
        Real.sqrt_le_sqrt (by linarith [Real.sqrt_le_sqrt ih])
      _ = u (n + 1 + 1) := (hnext (n + 1) (by omega)).symm

/-- Phương trình căn lồng có duy nhất một nghiệm trên [1,+∞). -/
theorem nested_sqrt_equation_unique {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hea : a ^ 2 = 2 + √a) (heb : b ^ 2 = 2 + √b) : a = b := by
  have no_lt (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y)
      (hex : x ^ 2 = 2 + √x) (hey : y ^ 2 = 2 + √y) : ¬ x < y := by
    intro hxy
    have hsx : 1 ≤ √x := Real.le_sqrt_of_sq_le (by linarith)
    have hsy : 1 ≤ √y := Real.le_sqrt_of_sq_le (by linarith)
    have hd : 0 ≤ √y - √x := sub_nonneg.mpr (Real.sqrt_le_sqrt hxy.le)
    have hroot : 2 * (√y - √x) ≤ y - x := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x),
        Real.sq_sqrt (by linarith : 0 ≤ y),
        mul_nonneg hd (by linarith : 0 ≤ √y + √x - 2)]
    have hsquare : 2 * (y - x) ≤ √y - √x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy.le) (by linarith : 0 ≤ y + x - 2)]
    linarith
  exact le_antisymm (le_of_not_gt (no_lt b a hb ha heb hea))
    (le_of_not_gt (no_lt a b ha hb hea heb))

/-- Bài 2.6.15: giới hạn là nghiệm duy nhất a∈[√2,2] của a²=2+√a; cũng thỏa a⁴−4a²−a+4=0. -/
theorem nested_sqrt_converges_unique_root (u : ℕ → ℝ) (hfirst : u 1 = √(2 : ℝ))
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = √(2 + √(u n))) :
    ∃ a : ℝ, a ∈ Icc (√(2 : ℝ)) 2 ∧ Section03.ConvergesTo u a ∧
      a ^ 2 = 2 + √a ∧ a ^ 4 - 4 * a ^ 2 - a + 4 = 0 ∧
      ∀ b : ℝ, b ∈ Icc (√(2 : ℝ)) 2 → b ^ 2 = 2 + √b → b = a := by
  have hb := nested_sqrt_bounds u hfirst hnext
  obtain ⟨a, ha⟩ := Section06.increasing_bounded_convergent u
    (nested_sqrt_increasing u hfirst hnext) ⟨2, fun n hn ↦ (hb n hn).2⟩
  have hal : √(2 : ℝ) ≤ a := Section04.limit_le_of_converges (fun _ ↦ √(2 : ℝ)) u
    (√(2 : ℝ)) a (Section03.constant_converges _) ha (fun n hn ↦ (hb n hn).1)
  have hau : a ≤ 2 := Section04.limit_le_of_converges u (fun _ ↦ 2) a 2 ha
    (Section03.constant_converges _) (fun n hn ↦ (hb n hn).2)
  have ha1 : 1 ≤ a := (Real.le_sqrt_of_sq_le (by norm_num : (1 : ℝ) ^ 2 ≤ 2)).trans hal
  have heq := recurrence_limit_equation ha
    (by fun_prop : Continuous (fun x : ℝ ↦ √(2 + √x))) hnext
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 + √a)
  rw [← heq] at hs
  have hpoly : a ^ 4 - 4 * a ^ 2 - a + 4 = 0 := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ a), sq_nonneg (a ^ 2 - 2 - √a)]
  refine ⟨a, ⟨hal, hau⟩, ha, hs, hpoly, fun b hb hbe ↦ ?_⟩
  have hb1 : 1 ≤ b := (Real.le_sqrt_of_sq_le (by norm_num : (1 : ℝ) ^ 2 ≤ 2)).trans hb.1
  exact nested_sqrt_equation_unique hb1 ha1 hbe hs

end calculus.Chapter02.Section06Recurrences
