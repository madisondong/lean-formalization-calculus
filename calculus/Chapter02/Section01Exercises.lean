import calculus.Chapter02.Section01
import calculus.Chapter01.Section04
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.Order.Group.Pointwise.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
# 2.1. Bài tập bổ sung

Nguồn: `source/Ch2_dayso.tex`, dòng 225 và 272–585.
-/

namespace calculus.Chapter02.Section01Exercises

open calculus.Chapter02.Section01
open scoped BigOperators
open scoped Pointwise

/-- Dòng 225: tập đối là ảnh của phép đổi dấu. -/
theorem negated_set_membership (A : Set ℝ) (x : ℝ) :
    x ∈ -A ↔ ∃ a ∈ A, -a = x := by
  constructor
  · intro hx
    exact ⟨-x, Set.mem_neg.mp hx, neg_neg x⟩
  · rintro ⟨a, ha, rfl⟩
    exact Set.neg_mem_neg.mpr ha

/-- Ví dụ 2.1.20: tập nghịch đảo của các số tự nhiên dương. -/
def positiveReciprocals : Set ℝ := {x | ∃ n : ℕ, 0 < n ∧ x = 1 / (n : ℝ)}

/-- Ví dụ 2.1.20: phần tử lớn nhất và cận trên bé nhất bằng 1, cận dưới lớn nhất bằng 0; không có phần tử nhỏ nhất. -/
theorem positiveReciprocals_extrema :
    IsGreatest positiveReciprocals 1 ∧ IsLUB positiveReciprocals 1 ∧
    IsGLB positiveReciprocals 0 ∧ (¬ ∃ x, IsLeast positiveReciprocals x) := by
  have hnonempty : positiveReciprocals.Nonempty := ⟨1, 1, by decide, by norm_num⟩
  have hpos : ∀ x ∈ positiveReciprocals, 0 < x := by
    rintro x ⟨n, hn, rfl⟩
    exact one_div_pos.mpr (Nat.cast_pos.mpr hn)
  have hgreatest : IsGreatest positiveReciprocals 1 := by
    refine ⟨⟨1, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
    simpa only [one_mul] using (Nat.one_le_cast.mpr hn)
  have hglb : IsGLB positiveReciprocals 0 := by
    apply (greatestLowerBound_iff_epsilon positiveReciprocals 0 hnonempty
      ⟨0, fun x hx ↦ (hpos x hx).le⟩).mpr
    refine ⟨fun x hx ↦ (hpos x hx).le, ?_⟩
    intro ε hε
    obtain ⟨n, hn, hsmall⟩ := exists_positive_nat_reciprocal_lt hε
    exact ⟨1 / (n : ℝ), ⟨n, hn, rfl⟩, by simpa using hsmall⟩
  refine ⟨hgreatest, hgreatest.isLUB, hglb, ?_⟩
  rintro ⟨x, hx⟩
  have heq := hx.isGLB.unique hglb
  exact (ne_of_gt (hpos x hx.1)) heq

/-- Bài tập 2.1.4(e): phần nguyên của tích với một số tự nhiên dương. -/
theorem floor_nat_mul_bounds (x : ℝ) (n : ℕ) (hn : 0 < n) :
    (n : ℤ) * ⌊x⌋ ≤ ⌊(n : ℝ) * x⌋ ∧
    ⌊(n : ℝ) * x⌋ ≤ (n : ℤ) * ⌊x⌋ + n - 1 := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  constructor
  · apply Int.le_floor.mpr
    push_cast
    exact mul_le_mul_of_nonneg_left (Int.floor_le x) hnreal.le
  · have h : (n : ℝ) * x < (n : ℝ) * ((⌊x⌋ : ℝ) + 1) :=
      mul_lt_mul_of_pos_left (Int.lt_floor_add_one x) hnreal
    have hfloor : ⌊(n : ℝ) * x⌋ < (n : ℤ) * ⌊x⌋ + n := by
      apply Int.floor_lt.mpr
      push_cast
      simpa only [mul_add, mul_one] using h
    omega

/-- Bài tập 2.1.5(a): công thức tổng từ 1 đến n. -/
theorem sum_consecutive_products (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * (k + 2)) =
      (n : ℝ) * (n + 1) * (n + 2) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.5(b), tích ba số liên tiếp. -/
theorem sum_three_consecutive_products (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * (k + 2) * (k + 3)) =
      (n : ℝ) * (n + 1) * (n + 2) * (n + 3) / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.6(a), tổng các số tự nhiên đầu tiên. -/
theorem sum_first_naturals (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1)) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.6(b), tổng bình phương. -/
theorem sum_squares (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 2) =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.6(c), tổng lập phương. -/
theorem sum_cubes (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 3) = ((n : ℝ) * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.6(d), tổng lũy thừa bậc bốn. -/
theorem sum_fourth_powers (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 4) =
      (n : ℝ) * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) / 30 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.6(e), tổng lũy thừa bậc năm. -/
theorem sum_fifth_powers (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 5) =
      (n : ℝ) ^ 2 * (n + 1) ^ 2 * (2 * n ^ 2 + 2 * n - 1) / 12 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.6(f), tổng n số lẻ đầu tiên. -/
theorem sum_first_odds (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1)) = (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.6(g), tổng bình phương n số lẻ đầu tiên. -/
theorem sum_odd_squares (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1) ^ 2) =
      (n : ℝ) * (4 * n ^ 2 - 1) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bài tập 2.1.6(h): bất đẳng thức tam giác cho tổng hữu hạn. -/
theorem absoluteValue_sum_le (n : ℕ) (a : ℕ → ℝ) :
    |∑ k ∈ Finset.range n, a (k + 1)| ≤ ∑ k ∈ Finset.range n, |a (k + 1)| :=
  Finset.abs_sum_le_sum_abs _ _

/-- Bài tập 2.1.10: so sánh các phần tử của hai tập để suy ra quan hệ giữa các cận. -/
theorem supremum_le_infimum {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) : sSup A ≤ sInf B := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have hbddA : BddAbove A := ⟨b₀, fun a ha ↦ hcross a ha b₀ hb₀⟩
  have hbddB : BddBelow B := ⟨a₀, fun b hb ↦ hcross a₀ ha₀ b hb⟩
  have hlub := Real.isLUB_sSup ⟨a₀, ha₀⟩ hbddA
  have hglb := Real.isGLB_sInf ⟨b₀, hb₀⟩ hbddB
  exact hglb.2 (fun b hb ↦ hlub.2 (fun a ha ↦ hcross a ha b hb))

/-- Nhận xét 2.1.30: có vô hạn số hữu tỉ trong mỗi khoảng mở khác rỗng. -/
theorem rationals_between_infinite {a b : ℝ} (hab : a < b) :
    {q : ℚ | a < (q : ℝ) ∧ (q : ℝ) < b}.Infinite := by
  intro hfinite
  obtain ⟨q₀, hq₀⟩ := rational_between hab
  obtain ⟨q, hq, hmax⟩ := Set.exists_max_image
    {q : ℚ | a < (q : ℝ) ∧ (q : ℝ) < b}
    (fun q : ℚ ↦ (q : ℝ)) hfinite ⟨q₀, hq₀⟩
  obtain ⟨r, hqr, hrb⟩ := rational_between hq.2
  exact (not_le.mpr hqr) (hmax r ⟨hq.1.trans hqr, hrb⟩)

/-- Định lí 2.1.31: có vô hạn số vô tỉ trong mỗi khoảng mở khác rỗng. -/
theorem irrationals_between_infinite {a b : ℝ} (hab : a < b) :
    {x : ℝ | Irrational x ∧ a < x ∧ x < b}.Infinite := by
  intro hfinite
  obtain ⟨x₀, hx₀⟩ := irrational_between hab
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image
    {x : ℝ | Irrational x ∧ a < x ∧ x < b}
    (fun x : ℝ ↦ x) hfinite ⟨x₀, hx₀⟩
  obtain ⟨y, hyirr, hxy, hyb⟩ := irrational_between hx.2.2
  exact (not_le.mpr hxy) (hmax y ⟨hyirr, hx.2.1.trans hxy, hyb⟩)

/-- Ví dụ 2.1.28: mỗi số tự nhiên lớn hơn 1 là tích các số nguyên tố, cho phép lặp thừa số. -/
theorem prime_or_product_of_primes (n : ℕ) (hn : 1 < n) :
    Nat.Prime n ∨ ∃ factors : List ℕ, factors ≠ [] ∧
      (∀ p ∈ factors, Nat.Prime p) ∧ factors.prod = n := by
  right
  refine ⟨n.primeFactorsList, ?_, fun _ hp ↦ Nat.prime_of_mem_primeFactorsList hp,
    Nat.prod_primeFactorsList (by omega)⟩
  intro hnil
  have h := (Nat.primeFactorsList_eq_nil n).mp hnil
  omega

/-- Bài tập 2.1.7: hệ số nhị thức bằng thương giai thừa khi k≤n. -/
theorem binomial_coefficient_factorial (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) = (n.factorial : ℝ) /
      (((n - k).factorial : ℝ) * (k.factorial : ℝ)) := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_mul_factorial_mul_factorial hk)
  push_cast at h
  apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))).mpr
  nlinarith only [h]

/-- Bài tập 2.1.7: khai triển Newton với số hạng aⁿ⁻ᵏbᵏ. -/
theorem newton_binomial (a b : ℝ) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * a ^ (n - k) * b ^ k := by
  rw [add_comm a b, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Bài tập 2.1.11: cận trên bé nhất và cận dưới lớn nhất của tổng, hiệu hai tập không rỗng, bị chặn; hiệu là {a−b : a∈A, b∈B}. -/
theorem sup_inf_of_set_add_sub {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAu : BddAbove A) (hAl : BddBelow A) (hBu : BddAbove B) (hBl : BddBelow B) :
    sSup (A + B) = sSup A + sSup B ∧ sInf (A + B) = sInf A + sInf B ∧
    sSup (A - B) = sSup A - sInf B ∧ sInf (A - B) = sInf A - sSup B := by
  have hsum : (A + B).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨a + b, Set.mem_add.mpr ⟨a, ha, b, hb, rfl⟩⟩
  have hdiff : (A - B).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨a - b, Set.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩⟩
  have hsupA := Real.isLUB_sSup hA hAu
  have hinfA := Real.isGLB_sInf hA hAl
  have hsupB := Real.isLUB_sSup hB hBu
  have hinfB := Real.isGLB_sInf hB hBl
  exact ⟨(hsupA.add hsupB).csSup_eq hsum, (hinfA.add hinfB).csInf_eq hsum,
    (hsupA.sub hinfB).csSup_eq hdiff, (hinfA.sub hsupB).csInf_eq hdiff⟩

/-- Bài tập 2.1.11: điều kiện thuộc tổng và hiệu của hai tập. -/
theorem set_add_sub_membership (A B : Set ℝ) (x : ℝ) :
    (x ∈ A + B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = x) ∧
    (x ∈ A - B ↔ ∃ a ∈ A, ∃ b ∈ B, a - b = x) :=
  ⟨Set.mem_add, Set.mem_sub⟩

/-- Bài tập 2.1.5(c): dạng nhân của công thức tổng tích p thừa số liên tiếp. -/
theorem sum_ascending_products_mul (n p : ℕ) :
    ((p : ℝ) + 1) * (∑ k ∈ Finset.range n, ((k + 1).ascFactorial p : ℝ)) =
      (n : ℝ) * ((n + 1).ascFactorial p : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_ascFactorial (n + 1) p)
    push_cast at h ⊢
    nlinarith only [h]

/-- Bài tập 2.1.5(c): công thức tổng các tích r(r+1)…(r+p−1), với p>0. -/
theorem sum_ascending_products (n p : ℕ) (_hp : 0 < p) :
    (∑ k ∈ Finset.range n, ((k + 1).ascFactorial p : ℝ)) =
      (n : ℝ) * ((n + 1).ascFactorial p : ℝ) / ((p : ℝ) + 1) := by
  apply (eq_div_iff (by positivity)).mpr
  simpa only [mul_comm] using sum_ascending_products_mul n p

/-- Tập hữu tỉ trong Mệnh đề 2.1.32. -/
def positiveRationalsSquareLtTwo : Set ℚ := {q | 0 < q ∧ q ^ 2 < 2}

/-- Với x>0, x²<2 khi và chỉ khi x<√2. -/
theorem positiveRationalsSquareLtTwo_iff (q : ℚ) :
    q ∈ positiveRationalsSquareLtTwo ↔ 0 < (q : ℝ) ∧ (q : ℝ) < Real.sqrt 2 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  change (0 < q ∧ q ^ 2 < 2) ↔ _
  constructor
  · intro h
    have hq : 0 < (q : ℝ) := by exact_mod_cast h.1
    have hsq : (q : ℝ) ^ 2 < 2 := by exact_mod_cast h.2
    exact ⟨hq, by nlinarith⟩
  · intro h
    constructor
    · exact_mod_cast h.1
    · have hsq : (q : ℝ) ^ 2 < 2 := by nlinarith
      exact_mod_cast hsq

/-- Mệnh đề 2.1.32: tập hữu tỉ khác rỗng bị chặn có cận trên bé nhất vô tỉ trong ℝ. -/
theorem rational_set_has_irrational_real_supremum :
    positiveRationalsSquareLtTwo.Nonempty ∧ BddAbove positiveRationalsSquareLtTwo ∧
    IsLUB ((Rat.cast : ℚ → ℝ) '' positiveRationalsSquareLtTwo) (Real.sqrt 2) ∧
    Irrational (Real.sqrt 2) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have htwo : Real.sqrt 2 < 2 := by nlinarith
  have hne : positiveRationalsSquareLtTwo.Nonempty := ⟨1, by norm_num [positiveRationalsSquareLtTwo]⟩
  have hupper : Real.sqrt 2 ∈ upperBounds
      ((Rat.cast : ℚ → ℝ) '' positiveRationalsSquareLtTwo) := by
    rintro x ⟨q, hq, rfl⟩
    exact ((positiveRationalsSquareLtTwo_iff q).mp hq).2.le
  refine ⟨hne, ⟨2, ?_⟩, ?_, irrational_sqrt_two⟩
  · intro q hq
    have hqreal := ((positiveRationalsSquareLtTwo_iff q).mp hq).2.le.trans htwo.le
    exact_mod_cast hqreal
  · apply (leastUpperBound_iff_epsilon _ (Real.sqrt 2)
      (hne.image _) ⟨Real.sqrt 2, hupper⟩).mpr
    refine ⟨hupper, ?_⟩
    intro ε hε
    have hmax : max 0 (Real.sqrt 2 - ε) < Real.sqrt 2 := max_lt hpos (by linarith)
    obtain ⟨q, hqlo, hqhi⟩ := rational_between hmax
    refine ⟨q, ⟨q, (positiveRationalsSquareLtTwo_iff q).mpr
      ⟨(le_max_left _ _).trans_lt hqlo, hqhi⟩, rfl⟩, ?_⟩
    exact (le_max_right _ _).trans_lt hqlo

/-- Bài tập 2.1.12(a): giao các khoảng (−1/n,1/n) là {0}. -/
theorem shrinking_interval_intersection :
    (⋂ n : ℕ+, Set.Ioo (-(1 / (n : ℕ)) : ℝ) (1 / (n : ℕ))) = {0} :=
  calculus.Chapter01.Section04.shrinking_open_intervals_union_inter.2

/-- Bài tập 2.1.12(b): không có số thực lớn hơn mọi số tự nhiên dương. -/
theorem positive_tail_interval_intersection :
    (⋂ n : ℕ+, Set.Ici ((n : ℕ) : ℝ)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨m, hm, hlarge⟩ := exists_positive_nat_gt x
  let n : ℕ+ := ⟨m, hm⟩
  have h := Set.mem_iInter.mp hx n
  exact (not_le.mpr hlarge) h

/-- Bài tập 2.1.12(c): hợp các đoạn [1/n,1−1/n], n≥1, bằng (0,1). -/
theorem inner_closed_intervals_union :
    (⋃ n : ℕ+, Set.Icc (1 / (n : ℕ) : ℝ) (1 - 1 / (n : ℕ))) = Set.Ioo 0 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    have hpos : (0 : ℝ) < 1 / (n : ℕ) :=
      one_div_pos.mpr (Nat.cast_pos.mpr n.pos)
    exact ⟨hpos.trans_le hn.1, by linarith [hn.2]⟩
  · intro hx
    have hε : 0 < min x (1 - x) := lt_min hx.1 (by linarith [hx.2])
    obtain ⟨m, hm, hsmall⟩ := exists_positive_nat_reciprocal_lt hε
    let n : ℕ+ := ⟨m, hm⟩
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hleft : 1 / (m : ℝ) < x := hsmall.trans_le (min_le_left _ _)
    have hright : 1 / (m : ℝ) < 1 - x := hsmall.trans_le (min_le_right _ _)
    exact ⟨hleft.le, by change x ≤ 1 - 1 / (m : ℝ); linarith⟩

/-- Ví dụ 2.1.21: tập số tự nhiên cộng một nhiễu luân phiên nhỏ. -/
def alternatingPerturbations : Set ℝ :=
  {x | ∃ n : ℕ, 0 < n ∧ x = (n : ℝ) + (-1 : ℝ) ^ n / (n : ℝ)}

/-- Ví dụ 2.1.21: cận của nhiễu luân phiên. -/
theorem alternating_perturbation_abs_le_one (n : ℕ) (hn : 0 < n) :
    |(-1 : ℝ) ^ n / (n : ℝ)| ≤ 1 := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hnpos]
  apply (div_le_iff₀ hnpos).mpr
  simpa only [one_mul] using (Nat.one_le_cast.mpr hn)

/-- Ví dụ 2.1.21: phần tử nhỏ nhất và cận dưới lớn nhất bằng 0; không có cận trên. -/
theorem alternatingPerturbations_extrema :
    IsLeast alternatingPerturbations 0 ∧ IsGLB alternatingPerturbations 0 ∧
    (¬ BddAbove alternatingPerturbations) ∧
    (¬ ∃ x, IsGreatest alternatingPerturbations x) ∧
    (¬ ∃ x, IsLUB alternatingPerturbations x) := by
  have hleast : IsLeast alternatingPerturbations 0 := by
    refine ⟨⟨1, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    have hbound := (abs_le.mp (alternating_perturbation_abs_le_one n hn)).1
    have hnat : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    linarith
  have hunbounded : ¬ BddAbove alternatingPerturbations := by
    rintro ⟨M, hM⟩
    obtain ⟨n, hn, hlarge⟩ := exists_positive_nat_gt (M + 1)
    have hbound := (abs_le.mp (alternating_perturbation_abs_le_one n hn)).1
    have hupper := hM ⟨n, hn, rfl⟩
    linarith
  refine ⟨hleast, hleast.isGLB, hunbounded, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact hunbounded ⟨x, hx.2⟩
  · rintro ⟨x, hx⟩
    exact hunbounded ⟨x, hx.1⟩

/-- Bài tập 2.1.5(c): giai thừa tăng bằng tích các thừa số thực liên tiếp. -/
theorem ascending_product_eq (r p : ℕ) :
    (r.ascFactorial p : ℝ) = ∏ j ∈ Finset.range p, ((r : ℝ) + j) := by
  exact_mod_cast Nat.ascFactorial_eq_prod_range r p

/-- Bài tập 2.1.9(a): khoảng nửa mở có phần tử nhỏ nhất, cận trên bé nhất và cận dưới lớn nhất; không có phần tử lớn nhất. -/
theorem halfOpenUnitInterval_extrema :
    BddAbove (Set.Ico (0 : ℝ) 1) ∧ BddBelow (Set.Ico (0 : ℝ) 1) ∧
    IsLUB (Set.Ico (0 : ℝ) 1) 1 ∧ IsGLB (Set.Ico (0 : ℝ) 1) 0 ∧
    IsLeast (Set.Ico (0 : ℝ) 1) 0 ∧ (¬ ∃ x, IsGreatest (Set.Ico (0 : ℝ) 1) x) := by
  have hleast : IsLeast (Set.Ico (0 : ℝ) 1) 0 :=
    ⟨⟨le_rfl, zero_lt_one⟩, fun _ hx ↦ hx.1⟩
  have hlub : IsLUB (Set.Ico (0 : ℝ) 1) 1 := isLUB_Ico zero_lt_one
  refine ⟨⟨1, hlub.1⟩, ⟨0, hleast.2⟩, hlub, hleast.isGLB, hleast, ?_⟩
  rintro ⟨x, hx⟩
  exact (ne_of_lt hx.1.2) (hx.isLUB.unique hlub)

/-- Bài tập 2.1.9(d): tịnh tiến tập nghịch đảo. -/
def onePlusReciprocals : Set ℝ := {x | ∃ n : ℕ, 0 < n ∧ x = 1 + 1 / (n : ℝ)}

/-- Bài tập 2.1.9(d): phần tử lớn nhất và cận trên bé nhất bằng 2, cận dưới lớn nhất bằng 1 không đạt được. -/
theorem onePlusReciprocals_extrema :
    BddAbove onePlusReciprocals ∧ BddBelow onePlusReciprocals ∧
    IsGreatest onePlusReciprocals 2 ∧ IsLUB onePlusReciprocals 2 ∧
    IsGLB onePlusReciprocals 1 ∧ (¬ ∃ x, IsLeast onePlusReciprocals x) := by
  have hpos : ∀ x ∈ onePlusReciprocals, 1 < x := by
    rintro x ⟨n, hn, rfl⟩
    have h := one_div_pos.mpr (Nat.cast_pos.mpr hn : (0 : ℝ) < n)
    linarith
  have hne : onePlusReciprocals.Nonempty := ⟨2, 1, by decide, by norm_num⟩
  have hgreatest : IsGreatest onePlusReciprocals 2 := by
    refine ⟨⟨1, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    have hbound := positiveReciprocals_extrema.1.2 ⟨n, hn, rfl⟩
    linarith
  have hglb : IsGLB onePlusReciprocals 1 := by
    apply (greatestLowerBound_iff_epsilon _ 1 hne ⟨1, fun x hx ↦ (hpos x hx).le⟩).mpr
    refine ⟨fun x hx ↦ (hpos x hx).le, ?_⟩
    intro ε hε
    obtain ⟨n, hn, hsmall⟩ := exists_positive_nat_reciprocal_lt hε
    exact ⟨1 + 1 / (n : ℝ), ⟨n, hn, rfl⟩, by linarith⟩
  refine ⟨⟨2, hgreatest.2⟩, ⟨1, hglb.1⟩, hgreatest, hgreatest.isLUB, hglb, ?_⟩
  rintro ⟨x, hx⟩
  exact (ne_of_gt (hpos x hx.1)) (hx.isGLB.unique hglb)

/-- Tập trong Bài tập 2.1.9(b). -/
def alternatingReciprocals : Set ℝ :=
  {x | ∃ n : ℕ, 0 < n ∧ x = (-1 : ℝ) ^ n / (n : ℝ)}

/-- Bài tập 2.1.9(b): phần tử nhỏ nhất đạt tại n=1, phần tử lớn nhất đạt tại n=2. -/
theorem alternatingReciprocals_extrema :
    BddAbove alternatingReciprocals ∧ BddBelow alternatingReciprocals ∧
    IsGreatest alternatingReciprocals (1 / 2) ∧ IsLeast alternatingReciprocals (-1) ∧
    IsLUB alternatingReciprocals (1 / 2) ∧ IsGLB alternatingReciprocals (-1) := by
  have hleast : IsLeast alternatingReciprocals (-1) := by
    refine ⟨⟨1, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    exact (abs_le.mp (alternating_perturbation_abs_le_one n hn)).1
  have hgreatest : IsGreatest alternatingReciprocals (1 / 2) := by
    refine ⟨⟨2, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    by_cases h1 : n = 1
    · subst n
      norm_num
    · have hn2 : 2 ≤ n := by omega
      have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hbound : |(-1 : ℝ) ^ n / (n : ℝ)| ≤ 1 / 2 := by
        rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hnpos]
        exact one_div_le_one_div_of_le (by norm_num) hnreal
      exact (abs_le.mp hbound).2
  exact ⟨⟨1 / 2, hgreatest.2⟩, ⟨-1, hleast.2⟩, hgreatest, hleast,
    hgreatest.isLUB, hleast.isGLB⟩

/-- Bài tập 2.1.9(c): tập số hữu tỉ được xem là tập con của ℝ. -/
def rationalSquareLeTwo : Set ℝ :=
  (Rat.cast : ℚ → ℝ) '' {q : ℚ | q ^ 2 ≤ 2}

/-- Bài tập 2.1.9(c): cận trên bé nhất và cận dưới lớn nhất thực là ±√2, không có phần tử lớn nhất/nhỏ nhất hữu tỉ. -/
theorem rationalSquareLeTwo_extrema :
    BddAbove rationalSquareLeTwo ∧ BddBelow rationalSquareLeTwo ∧
    IsLUB rationalSquareLeTwo (Real.sqrt 2) ∧
    IsGLB rationalSquareLeTwo (-Real.sqrt 2) ∧
    (¬ ∃ x, IsGreatest rationalSquareLeTwo x) ∧
    (¬ ∃ x, IsLeast rationalSquareLeTwo x) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hne : rationalSquareLeTwo.Nonempty := ⟨0, 0, by norm_num, by simp⟩
  have hbounds : ∀ x ∈ rationalSquareLeTwo, -Real.sqrt 2 ≤ x ∧ x ≤ Real.sqrt 2 := by
    rintro x ⟨q, hq, rfl⟩
    have hsq : (q : ℝ) ^ 2 ≤ 2 := by exact_mod_cast hq
    constructor <;> nlinarith
  have hlub : IsLUB rationalSquareLeTwo (Real.sqrt 2) := by
    apply (leastUpperBound_iff_epsilon _ _ hne ⟨_, fun x hx ↦ (hbounds x hx).2⟩).mpr
    refine ⟨fun x hx ↦ (hbounds x hx).2, ?_⟩
    intro ε hε
    obtain ⟨q, hqlo, hqhi⟩ := rational_between
      (show max 0 (Real.sqrt 2 - ε) < Real.sqrt 2 from max_lt hpos (by linarith))
    have hqpos : 0 < (q : ℝ) := (le_max_left _ _).trans_lt hqlo
    have hq : (q : ℝ) ^ 2 ≤ 2 := by nlinarith
    refine ⟨q, ⟨q, by exact_mod_cast hq, rfl⟩, ?_⟩
    exact (le_max_right _ _).trans_lt hqlo
  have hglb : IsGLB rationalSquareLeTwo (-Real.sqrt 2) := by
    apply (greatestLowerBound_iff_epsilon _ _ hne ⟨_, fun x hx ↦ (hbounds x hx).1⟩).mpr
    refine ⟨fun x hx ↦ (hbounds x hx).1, ?_⟩
    intro ε hε
    obtain ⟨q, hqlo, hqhi⟩ := rational_between
      (show max 0 (Real.sqrt 2 - ε) < Real.sqrt 2 from max_lt hpos (by linarith))
    have hqpos : 0 < (q : ℝ) := (le_max_left _ _).trans_lt hqlo
    have hq : (-q : ℚ) ^ 2 ≤ 2 := by
      have hsq : (q : ℝ) ^ 2 ≤ 2 := by nlinarith
      have hsqrat : q ^ 2 ≤ 2 := by exact_mod_cast hsq
      simpa only [neg_sq] using hsqrat
    refine ⟨-(q : ℝ), ⟨-q, hq, by simp⟩, ?_⟩
    have hlarge := (le_max_right _ _).trans_lt hqlo
    linarith
  refine ⟨⟨_, hlub.1⟩, ⟨_, hglb.1⟩, hlub, hglb, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨q, _, hq⟩ := hx.1
    exact irrational_sqrt_two ⟨q, hq.trans (hx.isLUB.unique hlub)⟩
  · rintro ⟨x, hx⟩
    obtain ⟨q, _, hq⟩ := hx.1
    have heq := hq.trans (hx.isGLB.unique hglb)
    exact irrational_sqrt_two ⟨-q, by push_cast; linarith⟩

/-- Tập các thương trong Bài tập 2.1.9(e). -/
def rationalNaturalRatios : Set ℝ :=
  {x | ∃ n : ℕ, 0 < n ∧ x = (2 * (n : ℝ) + 1) / (n + 1)}

/-- Dạng nghịch đảo của thương trong Bài tập 2.1.9(e), với mẫu dương. -/
theorem rationalNaturalRatio_eq (n : ℕ) :
    (2 * (n : ℝ) + 1) / (n + 1) = 2 - 1 / (n + 1) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Bài tập 2.1.9(e): phần tử nhỏ nhất và cận dưới lớn nhất bằng 3/2; cận trên bé nhất bằng 2 không đạt được. -/
theorem rationalNaturalRatios_extrema :
    BddAbove rationalNaturalRatios ∧ BddBelow rationalNaturalRatios ∧
    IsLeast rationalNaturalRatios (3 / 2) ∧ IsGLB rationalNaturalRatios (3 / 2) ∧
    IsLUB rationalNaturalRatios 2 ∧ (¬ ∃ x, IsGreatest rationalNaturalRatios x) := by
  have hless : ∀ x ∈ rationalNaturalRatios, x < 2 := by
    rintro x ⟨n, _, rfl⟩
    rw [rationalNaturalRatio_eq]
    have h : (0 : ℝ) < 1 / (n + 1) := by positivity
    linarith
  have hleast : IsLeast rationalNaturalRatios (3 / 2) := by
    refine ⟨⟨1, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    rw [rationalNaturalRatio_eq]
    have hnreal : (2 : ℝ) ≤ n + 1 := by exact_mod_cast (show 2 ≤ n + 1 by omega)
    have hsmall := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hnreal
    linarith
  have hne : rationalNaturalRatios.Nonempty := ⟨3 / 2, hleast.1⟩
  have hlub : IsLUB rationalNaturalRatios 2 := by
    apply (leastUpperBound_iff_epsilon _ 2 hne ⟨2, fun x hx ↦ (hless x hx).le⟩).mpr
    refine ⟨fun x hx ↦ (hless x hx).le, ?_⟩
    intro ε hε
    obtain ⟨n, hn, hsmall⟩ := exists_positive_nat_reciprocal_lt hε
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hrecip : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
      one_div_le_one_div_of_le hnpos (by linarith)
    refine ⟨(2 * (n : ℝ) + 1) / (n + 1), ⟨n, hn, rfl⟩, ?_⟩
    rw [rationalNaturalRatio_eq]
    linarith
  refine ⟨⟨2, hlub.1⟩, ⟨3 / 2, hleast.2⟩, hleast, hleast.isGLB, hlub, ?_⟩
  rintro ⟨x, hx⟩
  exact (ne_of_lt (hless x hx.1)) (hx.isLUB.unique hlub)

/-- Tập trong Bài tập 2.1.9(f), tử số bằng 0 với chỉ số lẻ. -/
def alternatingNaturalRatios : Set ℝ :=
  {x | ∃ n : ℕ, 0 < n ∧ x = ((n : ℝ) + (-1 : ℝ) ^ n * n) / (n + 1)}

/-- Bài tập 2.1.9(f): công thức số hạng tại chỉ số chẵn. -/
theorem alternatingNaturalRatio_even_eq (m : ℕ) :
    ((2 * m : ℕ) + (-1 : ℝ) ^ (2 * m) * (2 * m : ℕ)) / ((2 * m : ℕ) + 1) =
      2 - 2 / (2 * (m : ℝ) + 1) := by
  have hpow : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
  rw [hpow]
  push_cast
  have hden : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Bài tập 2.1.9(f): phần tử nhỏ nhất và cận dưới lớn nhất bằng 0; cận trên bé nhất bằng 2 không đạt được. -/
theorem alternatingNaturalRatios_extrema :
    BddAbove alternatingNaturalRatios ∧ BddBelow alternatingNaturalRatios ∧
    IsLeast alternatingNaturalRatios 0 ∧ IsGLB alternatingNaturalRatios 0 ∧
    IsLUB alternatingNaturalRatios 2 ∧ (¬ ∃ x, IsGreatest alternatingNaturalRatios x) := by
  have hpowers : ∀ n : ℕ, -1 ≤ (-1 : ℝ) ^ n ∧ (-1 : ℝ) ^ n ≤ 1 := by
    intro n
    have h : |(-1 : ℝ) ^ n| ≤ 1 := by rw [abs_pow]; norm_num
    exact abs_le.mp h
  have hless : ∀ x ∈ alternatingNaturalRatios, x < 2 := by
    rintro x ⟨n, hn, rfl⟩
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    have hmul := mul_le_mul_of_nonneg_right (hpowers n).2 hnpos.le
    linarith
  have hleast : IsLeast alternatingNaturalRatios 0 := by
    refine ⟨⟨1, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    apply div_nonneg _ (by positivity)
    have hnpos : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (hpowers n).1 hnpos
    linarith
  have hlub : IsLUB alternatingNaturalRatios 2 := by
    apply (leastUpperBound_iff_epsilon _ _ ⟨0, hleast.1⟩
      ⟨2, fun x hx ↦ (hless x hx).le⟩).mpr
    refine ⟨fun x hx ↦ (hless x hx).le, ?_⟩
    intro ε hε
    obtain ⟨m, hm, hsmall⟩ := exists_positive_nat_reciprocal_lt hε
    have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have hεm : 1 < ε * (m : ℝ) := (div_lt_iff₀ hmpos).mp hsmall
    have htwo : 2 / (2 * (m : ℝ) + 1) < ε := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    refine ⟨((2 * m : ℕ) + (-1 : ℝ) ^ (2 * m) * (2 * m : ℕ)) /
      ((2 * m : ℕ) + 1), ⟨2 * m, by omega, rfl⟩, ?_⟩
    rw [alternatingNaturalRatio_even_eq]
    linarith
  refine ⟨⟨2, hlub.1⟩, ⟨0, hleast.2⟩, hleast, hleast.isGLB, hlub, ?_⟩
  rintro ⟨x, hx⟩
  exact (ne_of_lt (hless x hx.1)) (hx.isLUB.unique hlub)

/-- Tập trong Bài tập 2.1.9(g). -/
def onePlusAlternatingCorrections : Set ℝ :=
  {x | ∃ n : ℕ, 0 < n ∧ x = 1 + (1 + (-1 : ℝ) ^ n) / (n : ℝ)}

/-- Bài tập 2.1.9(g): phần tử nhỏ nhất bằng 1, phần tử lớn nhất bằng 2. -/
theorem onePlusAlternatingCorrections_extrema :
    BddAbove onePlusAlternatingCorrections ∧ BddBelow onePlusAlternatingCorrections ∧
    IsLeast onePlusAlternatingCorrections 1 ∧ IsGreatest onePlusAlternatingCorrections 2 ∧
    IsGLB onePlusAlternatingCorrections 1 ∧ IsLUB onePlusAlternatingCorrections 2 := by
  have hpowers : ∀ n : ℕ, -1 ≤ (-1 : ℝ) ^ n ∧ (-1 : ℝ) ^ n ≤ 1 := by
    intro n
    have h : |(-1 : ℝ) ^ n| ≤ 1 := by rw [abs_pow]; norm_num
    exact abs_le.mp h
  have hleast : IsLeast onePlusAlternatingCorrections 1 := by
    refine ⟨⟨1, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    have hnum : 0 ≤ 1 + (-1 : ℝ) ^ n := by linarith [(hpowers n).1]
    have hdiv := div_nonneg hnum (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hgreatest : IsGreatest onePlusAlternatingCorrections 2 := by
    refine ⟨⟨2, by decide, by norm_num⟩, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    by_cases h1 : n = 1
    · subst n
      norm_num
    · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      have hbound : (1 + (-1 : ℝ) ^ n) / (n : ℝ) ≤ 1 := by
        apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
        linarith [(hpowers n).2]
      linarith
  exact ⟨⟨2, hgreatest.2⟩, ⟨1, hleast.2⟩, hleast, hgreatest, hleast.isGLB, hgreatest.isLUB⟩

end calculus.Chapter02.Section01Exercises
