import calculus.Chapter01.Section05
import calculus.Chapter01.Section04Exercises
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Irrational

/-!
# 1.4. Bài tập số học và căn đại số

Nguồn: `source/Ch1_taphop.tex`, dòng 882–963 và 1219–1231.
-/

namespace calculus.Chapter01.Section04Arithmetic

open Polynomial
open calculus.Chapter01.Section05 (realCubeRoot realCubeRoot_cube)


lemma integer_mod_self (m a : ℤ) : Int.ModEq m a (a % m) := by
  show a % m = (a % m) % m
  simp

/-- Bài tập 1.4.12(e): tích của ba số nguyên liên tiếp chia hết cho 6. -/
theorem six_dvd_cube_sub (a : ℤ) : (6 : ℤ) ∣ a ^ 3 - a := by
  apply Int.dvd_iff_emod_eq_zero.mpr
  have hp := (integer_mod_self 6 a).pow 3
  change a ^ 3 % 6 = (a % 6) ^ 3 % 6 at hp
  rw [Int.sub_emod, hp]
  have h0 := Int.emod_nonneg a (by norm_num : (6 : ℤ) ≠ 0)
  have h6 := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 6)
  interval_cases h : a % 6 <;> norm_num

/-- Bài tập 1.4.12(f): a⁵−a chia hết cho 30 với mọi a∈ℤ. -/
theorem thirty_dvd_fifth_power_sub (a : ℤ) : (30 : ℤ) ∣ a ^ 5 - a := by
  apply Int.dvd_iff_emod_eq_zero.mpr
  have hp := (integer_mod_self 30 a).pow 5
  change a ^ 5 % 30 = (a % 30) ^ 5 % 30 at hp
  rw [Int.sub_emod, hp]
  have h0 := Int.emod_nonneg a (by norm_num : (30 : ℤ) ≠ 0)
  have h30 := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 30)
  interval_cases h : a % 30 <;> norm_num

/-- Bài tập 1.4.12(b): 17a³+103a chia hết cho 6 với mọi số nguyên a. -/
theorem six_dvd_seventeen_cube_add (a : ℤ) : (6 : ℤ) ∣ 17 * a ^ 3 + 103 * a := by
  have h₁ : (6 : ℤ) ∣ 17 * (a ^ 3 - a) := dvd_mul_of_dvd_right (six_dvd_cube_sub a) 17
  have h₂ : (6 : ℤ) ∣ 120 * a := ⟨20 * a, by ring⟩
  have heq : 17 * a ^ 3 + 103 * a = 17 * (a ^ 3 - a) + 120 * a := by ring
  rw [heq]
  exact dvd_add h₁ h₂

/-- Bài tập 1.4.12(c): bình phương số nguyên lẻ đồng dư 1 theo môđun 8. -/
theorem eight_dvd_odd_square_sub_one (a : ℤ) (ha : Odd a) : (8 : ℤ) ∣ a ^ 2 - 1 := by
  apply Int.dvd_iff_emod_eq_zero.mpr
  have hp := (integer_mod_self 8 a).pow 2
  change a ^ 2 % 8 = (a % 8) ^ 2 % 8 at hp
  rw [Int.sub_emod, hp]
  have hodd : a % 2 = 1 := Int.odd_iff.mp ha
  have h0 := Int.emod_nonneg a (by norm_num : (8 : ℤ) ≠ 0)
  have h8 := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 8)
  interval_cases h : a % 8 <;> norm_num <;> omega

/-- Bài tập 1.4.12(c): hiệu hai số chính phương lẻ chia hết cho 8. -/
theorem eight_dvd_odd_squares_sub (a b : ℤ) (ha : Odd a) (hb : Odd b) :
    (8 : ℤ) ∣ a ^ 2 - b ^ 2 := by
  have heq : a ^ 2 - b ^ 2 = (a ^ 2 - 1) - (b ^ 2 - 1) := by ring
  rw [heq]
  exact dvd_sub (eight_dvd_odd_square_sub_one a ha)
    (eight_dvd_odd_square_sub_one b hb)

/-- Bài tập 1.4.12(c), trường hợp đặc biệt: a là số tự nhiên dương. -/
theorem eight_dvd_positive_odd_square_sub_one (a : ℕ+) (ha : Odd (a : ℕ)) :
    (8 : ℤ) ∣ ((a : ℕ) : ℤ) ^ 2 - 1 := by
  apply eight_dvd_odd_square_sub_one
  exact_mod_cast ha

/-- Bài tập 1.4.12(d): a lẻ dương; phép trừ lấy trong ℤ. -/
theorem sixteen_dvd_positive_odd_fourth_power_sub_one (a : ℕ+) (ha : Odd (a : ℕ)) :
    (16 : ℤ) ∣ ((a : ℕ) : ℤ) ^ 4 - 1 := by
  let z : ℤ := (a : ℕ)
  have hz : Odd z := by
    change Odd ((a : ℕ) : ℤ)
    exact_mod_cast ha
  obtain ⟨k, hk⟩ := eight_dvd_odd_square_sub_one z hz
  have hs : z ^ 4 - 1 = (z ^ 2 - 1) * (z ^ 2 + 1) := by ring
  rw [hs, hk]
  have hsecond : z ^ 2 + 1 = 2 * (4 * k + 1) := by linarith [hk]
  rw [hsecond]
  exact ⟨k * (4 * k + 1), by ring⟩


/-- Bài tập 1.4.12(a): 5^(2n+1)+2^(2n+1) chia hết cho 7. -/
theorem seven_dvd_odd_power_sum (n : ℕ+) :
    7 ∣ 5 ^ (2 * (n : ℕ) + 1) + 2 ^ (2 * (n : ℕ) + 1) := by
  have hp : Nat.ModEq 7 ((5 ^ 2) ^ (n : ℕ)) ((2 ^ 2) ^ (n : ℕ)) :=
    (show Nat.ModEq 7 (5 ^ 2) (2 ^ 2) by decide).pow (n : ℕ)
  have hs := (hp.mul (Nat.ModEq.refl 5)).add
    (Nat.ModEq.refl ((2 ^ 2) ^ (n : ℕ) * 2))
  have hz : Nat.ModEq 7 (((2 ^ 2) ^ (n : ℕ) * 5) + ((2 ^ 2) ^ (n : ℕ) * 2)) 0 := by
    apply Nat.modEq_zero_iff_dvd.mpr
    rw [← Nat.mul_add]
    exact dvd_mul_left 7 _
  apply Nat.modEq_zero_iff_dvd.mp
  simpa only [pow_add, pow_mul, pow_one] using hs.trans hz


lemma square_mod_eight (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h8 : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases h : a % 8 <;> norm_num [Nat.pow_mod, h]


lemma square_mod_five (a : ℕ) : a ^ 2 % 5 = 0 ∨ a ^ 2 % 5 = 1 ∨ a ^ 2 % 5 = 4 := by
  have h5 : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : a % 5 <;> norm_num [Nat.pow_mod, h]

/-- Bài tập 1.4.12(g): hai giả thiết về số chính phương suy ra n chia hết cho 8 và 5. -/
theorem forty_dvd_of_two_linear_squares (n : ℕ+)
    (h₂ : IsSquare (2 * (n : ℕ) + 1)) (h₃ : IsSquare (3 * (n : ℕ) + 1)) :
    40 ∣ (n : ℕ) := by
  obtain ⟨a, ha⟩ := h₂
  obtain ⟨b, hb⟩ := h₃
  have h2eight : (2 * (n : ℕ) + 1) % 8 = 0 ∨
      (2 * (n : ℕ) + 1) % 8 = 1 ∨ (2 * (n : ℕ) + 1) % 8 = 4 := by
    simpa only [ha, ← pow_two] using square_mod_eight a
  have h3eight : (3 * (n : ℕ) + 1) % 8 = 0 ∨
      (3 * (n : ℕ) + 1) % 8 = 1 ∨ (3 * (n : ℕ) + 1) % 8 = 4 := by
    simpa only [hb, ← pow_two] using square_mod_eight b
  have h2five : (2 * (n : ℕ) + 1) % 5 = 0 ∨
      (2 * (n : ℕ) + 1) % 5 = 1 ∨ (2 * (n : ℕ) + 1) % 5 = 4 := by
    simpa only [ha, ← pow_two] using square_mod_five a
  have h3five : (3 * (n : ℕ) + 1) % 5 = 0 ∨
      (3 * (n : ℕ) + 1) % 5 = 1 ∨ (3 * (n : ℕ) + 1) % 5 = 4 := by
    simpa only [hb, ← pow_two] using square_mod_five b
  have h8 : 8 ∣ (n : ℕ) := Nat.dvd_of_mod_eq_zero (by omega)
  have h5 : 5 ∣ (n : ℕ) := Nat.dvd_of_mod_eq_zero (by omega)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 8 5) h8 h5

/-- Bài tập 1.4.3(a), phần căn bậc hai. -/
theorem sqrt_three_irrational : Irrational (Real.sqrt 3) := by norm_num

/-- Bài tập 1.4.3(a), phần căn bậc ba; không có số nguyên có lập phương bằng 2. -/
theorem cubeRoot_two_irrational : Irrational (realCubeRoot 2) := by
  apply irrational_nrt_of_notint_nrt 3 2 (realCubeRoot_cube 2) _ (by norm_num)
  rintro ⟨y, hy⟩
  have hcube : (y : ℝ) ^ 3 = 2 := by rw [← hy]; exact realCubeRoot_cube 2
  have hmono := (Odd.strictMono_pow (R := ℝ) (show Odd (3 : ℕ) by decide)).monotone
  rcases (show y ≤ 1 ∨ 2 ≤ y by omega) with h | h
  · have hreal : (y : ℝ) ≤ 1 := by exact_mod_cast h
    have hpow := hmono hreal
    norm_num at hpow
    linarith
  · have hreal : (2 : ℝ) ≤ y := by exact_mod_cast h
    have hpow := hmono hreal
    norm_num at hpow
    linarith


/-- Bài tập 1.4.5: phương trình z³−z−7=0 không có nghiệm hữu tỉ. -/
theorem rational_cube_ne_self_add_seven (q : ℚ) : q ^ 3 ≠ q + 7 := by
  intro hq
  let p : ℤ[X] := X ^ 3 - (X + C 7)
  have hp : p.Monic := by
    apply monic_X_pow_sub
    rw [degree_X_add_C]
    norm_num
  have hroot : aeval q p = 0 := by
    simp only [p, map_sub, map_pow, map_add, aeval_X, aeval_C]
    norm_num
    linarith
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hp hroot
  have hzq : q = (z : ℚ) := hz
  have heq : z ^ 3 = z + 7 := by rw [hzq] at hq; exact_mod_cast hq
  have hdiv : (6 : ℤ) ∣ 7 := by
    have hdiff : z ^ 3 - z = 7 := by linarith
    rw [← hdiff]
    exact six_dvd_cube_sub z
  norm_num at hdiv

/-- Bài tập 1.4.4: với a<b, chọn r∈ℚ khác 0 sao cho a<r√2<b. -/
theorem exists_nonzero_rational_mul_sqrt_two_between (a b : ℝ) (hab : a < b) :
    ∃ q : ℚ, q ≠ 0 ∧ a < (q : ℝ) * Real.sqrt 2 ∧ (q : ℝ) * Real.sqrt 2 < b := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  by_cases hb : 0 < b
  · have hbound : max a 0 / Real.sqrt 2 < b / Real.sqrt 2 :=
      (div_lt_div_iff_of_pos_right hs).mpr (max_lt hab hb)
    obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hbound
    have hqpos : 0 < (q : ℝ) := by
      have hnonneg : 0 ≤ max a 0 / Real.sqrt 2 :=
        div_nonneg (le_max_right _ _) hs.le
      exact hnonneg.trans_lt hqlo
    refine ⟨q, by exact_mod_cast hqpos.ne', ?_, (lt_div_iff₀ hs).mp hqhi⟩
    exact (le_max_left _ _).trans_lt ((div_lt_iff₀ hs).mp hqlo)
  · obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn
      ((div_lt_div_iff_of_pos_right hs).mpr hab)
    have hqneg : (q : ℝ) < 0 := by
      exact hqhi.trans_le (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) hs.le)
    exact ⟨q, by exact_mod_cast hqneg.ne, (div_lt_iff₀ hs).mp hqlo,
      (lt_div_iff₀ hs).mp hqhi⟩

/-- Bài tập 1.4.4: mỗi khoảng (a,b), a<b, chứa một số vô tỉ. -/
theorem exists_irrational_between (a b : ℝ) (hab : a < b) :
    ∃ x : ℝ, Irrational x ∧ a < x ∧ x < b := by
  obtain ⟨q, hq, hqa, hqb⟩ := exists_nonzero_rational_mul_sqrt_two_between a b hab
  exact ⟨(q : ℝ) * Real.sqrt 2, irrational_sqrt_two.ratCast_mul hq, hqa, hqb⟩

/-- Bài tập 1.4.4: mỗi khoảng mở khác rỗng chứa vô hạn số vô tỉ. -/
theorem irrationals_between_infinite (a b : ℝ) (hab : a < b) :
    {x : ℝ | Irrational x ∧ a < x ∧ x < b}.Infinite := by
  intro hfinite
  obtain ⟨x₀, hx₀⟩ := exists_irrational_between a b hab
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image
    {x : ℝ | Irrational x ∧ a < x ∧ x < b}
    (fun x : ℝ ↦ x) hfinite ⟨x₀, hx₀⟩
  obtain ⟨y, hyirr, hxy, hyb⟩ := exists_irrational_between x b hx.2.2
  exact (not_le.mpr hxy) (hmax y ⟨hyirr, hx.2.1.trans hxy, hyb⟩)

/-- Đa thức 0 nhận mọi số thực làm nghiệm; định nghĩa số đại số cần loại đa thức này. -/
theorem zero_polynomial_root_every_real (x : ℝ) : ∃ p : ℤ[X], aeval x p = 0 :=
  ⟨0, map_zero _⟩

/-- Bài tập 1.4.7: √2 là nghiệm của đa thức nguyên khác 0, X²−2. -/
theorem sqrt_two_isAlgebraic : IsAlgebraic ℤ (Real.sqrt 2) := by
  refine ⟨X ^ 2 - C 2, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : ℤ[X] ↦ p.coeff 2) h
    norm_num at hc
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    norm_num

/-- Bài tập 1.4.7: căn bậc ba của 2 là nghiệm của X³−2. -/
theorem cubeRoot_two_isAlgebraic : IsAlgebraic ℤ (realCubeRoot 2) := by
  refine ⟨X ^ 3 - C 2, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : ℤ[X] ↦ p.coeff 3) h
    norm_num at hc
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    norm_num [realCubeRoot_cube]

/-- Bài tập 1.4.7: căn bậc ba của 1+√5 là nghiệm của X⁶−2X³−4. -/
theorem cubeRoot_one_add_sqrt_five_isAlgebraic :
    IsAlgebraic ℤ (realCubeRoot (1 + Real.sqrt 5)) := by
  let z := realCubeRoot (1 + Real.sqrt 5)
  refine ⟨X ^ 6 - C 2 * X ^ 3 - C 4, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : ℤ[X] ↦ p.coeff 6) h
    norm_num at hc
  · simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C]
    norm_num
    have hcube : z ^ 3 = 1 + Real.sqrt 5 := realCubeRoot_cube _
    have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h6 : z ^ 6 = (z ^ 3) ^ 2 := by ring
    change z ^ 6 - 2 * z ^ 3 - 4 = 0
    rw [h6, hcube]
    nlinarith


/-- Bài tập 1.4.8: tập nghiệm trên miền x≠0 của phân thức 999/x. -/
theorem integer_shift_reciprocal_sqrt_solutions (x : ℝ) :
    (x ≠ 0 ∧ (∃ m : ℤ, x + Real.sqrt 2023 = m) ∧
      ∃ n : ℤ, 999 / x + Real.sqrt 2023 = n) ↔
    x = 32 - Real.sqrt 2023 ∨ x = -32 - Real.sqrt 2023 := by
  have hs : Real.sqrt 2023 ^ 2 = 2023 := Real.sq_sqrt (by norm_num)
  have hirr : Irrational (Real.sqrt 2023) := by norm_num
  constructor
  · rintro ⟨hx, ⟨m, hm⟩, ⟨n, hn⟩⟩
    have hprod : ((m : ℝ) - Real.sqrt 2023) * ((n : ℝ) - Real.sqrt 2023) = 999 := by
      calc
        _ = x * (999 / x) := by congr 1 <;> linarith
        _ = 999 := by field_simp
    have hcoeff : ((m + n : ℤ) : ℝ) * Real.sqrt 2023 = ((m * n + 1024 : ℤ) : ℝ) := by
      push_cast
      nlinarith [hprod]
    have hsum : m + n = 0 := by
      by_contra hne
      have hi := hirr.intCast_mul hne
      exact (Int.not_irrational (m * n + 1024)) (hcoeff ▸ hi)
    have hnval : n = -m := by omega
    have hmreal : (m : ℝ) ^ 2 = 1024 := by
      rw [hsum] at hcoeff
      push_cast at hcoeff
      have hnm : (n : ℝ) = -(m : ℝ) := by exact_mod_cast hnval
      rw [hnm] at hcoeff
      nlinarith
    have hmchoice : (m : ℝ) = 32 ∨ (m : ℝ) = -32 := by
      have hmul : ((m : ℝ) - 32) * ((m : ℝ) + 32) = 0 := by nlinarith
      rcases mul_eq_zero.mp hmul with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hmchoice with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · have hx : (32 : ℝ) - Real.sqrt 2023 ≠ 0 := by
        intro h
        have he : Real.sqrt 2023 = 32 := by linarith
        rw [he] at hs
        norm_num at hs
      refine ⟨hx, ⟨32, by ring⟩, ⟨-32, ?_⟩⟩
      have hfrac : 999 / (32 - Real.sqrt 2023) = -32 - Real.sqrt 2023 := by
        apply (div_eq_iff hx).mpr
        nlinarith
      norm_num
      linarith
    · have hx : (-32 : ℝ) - Real.sqrt 2023 ≠ 0 := by
        intro h
        have he : Real.sqrt 2023 = -32 := by linarith
        rw [he] at hs
        norm_num at hs
      refine ⟨hx, ⟨-32, by ring⟩, ⟨32, ?_⟩⟩
      have hfrac : 999 / (-32 - Real.sqrt 2023) = 32 - Real.sqrt 2023 := by
        apply (div_eq_iff hx).mpr
        nlinarith
      norm_num
      linarith

/-! ## Ví dụ quan hệ hữu hạn 1.4.26, dòng 1219–1231 -/

/-- Ví dụ 1.4.26: ba phần tử của Y. -/
inductive RelationY where
  | a
  | b
  | c
  deriving DecidableEq

/-- Ví dụ 1.4.26: ba phần tử của Z. -/
inductive RelationZ where
  | l
  | m
  | n
  deriving DecidableEq

open calculus.Chapter01.Section04Exercises (relationGraph)

/-- Ví dụ 1.4.26: R gồm năm cặp, với tập nguồn {4,5,6}. -/
def finiteRelationR (x : ℕ) (y : RelationY) : Prop :=
  match y with
  | .a => x = 4 ∨ x = 6
  | .b => x = 4
  | .c => x = 5 ∨ x = 6

/-- Ví dụ 1.4.26: S gồm bảy cặp. -/
def finiteRelationS (y : RelationY) (z : RelationZ) : Prop :=
  match y, z with
  | .a, .m => False
  | .b, .n => False
  | _, _ => True


lemma exists_relationY_iff (P : RelationY → Prop) :
    (∃ y, P y) ↔ P .a ∨ P .b ∨ P .c := by
  constructor
  · rintro ⟨y, hy⟩
    cases y
    · exact Or.inl hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)
  · rintro (h | h | h)
    · exact ⟨.a, h⟩
    · exact ⟨.b, h⟩
    · exact ⟨.c, h⟩

/-- Ví dụ 1.4.26: đồ thị R gồm năm cặp đã liệt kê. -/
theorem finiteRelationR_graph :
    relationGraph finiteRelationR =
      {(4, RelationY.a), (4, RelationY.b), (5, RelationY.c),
       (6, RelationY.a), (6, RelationY.c)} := by
  ext ⟨x, y⟩
  cases y <;> simp [relationGraph, finiteRelationR]

/-- Ví dụ 1.4.26: đồ thị S gồm bảy cặp đã liệt kê. -/
theorem finiteRelationS_graph :
    relationGraph finiteRelationS =
      {(RelationY.a, RelationZ.l), (RelationY.a, RelationZ.n),
       (RelationY.b, RelationZ.l), (RelationY.b, RelationZ.m),
       (RelationY.c, RelationZ.l), (RelationY.c, RelationZ.m), (RelationY.c, RelationZ.n)} := by
  ext ⟨y, z⟩
  cases y <;> cases z <;> simp [relationGraph, finiteRelationS]

/-- Ví dụ 1.4.26: quan hệ ngược của R gồm đúng năm cặp đảo. -/
theorem finiteRelationR_inverse_graph :
    relationGraph (Function.swap finiteRelationR) =
      {(RelationY.a, 4), (RelationY.b, 4), (RelationY.c, 5),
       (RelationY.a, 6), (RelationY.c, 6)} := by
  ext ⟨y, x⟩
  cases y <;> simp [relationGraph, Function.swap, finiteRelationR]

/-- Ví dụ 1.4.26: đồ thị S∘R gồm chín cặp. -/
theorem finiteRelationS_comp_R_graph :
    relationGraph (Relation.Comp finiteRelationR finiteRelationS) =
      {(4, RelationZ.l), (4, RelationZ.n), (4, RelationZ.m),
       (5, RelationZ.l), (5, RelationZ.m), (5, RelationZ.n),
       (6, RelationZ.l), (6, RelationZ.m), (6, RelationZ.n)} := by
  ext ⟨x, z⟩
  cases z <;> simp [relationGraph, Relation.Comp, exists_relationY_iff,
    finiteRelationR, finiteRelationS, or_assoc, or_left_comm, or_comm]

/-- Ví dụ 1.4.26: đồ thị R⁻¹∘R gồm bảy cặp. -/
theorem finiteRelationR_inverse_comp_R_graph :
    relationGraph (Relation.Comp finiteRelationR (Function.swap finiteRelationR)) =
      {(4, 4), (5, 5), (5, 6), (6, 4), (6, 5), (4, 6), (6, 6)} := by
  ext ⟨x, y⟩
  simp [relationGraph, Relation.Comp, exists_relationY_iff, Function.swap, finiteRelationR]
  aesop



lemma reciprocal_step_bound (k : ℕ) :
    1 / ((k : ℝ) + 2) ^ 2 ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
  have ha : 0 < (k : ℝ) + 1 := by positivity
  have hb : 0 < (k : ℝ) + 2 := by positivity
  have hdiff : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
      1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp
    ring
  rw [hdiff]
  apply one_div_le_one_div_of_le (mul_pos ha hb)
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]


lemma reciprocal_square_sum_bound (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2) ^ 2) ≤ 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hterm := reciprocal_step_bound n
    have hsum := add_le_add ih hterm
    push_cast
    have hden : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    rw [hden]
    linarith

/-- Bài tập 1.4.9: tổng 2024 số hạng từ 1/2² đến 1/2025² nhỏ hơn 1. -/
theorem reciprocal_square_sum_2025_lt_one :
    (∑ k ∈ Finset.range 2024, 1 / ((k : ℝ) + 2) ^ 2) < 1 := by
  exact lt_of_le_of_lt (reciprocal_square_sum_bound 2024) (by norm_num)

/-- Bài tập 1.4.9: tổng không phải số tự nhiên dương. -/
theorem reciprocal_square_sum_2025_not_positive_natural :
    ¬ ∃ n : ℕ+, (∑ k ∈ Finset.range 2024, 1 / ((k : ℝ) + 2) ^ 2) = ((n : ℕ) : ℝ) := by
  rintro ⟨n, hn⟩
  have hbound := reciprocal_square_sum_2025_lt_one
  have hpos : (1 : ℝ) ≤ (n : ℕ) := Nat.one_le_cast.mpr n.pos
  exact (not_le.mpr hbound) (hn.symm ▸ hpos)



lemma rational_coefficients_of_irrational_relation (s : ℝ) (hs : Irrational s)
    (u v : ℚ) (h : (u : ℝ) = (v : ℝ) * s) : u = 0 ∧ v = 0 := by
  have hv : v = 0 := by
    by_contra hv
    exact (Rat.not_irrational u) (h.symm ▸ hs.ratCast_mul hv)
  refine ⟨?_, hv⟩
  have hu : (u : ℝ) = 0 := by simpa [hv] using h
  exact_mod_cast hu

/-- Bài tập 1.4.6: mẫu khác 0 khi c>0, vì √2024 vô tỉ. -/
theorem radical_fraction_denominator_ne_zero (b c : ℕ+) :
    ((b : ℕ) : ℝ) - ((c : ℕ) : ℝ) * Real.sqrt 2024 ≠ 0 := by
  have hs : Irrational (Real.sqrt 2024) := by norm_num
  have hi := hs.natCast_mul (Nat.ne_zero_of_lt c.pos)
  intro h
  have heq : ((c : ℕ) : ℝ) * Real.sqrt 2024 = (b : ℕ) := by linarith
  exact (Nat.not_irrational (b : ℕ)) (heq ▸ hi)

/-- Bài tập 1.4.6: phân thức hữu tỉ suy ra ac=b². -/
lemma rational_radical_fraction_implies_geometric (a b c : ℕ+)
    (hq : ∃ q : ℚ,
      (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) * Real.sqrt 2024) /
        (((b : ℕ) : ℝ) - ((c : ℕ) : ℝ) * Real.sqrt 2024) = q) :
    (a : ℕ) * (c : ℕ) = (b : ℕ) ^ 2 := by
  obtain ⟨q, hq⟩ := hq
  have hmul := (div_eq_iff (radical_fraction_denominator_ne_zero b c)).mp hq
  have hs : Irrational (Real.sqrt 2024) := by norm_num
  have hcoeff : ((((b : ℕ) : ℚ) * q - (a : ℕ) : ℚ) : ℝ) =
      ((((c : ℕ) : ℚ) * q - (b : ℕ) : ℚ) : ℝ) * Real.sqrt 2024 := by
    push_cast
    nlinarith only [hmul]
  obtain ⟨hu, hv⟩ := rational_coefficients_of_irrational_relation _ hs
    (((b : ℕ) : ℚ) * q - (a : ℕ)) (((c : ℕ) : ℚ) * q - (b : ℕ)) hcoeff
  have hba : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) * (q : ℝ) := by
    have h := congrArg (Rat.cast : ℚ → ℝ) hu
    push_cast at h
    linarith
  have hcb : ((c : ℕ) : ℝ) * (q : ℝ) = (b : ℕ) := by
    have h := congrArg (Rat.cast : ℚ → ℝ) hv
    push_cast at h
    linarith
  have hreal : ((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) = ((b : ℕ) : ℝ) ^ 2 := by
    calc
      _ = (((b : ℕ) : ℝ) * q) * (c : ℕ) := by rw [hba]
      _ = ((b : ℕ) : ℝ) * (((c : ℕ) : ℝ) * q) := by ring
      _ = ((b : ℕ) : ℝ) * (b : ℕ) := by rw [hcb]
      _ = ((b : ℕ) : ℝ) ^ 2 := (pow_two _).symm
  exact_mod_cast hreal

/-- Bài tập 1.4.6: phân thức hữu tỉ và a²+b²+c² nguyên tố khi và chỉ khi a=b=c=1. -/
theorem positive_radical_fraction_prime_solutions (a b c : ℕ+) :
    ((∃ q : ℚ,
      (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) * Real.sqrt 2024) /
        (((b : ℕ) : ℝ) - ((c : ℕ) : ℝ) * Real.sqrt 2024) = q) ∧
      Nat.Prime ((a : ℕ) ^ 2 + (b : ℕ) ^ 2 + (c : ℕ) ^ 2)) ↔
    a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · rintro ⟨hq, hp⟩
    have hac := rational_radical_fraction_implies_geometric a b c hq
    have hstrict : (b : ℕ) < (a : ℕ) + (c : ℕ) := by
      by_contra h
      have hle := Nat.le_of_not_gt h
      have hs := Nat.pow_le_pow_left hle 2
      nlinarith [a.pos, c.pos]
    have hfactor : ((a : ℕ) + (c : ℕ) - (b : ℕ)) *
        ((a : ℕ) + (c : ℕ) + (b : ℕ)) =
        (a : ℕ) ^ 2 + (b : ℕ) ^ 2 + (c : ℕ) ^ 2 := by
      have hacreal : ((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) = ((b : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast hac
      have hreal : (((a : ℕ) + (c : ℕ) - (b : ℕ) : ℕ) : ℝ) *
          (((a : ℕ) + (c : ℕ) + (b : ℕ) : ℕ) : ℝ) =
          ((a : ℕ) : ℝ) ^ 2 + ((b : ℕ) : ℝ) ^ 2 + ((c : ℕ) : ℝ) ^ 2 := by
        rw [Nat.cast_sub hstrict.le]
        push_cast
        nlinarith only [hacreal]
      exact_mod_cast hreal
    have hp' : Nat.Prime (((a : ℕ) + (c : ℕ) - (b : ℕ)) *
        ((a : ℕ) + (c : ℕ) + (b : ℕ))) := by rw [hfactor]; exact hp
    have hdiff : (a : ℕ) + (c : ℕ) - (b : ℕ) = 1 := by
      rcases Nat.prime_mul_iff.mp hp' with ⟨_, h⟩ | ⟨_, h⟩
      · omega
      · exact h
    have hsum : (a : ℕ) + (c : ℕ) = (b : ℕ) + 1 := by omega
    have hb : (b : ℕ) = 1 := by
      have habound : (4 : ℕ) * ((a : ℕ) * (c : ℕ)) ≤ ((a : ℕ) + (c : ℕ)) ^ 2 := by
        have hsq := sq_nonneg (((a : ℕ) : ℝ) - ((c : ℕ) : ℝ))
        have hreal : (4 : ℝ) * (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ)) ≤
            (((a : ℕ) : ℝ) + ((c : ℕ) : ℝ)) ^ 2 := by nlinarith
        exact_mod_cast hreal
      rw [hac, hsum] at habound
      nlinarith [b.pos]
    have hap := a.pos
    have hcp := c.pos
    have ha : (a : ℕ) = 1 := by omega
    have hc : (c : ℕ) = 1 := by omega
    exact ⟨by apply Subtype.ext; exact ha, by apply Subtype.ext; exact hb,
      by apply Subtype.ext; exact hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    constructor
    · refine ⟨1, ?_⟩
      simpa using div_self (radical_fraction_denominator_ne_zero 1 1)
    · decide


/-- Bài tập 1.4.11: nếu tổng hai bình phương chia hết cho 3 thì mỗi cơ số chia hết cho 3. -/
theorem three_dvd_each_of_sum_squares (m n : ℤ) (h : (3 : ℤ) ∣ m ^ 2 + n ^ 2) :
    (3 : ℤ) ∣ m ∧ (3 : ℤ) ∣ n := by
  have hm := (integer_mod_self 3 m).pow 2
  have hn := (integer_mod_self 3 n).pow 2
  change m ^ 2 % 3 = (m % 3) ^ 2 % 3 at hm
  change n ^ 2 % 3 = (n % 3) ^ 2 % 3 at hn
  have hsum := Int.dvd_iff_emod_eq_zero.mp h
  rw [Int.add_emod, hm, hn] at hsum
  have hm0 := Int.emod_nonneg m (by norm_num : (3 : ℤ) ≠ 0)
  have hm3 := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 3)
  have hn0 := Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0)
  have hn3 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 3)
  interval_cases hrm : m % 3 <;> interval_cases hrn : n % 3 <;> norm_num at hsum
  constructor <;> apply Int.dvd_iff_emod_eq_zero.mpr <;> omega


lemma nine_dvd_sum_squares_of_three_dvd (x z : ℤ) (hx : (3 : ℤ) ∣ x) (hz : (3 : ℤ) ∣ z) :
    (9 : ℤ) ∣ x ^ 2 + z ^ 2 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hz
  exact ⟨a ^ 2 + b ^ 2, by ring⟩

/-- Bài tập 1.4.11(a): phương trình buộc p=3. -/
lemma prime_eq_three_of_first_equation (x y : ℕ+) (p : ℕ) (hp : Nat.Prime p)
    (heq : ((x : ℕ) : ℤ) ^ 2 + (p : ℤ) ^ 2 * ((y : ℕ) : ℤ) ^ 2 =
      6 * (((x : ℕ) : ℤ) + 2 * p)) : p = 3 := by
  have h3 : (3 : ℤ) ∣ ((x : ℕ) : ℤ) ^ 2 + ((p : ℤ) * ((y : ℕ) : ℤ)) ^ 2 := by
    have hre : ((x : ℕ) : ℤ) ^ 2 + ((p : ℤ) * ((y : ℕ) : ℤ)) ^ 2 =
        6 * (((x : ℕ) : ℤ) + 2 * p) := by nlinarith only [heq]
    rw [hre]
    exact ⟨2 * (((x : ℕ) : ℤ) + 2 * p), by ring⟩
  obtain ⟨hx3, hpy3⟩ := three_dvd_each_of_sum_squares _ _ h3
  have h9 := nine_dvd_sum_squares_of_three_dvd _ _ hx3 hpy3
  have hx9 : (9 : ℤ) ∣ 6 * ((x : ℕ) : ℤ) := by
    obtain ⟨a, ha⟩ := hx3
    exact ⟨2 * a, by rw [ha]; ring⟩
  have hsum9 : (9 : ℤ) ∣ 6 * ((x : ℕ) : ℤ) + 12 * (p : ℤ) := by
    have hre : 6 * ((x : ℕ) : ℤ) + 12 * (p : ℤ) =
        ((x : ℕ) : ℤ) ^ 2 + ((p : ℤ) * ((y : ℕ) : ℤ)) ^ 2 := by nlinarith only [heq]
    rw [hre]
    exact h9
  have h12 : (9 : ℤ) ∣ 12 * (p : ℤ) := by
    have hsub := dvd_sub hsum9 hx9
    have hre : (6 * ((x : ℕ) : ℤ) + 12 * (p : ℤ)) - 6 * ((x : ℕ) : ℤ) =
        12 * (p : ℤ) := by ring
    rw [hre] at hsub
    exact hsub
  have hmod := Int.dvd_iff_emod_eq_zero.mp h12
  have hp3int : (3 : ℤ) ∣ (p : ℤ) := Int.dvd_iff_emod_eq_zero.mpr (by omega)
  have hp3 : 3 ∣ p := by exact_mod_cast hp3int
  exact ((hp.eq_one_or_self_of_dvd 3 hp3).resolve_left (by norm_num)).symm

/-- Bài tập 1.4.11(a): toàn bộ nghiệm x,y dương và p nguyên tố. -/
theorem first_prime_square_equation_solutions (x y : ℕ+) (p : ℕ) (hp : Nat.Prime p) :
    (((x : ℕ) : ℤ) ^ 2 + (p : ℤ) ^ 2 * ((y : ℕ) : ℤ) ^ 2 =
      6 * (((x : ℕ) : ℤ) + 2 * p)) ↔
    (x = 9 ∧ y = 1 ∧ p = 3) ∨ (x = 6 ∧ y = 2 ∧ p = 3) := by
  constructor
  · intro heq
    have hp3 := prime_eq_three_of_first_equation x y p hp heq
    subst p
    norm_num at heq
    have hxpos : (1 : ℤ) ≤ (x : ℕ) := by exact_mod_cast x.pos
    have hypos : (1 : ℤ) ≤ (y : ℕ) := by exact_mod_cast y.pos
    have hs := sq_nonneg (((x : ℕ) : ℤ) - 3)
    have hybound : ((y : ℕ) : ℤ) ≤ 2 := by nlinarith
    have hychoice : (y : ℕ) = 1 ∨ (y : ℕ) = 2 := by omega
    rcases hychoice with hy | hy
    · have hyreal : ((y : ℕ) : ℤ) = 1 := by exact_mod_cast hy
      rw [hyreal] at heq
      have hfactor : (((x : ℕ) : ℤ) - 9) * (((x : ℕ) : ℤ) + 3) = 0 := by nlinarith
      have hx : (x : ℕ) = 9 := by
        rcases mul_eq_zero.mp hfactor with h | h
        · exact_mod_cast (show ((x : ℕ) : ℤ) = 9 by linarith)
        · linarith
      exact Or.inl ⟨by apply Subtype.ext; exact hx, by apply Subtype.ext; exact hy, rfl⟩
    · have hyreal : ((y : ℕ) : ℤ) = 2 := by exact_mod_cast hy
      rw [hyreal] at heq
      have hfactor : ((x : ℕ) : ℤ) * (((x : ℕ) : ℤ) - 6) = 0 := by nlinarith
      have hx : (x : ℕ) = 6 := by
        rcases mul_eq_zero.mp hfactor with h | h
        · linarith
        · exact_mod_cast (show ((x : ℕ) : ℤ) = 6 by linarith)
      exact Or.inr ⟨by apply Subtype.ext; exact hx, by apply Subtype.ext; exact hy, rfl⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

/-- Bài tập 1.4.11(b): phương trình buộc p=3. -/
lemma prime_eq_three_of_second_equation (x y : ℕ+) (p : ℕ) (hp : Nat.Prime p)
    (heq : ((x : ℕ) : ℤ) ^ 2 - 3 * ((x : ℕ) : ℤ) * ((y : ℕ) : ℤ) +
      (p : ℤ) ^ 2 * ((y : ℕ) : ℤ) ^ 2 = 12 * p) : p = 3 := by
  have hsum : ((x : ℕ) : ℤ) ^ 2 + ((p : ℤ) * ((y : ℕ) : ℤ)) ^ 2 =
      3 * ((x : ℕ) : ℤ) * ((y : ℕ) : ℤ) + 12 * p := by nlinarith only [heq]
  have h3 : (3 : ℤ) ∣ ((x : ℕ) : ℤ) ^ 2 + ((p : ℤ) * ((y : ℕ) : ℤ)) ^ 2 := by
    rw [hsum]
    exact ⟨((x : ℕ) : ℤ) * ((y : ℕ) : ℤ) + 4 * p, by ring⟩
  obtain ⟨hx3, hpy3⟩ := three_dvd_each_of_sum_squares _ _ h3
  have h9 := nine_dvd_sum_squares_of_three_dvd _ _ hx3 hpy3
  have hxy9 : (9 : ℤ) ∣ 3 * ((x : ℕ) : ℤ) * ((y : ℕ) : ℤ) := by
    obtain ⟨a, ha⟩ := hx3
    exact ⟨a * ((y : ℕ) : ℤ), by rw [ha]; ring⟩
  rw [hsum] at h9
  have h12 : (9 : ℤ) ∣ 12 * (p : ℤ) := by
    have hsub := dvd_sub h9 hxy9
    have hre : (3 * ((x : ℕ) : ℤ) * ((y : ℕ) : ℤ) + 12 * (p : ℤ)) -
        3 * ((x : ℕ) : ℤ) * ((y : ℕ) : ℤ) = 12 * (p : ℤ) := by ring
    rw [hre] at hsub
    exact hsub
  have hmod := Int.dvd_iff_emod_eq_zero.mp h12
  have hp3int : (3 : ℤ) ∣ (p : ℤ) := Int.dvd_iff_emod_eq_zero.mpr (by omega)
  have hp3 : 3 ∣ p := by exact_mod_cast hp3int
  exact ((hp.eq_one_or_self_of_dvd 3 hp3).resolve_left (by norm_num)).symm

/-- Bài tập 1.4.11(b): nghiệm dương duy nhất là x=6, y=2, p=3; phép trừ lấy trong ℤ. -/
theorem second_prime_square_equation_solutions (x y : ℕ+) (p : ℕ) (hp : Nat.Prime p) :
    (((x : ℕ) : ℤ) ^ 2 - 3 * ((x : ℕ) : ℤ) * ((y : ℕ) : ℤ) +
      (p : ℤ) ^ 2 * ((y : ℕ) : ℤ) ^ 2 = 12 * p) ↔ x = 6 ∧ y = 2 ∧ p = 3 := by
  constructor
  · intro heq
    have hp3 := prime_eq_three_of_second_equation x y p hp heq
    subst p
    norm_num at heq
    have hxpos : (1 : ℤ) ≤ (x : ℕ) := by exact_mod_cast x.pos
    have hypos : (1 : ℤ) ≤ (y : ℕ) := by exact_mod_cast y.pos
    have hs := sq_nonneg (2 * ((x : ℕ) : ℤ) - 3 * ((y : ℕ) : ℤ))
    have hybound : ((y : ℕ) : ℤ) ≤ 2 := by nlinarith
    have hychoice : (y : ℕ) = 1 ∨ (y : ℕ) = 2 := by omega
    rcases hychoice with hy | hy
    · have hyint : ((y : ℕ) : ℤ) = 1 := by exact_mod_cast hy
      rw [hyint] at heq
      have hxchoice : ((x : ℕ) : ℤ) ≤ 6 ∨ 7 ≤ ((x : ℕ) : ℤ) := by omega
      rcases hxchoice with hx | hx
      · have hprod := mul_nonneg (show (0 : ℤ) ≤ (x : ℕ) by omega)
          (show (0 : ℤ) ≤ 6 - ((x : ℕ) : ℤ) by omega)
        nlinarith
      · have hprod := mul_nonneg (show (0 : ℤ) ≤ ((x : ℕ) : ℤ) - 7 by omega)
          (show (0 : ℤ) ≤ ((x : ℕ) : ℤ) + 4 by omega)
        nlinarith
    · have hyint : ((y : ℕ) : ℤ) = 2 := by exact_mod_cast hy
      rw [hyint] at heq
      have hfactor : ((x : ℕ) : ℤ) * (((x : ℕ) : ℤ) - 6) = 0 := by nlinarith
      have hx : (x : ℕ) = 6 := by
        rcases mul_eq_zero.mp hfactor with h | h
        · linarith
        · exact_mod_cast (show ((x : ℕ) : ℤ) = 6 by linarith)
      exact ⟨by apply Subtype.ext; exact hx, by apply Subtype.ext; exact hy, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

end calculus.Chapter01.Section04Arithmetic
