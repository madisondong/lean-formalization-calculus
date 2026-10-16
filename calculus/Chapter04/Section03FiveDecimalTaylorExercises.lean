import calculus.Chapter04.Section03TaylorElementary
import calculus.Chapter04.Section03TrigonometricMaclaurin
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# §4.3 — Bài 29: xấp xỉ Taylor và làm tròn năm chữ số

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1357–1361.
-/

set_option autoImplicit false
noncomputable section
open Set Finset
open scoped BigOperators
namespace calculus.Chapter04.Section03FiveDecimalTaylorExercises
open calculus.Chapter04.Section03TaylorElementary
open calculus.Chapter04.Section03TrigonometricMaclaurin

/-- Sai số làm tròn nhỏ hơn nửa đơn vị ở chữ số thập phân thứ năm. -/
def RoundsToFiveDecimals (value : ℝ) (digits : ℤ) : Prop :=
  |value - (digits : ℝ) / 100000| < (1 / 200000 : ℝ)

theorem rounds_to_five_decimals_iff (value : ℝ) (digits : ℤ) :
    RoundsToFiveDecimals value digits ↔
      (digits : ℝ) / 100000 - 1 / 200000 < value ∧
        value < (digits : ℝ) / 100000 + 1 / 200000 := by
  unfold RoundsToFiveDecimals
  rw [abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith


theorem square_taylor_certificate (a t : ℝ) (hne : a ≠ t) :
    ∃ c ∈ uIoo a t,
      iteratedDeriv 3 (fun y : ℝ ↦ y ^ 2) c = 0 ∧
        t ^ 2 = a ^ 2 + 2 * a * (t - a) + (t - a) ^ 2 := by
  have hf : ContDiff ℝ 3 (fun y : ℝ ↦ y ^ 2) := contDiff_id.pow 2
  obtain ⟨c, hc, he⟩ := global_taylor_lagrange 2 hf hne
  have hz : iteratedDeriv 3 (fun y : ℝ ↦ y ^ 2) c = 0 := by
    norm_num [iteratedDeriv_pow, Nat.descFactorial]
  refine ⟨c, hc, hz, ?_⟩
  norm_num [sum_range_succ, iteratedDeriv_pow, Nat.descFactorial] at he
  exact he


theorem cube_taylor_certificate (a t : ℝ) (hne : a ≠ t) :
    ∃ c ∈ uIoo a t,
      iteratedDeriv 4 (fun y : ℝ ↦ y ^ 3) c = 0 ∧
        t ^ 3 = a ^ 3 + 3 * a ^ 2 * (t - a) +
          3 * a * (t - a) ^ 2 + (t - a) ^ 3 := by
  have hf : ContDiff ℝ 4 (fun y : ℝ ↦ y ^ 3) := contDiff_id.pow 3
  obtain ⟨c, hc, he⟩ := global_taylor_lagrange 3 hf hne
  have hz : iteratedDeriv 4 (fun y : ℝ ↦ y ^ 3) c = 0 := by
    norm_num [iteratedDeriv_pow, Nat.descFactorial]
  refine ⟨c, hc, hz, ?_⟩
  norm_num [sum_range_succ, iteratedDeriv_pow, Nat.descFactorial] at he
  nlinarith [he]

theorem sqrt_two_rounds_to_five_decimals :
    RoundsToFiveDecimals (Real.sqrt 2) 141421 := by
  apply (rounds_to_five_decimals_iff _ _).mpr
  have hr : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · by_contra h
    have hh := pow_le_pow_left₀ hr (le_of_not_gt h) 2
    rw [hs] at hh
    norm_num at hh
  · by_contra h
    have hq : (0 : ℝ) ≤ (141421 : ℤ) / 100000 + 1 / 200000 := by norm_num
    have hh := pow_le_pow_left₀ hq (le_of_not_gt h) 2
    rw [hs] at hh
    norm_num at hh

/-- Căn bậc ba thực dương của `0,3 = 3/10`. -/
def cubeRootThreeTenths : ℝ := (3 / 10 : ℝ) ^ (1 / 3 : ℝ)

theorem cube_root_three_tenths_pos : 0 < cubeRootThreeTenths :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem cube_root_three_tenths_cube : cubeRootThreeTenths ^ 3 = (3 / 10 : ℝ) := by
  simpa only [cubeRootThreeTenths, Nat.cast_ofNat, one_div] using
    Real.rpow_inv_natCast_pow (x := (3 / 10 : ℝ)) (n := 3) (by norm_num) (by decide)

theorem cube_root_three_tenths_rounds_to_five_decimals :
    RoundsToFiveDecimals cubeRootThreeTenths 66943 := by
  apply (rounds_to_five_decimals_iff _ _).mpr
  have hr : 0 ≤ cubeRootThreeTenths := cube_root_three_tenths_pos.le
  constructor
  · by_contra h
    have hh := pow_le_pow_left₀ hr (le_of_not_gt h) 3
    rw [cube_root_three_tenths_cube] at hh
    norm_num at hh
  · by_contra h
    have hq : (0 : ℝ) ≤ (66943 : ℤ) / 100000 + 1 / 200000 := by norm_num
    have hh := pow_le_pow_left₀ hq (le_of_not_gt h) 3
    rw [cube_root_three_tenths_cube] at hh
    norm_num at hh

theorem cosine_taylor_sum_ten_at_one :
    (∑ k ∈ range 6, (-1 : ℝ) ^ k / ((2 * k).factorial : ℝ)) =
      (1960649 / 3628800 : ℝ) := by
  norm_num [sum_range_succ, Nat.factorial]


theorem cosine_one_taylor_certificate :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.cos 1 = 1960649 / 3628800 +
        Real.cos (θ + 11 * Real.pi / 2) / 39916800 := by
  obtain ⟨θ, hθ, he⟩ := cosine_maclaurin 5 (by decide) 1
  refine ⟨θ, hθ, ?_⟩
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat, one_pow, mul_one,
    cosine_taylor_sum_ten_at_one, Nat.factorial] at he
  exact he

theorem cosine_one_taylor_error_bound :
    |Real.cos 1 - 1960649 / 3628800| ≤ (1 / 39916800 : ℝ) := by
  obtain ⟨θ, _, he⟩ := cosine_one_taylor_certificate
  have hd : Real.cos 1 - 1960649 / 3628800 =
      Real.cos (θ + 11 * Real.pi / 2) / 39916800 := by linarith
  calc
    |Real.cos 1 - 1960649 / 3628800| =
        |Real.cos (θ + 11 * Real.pi / 2)| / 39916800 := by
      rw [hd, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 39916800)]
    _ ≤ 1 / 39916800 :=
      div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by norm_num)

theorem cosine_one_rounds_to_five_decimals :
    RoundsToFiveDecimals (Real.cos 1) 54030 := by
  change |Real.cos 1 - 54030 / 100000| < (1 / 200000 : ℝ)
  calc
    |Real.cos 1 - 54030 / 100000| ≤
        |Real.cos 1 - 1960649 / 3628800| + |1960649 / 3628800 - 54030 / 100000| :=
      abs_sub_le _ _ _
    _ ≤ 1 / 39916800 + |1960649 / 3628800 - 54030 / 100000| :=
      add_le_add cosine_one_taylor_error_bound (le_refl _)
    _ < 1 / 200000 := by norm_num

/-- Bài 29(a): `√2` làm tròn đến năm chữ số sau dấu phẩy là `1,41421`. -/
theorem source_sqrt_two_five_decimal_approximation :
    ∃ c ∈ uIoo (7 / 5 : ℝ) (Real.sqrt 2),
      iteratedDeriv 3 (fun y : ℝ ↦ y ^ 2) c = 0 ∧
        (Real.sqrt 2) ^ 2 = (7 / 5 : ℝ) ^ 2 +
          2 * (7 / 5) * (Real.sqrt 2 - 7 / 5) + (Real.sqrt 2 - 7 / 5) ^ 2 ∧
        RoundsToFiveDecimals (Real.sqrt 2) 141421 := by
  have hne : (7 / 5 : ℝ) ≠ Real.sqrt 2 := by
    intro h
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [← h] at hs
    norm_num at hs
  obtain ⟨c, hc, hz, he⟩ := square_taylor_certificate (7 / 5) (Real.sqrt 2) hne
  exact ⟨c, hc, hz, he, sqrt_two_rounds_to_five_decimals⟩

/-- Bài 29(b): căn bậc ba của `0,3` làm tròn là `0,66943`. -/
theorem source_cube_root_three_tenths_five_decimal_approximation :
    0 < cubeRootThreeTenths ∧ cubeRootThreeTenths ^ 3 = (3 / 10 : ℝ) ∧
      ∃ c ∈ uIoo (67 / 100 : ℝ) cubeRootThreeTenths,
        iteratedDeriv 4 (fun y : ℝ ↦ y ^ 3) c = 0 ∧
          cubeRootThreeTenths ^ 3 = (67 / 100 : ℝ) ^ 3 +
            3 * (67 / 100) ^ 2 * (cubeRootThreeTenths - 67 / 100) +
            3 * (67 / 100) * (cubeRootThreeTenths - 67 / 100) ^ 2 +
            (cubeRootThreeTenths - 67 / 100) ^ 3 ∧
          RoundsToFiveDecimals cubeRootThreeTenths 66943 := by
  have hne : (67 / 100 : ℝ) ≠ cubeRootThreeTenths := by
    intro h
    have hs := cube_root_three_tenths_cube
    rw [← h] at hs
    norm_num at hs
  obtain ⟨c, hc, hz, he⟩ := cube_taylor_certificate (67 / 100) cubeRootThreeTenths hne
  exact ⟨cube_root_three_tenths_pos, cube_root_three_tenths_cube,
    c, hc, hz, he, cube_root_three_tenths_rounds_to_five_decimals⟩

/-- Bài 29(c): `cos 1` làm tròn là `0,54030`. -/
theorem source_cosine_one_five_decimal_approximation :
    (∃ θ ∈ Ioo (0 : ℝ) 1,
      Real.cos 1 = 1960649 / 3628800 +
        Real.cos (θ + 11 * Real.pi / 2) / 39916800) ∧
      |Real.cos 1 - 1960649 / 3628800| ≤ (1 / 39916800 : ℝ) ∧
      RoundsToFiveDecimals (Real.cos 1) 54030 :=
  ⟨cosine_one_taylor_certificate, cosine_one_taylor_error_bound,
    cosine_one_rounds_to_five_decimals⟩

end calculus.Chapter04.Section03FiveDecimalTaylorExercises
