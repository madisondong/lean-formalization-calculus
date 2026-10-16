import calculus.Chapter02.Section02
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Bài 2.2.2(a,b): bảng số hạng và sai số

Nguồn: `source/Ch2_dayso.tex`, dòng 791–798.
Mười số hạng đầu lấy n=2,…,11.
-/

namespace calculus.Chapter02.Section02Numerics

/-- Tử số bảng căn bậc n, mẫu 10¹⁰. -/
def roundedNatNthRootNumerator : ℕ → ℕ
  | 2 => 14142135624
  | 3 => 14422495703
  | 4 => 14142135624
  | 5 => 13797296615
  | 6 => 13480061546
  | 7 => 13204692478
  | 8 => 12968395547
  | 9 => 12765180070
  | 10 => 12589254118
  | 11 => 12435752279
  | _ => 0

/-- Lũy thừa bậc n của hai đầu khoảng kẹp chặt n. -/
theorem nat_nth_root_power_interval_certificate (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 11) :
    0 < (2 * (roundedNatNthRootNumerator n : ℝ) - 1) / 20000000000 ∧
    ((2 * (roundedNatNthRootNumerator n : ℝ) - 1) / 20000000000) ^ n < (n : ℝ) ∧
    (n : ℝ) < ((2 * (roundedNatNthRootNumerator n : ℝ) + 1) / 20000000000) ^ n := by
  interval_cases n <;> norm_num [roundedNatNthRootNumerator]

/-- Bài 2.2.2(b): mười giá trị làm tròn có sai số nhỏ hơn 5·10⁻¹¹. -/
theorem first_ten_nat_nth_roots_decimal_error (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 11) :
    |(n : ℝ) ^ (1 / (n : ℝ)) - (roundedNatNthRootNumerator n : ℝ) / 10000000000| <
      1 / 20000000000 := by
  obtain ⟨hlpos, hlo, hup⟩ := nat_nth_root_power_interval_certificate n hn hn'
  have hn0 : n ≠ 0 := by omega
  have hroot0 : 0 ≤ (n : ℝ) ^ (1 / (n : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpower : ((n : ℝ) ^ (1 / (n : ℝ))) ^ n = n := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) hn0
  have hl : (2 * (roundedNatNthRootNumerator n : ℝ) - 1) / 20000000000 <
      (n : ℝ) ^ (1 / (n : ℝ)) := by
    by_contra h
    have hp := pow_le_pow_left₀ hroot0 (le_of_not_gt h) n
    rw [hpower] at hp
    linarith
  have hu : (n : ℝ) ^ (1 / (n : ℝ)) <
      (2 * (roundedNatNthRootNumerator n : ℝ) + 1) / 20000000000 := by
    by_contra h
    have hupos : 0 ≤ (2 * (roundedNatNthRootNumerator n : ℝ) + 1) / 20000000000 := by positivity
    have hp := pow_le_pow_left₀ hupos (le_of_not_gt h) n
    rw [hpower] at hp
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩



/-- Tử số bảng n sin(1/n), mẫu 10¹⁰. -/
def roundedNatMulSinReciprocalNumerator : ℕ → ℕ
  | 2 => 9588510772
  | 3 => 9815840904
  | 4 => 9896158370
  | 5 => 9933466540
  | 6 => 9953767962
  | 7 => 9966021085
  | 8 => 9973978671
  | 9 => 9979436566
  | 10 => 9983341665
  | 11 => 9986231586
  | _ => 0

/-- Số hạng x^(2k+1)/(2k+1)! chưa gồm dấu luân phiên. -/
noncomputable def sineOddPowerTerm (x : ℝ) (k : ℕ) : ℝ :=
  x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)


theorem sineOddPowerTerm_antitone (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    Antitone (sineOddPowerTerm x) := by
  apply antitone_nat_of_succ_le
  intro k
  have hpow : x ^ (2 * (k + 1) + 1) ≤ x ^ (2 * k + 1) :=
    pow_le_pow_of_le_one hx hx' (by omega)
  have hfact : (((2 * k + 1).factorial : ℕ) : ℝ) ≤ (2 * (k + 1) + 1).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1)
  have hfactpos : (0 : ℝ) < (2 * k + 1).factorial := by
    exact_mod_cast Nat.factorial_pos (2 * k + 1)
  unfold sineOddPowerTerm
  calc x ^ (2 * (k + 1) + 1) / ((2 * (k + 1) + 1).factorial : ℝ) ≤
        x ^ (2 * k + 1) / ((2 * (k + 1) + 1).factorial : ℝ) :=
          div_le_div_of_nonneg_right hpow (by positivity)
       _ ≤ x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) :=
          div_le_div_of_nonneg_left (pow_nonneg hx _) hfactpos hfact


theorem sine_partial_sum_bounds (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    (∑ k ∈ Finset.range 6, (-1 : ℝ) ^ k * sineOddPowerTerm x k) ≤ Real.sin x ∧
    Real.sin x ≤ ∑ k ∈ Finset.range 5, (-1 : ℝ) ^ k * sineOddPowerTerm x k := by
  have hm := sineOddPowerTerm_antitone x hx hx'
  have hsum : Filter.Tendsto (fun m : ℕ ↦ ∑ k ∈ Finset.range m,
      (-1 : ℝ) ^ k * sineOddPowerTerm x k) Filter.atTop (nhds (Real.sin x)) := by
    simpa only [sineOddPowerTerm, mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  exact ⟨hm.alternating_series_le_tendsto hsum 3, hm.tendsto_le_alternating_series hsum 2⟩

/-- Các tổng riêng hữu tỉ nằm trong khoảng làm tròn của từng ô. -/
theorem nat_mul_sin_reciprocal_decimal_partial_sum_certificate (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 11) :
    (2 * (roundedNatMulSinReciprocalNumerator n : ℝ) - 1) / 20000000000 <
      (n : ℝ) * (∑ k ∈ Finset.range 6, (-1 : ℝ) ^ k * sineOddPowerTerm (1 / (n : ℝ)) k) ∧
    (n : ℝ) * (∑ k ∈ Finset.range 5, (-1 : ℝ) ^ k * sineOddPowerTerm (1 / (n : ℝ)) k) <
      (2 * (roundedNatMulSinReciprocalNumerator n : ℝ) + 1) / 20000000000 := by
  interval_cases n <;> norm_num [roundedNatMulSinReciprocalNumerator, sineOddPowerTerm, Finset.sum_range_succ]

/-- Bài 2.2.2(a): mười giá trị làm tròn có sai số nhỏ hơn 5·10⁻¹¹. -/
theorem first_ten_nat_mul_sin_reciprocal_decimal_error (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 11) :
    |(n : ℝ) * Real.sin (1 / (n : ℝ)) - (roundedNatMulSinReciprocalNumerator n : ℝ) / 10000000000| <
      1 / 20000000000 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hx : (0 : ℝ) ≤ 1 / n := by positivity
  have hx' : (1 / (n : ℝ)) ≤ 1 := (div_le_one hnpos).mpr hn1
  obtain ⟨hl, hu⟩ := sine_partial_sum_bounds (1 / (n : ℝ)) hx hx'
  obtain ⟨hcertl, hcertu⟩ := nat_mul_sin_reciprocal_decimal_partial_sum_certificate n hn hn'
  have hlo := lt_of_lt_of_le hcertl (mul_le_mul_of_nonneg_left hl hnpos.le)
  have hup := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hu hnpos.le) hcertu
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end calculus.Chapter02.Section02Numerics
