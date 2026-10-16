import calculus.Chapter02.Section04
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast

/-!
# Mục 2.4: giới hạn hệ số nhị thức

Nguồn: `source/Ch2_dayso.tex`, dòng 1590–1603; Bài 2.4.12(a,b).
-/
namespace calculus.Chapter02.Section04Binomial
open Filter
open scoped Topology
open calculus.Chapter02.Section03


theorem iterated_pow_swap (a : ℝ) (k n : ℕ) : (a ^ k) ^ n = (a ^ n) ^ k := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm k n]


theorem stirling_denominator_scale (k n : ℕ) :
    Real.sqrt (2 * ((k * n : ℕ) : ℝ)) * (((k * n : ℕ) : ℝ) / Real.exp 1) ^ (k * n) =
      (Real.sqrt (k : ℝ) * Real.sqrt (2 * (n : ℝ))) *
        ((k : ℝ) ^ k) ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ k := by
  have hs : Real.sqrt (2 * ((k * n : ℕ) : ℝ)) =
      Real.sqrt (k : ℝ) * Real.sqrt (2 * (n : ℝ)) := by
    rw [show 2 * ((k * n : ℕ) : ℝ) = (k : ℝ) * (2 * (n : ℝ)) by push_cast; ring]
    exact Real.sqrt_mul (Nat.cast_nonneg k) _
  have hp : (((k * n : ℕ) : ℝ) / Real.exp 1) ^ (k * n) =
      ((k : ℝ) ^ k) ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ k := by
    rw [show ((k * n : ℕ) : ℝ) / Real.exp 1 = (k : ℝ) * ((n : ℝ) / Real.exp 1) by
      push_cast; ring, mul_pow, pow_mul, pow_mul, iterated_pow_swap ((n : ℝ) / Real.exp 1) k n]
  rw [hs, hp]
  ring


theorem factorial_stirling_scaled (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k * n).factorial : ℝ) = Stirling.stirlingSeq (k * n) * Real.sqrt (k : ℝ) *
      Real.sqrt (2 * (n : ℝ)) * ((k : ℝ) ^ k) ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ k := by
  have hkn : (0 : ℝ) < ((k * n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < k) (by omega : 0 < n)
  have hd : Real.sqrt (2 * ((k * n : ℕ) : ℝ)) *
      (((k * n : ℕ) : ℝ) / Real.exp 1) ^ (k * n) ≠ 0 := by positivity
  have he : ((k * n).factorial : ℝ) = Stirling.stirlingSeq (k * n) *
      (Real.sqrt (2 * ((k * n : ℕ) : ℝ)) * (((k * n : ℕ) : ℝ) / Real.exp 1) ^ (k * n)) := by
    unfold Stirling.stirlingSeq
    exact (div_mul_cancel₀ _ hd).symm
  rw [stirling_denominator_scale] at he
  simpa only [mul_assoc] using he


theorem stirling_positive (n : ℕ) (hn : 1 ≤ n) : 0 < Stirling.stirlingSeq n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold Stirling.stirlingSeq
  positivity

/-- Bài 2.4.12(a): dãy C₄ₙ²ⁿ/(4ⁿC₂ₙⁿ). -/
noncomputable def centralBinomialScalingRatio (n : ℕ) : ℝ :=
  ((4 * n).choose (2 * n) : ℝ) / ((4 : ℝ) ^ n * ((2 * n).choose n : ℝ))

/-- Bài 2.4.12(b): dãy 3³ⁿ(C₂ₙⁿ)²/(C₃ₙⁿC₆ₙ³ⁿ). -/
noncomputable def tripleBinomialScalingRatio (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (3 * n) * ((2 * n).choose n : ℝ) ^ 2 /
    (((3 * n).choose n : ℝ) * ((6 * n).choose (3 * n) : ℝ))

/-- Bài 2.4.12(a): công thức giai thừa của dãy. -/
theorem central_binomial_ratio_factorial (n : ℕ) :
    centralBinomialScalingRatio n =
      ((4 * n).factorial : ℝ) * (n.factorial : ℝ) ^ 2 /
        ((4 : ℝ) ^ n * ((2 * n).factorial : ℝ) ^ 3) := by
  unfold centralBinomialScalingRatio
  rw [Nat.cast_choose ℝ (show 2 * n ≤ 4 * n by omega), Nat.cast_choose ℝ (show n ≤ 2 * n by omega),
    show 4 * n - 2 * n = 2 * n by omega, show 2 * n - n = n by omega]
  field_simp

/-- Bài 2.4.12(b): công thức giai thừa của dãy. -/
theorem triple_binomial_ratio_factorial (n : ℕ) :
    tripleBinomialScalingRatio n =
      (3 : ℝ) ^ (3 * n) * ((2 * n).factorial : ℝ) ^ 3 * ((3 * n).factorial : ℝ) /
        ((n.factorial : ℝ) ^ 3 * ((6 * n).factorial : ℝ)) := by
  unfold tripleBinomialScalingRatio
  rw [Nat.cast_choose ℝ (show n ≤ 2 * n by omega), Nat.cast_choose ℝ (show n ≤ 3 * n by omega),
    Nat.cast_choose ℝ (show 3 * n ≤ 6 * n by omega),
    show 2 * n - n = n by omega, show 3 * n - n = 2 * n by omega,
    show 6 * n - 3 * n = 3 * n by omega]
  field_simp

/-- Bài 2.4.12(a): dạng chuẩn hóa với hệ số 1/√2. -/
theorem central_binomial_ratio_stirling (n : ℕ) (hn : 1 ≤ n) :
    centralBinomialScalingRatio n =
      (1 / Real.sqrt 2) * (Stirling.stirlingSeq (4 * n) * Stirling.stirlingSeq n ^ 2 /
        Stirling.stirlingSeq (2 * n) ^ 3) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 := factorial_stirling_scaled 1 n (by omega) hn
  have h2 := factorial_stirling_scaled 2 n (by omega) hn
  have h4 := factorial_stirling_scaled 4 n (by omega) hn
  norm_num at h1 h2 h4
  have hs4 : Real.sqrt 4 = (2 : ℝ) := by
    calc
      Real.sqrt 4 = Real.sqrt ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 := Real.sqrt_sq (by norm_num)
  rw [hs4] at h4
  have h256 : (256 : ℝ) ^ n = ((4 : ℝ) ^ n) ^ 4 := by
    calc
      (256 : ℝ) ^ n = ((4 : ℝ) ^ 4) ^ n := by norm_num
      _ = ((4 : ℝ) ^ n) ^ 4 := iterated_pow_swap _ _ _
  have hs3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [central_binomial_ratio_factorial, h1, h2, h4, h256]
  simp only [mul_pow]
  rw [hs3]
  have hS2 := (stirling_positive (2 * n) (by omega)).ne'
  have hT : Real.sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
  have hP : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
  have hA : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hS2, hT, hP, hA, hs2]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Bài 2.4.12(b): dạng chuẩn hóa với hệ số 2. -/
theorem triple_binomial_ratio_stirling (n : ℕ) (hn : 1 ≤ n) :
    tripleBinomialScalingRatio n = 2 *
      (Stirling.stirlingSeq (2 * n) ^ 3 * Stirling.stirlingSeq (3 * n) /
        (Stirling.stirlingSeq n ^ 3 * Stirling.stirlingSeq (6 * n))) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 := factorial_stirling_scaled 1 n (by omega) hn
  have h2 := factorial_stirling_scaled 2 n (by omega) hn
  have h3 := factorial_stirling_scaled 3 n (by omega) hn
  have h6 := factorial_stirling_scaled 6 n (by omega) hn
  norm_num at h1 h2 h3 h6
  have h27 : (3 : ℝ) ^ (3 * n) = (27 : ℝ) ^ n := by rw [pow_mul]; norm_num
  have h46656 : (46656 : ℝ) ^ n = ((4 : ℝ) ^ n) ^ 3 * ((27 : ℝ) ^ n) ^ 2 := by
    calc
      (46656 : ℝ) ^ n = ((4 : ℝ) ^ 3 * (27 : ℝ) ^ 2) ^ n := by norm_num
      _ = ((4 : ℝ) ^ n) ^ 3 * ((27 : ℝ) ^ n) ^ 2 := by
        rw [mul_pow, iterated_pow_swap (4 : ℝ) 3 n, iterated_pow_swap (27 : ℝ) 2 n]
  have hs3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    calc
      Real.sqrt 6 = Real.sqrt ((2 : ℝ) * 3) := by norm_num
      _ = Real.sqrt 2 * Real.sqrt 3 := Real.sqrt_mul (by norm_num) _
  rw [triple_binomial_ratio_factorial, h1, h2, h3, h6, h27, h46656, hs6]
  simp only [mul_pow]
  rw [hs3]
  have hS1 := (stirling_positive n hn).ne'
  have hS6 := (stirling_positive (6 * n) (by omega)).ne'
  have hT : Real.sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
  have hP : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
  have hA : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hB : (27 : ℝ) ^ n ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs3p : Real.sqrt 3 ≠ 0 := by positivity
  field_simp [hS1, hS6, hT, hP, hA, hB, hs2, hs3p]


theorem stirling_multiple_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => Stirling.stirlingSeq (k * n)) atTop (𝓝 (Real.sqrt Real.pi)) := by
  have hi : StrictMono (fun n : ℕ => k * n) :=
    fun i j hij => Nat.mul_lt_mul_of_pos_left hij (by omega)
  exact Stirling.tendsto_stirlingSeq_sqrt_pi.comp hi.tendsto_atTop

/-- Bài 2.4.12(a): giới hạn bằng 1/√2. -/
theorem central_binomial_ratio_converges :
    ConvergesTo centralBinomialScalingRatio (1 / Real.sqrt 2) := by
  have hS := Stirling.tendsto_stirlingSeq_sqrt_pi
  have h2 := stirling_multiple_tendsto 2 (by omega)
  have h4 := stirling_multiple_tendsto 4 (by omega)
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hconstant : Real.sqrt Real.pi * Real.sqrt Real.pi ^ 2 / Real.sqrt Real.pi ^ 3 = 1 := by
    field_simp
  have hratio : Tendsto (fun n : ℕ => Stirling.stirlingSeq (4 * n) * Stirling.stirlingSeq n ^ 2 /
      Stirling.stirlingSeq (2 * n) ^ 3) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_def, hconstant] using (h4.mul (hS.pow 2)).div (h2.pow 3) (pow_ne_zero _ hp)
  have ht : Tendsto (fun n : ℕ => (1 / Real.sqrt 2) *
      (Stirling.stirlingSeq (4 * n) * Stirling.stirlingSeq n ^ 2 / Stirling.stirlingSeq (2 * n) ^ 3))
      atTop (𝓝 (1 / Real.sqrt 2)) := by
    simpa using (tendsto_const_nhds (x := 1 / Real.sqrt 2)).mul hratio
  apply convergesTo_iff_tendsto.mpr
  exact ht.congr' (eventually_atTop.2 ⟨1, fun n hn => (central_binomial_ratio_stirling n hn).symm⟩)

/-- Bài 2.4.12(b): giới hạn bằng 2. -/
theorem triple_binomial_ratio_converges : ConvergesTo tripleBinomialScalingRatio 2 := by
  have hS := Stirling.tendsto_stirlingSeq_sqrt_pi
  have h2 := stirling_multiple_tendsto 2 (by omega)
  have h3 := stirling_multiple_tendsto 3 (by omega)
  have h6 := stirling_multiple_tendsto 6 (by omega)
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hratio : Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * n) ^ 3 * Stirling.stirlingSeq (3 * n) /
      (Stirling.stirlingSeq n ^ 3 * Stirling.stirlingSeq (6 * n))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_def, div_self (mul_ne_zero (pow_ne_zero 3 hp) hp)] using
      ((h2.pow 3).mul h3).div ((hS.pow 3).mul h6) (mul_ne_zero (pow_ne_zero 3 hp) hp)
  have ht : Tendsto (fun n : ℕ => 2 * (Stirling.stirlingSeq (2 * n) ^ 3 * Stirling.stirlingSeq (3 * n) /
      (Stirling.stirlingSeq n ^ 3 * Stirling.stirlingSeq (6 * n)))) atTop (𝓝 (2 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hratio
  apply convergesTo_iff_tendsto.mpr
  exact ht.congr' (eventually_atTop.2 ⟨1, fun n hn => (triple_binomial_ratio_stirling n hn).symm⟩)

end calculus.Chapter02.Section04Binomial
