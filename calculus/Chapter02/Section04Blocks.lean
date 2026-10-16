import calculus.Chapter02.Section04
import Mathlib.Data.Nat.Find

/-!
# Bài 2.4.13: dãy lặp thành từng khối

Nguồn: `source/Ch2_dayso.tex`, dòng 1607–1613.
Khối m gồm m số hạng bằng m.
-/
namespace calculus.Chapter02.Section04Blocks
open Filter
open scoped Topology


theorem exists_block_bound (n : ℕ) : ∃ m : ℕ, 2 * n ≤ m * (m + 1) := by
  exact ⟨2 * n, by nlinarith⟩

/-- Số hạng thứ n là m nhỏ nhất thỏa n≤m(m+1)/2. -/
noncomputable def repeatedBlock (n : ℕ) : ℕ := Nat.find (exists_block_bound n)


theorem repeatedBlock_upper (n : ℕ) : 2 * n ≤ repeatedBlock n * (repeatedBlock n + 1) :=
  Nat.find_spec (exists_block_bound n)


theorem repeatedBlock_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ repeatedBlock n := by
  have h := repeatedBlock_upper n
  by_contra hc
  have hz : repeatedBlock n = 0 := by omega
  rw [hz] at h
  simp only [zero_mul] at h
  omega


theorem repeatedBlock_lower (n : ℕ) (hn : 1 ≤ n) :
    (repeatedBlock n - 1) * repeatedBlock n < 2 * n := by
  have hm := repeatedBlock_pos n hn
  have hmin := Nat.find_min (exists_block_bound n)
    (show repeatedBlock n - 1 < repeatedBlock n by omega)
  change ¬ 2 * n ≤ (repeatedBlock n - 1) * (repeatedBlock n - 1 + 1) at hmin
  rw [Nat.sub_add_cancel hm] at hmin
  omega

/-- Quy luật khối: giá trị m xuất hiện đúng ở các chỉ số T(m−1)<n≤T(m). -/
theorem repeatedBlock_eq_iff (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    repeatedBlock n = m ↔ (m - 1) * m < 2 * n ∧ 2 * n ≤ m * (m + 1) := by
  constructor
  · intro he
    simpa [he] using And.intro (repeatedBlock_lower n hn) (repeatedBlock_upper n)
  · rintro ⟨hl, hu⟩
    have hle : repeatedBlock n ≤ m := Nat.find_min' (exists_block_bound n) hu
    have hnpos := repeatedBlock_pos n hn
    have hupper := repeatedBlock_upper n
    by_contra hne
    have hlt : repeatedBlock n ≤ m - 1 := by omega
    have hmul : repeatedBlock n * (repeatedBlock n + 1) ≤ (m - 1) * m :=
      Nat.mul_le_mul hlt (by omega)
    omega


theorem repeatedBlock_sqrt_bound (n : ℕ) (hn : 1 ≤ n) :
    |(repeatedBlock n : ℝ) - √(2 * (n : ℝ))| ≤ 1 := by
  have hm : 1 ≤ (repeatedBlock n : ℝ) := by exact_mod_cast repeatedBlock_pos n hn
  have hu : 2 * (n : ℝ) ≤ (repeatedBlock n : ℝ) * (repeatedBlock n + 1) := by
    exact_mod_cast repeatedBlock_upper n
  have hl : ((repeatedBlock n : ℝ) - 1) * repeatedBlock n < 2 * n := by
    have h := repeatedBlock_lower n hn
    have hsub : ((repeatedBlock n - 1 : ℕ) : ℝ) = (repeatedBlock n : ℝ) - 1 := by
      rw [Nat.cast_sub (repeatedBlock_pos n hn), Nat.cast_one]
    have hreal : ((repeatedBlock n - 1 : ℕ) : ℝ) * repeatedBlock n < 2 * n := by
      exact_mod_cast h
    simpa only [hsub] using hreal
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (n : ℝ) by positivity)
  have hs0 := Real.sqrt_nonneg (2 * (n : ℝ))
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((repeatedBlock n : ℝ) - 1),
    sq_nonneg ((repeatedBlock n : ℝ) + 1)]

/-- Bài 2.4.13: a_n/√n→√2. -/
theorem repeatedBlock_div_sqrt_tendsto :
    Tendsto (fun n : ℕ ↦ (repeatedBlock n : ℝ) / √(n : ℝ)) atTop (𝓝 (√(2 : ℝ))) := by
  have hr : Tendsto (fun n : ℕ ↦ 1 / √(n : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have habs : Tendsto (fun n : ℕ ↦ |(repeatedBlock n : ℝ) / √(n : ℝ) - √(2 : ℝ)|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ hr
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hspos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
    have he : (repeatedBlock n : ℝ) / √(n : ℝ) - √(2 : ℝ) =
        ((repeatedBlock n : ℝ) - √(2 * (n : ℝ))) / √(n : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    rw [he, abs_div, abs_of_pos hspos]
    exact div_le_div_of_nonneg_right (repeatedBlock_sqrt_bound n hn) (le_of_lt hspos)
  exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa only [Real.norm_eq_abs] using habs)

/-- Bài 2.4.13: aₙ/√n→√2 theo định nghĩa ε–N. -/
theorem repeatedBlock_div_sqrt_converges :
    Section03.ConvergesTo (fun n : ℕ ↦ (repeatedBlock n : ℝ) / √(n : ℝ)) (√(2 : ℝ)) :=
  Section03.convergesTo_iff_tendsto.mpr repeatedBlock_div_sqrt_tendsto

end calculus.Chapter02.Section04Blocks
