import calculus.Chapter02.Section06Supplement

/-!
# Bài 2.6.23–24: trung bình nhân và giới hạn căn

Nguồn: `source/Ch2_dayso.tex`, dòng 2177–2184; mã C02-S07-exercise-005/006.
-/
namespace calculus.Chapter02.Section06Means
open Filter Set
open scoped Topology BigOperators
open calculus.Chapter02.Section03 calculus.Chapter02.Section04 calculus.Chapter02.Section06
open calculus.Chapter02.Section06Supplement

/-- Trung bình nhân của n số hạng x₁,…,xₙ. -/
noncomputable def geometricMean (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.Icc 1 n, x k) ^ (1 / (n : ℝ))

/-- Căn bậc n của tích dương bằng mũ của trung bình logarit. -/
theorem geometricMean_eq_exp_arithmeticMean_log (x : ℕ → ℝ)
    (hx : ∀ n, 1 ≤ n → 0 < x n) (n : ℕ) :
    geometricMean x n = Real.exp (arithmeticMean (fun k => Real.log (x k)) n) := by
  have hprod : 0 < ∏ k ∈ Finset.Icc 1 n, x k :=
    Finset.prod_pos fun k hk => hx k (Finset.mem_Icc.mp hk).1
  rw [geometricMean, Real.rpow_def_of_pos hprod, Real.log_prod]
  · congr 1
    simp only [arithmeticMean, div_eq_mul_inv, one_mul]
  · intro k hk
    exact (hx k (Finset.mem_Icc.mp hk).1).ne'

/-- Trung bình nhân có cùng giới hạn với dãy hội tụ về số dương. -/
theorem geometricMean_converges_of_positive_limit (x : ℕ → ℝ) (a : ℝ)
    (hx : ∀ n, 1 ≤ n → 0 < x n) (ha : 0 < a) (hlim : ConvergesTo x a) :
    ConvergesTo (geometricMean x) a := by
  have hlog : ConvergesTo (fun n => Real.log (x n)) (Real.log a) :=
    convergesTo_iff_tendsto.mpr ((convergesTo_iff_tendsto.mp hlim).log ha.ne')
  have hmean := arithmeticMean_converges (fun n => Real.log (x n)) (Real.log a) hlog
  apply convergesTo_iff_tendsto.mpr
  have h := Real.continuous_exp.continuousAt.tendsto.comp (convergesTo_iff_tendsto.mp hmean)
  rw [Real.exp_log ha] at h
  apply h.congr
  intro n
  dsimp only [Function.comp_def]
  exact (geometricMean_eq_exp_arithmeticMean_log x hx n).symm

/-- Bài 2.6.23: trung bình nhân tiến về 0 khi giới hạn số hạng bằng 0. -/
theorem geometricMean_converges_zero (x : ℕ → ℝ)
    (hx : ∀ n, 1 ≤ n → 0 < x n) (hlim : ConvergesTo x 0) :
    ConvergesTo (geometricMean x) 0 := by
  intro ε hε
  let q := ε / 2
  have hq : 0 < q := by dsimp [q]; positivity
  let v := fun n => max (x n) q
  have hvpos : ∀ n, 1 ≤ n → 0 < v n := fun n _ => hq.trans_le (le_max_right _ _)
  have hvlim : ConvergesTo v q := by
    apply convergesTo_iff_tendsto.mpr
    simpa only [v, max_eq_right hq.le] using
      (convergesTo_iff_tendsto.mp hlim).max (tendsto_const_nhds (x := q))
  obtain ⟨N, hN, htail⟩ := geometricMean_converges_of_positive_limit v q hvpos hq hvlim q hq
  refine ⟨N, hN, ?_⟩
  intro n hn
  have hprod : 0 ≤ ∏ k ∈ Finset.Icc 1 n, x k :=
    Finset.prod_nonneg fun k hk => (hx k (Finset.mem_Icc.mp hk).1).le
  have hprodle : (∏ k ∈ Finset.Icc 1 n, x k) ≤ ∏ k ∈ Finset.Icc 1 n, v k := by
    apply Finset.prod_le_prod
    · intro k hk
      exact (hx k (Finset.mem_Icc.mp hk).1).le
    · intro k _
      exact le_max_left _ _
  have hle : geometricMean x n ≤ geometricMean v n :=
    Real.rpow_le_rpow hprod hprodle (by positivity)
  have hnneg : 0 ≤ geometricMean x n := Real.rpow_nonneg hprod _
  have hbound := (abs_lt.mp (htail n hn)).2
  rw [sub_zero, abs_of_nonneg hnneg]
  dsimp [q] at hbound
  linarith

/-- Bài 2.6.23: trung bình nhân có cùng giới hạn với dãy dương, kể cả giới hạn 0. -/
theorem geometricMean_converges (x : ℕ → ℝ) (a : ℝ)
    (hx : ∀ n, 1 ≤ n → 0 < x n) (hlim : ConvergesTo x a) :
    ConvergesTo (geometricMean x) a := by
  have hnonneg : 0 ≤ a := limit_le_of_converges (fun _ => 0) x 0 a
    (constant_converges 0) hlim (fun n hn => (hx n hn).le)
  rcases eq_or_lt_of_le hnonneg with ha | ha
  · subst a
    exact geometricMean_converges_zero x hx hlim
  · exact geometricMean_converges_of_positive_limit x a hx ha hlim

/-- Tỉ số đầu bằng x₁; từ n≥2, dùng xₙ/xₙ₋₁. -/
noncomputable def successiveRatioWithInitialTerm (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 1 then x 1 else x n / x (n - 1)

/-- Tỉ số của hai số hạng kế tiếp tại n≥2. -/
theorem successiveRatioWithInitialTerm_converges (x : ℕ → ℝ) (a : ℝ)
    (hratio : ConvergesTo (fun n => x (n + 1) / x n) a) :
    ConvergesTo (successiveRatioWithInitialTerm x) a := by
  apply convergesTo_iff_tendsto.mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply (convergesTo_iff_tendsto.mp hratio).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [successiveRatioWithInitialTerm, if_neg (show n + 1 ≠ 1 by omega), Nat.add_sub_cancel]

/-- Tích các tỉ số tại chỉ số dương rút gọn thành số hạng cuối. -/
theorem successiveRatioWithInitialTerm_product (x : ℕ → ℝ) (hx : ∀ n, 1 ≤ n → 0 < x n) :
    ∀ n, 1 ≤ n → (∏ k ∈ Finset.Icc 1 n, successiveRatioWithInitialTerm x k) = x n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [successiveRatioWithInitialTerm]
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    simp only [successiveRatioWithInitialTerm, if_neg (show n + 1 ≠ 1 by omega), Nat.add_sub_cancel]
    field_simp [(hx n hn).ne']

/-- Bài 2.6.24: giới hạn tỉ số kéo theo giới hạn căn, cả trường hợp a=0. -/
theorem nat_root_converges_of_ratio (x : ℕ → ℝ) (a : ℝ)
    (hx : ∀ n, 1 ≤ n → 0 < x n)
    (hratio : ConvergesTo (fun n => x (n + 1) / x n) a) :
    ConvergesTo (fun n : ℕ => x n ^ (1 / (n : ℝ))) a := by
  have hrpos : ∀ n, 1 ≤ n → 0 < successiveRatioWithInitialTerm x n := by
    intro n hn
    dsimp only [successiveRatioWithInitialTerm]
    split_ifs with heq
    · exact hx 1 (by omega)
    · exact div_pos (hx n hn) (hx (n - 1) (by omega))
  have hmean := geometricMean_converges (successiveRatioWithInitialTerm x) a hrpos (successiveRatioWithInitialTerm_converges x a hratio)
  apply convergesTo_iff_tendsto.mpr
  apply (convergesTo_iff_tendsto.mp hmean).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [geometricMean, successiveRatioWithInitialTerm_product x hx n hn]

end calculus.Chapter02.Section06Means
