import calculus.Chapter02.Section04
import calculus.Chapter02.Section01Exercises
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Field

/-!
# Mục 2.4: bài tập bổ sung

Nguồn: `source/Ch2_dayso.tex`: Bài 2.4.2, 2.4.4, 2.4.6(b), 2.4.7(a), 2.4.9(e), 2.4.11(d).
-/

namespace calculus.Chapter02.Section04Supplement

open Filter Set
open scoped Topology


theorem one_add_sum_le_product {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hxi := hx i (Finset.mem_insert_self i s)
    have hxs : ∀ j ∈ s, 0 ≤ x j := fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)
    have hsum := Finset.sum_nonneg hxs
    have hprod := mul_le_mul_of_nonneg_left (ih hxs) (by linarith : 0 ≤ 1 + x i)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith

/-- Bài 2.4.2: tích hữu hạn của các số hạng đã cho. -/
noncomputable def fractionalProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + ((k : ℝ) + 1) / n)

/-- Bài 2.4.2: tích không nhỏ hơn 1+(n+1)/2. -/
theorem fractionalProduct_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    1 + ((n : ℝ) + 1) / 2 ≤ fractionalProduct n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h := one_add_sum_le_product (Finset.range n)
    (fun k : ℕ ↦ ((k : ℝ) + 1) / n) (by intros; positivity)
  rw [← Finset.sum_div, Section01Exercises.sum_first_naturals] at h
  have heq : ((n : ℝ) * (n + 1) / 2) / n = (n + 1) / 2 := by field_simp
  simpa [fractionalProduct, heq] using h

/-- Bài 2.4.2: tích không bị chặn trên. -/
theorem fractionalProduct_unbounded : ¬ Section04.SequenceBounded fractionalProduct := by
  rintro ⟨⟨M, hM⟩, _⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * M) 1 : ℝ)
  have hpos : 1 ≤ n := by
    have h := lt_of_le_of_lt (le_max_right (2 * M) 1) hn
    exact_mod_cast (le_of_lt h)
  have hl := fractionalProduct_lower_bound n hpos
  have hu := hM n hpos
  have hgt := lt_of_le_of_lt (le_max_left (2 * M) 1) hn
  linarith

/-- Bài 2.4.4: mọi số hạng không nhỏ hơn 1. -/
theorem inverse_square_recurrence_positive (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = u n + 1 / (u n) ^ 2) :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ u n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [hfirst]
  | succ n hn ih =>
    rw [hnext n hn]
    have h : 0 ≤ 1 / (u n) ^ 2 := by positivity
    linarith

/-- Bài 2.4.4: cận tăng trưởng lập phương của dãy truy hồi. -/
theorem inverse_square_cube_gain (x : ℝ) (hx : 0 < x) :
    x ^ 3 + 3 ≤ (x + 1 / x ^ 2) ^ 3 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ht : 0 ≤ 1 / x ^ 2 := by positivity
  have hcancel : x ^ 2 * (1 / x ^ 2) = 1 := by field_simp
  have hcross : 0 ≤ 3 * x * (1 / x ^ 2) ^ 2 + (1 / x ^ 2) ^ 3 := by positivity
  nlinarith

/-- Bài 2.4.4: với n≥2, aₙ³≥3n+2. -/
theorem inverse_square_recurrence_cube_bound (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = u n + 1 / (u n) ^ 2) :
    ∀ n : ℕ, 2 ≤ n → 3 * (n : ℝ) + 2 ≤ (u n) ^ 3 := by
  have hpos := inverse_square_recurrence_positive u hfirst hnext
  have htwo : u 2 = 2 := by
    calc u 2 = u 1 + 1 / (u 1) ^ 2 := hnext 1 le_rfl
         _ = 2 := by rw [hfirst]; norm_num

  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [htwo]
  | succ n hn ih =>
    have hn1 : 1 ≤ n := by omega
    have hg := inverse_square_cube_gain (u n) (by linarith [hpos n hn1])
    rw [← hnext n hn1] at hg
    push_cast
    linarith

/-- Bài 2.4.4: dãy không bị chặn và a₉₀₀₀>30. -/
theorem inverse_square_recurrence_unbounded_and_large (u : ℕ → ℝ) (hfirst : u 1 = 1)
    (hnext : ∀ n : ℕ, 1 ≤ n → u (n + 1) = u n + 1 / (u n) ^ 2) :
    ¬ Section04.SequenceBounded u ∧ 30 < u 9000 := by
  have hpos := inverse_square_recurrence_positive u hfirst hnext
  have hcube := inverse_square_recurrence_cube_bound u hfirst hnext
  constructor
  · rintro ⟨⟨M, hM⟩, _⟩
    have hM1 : 1 ≤ M := by simpa [hfirst] using hM 1 le_rfl
    obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 3 + 2)
    have hn2 : 2 ≤ n := by
      have h : 0 ≤ M ^ 3 := by positivity
      have h2 : (2 : ℝ) < n := by linarith
      exact_mod_cast h2.le
    have hu := pow_le_pow_left₀ (by linarith [hpos n (by omega)]) (hM n (by omega)) 3
    have hl := hcube n hn2
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  · have h := hcube 9000 (by norm_num)
    by_contra hle
    have hle' : u 9000 ≤ 30 := le_of_not_gt hle
    have hupper := pow_le_pow_left₀ (by linarith [hpos 9000 (by norm_num)]) hle' 3
    norm_num at h hupper
    linarith

/-- Bài 2.4.6(b): sin n có một dãy con hội tụ. -/
theorem sine_has_convergent_sequenceSubsequence :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence (fun n : ℕ ↦ Real.sin n) v ∧
      ∃ a : ℝ, Section03.ConvergesTo v a := by
  obtain ⟨a, _, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n : ℕ ↦ Real.sin n)
    (fun n ↦ ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
  refine ⟨fun n ↦ Real.sin (φ n), ⟨φ, ?_, hφ.strictMonoOn _, fun _ _ ↦ rfl⟩,
    a, Section03.convergesTo_iff_tendsto.mpr hlim⟩
  intro n hn
  exact le_trans hn (hφ.id_le n)


theorem nat_add_one_le_two_pow (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    push_cast
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith

/-- Bài 2.4.7(a): (−2)ⁿ không hội tụ về số thực hữu hạn. -/
theorem negative_two_pow_divergent : Section03.IsDivergent (fun n : ℕ ↦ (-2 : ℝ) ^ n) := by
  apply Section04.unbounded_divergent
  intro hb
  obtain ⟨M, hMpos, hM⟩ := (Section04.sequenceBounded_iff_abs _).mp hb
  obtain ⟨n, hn⟩ := exists_nat_gt (max M 1)
  have hn1 : 1 ≤ n := by
    have h := lt_of_le_of_lt (le_max_right M 1) hn
    exact_mod_cast h.le
  have hbound := hM n hn1
  have hgrow := nat_add_one_le_two_pow n
  have hgt := lt_of_le_of_lt (le_max_left M 1) hn
  simp only [abs_pow, show |(-2 : ℝ)| = 2 by norm_num] at hbound
  linarith



/-- Bài 2.4.11(d): căn bậc n của tổng các lũy thừa của các số dương tiến về số lớn nhất. -/
theorem finite_power_sum_tendsto_max {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (hpos : ∀ i ∈ s, 0 < f i) (j : ι) (hj : j ∈ s)
    (hmax : ∀ i ∈ s, f i ≤ f j) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ s, (f i) ^ n) ^ (1 / (n : ℝ))) atTop (𝓝 (f j)) := by
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hlim : Tendsto (fun n : ℕ ↦ (s.card : ℝ) ^ (1 / (n : ℝ)) * f j)
      atTop (𝓝 (f j)) := by
    simpa using (Section04.constant_nth_root_tendsto_one (s.card : ℝ) hcard).mul_const (f j)
  apply Section04.squeeze_positive_terms (fun _ ↦ f j) _ _ (f j) tendsto_const_nhds hlim
  · intro n hn
    have hn0 : n ≠ 0 := by omega
    have hl : (f j) ^ n ≤ ∑ i ∈ s, (f i) ^ n :=
      Finset.single_le_sum (fun i hi ↦ pow_nonneg (hpos i hi).le _) hj
    simpa [one_div, Real.pow_rpow_inv_natCast (hpos j hj).le hn0] using
      Real.rpow_le_rpow (pow_nonneg (hpos j hj).le n) hl (by positivity : 0 ≤ (1 / (n : ℝ)))
  · intro n hn
    have hn0 : n ≠ 0 := by omega
    have hu : (∑ i ∈ s, (f i) ^ n) ≤ (s.card : ℝ) * (f j) ^ n := by
      calc (∑ i ∈ s, (f i) ^ n) ≤ ∑ _i ∈ s, (f j) ^ n :=
        Finset.sum_le_sum (fun i hi ↦ pow_le_pow_left₀ (hpos i hi).le (hmax i hi) n)
           _ = (s.card : ℝ) * (f j) ^ n := by simp [nsmul_eq_mul]
    have hsum : 0 ≤ ∑ i ∈ s, (f i) ^ n :=
      Finset.sum_nonneg (fun i hi ↦ pow_nonneg (hpos i hi).le _)
    have h := Real.rpow_le_rpow hsum hu (by positivity : 0 ≤ (1 / (n : ℝ)))
    simpa [Real.mul_rpow hcard.le (pow_nonneg (hpos j hj).le n), one_div,
      Real.pow_rpow_inv_natCast (hpos j hj).le hn0] using h

/-- Giá trị giới hạn trong bài 2.4.11(d) là phần tử lớn nhất trong f₁,…,fₖ. -/
theorem positive_power_sum_has_maximum_limit {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (hpos : ∀ i ∈ s, 0 < f i) :
    ∃ j ∈ s, (∀ i ∈ s, f i ≤ f j) ∧
      Tendsto (fun n : ℕ ↦ (∑ i ∈ s, (f i) ^ n) ^ (1 / (n : ℝ))) atTop (𝓝 (f j)) := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image s f hs
  exact ⟨j, hj, hmax, finite_power_sum_tendsto_max s hs f hpos j hj hmax⟩

/-- Bài 2.4.9(e): căn bậc n của 2ⁿ+3ⁿ tiến về 3. -/
theorem two_three_power_sum_root_tendsto_three :
    Tendsto (fun n : ℕ ↦ ((2 : ℝ) ^ n + (3 : ℝ) ^ n) ^ (1 / (n : ℝ))) atTop (𝓝 3) := by
  classical
  have hs : ({(2 : ℝ), 3} : Finset ℝ).Nonempty := by simp
  have hpos : ∀ i ∈ ({(2 : ℝ), 3} : Finset ℝ), 0 < id i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num
  have hmax : ∀ i ∈ ({(2 : ℝ), 3} : Finset ℝ), id i ≤ id 3 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num
  have h := finite_power_sum_tendsto_max ({(2 : ℝ), 3} : Finset ℝ) hs id hpos
    3 (by simp) hmax
  simpa using h




theorem sine_step_recurrence (x : ℝ) :
    Real.sin (x + 2) = 2 * Real.cos 1 * Real.sin (x + 1) - Real.sin x := by
  have heq : x + 2 = (x + 1) + 1 := by ring
  rw [heq]
  simp only [Real.sin_add, Real.cos_add]
  linear_combination (-Real.sin x) * (Real.sin_sq_add_cos_sq 1)

/-- Bài 2.4.7(b): sin n phân kì. -/
theorem sine_nat_divergent : Section03.IsDivergent (fun n : ℕ ↦ Real.sin n) := by
  rintro ⟨a, ha⟩
  have hlim := Section03.convergesTo_iff_tendsto.mp ha
  have hshift : ∀ k : ℕ, Tendsto (fun n : ℕ ↦ Real.sin (n + k : ℕ)) atTop (𝓝 a) := by
    intro k
    exact hlim.comp (tendsto_add_atTop_nat k)
  have hrec : Tendsto (fun n : ℕ ↦ Real.sin (n + 2 : ℕ)) atTop
      (𝓝 (2 * Real.cos 1 * a - a)) := by
    convert ((hshift 1).const_mul (2 * Real.cos 1)).sub hlim using 1
    ext n
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using sine_step_recurrence (n : ℝ)
  have heq : a = 2 * Real.cos 1 * a - a := tendsto_nhds_unique (hshift 2) hrec
  have hs : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi (by norm_num)
    (by linarith [Real.two_le_pi])
  have hc : Real.cos 1 < 1 := by
    by_contra h
    have he : Real.cos 1 = 1 := le_antisymm (Real.cos_le_one 1) (le_of_not_gt h)
    have htrig := Real.sin_sq_add_cos_sq 1
    rw [he] at htrig
    nlinarith
  have ha0 : a = 0 := by
    have hm : a * (Real.cos 1 - 1) = 0 := by nlinarith [heq]
    exact (mul_eq_zero.mp hm).resolve_right (by linarith)
  subst a
  have hcos : Tendsto (fun n : ℕ ↦ Real.cos n) atTop (𝓝 0) := by
    have h := ((hshift 1).sub (hlim.mul_const (Real.cos 1))).div_const (Real.sin 1)
    simp only [zero_mul, zero_sub, neg_zero, zero_div] at h
    convert h using 1
    ext n
    push_cast
    rw [Real.sin_add]
    field_simp
    ring
  have hzero : Tendsto (fun n : ℕ ↦ (Real.sin n) ^ 2 + (Real.cos n) ^ 2) atTop (𝓝 0) := by
    simpa using (hlim.pow 2).add (hcos.pow 2)
  have hone : Tendsto (fun n : ℕ ↦ (Real.sin n) ^ 2 + (Real.cos n) ^ 2) atTop (𝓝 1) := by
    simpa only [Real.sin_sq_add_cos_sq] using (tendsto_const_nhds (x := (1 : ℝ)))
  have hbad : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at hbad

/-- Cận cho các tổng ở bài 2.4.9(f), 2.4.11(c), với c≥0. -/
theorem sqrt_sum_bounds (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / √((n : ℝ) ^ 2 + c * n) ≤
      (∑ k ∈ Finset.range n, 1 / √((n : ℝ) ^ 2 + c * ((k : ℝ) + 1))) ∧
    (∑ k ∈ Finset.range n, 1 / √((n : ℝ) ^ 2 + c * ((k : ℝ) + 1))) ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbase : ∀ k : ℕ, (n : ℝ) ≤ √((n : ℝ) ^ 2 + c * ((k : ℝ) + 1)) := by
    intro k
    apply Real.le_sqrt_of_sq_le
    have hnon : 0 ≤ c * ((k : ℝ) + 1) := by positivity
    linarith
  constructor
  · calc (n : ℝ) / √((n : ℝ) ^ 2 + c * n) =
          ∑ _k ∈ Finset.range n, 1 / √((n : ℝ) ^ 2 + c * n) := by
          simp [nsmul_eq_mul, div_eq_mul_inv]
         _ ≤ ∑ k ∈ Finset.range n, 1 / √((n : ℝ) ^ 2 + c * ((k : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : (k : ℝ) + 1 ≤ n := by
            exact_mod_cast (by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp hk))
          apply one_div_le_one_div_of_le (lt_of_lt_of_le hnpos (hbase k))
          apply Real.sqrt_le_sqrt
          have h := mul_le_mul_of_nonneg_left hk' hc
          linarith
  · calc (∑ k ∈ Finset.range n, 1 / √((n : ℝ) ^ 2 + c * ((k : ℝ) + 1))) ≤
          ∑ _k ∈ Finset.range n, 1 / (n : ℝ) :=
            Finset.sum_le_sum (fun k _ ↦ one_div_le_one_div_of_le hnpos (hbase k))
         _ = 1 := by simp [nsmul_eq_mul, div_eq_mul_inv, hnpos.ne']


theorem nat_div_sqrt_square_linear (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / √((n : ℝ) ^ 2 + c * n) = 1 / √(1 + c / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hinside : (n : ℝ) ^ 2 + c * n = (n : ℝ) ^ 2 * (1 + c / n) := by
    field_simp
  rw [hinside, Real.sqrt_mul (sq_nonneg (n : ℝ)), Real.sqrt_sq hnpos.le]
  have hroot : 0 < √(1 + c / (n : ℝ)) := Real.sqrt_pos_of_pos (by positivity)
  field_simp


theorem sqrt_sum_tendsto_one (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      1 / √((n : ℝ) ^ 2 + c * ((k : ℝ) + 1))) atTop (𝓝 1) := by
  have hinside : Tendsto (fun n : ℕ ↦ 1 + c / n) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero, one_div, div_eq_mul_inv, one_mul] using
      (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_one_div_atTop_nhds_zero_nat.const_mul c)
  have hroot : Tendsto (fun n : ℕ ↦ √(1 + c / n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using Real.continuous_sqrt.continuousAt.tendsto.comp hinside
  have hl : Tendsto (fun n : ℕ ↦ 1 / √(1 + c / n)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).div hroot (by norm_num : (1 : ℝ) ≠ 0) using 1
    · ext n
      rfl
    · norm_num
  apply Section04.squeeze_positive_terms _ _ (fun _ ↦ 1) 1 hl tendsto_const_nhds
  · intro n hn
    rw [← nat_div_sqrt_square_linear c hc n hn]
    exact (sqrt_sum_bounds c hc n hn).1
  · intro n hn
    exact (sqrt_sum_bounds c hc n hn).2

/-- Bài 2.4.9(f), n số hạng từ k=1 đến n. -/
theorem sqrt_square_plus_index_sum_tendsto_one :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      1 / √((n : ℝ) ^ 2 + ((k : ℝ) + 1))) atTop (𝓝 1) := by
  simpa using sqrt_sum_tendsto_one 1 (by norm_num)

/-- Bài 2.4.11(c): giới hạn tổng có hệ số 2. -/
theorem sqrt_square_plus_twice_index_sum_tendsto_one :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      1 / √((n : ℝ) ^ 2 + 2 * ((k : ℝ) + 1))) atTop (𝓝 1) :=
  sqrt_sum_tendsto_one 2 (by norm_num)



/-- Bài 2.4.11(b): các cận chính xác 1/2 và 1/2+1/(2n). -/
theorem linear_fraction_sum_bounds (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ≤ (∑ k ∈ Finset.range n, ((k : ℝ) + 1) / ((n : ℝ) ^ 2 + ((k : ℝ) + 1))) ∧
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) / ((n : ℝ) ^ 2 + ((k : ℝ) + 1))) ≤
      1 / 2 + (1 / 2) * (1 / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  constructor
  · calc (1 / 2 : ℝ) = (∑ k ∈ Finset.range n, ((k : ℝ) + 1)) / ((n : ℝ) ^ 2 + n) := by
          rw [Section01Exercises.sum_first_naturals]
          have hden : (n : ℝ) ^ 2 + n ≠ 0 := by positivity
          field_simp
         _ = ∑ k ∈ Finset.range n, ((k : ℝ) + 1) / ((n : ℝ) ^ 2 + n) := Finset.sum_div _ _ _
         _ ≤ ∑ k ∈ Finset.range n, ((k : ℝ) + 1) / ((n : ℝ) ^ 2 + ((k : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : (k : ℝ) + 1 ≤ n := by
            exact_mod_cast (by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp hk))
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          linarith
  · calc (∑ k ∈ Finset.range n, ((k : ℝ) + 1) / ((n : ℝ) ^ 2 + ((k : ℝ) + 1))) ≤
          ∑ k ∈ Finset.range n, ((k : ℝ) + 1) / ((n : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro k hk
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          have hk0 : (0 : ℝ) ≤ k := by positivity
          linarith
         _ = (∑ k ∈ Finset.range n, ((k : ℝ) + 1)) / ((n : ℝ) ^ 2) := (Finset.sum_div _ _ _).symm
         _ = 1 / 2 + (1 / 2) * (1 / (n : ℝ)) := by
          rw [Section01Exercises.sum_first_naturals]
          field_simp

/-- Bài 2.4.11(b): giới hạn bằng 1/2. -/
theorem linear_fraction_sum_tendsto_half :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ((k : ℝ) + 1) / ((n : ℝ) ^ 2 + ((k : ℝ) + 1))) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hu : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) + (1 / 2) * (1 / n)) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add
      (tendsto_one_div_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ))
  apply Section04.squeeze_positive_terms (fun _ ↦ 1 / 2) _ _ (1 / 2) tendsto_const_nhds hu
  · intro n hn; exact (linear_fraction_sum_bounds n hn).1
  · intro n hn; exact (linear_fraction_sum_bounds n hn).2



/-- Bài 2.4.9(b): dãy n!/nⁿ tại n≥1. -/
noncomputable def factorialRatio (n : ℕ) : ℝ := (n.factorial : ℝ) / (n : ℝ) ^ n


theorem factorialRatio_step (n : ℕ) (hn : 1 ≤ n) :
    factorialRatio (n + 1) = factorialRatio n / (1 + 1 / (n : ℝ)) ^ n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnext : (n : ℝ) + 1 ≠ 0 := by positivity
  have heq : (1 + 1 / (n : ℝ)) ^ n = ((n : ℝ) + 1) ^ n / (n : ℝ) ^ n := by
    rw [show 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / n by field_simp, div_pow]
  simp only [factorialRatio, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [heq, pow_succ]
  field_simp


theorem factorialRatio_step_le_half (n : ℕ) (hn : 1 ≤ n) :
    factorialRatio (n + 1) ≤ factorialRatio n / 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
  have hbern := one_add_mul_le_pow (by linarith : -(2 : ℝ) ≤ 1 / (n : ℝ)) n
  have hcancel : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
  rw [hcancel] at hbern
  have htwo : (2 : ℝ) ≤ (1 + 1 / (n : ℝ)) ^ n := by linarith
  rw [factorialRatio_step n hn]
  exact div_le_div_of_nonneg_left (by unfold factorialRatio; positivity) (by norm_num) htwo

/-- Bài 2.4.9(b): cận hình học của n!/nⁿ. -/
theorem factorialRatio_geometric_bound (n : ℕ) : factorialRatio (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num [factorialRatio]
  | succ n ih =>
    calc factorialRatio (n + 1 + 1) ≤ factorialRatio (n + 1) / 2 :=
          factorialRatio_step_le_half (n + 1) (by omega)
         _ ≤ (1 / 2 : ℝ) ^ n / 2 := div_le_div_of_nonneg_right ih (by norm_num)
         _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

/-- Bài 2.4.9(b): n!/nⁿ→0. -/
theorem factorial_div_self_pow_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (n.factorial : ℝ) / (n : ℝ) ^ n) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ factorialRatio (n + 1)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ ?_) factorialRatio_geometric_bound
      (Section04.geometric_tendsto_zero (1 / 2 : ℝ) (by norm_num))
    unfold factorialRatio
    positivity
  exact (tendsto_add_atTop_iff_nat 1).mp hshift



/-- Bài 2.4.11(d): căn bậc n của tổng λ₁ⁿ+…+λₖⁿ hội tụ về phần tử lớn nhất. -/
theorem indexed_positive_power_sum_has_maximum_limit (k : ℕ) (hk : 1 ≤ k)
    (f : ℕ → ℝ) (hf : ∀ i : ℕ, 1 ≤ i → i ≤ k → 0 < f i) :
    ∃ j ∈ Finset.Icc 1 k, (∀ i ∈ Finset.Icc 1 k, f i ≤ f j) ∧
      Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.Icc 1 k, (f i) ^ n) ^ (1 / (n : ℝ)))
        atTop (𝓝 (f j)) := by
  have hs : (Finset.Icc 1 k).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩
  exact positive_power_sum_has_maximum_limit _ hs f
    (fun i hi ↦ hf i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)

end calculus.Chapter02.Section04Supplement
