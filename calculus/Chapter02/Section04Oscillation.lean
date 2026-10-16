import calculus.Chapter02.Section05

/-!
# Bài 2.4.7(c–f): dãy phân kì

Nguồn: `source/Ch2_dayso.tex`, dòng 1550–1553.
-/

namespace calculus.Chapter02.Section04Oscillation
open Filter
open scoped Topology


theorem four_mul_add_tendsto (b : ℕ) : Tendsto (fun n : ℕ ↦ 4 * n + b) atTop atTop :=
  (show StrictMono (fun n : ℕ ↦ 4 * n + b) from
    strictMono_nat_of_lt_succ (fun n ↦ by omega)).tendsto_atTop


theorem divergent_of_two_subsequence_limits {u : ℕ → ℝ} {φ ψ : ℕ → ℕ} {a b : ℝ}
    (hφ : Tendsto φ atTop atTop) (hψ : Tendsto ψ atTop atTop)
    (ha : Tendsto (fun n ↦ u (φ n)) atTop (𝓝 a))
    (hb : Tendsto (fun n ↦ u (ψ n)) atTop (𝓝 b)) (hab : a ≠ b) :
    Section03.IsDivergent u := by
  rintro ⟨c, hc⟩
  have ht := Section03.convergesTo_iff_tendsto.mp hc
  exact hab ((tendsto_nhds_unique ha (ht.comp hφ)).trans (tendsto_nhds_unique (ht.comp hψ) hb))


theorem nat_div_succ_tendsto_one :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
  have hr : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    by simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hr
  apply ht.congr'
  exact Eventually.of_forall fun n ↦ by field_simp; ring

/-- Dấu ở các chỉ số 4n của bài 2.4.7(c). -/
theorem triangular_sign_four_mul (n : ℕ) :
    (-1 : ℝ) ^ ((4 * n) * (4 * n + 1) / 2) = 1 := by
  have he : (4 * n) * (4 * n + 1) / 2 = 2 * (n * (4 * n + 1)) := by
    rw [show 4 * n * (4 * n + 1) = (n * (4 * n + 1)) * 2 * 2 by ring]
    simp
    ring
  rw [he]
  simp [pow_mul]

/-- Dấu ở các chỉ số 4n+1 của cùng bài. -/
theorem triangular_sign_four_mul_add_one (n : ℕ) :
    (-1 : ℝ) ^ ((4 * n + 1) * (4 * n + 1 + 1) / 2) = -1 := by
  have he : (4 * n + 1) * (4 * n + 1 + 1) / 2 = 2 * (n * (4 * n + 3)) + 1 := by
    rw [show (4 * n + 1) * (4 * n + 1 + 1) =
      (2 * (n * (4 * n + 3)) + 1) * 2 by ring]
    simp
  rw [he]
  simp [pow_add, pow_mul]

/-- Bài 2.4.7(c): hai giới hạn dãy con là 1 và −1. -/
theorem triangular_signed_ratio_divergent : Section03.IsDivergent
    (fun n : ℕ ↦ (n : ℝ) / (n + 1) * (-1 : ℝ) ^ (n * (n + 1) / 2)) := by
  have h0 : Tendsto (fun n : ℕ ↦ (4 * n : ℕ) / ((4 * n : ℕ) + 1) *
      (-1 : ℝ) ^ ((4 * n) * (4 * n + 1) / 2)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Nat.add_zero, triangular_sign_four_mul, mul_one] using
      nat_div_succ_tendsto_one.comp (four_mul_add_tendsto 0)
  have h1 : Tendsto (fun n : ℕ ↦ ((4 * n + 1 : ℕ) : ℝ) / ((4 * n + 1 : ℕ) + 1) *
      (-1 : ℝ) ^ ((4 * n + 1) * (4 * n + 1 + 1) / 2)) atTop (𝓝 (-1)) := by
    simpa only [Function.comp_def, triangular_sign_four_mul_add_one, mul_neg_one] using
      (nat_div_succ_tendsto_one.comp (four_mul_add_tendsto 1)).neg
  exact divergent_of_two_subsequence_limits (four_mul_add_tendsto 0)
    (four_mul_add_tendsto 1) h0 h1 (by norm_num)

/-- Bài 2.4.7(d): rút gọn góc khi n>0. -/
theorem sine_angle_normalize (n : ℕ) (hn : 1 ≤ n) :
    Real.pi * ((n : ℝ) ^ 2 + 1) / (2 * n) = Real.pi * n / 2 + Real.pi / (2 * n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp [hn0]


theorem half_reciprocal_angle_tendsto :
    Tendsto (fun n : ℕ ↦ Real.pi / (2 * n)) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.pi / 2)

/-- Bài 2.4.7(d): góc tại chỉ số 4n+b theo chu kì 2π. -/
theorem sine_angle_subsequence_tendsto (b : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.sin (Real.pi * (((4 * n + b : ℕ) : ℝ) ^ 2 + 1) /
      (2 * (4 * n + b : ℕ)))) atTop (𝓝 (Real.sin (Real.pi * b / 2))) := by
  have herr := half_reciprocal_angle_tendsto.comp (four_mul_add_tendsto b)
  have ht : Tendsto (fun n : ℕ ↦ Real.sin (Real.pi * b / 2 +
      Real.pi / (2 * (4 * n + b : ℕ)))) atTop (𝓝 (Real.sin (Real.pi * b / 2))) := by
    simpa only [Function.comp_def, add_zero] using Real.continuous_sin.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := Real.pi * b / 2)).add herr)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : 1 ≤ 4 * n + b := by omega
  rw [sine_angle_normalize _ hpos]
  have he : Real.pi * ((4 * n + b : ℕ) : ℝ) / 2 + Real.pi / (2 * (4 * n + b : ℕ)) =
      (Real.pi * b / 2 + Real.pi / (2 * (4 * n + b : ℕ))) + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [he, Real.sin_add_nat_mul_two_pi]

/-- Bài 2.4.7(d): hai giới hạn dãy con là ±1/2. -/
theorem radical_times_sine_divergent : Section03.IsDivergent (fun n : ℕ ↦
    (√((n : ℝ) ^ 2 + n) - n) * Real.sin (Real.pi * ((n : ℝ) ^ 2 + 1) / (2 * n))) := by
  have ha := Section03.convergesTo_iff_tendsto.mp Section05.sqrt_quadratic_increment_converges
  have h0 : Tendsto (fun n : ℕ ↦
      (√(((4 * n + 1 : ℕ) : ℝ) ^ 2 + (4 * n + 1 : ℕ)) - (4 * n + 1 : ℕ)) *
        Real.sin (Real.pi * (((4 * n + 1 : ℕ) : ℝ) ^ 2 + 1) / (2 * (4 * n + 1 : ℕ))))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (ha.comp (four_mul_add_tendsto 1)).mul (sine_angle_subsequence_tendsto 1)
  have hs : Real.sin (Real.pi * (3 : ℝ) / 2) = -1 := by
    rw [show Real.pi * (3 : ℝ) / 2 = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two]
  have h1 : Tendsto (fun n : ℕ ↦
      (√(((4 * n + 3 : ℕ) : ℝ) ^ 2 + (4 * n + 3 : ℕ)) - (4 * n + 3 : ℕ)) *
        Real.sin (Real.pi * (((4 * n + 3 : ℕ) : ℝ) ^ 2 + 1) / (2 * (4 * n + 3 : ℕ))))
      atTop (𝓝 (-1 / 2 : ℝ)) := by
    simpa [hs, neg_div] using (ha.comp (four_mul_add_tendsto 3)).mul (sine_angle_subsequence_tendsto 3)
  exact divergent_of_two_subsequence_limits (four_mul_add_tendsto 1)
    (four_mul_add_tendsto 3) h0 h1 (by norm_num)

/-- Bài 2.4.7(f): phân tích góc bằng phép chia đa thức, với n≥1. -/
theorem cubic_cosine_angle_normalize (n : ℕ) (hn : 1 ≤ n) :
    Real.pi * (n : ℝ) ^ 3 / (2 * (n : ℝ) ^ 2 + n) =
      Real.pi * n / 2 - Real.pi / 4 + Real.pi / (4 * (2 * n + 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hd : 2 * (n : ℝ) ^ 2 + n ≠ 0 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  field_simp
  ring

/-- Bài 2.4.7(f): sai số sau phép chia đa thức tiến về 0. -/
theorem cubic_cosine_error_tendsto :
    Tendsto (fun n : ℕ ↦ Real.pi / (4 * (2 * (n : ℝ) + 1))) atTop (𝓝 0) := by
  have hidx : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop :=
    (show StrictMono (fun n : ℕ ↦ 2 * n + 1) from
      strictMono_nat_of_lt_succ (fun n ↦ by omega)).tendsto_atTop
  have hr : Tendsto (fun n : ℕ ↦ 1 / (2 * (n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hidx
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hr.const_mul (Real.pi / 4)

/-- Trên các chỉ số 4n+b, bài(f) có giới hạn cos(πb/2−π/4). -/
theorem cubic_cosine_subsequence_tendsto (b : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.cos (Real.pi * ((4 * n + b : ℕ) : ℝ) ^ 3 /
      (2 * ((4 * n + b : ℕ) : ℝ) ^ 2 + (4 * n + b : ℕ))))
      atTop (𝓝 (Real.cos (Real.pi * b / 2 - Real.pi / 4))) := by
  have herr := cubic_cosine_error_tendsto.comp (four_mul_add_tendsto b)
  have ht : Tendsto (fun n : ℕ ↦ Real.cos (Real.pi * b / 2 - Real.pi / 4 +
      Real.pi / (4 * (2 * ((4 * n + b : ℕ) : ℝ) + 1))))
      atTop (𝓝 (Real.cos (Real.pi * b / 2 - Real.pi / 4))) := by
    simpa only [Function.comp_def, add_zero] using Real.continuous_cos.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := Real.pi * b / 2 - Real.pi / 4)).add herr)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [cubic_cosine_angle_normalize _ (by omega)]
  have he : Real.pi * ((4 * n + b : ℕ) : ℝ) / 2 - Real.pi / 4 +
      Real.pi / (4 * (2 * ((4 * n + b : ℕ) : ℝ) + 1)) =
      (Real.pi * b / 2 - Real.pi / 4 + Real.pi / (4 * (2 * ((4 * n + b : ℕ) : ℝ) + 1))) +
        (n : ℝ) * (2 * Real.pi) := by push_cast; ring
  rw [he, Real.cos_add_nat_mul_two_pi]

/-- Bài 2.4.7(f): hai giá trị cos(π/4) và −cos(π/4) khác nhau. -/
theorem cubic_cosine_divergent : Section03.IsDivergent (fun n : ℕ ↦
    Real.cos (Real.pi * (n : ℝ) ^ 3 / (2 * (n : ℝ) ^ 2 + n))) := by
  have h0 := cubic_cosine_subsequence_tendsto 0
  have h2 := cubic_cosine_subsequence_tendsto 2
  apply divergent_of_two_subsequence_limits (four_mul_add_tendsto 0)
    (four_mul_add_tendsto 2) h0 h2
  have hp : 0 < Real.cos (Real.pi / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  simp only [Nat.cast_zero, Nat.cast_ofNat, mul_zero, zero_div, zero_sub, Real.cos_neg]
  rw [show Real.pi * (2 : ℝ) / 2 - Real.pi / 4 = -Real.pi / 4 + Real.pi by ring,
    Real.cos_add_pi]
  simp only [neg_div, Real.cos_neg]
  linarith

/-- Bài 2.4.7(e): phần lệch khỏi π(n+1) tiến về 0. -/
theorem quadratic_cosine_error_tendsto :
    Tendsto (fun n : ℕ ↦ Real.pi * (√((n : ℝ) ^ 2 + 2 * n + 2) - n - 1))
      atTop (𝓝 0) := by
  have h := (Section03.convergesTo_iff_tendsto.mp
    (Section05.sqrt_increment_converges 2 2 (by norm_num) (by norm_num))).sub_const 1
  simpa using h.const_mul Real.pi

/-- Bài 2.4.7(e): đẳng thức cho góc chứa căn. -/
theorem quadratic_cosine_normalize (n : ℕ) :
    Real.cos (Real.pi * √((n : ℝ) ^ 2 + 2 * n + 2)) =
      (-1 : ℝ) ^ (n + 1) * Real.cos (Real.pi * (√((n : ℝ) ^ 2 + 2 * n + 2) - n - 1)) := by
  have he : Real.pi * √((n : ℝ) ^ 2 + 2 * n + 2) =
      Real.pi * (√((n : ℝ) ^ 2 + 2 * n + 2) - n - 1) + (n + 1 : ℕ) * Real.pi := by
    push_cast
    ring
  rw [he, Real.cos_add_nat_mul_pi]

/-- Bài 2.4.7(e): chỉ số 4n có giới hạn −1, chỉ số 4n+1 có giới hạn 1. -/
theorem quadratic_cosine_divergent : Section03.IsDivergent (fun n : ℕ ↦
    Real.cos (Real.pi * √((n : ℝ) ^ 2 + 2 * n + 2))) := by
  have hc : Tendsto (fun n : ℕ ↦
      Real.cos (Real.pi * (√((n : ℝ) ^ 2 + 2 * n + 2) - n - 1))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.comp quadratic_cosine_error_tendsto
  have h0 : Tendsto (fun n : ℕ ↦
      Real.cos (Real.pi * √(((4 * n : ℕ) : ℝ) ^ 2 + 2 * (4 * n : ℕ) + 2)))
      atTop (𝓝 (-1)) := by
    have he (n : ℕ) : (-1 : ℝ) ^ (4 * n + 1) = -1 := by norm_num [pow_add, pow_mul]
    simpa only [Function.comp_def, Nat.add_zero, quadratic_cosine_normalize,
      he, neg_one_mul] using (hc.comp (four_mul_add_tendsto 0)).neg
  have h1 : Tendsto (fun n : ℕ ↦
      Real.cos (Real.pi * √(((4 * n + 1 : ℕ) : ℝ) ^ 2 + 2 * (4 * n + 1 : ℕ) + 2)))
      atTop (𝓝 1) := by
    have he (n : ℕ) : (-1 : ℝ) ^ (4 * n + 1 + 1) = 1 := by
      rw [show 4 * n + 1 + 1 = 4 * n + 2 by omega]
      norm_num [pow_add, pow_mul]
    simpa only [Function.comp_def, quadratic_cosine_normalize, he, one_mul] using
      hc.comp (four_mul_add_tendsto 1)
  exact divergent_of_two_subsequence_limits (four_mul_add_tendsto 0)
    (four_mul_add_tendsto 1) h0 h1 (by norm_num)

end calculus.Chapter02.Section04Oscillation
