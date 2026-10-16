import Mathlib.Analysis.Real.OfDigits
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.Prime

/-!
# Biểu diễn thập phân và tính hữu tỉ

Nguồn: `source/Ch1_taphop.tex`, dòng 773–777 và 852.
Chỉ số 0 là chữ số đầu sau dấu phẩy.
-/

set_option autoImplicit false

namespace calculus.Chapter01.Section04Decimals

open scoped BigOperators

/-- Chữ số thập phân có giá trị trong 0,…,9. -/
abbrev DecimalDigit := Fin 10

/-- Biểu diễn hữu hạn: từ một vị trí nào đó, mọi chữ số đều bằng 0. -/
def TerminatingDigits (d : ℕ → DecimalDigit) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → d n = 0

/-- Các chữ số lặp theo chu kì p>0 từ một vị trí trở đi. -/
def EventuallyPeriodicDigits (d : ℕ → DecimalDigit) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → d (n + p) = d n

/-- Giá trị thập phân bằng phần nguyên cộng với chuỗi `Real.ofDigits`. -/
noncomputable def decimalValue (z : ℤ) (d : ℕ → DecimalDigit) : ℝ :=
  (z : ℝ) + Real.ofDigits d

/-- Các chữ số do `Real.digits` chọn cho phần lẻ x−⌊x⌋∈[0,1). -/
noncomputable def canonicalDigits (x : ℝ) : ℕ → DecimalDigit :=
  Real.digits (Int.fract x) 10

/-- `Real.ofDigits` cho phép hai biểu diễn của cùng một số: 0,(9)=1. -/
theorem repeating_nines_value : Real.ofDigits (fun _ : ℕ ↦ (9 : DecimalDigit)) = 1 := by
  simpa using Real.ofDigits_const_last_eq_one' (b := 10) (by norm_num)

/-- Phần nguyên và các chữ số thập phân khôi phục x, kể cả khi x<0. -/
theorem canonical_decimalValue (x : ℝ) : decimalValue ⌊x⌋ (canonicalDigits x) = x := by
  unfold decimalValue canonicalDigits
  rw [Real.ofDigits_digits (by norm_num) ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩]
  exact Int.floor_add_fract x

/-- Giá trị của N chữ số đầu là một tổng hữu tỉ hữu hạn. -/
def decimalPrefix (d : ℕ → DecimalDigit) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, (d k : ℕ) / (10 : ℚ) ^ (k + 1)


theorem decimalPrefix_cast (d : ℕ → DecimalDigit) (N : ℕ) :
    (decimalPrefix d N : ℝ) = ∑ k ∈ Finset.range N, Real.ofDigitsTerm d k := by
  simp [decimalPrefix, Real.ofDigitsTerm, div_eq_mul_inv]


theorem TerminatingDigits.eventuallyPeriodic {d : ℕ → DecimalDigit} (h : TerminatingDigits d) :
    EventuallyPeriodicDigits d := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, 1, by omega, ?_⟩
  intro n hn
  rw [hN (n + 1) (by omega), hN n hn]


theorem periodic_ofDigits_is_rational (d : ℕ → DecimalDigit) (p : ℕ) (hp : 0 < p)
    (hper : ∀ n : ℕ, d (n + p) = d n) : ∃ q : ℚ, (q : ℝ) = Real.ofDigits d := by
  have hstream : (fun n : ℕ ↦ d (n + p)) = d := funext hper
  have hsplit := Real.ofDigits_eq_sum_add_ofDigits d p
  rw [hstream, ← decimalPrefix_cast] at hsplit
  have hpow : (1 : ℝ) < 10 ^ p := one_lt_pow₀ (by norm_num) (by omega : p ≠ 0)
  have hinv : ((10 : ℝ) ^ p)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpow
  have hden : (1 : ℝ) - ((10 : ℝ) ^ p)⁻¹ ≠ 0 := by linarith
  refine ⟨decimalPrefix d p / (1 - ((10 : ℚ) ^ p)⁻¹), ?_⟩
  push_cast
  apply (div_eq_iff hden).mpr
  nlinarith [hsplit]


theorem eventuallyPeriodic_ofDigits_is_rational (d : ℕ → DecimalDigit)
    (hd : EventuallyPeriodicDigits d) : ∃ q : ℚ, (q : ℝ) = Real.ofDigits d := by
  obtain ⟨N, p, hp, hper⟩ := hd
  let tail : ℕ → DecimalDigit := fun n ↦ d (n + N)
  have ht : ∀ n : ℕ, tail (n + p) = tail n := by
    intro n
    have hh := hper (n + N) (by omega)
    simpa [tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
  obtain ⟨q, hq⟩ := periodic_ofDigits_is_rational tail p hp ht
  refine ⟨decimalPrefix d N + ((10 : ℚ) ^ N)⁻¹ * q, ?_⟩
  have hsplit := Real.ofDigits_eq_sum_add_ofDigits d N
  rw [← decimalPrefix_cast] at hsplit
  change Real.ofDigits d = (decimalPrefix d N : ℝ) +
    ((10 : ℝ) ^ N)⁻¹ * Real.ofDigits tail at hsplit
  push_cast
  rw [hq]
  exact hsplit.symm


theorem eventuallyPeriodic_decimalValue_is_rational (z : ℤ) (d : ℕ → DecimalDigit)
    (hd : EventuallyPeriodicDigits d) : ∃ q : ℚ, (q : ℝ) = decimalValue z d := by
  obtain ⟨q, hq⟩ := eventuallyPeriodic_ofDigits_is_rational d hd
  refine ⟨(z : ℚ) + q, ?_⟩
  simp [decimalValue, hq]

/-- Số vô tỉ không có biểu diễn thập phân tuần hoàn từ một vị trí trở đi, kể cả biểu diễn kết thúc bằng các chữ số 9. -/
theorem digits_not_eventually_periodic_of_irrational_decimalValue (z : ℤ) (d : ℕ → DecimalDigit)
    (hx : Irrational (decimalValue z d)) : ¬ EventuallyPeriodicDigits d := by
  intro hd
  exact hx (eventuallyPeriodic_decimalValue_is_rational z d hd)

/-- Biểu diễn thập phân của số vô tỉ không kết thúc và không tuần hoàn từ bất cứ vị trí nào. -/
theorem canonicalDigits_not_eventually_periodic_of_irrational (x : ℝ) (hx : Irrational x) :
    ¬ EventuallyPeriodicDigits (canonicalDigits x) ∧ ¬ TerminatingDigits (canonicalDigits x) := by
  have hi : Irrational (decimalValue ⌊x⌋ (canonicalDigits x)) := by
    rwa [canonical_decimalValue]
  have hp := digits_not_eventually_periodic_of_irrational_decimalValue ⌊x⌋ (canonicalDigits x) hi
  exact ⟨hp, fun ht ↦ hp ht.eventuallyPeriodic⟩

/-- Dòng 852: với n:ℕ dương không phải số chính phương, √n là số vô tỉ. -/
theorem nonsquare_sqrt_irrational (n : ℕ) (_hpos : 1 ≤ n) (hn : ¬ IsSquare n) : Irrational (Real.sqrt n) :=
  irrational_sqrt_natCast_iff.mpr hn

/-- Các căn bậc hai của 2, 3, 5, 6, 7, 8 đều vô tỉ. -/
theorem printed_square_roots_irrational :
    Irrational (Real.sqrt 2) ∧ Irrational (Real.sqrt 3) ∧ Irrational (Real.sqrt 5) ∧
      Irrational (Real.sqrt 6) ∧ Irrational (Real.sqrt 7) ∧ Irrational (Real.sqrt 8) := by
  repeat' constructor
  all_goals norm_num

/-- Dòng 852: π là số vô tỉ. -/
theorem pi_irrational : Irrational Real.pi := irrational_pi


theorem natFloor_natCast_div_natCast_real (a b : ℕ) : ⌊((a : ℝ) / (b : ℝ))⌋₊ = a / b := by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_floor_eq_floor (by positivity)]
  have hcast : (((a : ℚ) / (b : ℚ) : ℚ) : ℝ) = (a : ℝ) / (b : ℝ) := by
    push_cast
    rfl
  rw [← hcast, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  norm_cast


theorem digits_fraction_val (a b n : ℕ) (hb : 0 < b) :
    ((Real.digits ((a : ℝ) / (b : ℝ)) 10 n : DecimalDigit) : ℕ) =
      ((a * 10 ^ n) % b) * 10 / b := by
  change ⌊(a : ℝ) / (b : ℝ) * 10 ^ (n + 1)⌋₊ % 10 = _
  have hreal : (a : ℝ) / (b : ℝ) * 10 ^ (n + 1) =
      ((a * 10 ^ (n + 1) : ℕ) : ℝ) / (b : ℝ) := by push_cast; ring
  rw [hreal, natFloor_natCast_div_natCast_real]
  have hdecomp : a * 10 ^ (n + 1) =
      ((a * 10 ^ n) % b) * 10 + (((a * 10 ^ n) / b) * 10) * b := by
    calc
      a * 10 ^ (n + 1) = (a * 10 ^ n) * 10 := by rw [pow_succ]; ring
      _ = (((a * 10 ^ n) / b) * b + (a * 10 ^ n) % b) * 10 := by
        rw [Nat.mul_comm ((a * 10 ^ n) / b) b, Nat.div_add_mod]
      _ = ((a * 10 ^ n) % b) * 10 + (((a * 10 ^ n) / b) * 10) * b := by ring
  rw [hdecomp, Nat.add_mul_div_right _ _ hb]
  have hsmall : ((a * 10 ^ n) % b) * 10 / b < 10 := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    nlinarith [Nat.mod_lt (a * 10 ^ n) hb]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hsmall]


theorem decimal_remainders_eventually_periodic (a b : ℕ) (hb : 0 < b) :
    ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n →
      (a * 10 ^ (n + p)) % b = (a * 10 ^ n) % b := by
  let r : ℕ → Fin b := fun n ↦ ⟨(a * 10 ^ n) % b, Nat.mod_lt _ hb⟩
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite r
  have hex : ∃ i j : ℕ, i < j ∧ r i = r j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  obtain ⟨i, j, hlt, hijr⟩ := hex
  have hr : (a * 10 ^ i) % b = (a * 10 ^ j) % b := congrArg Fin.val hijr
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have hn1 : n = i + (n - i) := by omega
  have hn2 : n + (j - i) = j + (n - i) := by omega
  calc
    (a * 10 ^ (n + (j - i))) % b = (a * 10 ^ j * 10 ^ (n - i)) % b := by
      rw [hn2, pow_add]
      simp [Nat.mul_assoc]
    _ = ((a * 10 ^ j) % b * (10 ^ (n - i) % b)) % b := Nat.mul_mod _ _ _
    _ = ((a * 10 ^ i) % b * (10 ^ (n - i) % b)) % b := by rw [hr]
    _ = (a * 10 ^ i * 10 ^ (n - i)) % b := (Nat.mul_mod _ _ _).symm
    _ = (a * 10 ^ n) % b := by rw [hn1, pow_add]; simp [Nat.mul_assoc]


theorem digits_fraction_eventually_periodic (a b : ℕ) (hb : 0 < b) :
    EventuallyPeriodicDigits (Real.digits ((a : ℝ) / (b : ℝ)) 10) := by
  obtain ⟨N, p, hp, hper⟩ := decimal_remainders_eventually_periodic a b hb
  refine ⟨N, p, hp, ?_⟩
  intro n hn
  apply Fin.ext
  rw [digits_fraction_val a b (n + p) hb, digits_fraction_val a b n hb, hper n hn]


theorem rational_fract_eq_remainder (q : ℚ) :
    Int.fract (q : ℝ) = (((q.num % (q.den : ℤ)).toNat : ℕ) : ℝ) / (q.den : ℝ) := by
  rw [Rat.cast_def, Int.fract_div_intCast_eq_div_intCast_mod]
  have hnonneg : 0 ≤ q.num % (q.den : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast q.den_nz)
  have hnat : (((q.num % (q.den : ℤ)).toNat : ℕ) : ℤ) = q.num % (q.den : ℤ) :=
    Int.natCast_toNat_eq_self.mpr hnonneg
  exact congrArg (fun r : ℝ ↦ r / (q.den : ℝ)) (by exact_mod_cast hnat.symm)

/-- Dòng 773: các chữ số được chọn của mọi số hữu tỉ tuần hoàn từ một vị trí nào đó. -/
theorem canonicalDigits_eventually_periodic_of_rational (q : ℚ) : EventuallyPeriodicDigits (canonicalDigits (q : ℝ)) := by
  unfold canonicalDigits
  rw [rational_fract_eq_remainder]
  exact digits_fraction_eventually_periodic _ _ q.den_pos

/-- Dòng 773: số hữu tỉ có biểu diễn thập phân hữu hạn hoặc tuần hoàn từ một vị trí trở đi. -/
theorem rational_decimal_classification (q : ℚ) :
    TerminatingDigits (canonicalDigits (q : ℝ)) ∨
      (EventuallyPeriodicDigits (canonicalDigits (q : ℝ)) ∧
        ¬ TerminatingDigits (canonicalDigits (q : ℝ))) := by
  classical
  by_cases ht : TerminatingDigits (canonicalDigits (q : ℝ))
  · exact Or.inl ht
  · exact Or.inr ⟨canonicalDigits_eventually_periodic_of_rational q, ht⟩

/-- x hữu tỉ khi và chỉ khi các chữ số được chọn tuần hoàn từ một vị trí nào đó. -/
theorem rational_iff_canonicalDigits_eventually_periodic (x : ℝ) :
    (∃ q : ℚ, (q : ℝ) = x) ↔ EventuallyPeriodicDigits (canonicalDigits x) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact canonicalDigits_eventually_periodic_of_rational q
  · intro hp
    obtain ⟨q, hq⟩ := eventuallyPeriodic_decimalValue_is_rational ⌊x⌋ (canonicalDigits x) hp
    exact ⟨q, by simpa only [canonical_decimalValue] using hq⟩

/-- Dòng 852: x vô tỉ khi và chỉ khi các chữ số được chọn không tuần hoàn
từ bất kỳ vị trí nào; khi đó biểu diễn cũng không kết thúc. -/
theorem irrational_iff_canonicalDigits_not_eventually_periodic (x : ℝ) :
    Irrational x ↔ ¬ EventuallyPeriodicDigits (canonicalDigits x) := by
  simpa only [Irrational, Set.mem_range] using not_congr (rational_iff_canonicalDigits_eventually_periodic x)

/-- Tiêu chuẩn số học: mẫu số chia một lũy thừa của 10 khi và chỉ khi
mọi ước nguyên tố của nó đều là 2 hoặc 5. -/
theorem denominator_dvd_power_ten_iff (b : ℕ) (hb : 0 < b) :
    (∃ N : ℕ, b ∣ 10 ^ N) ↔ ∀ p : ℕ, Nat.Prime p → p ∣ b → p = 2 ∨ p = 5 := by
  rw [Nat.exists_dvd_pow_iff (by omega : b ≠ 0) (by norm_num : 10 ≠ 0)]
  constructor
  · intro hs p hp hpb
    have hmem : p ∈ b.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpb, by omega⟩
    have hp10 : p ∣ 2 * 5 := by simpa using Nat.dvd_of_mem_primeFactors (hs hmem)
    rcases hp.dvd_mul.mp hp10 with h2 | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).mp h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h5)
  · intro hs p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpb := Nat.dvd_of_mem_primeFactors hp
    rcases hs p hprime hpb with rfl | rfl <;> norm_num [Nat.mem_primeFactors]

/-- Biểu diễn được chọn kết thúc khi và chỉ khi nhân x với một lũy thừa của 10
cho một số nguyên. -/
theorem canonical_terminating_iff_scaled_integer (x : ℝ) :
    TerminatingDigits (canonicalDigits x) ↔ ∃ N : ℕ, ∃ z : ℤ, (10 : ℝ) ^ N * x = (z : ℝ) := by
  constructor
  · rintro ⟨N, hN⟩
    have htail : (fun i : ℕ ↦ canonicalDigits x (i + N)) = (fun _ : ℕ ↦ (0 : DecimalDigit)) := by
      funext i
      exact hN (i + N) (by omega)
    have hsplit := Real.ofDigits_eq_sum_add_ofDigits (canonicalDigits x) N
    rw [htail] at hsplit
    have hzero : Real.ofDigits (fun _ : ℕ ↦ (0 : DecimalDigit)) = 0 := by
      simp [Real.ofDigits, Real.ofDigitsTerm]
    rw [hzero, mul_zero, add_zero] at hsplit
    have hxfrac : Int.fract x = ∑ k ∈ Finset.range N, Real.ofDigitsTerm (canonicalDigits x) k := by
      rw [← Real.ofDigits_digits (b := 10) (by norm_num) ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩]
      exact hsplit
    have hscaled : (10 : ℝ) ^ N * Int.fract x = (⌊(10 : ℝ) ^ N * Int.fract x⌋₊ : ℝ) := by
      calc
        (10 : ℝ) ^ N * Int.fract x = (10 : ℝ) ^ N *
            (∑ k ∈ Finset.range N, Real.ofDigitsTerm (canonicalDigits x) k) :=
          congrArg (fun y : ℝ ↦ (10 : ℝ) ^ N * y) hxfrac
        _ = (⌊(10 : ℝ) ^ N * Int.fract x⌋₊ : ℝ) :=
          Real.ofDigits_digits_sum_eq ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩ N
    refine ⟨N, (⌊(10 : ℝ) ^ N * Int.fract x⌋₊ : ℤ) + ⌊x⌋ * (10 : ℤ) ^ N, ?_⟩
    have hx := Int.floor_add_fract x
    calc
      (10 : ℝ) ^ N * x = (10 : ℝ) ^ N * ((⌊x⌋ : ℝ) + Int.fract x) := by rw [hx]
      _ = (⌊(10 : ℝ) ^ N * Int.fract x⌋₊ : ℝ) + (⌊x⌋ : ℝ) * (10 : ℝ) ^ N := by
        calc
          (10 : ℝ) ^ N * ((⌊x⌋ : ℝ) + Int.fract x) =
              (⌊x⌋ : ℝ) * (10 : ℝ) ^ N + (10 : ℝ) ^ N * Int.fract x := by ring
          _ = (⌊x⌋ : ℝ) * (10 : ℝ) ^ N + (⌊(10 : ℝ) ^ N * Int.fract x⌋₊ : ℝ) :=
            congrArg (fun r : ℝ ↦ (⌊x⌋ : ℝ) * (10 : ℝ) ^ N + r) hscaled
          _ = (⌊(10 : ℝ) ^ N * Int.fract x⌋₊ : ℝ) + (⌊x⌋ : ℝ) * (10 : ℝ) ^ N := by ring
      _ = (((⌊(10 : ℝ) ^ N * Int.fract x⌋₊ : ℤ) + ⌊x⌋ * (10 : ℤ) ^ N : ℤ) : ℝ) := by
        push_cast
        rfl
  · rintro ⟨N, z, hz⟩
    let w : ℤ := z - ⌊x⌋ * (10 : ℤ) ^ N
    have hw : Int.fract x * (10 : ℝ) ^ N = (w : ℝ) := by
      dsimp [w]
      push_cast
      rw [Int.fract, sub_mul, mul_comm x _, hz]
    have hwr : (0 : ℝ) ≤ (w : ℝ) := by rw [← hw]; positivity
    have hwpos : (0 : ℤ) ≤ w := by exact_mod_cast hwr
    have hwcast : (w.toNat : ℝ) = (w : ℝ) := by
      exact_mod_cast Int.natCast_toNat_eq_self.mpr hwpos
    refine ⟨N, ?_⟩
    intro n hn
    apply Fin.ext
    change ⌊Int.fract x * (10 : ℝ) ^ (n + 1)⌋₊ % 10 = 0
    have hexp : n + 1 = N + (n - N) + 1 := by omega
    have hnum : Int.fract x * (10 : ℝ) ^ (n + 1) =
        ((w.toNat * 10 ^ (n - N) * 10 : ℕ) : ℝ) := by
      calc
        Int.fract x * (10 : ℝ) ^ (n + 1) =
            (Int.fract x * (10 : ℝ) ^ N) * (10 : ℝ) ^ (n - N) * 10 := by
          rw [hexp, pow_succ, pow_add]
          ring
        _ = (w : ℝ) * (10 : ℝ) ^ (n - N) * 10 := by rw [hw]
        _ = ((w.toNat * 10 ^ (n - N) * 10 : ℕ) : ℝ) := by
          push_cast
          rw [hwcast]
    rw [hnum, Nat.floor_natCast]
    simp


theorem reduced_fraction_scaled_integer_iff (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hc : Nat.Coprime a.natAbs b) :
    (∃ N : ℕ, ∃ z : ℤ, (10 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)) = (z : ℝ)) ↔
      ∃ N : ℕ, b ∣ 10 ^ N := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  constructor
  · rintro ⟨N, z, hz⟩
    have hre : (10 : ℝ) ^ N * (a : ℝ) = (z : ℝ) * (b : ℝ) := by
      apply (div_eq_iff hb0).mp
      simpa only [mul_div_assoc] using hz
    have hint : ((10 ^ N : ℕ) : ℤ) * a = z * (b : ℤ) := by exact_mod_cast hre
    have hdiv : (b : ℤ) ∣ ((10 ^ N : ℕ) : ℤ) * a := ⟨z, by rw [hint]; ring⟩
    have hnat : b ∣ 10 ^ N * a.natAbs := by
      have hh := Int.natCast_dvd.mp hdiv
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hh
    exact ⟨N, hc.symm.dvd_of_dvd_mul_right hnat⟩
  · rintro ⟨N, k, hk⟩
    refine ⟨N, a * (k : ℤ), ?_⟩
    have hre : (10 : ℝ) ^ N = (b : ℝ) * (k : ℝ) := by exact_mod_cast hk
    rw [hre]
    push_cast
    field_simp

/-- Định lí 1.4.15: biểu diễn thập phân hữu hạn khi và chỉ khi mẫu số tối giản
không có ước nguyên tố nào ngoài 2,5. -/
theorem reduced_fraction_terminating_iff (a : ℤ) (b : ℕ) (hb : 1 < b)
    (hc : Nat.Coprime a.natAbs b) :
    TerminatingDigits (canonicalDigits ((a : ℝ) / (b : ℝ))) ↔
      ∀ p : ℕ, Nat.Prime p → p ∣ b → p = 2 ∨ p = 5 := by
  rw [canonical_terminating_iff_scaled_integer,
    reduced_fraction_scaled_integer_iff a b (by omega) hc,
    denominator_dvd_power_ten_iff b (by omega)]

/-- Định lí 1.4.15: nếu mẫu số tối giản có ước nguyên tố khác 2,5
thì biểu diễn thập phân vô hạn và tuần hoàn từ một vị trí nào đó. -/
theorem reduced_fraction_nonterminating_eventually_periodic (a : ℤ) (b : ℕ) (hb : 1 < b)
    (hc : Nat.Coprime a.natAbs b)
    (hother : ∃ p : ℕ, Nat.Prime p ∧ p ∣ b ∧ p ≠ 2 ∧ p ≠ 5) :
    EventuallyPeriodicDigits (canonicalDigits ((a : ℝ) / (b : ℝ))) ∧
      ¬ TerminatingDigits (canonicalDigits ((a : ℝ) / (b : ℝ))) := by
  constructor
  · have hcast : ((((a : ℚ) / (b : ℚ)) : ℚ) : ℝ) = (a : ℝ) / (b : ℝ) := by
      push_cast
      rfl
    rw [← hcast]
    exact canonicalDigits_eventually_periodic_of_rational _
  · intro ht
    have hpall := (reduced_fraction_terminating_iff a b hb hc).mp ht
    obtain ⟨p, hp, hpb, hp2, hp5⟩ := hother
    exact (hpall p hp hpb).elim hp2 hp5

end calculus.Chapter01.Section04Decimals
