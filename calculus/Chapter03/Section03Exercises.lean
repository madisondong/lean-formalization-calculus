import calculus.Chapter03.Section03Supplement
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! §3.3 — bài tập về giới hạn trên miền tự nhiên của từng biểu thức. -/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02Infinite calculus.Chapter03.Section03
open calculus.Chapter03.Section03Supplement calculus.Chapter02.Section03


theorem hasDerivAt_domainLimit_slope {f : ℝ → ℝ} {a f' : ℝ} (hf : HasDerivAt f f' a) :
    DomainLimit univ (slope f a) a f' := by
  apply (domainLimit_iff_tendsto (univ_accumulation a)).mpr
  simpa only [← compl_eq_univ_sdiff] using hf.tendsto_slope


theorem derivative_quotient_domain_accumulation {g : ℝ → ℝ} {a g' : ℝ}
    (hg : HasDerivAt g g' a) (hg0 : g a = 0) (hg' : g' ≠ 0) :
    AccumulationPointOf {x : ℝ | g x ≠ 0} a := by
  have ha := quotient_domain_accumulation (hasDerivAt_domainLimit_slope hg) hg'
  intro δ hδ
  obtain ⟨x, hx, hn, hl, hr⟩ := ha δ hδ
  refine ⟨x, ?_, hn, hl, hr⟩
  intro hx0
  have hs := hx.2
  rw [slope_def_field, hx0, hg0, sub_self, zero_div] at hs
  exact hs rfl


theorem ratio_of_derivative_slopes {D : Set ℝ} {f g : ℝ → ℝ} {a f' g' : ℝ}
    (ha : AccumulationPointOf D a) (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a)
    (hf0 : f a = 0) (hg0 : g a = 0) (hg' : g' ≠ 0) :
    DomainLimit D (fun x ↦ f x / g x) a (f' / g') := by
  have hs := domainLimit_div_extension (hasDerivAt_domainLimit_slope hf)
    (hasDerivAt_domainLimit_slope hg) hg'
  have hr := domainLimit_restrict hs ha (fun _ _ ↦ mem_univ _)
  apply (domainLimit_congr_punctured ?_).mp hr
  intro x _ hx
  rw [slope_def_field, slope_def_field, hf0, hg0, sub_zero, sub_zero]
  exact div_div_div_cancel_right₀ (sub_ne_zero.mpr hx) (f x) (g x)

theorem accumulationPointOf_mono {D E : Set ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) (hDE : D ⊆ E) : AccumulationPointOf E a := by
  intro δ hδ
  obtain ⟨x, hx, hn, hl, hr⟩ := ha δ hδ
  exact ⟨x, hDE hx, hn, hl, hr⟩


theorem accumulationPointOf_inter_Ioi {D : Set ℝ} {a c : ℝ}
    (ha : AccumulationPointOf D a) (hc : c < a) : AccumulationPointOf (D ∩ Ioi c) a := by
  intro δ hδ
  have hp : 0 < (a - c) / 2 := by linarith
  obtain ⟨x, hx, hn, hl, hr⟩ := ha (min δ ((a - c) / 2)) (lt_min hδ hp)
  refine ⟨x, ⟨hx, ?_⟩, hn, ?_, ?_⟩
  · change c < x
    linarith [min_le_right δ ((a - c) / 2)]
  · linarith [min_le_left δ ((a - c) / 2)]
  · linarith [min_le_left δ ((a - c) / 2)]

/-- Bài tập 3.3.1(a): miền mẫu khác 0. -/
theorem polynomial_ratio_at_two :
    DomainLimit (univ \ {(3 : ℝ)}) (fun x ↦ (3 * x ^ 2 - 2 * x + 5) / (x - 3)) 2 (-13) := by
  have hf : ContinuousAt (fun x : ℝ ↦ (3 * x ^ 2 - 2 * x + 5) / (x - 3)) 2 :=
    (((continuous_const.mul (continuous_id.pow 2)).sub (continuous_const.mul continuous_id)).add
      continuous_const).continuousAt.div (continuous_id.sub continuous_const).continuousAt (by norm_num)
  convert! domainLimit_of_continuousAt (punctured_univ_accumulation 2 3) hf using 1
  norm_num

/-- Bài tập 3.3.1(b): miền xác định loại cả ±3. -/
theorem quadratic_ratio_at_negative_three :
    DomainLimit {x : ℝ | x ^ 2 - 9 ≠ 0} (fun x ↦ (x ^ 2 + 4 * x + 3) / (x ^ 2 - 9)) (-3) (1 / 3) := by
  have hf : HasDerivAt (fun x : ℝ ↦ x ^ 2 + 4 * x + 3) (-2) (-3) := by
    convert! (((hasDerivAt_id (-3 : ℝ)).pow 2).add ((hasDerivAt_id (-3 : ℝ)).const_mul 4)).add_const 3 using 1
    norm_num [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply]
  have hg : HasDerivAt (fun x : ℝ ↦ x ^ 2 - 9) (-6) (-3) := by
    convert! ((hasDerivAt_id (-3 : ℝ)).pow 2).sub_const 9 using 1
    norm_num [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply]
  convert! ratio_of_derivative_slopes (derivative_quotient_domain_accumulation hg (by norm_num) (by norm_num))
    hf hg (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

/-- Bài tập 3.3.1(c): miền loại ba nghiệm thực của x⁵−x. -/
theorem polynomial_zero_ratio :
    DomainLimit {x : ℝ | x ^ 5 - x ≠ 0} (fun x ↦ (x ^ 4 - 2 * x ^ 3 + 3 * x) / (x ^ 5 - x)) 0 (-3) := by
  have hf : HasDerivAt (fun x : ℝ ↦ x ^ 4 - 2 * x ^ 3 + 3 * x) 3 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).pow 4).sub (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul 2)).add
      ((hasDerivAt_id (0 : ℝ)).const_mul 3) using 1
    norm_num [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply]
  have hg : HasDerivAt (fun x : ℝ ↦ x ^ 5 - x) (-1) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).pow 5).sub (hasDerivAt_id (0 : ℝ)) using 1
    norm_num [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply]
  convert! ratio_of_derivative_slopes (derivative_quotient_domain_accumulation hg (by norm_num) (by norm_num))
    hf hg (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

/-- Bài tập 3.3.1(d): giới hạn với m,n≥1. -/
theorem power_ratio_at_one (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    DomainLimit {x : ℝ | x ^ n - 1 ≠ 0} (fun x ↦ (x ^ m - 1) / (x ^ n - 1)) 1 ((m : ℝ) / n) := by
  have hf : HasDerivAt (fun x : ℝ ↦ x ^ m - 1) (m : ℝ) 1 := by
    simpa only [Pi.pow_apply, id_eq, one_pow, mul_one] using ((hasDerivAt_id (1 : ℝ)).pow m).sub_const 1
  have hg : HasDerivAt (fun x : ℝ ↦ x ^ n - 1) (n : ℝ) 1 := by
    simpa only [Pi.pow_apply, id_eq, one_pow, mul_one] using ((hasDerivAt_id (1 : ℝ)).pow n).sub_const 1
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have _ := hm
  exact ratio_of_derivative_slopes (derivative_quotient_domain_accumulation hg (by simp) hne)
    hf hg (by simp) (by simp) hne

/-- Bài tập 3.3.2(a): giới hạn trên miền căn xác định và mẫu khác 0. -/
theorem sqrt_ratio_at_one :
    DomainLimit {x : ℝ | 0 ≤ x ∧ x ^ 2 - 1 ≠ 0} (fun x ↦ (Real.sqrt x - 1) / (x ^ 2 - 1)) 1 (1 / 4) := by
  have hf : HasDerivAt (fun x : ℝ ↦ Real.sqrt x - 1) (1 / 2) 1 := by
    simpa only [Real.sqrt_one, mul_one] using (Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0)).sub_const 1
  have hg : HasDerivAt (fun x : ℝ ↦ x ^ 2 - 1) 2 1 := by
    simpa only [Pi.pow_apply, id_eq, one_pow, mul_one, Nat.cast_ofNat] using ((hasDerivAt_id (1 : ℝ)).pow 2).sub_const 1
  have ha0 := derivative_quotient_domain_accumulation hg (by norm_num) (by norm_num)
  have ha := accumulationPointOf_mono (accumulationPointOf_inter_Ioi ha0 (by norm_num : (0 : ℝ) < 1))
    (show {x : ℝ | x ^ 2 - 1 ≠ 0} ∩ Ioi 0 ⊆ {x : ℝ | 0 ≤ x ∧ x ^ 2 - 1 ≠ 0} from fun _ hx ↦ ⟨hx.2.le, hx.1⟩)
  convert! ratio_of_derivative_slopes ha hf hg (by simp) (by norm_num) (by norm_num) using 1
  norm_num


theorem signedCubeRoot_hasDerivAt_eight : HasDerivAt signedCubeRoot (1 / 12) 8 := by
  have hp : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    simpa only [signedCubeRoot, if_pos (by norm_num : (0 : ℝ) ≤ 8)] using signedCubeRoot_at_eight
  have hh := Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl (by norm_num : (8 : ℝ) ≠ 0))
  have hd : (1 / 3 : ℝ) * (8 : ℝ) ^ ((1 / 3 : ℝ) - 1) = 1 / 12 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 8), Real.rpow_one, hp]
    norm_num
  rw [hd] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 8)] with x hx
  exact if_pos hx.le

/-- Bài tập 3.3.2(b): giới hạn của thương chứa căn bậc ba thực. -/
theorem cubic_root_ratio_at_two :
    DomainLimit (univ \ {(2 : ℝ)}) (fun x ↦ (signedCubeRoot (10 - x) - 2) / (x - 2)) 2 (-1 / 12) := by
  have hlin : HasDerivAt (fun x : ℝ ↦ 10 - x) (-1) 2 := (hasDerivAt_id (2 : ℝ)).const_sub 10
  have hf : HasDerivAt (fun x : ℝ ↦ signedCubeRoot (10 - x) - 2) (-1 / 12) 2 := by
    have hc : HasDerivAt signedCubeRoot (1 / 12) (10 - (2 : ℝ)) := by
      convert! signedCubeRoot_hasDerivAt_eight using 1
      norm_num
    have hh := (hc.comp 2 hlin).sub_const 2
    convert! hh using 1
    norm_num [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply]
  have hg : HasDerivAt (fun x : ℝ ↦ x - 2) 1 2 := (hasDerivAt_id (2 : ℝ)).sub_const 2
  convert! ratio_of_derivative_slopes (univ_diff_accumulation 2) hf hg
    (by norm_num [signedCubeRoot_at_eight]) (by norm_num) (by norm_num) using 1
  norm_num


noncomputable def realNthRoot (n : ℕ) (x : ℝ) : ℝ :=
  if Odd n ∧ x < 0 then -((-x) ^ ((n : ℝ)⁻¹)) else x ^ ((n : ℝ)⁻¹)

def nthRootDomain (n : ℕ) : Set ℝ := {x : ℝ | Odd n ∨ 0 ≤ x}

theorem realNthRoot_pow {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ nthRootDomain n) :
    realNthRoot n x ^ n = x := by
  unfold realNthRoot
  split_ifs with hh
  · have hp : 0 ≤ -x := by linarith [hh.2]
    rw [hh.1.neg_pow, Real.rpow_inv_natCast_pow hp (show n ≠ 0 by omega), neg_neg]
  · have hp : 0 ≤ x := by
      rcases hx with hodd | hpos
      · by_contra hneg
        exact hh ⟨hodd, lt_of_not_ge hneg⟩
      · exact hpos
    exact Real.rpow_inv_natCast_pow hp (show n ≠ 0 by omega)

theorem realNthRoot_one (n : ℕ) : realNthRoot n 1 = 1 := by simp [realNthRoot]

theorem realNthRoot_hasDerivAt_one {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (realNthRoot n) ((n : ℝ)⁻¹) 1 := by
  have hh := Real.hasDerivAt_rpow_const (p := (n : ℝ)⁻¹) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  simp only [Real.one_rpow, mul_one] at hh
  have _ := hn
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
  exact if_neg (by rintro ⟨_, hneg⟩; exact not_lt_of_ge hx.le hneg)


def rootRatioDomain (m n : ℕ) : Set ℝ :=
  {x : ℝ | x ∈ nthRootDomain n ∧ x ∈ nthRootDomain m ∧ realNthRoot m x - 1 ≠ 0}

/-- Bài tập 3.3.2(c): giới hạn thương căn với m,n≥2. -/
theorem nth_root_ratio_at_one (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    DomainLimit (rootRatioDomain m n) (fun x ↦ (realNthRoot n x - 1) / (realNthRoot m x - 1))
      1 ((m : ℝ) / n) := by
  have hf := (realNthRoot_hasDerivAt_one (show 1 ≤ n by omega)).sub_const 1
  have hg := (realNthRoot_hasDerivAt_one (show 1 ≤ m by omega)).sub_const 1
  have hmne : (m : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (show m ≠ 0 by omega))
  have ha0 := derivative_quotient_domain_accumulation hg (by simp [realNthRoot_one]) hmne
  have ha : AccumulationPointOf (rootRatioDomain m n) 1 :=
    accumulationPointOf_mono (accumulationPointOf_inter_Ioi ha0 (by norm_num : (0 : ℝ) < 1))
      (fun _ hx ↦ ⟨Or.inr hx.2.le, Or.inr hx.2.le, hx.1⟩)
  convert! ratio_of_derivative_slopes ha hf hg (by simp [realNthRoot_one])
    (by simp [realNthRoot_one]) hmne using 1
  simp only [inv_div_inv]


theorem signedCubeRoot_hasDerivAt_one : HasDerivAt signedCubeRoot (1 / 3) 1 := by
  have hh := Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  simp only [Real.one_rpow, mul_one] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
  exact if_pos hx.le

/-- Bài tập 3.3.2(d): giới hạn trên miền căn xác định, loại x=1. -/
theorem sqrt_cube_root_difference_ratio :
    DomainLimit {x : ℝ | 0 ≤ x ∧ x ≠ 1} (fun x ↦ (Real.sqrt x - signedCubeRoot x) / (x - 1)) 1 (1 / 6) := by
  have hf : HasDerivAt (fun x : ℝ ↦ Real.sqrt x - signedCubeRoot x) (1 / 6) 1 := by
    convert! (Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0)).sub signedCubeRoot_hasDerivAt_one using 1
    norm_num [id_eq, Pi.pow_apply, Pi.add_apply, Pi.sub_apply]
  have hg : HasDerivAt (fun x : ℝ ↦ x - 1) 1 1 := (hasDerivAt_id (1 : ℝ)).sub_const 1
  have ha : AccumulationPointOf {x : ℝ | 0 ≤ x ∧ x ≠ 1} 1 := by
    intro δ hδ
    exact ⟨1 + δ / 2, ⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩
  convert! ratio_of_derivative_slopes ha hf hg (by norm_num [signedCubeRoot])
    (by norm_num) (by norm_num) using 1
  norm_num



/-- Bài tập 3.3.6: điều kiện Lipschitz suy ra giới hạn hữu hạn tồn tại. -/
theorem lipschitz_punctured_hasDomainLimit {D : Set ℝ} {f : ℝ → ℝ} {a M : ℝ}
    (ha : AccumulationPointOf D a) (hM : 0 ≤ M)
    (hf : ∀ x ∈ D \ {a}, ∀ y ∈ D \ {a}, |f x - f y| ≤ M * |x - y|) :
    HasDomainLimit D f a := by
  apply (hasDomainLimit_iff_cauchy ha).mpr
  intro ε hε
  have hp : 0 < M + 1 := by linarith
  let δ := ε / (2 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, fun x hx y hy hxn hxd hyn hyd ↦ ?_⟩
  have hxne : x ≠ a := sub_ne_zero.mp (abs_pos.mp hxn)
  have hyne : y ≠ a := sub_ne_zero.mp (abs_pos.mp hyn)
  have hbound := hf x ⟨hx, by simpa only [mem_singleton_iff] using hxne⟩
    y ⟨hy, by simpa only [mem_singleton_iff] using hyne⟩
  have htri := abs_sub_le x a y
  rw [abs_sub_comm a y] at htri
  have hs : |x - a| + |y - a| < 2 * δ := by linarith
  calc
    |f x - f y| ≤ M * |x - y| := hbound
    _ ≤ M * (|x - a| + |y - a|) := mul_le_mul_of_nonneg_left htri hM
    _ ≤ (M + 1) * (|x - a| + |y - a|) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ < (M + 1) * (2 * δ) := mul_lt_mul_of_pos_left hs hp
    _ = ε := by dsimp [δ]; field_simp

/-- Bài tập 3.3.7: hai giới hạn một phía của hàm phần nguyên tại −3. -/
theorem floor_negative_three_one_sided_limits :
    DomainLeftLimit univ (fun x ↦ (⌊x⌋ : ℝ)) (-3) (-4) ∧
    DomainRightLimit univ (fun x ↦ (⌊x⌋ : ℝ)) (-3) (-3) := by
  constructor
  · refine ⟨leftAccumulation_univ (-3), fun ε hε ↦ ⟨1 / 2, by norm_num, ?_⟩⟩
    intro x _ hx hx3
    have hfloor : ⌊x⌋ = (-4 : ℤ) := Int.floor_eq_iff.mpr
      ⟨by norm_num; linarith, by norm_num; linarith⟩
    simpa only [hfloor, Int.cast_neg, Int.cast_ofNat, sub_self, abs_zero] using hε
  · refine ⟨rightAccumulation_univ (-3), fun ε hε ↦ ⟨1 / 2, by norm_num, ?_⟩⟩
    intro x _ hx3 hx
    have hfloor : ⌊x⌋ = (-3 : ℤ) := Int.floor_eq_iff.mpr
      ⟨by norm_num; linarith, by norm_num; linarith⟩
    simpa only [hfloor, Int.cast_neg, Int.cast_ofNat, sub_self, abs_zero] using hε

/-- Bài tập 3.3.8(a): giới hạn phải bằng +∞ trên miền xác định. -/
theorem linear_ratio_right_top_at_one :
    DomainRightTopLimit (univ \ {(1 : ℝ)}) (fun x ↦ (x + 1) / (x - 1)) 1 := by
  refine ⟨rightAccumulation_univ_diff 1, ?_⟩
  have hh : Tendsto (fun x : ℝ ↦ 1 / (x - 1)) (𝓝[(univ \ {1}) ∩ Ioi 1] 1) atTop := by
    simpa only [pow_one] using (reciprocal_power_right_top 1 1 (by omega)).2
  have hm := Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hh
  have ht : Tendsto (fun x : ℝ ↦ 1 + 2 * (1 / (x - 1))) (𝓝[(univ \ {1}) ∩ Ioi 1] 1) atTop :=
    tendsto_atTop_add_const_left _ 1 hm
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx1 : x ≠ 1 := by simpa only [mem_singleton_iff] using hx.1.2
  field_simp [sub_ne_zero.mpr hx1]
  ring

/-- Bài tập 3.3.8(b): biểu thức dao động với thừa số bình phương tiến đến 0 khi x→0⁺. -/
theorem absolute_square_sine_reciprocal_right_zero :
    DomainRightLimit (univ \ {(0 : ℝ)}) (fun x ↦ |x ^ 2 * Real.sin (1 / x)|) 0 0 := by
  refine ⟨rightAccumulation_univ_diff 0, fun ε hε ↦ ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩⟩
  intro x _ hx hxd
  have hx0 : 0 < x := hx
  simp only [zero_add] at hxd
  have hx1 : x < 1 := hxd.trans_le (min_le_left _ _)
  have hxε : x < ε := hxd.trans_le (min_le_right _ _)
  have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / x)) (sq_nonneg x)
  simp only [mul_one] at hs
  change abs (abs (x ^ 2 * Real.sin (1 / x)) - 0) < ε
  simp only [sub_zero, abs_abs, abs_mul, abs_pow, abs_of_pos hx0]
  nlinarith

/-- Bài tập 3.3.8(c): hai giới hạn một phía của phần thập phân khác nhau, nên không có giới hạn hữu hạn hai phía. -/
theorem fractional_part_at_one_no_domainLimit :
    ¬ HasDomainLimit univ (fun x ↦ x - (⌊x⌋ : ℝ)) 1 := by
  have hl : DomainLeftLimit univ (fun x ↦ x - (⌊x⌋ : ℝ)) 1 1 := by
    apply (domainLeftLimit_iff_tendsto (leftAccumulation_univ 1)).mpr
    have hi : Tendsto (fun x : ℝ ↦ x) (𝓝[univ ∩ Iio 1] 1) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hh := hi.sub ((domainLeftLimit_iff_tendsto (leftAccumulation_univ 1)).mp floor_one_sided_limits.1)
    simpa only [sub_zero] using hh
  have hr : DomainRightLimit univ (fun x ↦ x - (⌊x⌋ : ℝ)) 1 0 := by
    apply (domainRightLimit_iff_tendsto (rightAccumulation_univ 1)).mpr
    have hi : Tendsto (fun x : ℝ ↦ x) (𝓝[univ ∩ Ioi 1] 1) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hh := hi.sub ((domainRightLimit_iff_tendsto (rightAccumulation_univ 1)).mp floor_one_sided_limits.2)
    simpa only [sub_self] using hh
  rintro ⟨L, hL⟩
  obtain ⟨hleft, hright⟩ := (domainLimit_iff_left_right (leftAccumulation_univ 1) (rightAccumulation_univ 1)).mp hL
  have he1 := domainLeftLimit_unique hl hleft
  have he0 := domainRightLimit_unique hr hright
  linarith

/-- Bài tập 3.3.9: x sin(1/x)→0 khi x→0, với x≠0. -/
theorem linear_sine_reciprocal_limit :
    DomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ x * Real.sin (1 / x)) 0 0 := by
  refine ⟨univ_diff_accumulation 0, fun ε hε ↦ ⟨ε, hε, fun x _ _ hx ↦ ?_⟩⟩
  have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / x)) (abs_nonneg x)
  rw [mul_one] at hs
  change |x * Real.sin (1 / x) - 0| < ε
  simpa only [sub_zero, abs_mul] using hs.trans_lt (by simpa only [sub_zero] using hx)



/-- Bài tập 3.3.10: hàm từng phần phụ thuộc tham số. -/
noncomputable def parameterPiecewise (a x : ℝ) : ℝ := if 1 < x then x ^ 2 else a * x - 1

theorem parameterPiecewise_left_limit (a : ℝ) :
    DomainLeftLimit univ (parameterPiecewise a) 1 (a - 1) := by
  have hcont : ContinuousAt (fun x : ℝ ↦ a * x - 1) 1 :=
    ((continuous_const.mul continuous_id).sub continuous_const).continuousAt
  have hlim : DomainLimit univ (fun x : ℝ ↦ a * x - 1) 1 (a - 1) := by
    simpa only [mul_one] using domainLimit_of_continuousAt (univ_accumulation 1) hcont
  have hl := ((domainLimit_iff_left_right (leftAccumulation_univ 1) (rightAccumulation_univ 1)).mp hlim).1
  apply domainLeftLimit_iff_restricted.mpr
  apply (domainLimit_congr_domain ?_).mpr (domainLeftLimit_iff_restricted.mp hl)
  intro x hx
  exact if_neg (not_lt_of_ge hx.2.le)

theorem parameterPiecewise_right_limit (a : ℝ) :
    DomainRightLimit univ (parameterPiecewise a) 1 1 := by
  have hcont : ContinuousAt (fun x : ℝ ↦ x ^ 2) 1 := (continuous_id.pow 2).continuousAt
  have hlim : DomainLimit univ (fun x : ℝ ↦ x ^ 2) 1 1 := by
    simpa only [one_pow] using domainLimit_of_continuousAt (univ_accumulation 1) hcont
  have hr := ((domainLimit_iff_left_right (leftAccumulation_univ 1) (rightAccumulation_univ 1)).mp hlim).2
  apply domainRightLimit_iff_restricted.mpr
  apply (domainLimit_congr_domain ?_).mpr (domainRightLimit_iff_restricted.mp hr)
  intro x hx
  exact if_pos hx.2

/-- Bài tập 3.3.10: các tham số cho giới hạn tồn tại và giá trị giới hạn. -/
theorem parameterPiecewise_limit_iff (a L : ℝ) :
    DomainLimit univ (parameterPiecewise a) 1 L ↔ a = 2 ∧ L = 1 := by
  constructor
  · intro h
    obtain ⟨hl, hr⟩ := (domainLimit_iff_left_right (leftAccumulation_univ 1) (rightAccumulation_univ 1)).mp h
    have heL := domainLeftLimit_unique (parameterPiecewise_left_limit a) hl
    have heR := domainRightLimit_unique (parameterPiecewise_right_limit a) hr
    exact ⟨by linarith, heR.symm⟩
  · rintro ⟨rfl, rfl⟩
    apply (domainLimit_iff_left_right (leftAccumulation_univ 1) (rightAccumulation_univ 1)).mpr
    exact ⟨by convert! parameterPiecewise_left_limit 2 using 1; norm_num, parameterPiecewise_right_limit 2⟩

theorem parameterPiecewise_hasDomainLimit_iff (a : ℝ) :
    HasDomainLimit univ (parameterPiecewise a) 1 ↔ a = 2 := by
  constructor
  · rintro ⟨L, hL⟩
    exact (parameterPiecewise_limit_iff a L).mp hL |>.1
  · intro ha
    exact ⟨1, (parameterPiecewise_limit_iff a 1).mpr ⟨ha, rfl⟩⟩

/-- Bài tập 3.3.11: công thức phần thập phân sau phép tịnh tiến. -/
noncomputable def shiftedFractionalPart (x : ℝ) : ℝ := 1 + x - (⌊x⌋ : ℝ)

theorem shiftedFractionalPart_eq (x : ℝ) : shiftedFractionalPart x = 1 + Int.fract x := by
  unfold shiftedFractionalPart Int.fract
  ring

theorem shiftedFractionalPart_integer_side_limits (k : ℤ) :
    DomainLeftLimit univ shiftedFractionalPart k 2 ∧ DomainRightLimit univ shiftedFractionalPart k 1 := by
  constructor
  · apply (domainLeftLimit_iff_tendsto (leftAccumulation_univ (k : ℝ))).mpr
    have ht : Tendsto (fun x : ℝ ↦ 1 + Int.fract x) (𝓝[Iio (k : ℝ)] (k : ℝ)) (𝓝 (1 + 1)) :=
      (tendsto_fract_left' k).const_add 1
    simp only [univ_inter]
    convert! (ht.congr fun x ↦ (shiftedFractionalPart_eq x).symm) using 1
    norm_num
  · apply (domainRightLimit_iff_tendsto (rightAccumulation_univ (k : ℝ))).mpr
    have hf : Tendsto Int.fract (𝓝[Ioi (k : ℝ)] (k : ℝ)) (𝓝 0) :=
      (tendsto_fract_right' k).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have ht := hf.const_add 1
    simp only [univ_inter]
    convert! (ht.congr fun x ↦ (shiftedFractionalPart_eq x).symm) using 1
    norm_num

theorem shiftedFractionalPart_integer_no_limit (k : ℤ) :
    ¬ HasDomainLimit univ shiftedFractionalPart k := by
  rintro ⟨L, hL⟩
  obtain ⟨hl, hr⟩ := (domainLimit_iff_left_right (leftAccumulation_univ (k : ℝ)) (rightAccumulation_univ (k : ℝ))).mp hL
  have he2 := domainLeftLimit_unique (shiftedFractionalPart_integer_side_limits k).1 hl
  have he1 := domainRightLimit_unique (shiftedFractionalPart_integer_side_limits k).2 hr
  linarith

theorem shiftedFractionalPart_noninteger_limit {a : ℝ}
    (ha : a ∉ range ((↑) : ℤ → ℝ)) : DomainLimit univ shiftedFractionalPart a (shiftedFractionalPart a) := by
  have hne : a ≠ (⌊a⌋ : ℝ) := by
    intro he
    exact ha ⟨⌊a⌋, he.symm⟩
  have hc : ContinuousAt (fun x : ℝ ↦ 1 + Int.fract x) a :=
    continuous_const.continuousAt.add (continuousAt_fract hne)
  apply domainLimit_of_continuousAt (univ_accumulation a)
  exact hc.congr_of_eventuallyEq (Eventually.of_forall shiftedFractionalPart_eq)

/-- Bài tập 3.3.11: các điểm tại đó hàm có giới hạn. -/
theorem shiftedFractionalPart_hasDomainLimit_iff (a : ℝ) :
    HasDomainLimit univ shiftedFractionalPart a ↔ a ∉ range ((↑) : ℤ → ℝ) := by
  constructor
  · intro h ha
    obtain ⟨k, hk⟩ := ha
    rw [← hk] at h
    exact shiftedFractionalPart_integer_no_limit k h
  · intro ha
    exact ⟨shiftedFractionalPart a, shiftedFractionalPart_noninteger_limit ha⟩



theorem accumulationPointOf_inter_nhds {D E : Set ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) (hE : E ∈ 𝓝 a) : AccumulationPointOf (D ∩ E) a := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hE
  intro δ hδ
  obtain ⟨x, hx, hn, hl, hu⟩ := ha (min δ r) (lt_min hδ hr)
  refine ⟨x, ⟨hx, hball ?_⟩, hn, ?_, ?_⟩
  · change dist x a < r
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [min_le_right δ r]
  · linarith [min_le_left δ r]
  · linarith [min_le_left δ r]

/-- Bài tập 3.3.5(a): giới hạn của thương lượng giác. -/
theorem sine_square_div_limit :
    DomainLimit (univ \ {0}) (fun x : ℝ ↦ Real.sin x ^ 2 / x) 0 0 := by
  have hs := domainLimit_restrict (domainLimit_of_continuousAt (univ_accumulation 0)
    Real.continuous_sin.continuousAt) (univ_diff_accumulation 0) (fun _ _ ↦ mem_univ _)
  have hp := domainLimit_mul hs sine_div_domainLimit
  norm_num only [Real.sin_zero, zero_mul] at hp
  apply (domainLimit_congr_domain ?_).mp hp
  intro x _
  ring

/-- Bài tập 3.3.5(b): giới hạn trên miền cả hai mẫu lượng giác khác 0. -/
theorem tangent_cosine_ratio_limit :
    DomainLimit {x : ℝ | Real.cos x ≠ 0 ∧ 1 - Real.cos x ≠ 0}
      (fun x ↦ x * Real.tan x / (1 - Real.cos x)) 0 2 := by
  have haSin := derivative_quotient_domain_accumulation (Real.hasDerivAt_sin 0)
    Real.sin_zero (by norm_num)
  have hcos : {x : ℝ | Real.cos x ≠ 0} ∈ 𝓝 0 :=
    Real.continuous_cos.continuousAt.eventually_ne (by norm_num)
  have ha : AccumulationPointOf {x : ℝ | Real.cos x ≠ 0 ∧ 1 - Real.cos x ≠ 0} 0 := by
    apply accumulationPointOf_mono (accumulationPointOf_inter_nhds haSin hcos)
    intro x hx
    refine ⟨hx.2, ?_⟩
    intro he
    have hc : Real.cos x = 1 := by linarith
    have hs := Real.sin_sq_add_cos_sq x
    rw [hc] at hs
    exact hx.1 (by nlinarith [sq_nonneg (Real.sin x)])
  have hsinv := domainLimit_div_extension
    (domainLimit_restrict (constant_domainLimit 1 0) (univ_diff_accumulation 0) (fun _ _ ↦ mem_univ _)) sine_div_domainLimit (by norm_num)
  norm_num only [div_one] at hsinv
  have hRatio : DomainLimit (univ \ {0}) (fun x : ℝ ↦ x / Real.sin x) 0 1 := by
    apply (domainLimit_congr_domain ?_).mp hsinv
    intro x _
    simp only [one_div, inv_div]
  have hR := domainLimit_restrict hRatio ha (by
    intro x hx
    refine ⟨mem_univ x, ?_⟩
    simp only [mem_singleton_iff]
    intro he
    rw [he] at hx
    exact hx.2 (by norm_num))
  have hc := domainLimit_of_continuousAt ha Real.continuous_cos.continuousAt
  have hnum := domainLimit_mul hR (domainLimit_add (domainLimit_restrict (constant_domainLimit 1 0) ha (fun _ _ ↦ mem_univ _)) hc)
  have hlim := domainLimit_div_extension hnum hc (by norm_num)
  norm_num only [Real.cos_zero, one_add_one_eq_two, mul_one, one_mul, div_one] at hlim
  apply (domainLimit_congr_domain ?_).mp hlim
  intro x hx
  rcases hx with ⟨hcosx, hden⟩
  by_cases hsinx : Real.sin x = 0
  · simp [Real.tan_eq_sin_div_cos, hsinx]
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hcosx, hden, hsinx]
    have he : (1 + Real.cos x) * (1 - Real.cos x) = Real.sin x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [mul_assoc, he]


theorem cos_add_one_half_square (x : ℝ) : Real.cos x + 1 = 2 * Real.cos (x / 2) ^ 2 := by
  have h := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  linarith

/-- Bài tập 3.3.5(c): giới hạn trên miền mẫu khác 0. -/
theorem cosine_triple_ratio_limit :
    DomainLimit {x : ℝ | Real.cos (3 * x) + 1 ≠ 0}
      (fun x ↦ (Real.cos x + 1) / (Real.cos (3 * x) + 1)) Real.pi (1 / 9) := by
  have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two]
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  have hf : HasDerivAt (fun x : ℝ ↦ Real.cos (x / 2)) (-1 / 2) Real.pi := by
    convert! (Real.hasDerivAt_cos (Real.pi / 2)).comp Real.pi
      ((hasDerivAt_id Real.pi).div_const 2) using 1
    norm_num [Function.comp_def, Real.sin_pi_div_two]
  have hg : HasDerivAt (fun x : ℝ ↦ Real.cos (3 * x / 2)) (3 / 2) Real.pi := by
    convert! (Real.hasDerivAt_cos (3 * Real.pi / 2)).comp Real.pi
      (((hasDerivAt_id Real.pi).const_mul 3).div_const 2) using 1
    norm_num [Function.comp_def, hsin]
  have haHalf := derivative_quotient_domain_accumulation hg hcos (by norm_num)
  have ha : AccumulationPointOf {x : ℝ | Real.cos (3 * x) + 1 ≠ 0} Real.pi := by
    apply accumulationPointOf_mono haHalf
    intro x hx
    change Real.cos (3 * x) + 1 ≠ 0
    rw [cos_add_one_half_square]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  have hr := ratio_of_derivative_slopes ha hf hg Real.cos_pi_div_two hcos (by norm_num)
  have hp := domainLimit_mul hr hr
  norm_num only at hp
  apply (domainLimit_congr_domain ?_).mp hp
  intro x hx
  rw [cos_add_one_half_square, cos_add_one_half_square]
  rw [← div_mul_div_comm]
  ring

/-- Bài tập 3.3.5(d): giới hạn trên miền hai căn xác định và hai mẫu lượng giác khác 0. -/
theorem square_root_tangent_sine_ratio_limit :
    DomainLimit {x : ℝ | Real.cos x ≠ 0 ∧ Real.sin x ≠ 0 ∧
      0 ≤ 1 + Real.tan x ∧ 0 ≤ 1 - Real.tan x}
      (fun x ↦ (Real.sqrt (1 + Real.tan x) - Real.sqrt (1 - Real.tan x)) / Real.sin x) 0 1 := by
  have ht : HasDerivAt Real.tan 1 0 := by
    convert! Real.hasDerivAt_tan (x := 0) (by norm_num) using 1
    norm_num
  have hsp : HasDerivAt Real.sqrt (1 / 2) (1 + Real.tan 0) := by
    convert! Real.hasDerivAt_sqrt (x := 1) (by norm_num) using 1
    all_goals norm_num [Real.tan_zero]
  have hsm : HasDerivAt Real.sqrt (1 / 2) (1 - Real.tan 0) := by
    convert! Real.hasDerivAt_sqrt (x := 1) (by norm_num) using 1
    all_goals norm_num [Real.tan_zero]
  have hp : HasDerivAt (fun x : ℝ ↦ Real.sqrt (1 + Real.tan x)) (1 / 2) 0 := by
    convert! hsp.comp 0 (ht.const_add 1) using 1
    norm_num [Function.comp_def]
  have hm : HasDerivAt (fun x : ℝ ↦ Real.sqrt (1 - Real.tan x)) (-1 / 2) 0 := by
    convert! hsm.comp 0 (ht.const_sub 1) using 1
    norm_num [Function.comp_def]
  have hnum : HasDerivAt
      (fun x : ℝ ↦ Real.sqrt (1 + Real.tan x) - Real.sqrt (1 - Real.tan x)) 1 0 := by
    convert! hp.sub hm using 1
    norm_num
  have haSin := derivative_quotient_domain_accumulation (Real.hasDerivAt_sin 0)
    Real.sin_zero (by norm_num)
  have hE : {x : ℝ | Real.cos x ≠ 0 ∧ -1 < Real.tan x ∧ Real.tan x < 1} ∈ 𝓝 0 := by
    have hc : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), Real.cos x ≠ 0 :=
      (show ContinuousAt Real.cos 0 from Real.continuous_cos.continuousAt).eventually_ne (by norm_num)
    have hh := ht.continuousAt (Ioo_mem_nhds (a := (-1 : ℝ)) (b := 1) (by norm_num) (by norm_num))
    filter_upwards [hc, hh] with x hx hy
    exact ⟨hx, hy⟩
  have ha : AccumulationPointOf {x : ℝ | Real.cos x ≠ 0 ∧ Real.sin x ≠ 0 ∧
      0 ≤ 1 + Real.tan x ∧ 0 ≤ 1 - Real.tan x} 0 := by
    apply accumulationPointOf_mono (accumulationPointOf_inter_nhds haSin hE)
    intro x hx
    exact ⟨hx.2.1, hx.1, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
  convert! ratio_of_derivative_slopes ha hnum (Real.hasDerivAt_sin 0)
    (by norm_num) Real.sin_zero (by norm_num) using 1
  norm_num


theorem not_bddAbove_of_eventually_mem {D : Set ℝ} (hD : ∀ᶠ x : ℝ in atTop, x ∈ D) :
    ¬ BddAbove D := by
  rintro ⟨M, hM⟩
  obtain ⟨x, hxD, hxM⟩ := (hD.and (eventually_gt_atTop M)).exists
  exact not_lt_of_ge (hM hxD) hxM


theorem not_bddBelow_of_eventually_mem {D : Set ℝ} (hD : ∀ᶠ x : ℝ in atBot, x ∈ D) :
    ¬ BddBelow D := by
  rintro ⟨M, hM⟩
  obtain ⟨x, hxD, hxM⟩ := (hD.and (eventually_lt_atBot M)).exists
  exact not_lt_of_ge (hM hxD) hxM

/-- Bài tập 3.3.3(a): giới hạn phân thức tại vô cực. -/
theorem cubic_denominator_ratio_atTop :
    DomainAtTopLimit {x : ℝ | x ^ 3 - 3 ≠ 0}
      (fun x ↦ (3 * x ^ 2 - 2 * x + 5) / (x ^ 3 - 3)) 0 := by
  have heD : ∀ᶠ x : ℝ in atTop, x ^ 3 - 3 ≠ 0 := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hp : 2 ^ 3 < x ^ 3 := pow_lt_pow_left₀ hx (by norm_num) (by decide : (3 : ℕ) ≠ 0)
    norm_num at hp
    linarith
  apply (domainAtTopLimit_iff_tendsto (not_bddAbove_of_eventually_mem heD)).mpr
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have ht : Tendsto (fun x : ℝ ↦
      (3 * x⁻¹ - 2 * (x⁻¹) ^ 2 + 5 * (x⁻¹) ^ 3) / (1 - 3 * (x⁻¹) ^ 3)) atTop (𝓝 0) := by
    convert! (((hi.const_mul 3).sub ((hi.pow 2).const_mul 2)).add
      ((hi.pow 3).const_mul 5)).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub ((hi.pow 3).const_mul 3)) (by norm_num) using 1
    norm_num
  have heq : (fun x : ℝ ↦
      (3 * x⁻¹ - 2 * (x⁻¹) ^ 2 + 5 * (x⁻¹) ^ 3) / (1 - 3 * (x⁻¹) ^ 3)) =ᶠ[atTop]
      (fun x ↦ (3 * x ^ 2 - 2 * x + 5) / (x ^ 3 - 3)) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ), heD] with x hx hd
    have hx0 : x ≠ 0 := by linarith
    field_simp [hx0, hd]
  exact (ht.congr' heq).mono_left inf_le_left

/-- Bài tập 3.3.3(b): giới hạn bằng −∞ trên miền tự nhiên của thương đa thức. -/
theorem quartic_cubic_ratio_atBot :
    ¬ BddBelow {x : ℝ | x ^ 3 - 9 * x ≠ 0} ∧
      Tendsto (fun x : ℝ ↦ (x ^ 4 - x + 3) / (x ^ 3 - 9 * x))
        (atBot ⊓ 𝓟 {x : ℝ | x ^ 3 - 9 * x ≠ 0}) atBot := by
  have heD : ∀ᶠ x : ℝ in atBot, x ^ 3 - 9 * x ≠ 0 := by
    filter_upwards [eventually_lt_atBot (-4 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hxx : x ^ 2 - 9 ≠ 0 := by nlinarith [sq_nonneg (x + 4)]
    rw [show x ^ 3 - 9 * x = x * (x ^ 2 - 9) by ring]
    exact mul_ne_zero hx0 hxx
  refine ⟨not_bddBelow_of_eventually_mem heD, ?_⟩
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have ht : Tendsto (fun x : ℝ ↦
      (1 - (x⁻¹) ^ 3 + 3 * (x⁻¹) ^ 4) / (1 - 9 * (x⁻¹) ^ 2)) atBot (𝓝 1) := by
    convert! (((tendsto_const_nhds (x := (1 : ℝ))).sub (hi.pow 3)).add
      ((hi.pow 4).const_mul 3)).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub ((hi.pow 2).const_mul 9)) (by norm_num) using 1
    norm_num
  have hprod := Tendsto.atBot_mul_pos (by norm_num : 0 < (1 : ℝ))
    (tendsto_id : Tendsto (fun x : ℝ ↦ x) atBot atBot) ht
  have heq : (fun x : ℝ ↦ x *
      ((1 - (x⁻¹) ^ 3 + 3 * (x⁻¹) ^ 4) / (1 - 9 * (x⁻¹) ^ 2))) =ᶠ[atBot]
      (fun x ↦ (x ^ 4 - x + 3) / (x ^ 3 - 9 * x)) := by
    filter_upwards [eventually_lt_atBot (-4 : ℝ), heD] with x hx hd
    have hx0 : x ≠ 0 := by linarith
    field_simp [hx0, hd]
  exact (hprod.congr' heq).mono_left inf_le_left


theorem sqrt_quadratic_factor {x : ℝ} (hx : x ≠ 0) :
    Real.sqrt (2 * x ^ 2 + 3) = |x| * Real.sqrt (2 + 3 * (x⁻¹) ^ 2) := by
  have he : 2 * x ^ 2 + 3 = x ^ 2 * (2 + 3 * (x⁻¹) ^ 2) := by
    field_simp [hx]
  rw [he, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs]

/-- Bài tập 3.3.3(c): giới hạn phân thức tại vô cực. -/
theorem sqrt_quadratic_ratio_atTop :
    DomainAtTopLimit {x : ℝ | 5 * x - 1 ≠ 0}
      (fun x ↦ Real.sqrt (2 * x ^ 2 + 3) / (5 * x - 1)) (Real.sqrt 2 / 5) := by
  have heD : ∀ᶠ x : ℝ in atTop, 5 * x - 1 ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    linarith
  apply (domainAtTopLimit_iff_tendsto (not_bddAbove_of_eventually_mem heD)).mpr
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have ht : Tendsto (fun x : ℝ ↦ Real.sqrt (2 + 3 * (x⁻¹) ^ 2) / (5 - x⁻¹))
      atTop (𝓝 (Real.sqrt 2 / 5)) := by
    convert! ((tendsto_const_nhds (x := (2 : ℝ))).add ((hi.pow 2).const_mul 3)).sqrt.div
      ((tendsto_const_nhds (x := (5 : ℝ))).sub hi) (by norm_num) using 1
    norm_num
  have heq : (fun x : ℝ ↦ Real.sqrt (2 + 3 * (x⁻¹) ^ 2) / (5 - x⁻¹)) =ᶠ[atTop]
      (fun x ↦ Real.sqrt (2 * x ^ 2 + 3) / (5 * x - 1)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), heD] with x hx hd
    have hx0 : x ≠ 0 := by linarith
    rw [sqrt_quadratic_factor hx0, abs_of_pos (by linarith : 0 < x)]
    field_simp [hx0, hd]
  exact (ht.congr' heq).mono_left inf_le_left

/-- Bài tập 3.3.3(d): giới hạn phân thức tại vô cực. -/
theorem sqrt_quadratic_ratio_atBot :
    DomainAtBotLimit {x : ℝ | 5 * x - 1 ≠ 0}
      (fun x ↦ Real.sqrt (2 * x ^ 2 + 3) / (5 * x - 1)) (-Real.sqrt 2 / 5) := by
  have heD : ∀ᶠ x : ℝ in atBot, 5 * x - 1 ≠ 0 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    linarith
  apply (domainAtBotLimit_iff_tendsto (not_bddBelow_of_eventually_mem heD)).mpr
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have ht : Tendsto (fun x : ℝ ↦ -Real.sqrt (2 + 3 * (x⁻¹) ^ 2) / (5 - x⁻¹))
      atBot (𝓝 (-Real.sqrt 2 / 5)) := by
    convert! ((tendsto_const_nhds (x := (2 : ℝ))).add ((hi.pow 2).const_mul 3)).sqrt.neg.div
      ((tendsto_const_nhds (x := (5 : ℝ))).sub hi) (by norm_num) using 1
    norm_num
  have heq : (fun x : ℝ ↦ -Real.sqrt (2 + 3 * (x⁻¹) ^ 2) / (5 - x⁻¹)) =ᶠ[atBot]
      (fun x ↦ Real.sqrt (2 * x ^ 2 + 3) / (5 * x - 1)) := by
    filter_upwards [eventually_lt_atBot (0 : ℝ), heD] with x hx hd
    have hx0 : x ≠ 0 := ne_of_lt hx
    rw [sqrt_quadratic_factor hx0, abs_of_neg hx]
    field_simp [hx0, hd]
  exact (ht.congr' heq).mono_left inf_le_left


/-- Bài tập 3.3.4(a): giới hạn trên miền căn bậc hai xác định. -/
theorem consecutive_sqrt_difference_atTop :
    DomainAtTopLimit (Ici (0 : ℝ)) (fun x ↦ Real.sqrt (x + 1) - Real.sqrt x) 0 := by
  have heD : ∀ᶠ x : ℝ in atTop, x ∈ Ici (0 : ℝ) := eventually_ge_atTop 0
  apply (domainAtTopLimit_iff_tendsto (not_bddAbove_of_eventually_mem heD)).mpr
  have hsqrt : Tendsto Real.sqrt atTop atTop := by
    change Tendsto (fun x : ℝ ↦ Real.sqrt x) atTop atTop
    simpa only [Real.sqrt_eq_rpow] using tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))
  have hsum : Tendsto (fun x : ℝ ↦ Real.sqrt (x + 1) + Real.sqrt x) atTop atTop :=
    tendsto_atTop_mono (fun x ↦ le_add_of_nonneg_left (Real.sqrt_nonneg (x + 1))) hsqrt
  have hi := hsum.inv_tendsto_atTop
  have heq : (fun x : ℝ ↦ (Real.sqrt (x + 1) + Real.sqrt x)⁻¹) =ᶠ[atTop]
      (fun x ↦ Real.sqrt (x + 1) - Real.sqrt x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hden : Real.sqrt (x + 1) + Real.sqrt x ≠ 0 := by positivity
    have h1 := Real.sq_sqrt (by linarith : 0 ≤ x + 1)
    have h2 := Real.sq_sqrt hx.le
    rw [← one_div]
    symm
    apply (eq_div_iff hden).mpr
    nlinarith
  exact (hi.congr' heq).mono_left inf_le_left


theorem signedCubeRoot_tendsto_atBot : Tendsto signedCubeRoot atBot atBot := by
  have hh : Tendsto (fun x : ℝ ↦ -((-x) ^ (1 / 3 : ℝ))) atBot atBot :=
    tendsto_neg_atTop_atBot.comp ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 3 : ℝ))).comp
      tendsto_neg_atBot_atTop)
  apply hh.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  exact (if_neg (not_le_of_gt hx)).symm

/-- Bài tập 3.3.4(b): giới hạn chứa căn bậc ba thực. -/
theorem consecutive_cube_root_difference_atBot :
    DomainAtBotLimit univ (fun x ↦ signedCubeRoot (x + 1) - signedCubeRoot (x - 1)) 0 := by
  apply (domainAtBotLimit_iff_tendsto not_bddBelow_univ).mpr
  have hu : Tendsto (fun x : ℝ ↦ signedCubeRoot (x + 1)) atBot atBot :=
    signedCubeRoot_tendsto_atBot.comp (tendsto_atBot_add_const_right atBot 1 tendsto_id)
  have hv : Tendsto (fun x : ℝ ↦ signedCubeRoot (x - 1)) atBot atBot :=
    signedCubeRoot_tendsto_atBot.comp (by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atBot_add_const_right atBot (-1 : ℝ) tendsto_id)
  have hu2 : Tendsto (fun x : ℝ ↦ signedCubeRoot (x + 1) ^ 2) atBot atTop := by
    convert! (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp (tendsto_neg_atBot_atTop.comp hu) using 1
    funext x
    simp only [Function.comp_def, neg_sq]
  have hden : Tendsto (fun x : ℝ ↦ signedCubeRoot (x + 1) ^ 2 +
      signedCubeRoot (x + 1) * signedCubeRoot (x - 1) + signedCubeRoot (x - 1) ^ 2) atBot atTop := by
    apply tendsto_atTop_mono' atBot ?_ hu2
    filter_upwards [hu.eventually_lt_atBot 0, hv.eventually_lt_atBot 0] with x hx hy
    have hp : 0 ≤ signedCubeRoot (x + 1) * signedCubeRoot (x - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hx.le hy.le
    nlinarith [sq_nonneg (signedCubeRoot (x - 1))]
  have hi := hden.inv_tendsto_atTop.const_mul 2
  have heq : (fun x : ℝ ↦ 2 * (signedCubeRoot (x + 1) ^ 2 +
      signedCubeRoot (x + 1) * signedCubeRoot (x - 1) + signedCubeRoot (x - 1) ^ 2)⁻¹) =ᶠ[atBot]
      (fun x ↦ signedCubeRoot (x + 1) - signedCubeRoot (x - 1)) := by
    filter_upwards [hden.eventually_gt_atTop 0] with x hx
    rw [← div_eq_mul_inv]
    symm
    apply (eq_div_iff (ne_of_gt hx)).mpr
    have hu3 := signedCubeRoot_cube (x + 1)
    have hv3 := signedCubeRoot_cube (x - 1)
    nlinarith
  have ht : Tendsto (fun x : ℝ ↦ 2 * (signedCubeRoot (x + 1) ^ 2 +
      signedCubeRoot (x + 1) * signedCubeRoot (x - 1) + signedCubeRoot (x - 1) ^ 2)⁻¹)
      atBot (𝓝 0) := by simpa only [mul_zero, Pi.inv_apply] using hi
  exact (ht.congr' heq).mono_left inf_le_left


theorem cubic_root_polynomial_factor {x : ℝ} (hx : x ≠ 0) :
    signedCubeRoot (x ^ 3 + 3 * x ^ 2) = x * signedCubeRoot (1 + 3 * x⁻¹) := by
  apply signedCubeRoot_unique
  rw [mul_pow, signedCubeRoot_cube]
  field_simp [hx]


theorem sqrt_square_add_one_factor {x : ℝ} (hx : x ≠ 0) :
    Real.sqrt (x ^ 2 + 1) = |x| * Real.sqrt (1 + (x⁻¹) ^ 2) := by
  have he : x ^ 2 + 1 = x ^ 2 * (1 + (x⁻¹) ^ 2) := by field_simp [hx]
  rw [he, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs]

/-- Bài tập 3.3.4(c): giới hạn bằng 1. -/
theorem cubic_root_minus_sqrt_atTop :
    DomainAtTopLimit univ (fun x : ℝ ↦ signedCubeRoot (x ^ 3 + 3 * x ^ 2) - Real.sqrt (x ^ 2 + 1)) 1 := by
  apply (domainAtTopLimit_iff_tendsto not_bddAbove_univ).mpr
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have harg : Tendsto (fun x : ℝ ↦ 1 + 3 * x⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using (hi.const_mul 3).const_add 1
  have harg' : Tendsto (fun x : ℝ ↦ 1 + 3 * x⁻¹) atTop (𝓝[≠] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨harg, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    have hi0 : 0 < x⁻¹ := inv_pos.mpr hx
    linarith
  have hfirst : Tendsto (fun x : ℝ ↦ 3 * slope signedCubeRoot 1 (1 + 3 * x⁻¹)) atTop (𝓝 1) := by
    have hh := (signedCubeRoot_hasDerivAt_one.tendsto_slope.comp harg').const_mul 3
    simpa only [mul_one_div_cancel (by norm_num : (3 : ℝ) ≠ 0), Function.comp_apply] using hh
  have hsecond : Tendsto (fun x : ℝ ↦ x⁻¹ / (Real.sqrt (1 + (x⁻¹) ^ 2) + 1)) atTop (𝓝 0) := by
    convert! hi.div (((tendsto_const_nhds (x := (1 : ℝ))).add (hi.pow 2)).sqrt.add_const 1)
      (by norm_num) using 1
    norm_num
  have ht := hfirst.sub hsecond
  have heq : (fun x : ℝ ↦ 3 * slope signedCubeRoot 1 (1 + 3 * x⁻¹) -
      x⁻¹ / (Real.sqrt (1 + (x⁻¹) ^ 2) + 1)) =ᶠ[atTop]
      (fun x ↦ signedCubeRoot (x ^ 3 + 3 * x ^ 2) - Real.sqrt (x ^ 2 + 1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hroot1 : signedCubeRoot 1 = 1 := signedCubeRoot_unique (by norm_num)
    have hfirstx : x * (signedCubeRoot (1 + 3 * x⁻¹) - 1) =
        3 * slope signedCubeRoot 1 (1 + 3 * x⁻¹) := by
      rw [slope_def_field, hroot1]
      field_simp [hx0]
      ring
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + (x⁻¹) ^ 2)
    have hden : Real.sqrt (1 + (x⁻¹) ^ 2) + 1 ≠ 0 := by positivity
    have hsecondx : x * (Real.sqrt (1 + (x⁻¹) ^ 2) - 1) =
        x⁻¹ / (Real.sqrt (1 + (x⁻¹) ^ 2) + 1) := by
      apply (eq_div_iff hden).mpr
      calc
        x * (Real.sqrt (1 + (x⁻¹) ^ 2) - 1) * (Real.sqrt (1 + (x⁻¹) ^ 2) + 1) =
            x * (x⁻¹) ^ 2 := by nlinarith
        _ = x⁻¹ := by field_simp [hx0]
    rw [cubic_root_polynomial_factor hx0, sqrt_square_add_one_factor hx0, abs_of_pos hx]
    rw [← hfirstx, ← hsecondx]
    ring
  have ht' : Tendsto (fun x : ℝ ↦ 3 * slope signedCubeRoot 1 (1 + 3 * x⁻¹) -
      x⁻¹ / (Real.sqrt (1 + (x⁻¹) ^ 2) + 1)) atTop (𝓝 1) := by simpa only [sub_zero] using ht
  exact (ht'.congr' heq).mono_left inf_le_left

/-- Bài tập 3.3.4(d): giới hạn bằng −∞ trên nhánh âm. -/
theorem cubic_root_minus_sqrt_atBot :
    ¬ BddBelow (univ : Set ℝ) ∧ Tendsto
      (fun x : ℝ ↦ signedCubeRoot (x ^ 3 + 3 * x ^ 2) - Real.sqrt (x ^ 2 + 1))
      (atBot ⊓ 𝓟 univ) atBot := by
  refine ⟨not_bddBelow_univ, ?_⟩
  have hi : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have harg : Tendsto (fun x : ℝ ↦ 1 + 3 * x⁻¹) atBot (𝓝 1) := by
    simpa only [mul_zero, add_zero] using (hi.const_mul 3).const_add 1
  have hroot : Tendsto (fun x : ℝ ↦ signedCubeRoot (1 + 3 * x⁻¹)) atBot (𝓝 1) := by
    have hh := signedCubeRoot_hasDerivAt_one.continuousAt.tendsto.comp harg
    convert! hh using 1
    norm_num [signedCubeRoot]
  have hsum : Tendsto (fun x : ℝ ↦ signedCubeRoot (1 + 3 * x⁻¹) + Real.sqrt (1 + (x⁻¹) ^ 2))
      atBot (𝓝 2) := by
    convert! hroot.add ((tendsto_const_nhds (x := (1 : ℝ))).add (hi.pow 2)).sqrt using 1
    norm_num
  have ht := Tendsto.atBot_mul_pos (by norm_num : 0 < (2 : ℝ))
    (tendsto_id : Tendsto (fun x : ℝ ↦ x) atBot atBot) hsum
  have heq : (fun x : ℝ ↦ x * (signedCubeRoot (1 + 3 * x⁻¹) + Real.sqrt (1 + (x⁻¹) ^ 2))) =ᶠ[atBot]
      (fun x ↦ signedCubeRoot (x ^ 3 + 3 * x ^ 2) - Real.sqrt (x ^ 2 + 1)) := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    rw [cubic_root_polynomial_factor (ne_of_lt hx), sqrt_square_add_one_factor (ne_of_lt hx), abs_of_neg hx]
    ring
  exact (ht.congr' heq).mono_left inf_le_left


theorem monotone_upper_endpoint {D : Set ℝ} {f : ℝ → ℝ} {F : Filter ℝ}
    (hD : D.Nonempty) (hf : MonotoneOn f D) (hmem : ∀ᶠ x in F, x ∈ D)
    (hafter : ∀ y ∈ D, ∀ᶠ x in F, y ≤ x) :
    (BddAbove (f '' D) → Tendsto f F (𝓝 (sSup (f '' D)))) ∧
      (¬ BddAbove (f '' D) → Tendsto f F atTop) := by
  constructor
  · intro hb
    apply tendsto_order.mpr
    constructor
    · intro L hL
      obtain ⟨v, ⟨y, hy, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (hD.image f) hL
      filter_upwards [hmem, hafter y hy] with x hx hxy
      exact hv.trans_le (hf hy hx hxy)
    · intro U hU
      filter_upwards [hmem] with x hx
      exact (le_csSup hb ⟨x, hx, rfl⟩).trans_lt hU
  · intro hb
    apply tendsto_atTop.mpr
    intro M
    have hh : ∃ y ∈ D, M < f y := by
      by_contra hn
      push Not at hn
      exact hb ⟨M, by rintro v ⟨y, hy, rfl⟩; exact hn y hy⟩
    obtain ⟨y, hy, hMy⟩ := hh
    filter_upwards [hmem, hafter y hy] with x hx hxy
    exact hMy.le.trans (hf hy hx hxy)


theorem monotone_lower_endpoint {D : Set ℝ} {f : ℝ → ℝ} {F : Filter ℝ}
    (hD : D.Nonempty) (hf : MonotoneOn f D) (hmem : ∀ᶠ x in F, x ∈ D)
    (hbefore : ∀ y ∈ D, ∀ᶠ x in F, x ≤ y) :
    (BddBelow (f '' D) → Tendsto f F (𝓝 (sInf (f '' D)))) ∧
      (¬ BddBelow (f '' D) → Tendsto f F atBot) := by
  constructor
  · intro hb
    apply tendsto_order.mpr
    constructor
    · intro L hL
      filter_upwards [hmem] with x hx
      exact hL.trans_le (csInf_le hb ⟨x, hx, rfl⟩)
    · intro U hU
      obtain ⟨v, ⟨y, hy, rfl⟩, hv⟩ := exists_lt_of_csInf_lt (hD.image f) hU
      filter_upwards [hmem, hbefore y hy] with x hx hxy
      exact (hf hx hy hxy).trans_lt hv
  · intro hb
    apply tendsto_atBot.mpr
    intro M
    have hh : ∃ y ∈ D, f y < M := by
      by_contra hn
      push Not at hn
      exact hb ⟨M, by rintro v ⟨y, hy, rfl⟩; exact hn y hy⟩
    obtain ⟨y, hy, hyM⟩ := hh
    filter_upwards [hmem, hbefore y hy] with x hx hxy
    exact (hf hx hy hxy).trans hyM.le


theorem leftAccumulation_interval_endpoint {a b : ℝ} (hab : a < b) : LeftAccumulationPointOf (Ioo a b) b := by
  intro δ hδ
  refine ⟨b - min δ (b - a) / 2, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    linarith [lt_min hδ (sub_pos.mpr hab), min_le_left δ (b - a), min_le_right δ (b - a)]


theorem rightAccumulation_interval_endpoint {a b : ℝ} (hab : a < b) : RightAccumulationPointOf (Ioo a b) a := by
  intro δ hδ
  refine ⟨a + min δ (b - a) / 2, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    linarith [lt_min hδ (sub_pos.mpr hab), min_le_left δ (b - a), min_le_right δ (b - a)]


theorem leftAccumulation_Iio_endpoint (b : ℝ) : LeftAccumulationPointOf (Iio b) b := by
  intro δ hδ
  exact ⟨b - δ / 2, by change b - δ / 2 < b; linarith, by linarith, by linarith⟩


theorem rightAccumulation_Ioi_endpoint (a : ℝ) : RightAccumulationPointOf (Ioi a) a := by
  intro δ hδ
  exact ⟨a + δ / 2, by change a < a + δ / 2; linarith, by linarith, by linarith⟩

/-- Bài tập 3.3.12(a) sai nếu thiếu giả thiết a<b. -/
theorem printed_bounded_interval_endpoint_false :
    ¬ (∀ (a b : ℝ) (f : ℝ → ℝ), MonotoneOn f (Ioo a b) → BddAbove (f '' Ioo a b) →
      ∃ L, DomainLeftLimit (Ioo a b) f b L) := by
  intro h
  have hm : MonotoneOn (fun _ : ℝ ↦ (0 : ℝ)) (Ioo 0 0) := fun _ _ _ _ _ ↦ le_rfl
  have hb : BddAbove ((fun _ : ℝ ↦ (0 : ℝ)) '' Ioo (0 : ℝ) 0) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact le_rfl
  obtain ⟨L, hL⟩ := h 0 0 (fun _ ↦ 0) hm hb
  obtain ⟨x, hx, _, _⟩ := hL.1 1 zero_lt_one
  exact (not_lt_of_ge hx.1.le) hx.2

/-- Bài tập 3.3.12(a): với a<b, hàm tăng không ngặt trên (a,b) có giới hạn trái tại b hữu hạn nếu bị chặn trên, bằng +∞ nếu không. -/
theorem monotone_Ioo_upper_endpoint {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : MonotoneOn f (Ioo a b)) :
    (BddAbove (f '' Ioo a b) → DomainLeftLimit (Ioo a b) f b (sSup (f '' Ioo a b))) ∧
      (¬ BddAbove (f '' Ioo a b) → DomainLeftTopLimit (Ioo a b) f b) := by
  have ha := leftAccumulation_interval_endpoint hab
  have hh := monotone_upper_endpoint (nonempty_Ioo.mpr hab) hf
    (show ∀ᶠ x in 𝓝[Ioo a b ∩ Iio b] b, x ∈ Ioo a b from
      Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[Ioo a b ∩ Iio b] b, x ∈ Ioo a b ∩ Iio b) (fun _ hx ↦ hx.1))
    (fun y hy ↦ Filter.Eventually.filter_mono nhdsWithin_le_nhds (show ∀ᶠ x in 𝓝 b, y ≤ x from Ici_mem_nhds hy.2))
  exact ⟨fun hb ↦ (domainLeftLimit_iff_tendsto ha).mpr (hh.1 hb), fun hb ↦ ⟨ha, hh.2 hb⟩⟩

/-- Bài tập 3.3.12(b): giả thiết không bị chặn suy ra a<b. -/
theorem monotone_Ioo_unbounded_upper_endpoint {a b : ℝ} {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ioo a b)) (hb : ¬ BddAbove (f '' Ioo a b)) : DomainLeftTopLimit (Ioo a b) f b := by
  have hab : a < b := by
    by_contra hn
    have he : Ioo a b = ∅ := Ioo_eq_empty_of_le (not_lt.mp hn)
    rw [he, image_empty] at hb
    exact hb bddAbove_empty
  exact (monotone_Ioo_upper_endpoint hab hf).2 hb


theorem monotone_Ioo_lower_endpoint {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : MonotoneOn f (Ioo a b)) :
    (BddBelow (f '' Ioo a b) → DomainRightLimit (Ioo a b) f a (sInf (f '' Ioo a b))) ∧
      (¬ BddBelow (f '' Ioo a b) → DomainRightBotLimit (Ioo a b) f a) := by
  have ha := rightAccumulation_interval_endpoint hab
  have hh := monotone_lower_endpoint (nonempty_Ioo.mpr hab) hf
    (show ∀ᶠ x in 𝓝[Ioo a b ∩ Ioi a] a, x ∈ Ioo a b from
      Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[Ioo a b ∩ Ioi a] a, x ∈ Ioo a b ∩ Ioi a) (fun _ hx ↦ hx.1))
    (fun y hy ↦ Filter.Eventually.filter_mono nhdsWithin_le_nhds (show ∀ᶠ x in 𝓝 a, x ≤ y from Iic_mem_nhds hy.1))
  exact ⟨fun hb ↦ (domainRightLimit_iff_tendsto ha).mpr (hh.1 hb), fun hb ↦ ⟨ha, hh.2 hb⟩⟩


theorem monotone_Iio_upper_endpoint {b : ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f (Iio b)) :
    (BddAbove (f '' Iio b) → DomainLeftLimit (Iio b) f b (sSup (f '' Iio b))) ∧
      (¬ BddAbove (f '' Iio b) → DomainLeftTopLimit (Iio b) f b) := by
  have ha := leftAccumulation_Iio_endpoint b
  have hh := monotone_upper_endpoint (show (Iio b).Nonempty from ⟨b - 1, by change b - 1 < b; linarith⟩) hf
    (show ∀ᶠ x in 𝓝[Iio b ∩ Iio b] b, x ∈ Iio b from
      Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[Iio b ∩ Iio b] b, x ∈ Iio b ∩ Iio b) (fun _ hx ↦ hx.1))
    (fun y hy ↦ Filter.Eventually.filter_mono nhdsWithin_le_nhds (show ∀ᶠ x in 𝓝 b, y ≤ x from Ici_mem_nhds (show y < b from hy)))
  exact ⟨fun hb ↦ (domainLeftLimit_iff_tendsto ha).mpr (hh.1 hb), fun hb ↦ ⟨ha, hh.2 hb⟩⟩


theorem monotone_Ioi_lower_endpoint {a : ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f (Ioi a)) :
    (BddBelow (f '' Ioi a) → DomainRightLimit (Ioi a) f a (sInf (f '' Ioi a))) ∧
      (¬ BddBelow (f '' Ioi a) → DomainRightBotLimit (Ioi a) f a) := by
  have ha := rightAccumulation_Ioi_endpoint a
  have hh := monotone_lower_endpoint (show (Ioi a).Nonempty from ⟨a + 1, by change a < a + 1; linarith⟩) hf
    (show ∀ᶠ x in 𝓝[Ioi a ∩ Ioi a] a, x ∈ Ioi a from
      Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[Ioi a ∩ Ioi a] a, x ∈ Ioi a ∩ Ioi a) (fun _ hx ↦ hx.1))
    (fun y hy ↦ Filter.Eventually.filter_mono nhdsWithin_le_nhds (show ∀ᶠ x in 𝓝 a, x ≤ y from Iic_mem_nhds (show a < y from hy)))
  exact ⟨fun hb ↦ (domainRightLimit_iff_tendsto ha).mpr (hh.1 hb), fun hb ↦ ⟨ha, hh.2 hb⟩⟩


def DomainAtBotBotLimit (D : Set ℝ) (f : ℝ → ℝ) : Prop := ¬ BddBelow D ∧ Tendsto f (atBot ⊓ 𝓟 D) atBot


theorem monotone_atTop_endpoint {D : Set ℝ} {f : ℝ → ℝ}
    (hD : ¬ BddAbove D) (hne : D.Nonempty) (hf : MonotoneOn f D) :
    (BddAbove (f '' D) → DomainAtTopLimit D f (sSup (f '' D))) ∧
      (¬ BddAbove (f '' D) → DomainAtTopTopLimit D f) := by
  have hh := monotone_upper_endpoint hne hf
    ((eventually_mem_principal D).filter_mono inf_le_right)
    (fun y _ ↦ (eventually_ge_atTop y).filter_mono inf_le_left)
  exact ⟨fun hb ↦ (domainAtTopLimit_iff_tendsto hD).mpr (hh.1 hb), fun hb ↦ ⟨hD, hh.2 hb⟩⟩


theorem monotone_atBot_endpoint {D : Set ℝ} {f : ℝ → ℝ}
    (hD : ¬ BddBelow D) (hne : D.Nonempty) (hf : MonotoneOn f D) :
    (BddBelow (f '' D) → DomainAtBotLimit D f (sInf (f '' D))) ∧
      (¬ BddBelow (f '' D) → DomainAtBotBotLimit D f) := by
  have hh := monotone_lower_endpoint hne hf
    ((eventually_mem_principal D).filter_mono inf_le_right)
    (fun y _ ↦ (eventually_le_atBot y).filter_mono inf_le_left)
  exact ⟨fun hb ↦ (domainAtBotLimit_iff_tendsto hD).mpr (hh.1 hb), fun hb ↦ ⟨hD, hh.2 hb⟩⟩


theorem monotone_Ioi_upper_endpoint {a : ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f (Ioi a)) :
    (BddAbove (f '' Ioi a) → DomainAtTopLimit (Ioi a) f (sSup (f '' Ioi a))) ∧
      (¬ BddAbove (f '' Ioi a) → DomainAtTopTopLimit (Ioi a) f) := by
  apply monotone_atTop_endpoint ?_ ⟨a + 1, by change a < a + 1; linarith⟩ hf
  rintro ⟨M, hM⟩
  have hx : max M a + 1 ∈ Ioi a := by change a < max M a + 1; linarith [le_max_right M a]
  have hh := hM hx
  linarith [le_max_left M a]


theorem monotone_Iio_lower_endpoint {b : ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f (Iio b)) :
    (BddBelow (f '' Iio b) → DomainAtBotLimit (Iio b) f (sInf (f '' Iio b))) ∧
      (¬ BddBelow (f '' Iio b) → DomainAtBotBotLimit (Iio b) f) := by
  apply monotone_atBot_endpoint ?_ ⟨b - 1, by change b - 1 < b; linarith⟩ hf
  rintro ⟨M, hM⟩
  have hx : min M b - 1 ∈ Iio b := by change min M b - 1 < b; linarith [min_le_right M b]
  have hh := hM hx
  linarith [min_le_left M b]


theorem monotone_univ_upper_endpoint {f : ℝ → ℝ} (hf : Monotone f) :
    (BddAbove (range f) → DomainAtTopLimit univ f (sSup (range f))) ∧
      (¬ BddAbove (range f) → DomainAtTopTopLimit univ f) := by
  simpa only [image_univ] using monotone_atTop_endpoint not_bddAbove_univ univ_nonempty (hf.monotoneOn univ)


theorem monotone_univ_lower_endpoint {f : ℝ → ℝ} (hf : Monotone f) :
    (BddBelow (range f) → DomainAtBotLimit univ f (sInf (range f))) ∧
      (¬ BddBelow (range f) → DomainAtBotBotLimit univ f) := by
  simpa only [image_univ] using monotone_atBot_endpoint not_bddBelow_univ univ_nonempty (hf.monotoneOn univ)



theorem printed_bounded_lower_interval_endpoint_false :
    ¬ (∀ (a b : ℝ) (f : ℝ → ℝ), MonotoneOn f (Ioo a b) → BddBelow (f '' Ioo a b) →
      ∃ L, DomainRightLimit (Ioo a b) f a L) := by
  intro h
  have hm : MonotoneOn (fun _ : ℝ ↦ (0 : ℝ)) (Ioo 0 0) := fun _ _ _ _ _ ↦ le_rfl
  have hb : BddBelow ((fun _ : ℝ ↦ (0 : ℝ)) '' Ioo (0 : ℝ) 0) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact le_rfl
  obtain ⟨L, hL⟩ := h 0 0 (fun _ ↦ 0) hm hb
  obtain ⟨x, hx, _, _⟩ := hL.1 1 zero_lt_one
  exact (not_lt_of_ge hx.1.le) hx.2


theorem monotone_Ioo_unbounded_lower_endpoint {a b : ℝ} {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ioo a b)) (hb : ¬ BddBelow (f '' Ioo a b)) : DomainRightBotLimit (Ioo a b) f a := by
  have hab : a < b := by
    by_contra hn
    have he : Ioo a b = ∅ := Ioo_eq_empty_of_le (not_lt.mp hn)
    rw [he, image_empty] at hb
    exact hb bddBelow_empty
  exact (monotone_Ioo_lower_endpoint hab hf).2 hb

end calculus.Chapter03.Section03Exercises
