import calculus.Chapter03.Section01
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.Irrational

/-!
# 3.1. Lũy thừa, hàm mũ và logarit

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 418–637.
-/

namespace calculus.Chapter03.Section01Powers

open Set Function


def IntegerExponent (α : ℝ) : Prop := ∃ z : ℤ, (z : ℝ) = α


noncomputable def realPowerDomain (α : ℝ) : Set ℝ := by
  classical
  exact if IntegerExponent α then if 0 < α then univ else {x | x ≠ 0} else Ioi 0


noncomputable def realPowerOnDomain (α : ℝ) : realPowerDomain α → ℝ := fun x => (x : ℝ)^α


theorem positive_integer_power_domain (z : ℤ) (hz : 0 < z) :
    realPowerDomain (z : ℝ) = univ := by
  have hi : IntegerExponent (z : ℝ) := ⟨z,rfl⟩
  have hp : (0:ℝ) < z := by exact_mod_cast hz
  simp only [realPowerDomain,if_pos hi,if_pos hp]


theorem nonpositive_integer_power_domain (z : ℤ) (hz : z ≤ 0) :
    realPowerDomain (z : ℝ) = {x | x ≠ 0} := by
  have hi : IntegerExponent (z : ℝ) := ⟨z,rfl⟩
  have hp : ¬(0:ℝ) < z := by exact_mod_cast (not_lt.mpr hz)
  simp only [realPowerDomain,if_pos hi,if_neg hp]


theorem noninteger_power_domain {α : ℝ} (hα : ¬IntegerExponent α) :
    realPowerDomain α = Ioi 0 := by
  simp only [realPowerDomain,if_neg hα]


theorem zero_exponent_domain : realPowerDomain 0 = {x | x ≠ 0} := by
  simpa only [Int.cast_zero] using nonpositive_integer_power_domain 0 (by norm_num)


theorem one_mem_power_domain (α : ℝ) : (1:ℝ) ∈ realPowerDomain α := by
  unfold realPowerDomain
  split_ifs <;> norm_num


theorem real_power_at_one (α : ℝ) : realPowerOnDomain α ⟨1,one_mem_power_domain α⟩ = 1 := by
  simp only [realPowerOnDomain,Real.one_rpow]


theorem natural_power_domain_and_value (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (x ^ (n:ℝ)) = x^n ∧ x ∈ realPowerDomain (n:ℝ) := by
  refine ⟨Real.rpow_natCast x n,?_⟩
  have hnz : (0:ℤ) < (n:ℤ) := by exact_mod_cast (show 0<n by omega)
  have he := positive_integer_power_domain (n:ℤ) hnz
  have hd : realPowerDomain (n:ℝ)=univ := by simpa only [Int.cast_natCast] using he
  rw [hd]
  exact mem_univ x


theorem integer_real_power_value (z : ℤ) (x : realPowerDomain (z:ℝ)) :
    realPowerOnDomain (z:ℝ) x = (x:ℝ)^z := Real.rpow_intCast _ _


theorem zero_real_power_domain_and_value (x : ℝ) (hx : x ≠ 0) :
    x ∈ realPowerDomain 0 ∧ x^(0:ℝ)=1 := by
  rw [zero_exponent_domain]
  exact ⟨hx,Real.rpow_zero x⟩


theorem negative_power_reciprocal (u v : ℝ) (hu : 0 < u) :
    u^(-v) = 1/u^v := by
  rw [Real.rpow_neg hu.le,one_div]


theorem base_reciprocal_power (u v : ℝ) (hu : 0 < u) (_hu1 : u < 1) :
    u^v = 1/((1/u)^v) := by
  simp only [one_div]
  rw [←Real.rpow_neg_eq_inv_rpow,Real.rpow_neg hu.le,inv_inv]


theorem rational_power_root_equation (u : ℝ) (hu : 0 < u) (m n : ℕ)
    (_hm : 1 ≤ m) (hn : 1 ≤ n) (_hcoprime : Nat.Coprime m n) :
    0 < u^((m:ℝ)/(n:ℝ)) ∧ (u^((m:ℝ)/(n:ℝ)))^n = u^m := by
  refine ⟨Real.rpow_pos_of_pos hu _,?_⟩
  rw [←Real.rpow_natCast, ←Real.rpow_mul hu.le]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
  rw [div_mul_cancel₀ _ hn0,Real.rpow_natCast]


theorem rational_power_root_formula (u : ℝ) (hu : 0<u) (m n : ℕ)
    (_hm : 1≤m) (_hn : 1≤n) (_hcoprime : Nat.Coprime m n) :
    u^((m:ℝ)/(n:ℝ))=(u^m)^((1:ℝ)/(n:ℝ)) := by
  rw [←Real.rpow_natCast u m, ←Real.rpow_mul hu.le]
  congr 1
  ring


theorem negative_integer_power_reciprocal (u : ℝ) (_hu : u≠0) (n : ℕ) (_hn : 1≤n) :
    u^(-(n:ℝ))=1/u^n := by
  rw [Real.rpow_neg_natCast,zpow_neg,zpow_natCast,one_div]


theorem rational_denominator_one (u : ℝ) (m : ℕ) : u^((m:ℝ)/1)=u^m := by
  rw [div_one,Real.rpow_natCast]


theorem rational_positive_power_strictMono (α : ℚ) (hα : 0 < α) :
    StrictMonoOn (fun x : ℝ => x^(α:ℝ)) (Ioi 0) := by
  have hr : (0:ℝ)<α := by exact_mod_cast hα
  exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos hr).mono Ioi_subset_Ici_self


def rationalPowersBelow (a v : ℝ) : Set ℝ := {y | ∃ q : ℚ, (q:ℝ) ≤ v ∧ y=a^(q:ℝ)}


theorem rational_powers_isLUB (a v : ℝ) (ha : 1<a) :
    IsLUB (rationalPowersBelow a v) (a^v) := by
  constructor
  · rintro y ⟨q,hq,rfl⟩
    exact Real.rpow_le_rpow_of_exponent_le ha.le hq
  · intro M hM
    by_contra hn
    have hlt : M<a^v := lt_of_not_ge hn
    by_cases hp : 0<M
    · have hlog : Real.logb a M<v := (Real.logb_lt_iff_lt_rpow ha hp).mpr hlt
      obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn hlog
      have hy : M<a^(q:ℝ) := (Real.logb_lt_iff_lt_rpow ha hp).mp hq1
      exact (not_lt_of_ge (hM ⟨q,hq2.le,rfl⟩)) hy
    · obtain ⟨q,hq⟩ := exists_rat_lt v
      have hy : 0<a^(q:ℝ) := Real.rpow_pos_of_pos (by linarith) _
      have hm := hM ⟨q,hq.le,rfl⟩
      linarith


theorem rational_powers_below_nonempty (a v : ℝ) : (rationalPowersBelow a v).Nonempty := by
  obtain ⟨q,hq⟩ := exists_rat_lt v
  exact ⟨a^(q:ℝ),q,hq.le,rfl⟩


theorem real_power_supremum_definition (a v : ℝ) (ha : 1<a) (_hv : 0<v) :
    sSup (rationalPowersBelow a v) = a^v :=
  (rational_powers_isLUB a v ha).csSup_eq (rational_powers_below_nonempty a v)


theorem rational_power_supremum_consistency (a : ℝ) (ha : 1<a) (v : ℚ) (hv : 0<v) :
    sSup (rationalPowersBelow a (v:ℝ)) = a^(v:ℝ) :=
  real_power_supremum_definition a v ha (by exact_mod_cast hv)

/-- Mục `C03-S01-proposition-001` (i): aᵇ<aᶜ khi a>1 và 0<b<c. -/
theorem exponential_strict_increasing (a b c : ℝ) (ha : 1<a) (_hb : 0<b) (hbc : b<c) :
    a^b<a^c := Real.strictMono_rpow_of_base_gt_one ha hbc

/-- Mục `C03-S01-proposition-001` (ii): aᶜ<aᵇ khi 0<a<1 và 0<b<c. -/
theorem exponential_strict_decreasing (a b c : ℝ) (ha0 : 0<a) (ha1 : a<1)
    (_hb : 0<b) (hbc : b<c) : a^c<a^b :=
  Real.strictAnti_rpow_of_base_lt_one ha0 ha1 hbc

/-- Mục `C03-S01-proposition-001` (iii): a^(b+c)=a^b·a^c với a>0 và b,c thực. -/
theorem real_power_exponent_add (a b c : ℝ) (ha : 0<a) : a^(b+c)=a^b*a^c :=
  Real.rpow_add ha b c


theorem half_exponent_noninteger : ¬IntegerExponent (1/2) := by
  rintro ⟨z,hz⟩
  have hz0 : (0:ℤ) ≤ z := by exact_mod_cast (show (0:ℝ) ≤ (z:ℝ) by linarith)
  have hz1 : z < (1:ℤ) := by exact_mod_cast (show (z:ℝ)<1 by linarith)
  have he : z=0 := by omega
  subst z
  norm_num at hz

/-- Với α=1/2, cơ số 0 không thuộc miền lũy thừa của giáo trình. -/
theorem positive_power_origin_claim_counterexample :
    (0:ℝ)<1/2 ∧ (0:ℝ) ∉ realPowerDomain (1/2) := by
  rw [noninteger_power_domain half_exponent_noninteger]
  norm_num

/-- Lũy thừa với số mũ nguyên dương xác định tại 0 và có giá trị 0. -/
theorem positive_integer_power_at_origin (n : ℕ) (hn : 1 ≤ n) :
    (0:ℝ) ∈ realPowerDomain (n:ℝ) ∧ (0:ℝ)^(n:ℝ)=0 := by
  refine ⟨(natural_power_domain_and_value n hn 0).2,?_⟩
  rw [Real.rpow_natCast,zero_pow (show n≠0 by omega)]


theorem negative_power_origin_excluded (α : ℝ) (hα : α<0) : (0:ℝ) ∉ realPowerDomain α := by
  by_cases hi : IntegerExponent α
  · have hp : ¬0<α := by linarith
    simp only [realPowerDomain,if_pos hi,if_neg hp,mem_ofPred_eq,not_not]
  · rw [noninteger_power_domain hi]
    change ¬(0:ℝ)<0
    exact lt_irrefl 0


noncomputable def exponentialToPositiveReals (a : ℝ) (ha : 0<a) (_ha1 : a≠1) : ℝ → Ioi (0:ℝ) :=
  fun x => ⟨a^x,Real.rpow_pos_of_pos ha x⟩


noncomputable def logarithmOnPositiveReals (a : ℝ) (_ha : 0<a) (_ha1 : a≠1) : Ioi (0:ℝ) → ℝ :=
  fun x => Real.logb a x


noncomputable def exponentialLogarithmEquiv (a : ℝ) (ha : 0<a) (ha1 : a≠1) : ℝ ≃ Ioi (0:ℝ) where
  toFun := exponentialToPositiveReals a ha ha1
  invFun := logarithmOnPositiveReals a ha ha1
  left_inv := fun x => Real.logb_rpow (x:=x) ha ha1
  right_inv := fun x => Subtype.ext (Real.rpow_logb ha ha1 x.property)


theorem exponential_range (a : ℝ) (ha : 0<a) (ha1 : a≠1) :
    range (fun x : ℝ => a^x)=Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact Real.rpow_pos_of_pos ha x
  · intro hy
    exact ⟨Real.logb a y,Real.rpow_logb ha ha1 hy⟩


theorem logarithm_range (a : ℝ) (ha : 0<a) (ha1 : a≠1) :
    range (logarithmOnPositiveReals a ha ha1)=univ := by
  ext y
  simp only [mem_univ,iff_true,mem_range]
  exact ⟨exponentialToPositiveReals a ha ha1 y,Real.logb_rpow ha ha1⟩


theorem exponential_logarithm_base_points (a : ℝ) (ha : 0<a) (ha1 : a≠1) :
    (exponentialToPositiveReals a ha ha1 0 : ℝ)=1 ∧
      logarithmOnPositiveReals a ha ha1 ⟨1,by norm_num⟩=0 := by
  exact ⟨Real.rpow_zero a,Real.logb_one⟩

/-- Phép tách t=r+s với r≤b,s≤c hữu tỉ thất bại khi t=b+c và b,c vô tỉ. -/
theorem rational_endpoint_split_claim_counterexample :
    (0:ℝ) ≤ Real.sqrt 2 + -Real.sqrt 2 ∧
      ¬∃ r s : ℚ, (r:ℝ) ≤ Real.sqrt 2 ∧ (s:ℝ) ≤ -Real.sqrt 2 ∧ (r:ℝ)+(s:ℝ)=0 := by
  constructor
  · simp only [add_neg_cancel,le_refl]
  · rintro ⟨r,s,hr,hs,he⟩
    have hrEq : (r:ℝ)=Real.sqrt 2 := by linarith
    exact irrational_sqrt_two.ne_rat r hrEq.symm

end calculus.Chapter03.Section01Powers
