import calculus.Chapter01.Section04Exercises
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Quot
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic.Ring

/-!
# 1.4. Lớp tương đương, số nguyên và số hữu tỉ

Nguồn: `source/Ch1_taphop.tex`, dòng 734–1509.
-/

set_option autoImplicit false

namespace calculus.Chapter01.Section04Remaining

open Set
open calculus.Chapter01.Section04Exercises (equivalenceClass equivalenceClass_family_eq_pair)

/-- Bài tập 1.4.20: đồng dư hai bình phương theo môđun 4. -/
def integerSquareModFour (x y : ℤ) : Prop := Int.ModEq 4 (x ^ 2) (y ^ 2)


lemma integer_square_mod_four (x : ℤ) : x ^ 2 % 4 = (x % 2) ^ 2 := by
  have hp := (show Int.ModEq 4 x (x % 4) by
    show x % 4 = (x % 4) % 4
    simp).pow 2
  change x ^ 2 % 4 = (x % 4) ^ 2 % 4 at hp
  rw [hp]
  have h0 := Int.emod_nonneg x (by norm_num : (4 : ℤ) ≠ 0)
  have h4 := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 4)
  interval_cases h : x % 4 <;>
    (have h2 : x % 2 = (x % 4) % 2 := by omega)
  all_goals rw [h2, h]; norm_num

/-- Bài tập 1.4.20: đồng dư hai bình phương theo môđun 4 khi và chỉ khi cùng tính chẵn lẻ. -/
theorem integerSquareModFour_iff (x y : ℤ) :
    integerSquareModFour x y ↔ x % 2 = y % 2 := by
  change x ^ 2 % 4 = y ^ 2 % 4 ↔ x % 2 = y % 2
  rw [integer_square_mod_four, integer_square_mod_four]
  have hx0 := Int.emod_nonneg x (by norm_num : (2 : ℤ) ≠ 0)
  have hx2 := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 2)
  have hy0 := Int.emod_nonneg y (by norm_num : (2 : ℤ) ≠ 0)
  have hy2 := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 2)
  interval_cases x % 2 <;> interval_cases y % 2 <;> norm_num

/-- Bài tập 1.4.20: phản xạ, đối xứng và bắc cầu trên toàn ℤ. -/
theorem integerSquareModFour_equivalence : Equivalence integerSquareModFour := by
  constructor
  · intro x
    exact (integerSquareModFour_iff x x).mpr rfl
  · intro x y h
    exact (integerSquareModFour_iff y x).mpr ((integerSquareModFour_iff x y).mp h).symm
  · intro x y z hxy hyz
    exact (integerSquareModFour_iff x z).mpr
      (((integerSquareModFour_iff x y).mp hxy).trans ((integerSquareModFour_iff y z).mp hyz))

/-- Bài tập 1.4.20: hai lớp là các số nguyên chẵn và lẻ. -/
theorem integerSquareModFour_classes :
    equivalenceClass integerSquareModFour 0 = {x : ℤ | Even x} ∧
    equivalenceClass integerSquareModFour 1 = {x : ℤ | Odd x} := by
  constructor <;> ext x
  · simp [equivalenceClass, integerSquareModFour_iff, Int.even_iff]
  · simp [equivalenceClass, integerSquareModFour_iff, Int.odd_iff]

/-- Bài tập 1.4.20: tập thương gồm đúng hai lớp chẵn và lẻ. -/
theorem integerSquareModFour_quotient_classes :
    range (equivalenceClass integerSquareModFour) =
      { {x : ℤ | Even x}, {x : ℤ | Odd x} } := by
  have hclasses := integerSquareModFour_classes
  rw [← hclasses.1, ← hclasses.2]
  apply equivalenceClass_family_eq_pair integerSquareModFour integerSquareModFour_equivalence 0 1
  intro x
  have h0 := Int.emod_nonneg x (by norm_num : (2 : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 2)
  rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h
  · exact Or.inl ((integerSquareModFour_iff x 0).mpr (by simpa using h))
  · exact Or.inr ((integerSquareModFour_iff x 1).mpr (by simpa using h))

/-- Đại diện số nguyên trong Bài tập 1.4.22. -/
abbrev PositivePair := ℕ+ × ℕ+

/-- Bài tập 1.4.22: quan hệ a+d=b+c trên các cặp số tự nhiên dương. -/
def positivePairRelation (p q : PositivePair) : Prop :=
  (p.1 : ℕ) + (q.2 : ℕ) = (p.2 : ℕ) + (q.1 : ℕ)

/-- Giá trị số nguyên mà cặp (a,b) biểu diễn. Phép trừ nằm trong ℤ. -/
def positivePairValue (p : PositivePair) : ℤ := (p.1 : ℕ) - (p.2 : ℕ)


theorem positivePairRelation_iff_value_eq (p q : PositivePair) :
    positivePairRelation p q ↔ positivePairValue p = positivePairValue q := by
  unfold positivePairRelation positivePairValue
  constructor
  · intro h
    have h' : ((p.1 : ℕ) : ℤ) + (q.2 : ℕ) = (p.2 : ℕ) + (q.1 : ℕ) := by exact_mod_cast h
    linarith
  · intro h
    have h' : ((p.1 : ℕ) : ℤ) + (q.2 : ℕ) = (p.2 : ℕ) + (q.1 : ℕ) := by linarith
    exact_mod_cast h'

/-- Bài tập 1.4.22(a): (3,6) cùng lớp với (7,10). -/
theorem positivePair_first_example : positivePairRelation (3, 6) (7, 10) := by norm_num [positivePairRelation]

/-- Bài tập 1.4.22(b): (1,1) không cùng lớp với (3,5). -/
theorem positivePair_second_example : ¬ positivePairRelation (1, 1) (3, 5) := by norm_num [positivePairRelation]

/-- Bài tập 1.4.22(c): quan hệ cặp dương là một quan hệ tương đương. -/
theorem positivePairRelation_equivalence : Equivalence positivePairRelation := by
  constructor
  · intro p
    exact (positivePairRelation_iff_value_eq p p).mpr rfl
  · intro p q h
    exact (positivePairRelation_iff_value_eq q p).mpr
      ((positivePairRelation_iff_value_eq p q).mp h).symm
  · intro p q r hpq hqr
    exact (positivePairRelation_iff_value_eq p r).mpr
      (((positivePairRelation_iff_value_eq p q).mp hpq).trans
        ((positivePairRelation_iff_value_eq q r).mp hqr))

/-- Bài tập 1.4.22(d): năm đại diện phân biệt của mỗi lớp đã cho. -/
theorem positivePair_five_representatives :
    ([((1, 1) : PositivePair), (2, 2), (3, 3), (4, 4), (5, 5)].Nodup ∧
      ∀ p ∈ [((1, 1) : PositivePair), (2, 2), (3, 3), (4, 4), (5, 5)],
        p ∈ equivalenceClass positivePairRelation (1, 1)) ∧
    ([((1, 2) : PositivePair), (2, 3), (3, 4), (4, 5), (5, 6)].Nodup ∧
      ∀ p ∈ [((1, 2) : PositivePair), (2, 3), (3, 4), (4, 5), (5, 6)],
        p ∈ equivalenceClass positivePairRelation (1, 2)) ∧
    ([((2, 1) : PositivePair), (3, 2), (4, 3), (5, 4), (6, 5)].Nodup ∧
      ∀ p ∈ [((2, 1) : PositivePair), (3, 2), (4, 3), (5, 4), (6, 5)],
        p ∈ equivalenceClass positivePairRelation (2, 1)) ∧
    ([((1, 8) : PositivePair), (2, 9), (3, 10), (4, 11), (5, 12)].Nodup ∧
      ∀ p ∈ [((1, 8) : PositivePair), (2, 9), (3, 10), (4, 11), (5, 12)],
        p ∈ equivalenceClass positivePairRelation (5, 12)) := by
  norm_num [List.nodup_cons, equivalenceClass, positivePairRelation]


def positivePairSetoid : Setoid PositivePair where
  r := positivePairRelation
  iseqv := positivePairRelation_equivalence


abbrev IntegerQuotient := Quotient positivePairSetoid

/-- Cộng hai đại diện: (a+c,b+d). -/
def positivePairAdd (p q : PositivePair) : PositivePair := (p.1 + q.1, p.2 + q.2)

/-- Nhân hai đại diện: (ac+bd,ad+bc). -/
def positivePairMul (p q : PositivePair) : PositivePair :=
  (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1)


theorem positivePairValue_add (p q : PositivePair) :
    positivePairValue (positivePairAdd p q) = positivePairValue p + positivePairValue q := by
  simp only [positivePairValue, positivePairAdd, PNat.add_coe, Nat.cast_add]
  ring


theorem positivePairValue_mul (p q : PositivePair) :
    positivePairValue (positivePairMul p q) = positivePairValue p * positivePairValue q := by
  simp only [positivePairValue, positivePairMul, PNat.add_coe, PNat.mul_coe,
    Nat.cast_add, Nat.cast_mul]
  ring

/-- Bài tập 1.4.22(e): phép cộng không phụ thuộc hai đại diện được chọn. -/
theorem positivePairAdd_respects (p p' q q' : PositivePair)
    (hp : positivePairRelation p p') (hq : positivePairRelation q q') :
    positivePairRelation (positivePairAdd p q) (positivePairAdd p' q') := by
  apply (positivePairRelation_iff_value_eq _ _).mpr
  rw [positivePairValue_add, positivePairValue_add,
    (positivePairRelation_iff_value_eq p p').mp hp,
    (positivePairRelation_iff_value_eq q q').mp hq]

/-- Bài tập 1.4.22(e): phép nhân không phụ thuộc hai đại diện được chọn. -/
theorem positivePairMul_respects (p p' q q' : PositivePair)
    (hp : positivePairRelation p p') (hq : positivePairRelation q q') :
    positivePairRelation (positivePairMul p q) (positivePairMul p' q') := by
  apply (positivePairRelation_iff_value_eq _ _).mpr
  rw [positivePairValue_mul, positivePairValue_mul,
    (positivePairRelation_iff_value_eq p p').mp hp,
    (positivePairRelation_iff_value_eq q q').mp hq]


def integerQuotientAdd : IntegerQuotient → IntegerQuotient → IntegerQuotient :=
  Quotient.map₂ positivePairAdd (fun {p p'} hp {q q'} hq ↦ positivePairAdd_respects p p' q q' hp hq)


def integerQuotientMul : IntegerQuotient → IntegerQuotient → IntegerQuotient :=
  Quotient.map₂ positivePairMul (fun {p p'} hp {q q'} hq ↦ positivePairMul_respects p p' q q' hp hq)


def integerQuotientValue : IntegerQuotient → ℤ :=
  Quotient.lift positivePairValue (fun p q h ↦ (positivePairRelation_iff_value_eq p q).mp h)


theorem integerQuotientValue_add (p q : IntegerQuotient) :
    integerQuotientValue (integerQuotientAdd p q) = integerQuotientValue p + integerQuotientValue q := by
  induction p, q using Quotient.inductionOn₂ with | _ p q =>
    exact positivePairValue_add p q


theorem integerQuotientValue_mul (p q : IntegerQuotient) :
    integerQuotientValue (integerQuotientMul p q) = integerQuotientValue p * integerQuotientValue q := by
  induction p, q using Quotient.inductionOn₂ with | _ p q =>
    exact positivePairValue_mul p q



theorem integerQuotientValue_injective : Function.Injective integerQuotientValue := by
  intro p q
  induction p, q using Quotient.inductionOn₂ with | _ p q =>
    intro h
    exact Quotient.sound ((positivePairRelation_iff_value_eq p q).mpr h)


theorem integerQuotientValue_surjective : Function.Surjective integerQuotientValue := by
  intro z
  let p : PositivePair := (⟨z.toNat + 1, by omega⟩, ⟨(-z).toNat + 1, by omega⟩)
  refine ⟨Quotient.mk positivePairSetoid p, ?_⟩
  change ((z.toNat + 1 : ℕ) : ℤ) - ((-z).toNat + 1 : ℕ) = z
  push_cast
  linarith [Int.toNat_sub_toNat_neg z]


noncomputable def integerQuotientEquiv : IntegerQuotient ≃ ℤ :=
  Equiv.ofBijective integerQuotientValue ⟨integerQuotientValue_injective, integerQuotientValue_surjective⟩

/-- Miền phân số trong Bài tập 1.4.23: mẫu nguyên khác 0, cho phép mẫu âm. -/
abbrev FractionPair := ℤ × {b : ℤ // b ≠ 0}

/-- Đại diện phân số (a,b), với b≠0. -/
def fractionPair (a b : ℤ) (hb : b ≠ 0) : FractionPair := (a, ⟨b, hb⟩)

/-- Bài tập 1.4.23: quan hệ ad=bc trên các cặp có mẫu khác 0. -/
def fractionPairRelation (p q : FractionPair) : Prop := p.1 * q.2.val = p.2.val * q.1

/-- Giá trị hữu tỉ a/b của đại diện (a,b). -/
def fractionPairValue (p : FractionPair) : ℚ := (p.1 : ℚ) / (p.2.val : ℚ)

/-- Hai phân số có mẫu khác 0 liên hệ khi và chỉ khi có cùng giá trị hữu tỉ. -/
theorem fractionPairRelation_iff_value_eq (p q : FractionPair) :
    fractionPairRelation p q ↔ fractionPairValue p = fractionPairValue q := by
  unfold fractionPairRelation fractionPairValue
  have hp : (p.2.val : ℚ) ≠ 0 := by exact_mod_cast p.2.property
  have hq : (q.2.val : ℚ) ≠ 0 := by exact_mod_cast q.2.property
  rw [div_eq_div_iff hp hq]
  rw [mul_comm (q.1 : ℚ) (p.2.val : ℚ)]
  norm_cast

/-- Bài tập 1.4.23(a): (1,5) cùng lớp với (−3,−15). -/
theorem fractionPair_first_example :
    fractionPairRelation (fractionPair 1 5 (by norm_num))
      (fractionPair (-3) (-15) (by norm_num)) := by
  norm_num [fractionPairRelation, fractionPair]

/-- Bài tập 1.4.23(b): (−1,1) không cùng lớp với(2,3). -/
theorem fractionPair_second_example :
    ¬ fractionPairRelation (fractionPair (-1) 1 (by norm_num))
      (fractionPair 2 3 (by norm_num)) := by
  norm_num [fractionPairRelation, fractionPair]

/-- Bài tập 1.4.23(c): quan hệ phân số là quan hệ tương đương trên miền có mẫu khác 0. -/
theorem fractionPairRelation_equivalence : Equivalence fractionPairRelation := by
  constructor
  · intro p
    exact (fractionPairRelation_iff_value_eq p p).mpr rfl
  · intro p q h
    exact (fractionPairRelation_iff_value_eq q p).mpr
      ((fractionPairRelation_iff_value_eq p q).mp h).symm
  · intro p q r hpq hqr
    exact (fractionPairRelation_iff_value_eq p r).mpr
      (((fractionPairRelation_iff_value_eq p q).mp hpq).trans
        ((fractionPairRelation_iff_value_eq q r).mp hqr))

/-- Bài tập 1.4.23(d): năm đại diện phân biệt của mỗi lớp đã cho. -/
theorem fractionPair_five_representatives :
    ([fractionPair 1 1 (by norm_num), fractionPair 2 2 (by norm_num),
      fractionPair 3 3 (by norm_num), fractionPair 4 4 (by norm_num),
      fractionPair 5 5 (by norm_num)].Nodup ∧
      ∀ p ∈ [fractionPair 1 1 (by norm_num), fractionPair 2 2 (by norm_num),
        fractionPair 3 3 (by norm_num), fractionPair 4 4 (by norm_num),
        fractionPair 5 5 (by norm_num)],
        p ∈ equivalenceClass fractionPairRelation (fractionPair 1 1 (by norm_num))) ∧
    ([fractionPair 0 1 (by norm_num), fractionPair 0 2 (by norm_num),
      fractionPair 0 3 (by norm_num), fractionPair 0 4 (by norm_num),
      fractionPair 0 5 (by norm_num)].Nodup ∧
      ∀ p ∈ [fractionPair 0 1 (by norm_num), fractionPair 0 2 (by norm_num),
        fractionPair 0 3 (by norm_num), fractionPair 0 4 (by norm_num),
        fractionPair 0 5 (by norm_num)],
        p ∈ equivalenceClass fractionPairRelation (fractionPair 0 2 (by norm_num))) ∧
    ([fractionPair 2 1 (by norm_num), fractionPair 4 2 (by norm_num),
      fractionPair 6 3 (by norm_num), fractionPair 8 4 (by norm_num),
      fractionPair 10 5 (by norm_num)].Nodup ∧
      ∀ p ∈ [fractionPair 2 1 (by norm_num), fractionPair 4 2 (by norm_num),
        fractionPair 6 3 (by norm_num), fractionPair 8 4 (by norm_num),
        fractionPair 10 5 (by norm_num)],
        p ∈ equivalenceClass fractionPairRelation (fractionPair 2 1 (by norm_num))) ∧
    ([fractionPair 2 3 (by norm_num), fractionPair 4 6 (by norm_num),
      fractionPair 6 9 (by norm_num), fractionPair 8 12 (by norm_num),
      fractionPair 10 15 (by norm_num)].Nodup ∧
      ∀ p ∈ [fractionPair 2 3 (by norm_num), fractionPair 4 6 (by norm_num),
        fractionPair 6 9 (by norm_num), fractionPair 8 12 (by norm_num),
        fractionPair 10 15 (by norm_num)],
        p ∈ equivalenceClass fractionPairRelation (fractionPair 2 3 (by norm_num))) := by
  norm_num [List.nodup_cons, equivalenceClass, fractionPairRelation, fractionPair]


def fractionPairSetoid : Setoid FractionPair where
  r := fractionPairRelation
  iseqv := fractionPairRelation_equivalence


abbrev RationalQuotient := Quotient fractionPairSetoid

/-- Tổng hai đại diện phân số: (ad+bc,bd), với bd≠0. -/
def fractionPairAdd (p q : FractionPair) : FractionPair :=
  (p.1 * q.2.val + p.2.val * q.1,
    ⟨p.2.val * q.2.val, mul_ne_zero p.2.property q.2.property⟩)

/-- Tích hai đại diện phân số: (ac,bd), với bd≠0. -/
def fractionPairMul (p q : FractionPair) : FractionPair :=
  (p.1 * q.1, ⟨p.2.val * q.2.val, mul_ne_zero p.2.property q.2.property⟩)


theorem fractionPairValue_add (p q : FractionPair) :
    fractionPairValue (fractionPairAdd p q) = fractionPairValue p + fractionPairValue q := by
  have hp : (p.2.val : ℚ) ≠ 0 := by exact_mod_cast p.2.property
  have hq : (q.2.val : ℚ) ≠ 0 := by exact_mod_cast q.2.property
  simp only [fractionPairValue, fractionPairAdd, Int.cast_add, Int.cast_mul]
  field_simp


theorem fractionPairValue_mul (p q : FractionPair) :
    fractionPairValue (fractionPairMul p q) = fractionPairValue p * fractionPairValue q := by
  simp only [fractionPairValue, fractionPairMul, Int.cast_mul]
  exact (div_mul_div_comm (p.1 : ℚ) (p.2.val : ℚ) (q.1 : ℚ) (q.2.val : ℚ)).symm

/-- Bài tập 1.4.23(e): phép cộng không phụ thuộc vào đại diện. -/
theorem fractionPairAdd_respects (p p' q q' : FractionPair)
    (hp : fractionPairRelation p p') (hq : fractionPairRelation q q') :
    fractionPairRelation (fractionPairAdd p q) (fractionPairAdd p' q') := by
  apply (fractionPairRelation_iff_value_eq _ _).mpr
  rw [fractionPairValue_add, fractionPairValue_add,
    (fractionPairRelation_iff_value_eq p p').mp hp,
    (fractionPairRelation_iff_value_eq q q').mp hq]

/-- Bài tập 1.4.23(e): phép nhân không phụ thuộc vào đại diện. -/
theorem fractionPairMul_respects (p p' q q' : FractionPair)
    (hp : fractionPairRelation p p') (hq : fractionPairRelation q q') :
    fractionPairRelation (fractionPairMul p q) (fractionPairMul p' q') := by
  apply (fractionPairRelation_iff_value_eq _ _).mpr
  rw [fractionPairValue_mul, fractionPairValue_mul,
    (fractionPairRelation_iff_value_eq p p').mp hp,
    (fractionPairRelation_iff_value_eq q q').mp hq]


def rationalQuotientAdd : RationalQuotient → RationalQuotient → RationalQuotient :=
  Quotient.map₂ fractionPairAdd
    (fun {p p'} hp {q q'} hq ↦ fractionPairAdd_respects p p' q q' hp hq)


def rationalQuotientMul : RationalQuotient → RationalQuotient → RationalQuotient :=
  Quotient.map₂ fractionPairMul
    (fun {p p'} hp {q q'} hq ↦ fractionPairMul_respects p p' q q' hp hq)


def rationalQuotientValue : RationalQuotient → ℚ :=
  Quotient.lift fractionPairValue (fun p q h ↦ (fractionPairRelation_iff_value_eq p q).mp h)


theorem rationalQuotientValue_add (p q : RationalQuotient) :
    rationalQuotientValue (rationalQuotientAdd p q) = rationalQuotientValue p + rationalQuotientValue q := by
  induction p, q using Quotient.inductionOn₂ with | _ p q =>
    exact fractionPairValue_add p q


theorem rationalQuotientValue_mul (p q : RationalQuotient) :
    rationalQuotientValue (rationalQuotientMul p q) = rationalQuotientValue p * rationalQuotientValue q := by
  induction p, q using Quotient.inductionOn₂ with | _ p q =>
    exact fractionPairValue_mul p q


theorem rationalQuotientValue_injective : Function.Injective rationalQuotientValue := by
  intro p q
  induction p, q using Quotient.inductionOn₂ with | _ p q =>
    intro h
    exact Quotient.sound ((fractionPairRelation_iff_value_eq p q).mpr h)


theorem rationalQuotientValue_surjective : Function.Surjective rationalQuotientValue := by
  intro q
  have hden : (q.den : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt q.den_pos)
  refine ⟨Quotient.mk fractionPairSetoid (fractionPair q.num q.den hden), ?_⟩
  change (q.num : ℚ) / ((q.den : ℤ) : ℚ) = q
  simpa using q.num_div_den


noncomputable def rationalQuotientEquiv : RationalQuotient ≃ ℚ :=
  Equiv.ofBijective rationalQuotientValue ⟨rationalQuotientValue_injective, rationalQuotientValue_surjective⟩


/-- Dòng 738: số âm ứng với a dương là nghiệm duy nhất của a+x=0. -/
theorem negative_integer_exists_unique (a : ℕ+) :
    ∃! x : ℤ, ((a : ℕ) : ℤ) + x = 0 ∧ x < 0 := by
  have ha : (0 : ℤ) < (a : ℕ) := by exact_mod_cast a.pos
  refine ⟨-((a : ℕ) : ℤ), ⟨by simp, by omega⟩, ?_⟩
  intro x hx
  omega

/-- Dòng 738–740: mọi số nguyên là 0, số tự nhiên dương, hoặc đối của số dương. -/
theorem integer_positive_zero_negative (z : ℤ) :
    z = 0 ∨ (∃ a : ℕ+, z = ((a : ℕ) : ℤ)) ∨
      ∃ a : ℕ+, z = -((a : ℕ) : ℤ) := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · right; right
    have hval : ((-z).toNat : ℤ) = -z := Int.toNat_of_nonneg (by omega)
    have hpos : 0 < (-z).toNat := by omega
    exact ⟨⟨(-z).toNat, hpos⟩, by simpa using congrArg Neg.neg hval.symm⟩
  · exact Or.inl hz
  · right; left
    have hval : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
    have hpos : 0 < z.toNat := by omega
    exact ⟨⟨z.toNat, hpos⟩, hval.symm⟩

/-- Dòng 741: a+x=b có thể vô nghiệm trong ℕ+; lấy a=b=1 thì x phải bằng 0. -/
theorem positive_natural_add_equation_not_solvable :
    ¬ ∃ x : ℕ+, (1 : ℕ+) + x = 1 := by
  rintro ⟨x, hx⟩
  have h := congrArg (fun y : ℕ+ ↦ (y : ℕ)) hx
  change 1 + (x : ℕ) = 1 at h
  have hxzero : (x : ℕ) = 0 := Nat.add_left_cancel (show 1 + (x : ℕ) = 1 + 0 from h)
  exact (Nat.ne_of_gt x.property) hxzero

/-- Dòng 741: a+x=b có nghiệm nguyên x=b−a với mọi a,b nguyên dương. -/
theorem integer_add_equation_solvable (a b : ℕ+) :
    ∃ x : ℤ, ((a : ℕ) : ℤ) + x = (b : ℕ) :=
  ⟨((b : ℕ) : ℤ) - (a : ℕ), by ring⟩

/-- Dòng 741: phương trình 2x=1 vô nghiệm nguyên. -/
theorem integer_division_not_always_solvable : ¬ ∃ x : ℤ, 2 * x = 1 := by omega

/-- Dòng 741: mọi bx=a với b nguyên khác 0 có nghiệm hữu tỉ duy nhất. -/
theorem rational_integer_division_exists_unique (a b : ℤ) (hb : b ≠ 0) :
    ∃! x : ℚ, (b : ℚ) * x = a := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  refine ⟨(a : ℚ) / b, ?_, ?_⟩
  · exact mul_div_cancel₀ (a : ℚ) hbq
  · intro x hx
    apply (eq_div_iff hbq).mpr
    simpa [mul_comm] using hx

/-- Dòng 744: thương và dư nguyên duy nhất với 0≤r<|b|, cho phép b âm. -/
theorem integer_euclidean_division (a b : ℤ) (hb : b ≠ 0) :
    ∃! qr : ℤ × ℤ, a = b * qr.1 + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < |b| := by
  refine ⟨(a / b, a % b), ?_, ?_⟩
  · exact ⟨by simpa [mul_comm] using (Int.ediv_mul_add_emod a b).symm,
      Int.emod_nonneg a hb, Int.emod_lt_abs a hb⟩
  · rintro ⟨q, r⟩ ⟨h, hr0, hrb⟩
    dsimp at h
    apply Prod.ext
    all_goals
      have heq : r + b * q = a := by omega
      rcases lt_or_gt_of_ne hb with hb | hb
      · have hr : r < -b := by simpa [abs_of_neg hb] using hrb
        have hqr := (Int.ediv_emod_unique' hb).mpr ⟨heq, hr0, hr⟩
        first | exact hqr.1.symm | exact hqr.2.symm
      · have hr : r < b := by simpa [abs_of_pos hb] using hrb
        have hqr := (Int.ediv_emod_unique hb).mpr ⟨heq, hr0, hr⟩
        first | exact hqr.1.symm | exact hqr.2.symm

/-- Dòng 755–758: bằng nhau của phân số hữu tỉ tương đương tích chéo bằng nhau. -/
theorem rational_fraction_eq_iff (a b c d : ℤ) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℚ) / b = (c : ℚ) / d ↔ a * d = b * c := by
  exact (fractionPairRelation_iff_value_eq (fractionPair a b hb) (fractionPair c d hd)).symm

/-- Dòng 760: nhân cả tử và mẫu của −3/4 với cùng một số nguyên dương. -/
theorem scaled_negative_three_fourths (n : ℕ+) :
    (-3 : ℚ) / 4 = (-3 * (n : ℕ)) / (4 * (n : ℕ)) := by
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
  field_simp

/-- Dòng 761–762: mỗi số hữu tỉ có biểu diễn với mẫu dương, tử và mẫu nguyên tố cùng nhau. -/
theorem rational_reduced_positive_denominator (q : ℚ) :
    ∃ a : ℤ, ∃ b : ℕ+, q = (a : ℚ) / (b : ℕ) ∧ a.natAbs.Coprime (b : ℕ) := by
  exact ⟨q.num, ⟨q.den, q.den_pos⟩, q.num_div_den.symm, q.reduced⟩

/-- Dòng 742: các phân số có mẫu nguyên khác 0 biểu diễn mọi hữu tỉ. -/
theorem rational_fraction_representation (q : ℚ) :
    ∃ a b : ℤ, b ≠ 0 ∧ q = (a : ℚ) / b := by
  have hb : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  refine ⟨q.num, q.den, hb, ?_⟩
  simpa using q.num_div_den.symm

/-- Dòng 792–794: thứ tự phân số khi hai mẫu tự nhiên dương. -/
theorem rational_fraction_gt_iff (a c : ℤ) (b d : ℕ+) :
    (a : ℚ) / (b : ℕ) > (c : ℚ) / (d : ℕ) ↔
      a * ((d : ℕ) : ℤ) > ((b : ℕ) : ℤ) * c := by
  have hb : (0 : ℚ) < (b : ℕ) := by exact_mod_cast b.pos
  have hd : (0 : ℚ) < (d : ℕ) := by exact_mod_cast d.pos
  change (c : ℚ) / (d : ℕ) < (a : ℚ) / (b : ℕ) ↔
    ((b : ℕ) : ℤ) * c < a * ((d : ℕ) : ℤ)
  rw [div_lt_div_iff₀ hd hb, mul_comm (c : ℚ) ((b : ℕ) : ℚ)]
  norm_cast

/-- Dòng 1004: phủ định “mọi bình phương không âm” là tồn tại bình phương âm. -/
theorem not_all_squares_nonnegative_iff :
    ¬ (∀ x : ℝ, 0 ≤ x ^ 2) ↔ ∃ x : ℝ, x ^ 2 < 0 := by
  classical
  simp only [not_forall, not_le]

/-- Dòng 1014–1017: 2+3≠0 bác bỏ khẳng định tổng mọi cặp số nguyên bằng 0. -/
theorem not_all_integer_pair_sums_zero :
    ¬ (∀ x y : ℤ, x + y = 0) ∧ (2 : ℤ) + 3 ≠ 0 := by
  constructor
  · intro h
    have h23 := h 2 3
    norm_num at h23
  · norm_num

/-- Dòng 1020: mọi số nguyên đều có số đối. -/
theorem every_integer_has_additive_opposite : ∀ x : ℤ, ∃ y : ℤ, x + y = 0 := by
  intro x
  exact ⟨-x, by simp⟩

/-- Dòng 1023: không có số nguyên cộng với mọi y để được 0. -/
theorem no_integer_common_additive_opposite : ¬ ∃ x : ℤ, ∀ y : ℤ, x + y = 0 := by
  rintro ⟨x, hx⟩
  have h0 := hx 0
  have h1 := hx 1
  omega

/-- Dòng 1026: nhân chứng cụ thể 1 và −1 cho hai lượng từ tồn tại. -/
theorem exists_integer_pair_sum_zero : ∃ x y : ℤ, x + y = 0 := ⟨1, -1, by norm_num⟩

/-- Dòng 1029–1030: hai lượng từ cùng loại có thể đổi chỗ. -/
theorem forall_integer_pair_sum_zero_swap :
    (∀ x y : ℤ, x + y = 0) ↔ ∀ y x : ℤ, x + y = 0 := forall_comm

/-- Dòng 1037–1038: phủ định mệnh đề có hai loại lượng từ. -/
theorem not_every_integer_has_opposite_iff :
    ¬ (∀ x : ℤ, ∃ y : ℤ, x + y = 0) ↔ ∃ x : ℤ, ∀ y : ℤ, x + y ≠ 0 := by
  classical
  simp only [not_forall, not_exists]

/-- Dòng 1040–1042: phủ định công thức ε–δ cho căn bậc hai. -/
theorem sqrt_continuity_predicate_negation (D : Set ℝ) (x₀ : ℝ) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ D → |x - x₀| < δ → |Real.sqrt x - Real.sqrt x₀| < ε) ↔
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ x : ℝ, x ∈ D ∧ |x - x₀| < δ ∧ ε ≤ |Real.sqrt x - Real.sqrt x₀| := by
  classical
  push Not
  rfl

/-- Dòng 1043: phủ định phép kéo theo là tiền đề đúng và kết luận sai. -/
theorem not_implication_iff (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q := by
  classical
  exact Classical.not_imp

/-- Dòng 1101: tập đơn có một phần tử; tập {a,b} có một hay hai phần tử tùy a=b hay a≠b. -/
theorem singleton_pair_cardinality {α : Type*} (a b : α) :
    ({a} : Set α).ncard = 1 ∧
      (a = b → ({a, b} : Set α).ncard = 1) ∧
      (a ≠ b → ({a, b} : Set α).ncard = 2) := by
  refine ⟨by simp, ?_, fun h ↦ Set.ncard_pair h⟩
  intro h
  subst b
  simp


/-- Dòng 749: đặc trưng số nguyên tố trên các số tự nhiên dương. -/
theorem positive_prime_criterion (p : ℕ+) :
    Nat.Prime (p : ℕ) ↔ 1 < (p : ℕ) ∧
      ∀ d : ℕ+, (d : ℕ) ∣ (p : ℕ) → d = 1 ∨ d = p := by
  constructor
  · intro hp
    refine ⟨hp.one_lt, ?_⟩
    intro d hd
    rcases hp.eq_one_or_self_of_dvd (d : ℕ) hd with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro ⟨hp, hdiv⟩
    apply Nat.prime_def.mpr
    refine ⟨by omega, ?_⟩
    intro d hd
    rcases Nat.eq_zero_or_pos d with h | h
    · subst d
      simp only [zero_dvd_iff] at hd
      omega
    · rcases hdiv ⟨d, h⟩ hd with hd | hd
      · exact Or.inl (congrArg (fun x : ℕ+ ↦ (x : ℕ)) hd)
      · exact Or.inr (congrArg (fun x : ℕ+ ↦ (x : ℕ)) hd)

/-- Dòng 744–746: chia hết khi và chỉ khi dư 0, với số chia khác 0. -/
theorem integer_divisible_iff_remainder_zero (a b : ℤ) (_hb : b ≠ 0) :
    b ∣ a ↔ a % b = 0 := Int.dvd_iff_emod_eq_zero

/-- Dòng 796: khoảng mở giữa hai số nguyên chỉ chứa hữu hạn số nguyên. -/
theorem integers_between_finite (a b : ℤ) : ({x : ℤ | a < x ∧ x < b} : Set ℤ).Finite :=
  Set.finite_Ioo a b

/-- Dòng 854: tổng, hiệu, tích và thương với mẫu khác 0 của hai số hữu tỉ đều hữu tỉ. -/
theorem rational_operations_real_representations (q r : ℚ) (_hr : r ≠ 0) :
    (∃ s : ℚ, (s : ℝ) = (q : ℝ) + r) ∧
    (∃ s : ℚ, (s : ℝ) = (q : ℝ) - r) ∧
    (∃ s : ℚ, (s : ℝ) = (q : ℝ) * r) ∧
    ∃ s : ℚ, (s : ℝ) = (q : ℝ) / r := by
  exact ⟨⟨q + r, by push_cast; rfl⟩, ⟨q - r, by push_cast; rfl⟩,
    ⟨q * r, by push_cast; rfl⟩, ⟨q / r, by push_cast; rfl⟩⟩

/-- Dòng 854: q↦q+√2 tạo số vô tỉ với từng q hữu tỉ. -/
noncomputable def rationalToIrrational (q : ℚ) : {x : ℝ // Irrational x} :=
  ⟨(q : ℝ) + Real.sqrt 2, irrational_sqrt_two.ratCast_add q⟩

/-- Dòng 854: hai hữu tỉ khác nhau tạo hai số vô tỉ khác nhau. -/
theorem rationalToIrrational_injective : Function.Injective rationalToIrrational := by
  intro q r h
  have hval := congrArg Subtype.val h
  change (q : ℝ) + Real.sqrt 2 = (r : ℝ) + Real.sqrt 2 at hval
  exact_mod_cast add_right_cancel hval

/-- Dòng 854: tập các số vô tỉ không đếm được. -/
theorem irrational_set_uncountable : ¬ ({x : ℝ | Irrational x} : Set ℝ).Countable := by
  intro h
  have hq : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have hcover : Set.range ((↑) : ℚ → ℝ) ∪ {x : ℝ | Irrational x} = Set.univ := by
    classical
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, Irrational]
    exact iff_true_intro (Classical.em _)
  have hreal := hq.union h
  rw [hcover] at hreal
  exact Cardinal.not_countable_real hreal

/-- Dòng 854: so sánh lực lượng của tập số hữu tỉ và tập số vô tỉ. -/
theorem irrational_cardinality_gt_rational :
    Cardinal.mk ℚ < Cardinal.mk {x : ℝ // Irrational x} := by
  rw [Cardinal.mkRat]
  exact lt_of_not_ge fun h ↦ irrational_set_uncountable
    (Cardinal.le_aleph0_iff_set_countable.mp h)

/-- Tổng chuỗi hình học bắt đầu từ lũy thừa 1. -/
lemma geometric_sum_from_one (r : ℝ) (hr : |r| < 1) :
    Summable (fun k : ℕ ↦ r ^ (k + 1)) ∧
      (∑' k : ℕ, r ^ (k + 1)) = r / (1 - r) := by
  constructor
  · simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one hr).mul_left r
  · simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hr, div_eq_mul_inv]

/-- Giá trị của khối d chữ số lặp ở các vị trí d,2d,3d,…; có thể thêm chữ số 0 ở đầu khối. -/
noncomputable def repeatingBlockValue (block : ℕ) (digits : ℕ+) : ℝ :=
  (block : ℝ) * ∑' k : ℕ, 1 / (10 : ℝ) ^ ((digits : ℕ) * (k + 1))


lemma repeatingBlockValue_as_geometric (block : ℕ) (digits : ℕ+) :
    repeatingBlockValue block digits =
      (block : ℝ) * ∑' k : ℕ, (1 / (10 : ℝ) ^ (digits : ℕ)) ^ (k + 1) := by
  unfold repeatingBlockValue
  congr 1
  apply tsum_congr
  intro k
  rw [pow_mul, one_div_pow]


lemma decimal_ratio_abs_lt_one (digits : ℕ+) : |1 / (10 : ℝ) ^ (digits : ℕ)| < 1 := by
  have hpow : (1 : ℝ) < 10 ^ (digits : ℕ) :=
    one_lt_pow₀ (by norm_num) digits.ne_zero
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / 10 ^ (digits : ℕ))]
  exact (div_lt_one (by positivity : (0 : ℝ) < 10 ^ (digits : ℕ))).mpr hpow

/-- Công thức phân số của một khối thập phân tuần hoàn. -/
theorem repeatingBlockValue_eq_fraction (block : ℕ) (digits : ℕ+) :
    repeatingBlockValue block digits = (block : ℝ) / ((10 : ℝ) ^ (digits : ℕ) - 1) := by
  rw [repeatingBlockValue_as_geometric,
    (geometric_sum_from_one _ (decimal_ratio_abs_lt_one digits)).2]
  have hpow : (1 : ℝ) < 10 ^ (digits : ℕ) :=
    one_lt_pow₀ (by norm_num) digits.ne_zero
  have hne : (10 : ℝ) ^ (digits : ℕ) - 1 ≠ 0 := by linarith
  have hne' : 1 - 1 / (10 : ℝ) ^ (digits : ℕ) ≠ 0 := by
    have hlt := decimal_ratio_abs_lt_one digits
    have hpos : (0 : ℝ) < 1 / 10 ^ (digits : ℕ) := by positivity
    rw [abs_of_pos hpos] at hlt
    linarith
  field_simp

/-- Dòng 766–772: giá trị các thập phân hữu hạn và hai khối tuần hoàn. -/
theorem decimal_fraction_examples :
    (1 : ℝ) / 2 = 5 / 10 ∧ (1 : ℝ) / 5 = 2 / 10 ∧
    (1 : ℝ) / 20 = 1 / (2 ^ 2 * 5) ∧
    (1 : ℝ) / 20 = (1 / 2) * (1 / 2) * (1 / 5) ∧
    (1 : ℝ) / 20 = (5 / 10) ^ 2 * (2 / 10) ∧
    repeatingBlockValue 3 1 = 1 / 3 ∧ repeatingBlockValue 142857 6 = 1 / 7 := by
  norm_num [repeatingBlockValue_eq_fraction]

/-- Dòng 779: mọi thập phân hữu hạn a/10^k là hữu tỉ, gồm a nguyên âm. -/
theorem finite_decimal_is_rational (a : ℤ) (k : ℕ) :
    ∃ q : ℚ, (q : ℝ) = (a : ℝ) / (10 : ℝ) ^ k := by
  exact ⟨(a : ℚ) / 10 ^ k, by push_cast; rfl⟩

/-- Dòng 779: hai ví dụ đổi thập phân hữu hạn thành phân số. -/
theorem finite_decimal_conversion_examples :
    (12 : ℝ) / 10 = 6 / 5 ∧ (12345 : ℝ) / 1000 = 2469 / 200 := by norm_num

/-- Dòng 780–782: 1,(23) là 1 cộng khối 23 lặp ở các vị trí 2,4,6,… -/
theorem repeating_twenty_three_conversion :
    1 + repeatingBlockValue 23 2 = 1 + (23 : ℝ) / 99 ∧
      1 + (23 : ℝ) / 99 = 122 / 99 := by
  norm_num [repeatingBlockValue_eq_fraction]

/-- Giá trị thập phân có phần đầu hữu hạn và một khối lặp; `prefixLength=0` khi không có phần đầu. -/
noncomputable def eventuallyPeriodicDecimalValue (integerPart : ℤ) (leadingDigits prefixLength : ℕ)
    (block : ℕ) (blockLength : ℕ+) : ℝ :=
  (integerPart : ℝ) + (leadingDigits : ℝ) / (10 : ℝ) ^ prefixLength +
    repeatingBlockValue block blockLength / (10 : ℝ) ^ prefixLength

/-- Dòng 783,788: biểu diễn thập phân có phần đầu và khối lặp có một giá trị hữu tỉ. -/
theorem eventually_periodic_decimal_is_rational (integerPart : ℤ) (leadingDigits prefixLength : ℕ)
    (block : ℕ) (blockLength : ℕ+) :
    ∃ q : ℚ, (q : ℝ) =
      eventuallyPeriodicDecimalValue integerPart leadingDigits prefixLength block blockLength := by
  refine ⟨(integerPart : ℚ) + (leadingDigits : ℚ) / 10 ^ prefixLength +
    ((block : ℚ) / (10 ^ (blockLength : ℕ) - 1)) / 10 ^ prefixLength, ?_⟩
  unfold eventuallyPeriodicDecimalValue
  rw [repeatingBlockValue_eq_fraction]
  push_cast
  rfl

/-- Dòng 784–787: phần đầu 1,23 và khối 4567 bắt đầu sau hai vị trí thập phân. -/
theorem eventually_periodic_decimal_conversion_example :
    eventuallyPeriodicDecimalValue 1 23 2 4567 4 =
      (123 : ℝ) / 100 + (1 / 100) * (4567 / 9999) := by
  unfold eventuallyPeriodicDecimalValue
  norm_num [repeatingBlockValue_eq_fraction]


/-- Dòng 850: các điểm x²=2 trên trục số không có tọa độ hữu tỉ. -/
theorem irrational_of_square_eq_two (x : ℝ) (hx : x ^ 2 = 2) :
    Irrational x := by
  rintro ⟨q, rfl⟩
  have hq : q ^ 2 = 2 := by exact_mod_cast hx
  exact calculus.Chapter01.Section04Exercises.rational_square_ne_two q hq

/-- Bài tập 1.4.20: họ lớp tương đương có đúng hai phần tử. -/
theorem integerSquareModFour_quotient_ncard :
    (range (equivalenceClass integerSquareModFour)).ncard = 2 := by
  rw [integerSquareModFour_quotient_classes]
  apply Set.ncard_pair
  intro h
  have hzero : (0 : ℤ) ∈ ({x : ℤ | Even x} : Set ℤ) := by norm_num
  rw [h] at hzero
  norm_num at hzero


/-- Dòng 745–746: `Int.gcd` có giá trị tự nhiên dương khi b≠0. -/
theorem integer_gcd_greatest_positive_common_divisor (a b : ℤ) (hb : b ≠ 0) :
    0 < Int.gcd a b ∧ ((Int.gcd a b : ℕ) : ℤ) ∣ a ∧
      ((Int.gcd a b : ℕ) : ℤ) ∣ b ∧
      ∀ d : ℕ+, ((d : ℕ) : ℤ) ∣ a → ((d : ℕ) : ℤ) ∣ b →
        (d : ℕ) ≤ Int.gcd a b := by
  have hpos := Int.gcd_pos_of_ne_zero_right a hb
  refine ⟨hpos, Int.gcd_dvd_left a b, Int.gcd_dvd_right a b, ?_⟩
  intro d ha hb
  exact Nat.le_of_dvd hpos (Int.dvd_gcd ha hb)

end calculus.Chapter01.Section04Remaining
