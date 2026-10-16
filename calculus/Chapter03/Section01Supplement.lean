import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.PNat.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# 3.1. Căn bậc ba và Bài tập 11

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 145–147, 265–273.
-/

namespace calculus.Chapter03.Section01Supplement

open Set Function
open scoped NNReal


theorem real_cube_exists (x : ℝ) : ∃ y : ℝ, y^3 = x := by
  by_cases hx : 0 ≤ x
  · let y := (NNReal.powOrderIso 3 (by norm_num)).symm ⟨x,hx⟩
    have h := (NNReal.powOrderIso 3 (by norm_num)).apply_symm_apply ⟨x,hx⟩
    change y^3 = (⟨x,hx⟩ : ℝ≥0) at h
    have hr := congrArg (fun z : ℝ≥0 => (z:ℝ)) h
    change (y:ℝ)^3 = x at hr
    exact ⟨(y:ℝ), hr⟩
  · have hx' : 0 ≤ -x := by linarith
    let y := (NNReal.powOrderIso 3 (by norm_num)).symm ⟨-x,hx'⟩
    have h := (NNReal.powOrderIso 3 (by norm_num)).apply_symm_apply ⟨-x,hx'⟩
    change y^3 = (⟨-x,hx'⟩ : ℝ≥0) at h
    have hr := congrArg (fun z : ℝ≥0 => (z:ℝ)) h
    change (y:ℝ)^3 = -x at hr
    refine ⟨-(y:ℝ), ?_⟩
    nlinarith


noncomputable def realCubeRoot (x : ℝ) : ℝ := Classical.choose (real_cube_exists x)


theorem real_cube_root_cube (x : ℝ) : (realCubeRoot x)^3 = x := Classical.choose_spec (real_cube_exists x)


theorem real_cube_root_unique (x y : ℝ) (hy : y^3 = x) : y = realCubeRoot x :=
  (show Odd 3 by decide).pow_injective (hy.trans (real_cube_root_cube x).symm)


theorem real_cube_root_of_cube (x : ℝ) : realCubeRoot (x^3) = x :=
  (real_cube_root_unique (x^3) x rfl).symm

/-- Ví dụ hàm bậc ba: nghịch đảo của x↦2x³−1 là y↦∛((y+1)/2). -/
theorem affine_cubic_inverse_formulas (x : ℝ) :
    2*(realCubeRoot ((x+1)/2))^3-1 = x ∧
      realCubeRoot (((2*x^3-1)+1)/2) = x := by
  constructor
  · rw [real_cube_root_cube]
    ring
  · rw [show (((2*x^3-1)+1)/2) = x^3 by ring, real_cube_root_of_cube]


theorem affine_cubic_bijective : Bijective (fun x : ℝ => 2*x^3-1) := by
  constructor
  · intro x y h
    change 2*x^3-1 = 2*y^3-1 at h
    have hx := (affine_cubic_inverse_formulas x).2
    have hy := (affine_cubic_inverse_formulas y).2
    rw [h] at hx
    exact hx.symm.trans hy
  · intro y
    exact ⟨realCubeRoot ((y+1)/2), (affine_cubic_inverse_formulas y).1⟩

/-- Bài tập 11(a): x³+x−1 tăng ngặt trên ℝ. -/
theorem cubic_plus_linear_strictMono : StrictMono (fun x : ℝ => x^3+x-1) := by
  intro x y hxy
  have hp := (show Odd 3 by decide).strictMono_pow hxy
  dsimp
  linarith


theorem cubic_plus_linear_surjective : Surjective (fun x : ℝ => x^3+x-1) := by
  intro y
  let m := |y|+2
  have hm : 2 ≤ m := by dsimp [m]; linarith [abs_nonneg y]
  have hc : m ≤ m^3 := by
    have hs : 0 ≤ m^2-1 := by nlinarith
    have hh := mul_nonneg (show 0 ≤ m by linarith) hs
    nlinarith
  have hleft : (-m)^3+(-m)-1 ≤ y := by
    have hy := neg_abs_le y
    dsimp [m] at hm hc ⊢
    nlinarith
  have hright : y ≤ m^3+m-1 := by
    have hy := le_abs_self y
    dsimp [m] at hm hc ⊢
    nlinarith
  have hcont : Continuous (fun x : ℝ => x^3+x-1) := by fun_prop
  exact mem_range_of_exists_le_of_exists_ge hcont ⟨-m,hleft⟩ ⟨m,hright⟩

/-- Bài tập 11(a): hàm có hàm ngược trên ℝ. -/
theorem cubic_plus_linear_bijective : Bijective (fun x : ℝ => x^3+x-1) :=
  ⟨cubic_plus_linear_strictMono.injective, cubic_plus_linear_surjective⟩


theorem cubic_minus_linear_not_injective : ¬Injective (fun x : ℝ => x^3-x+1) := by
  intro h
  have hh := h (a₁ := 0) (a₂ := 1) (by norm_num)
  norm_num at hh

/-- Bài tập 11(b): hàm không song ánh. -/
theorem cubic_minus_linear_not_bijective : ¬Bijective (fun x : ℝ => x^3-x+1) :=
  fun h => cubic_minus_linear_not_injective h.1


theorem restricted_sine_not_injective :
    ¬Injective (fun x : Set.Icc (0:ℝ) (2*Real.pi) => Real.sin (x:ℝ)) := by
  intro h
  let a : Set.Icc (0:ℝ) (2*Real.pi) := ⟨0,⟨le_rfl, by positivity⟩⟩
  let b : Set.Icc (0:ℝ) (2*Real.pi) := ⟨2*Real.pi,⟨by positivity, le_rfl⟩⟩
  have he : Real.sin (a:ℝ) = Real.sin (b:ℝ) := by simp [a,b]
  have hab := congrArg (fun x : Set.Icc (0:ℝ) (2*Real.pi) => (x:ℝ)) (h he)
  dsimp [a,b] at hab
  have hp := Real.pi_pos
  linarith

/-- Bài tập 11(c): hàm không song ánh trên [0,2π]. -/
theorem restricted_sine_not_bijective :
    ¬Bijective (fun x : Set.Icc (0:ℝ) (2*Real.pi) => Real.sin (x:ℝ)) :=
  fun h => restricted_sine_not_injective h.1


def integerNegEquiv : ℤ ≃ ℤ where
  toFun z := -z
  invFun z := -z
  left_inv := neg_neg
  right_inv := neg_neg


def positiveIntegerEnumerationEquiv : ℕ+ ≃ ℤ :=
  (Equiv.pnatEquivNat.trans Equiv.intEquivNat.symm).trans integerNegEquiv


def integerEnumerationFormula (n : ℕ+) : ℤ :=
  ((-1:ℤ)^(n:ℕ)*(2*(n:ℤ)-1)+1)/4


theorem integer_enumeration_numerator (n : ℕ+) :
    (-1:ℤ)^(n:ℕ)*(2*(n:ℤ)-1)+1 = 4*positiveIntegerEnumerationEquiv n := by
  have hpred : n.natPred+1 = (n:ℕ) := by
    exact congrArg PNat.val (PNat.succPNat_natPred n)
  have henc := Equiv.intEquivNat.apply_symm_apply n.natPred
  cases he : Equiv.intEquivNat.symm n.natPred with
  | ofNat k =>
    rw [he] at henc
    change 2*k = n.natPred at henc
    have hn : (n:ℕ) = 2*k+1 := by omega
    change (-1:ℤ)^(n:ℕ)*(2*(n:ℤ)-1)+1 = 4*(-Equiv.intEquivNat.symm n.natPred)
    rw [he, hn]
    norm_num [pow_add,pow_mul]
    ring
  | negSucc k =>
    rw [he] at henc
    change 2*k+1 = n.natPred at henc
    have hn : (n:ℕ) = 2*k+2 := by omega
    change (-1:ℤ)^(n:ℕ)*(2*(n:ℤ)-1)+1 = 4*(-Equiv.intEquivNat.symm n.natPred)
    rw [he, hn]
    norm_num [pow_add,pow_mul]
    ring


theorem integer_enumeration_formula_eq (n : ℕ+) :
    integerEnumerationFormula n = positiveIntegerEnumerationEquiv n := by
  unfold integerEnumerationFormula
  rw [integer_enumeration_numerator]
  omega


theorem integer_enumeration_real_formula (n : ℕ+) :
    (integerEnumerationFormula n : ℝ) =
      ((-1:ℝ)^(n:ℕ)*(2*(n:ℝ)-1)+1)/4 := by
  rw [integer_enumeration_formula_eq]
  have hreal : (-1:ℝ)^(n:ℕ)*(2*(n:ℝ)-1)+1 =
      4*(positiveIntegerEnumerationEquiv n : ℝ) := by
    exact_mod_cast integer_enumeration_numerator n
  linarith

/-- Bài tập 11(d): công thức cho một song ánh từ ℕ+ vào ℤ. -/
theorem integer_enumeration_bijective : Bijective integerEnumerationFormula := by
  have he : integerEnumerationFormula = positiveIntegerEnumerationEquiv :=
    funext integer_enumeration_formula_eq
  rw [he]
  exact positiveIntegerEnumerationEquiv.bijective

end calculus.Chapter03.Section01Supplement
