import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# 4.1. Bảng đạo hàm các hàm sơ cấp

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 270–315.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01ElementaryDerivatives
open Filter
open scoped Topology

/-- Hàm sec, xét trên miền `cos x ≠ 0`. -/
def sec (x : ℝ) : ℝ := 1 / Real.cos x
/-- Hàm csc, xét trên miền `sin x ≠ 0`. -/
def csc (x : ℝ) : ℝ := 1 / Real.sin x

def sech (x : ℝ) : ℝ := 1 / Real.cosh x
/-- Hàm csch, xét trên miền `x ≠ 0`. -/
def csch (x : ℝ) : ℝ := 1 / Real.sinh x
/-- Hàm coth, xét trên miền `x ≠ 0`. -/
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x
/-- Nhánh arccot có giá trị trong `(0, π)`. -/
def arccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x
/-- Nhánh arcsec trên `|x| ≥ 1`, có giá trị trong `[0, π] \ {π/2}`. -/
def arcsec (x : ℝ) : ℝ := Real.arccos (1 / x)
/-- Nhánh arccsc trên `|x| ≥ 1`, có giá trị trong `[-π/2, π/2] \ {0}`. -/
def arccsc (x : ℝ) : ℝ := Real.arcsin (1 / x)
/-- Nhánh hàm ngược của sech trên `0 < x ≤ 1`. -/
def arsech (x : ℝ) : ℝ := Real.arcosh (1 / x)
/-- Nhánh hàm ngược của csch trên `x ≠ 0`. -/
def arcsch (x : ℝ) : ℝ := Real.arsinh (1 / x)
/-- Nhánh hàm ngược của coth trên `|x| > 1`. -/
def arcoth (x : ℝ) : ℝ := 1 / 2 * Real.log ((x + 1) / (x - 1))

/-- Bảng (1): đạo hàm hằng số. -/
theorem hasDerivAt_constant (C x : ℝ) : HasDerivAt (fun _ : ℝ ↦ C) 0 x :=
  hasDerivAt_const x C

/-- Bảng (2): đạo hàm lũy thừa thực trên miền cơ số dương. -/
theorem hasDerivAt_real_power (α x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ t ^ α) (α * x ^ (α - 1)) x :=
  Real.hasDerivAt_rpow_const (Or.inl hx.ne')

/-- Bảng (2): đạo hàm lũy thừa với số mũ nguyên dương trên ℝ. -/
theorem hasDerivAt_natural_power (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ t ^ n) ((n : ℝ) * x ^ (n - 1)) x :=
  hasDerivAt_pow n x

/-- Bảng (2): đạo hàm lũy thừa với số mũ nguyên không dương, trên `x ≠ 0`. -/
theorem hasDerivAt_integer_power (k : ℤ) (_hk : k ≤ 0) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ t ^ k) ((k : ℝ) * x ^ (k - 1)) x :=
  hasDerivAt_zpow k x (Or.inl hx)

/-- Bảng (3): đạo hàm hàm mũ có cơ số `a > 0`, `a ≠ 1`. -/
theorem hasDerivAt_exponential (a x : ℝ) (ha : 0 < a) (_ha1 : a ≠ 1) :
    HasDerivAt (fun t : ℝ ↦ a ^ t) (a ^ x * Real.log a) x := by
  simpa only [mul_one, one_mul, mul_comm, id_eq] using (hasDerivAt_id x).const_rpow ha

/-- Bảng (4): logarit theo cơ số trên miền `x > 0`. -/
theorem hasDerivAt_logarithm (a x : ℝ) (_ha : 0 < a) (_ha1 : a ≠ 1) (hx : 0 < x) :
    HasDerivAt (Real.logb a) (1 / (x * Real.log a)) x := by
  change HasDerivAt (fun t : ℝ ↦ Real.log t / Real.log a) _ x
  simpa [div_eq_mul_inv, mul_inv, mul_comm] using (Real.hasDerivAt_log hx.ne').div_const (Real.log a)

/-- Bảng (5): đạo hàm của sin. -/
theorem hasDerivAt_sine (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
/-- Bảng (6): đạo hàm của cos. -/
theorem hasDerivAt_cosine (x : ℝ) : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x

/-- Bảng (7): đạo hàm của sec khi `cos x ≠ 0`. -/
theorem hasDerivAt_secant (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt sec (sec x * Real.tan x) x := by
  have h : HasDerivAt sec (-(-Real.sin x) / Real.cos x ^ 2) x :=
    ((Real.hasDerivAt_cos x).inv hc).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ by simp [sec])
  apply h.congr_deriv
  simp [sec, Real.tan_eq_sin_div_cos]
  ring

/-- Bảng (8): đạo hàm của csc khi `sin x ≠ 0`. -/
theorem hasDerivAt_cosecant (x : ℝ) (hs : Real.sin x ≠ 0) :
    HasDerivAt csc (-csc x * Real.cot x) x := by
  have h : HasDerivAt csc (-Real.cos x / Real.sin x ^ 2) x :=
    ((Real.hasDerivAt_sin x).inv hs).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ by simp [csc])
  apply h.congr_deriv
  simp [csc, Real.cot_eq_cos_div_sin]
  ring

/-- Bảng (9): ba biểu thức của đạo hàm tan. -/
theorem tangent_derivative_forms (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 / Real.cos x ^ 2) x ∧
      1 / Real.cos x ^ 2 = 1 + Real.tan x ^ 2 ∧
      1 + Real.tan x ^ 2 = sec x ^ 2 := by
  refine ⟨Real.hasDerivAt_tan hc, ?_, ?_⟩
  · rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  · rw [Real.tan_eq_sin_div_cos]
    unfold sec
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]

/-- Bảng (10): đạo hàm cot bằng `−1/sin²x`. -/
theorem hasDerivAt_cotangent (x : ℝ) (hs : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(1 / Real.sin x ^ 2)) x := by
  have h : HasDerivAt Real.cot
      ((-Real.sin x * Real.sin x - Real.cos x * Real.cos x) / Real.sin x ^ 2) x :=
    ((Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hs).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ Real.cot_eq_cos_div_sin t)
  apply h.congr_deriv
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- Bảng (10): ba biểu thức của đạo hàm cot. -/
theorem cotangent_derivative_forms (x : ℝ) (hs : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(1 / Real.sin x ^ 2)) x ∧
      -(1 / Real.sin x ^ 2) = -(1 + Real.cot x ^ 2) ∧
      -(1 + Real.cot x ^ 2) = -(csc x ^ 2) := by
  refine ⟨hasDerivAt_cotangent x hs, ?_, ?_⟩
  · rw [Real.cot_eq_cos_div_sin]
    field_simp
    nlinarith [Real.cos_sq_add_sin_sq x]
  · rw [Real.cot_eq_cos_div_sin]
    unfold csc
    field_simp
    nlinarith [Real.cos_sq_add_sin_sq x]

/-- Bảng (11): đạo hàm của arcsin trên `(-1, 1)`. -/
theorem hasDerivAt_arcsine (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.arcsin (1 / √(1 - x ^ 2)) x :=
  Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])
/-- Bảng (12): đạo hàm của arccos trên `(-1, 1)`. -/
theorem hasDerivAt_arccosine (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.arccos (-(1 / √(1 - x ^ 2))) x :=
  Real.hasDerivAt_arccos (by linarith [hx.1]) (by linarith [hx.2])
/-- Bảng (13): đạo hàm của arctan. -/
theorem hasDerivAt_arctangent (x : ℝ) : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
  Real.hasDerivAt_arctan x
/-- Bảng (14): đạo hàm của nhánh arccot giảm. -/
theorem hasDerivAt_arccotangent (x : ℝ) : HasDerivAt arccot (-(1 / (1 + x ^ 2))) x :=
  (Real.hasDerivAt_arctan x).const_sub (Real.pi / 2)

/-- Bảng (17): đạo hàm của sinh. -/
theorem hasDerivAt_hyperbolic_sine (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x :=
  Real.hasDerivAt_sinh x
/-- Bảng (18): đạo hàm của cosh. -/
theorem hasDerivAt_hyperbolic_cosine (x : ℝ) : HasDerivAt Real.cosh (Real.sinh x) x :=
  Real.hasDerivAt_cosh x
/-- Bảng (19): đạo hàm của sech. -/
theorem hasDerivAt_hyperbolic_secant (x : ℝ) :
    HasDerivAt sech (-sech x * Real.tanh x) x := by
  have h : HasDerivAt sech (-Real.sinh x / Real.cosh x ^ 2) x :=
    ((Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne').congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ by simp [sech])
  apply h.congr_deriv
  simp [sech, Real.tanh_eq_sinh_div_cosh]
  ring
/-- Bảng (20): đạo hàm của csch trên `x ≠ 0`. -/
theorem hasDerivAt_hyperbolic_cosecant (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt csch (-csch x * coth x) x := by
  have h : HasDerivAt csch (-Real.cosh x / Real.sinh x ^ 2) x :=
    ((Real.hasDerivAt_sinh x).inv (Real.sinh_ne_zero.mpr hx)).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ by simp [csch])
  apply h.congr_deriv
  simp [csch, coth]
  ring
/-- Bảng (21): đạo hàm của tanh. -/
theorem hasDerivAt_hyperbolic_tangent (x : ℝ) :
    HasDerivAt Real.tanh (sech x ^ 2) x := by
  have h : HasDerivAt Real.tanh
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
      (Real.cosh_pos x).ne').congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ Real.tanh_eq_sinh_div_cosh t)
  apply h.congr_deriv
  unfold sech
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]
/-- Bảng (22): đạo hàm của coth khi `x ≠ 0`. -/
theorem hasDerivAt_hyperbolic_cotangent (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt coth (-(csch x ^ 2)) x := by
  apply ((Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x)
    (Real.sinh_ne_zero.mpr hx)).congr_deriv
  unfold csch
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]
/-- Bảng (23): đạo hàm của arsinh. -/
theorem hasDerivAt_inverse_hyperbolic_sine (x : ℝ) :
    HasDerivAt Real.arsinh (1 / √(x ^ 2 + 1)) x := by
  simpa only [one_div, add_comm] using Real.hasDerivAt_arsinh x
/-- Bảng (24): đạo hàm của arcosh trên `x > 1`. -/
theorem hasDerivAt_inverse_hyperbolic_cosine (x : ℝ) (hx : 1 < x) :
    HasDerivAt Real.arcosh (1 / √(x ^ 2 - 1)) x := by
  simpa only [one_div] using Real.hasDerivAt_arcosh hx



theorem reciprocal_mem_open_unit (x : ℝ) (hx : 1 < |x|) :
    x ≠ 0 ∧ 1 / x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hx0 : x ≠ 0 := by intro hz; norm_num [hz] at hx
  have habs : |1 / x| < 1 := by
    simpa only [one_div, abs_inv] using inv_lt_one_of_one_lt₀ hx
  exact ⟨hx0, abs_lt.mp habs⟩


theorem reciprocal_sqrt_minus (x : ℝ) (hx : 1 < |x|) :
    √(1 - (1 / x) ^ 2) = √(x ^ 2 - 1) / |x| := by
  have hx0 := (reciprocal_mem_open_unit x hx).1
  have hs : 0 ≤ x ^ 2 - 1 := by nlinarith [sq_abs x]
  have he : 1 - (1 / x) ^ 2 = (x ^ 2 - 1) / x ^ 2 := by
    field_simp
  rw [he, Real.sqrt_div hs, Real.sqrt_sq_eq_abs]


theorem reciprocal_sqrt_plus (x : ℝ) (hx : x ≠ 0) :
    √(1 + (1 / x) ^ 2) = √(1 + x ^ 2) / |x| := by
  have he : 1 + (1 / x) ^ 2 = (1 + x ^ 2) / x ^ 2 := by
    field_simp
    ring
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs]


theorem arccot_mem_Ioo (x : ℝ) : arccot x ∈ Set.Ioo 0 Real.pi := by
  have h := Real.arctan_mem_Ioo x
  dsimp [arccot]
  constructor <;> linarith [h.1, h.2]


theorem cot_arccot (x : ℝ) : Real.cot (arccot x) = x := by
  rw [arccot, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, ← Real.tan_eq_sin_div_cos, Real.tan_arctan]


theorem arccot_cot (x : ℝ) (hx : x ∈ Set.Ioo 0 Real.pi) : arccot (Real.cot x) = x := by
  have hc : Real.cot x = Real.tan (Real.pi / 2 - x) := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [arccot, hc, Real.arctan_tan (by linarith [hx.2]) (by linarith [hx.1])]
  ring


theorem sec_arcsec (x : ℝ) (hx : 1 < |x|) : sec (arcsec x) = x := by
  have hh := (reciprocal_mem_open_unit x hx).2
  simp only [sec, arcsec, Real.cos_arccos hh.1.le hh.2.le, one_div_one_div]


theorem csc_arccsc (x : ℝ) (hx : 1 < |x|) : csc (arccsc x) = x := by
  have hh := (reciprocal_mem_open_unit x hx).2
  simp only [csc, arccsc, Real.sin_arcsin hh.1.le hh.2.le, one_div_one_div]


theorem hasDerivAt_comp_reciprocal {f : ℝ → ℝ} {d : ℝ} (x : ℝ) (hx : x ≠ 0)
    (hf : HasDerivAt f d (1 / x)) :
    HasDerivAt (fun t : ℝ ↦ f (1 / t)) (d * (-1 / x ^ 2)) x := by
  have hinv : HasDerivAt (fun t : ℝ ↦ 1 / t) (-1 / x ^ 2) x :=
    ((hasDerivAt_id x).inv hx).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ by simp)
  simpa only [Function.comp_def] using hf.comp x hinv

/-- Bảng (15): đạo hàm của arcsec trên `|x| > 1`. -/
theorem hasDerivAt_arcsecant (x : ℝ) (hx : 1 < |x|) :
    HasDerivAt arcsec (1 / (|x| * √(x ^ 2 - 1))) x := by
  obtain ⟨hx0, hh⟩ := reciprocal_mem_open_unit x hx
  have h := hasDerivAt_comp_reciprocal x hx0
    (Real.hasDerivAt_arccos (by linarith [hh.1]) (by linarith [hh.2]))
  apply h.congr_deriv
  rw [reciprocal_sqrt_minus x hx]
  field_simp
  simp only [sq_abs]

/-- Bảng (16): đạo hàm của arccsc trên `|x| > 1`. -/
theorem hasDerivAt_arccosecant (x : ℝ) (hx : 1 < |x|) :
    HasDerivAt arccsc (-(1 / (|x| * √(x ^ 2 - 1)))) x := by
  obtain ⟨hx0, hh⟩ := reciprocal_mem_open_unit x hx
  have h := hasDerivAt_comp_reciprocal x hx0
    (Real.hasDerivAt_arcsin (by linarith [hh.1]) (by linarith [hh.2]))
  apply h.congr_deriv
  rw [reciprocal_sqrt_minus x hx]
  field_simp
  simp only [sq_abs]


theorem reciprocal_sqrt_sech (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    √((1 / x) ^ 2 - 1) = √(1 - x ^ 2) / x := by
  have he : (1 / x) ^ 2 - 1 = (1 - x ^ 2) / x ^ 2 := by
    field_simp
  rw [he, Real.sqrt_div (by nlinarith), Real.sqrt_sq_eq_abs, abs_of_pos hx]


theorem arsech_eq_source_formula (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    arsech x = Real.log ((1 + √(1 - x ^ 2)) / x) := by
  unfold arsech Real.arcosh
  rw [reciprocal_sqrt_sech x hx hx1, add_div]


theorem arcsch_eq_source_formula (x : ℝ) (hx : x ≠ 0) :
    arcsch x = Real.log (1 / x + √(1 + x ^ 2) / |x|) := by
  unfold arcsch Real.arsinh
  rw [reciprocal_sqrt_plus x hx]

/-- Bảng (25): đạo hàm của arsech trên `0 < x < 1`. -/
theorem hasDerivAt_inverse_hyperbolic_secant (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt arsech (-(1 / (x * √(1 - x ^ 2)))) x := by
  have hinv : 1 < 1 / x := (lt_div_iff₀ hx).mpr (by simpa using hx1)
  have h := hasDerivAt_comp_reciprocal x hx.ne' (Real.hasDerivAt_arcosh hinv)
  apply h.congr_deriv
  rw [reciprocal_sqrt_sech x hx hx1.le]
  field_simp

/-- Bảng (26): đạo hàm của arcsch trên `x ≠ 0`. -/
theorem hasDerivAt_inverse_hyperbolic_cosecant (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt arcsch (-(1 / (|x| * √(1 + x ^ 2)))) x := by
  have h := hasDerivAt_comp_reciprocal x hx (Real.hasDerivAt_arsinh (1 / x))
  apply h.congr_deriv
  rw [reciprocal_sqrt_plus x hx]
  field_simp
  simp only [sq_abs]


theorem artanh_eq_source_formula (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.artanh x = 1 / 2 * Real.log ((1 + x) / (1 - x)) :=
  Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩


theorem hasDerivAt_artanh_formula (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ ↦ 1 / 2 * Real.log ((1 + t) / (1 - t))) (1 / (1 - x ^ 2)) x := by
  have hn : 0 < 1 + x := by linarith [hx.1]
  have hd : 0 < 1 - x := by linarith [hx.2]
  have hq := ((hasDerivAt_id x).const_add 1).div ((hasDerivAt_id x).const_sub 1) hd.ne'
  have h := (hq.log (div_pos hn hd).ne').const_mul (1 / 2 : ℝ)
  apply h.congr_deriv
  simp only [Pi.div_apply, id_eq]
  have hsq : 1 - x ^ 2 ≠ 0 := by nlinarith [mul_pos hn hd]
  field_simp [hn.ne', hd.ne', hsq]
  ring

/-- Bảng (27): đạo hàm của artanh trên `−1 < x < 1`. -/
theorem hasDerivAt_inverse_hyperbolic_tangent (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  apply (hasDerivAt_artanh_formula x hx).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
  exact artanh_eq_source_formula t ht

/-- Bảng (28): đạo hàm của arcoth trên `|x| > 1`. -/
theorem hasDerivAt_inverse_hyperbolic_cotangent (x : ℝ) (hx : 1 < |x|) :
    HasDerivAt arcoth (1 / (1 - x ^ 2)) x := by
  have hx1 : x - 1 ≠ 0 := by
    intro hh
    have he : x = 1 := by linarith
    simp [he] at hx
  have hxp : x + 1 ≠ 0 := by
    intro hh
    have he : x = -1 := by linarith
    simp [he] at hx
  have hq := ((hasDerivAt_id x).add_const 1).div ((hasDerivAt_id x).sub_const 1) hx1
  have harg : 0 < (x + 1) / (x - 1) := by
    rcases lt_abs.mp hx with hpos | hneg
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  have h := (hq.log harg.ne').const_mul (1 / 2 : ℝ)
  apply h.congr_deriv
  simp only [Pi.div_apply, id_eq]
  have hsq : 1 - x ^ 2 ≠ 0 := by nlinarith [sq_abs x]
  field_simp [hxp, hx1, hsq]
  ring



theorem arsinh_eq_source_formula (x : ℝ) :
    Real.arsinh x = Real.log (x + √(x ^ 2 + 1)) := by
  simp only [Real.arsinh, add_comm 1 (x ^ 2)]

/-- Công thức, dòng 312: đạo hàm của arsinh. -/
theorem arsinh_derivative_calculation (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.log (t + √(t ^ 2 + 1)))
      ((1 + x / √(x ^ 2 + 1)) / (x + √(x ^ 2 + 1))) x ∧
      (1 + x / √(x ^ 2 + 1)) / (x + √(x ^ 2 + 1)) = 1 / √(x ^ 2 + 1) := by
  have hr : √(x ^ 2 + 1) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hxarg : 0 < x + √(x ^ 2 + 1) := by
    simpa only [Real.exp_arsinh, add_comm 1 (x ^ 2)] using Real.exp_pos (Real.arsinh x)
  have he : (1 + x / √(x ^ 2 + 1)) / (x + √(x ^ 2 + 1)) = 1 / √(x ^ 2 + 1) := by
    field_simp [hr, hxarg.ne']
    ring
  refine ⟨?_, he⟩
  apply ((hasDerivAt_inverse_hyperbolic_sine x).congr_deriv he.symm).congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (arsinh_eq_source_formula t).symm

/-- Công thức, dòng 313: đạo hàm của artanh. -/
theorem artanh_derivative_calculation (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / 2 * ((2 / (1 - x) ^ 2) / ((1 + x) / (1 - x)))) x ∧
      1 / 2 * ((2 / (1 - x) ^ 2) / ((1 + x) / (1 - x))) = 1 / (1 - x ^ 2) := by
  have hn : 0 < 1 + x := by linarith [hx.1]
  have hd : 0 < 1 - x := by linarith [hx.2]
  have hsq : 1 - x ^ 2 ≠ 0 := by nlinarith [mul_pos hn hd]
  have he : 1 / 2 * ((2 / (1 - x) ^ 2) / ((1 + x) / (1 - x))) = 1 / (1 - x ^ 2) := by
    field_simp [hn.ne', hd.ne', hsq]
    ring
  exact ⟨(hasDerivAt_inverse_hyperbolic_tangent x hx).congr_deriv he.symm, he⟩

/-- Dòng 307: thương sai phân khi `x → x₀`, với `x ≠ x₀`. -/
theorem exponential_difference_quotient_limit (a x : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Tendsto (fun y : ℝ ↦ (a ^ y - a ^ x) / (y - x)) (𝓝[≠] x)
      (𝓝 (a ^ x * Real.log a)) := by
  have h := (hasDerivAt_exponential a x ha ha1).tendsto_slope
  have he : slope (fun t : ℝ ↦ a ^ t) x = fun y : ℝ ↦ (a ^ y - a ^ x) / (y - x) := by
    funext y
    exact slope_def_field _ _ _
  rwa [he] at h

/-- Dòng 307: thương sai phân theo số gia `t → 0`, với `t ≠ 0`. -/
theorem exponential_increment_quotient_limit (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Tendsto (fun t : ℝ ↦ (a ^ t - 1) / t) (𝓝[≠] 0) (𝓝 (Real.log a)) := by
  simpa only [Real.rpow_zero, one_mul, sub_zero] using
    exponential_difference_quotient_limit a 0 ha ha1

/-- Dòng 307: phân tích thương sai phân của hàm mũ. -/
theorem exponential_difference_factor (a x y : ℝ) (ha : 0 < a) :
    (a ^ y - a ^ x) / (y - x) = a ^ x * ((a ^ (y - x) - 1) / (y - x)) := by
  have he : a ^ y - a ^ x = a ^ x * (a ^ (y - x) - 1) := by
    rw [Real.rpow_sub ha y x]
    field_simp [(Real.rpow_pos_of_pos ha x).ne']
  rw [he, mul_div_assoc]

/-- Dòng 307: thương sai phân sau đổi biến có giới hạn `log a`. -/
theorem exponential_shifted_quotient_limit (a x : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Tendsto (fun y : ℝ ↦ (a ^ (y - x) - 1) / (y - x)) (𝓝[≠] x)
      (𝓝 (Real.log a)) := by
  have hp : a ^ x ≠ 0 := (Real.rpow_pos_of_pos ha x).ne'
  have h := (exponential_difference_quotient_limit a x ha ha1).div_const (a ^ x)
  have he : a ^ x * Real.log a / a ^ x = Real.log a := by field_simp
  rw [he] at h
  apply h.congr
  intro y
  rw [exponential_difference_factor a x y ha]
  simp [hp]


theorem logarithm_exponential_inverse (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    (∀ x : ℝ, Real.logb a (a ^ x) = x) ∧
      (∀ y : ℝ, 0 < y → a ^ Real.logb a y = y) := by
  exact ⟨fun _ ↦ Real.logb_rpow ha ha1, fun _ hy ↦ Real.rpow_logb ha ha1 hy⟩

/-- Công thức, dòng 310: đạo hàm logarit theo cơ số tại `y = aˣ`. -/
theorem logarithm_inverse_derivative_chain (a x y : ℝ) (ha : 0 < a) (ha1 : a ≠ 1)
    (hy : y = a ^ x) :
    deriv (Real.logb a) y = 1 / deriv (fun t : ℝ ↦ a ^ t) x ∧
      1 / deriv (fun t : ℝ ↦ a ^ t) x = 1 / (a ^ x * Real.log a) ∧
      1 / (a ^ x * Real.log a) = 1 / (y * Real.log a) := by
  have hxder := (hasDerivAt_exponential a x ha ha1).deriv
  have hypos : 0 < y := by rw [hy]; exact Real.rpow_pos_of_pos ha x
  have hyder := (hasDerivAt_logarithm a y ha ha1 hypos).deriv
  rw [hxder, hyder, hy]
  exact ⟨rfl, rfl, rfl⟩



theorem arcsec_mem_principal_range (x : ℝ) (hx : 1 < |x|) :
    arcsec x ∈ Set.Ioo 0 Real.pi ∧ arcsec x ≠ Real.pi / 2 := by
  obtain ⟨hx0, hh⟩ := reciprocal_mem_open_unit x hx
  refine ⟨⟨Real.arccos_pos.mpr hh.2, Real.arccos_lt_pi.mpr hh.1⟩, ?_⟩
  intro he
  exact (one_div_ne_zero hx0) (Real.arccos_eq_pi_div_two.mp he)


theorem arccsc_mem_principal_range (x : ℝ) (hx : 1 < |x|) :
    arccsc x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧ arccsc x ≠ 0 := by
  obtain ⟨hx0, hh⟩ := reciprocal_mem_open_unit x hx
  refine ⟨⟨Real.neg_pi_div_two_lt_arcsin.mpr hh.1, Real.arcsin_lt_pi_div_two.mpr hh.2⟩, ?_⟩
  intro he
  exact (one_div_ne_zero hx0) (Real.arcsin_eq_zero_iff.mp he)


theorem sech_arsech (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : sech (arsech x) = x := by
  have hinv : 1 ≤ 1 / x := (le_div_iff₀ hx).mpr (by simpa using hx1)
  simp only [sech, arsech, Real.cosh_arcosh hinv, one_div_one_div]


theorem csch_arcsch (x : ℝ) (_hx : x ≠ 0) : csch (arcsch x) = x := by
  simp only [csch, arcsch, Real.sinh_arsinh, one_div_one_div]

end calculus.Chapter04.Section01ElementaryDerivatives
