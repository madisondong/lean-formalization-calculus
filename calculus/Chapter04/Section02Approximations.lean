import calculus.Chapter04.Section02
import calculus.Chapter04.Section01ElementaryDerivatives
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# §4.2 Bài tập 3: xấp xỉ bằng vi phân

Nguồn: dòng 840–852.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter04.Section02Approximations
open calculus.Chapter04.Section02 calculus.Chapter04.Section01ElementaryDerivatives

/-- Xấp xỉ tuyến tính của `f(a+h)`, kèm cận sai số địa phương. -/
def DifferentialEstimate (f : ℝ → ℝ) (a A h value : ℝ) : Prop :=
  HasLinearApproximation f a A ∧ f a + A * h = value ∧
    ∀ ε > 0, ∃ δ > 0, ∀ u : ℝ, |u| < δ → |f (a + u) - (f a + A * u)| ≤ ε * |u|


theorem differentialEstimate_of_hasDerivAt {f : ℝ → ℝ} {a A h value : ℝ}
    (hf : HasDerivAt f A a) (hv : f a + A * h = value) : DifferentialEstimate f a A h value := by
  refine ⟨(hasLinearApproximation_iff_hasDerivAt f a A).mpr hf, hv, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := linearApproximation_error_bound hf.differentiableAt hε
  refine ⟨δ, hδ, fun u hu ↦ ?_⟩
  have hh := hb u hu
  simpa only [firstDifferential, hf.deriv] using hh

/-- Bài 4.2.3(a): xấp xỉ `1,999⁴` bằng `15,968`, kèm cận sai số. -/
theorem quartic_differential_estimate :
    DifferentialEstimate (fun x : ℝ ↦ x ^ 4) 2 32 (-1 / 1000) (1996 / 125) ∧
      |(1999 / 1000 : ℝ) ^ 4 - 1996 / 125| < 3 / 125000 := by
  constructor
  · apply differentialEstimate_of_hasDerivAt
    · convert! (hasDerivAt_id (2 : ℝ)).pow 4 using 1
      norm_num [id_eq, Pi.pow_apply]
    · norm_num
  · norm_num

/-- Bài 4.2.3(b): xấp xỉ `1/4002` bằng vi phân tại 4000. -/
theorem reciprocal_differential_estimate :
    DifferentialEstimate (fun x : ℝ ↦ 1 / x) 4000 (-1 / 16000000) 2 (1999 / 8000000) ∧
      |(1 / 4002 : ℝ) - 1999 / 8000000| < 1 / 16000000000 := by
  constructor
  · apply differentialEstimate_of_hasDerivAt
    · convert! (hasDerivAt_const (4000 : ℝ) (1 : ℝ)).div (hasDerivAt_id 4000) (by norm_num) using 1
      norm_num [id_eq]
    · norm_num
  · norm_num

/-- Bài 4.2.3(c): xấp xỉ `exp(0,2)` bằng `1,2`. -/
theorem exponential_differential_estimate :
    DifferentialEstimate Real.exp 0 1 (1 / 5) (6 / 5) := by
  apply differentialEstimate_of_hasDerivAt
  · simpa only [Real.exp_zero] using Real.hasDerivAt_exp 0
  · norm_num

/-- Bài 4.2.3(d): xấp xỉ `log₁₀ 11` bằng vi phân tại 10. -/
theorem base_ten_log_differential_estimate :
    DifferentialEstimate (Real.logb 10) 10 (1 / (10 * Real.log 10)) 1
      (1 + 1 / (10 * Real.log 10)) := by
  apply differentialEstimate_of_hasDerivAt (hasDerivAt_logarithm 10 10 (by norm_num) (by norm_num) (by norm_num))
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 10)]
  ring

/-- Bài 4.2.3(e): xấp xỉ `√100,5` bằng `10,025`. -/
theorem square_root_differential_estimate :
    DifferentialEstimate Real.sqrt 100 (1 / 20) (1 / 2) (401 / 40) := by
  have hs : Real.sqrt (100 : ℝ) = 10 := by
    rw [show (100 : ℝ) = 10 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)]
  apply differentialEstimate_of_hasDerivAt
  · convert! Real.hasDerivAt_sqrt (x := 100) (by norm_num) using 1
    norm_num [hs]
  · norm_num [hs]


theorem fourth_root_at_625 : (625 : ℝ) ^ (1 / 4 : ℝ) = 5 := by
  rw [show (625 : ℝ) = 5 ^ (4 : ℕ) by norm_num]
  convert! Real.pow_rpow_inv_natCast (x := (5 : ℝ)) (by norm_num) (by decide : (4 : ℕ) ≠ 0) using 1
  norm_num

/-- Bài 4.2.3(f): xấp xỉ căn bậc bốn của 624 bằng `4,998`. -/
theorem fourth_root_differential_estimate :
    DifferentialEstimate (fun x : ℝ ↦ x ^ (1 / 4 : ℝ)) 625 (1 / 500) (-1) (2499 / 500) := by
  have hp : (625 : ℝ) ^ (1 / 4 - 1 : ℝ) = 1 / 125 := by
    rw [Real.rpow_sub (by norm_num), fourth_root_at_625, Real.rpow_one]
    norm_num
  apply differentialEstimate_of_hasDerivAt
  · convert! Real.hasDerivAt_rpow_const (x := (625 : ℝ)) (p := (1 / 4 : ℝ))
      (Or.inl (by norm_num)) using 1
    norm_num [hp]
  · rw [fourth_root_at_625]
    norm_num

/-- Bài 4.2.3(g): xấp xỉ `cos 29°` bằng `√3/2 + π/360`. -/
theorem degree_cosine_differential_estimate :
    DifferentialEstimate Real.cos (Real.pi / 6) (-1 / 2) (-Real.pi / 180)
      (Real.sqrt 3 / 2 + Real.pi / 360) := by
  apply differentialEstimate_of_hasDerivAt
  · convert! Real.hasDerivAt_cos (Real.pi / 6) using 1
    norm_num [Real.sin_pi_div_six]
  · rw [Real.cos_pi_div_six]
    ring


theorem degree_cosine_estimate_input : Real.pi / 6 + (-Real.pi / 180) = 29 * Real.pi / 180 := by ring

/-- Bài 4.2.3(h): xấp xỉ `arctan 1,05` bằng `π/4 + 0,025`. -/
theorem arctan_differential_estimate :
    DifferentialEstimate Real.arctan 1 (1 / 2) (1 / 20) (Real.pi / 4 + 1 / 40) := by
  apply differentialEstimate_of_hasDerivAt
  · convert! Real.hasDerivAt_arctan 1 using 1
    norm_num
  · rw [Real.arctan_one]
    ring


theorem differential_estimate_inputs :
    (2 + (-1 / 1000) : ℝ) = 1999 / 1000 ∧ (4000 + 2 : ℝ) = 4002 ∧
      (0 + 1 / 5 : ℝ) = 1 / 5 ∧ (10 + 1 : ℝ) = 11 ∧
      (100 + 1 / 2 : ℝ) = 201 / 2 ∧ (625 + (-1) : ℝ) = 624 ∧
      Real.pi / 6 + (-Real.pi / 180) = 29 * Real.pi / 180 ∧
      (1 + 1 / 20 : ℝ) = 21 / 20 := by
  norm_num
  ring

end calculus.Chapter04.Section02Approximations
