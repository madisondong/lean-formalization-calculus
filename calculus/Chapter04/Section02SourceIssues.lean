import calculus.Chapter04.Section02
import calculus.Chapter04.Section01Higher
import calculus.Chapter03.Section03Supplement
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Xấp xỉ căn bậc ba và đạo hàm cấp hai theo tham số

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 764–774, 807. Hệ số của xấp xỉ căn bậc ba là `1/300`; mẫu của đạo hàm cấp hai theo tham số là `φ′(t)³`.
-/
namespace calculus.Chapter04.Section02SourceIssues
open Set Filter calculus.Chapter04.Section02 calculus.Chapter04.Section01Higher
open calculus.Chapter03.Section03Supplement
open scoped Topology


theorem cubeRoot_at_thousand : signedCubeRoot 1000 = 10 :=
  signedCubeRoot_unique (by norm_num)


theorem cubeRoot_at_million : signedCubeRoot 1000000 = 100 :=
  signedCubeRoot_unique (by norm_num)

/-- Phản ví dụ cho phép tính trong Ví dụ 4.2.3. -/
theorem printed_cubeRoot_increment_false :
    signedCubeRoot 1000 + 1 / (3 * signedCubeRoot 1000000) * (1 : ℝ) ≠ 10 + 1 / 30 := by
  rw [cubeRoot_at_thousand, cubeRoot_at_million]
  norm_num


theorem cubeRoot_hasDerivAt_thousand : HasDerivAt signedCubeRoot (1 / 300) 1000 := by
  have he : signedCubeRoot =ᶠ[𝓝 (1000 : ℝ)] (fun x : ℝ ↦ x ^ (1 / 3 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1000)] with x hx
    simp only [signedCubeRoot, if_pos (le_of_lt (mem_Ioi.mp hx))]
  have h := Real.hasDerivAt_rpow_const (x := (1000 : ℝ)) (p := (1 / 3 : ℝ))
    (Or.inl (by norm_num))
  apply (h.congr_of_eventuallyEq he).congr_deriv
  rw [show (1000 : ℝ) = (10 : ℝ) ^ 3 by norm_num,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 10) 3]
  norm_num


theorem corrected_cubeRoot_linear_value :
    signedCubeRoot 1000 + firstDifferential signedCubeRoot 1000 1 = (3001 / 300 : ℝ) := by
  rw [cubeRoot_at_thousand, firstDifferential, cubeRoot_hasDerivAt_thousand.deriv]
  norm_num


theorem corrected_cubeRoot_error :
    |signedCubeRoot 1001 - (3001 / 300 : ℝ)| < 1 / 500000 := by
  have hm : StrictMono (fun x : ℝ ↦ x ^ (3 : ℕ)) :=
    (show Odd (3 : ℕ) from by decide).strictMono_pow
  have hl : (3001 / 300 : ℝ) - 1 / 500000 < signedCubeRoot 1001 := by
    apply hm.lt_iff_lt.mp
    rw [signedCubeRoot_cube]
    norm_num
  have hu : signedCubeRoot 1001 < (3001 / 300 : ℝ) := by
    apply hm.lt_iff_lt.mp
    rw [signedCubeRoot_cube]
    norm_num
  rw [abs_lt]
  constructor <;> linarith


theorem printed_parametric_second_denominator_false :
    iteratedDeriv 2 (fun x : ℝ ↦ x ^ (2 : ℕ)) 2 ≠
      (deriv (fun t : ℝ ↦ t) 2 * iteratedDeriv 2 (fun t : ℝ ↦ t ^ (2 : ℕ)) 2 -
        iteratedDeriv 2 (fun t : ℝ ↦ t) 2 * deriv (fun t : ℝ ↦ t ^ (2 : ℕ)) 2) /
        (2 : ℝ) ^ 3 := by
  have hid : (fun x : ℝ ↦ x) = (fun x : ℝ ↦ x ^ (1 : ℕ)) := by funext x; simp
  have hsecond : iteratedDeriv 2 (fun t : ℝ ↦ t) 2 = 0 := by
    rw [hid]
    exact pow_iteratedDeriv_above_degree 1 2 2 (by decide)
  rw [pow_iteratedDeriv_at_degree 2 2, hsecond]
  norm_num


theorem corrected_second_parametric_algebra (A B C D h : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    (D * h ^ 2 - (B / A) * (C * h ^ 2)) / (A * h) ^ 2 =
      (A * D - C * B) / A ^ 3 := by
  field_simp

end calculus.Chapter04.Section02SourceIssues
