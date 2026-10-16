import calculus.Chapter04.Section02
import calculus.Chapter04.Section01Exercises

/-!
# §4.2 Bài tập 1: vi phân cấp một

Nguồn: dòng 818–827.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter04.Section02FirstExercises
open calculus.Chapter04.Section02 calculus.Chapter04.Section01ElementaryDerivatives
open calculus.Chapter04.Section01Exercises
open calculus.Chapter03.Section01Supplement (realCubeRoot)


theorem firstDifferential_of_hasDerivAt {f : ℝ → ℝ} {x A : ℝ} (hf : HasDerivAt f A x) (h : ℝ) :
    firstDifferential f x h = A * h := by
  rw [firstDifferential, hf.deriv]

/-- Bài 4.2.1(a): vi phân của tích x và exp(−5x). -/
theorem exp_product_first_differential (x h : ℝ) :
    firstDifferential (fun y : ℝ ↦ y * Real.exp (-5 * y)) x h =
      (1 - 5 * x) * Real.exp (-5 * x) * h := by
  have he : HasDerivAt (fun y : ℝ ↦ Real.exp (-5 * y))
      (-5 * Real.exp (-5 * x)) x := by
    convert! (Real.hasDerivAt_exp (-5 * x)).comp x ((hasDerivAt_id x).const_mul (-5)) using 1
    norm_num [Function.comp_def]
    ring
  have hf := (hasDerivAt_id x).mul he
  calc
    _ = _ := firstDifferential_of_hasDerivAt hf h
    _ = _ := by simp only [id_eq]; ring

/-- Bài 4.2.1(b): vi phân của `tan √x`, với `x > 0` và `cos √x ≠ 0`. -/
theorem tan_sqrt_first_differential (x h : ℝ) (hx : 0 < x) (hc : Real.cos (Real.sqrt x) ≠ 0) :
    firstDifferential (fun y : ℝ ↦ Real.tan (Real.sqrt y)) x h =
      (1 / (2 * Real.sqrt x * Real.cos (Real.sqrt x) ^ 2)) * h := by
  have hf := (Real.hasDerivAt_tan hc).comp x (Real.hasDerivAt_sqrt hx.ne')
  calc
    _ = _ := firstDifferential_of_hasDerivAt hf h
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring


theorem tan_sqrt_not_differentiable_zero :
    ¬ DifferentiableAt ℝ (fun x : ℝ ↦ Real.tan (Real.sqrt x)) 0 := by
  intro hf
  have hc : DifferentiableAt ℝ (fun x : ℝ ↦ Real.arctan (Real.tan (Real.sqrt x))) 0 :=
    (Real.differentiable_arctan.differentiableAt).comp 0 hf
  have he : (fun x : ℝ ↦ Real.arctan (Real.tan (Real.sqrt x))) =ᶠ[𝓝 (0 : ℝ)] Real.sqrt := by
    have hu : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), Real.sqrt x < Real.pi / 2 :=
      (show Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 0) from by
        simpa only [Real.sqrt_zero] using (show ContinuousAt Real.sqrt (0 : ℝ) from Real.continuous_sqrt.continuousAt).tendsto).eventually
        (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))
    filter_upwards [hu] with x hx
    exact Real.arctan_tan (by linarith [Real.sqrt_nonneg x, Real.pi_pos]) hx
  have hs : DifferentiableAt ℝ Real.sqrt 0 := hc.congr_of_eventuallyEq he.symm
  apply Real.not_differentiableAt_rpow_const_zero (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num)
  have heq : Real.sqrt = (fun x : ℝ ↦ x ^ (1 / (2 : ℝ))) := funext Real.sqrt_eq_rpow
  rw [← heq]
  exact hs

/-- Bài 4.2.1(c): vi phân của x² sin(2x). -/
theorem square_sine_first_differential (x h : ℝ) :
    firstDifferential (fun y : ℝ ↦ y ^ 2 * Real.sin (2 * y)) x h =
      (2 * x * Real.sin (2 * x) + 2 * x ^ 2 * Real.cos (2 * x)) * h := by
  have hs := (Real.hasDerivAt_sin (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hf := ((hasDerivAt_id x).pow 2).mul hs
  calc
    _ = _ := firstDifferential_of_hasDerivAt hf h
    _ = _ := by
      simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Function.comp_apply]
      ring

/-- Bài 4.2.1(d): vi phân của `log(cos x)` trên `cos x > 0`. -/
theorem log_cosine_first_differential (x h : ℝ) (hc : 0 < Real.cos x) :
    firstDifferential (fun y : ℝ ↦ Real.log (Real.cos y)) x h = -Real.tan x * h := by
  have hf := (Real.hasDerivAt_log hc.ne').comp x (Real.hasDerivAt_cos x)
  calc
    _ = _ := firstDifferential_of_hasDerivAt hf h
    _ = _ := by simp only [Real.tan_eq_sin_div_cos, div_eq_mul_inv]; ring


theorem hasDerivAt_square_ratio (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (1 - y ^ 2) / (1 + y ^ 2))
      (-4 * x / (1 + x ^ 2) ^ 2) x := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hs := (hasDerivAt_id x).pow 2
  have hf := (hs.const_sub 1).div (hs.const_add 1) hd
  apply hf.congr_deriv
  simp only [id_eq, Nat.cast_ofNat]
  congr 1
  ring

/-- Bài 4.2.1(e): vi phân căn bậc ba thực của `(1−x²)/(1+x²)` trên `x ≠ ±1`. -/
theorem cube_root_square_ratio_first_differential (x h : ℝ) (hx : x ≠ 1) (hxm : x ≠ -1) :
    firstDifferential (fun y : ℝ ↦ realCubeRoot ((1 - y ^ 2) / (1 + y ^ 2))) x h =
      (-4 * x / (3 * (1 + x ^ 2) ^ 2 * realCubeRoot ((1 - x ^ 2) / (1 + x ^ 2)) ^ 2)) * h := by
  have hn : 1 - x ^ 2 ≠ 0 := by
    intro he
    have hprod : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hp | hp
    · exact hx (by linarith)
    · exact hxm (by linarith)
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hf := (hasDerivAt_realCubeRoot _ (div_ne_zero hn hd)).comp x (hasDerivAt_square_ratio x)
  calc
    _ = _ := firstDifferential_of_hasDerivAt hf h
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring


theorem cube_root_square_ratio_not_differentiable (x : ℝ) (hx : x = 1 ∨ x = -1) :
    ¬ DifferentiableAt ℝ (fun y : ℝ ↦ realCubeRoot ((1 - y ^ 2) / (1 + y ^ 2))) x := by
  intro hf
  have hr0 : realCubeRoot ((1 - x ^ 2) / (1 + x ^ 2)) = 0 := by
    apply (realCubeRoot_eq_iff _ 0).mpr
    rcases hx with rfl | rfl <;> norm_num
  have hcube := hf.hasDerivAt.pow 3
  have heq : (fun y : ℝ ↦ realCubeRoot ((1 - y ^ 2) / (1 + y ^ 2)) ^ 3) =
      (fun y ↦ (1 - y ^ 2) / (1 + y ^ 2)) := funext fun y ↦ realCubeRoot_cubed _
  change HasDerivAt (fun y : ℝ ↦ realCubeRoot ((1 - y ^ 2) / (1 + y ^ 2)) ^ 3) _ x at hcube
  rw [heq, hr0] at hcube
  norm_num only [zero_pow, Nat.cast_ofNat, mul_zero, zero_mul] at hcube
  have he := hcube.unique (hasDerivAt_square_ratio x)
  rcases hx with rfl | rfl <;> norm_num at he

end calculus.Chapter04.Section02FirstExercises
