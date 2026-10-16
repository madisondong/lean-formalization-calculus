import calculus.Chapter04.Section02Higher
import calculus.Chapter04.Section01ElementaryDerivatives
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# §4.2 Bài tập 2: vi phân cấp hai

Nguồn: dòng 829–838.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter04.Section02SecondExercises
open calculus.Chapter04.Section02Higher calculus.Chapter04.Section01ElementaryDerivatives


theorem hasDerivAt_deriv_of_local_formula {f g : ℝ → ℝ} {I : Set ℝ} {x A : ℝ}
    (hI : IsOpen I) (hx : x ∈ I) (hf : ∀ y ∈ I, HasDerivAt f (g y) y) (hg : HasDerivAt g A x) :
    HasDerivAt (deriv f) A x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds hx] with y hy
  exact (hf y hy).deriv


theorem secondDifferential_of_hasDerivAt_deriv {f : ℝ → ℝ} {I : Set ℝ} {x A : ℝ}
    (hI : IsOpen I) (hx : x ∈ I) (hf : HasDerivAt (deriv f) A x) (h : ℝ) :
    higherDifferential 2 f I x h = A * h ^ 2 := by
  unfold higherDifferential
  rw [iteratedDerivWithin_of_isOpen hI hx]
  rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one, hf.deriv]


theorem hasDerivAt_scaled_arctan (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 1 / 3 * Real.arctan (y / 3)) (1 / (9 + x ^ 2)) x := by
  have hf := ((Real.hasDerivAt_arctan (x / 3)).comp x ((hasDerivAt_id x).div_const 3)).const_mul (1 / 3)
  apply hf.congr_deriv
  field_simp
  ring

/-- Bài 4.2.2(a): đạo hàm và vi phân cấp hai. -/
theorem scaled_arctan_second_differential (x h : ℝ) :
    HasDerivAt (deriv (fun y : ℝ ↦ 1 / 3 * Real.arctan (y / 3)))
      (-2 * x / (9 + x ^ 2) ^ 2) x ∧
    higherDifferential 2 (fun y : ℝ ↦ 1 / 3 * Real.arctan (y / 3)) univ x h =
      (-2 * x / (9 + x ^ 2) ^ 2) * h ^ 2 := by
  have hg : HasDerivAt (fun y : ℝ ↦ 1 / (9 + y ^ 2)) (-2 * x / (9 + x ^ 2) ^ 2) x := by
    have hh := (hasDerivAt_const x (1 : ℝ)).div (((hasDerivAt_id x).pow 2).const_add 9)
      (by positivity : 9 + x ^ 2 ≠ 0)
    apply hh.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, zero_mul, zero_sub, one_mul]
    ring
  have hf := hasDerivAt_deriv_of_local_formula isOpen_univ (mem_univ x)
    (fun y _ ↦ hasDerivAt_scaled_arctan y) hg
  exact ⟨hf, secondDifferential_of_hasDerivAt_deriv isOpen_univ (mem_univ x) hf h⟩


theorem hasDerivAt_sinh_quotient (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.sinh (4 * y) / y)
      ((4 * x * Real.cosh (4 * x) - Real.sinh (4 * x)) / x ^ 2) x := by
  have hs := (Real.hasDerivAt_sinh (4 * x)).comp x ((hasDerivAt_id x).const_mul 4)
  have hf := hs.div (hasDerivAt_id x) hx
  apply hf.congr_deriv
  simp only [id_eq, mul_one, Function.comp_apply]
  congr 1
  ring

/-- Bài 4.2.2(b): vi phân cấp hai trên `x ≠ 0`. -/
theorem sinh_quotient_second_differential (x h : ℝ) (hx : x ≠ 0) :
    HasDerivAt (deriv (fun y : ℝ ↦ Real.sinh (4 * y) / y))
      (((16 * x ^ 2 + 2) * Real.sinh (4 * x) - 8 * x * Real.cosh (4 * x)) / x ^ 3) x ∧
    higherDifferential 2 (fun y : ℝ ↦ Real.sinh (4 * y) / y) {y : ℝ | y ≠ 0} x h =
      (((16 * x ^ 2 + 2) * Real.sinh (4 * x) - 8 * x * Real.cosh (4 * x)) / x ^ 3) * h ^ 2 := by
  have hs := (Real.hasDerivAt_sinh (4 * x)).comp x ((hasDerivAt_id x).const_mul 4)
  have hc := (Real.hasDerivAt_cosh (4 * x)).comp x ((hasDerivAt_id x).const_mul 4)
  have hn : HasDerivAt (fun y : ℝ ↦ 4 * y * Real.cosh (4 * y) - Real.sinh (4 * y))
      (16 * x * Real.sinh (4 * x)) x := by
    have hh := (((hasDerivAt_id x).const_mul 4).mul hc).sub hs
    apply hh.congr_deriv
    simp only [id_eq, Function.comp_apply]
    ring
  have hg : HasDerivAt (fun y : ℝ ↦
      (4 * y * Real.cosh (4 * y) - Real.sinh (4 * y)) / y ^ 2)
      (((16 * x ^ 2 + 2) * Real.sinh (4 * x) - 8 * x * Real.cosh (4 * x)) / x ^ 3) x := by
    have hh := hn.div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
    apply hh.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat]
    field_simp [hx]
    ring
  have hI : IsOpen {y : ℝ | y ≠ 0} := isOpen_ne
  have hf := hasDerivAt_deriv_of_local_formula hI hx (fun y hy ↦ hasDerivAt_sinh_quotient y hy) hg
  exact ⟨hf, secondDifferential_of_hasDerivAt_deriv hI hx hf h⟩


theorem hasDerivAt_double_arsech (x : ℝ) (hx : 0 < x) (hx1 : x < 1 / 2) :
    HasDerivAt (fun y : ℝ ↦ arsech (2 * y)) (-1 / (x * Real.sqrt (1 - 4 * x ^ 2))) x := by
  have hf := (hasDerivAt_inverse_hyperbolic_secant (2 * x) (by linarith) (by linarith)).comp x
    ((hasDerivAt_id x).const_mul 2)
  apply hf.congr_deriv
  rw [show (2 * x) ^ 2 = 4 * x ^ 2 by ring]
  ring

/-- Bài 4.2.2(c): vi phân cấp hai của `arsech(2x)`. -/
theorem double_arsech_second_differential (x h : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt (deriv (fun y : ℝ ↦ arsech (2 * y)))
      ((1 - 8 * x ^ 2) / (x ^ 2 * Real.sqrt (1 - 4 * x ^ 2) ^ 3)) x ∧
    higherDifferential 2 (fun y : ℝ ↦ arsech (2 * y)) (Ioo (0 : ℝ) (1 / 2)) x h =
      ((1 - 8 * x ^ 2) / (x ^ 2 * Real.sqrt (1 - 4 * x ^ 2) ^ 3)) * h ^ 2 := by
  have hp : 0 < 1 - 4 * x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs0 : Real.sqrt (1 - 4 * x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hr : HasDerivAt (fun y : ℝ ↦ 1 - 4 * y ^ 2) (-8 * x) x := by
    convert! (((hasDerivAt_id x).pow 2).const_mul 4).const_sub 1 using 1
    norm_num [id_eq, Pi.pow_apply, Pi.mul_apply]
    ring
  have hs : HasDerivAt (fun y : ℝ ↦ Real.sqrt (1 - 4 * y ^ 2))
      (-4 * x / Real.sqrt (1 - 4 * x ^ 2)) x := by
    have hh := (Real.hasDerivAt_sqrt hp.ne').comp x hr
    apply hh.congr_deriv
    ring
  have hg : HasDerivAt (fun y : ℝ ↦ -1 / (y * Real.sqrt (1 - 4 * y ^ 2)))
      ((1 - 8 * x ^ 2) / (x ^ 2 * Real.sqrt (1 - 4 * x ^ 2) ^ 3)) x := by
    have hh := (hasDerivAt_const x (-1 : ℝ)).div ((hasDerivAt_id x).mul hs) (mul_ne_zero hx0 hs0)
    apply hh.congr_deriv
    simp only [Pi.mul_apply, id_eq, zero_mul, one_mul, zero_sub, neg_mul, neg_neg]
    field_simp [hx0, hs0]
    simp only [Real.sq_sqrt hp.le]
    ring
  have hf := hasDerivAt_deriv_of_local_formula isOpen_Ioo hx
    (fun y hy ↦ hasDerivAt_double_arsech y hy.1 hy.2) hg
  exact ⟨hf, secondDifferential_of_hasDerivAt_deriv isOpen_Ioo hx hf h⟩


theorem double_arsech_not_differentiable_endpoint :
    ¬ DifferentiableAt ℝ (fun x : ℝ ↦ arsech (2 * x)) (1 / 2) := by
  intro hf
  have hz : HasDerivAt (fun x : ℝ ↦ sech (arsech (2 * x))) 0 (1 / 2) := by
    have hh := (hasDerivAt_hyperbolic_secant (arsech (2 * (1 / 2 : ℝ)))).comp (1 / 2) hf.hasDerivAt
    simpa [Function.comp_def, arsech] using hh
  have he : (fun x : ℝ ↦ 2 * x) =ᶠ[𝓝[Iic (1 / 2 : ℝ)] (1 / 2)]
      (fun x ↦ sech (arsech (2 * x))) := by
    have hp : ∀ᶠ x : ℝ in 𝓝[Iic (1 / 2 : ℝ)] (1 / 2), 0 < x :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hp, self_mem_nhdsWithin] with x hx hx1
    change x ≤ 1 / 2 at hx1
    exact (sech_arsech (2 * x) (by linarith) (by linarith)).symm
  have hzero : HasDerivWithinAt (fun x : ℝ ↦ 2 * x) 0 (Iic (1 / 2)) (1 / 2) :=
    hz.hasDerivWithinAt.congr_of_eventuallyEq_of_mem he (by simp)
  have htwo : HasDerivWithinAt (fun x : ℝ ↦ 2 * x) 2 (Iic (1 / 2)) (1 / 2) :=
    by simpa only [mul_one, id_eq] using
      ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).hasDerivWithinAt
  have hh := UniqueDiffWithinAt.eq_deriv (Iic (1 / 2 : ℝ))
    (uniqueDiffWithinAt_Iic (1 / 2)) hzero htwo
  norm_num at hh


theorem hasDerivAt_fifth_arcoth (x : ℝ) (hx : 5 < |x|) :
    HasDerivAt (fun y : ℝ ↦ arcoth (y / 5)) (-5 / (x ^ 2 - 25)) x := by
  have hp : 1 < |x / 5| := by rw [abs_div]; norm_num; linarith
  have hd : x ^ 2 - 25 ≠ 0 := by
    have hsq : 25 < x ^ 2 := by nlinarith [sq_abs x]
    linarith
  have hf := (hasDerivAt_inverse_hyperbolic_cotangent (x / 5) hp).comp x ((hasDerivAt_id x).div_const 5)
  apply hf.congr_deriv
  have hd' : 25 - x ^ 2 ≠ 0 := by intro he; apply hd; linarith
  field_simp [hd]
  norm_num
  rw [div_eq_iff hd']
  ring

/-- Bài 4.2.2(d): vi phân cấp hai trên `|x| > 5`. -/
theorem fifth_arcoth_second_differential (x h : ℝ) (hx : 5 < |x|) :
    HasDerivAt (deriv (fun y : ℝ ↦ arcoth (y / 5))) (10 * x / (x ^ 2 - 25) ^ 2) x ∧
    higherDifferential 2 (fun y : ℝ ↦ arcoth (y / 5)) {y : ℝ | 5 < |y|} x h =
      (10 * x / (x ^ 2 - 25) ^ 2) * h ^ 2 := by
  have hd : x ^ 2 - 25 ≠ 0 := by
    have hp : 25 < x ^ 2 := by nlinarith [sq_abs x]
    linarith
  have hg : HasDerivAt (fun y : ℝ ↦ -5 / (y ^ 2 - 25)) (10 * x / (x ^ 2 - 25) ^ 2) x := by
    have hh := (hasDerivAt_const x (-5 : ℝ)).div (((hasDerivAt_id x).pow 2).sub_const 25) hd
    apply hh.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, zero_mul, zero_sub]
    ring
  have hI : IsOpen {y : ℝ | 5 < |y|} := isOpen_lt continuous_const continuous_abs
  have hf := hasDerivAt_deriv_of_local_formula hI hx (fun y hy ↦ hasDerivAt_fifth_arcoth y hy) hg
  exact ⟨hf, secondDifferential_of_hasDerivAt_deriv hI hx hf h⟩

end calculus.Chapter04.Section02SecondExercises
