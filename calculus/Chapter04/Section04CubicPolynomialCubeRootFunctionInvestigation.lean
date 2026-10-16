import calculus.Chapter04.Section04CurveInvestigationSourceIssues
import calculus.Chapter04.Section04AsymptoteClassificationSupport
import calculus.Chapter04.Section01Exercises
import calculus.Chapter03.Section03Exercises
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Convex.Deriv

/-!
# Ví dụ 4.4.25: căn bậc ba thực có dấu

Nguồn: Ví dụ 4.4.25. Tại điểm nhọn 1, hai độ dốc một bên tiến tới hai vô cùng trái dấu.
-/
noncomputable section
namespace calculus.Chapter04.Section04CubicPolynomialCubeRootFunctionInvestigation

set_option autoImplicit false

open Set Filter
open scoped Topology
open calculus.Chapter03.Section01Supplement (realCubeRoot)
open calculus.Chapter03.Section03Supplement
open calculus.Chapter03.Section03Exercises
open calculus.Chapter04.Section01Exercises
open calculus.Chapter04.Section01Derivatives
open calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04CurveInvestigationSourceIssues
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport

def cubicRadicand (x : ℝ) : ℝ := x^3 - 3*x + 2
def cubeRootCubeSubThreeXAddTwoFirstDeriv (x : ℝ) : ℝ := (x^2-1) / cubeRootCubeSubThreeXAddTwo x^2
def cubeRootCubeSubThreeXAddTwoSecondDeriv (x : ℝ) : ℝ := -2*(x-1)^2 / cubeRootCubeSubThreeXAddTwo x^5

theorem cubicRadicand_factor (x : ℝ) : cubicRadicand x = (x+2)*(x-1)^2 := by
  unfold cubicRadicand
  ring

theorem cubeRootCubeSubThreeXAddTwo_cube (x : ℝ) : cubeRootCubeSubThreeXAddTwo x^3 = cubicRadicand x :=
  signedCubeRoot_cube _

theorem signed_root_zero : signedCubeRoot 0 = 0 := signedCubeRoot_unique (by norm_num)

theorem signed_root_strictMono : StrictMono signedCubeRoot := by
  intro x y hxy
  apply (show Odd (3 : ℕ) by decide).pow_lt_pow.mp
  simpa only [signedCubeRoot_cube] using hxy

theorem signed_root_surjective : Function.Surjective signedCubeRoot := by
  intro y
  exact ⟨y^3, signedCubeRoot_unique rfl⟩

theorem signed_root_continuous : Continuous signedCubeRoot := by
  exact (signed_root_strictMono.orderIsoOfSurjective signedCubeRoot signed_root_surjective).continuous

theorem signed_root_hasDerivAt {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt signedCubeRoot (1/(3*signedCubeRoot u^2)) u := by
  have heq : signedCubeRoot = realCubeRoot := by
    funext x
    exact signedCubeRoot_unique (realCubeRoot_cubed x)
  rw [heq]
  exact hasDerivAt_realCubeRoot u hu

theorem cubicRadicand_hasDerivAt (x : ℝ) :
    HasDerivAt cubicRadicand (3*(x^2-1)) x := by
  have h := (((hasDerivAt_id x).fun_pow 3).sub
    ((hasDerivAt_id x).const_mul 3)).add_const 2
  apply h.congr_deriv
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
  ring

theorem cubeRootCubeSubThreeXAddTwo_continuous : Continuous cubeRootCubeSubThreeXAddTwo := by
  exact signed_root_continuous.comp (by unfold cubicRadicand; fun_prop : Continuous cubicRadicand)

theorem cubeRootCubeSubThreeXAddTwo_nonzero {x : ℝ} (hx2 : x ≠ -2) (hx1 : x ≠ 1) :
    cubeRootCubeSubThreeXAddTwo x ≠ 0 := by
  intro h
  have hc := cubeRootCubeSubThreeXAddTwo_cube x
  rw [h, zero_pow (by decide : 3 ≠ 0), cubicRadicand_factor] at hc
  exact (mul_ne_zero (by intro h; apply hx2; linarith : x+2≠0)
    (pow_ne_zero 2 (sub_ne_zero.mpr hx1))) hc.symm

theorem cubeRootCubeSubThreeXAddTwo_hasDerivAt {x : ℝ} (hx2 : x ≠ -2) (hx1 : x ≠ 1) :
    HasDerivAt cubeRootCubeSubThreeXAddTwo (cubeRootCubeSubThreeXAddTwoFirstDeriv x) x := by
  have hp : cubicRadicand x ≠ 0 := by
    rw [cubicRadicand_factor]
    exact mul_ne_zero (by intro h; apply hx2; linarith)
      (pow_ne_zero 2 (sub_ne_zero.mpr hx1))
  have h := (signed_root_hasDerivAt hp).comp x (cubicRadicand_hasDerivAt x)
  apply h.congr_deriv
  unfold cubeRootCubeSubThreeXAddTwoFirstDeriv
  change 1/(3*cubeRootCubeSubThreeXAddTwo x^2)*(3*(x^2-1)) = (x^2-1)/cubeRootCubeSubThreeXAddTwo x^2
  field_simp [cubeRootCubeSubThreeXAddTwo_nonzero hx2 hx1]

theorem cubeRootCubeSubThreeXAddTwo_second_hasDerivAt {x : ℝ} (hx2 : x ≠ -2) (hx1 : x ≠ 1) :
    HasDerivAt (deriv cubeRootCubeSubThreeXAddTwo) (cubeRootCubeSubThreeXAddTwoSecondDeriv x) x := by
  have hF := cubeRootCubeSubThreeXAddTwo_nonzero hx2 hx1
  have hd := (((hasDerivAt_id x).fun_pow 2).sub_const 1).div
    ((cubeRootCubeSubThreeXAddTwo_hasDerivAt hx2 hx1).fun_pow 2) (pow_ne_zero 2 hF)
  have hcoeff : (2*x*cubeRootCubeSubThreeXAddTwo x^2-(x^2-1)*(2*cubeRootCubeSubThreeXAddTwo x*cubeRootCubeSubThreeXAddTwoFirstDeriv x)) /
      (cubeRootCubeSubThreeXAddTwo x^2)^2 = cubeRootCubeSubThreeXAddTwoSecondDeriv x := by
    unfold cubeRootCubeSubThreeXAddTwoFirstDeriv cubeRootCubeSubThreeXAddTwoSecondDeriv
    field_simp
    have hc := cubeRootCubeSubThreeXAddTwo_cube x
    unfold cubicRadicand at hc
    nlinarith [congrArg (fun u : ℝ ↦ x*u) hc]
  have hD : HasDerivAt cubeRootCubeSubThreeXAddTwoFirstDeriv (cubeRootCubeSubThreeXAddTwoSecondDeriv x) x := by
    apply hd.congr_deriv
    simpa [cubeRootCubeSubThreeXAddTwoFirstDeriv] using hcoeff
  apply hD.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx2, eventually_ne_nhds hx1] with y hy2 hy1
  exact (cubeRootCubeSubThreeXAddTwo_hasDerivAt hy2 hy1).deriv

theorem cubeRootCubeSubThreeXAddTwo_root_factor (x : ℝ) :
    cubeRootCubeSubThreeXAddTwo x = signedCubeRoot (x+2) * signedCubeRoot (x-1)^2 := by
  apply (show Odd (3 : ℕ) by decide).pow_injective
  change cubeRootCubeSubThreeXAddTwo x^3 = (signedCubeRoot (x+2) * signedCubeRoot (x-1)^2)^3
  rw [cubeRootCubeSubThreeXAddTwo_cube, cubicRadicand_factor, mul_pow, ← pow_mul, mul_comm 2 3,
    pow_mul, signedCubeRoot_cube, signedCubeRoot_cube]


theorem cubeRootCubeSubThreeXAddTwo_derivatives_eq_source_formulas {x : ℝ} (hx2 : x ≠ -2) (hx1 : x ≠ 1) :
    deriv cubeRootCubeSubThreeXAddTwo x = (x+1)/signedCubeRoot ((x+2)^2*(x-1)) ∧
      deriv (deriv cubeRootCubeSubThreeXAddTwo) x =
        -2/(signedCubeRoot (x-1)^4 * signedCubeRoot (x+2)^5) := by
  have ha : signedCubeRoot (x+2) ≠ 0 := by
    intro h
    have hc := signedCubeRoot_cube (x+2)
    rw [h] at hc
    norm_num at hc
    exact hx2 (by linarith)
  have hb : signedCubeRoot (x-1) ≠ 0 := by
    intro h
    have hc := signedCubeRoot_cube (x-1)
    rw [h] at hc
    norm_num at hc
    exact hx1 (by linarith)
  have hr : signedCubeRoot ((x+2)^2*(x-1)) = signedCubeRoot (x+2)^2*signedCubeRoot (x-1) := by
    apply signedCubeRoot_unique
    rw [mul_pow, ← pow_mul, mul_comm 2 3, pow_mul, signedCubeRoot_cube, signedCubeRoot_cube]
  have hc := signedCubeRoot_cube (x-1)
  constructor
  · rw [(cubeRootCubeSubThreeXAddTwo_hasDerivAt hx2 hx1).deriv, cubeRootCubeSubThreeXAddTwoFirstDeriv,
      cubeRootCubeSubThreeXAddTwo_root_factor, hr]
    have hnum : x^2-1 = (x+1)*signedCubeRoot (x-1)^3 := by rw [hc]; ring
    rw [hnum]
    field_simp [ha,hb]
  · rw [(cubeRootCubeSubThreeXAddTwo_second_hasDerivAt hx2 hx1).deriv, cubeRootCubeSubThreeXAddTwoSecondDeriv,
      cubeRootCubeSubThreeXAddTwo_root_factor]
    have hnum : (x-1)^2 = signedCubeRoot (x-1)^6 := by
      calc
        (x-1)^2 = (signedCubeRoot (x-1)^3)^2 := congrArg (fun u : ℝ ↦ u^2) hc.symm
        _ = signedCubeRoot (x-1)^6 := by ring
    rw [hnum]
    field_simp [ha,hb]

theorem cubeRootCubeSubThreeXAddTwo_values : cubeRootCubeSubThreeXAddTwo (-2) = 0 ∧
    cubeRootCubeSubThreeXAddTwo (-1) = signedCubeRoot 4 ∧ cubeRootCubeSubThreeXAddTwo 1 = 0 ∧
    cubeRootCubeSubThreeXAddTwo 0 = signedCubeRoot 2 := by
  constructor
  · norm_num [cubeRootCubeSubThreeXAddTwo, signed_root_zero]
  constructor
  · norm_num [cubeRootCubeSubThreeXAddTwo]
  exact ⟨cubeRootCubeSubThreeXAddTwo_value_one, cubeRootCubeSubThreeXAddTwo_value_zero⟩

theorem cubeRootCubeSubThreeXAddTwo_zeros (x : ℝ) : cubeRootCubeSubThreeXAddTwo x = 0 ↔ x=-2 ∨ x=1 := by
  constructor
  · intro h
    have hc := cubeRootCubeSubThreeXAddTwo_cube x
    rw [h, zero_pow (by decide : 3≠0), cubicRadicand_factor] at hc
    rcases mul_eq_zero.mp hc.symm with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by have := eq_zero_of_pow_eq_zero h; linarith)
  · rintro (rfl | rfl)
    · exact cubeRootCubeSubThreeXAddTwo_values.1
    · exact cubeRootCubeSubThreeXAddTwo_value_one

theorem cubeRootCubeSubThreeXAddTwo_variation :
    StrictMonoOn cubeRootCubeSubThreeXAddTwo (Iic (-1 : ℝ)) ∧
      StrictAntiOn cubeRootCubeSubThreeXAddTwo (Icc (-1 : ℝ) 1) ∧
      StrictMonoOn cubeRootCubeSubThreeXAddTwo (Ici (1 : ℝ)) := by
  have hP : Continuous cubicRadicand := by unfold cubicRadicand; fun_prop
  have hi : StrictMonoOn cubicRadicand (Iic (-1 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic _) hP.continuousOn
    intro x hx
    rw [interior_Iic] at hx
    change x < -1 at hx
    rw [(cubicRadicand_hasDerivAt x).deriv]
    have hp : 0 < (x+1)*(x-1) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    nlinarith [hp]
  have hd : StrictAntiOn cubicRadicand (Icc (-1 : ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hP.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rcases hx with ⟨hxl,hxu⟩
    rw [(cubicRadicand_hasDerivAt x).deriv]
    nlinarith [mul_pos (by linarith : 0<x+1) (by linarith : 0<1-x)]
  have hr : StrictMonoOn cubicRadicand (Ici (1 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) hP.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    rw [(cubicRadicand_hasDerivAt x).deriv]
    have hp : 0 < (x+1)*(x-1) := mul_pos (by linarith) (by linarith)
    nlinarith [hp]
  exact ⟨fun x hx y hy hxy ↦ signed_root_strictMono (hi hx hy hxy),
    fun x hx y hy hxy ↦ signed_root_strictMono (hd hx hy hxy),
    fun x hx y hy hxy ↦ signed_root_strictMono (hr hx hy hxy)⟩

theorem cubeRootCubeSubThreeXAddTwo_local_extrema : IsLocalMax cubeRootCubeSubThreeXAddTwo (-1) ∧ IsLocalMin cubeRootCubeSubThreeXAddTwo 1 := by
  refine ⟨?_, cubeRootCubeSubThreeXAddTwo_local_minimum_one⟩
  change ∀ᶠ x in 𝓝 (-1 : ℝ), cubeRootCubeSubThreeXAddTwo x ≤ cubeRootCubeSubThreeXAddTwo (-1)
  filter_upwards [Iio_mem_nhds (by norm_num : (-1 : ℝ)<2)] with x hx
  change x < 2 at hx
  apply signed_root_strictMono.monotone
  change cubicRadicand x ≤ cubicRadicand (-1)
  unfold cubicRadicand
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x+1)) (by linarith : x-2≤0)]

theorem cubeRootCubeSubThreeXAddTwo_negative {x : ℝ} (hx : x < -2) : cubeRootCubeSubThreeXAddTwo x < 0 := by
  rw [← signed_root_zero]
  apply signed_root_strictMono
  change cubicRadicand x < 0
  rw [cubicRadicand_factor]
  exact mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero (by linarith))

theorem cubeRootCubeSubThreeXAddTwo_positive {x : ℝ} (hx : -2 < x) (hx1 : x ≠ 1) : 0 < cubeRootCubeSubThreeXAddTwo x := by
  rw [← signed_root_zero]
  apply signed_root_strictMono
  change 0 < cubicRadicand x
  rw [cubicRadicand_factor]
  exact mul_pos (by linarith) (sq_pos_of_ne_zero (sub_ne_zero.mpr hx1))

theorem cubeRootCubeSubThreeXAddTwo_second_signs {x : ℝ} (hx2 : x ≠ -2) (hx1 : x ≠ 1) :
    (x < -2 → 0 < deriv (deriv cubeRootCubeSubThreeXAddTwo) x) ∧
      (-2 < x → deriv (deriv cubeRootCubeSubThreeXAddTwo) x < 0) := by
  rw [(cubeRootCubeSubThreeXAddTwo_second_hasDerivAt hx2 hx1).deriv, cubeRootCubeSubThreeXAddTwoSecondDeriv]
  constructor
  · intro hx
    exact div_pos_of_neg_of_neg (by nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hx1)])
      ((show Odd (5 : ℕ) by decide).pow_neg_iff.mpr (cubeRootCubeSubThreeXAddTwo_negative hx))
  · intro hx
    exact div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hx1)])
      (pow_pos (cubeRootCubeSubThreeXAddTwo_positive hx hx1) 5)

theorem cubeRootCubeSubThreeXAddTwo_convexity : StrictConvexOn ℝ (Iio (-2 : ℝ)) cubeRootCubeSubThreeXAddTwo ∧
    StrictConcaveOn ℝ (Ioo (-2 : ℝ) 1) cubeRootCubeSubThreeXAddTwo ∧
    StrictConcaveOn ℝ (Ioi (1 : ℝ)) cubeRootCubeSubThreeXAddTwo := by
  refine ⟨?_, ?_, ?_⟩
  · apply strictConvexOn_of_deriv2_pos (convex_Iio _) cubeRootCubeSubThreeXAddTwo_continuous.continuousOn
    intro x hx
    rw [isOpen_Iio.interior_eq] at hx
    change x < -2 at hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      (cubeRootCubeSubThreeXAddTwo_second_signs (by linarith : x≠-2) (by linarith : x≠1)).1 hx
  · apply strictConcaveOn_of_deriv2_neg (convex_Ioo _ _) cubeRootCubeSubThreeXAddTwo_continuous.continuousOn
    intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      (cubeRootCubeSubThreeXAddTwo_second_signs (ne_of_gt hx.1) (ne_of_lt hx.2)).2 hx.1
  · apply strictConcaveOn_of_deriv2_neg (convex_Ioi _) cubeRootCubeSubThreeXAddTwo_continuous.continuousOn
    intro x hx
    rw [isOpen_Ioi.interior_eq] at hx
    change 1 < x at hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      (cubeRootCubeSubThreeXAddTwo_second_signs (by linarith : x≠-2) (ne_of_gt hx)).2 (by linarith)


theorem cubeRootCubeSubThreeXAddTwo_secant_neg_two {x : ℝ} (hx2 : x ≠ -2) (hx1 : x ≠ 1) :
    (cubeRootCubeSubThreeXAddTwo x-cubeRootCubeSubThreeXAddTwo (-2))/(x-(-2)) = (x-1)^2/cubeRootCubeSubThreeXAddTwo x^2 := by
  rw [cubeRootCubeSubThreeXAddTwo_values.1, sub_zero]
  have hd : x-(-2) ≠ 0 := sub_ne_zero.mpr hx2
  apply (div_eq_div_iff hd (pow_ne_zero 2 (cubeRootCubeSubThreeXAddTwo_nonzero hx2 hx1))).mpr
  have hc := cubeRootCubeSubThreeXAddTwo_cube x
  rw [cubicRadicand_factor] at hc
  nlinarith


theorem cubeRootCubeSubThreeXAddTwo_neg_two_slope_top :
    Tendsto (fun x : ℝ ↦ (cubeRootCubeSubThreeXAddTwo x-cubeRootCubeSubThreeXAddTwo (-2))/(x-(-2)))
      (𝓝[≠] (-2 : ℝ)) atTop := by
  have hf : Tendsto cubeRootCubeSubThreeXAddTwo (𝓝[≠] (-2 : ℝ)) (𝓝 0) := by
    simpa only [cubeRootCubeSubThreeXAddTwo_values.1] using
      (cubeRootCubeSubThreeXAddTwo_continuous.continuousAt (x := (-2 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (-2 : ℝ) ≤ 𝓝 (-2 : ℝ))
  have hp : ∀ᶠ x : ℝ in 𝓝[≠] (-2 : ℝ), 0 < cubeRootCubeSubThreeXAddTwo x^2 := by
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[≠] (-2 : ℝ), x≠-2),
      (eventually_ne_nhds (by norm_num : (-2 : ℝ)≠1)).filter_mono nhdsWithin_le_nhds] with x hx2 hx1
    exact sq_pos_of_ne_zero (cubeRootCubeSubThreeXAddTwo_nonzero hx2 hx1)
  have hs : Tendsto (fun x : ℝ ↦ cubeRootCubeSubThreeXAddTwo x^2) (𝓝[≠] (-2 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [zero_pow (by decide : 2≠0)] using hf.pow 2, hp⟩
  have hi := tendsto_inv_nhdsGT_zero.comp hs
  have hn : Tendsto (fun x : ℝ ↦ (x-1)^2) (𝓝[≠] (-2 : ℝ)) (𝓝 (9 : ℝ)) := by
    have hc : Continuous (fun x : ℝ ↦ (x-1)^2) := by fun_prop
    convert (hc.tendsto (-2 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (-2 : ℝ) ≤ 𝓝 (-2 : ℝ)) using 1
    norm_num
  apply (hn.pos_mul_atTop (by norm_num) hi).congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[≠] (-2 : ℝ), x≠-2),
    (eventually_ne_nhds (by norm_num : (-2 : ℝ)≠1)).filter_mono nhdsWithin_le_nhds] with x hx2 hx1
  simpa only [div_eq_mul_inv, Function.comp_def] using (cubeRootCubeSubThreeXAddTwo_secant_neg_two hx2 hx1).symm

theorem cubeRootCubeSubThreeXAddTwo_infinite_derivative_neg_two :
    HasInfiniteDerivativeWithinAt cubeRootCubeSubThreeXAddTwo (Ioo (-3) (-1)) (-2) := by
  apply Or.inl
  exact cubeRootCubeSubThreeXAddTwo_neg_two_slope_top.mono_left
    (nhdsWithin_mono _ (fun _ hx ↦ hx.2))


theorem cubeRootCubeSubThreeXAddTwo_secant_one {x : ℝ} (hx : x ≠ 1) :
    (cubeRootCubeSubThreeXAddTwo x-cubeRootCubeSubThreeXAddTwo 1)/(x-1) = signedCubeRoot ((x+2)/(x-1)) := by
  rw [cubeRootCubeSubThreeXAddTwo_value_one, sub_zero]
  symm
  apply signedCubeRoot_unique
  rw [div_pow, cubeRootCubeSubThreeXAddTwo_cube, cubicRadicand_factor]
  field_simp [show x-1≠0 from sub_ne_zero.mpr hx]

theorem signed_root_top : Tendsto signedCubeRoot atTop atTop :=
  (signed_root_strictMono.orderIsoOfSurjective signedCubeRoot signed_root_surjective).tendsto_atTop

theorem signed_root_bot : Tendsto signedCubeRoot atBot atBot :=
  (signed_root_strictMono.orderIsoOfSurjective signedCubeRoot signed_root_surjective).tendsto_atBot


theorem cubeRootCubeSubThreeXAddTwo_cusp_at_one :
    Tendsto (fun x : ℝ ↦ (cubeRootCubeSubThreeXAddTwo x-cubeRootCubeSubThreeXAddTwo 1)/(x-1)) (𝓝[<] (1 : ℝ)) atBot ∧
      Tendsto (fun x : ℝ ↦ (cubeRootCubeSubThreeXAddTwo x-cubeRootCubeSubThreeXAddTwo 1)/(x-1)) (𝓝[>] (1 : ℝ)) atTop := by
  have hsub : Tendsto (fun x : ℝ ↦ x-1) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : Continuous (fun x : ℝ ↦ x-1) := by fun_prop
    simpa only [sub_self] using hc.tendsto (1 : ℝ)
  have hadd : Tendsto (fun x : ℝ ↦ x+2) (𝓝 (1 : ℝ)) (𝓝 (3 : ℝ)) := by
    have hc : Continuous (fun x : ℝ ↦ x+2) := by fun_prop
    convert hc.tendsto (1 : ℝ) using 1
    norm_num
  have hsR : Tendsto (fun x : ℝ ↦ x-1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · exact hsub.mono_left nhdsWithin_le_nhds
    · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), 1<x)] with x hx
      change 1 < x at hx
      exact sub_pos.mpr hx
  have hsL : Tendsto (fun x : ℝ ↦ x-1) (𝓝[<] (1 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · exact hsub.mono_left nhdsWithin_le_nhds
    · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), x<1)] with x hx
      change x < 1 at hx
      exact sub_neg.mpr hx
  have hnR : Tendsto (fun x : ℝ ↦ x+2) (𝓝[>] (1 : ℝ)) (𝓝 (3 : ℝ)) := by
    exact hadd.mono_left nhdsWithin_le_nhds
  have hnL : Tendsto (fun x : ℝ ↦ x+2) (𝓝[<] (1 : ℝ)) (𝓝 (3 : ℝ)) := by
    exact hadd.mono_left nhdsWithin_le_nhds
  constructor
  · apply (signed_root_bot.comp (hnL.pos_mul_atBot (by norm_num) (tendsto_inv_nhdsLT_zero.comp hsL))).congr'
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), x<1)] with x hx
    simpa only [Function.comp_def, div_eq_mul_inv] using (cubeRootCubeSubThreeXAddTwo_secant_one (ne_of_lt hx)).symm
  · apply (signed_root_top.comp (hnR.pos_mul_atTop (by norm_num) (tendsto_inv_nhdsGT_zero.comp hsR))).congr'
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), 1<x)] with x hx
    simpa only [Function.comp_def, div_eq_mul_inv] using (cubeRootCubeSubThreeXAddTwo_secant_one (ne_of_gt hx)).symm

theorem cubeRootCubeSubThreeXAddTwo_no_two_sided_infinite_derivative_one :
    ¬ HasInfiniteDerivativeWithinAt cubeRootCubeSubThreeXAddTwo univ 1 := by
  intro h
  rcases h with ht | hb
  · have hh := ht.mono_left (nhdsWithin_mono (1 : ℝ) (show Iio (1 : ℝ) ⊆ univ \ {(1 : ℝ)} from
      fun x hx ↦ ⟨mem_univ x, by simpa using ne_of_lt hx⟩))
    exact cubeRootCubeSubThreeXAddTwo_cusp_at_one.1.not_tendsto disjoint_atBot_atTop hh
  · have hh := hb.mono_left (nhdsWithin_mono (1 : ℝ) (show Ioi (1 : ℝ) ⊆ univ \ {(1 : ℝ)} from
      fun x hx ↦ ⟨mem_univ x, by simpa using ne_of_gt hx⟩))
    exact cubeRootCubeSubThreeXAddTwo_cusp_at_one.2.not_tendsto disjoint_atTop_atBot hh


theorem cubeRootCubeSubThreeXAddTwo_vertical_secant_directions :
    Tendsto (fun x : ℝ ↦ (x-(-2))/(cubeRootCubeSubThreeXAddTwo x-cubeRootCubeSubThreeXAddTwo (-2)))
      (𝓝[≠] (-2 : ℝ)) (𝓝 0) ∧
    Tendsto (fun x : ℝ ↦ (x-1)/(cubeRootCubeSubThreeXAddTwo x-cubeRootCubeSubThreeXAddTwo 1))
      (𝓝[≠] (1 : ℝ)) (𝓝 0) := by
  constructor
  · simpa only [Pi.inv_def, inv_div] using cubeRootCubeSubThreeXAddTwo_neg_two_slope_top.inv_tendsto_atTop
  · rw [← nhdsLT_sup_nhdsGT (1 : ℝ), tendsto_sup]
    constructor
    · simpa only [Pi.inv_def, inv_div] using cubeRootCubeSubThreeXAddTwo_cusp_at_one.1.inv_tendsto_atBot
    · simpa only [Pi.inv_def, inv_div] using cubeRootCubeSubThreeXAddTwo_cusp_at_one.2.inv_tendsto_atTop

theorem cubeRootCubeSubThreeXAddTwo_source_inflection_neg_two : SourceInflectionOn cubeRootCubeSubThreeXAddTwo (-3) (-1) (-2) := by
  have htwice {a b : ℝ} (hD : Ioo a b ⊆ {x : ℝ | x≠-2 ∧ x≠1}) :
      DifferentiableToOrderOn 2 cubeRootCubeSubThreeXAddTwo (Ioo a b) := by
    apply (differentiableToOrderOn_two cubeRootCubeSubThreeXAddTwo isOpen_Ioo).mpr
    exact ⟨fun x hx ↦ (cubeRootCubeSubThreeXAddTwo_hasDerivAt (hD hx).1 (hD hx).2).differentiableAt.differentiableWithinAt,
      fun x hx ↦ (cubeRootCubeSubThreeXAddTwo_second_hasDerivAt (hD hx).1 (hD hx).2).differentiableAt.differentiableWithinAt⟩
  have hl := htwice (a:=(-3)) (b:=(-2)) (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  have hr := htwice (a:=(-2)) (b:=(-1)) (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  convert sourceInflectionOn_of_second_deriv_pos_neg
    (x₀:=(-2 : ℝ)) (δ:=1) (by norm_num)
    (by convert hl using 1; norm_num) (by convert hr using 1; norm_num)
    (Or.inr (by convert cubeRootCubeSubThreeXAddTwo_infinite_derivative_neg_two using 1; norm_num))
    (fun x hx ↦ (cubeRootCubeSubThreeXAddTwo_second_signs (by linarith [hx.2]) (by linarith [hx.2])).1 (by linarith [hx.2]))
    (fun x hx ↦ (cubeRootCubeSubThreeXAddTwo_second_signs (by linarith [hx.1]) (by linarith [hx.2])).2 (by linarith [hx.1])) using 1 <;> norm_num


theorem cubeRootCubeSubThreeXAddTwo_ratio_identity {x : ℝ} (hx : x≠0) :
    cubeRootCubeSubThreeXAddTwo x/x = signedCubeRoot (1-3*(x⁻¹)^2+2*(x⁻¹)^3) := by
  symm
  apply signedCubeRoot_unique
  rw [div_pow, cubeRootCubeSubThreeXAddTwo_cube]
  unfold cubicRadicand
  field_simp [hx]

theorem cubeRootCubeSubThreeXAddTwo_ratio_limit {l : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ x⁻¹) l (𝓝 0)) (hn : ∀ᶠ x : ℝ in l, x≠0) :
    Tendsto (fun x : ℝ ↦ cubeRootCubeSubThreeXAddTwo x/x) l (𝓝 (1 : ℝ)) := by
  have harg : Tendsto (fun x : ℝ ↦ 1-3*(x⁻¹)^2+2*(x⁻¹)^3) l (𝓝 (1 : ℝ)) := by
    convert (tendsto_const_nhds.sub ((hi.pow 2).const_mul 3)).add ((hi.pow 3).const_mul 2) using 1
    norm_num
  have hroot1 : signedCubeRoot 1 = 1 := signedCubeRoot_unique (by norm_num)
  have h := (signed_root_continuous.tendsto 1).comp harg
  rw [hroot1] at h
  apply h.congr'
  filter_upwards [hn] with x hx
  exact (cubeRootCubeSubThreeXAddTwo_ratio_identity hx).symm

theorem cubeRootCubeSubThreeXAddTwo_residual_identity {x : ℝ} (hx : x≠0) :
    cubeRootCubeSubThreeXAddTwo x-x = (-3*x⁻¹+2*(x⁻¹)^2) /
      ((cubeRootCubeSubThreeXAddTwo x/x)^2+cubeRootCubeSubThreeXAddTwo x/x+1) := by
  have hd : (cubeRootCubeSubThreeXAddTwo x/x)^2+cubeRootCubeSubThreeXAddTwo x/x+1≠0 := by
    nlinarith [sq_nonneg (cubeRootCubeSubThreeXAddTwo x/x+1/2)]
  apply (eq_div_iff hd).mpr
  have hc := cubeRootCubeSubThreeXAddTwo_cube x
  unfold cubicRadicand at hc
  field_simp [hx]
  nlinarith

theorem cubeRootCubeSubThreeXAddTwo_residual_limit {l : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ x⁻¹) l (𝓝 0)) (hn : ∀ᶠ x : ℝ in l, x≠0) :
    Tendsto (fun x : ℝ ↦ cubeRootCubeSubThreeXAddTwo x-x) l (𝓝 (0 : ℝ)) := by
  have hr := cubeRootCubeSubThreeXAddTwo_ratio_limit hi hn
  have hnum : Tendsto (fun x : ℝ ↦ -3*x⁻¹+2*(x⁻¹)^2) l (𝓝 (0 : ℝ)) := by
    convert (hi.const_mul (-3)).add ((hi.pow 2).const_mul 2) using 1 ; norm_num
  have hden : Tendsto (fun x : ℝ ↦ (cubeRootCubeSubThreeXAddTwo x/x)^2+cubeRootCubeSubThreeXAddTwo x/x+1) l (𝓝 (3 : ℝ)) := by
    convert ((hr.pow 2).add hr).add_const 1 using 1 ; norm_num
  have h : Tendsto (fun x : ℝ ↦ (-3*x⁻¹+2*(x⁻¹)^2) /
      ((cubeRootCubeSubThreeXAddTwo x/x)^2+cubeRootCubeSubThreeXAddTwo x/x+1)) l (𝓝 (0 : ℝ)) := by
    simpa only [Pi.div_apply, zero_div] using! hnum.div hden (by norm_num : (3 : ℝ)≠0)
  apply h.congr'
  filter_upwards [hn] with x hx
  exact (cubeRootCubeSubThreeXAddTwo_residual_identity hx).symm

theorem cubeRootCubeSubThreeXAddTwo_end_limits :
    Tendsto cubeRootCubeSubThreeXAddTwo atTop atTop ∧ Tendsto cubeRootCubeSubThreeXAddTwo atBot atBot ∧
      Tendsto (fun x : ℝ ↦ cubeRootCubeSubThreeXAddTwo x/x) atTop (𝓝 1) ∧
      Tendsto (fun x : ℝ ↦ cubeRootCubeSubThreeXAddTwo x/x) atBot (𝓝 1) ∧
      Tendsto (fun x : ℝ ↦ cubeRootCubeSubThreeXAddTwo x-x) atTop (𝓝 0) ∧
      Tendsto (fun x : ℝ ↦ cubeRootCubeSubThreeXAddTwo x-x) atBot (𝓝 0) := by
  have hnt : ∀ᶠ x : ℝ in atTop, x≠0 := (eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ ne_of_gt hx
  have hnb : ∀ᶠ x : ℝ in atBot, x≠0 := (eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ ne_of_lt hx
  have ht := cubeRootCubeSubThreeXAddTwo_ratio_limit tendsto_inv_atTop_zero hnt
  have hb := cubeRootCubeSubThreeXAddTwo_ratio_limit tendsto_inv_atBot_zero hnb
  refine ⟨?_, ?_, ht, hb, cubeRootCubeSubThreeXAddTwo_residual_limit tendsto_inv_atTop_zero hnt,
    cubeRootCubeSubThreeXAddTwo_residual_limit tendsto_inv_atBot_zero hnb⟩
  · apply (ht.pos_mul_atTop (by norm_num) tendsto_id).congr'
    filter_upwards [hnt] with x hx
    exact div_mul_cancel₀ _ hx
  · apply (hb.pos_mul_atBot (by norm_num) tendsto_id).congr'
    filter_upwards [hnb] with x hx
    exact div_mul_cancel₀ _ hx

theorem cubeRootCubeSubThreeXAddTwo_asymptote_classification (m b : ℝ) :
    HasObliqueAsymptote cubeRootCubeSubThreeXAddTwo m b ↔ m=1 ∧ b=0 := by
  have hnt : ∀ᶠ x : ℝ in atTop, x≠0 := (eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ ne_of_gt hx
  have hnb : ∀ᶠ x : ℝ in atBot, x≠0 := (eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ ne_of_lt hx
  constructor
  · rintro ⟨_, ht | hb⟩
    · have h := (affine_residual_limit_iff tendsto_inv_atTop_zero hnt cubeRootCubeSubThreeXAddTwo m b).mp ht
      have hm : m=1 := tendsto_nhds_unique h.1 cubeRootCubeSubThreeXAddTwo_end_limits.2.2.1
      subst m
      have hz : b=0 := tendsto_nhds_unique (by simpa using h.2) cubeRootCubeSubThreeXAddTwo_end_limits.2.2.2.2.1
      exact ⟨rfl,hz⟩
    · have h := (affine_residual_limit_iff tendsto_inv_atBot_zero hnb cubeRootCubeSubThreeXAddTwo m b).mp hb
      have hm : m=1 := tendsto_nhds_unique h.1 cubeRootCubeSubThreeXAddTwo_end_limits.2.2.2.1
      subst m
      have hz : b=0 := tendsto_nhds_unique (by simpa using h.2) cubeRootCubeSubThreeXAddTwo_end_limits.2.2.2.2.2
      exact ⟨rfl,hz⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨by norm_num, Or.inl (by simpa using cubeRootCubeSubThreeXAddTwo_end_limits.2.2.2.2.1)⟩

theorem cubeRootCubeSubThreeXAddTwo_no_horizontal (b : ℝ) : ¬ HasHorizontalAsymptote cubeRootCubeSubThreeXAddTwo b := by
  rintro (ht | hb)
  · exact not_tendsto_atTop_of_tendsto_nhds ht cubeRootCubeSubThreeXAddTwo_end_limits.1
  · exact not_tendsto_atBot_of_tendsto_nhds hb cubeRootCubeSubThreeXAddTwo_end_limits.2.1

theorem cubeRootCubeSubThreeXAddTwo_no_vertical (a : ℝ) : ¬ HasVerticalAsymptoteWithinAt cubeRootCubeSubThreeXAddTwo univ a :=
  no_vertical_of_continuousAt cubeRootCubeSubThreeXAddTwo_continuous.continuousAt

theorem cubeRootCubeSubThreeXAddTwo_source_asymptotes (m b : ℝ) :
    (HasObliqueAsymptoteWithin cubeRootCubeSubThreeXAddTwo univ m b ↔ m=1 ∧ b=0) ∧
      ¬ HasHorizontalAsymptoteWithin cubeRootCubeSubThreeXAddTwo univ b ∧
      (∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt cubeRootCubeSubThreeXAddTwo univ a) := by
  have hT : ∀ᶠ x : ℝ in atTop, x∈(univ : Set ℝ) := Eventually.of_forall mem_univ
  have hB : ∀ᶠ x : ℝ in atBot, x∈(univ : Set ℝ) := Eventually.of_forall mem_univ
  refine ⟨?_, ?_, cubeRootCubeSubThreeXAddTwo_no_vertical⟩
  · rw [full_tail_oblique_iff hT hB]
    exact cubeRootCubeSubThreeXAddTwo_asymptote_classification m b
  · rw [full_tail_horizontal_iff hT hB]
    exact cubeRootCubeSubThreeXAddTwo_no_horizontal b

theorem cubeRootCubeSubThreeXAddTwo_position_relative_oblique (x : ℝ) :
    (cubeRootCubeSubThreeXAddTwo x=x ↔ x=2/3) ∧
      (x<cubeRootCubeSubThreeXAddTwo x ↔ x<2/3) ∧ (cubeRootCubeSubThreeXAddTwo x<x ↔ 2/3<x) := by
  have ho : Odd (3 : ℕ) := by decide
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      have hc := cubeRootCubeSubThreeXAddTwo_cube x
      rw [h] at hc
      unfold cubicRadicand at hc
      linarith
    · intro h
      subst x
      apply signedCubeRoot_unique
      norm_num
  · rw [← ho.pow_lt_pow, cubeRootCubeSubThreeXAddTwo_cube]
    unfold cubicRadicand
    constructor <;> intro h <;> linarith
  · rw [← ho.pow_lt_pow, cubeRootCubeSubThreeXAddTwo_cube]
    unfold cubicRadicand
    constructor <;> intro h <;> linarith

end calculus.Chapter04.Section04CubicPolynomialCubeRootFunctionInvestigation
