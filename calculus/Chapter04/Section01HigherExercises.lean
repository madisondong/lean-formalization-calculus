import calculus.Chapter04.Section01HigherRules
import calculus.Chapter04.Section01LocalExercises
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith

/-!
# Bài 19,25,27,28: tính khả vi, hàm ghép và phương trình vi phân

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 640–642, 677–699. Phương trình cấp hai chỉ cần hàm khả vi hai lần.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01HigherExercises
open Filter Set calculus.Chapter04.Section01Higher calculus.Chapter04.Section01HigherRules
open scoped ContDiff Topology


def flatExponentialSquare (x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.exp (-1 / x ^ 2)


def flatExponentialPositive (x : ℝ) : ℝ :=
  if 0 < x then Real.exp (-1 / x) else 0


theorem flatExponentialPositive_eq_glue : flatExponentialPositive = expNegInvGlue := by
  funext x
  by_cases hx : 0 < x
  · simp [flatExponentialPositive, expNegInvGlue, hx, not_le.mpr hx, neg_div, one_div]
  · simp [flatExponentialPositive, expNegInvGlue, hx, le_of_not_gt hx]


theorem flatExponentialSquare_eq_glue_square :
    flatExponentialSquare = fun x : ℝ ↦ expNegInvGlue (x ^ 2) := by
  funext x
  by_cases hx : x = 0
  · simp [flatExponentialSquare, hx, expNegInvGlue.zero]
  · have hs : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp [flatExponentialSquare, expNegInvGlue, hx, not_le.mpr hs, neg_div, one_div]

/-- Bài 25(a): hàm trơn trên ℝ, kể cả tại điểm ghép 0. -/
theorem flatExponentialSquare_domainSmooth : DomainSmooth flatExponentialSquare univ := by
  apply (domainSmooth_iff_contDiffOn _ isOpen_univ).mpr
  rw [flatExponentialSquare_eq_glue_square]
  exact (expNegInvGlue.contDiff.comp (contDiff_id.pow 2)).contDiffOn

/-- Bài 25(b): khả vi ở mọi cấp trên ℝ, với nhánh trái bằng 0. -/
theorem flatExponentialPositive_domainSmooth : DomainSmooth flatExponentialPositive univ := by
  apply (domainSmooth_iff_contDiffOn _ isOpen_univ).mpr
  rw [flatExponentialPositive_eq_glue]
  exact expNegInvGlue.contDiff.contDiffOn


def exponentialOdeSolution (a b x : ℝ) : ℝ :=
  a * Real.exp (-x) + b * Real.exp (-2 * x)


theorem exponentialOdeSolution_hasDerivAt (a b x : ℝ) :
    HasDerivAt (exponentialOdeSolution a b)
      (-a * Real.exp (-x) - 2 * b * Real.exp (-2 * x)) x := by
  have h1 := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).const_mul a
  have h2 := ((Real.hasDerivAt_exp (-2 * x)).comp x
    ((hasDerivAt_id x).const_mul (-2))).const_mul b
  apply ((h1.add h2).congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  ring


theorem exponentialOdeSolution_deriv (a b : ℝ) :
    deriv (exponentialOdeSolution a b) =
      fun x ↦ -a * Real.exp (-x) - 2 * b * Real.exp (-2 * x) := by
  funext x
  exact (exponentialOdeSolution_hasDerivAt a b x).deriv


theorem exponentialOdeSolution_second_deriv (a b x : ℝ) :
    deriv (deriv (exponentialOdeSolution a b)) x =
      a * Real.exp (-x) + 4 * b * Real.exp (-2 * x) := by
  rw [exponentialOdeSolution_deriv]
  have h1 := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).const_mul (-a)
  have h2 := ((Real.hasDerivAt_exp (-2 * x)).comp x
    ((hasDerivAt_id x).const_mul (-2))).const_mul (2 * b)
  have hd : HasDerivAt
      (fun y : ℝ ↦ -a * Real.exp (-y) - 2 * b * Real.exp (-2 * y))
      (a * Real.exp (-x) + 4 * b * Real.exp (-2 * x)) x := by
    apply ((h1.sub h2).congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
    ring
  exact hd.deriv

/-- Bài 27: hàm thỏa phương trình `y″ + 3y′ + 2y = 0`. -/
theorem exponentialOdeSolution_equation (a b x : ℝ) :
    deriv (deriv (exponentialOdeSolution a b)) x +
      3 * deriv (exponentialOdeSolution a b) x + 2 * exponentialOdeSolution a b x = 0 := by
  rw [exponentialOdeSolution_second_deriv, exponentialOdeSolution_deriv]
  simp only [exponentialOdeSolution]
  ring

/-- Bài 28: nghiệm của `3f″ + 2f′ + f = 0` trơn trên miền mở. -/
theorem linear_second_order_domainSmooth {f : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hf : DifferentiableToOrderOn 2 f I)
    (heq : ∀ x ∈ I, 3 * deriv (deriv f) x + 2 * deriv f x + f x = 0) :
    DomainSmooth f I := by
  let d : ℝ → ℝ := derivWithin f I
  have hdval : EqOn d (deriv f) I := fun x hx ↦ derivWithin_of_isOpen hI hx
  have hbase := (differentiableToOrderOn_two f hI).mp hf
  have hdf : DifferentiableOn ℝ d I := hbase.2.congr hdval
  have hddval : EqOn (derivWithin d I)
      (fun x ↦ (-2 / 3 : ℝ) * d x + (-1 / 3 : ℝ) * f x) I := by
    intro x hx
    change derivWithin d I x = (-2 / 3 : ℝ) * d x + (-1 / 3 : ℝ) * f x
    have hder : derivWithin d I x = deriv (deriv f) x := by
      rw [derivWithin_congr hdval (hdval hx), derivWithin_of_isOpen hI hx]
    rw [hder, hdval hx]
    linarith [heq x hx]
  have hall : ∀ n : ℕ, DifferentiableToOrderOn n f I ∧ DifferentiableToOrderOn n d I := by
    intro n
    induction n with
    | zero => exact ⟨fun k hk ↦ (Nat.not_lt_zero k hk).elim,
        fun k hk ↦ (Nat.not_lt_zero k hk).elim⟩
    | succ n ih =>
      have hdnext := (source_add_higher n hI
        (source_const_mul_higher n ih.2 (-2 / 3)).1
        (source_const_mul_higher n ih.1 (-1 / 3)).1).1
      exact ⟨(differentiableToOrderOn_succ n f I).mpr ⟨hbase.1, ih.2⟩,
        (differentiableToOrderOn_succ n d I).mpr
          ⟨hdf, differentiableToOrderOn_congr n hddval.symm hdnext⟩⟩
  exact fun n ↦ (hall n).1

/-- Bài 28: nghiệm của `3f″ + 2f′ + f = 0` trơn trên `(a, b)`. -/
theorem linear_second_order_interval_domainSmooth (a b : ℝ) {f : ℝ → ℝ}
    (hf : DifferentiableToOrderOn 2 f (Ioo a b))
    (heq : ∀ x ∈ Ioo a b, 3 * deriv (deriv f) x + 2 * deriv f x + f x = 0) :
    DomainSmooth f (Ioo a b) := linear_second_order_domainSmooth isOpen_Ioo hf heq



def absoluteCube (x : ℝ) : ℝ := |x| ^ 3


theorem signed_absolute_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y * |y|) (2 * |x|) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h := (hasDerivAt_pow 2 x).neg
    apply (h.congr_deriv (by simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, abs_of_neg hx]; ring)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    change y * |y| = -(y ^ 2)
    rw [abs_of_neg (show y < 0 from hy)]
    ring
  · subst x
    simpa using calculus.Chapter04.Section01LocalExercises.signed_absolute_hasDerivAt_zero
  · have h := hasDerivAt_pow 2 x
    apply (h.congr_deriv (by simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, abs_of_pos hx])).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [abs_of_pos (show 0 < y from hy)]
    ring


theorem signed_absolute_deriv : deriv (fun y : ℝ ↦ y * |y|) = fun x ↦ 2 * |x| := by
  funext x
  exact (signed_absolute_hasDerivAt x).deriv


theorem signed_absolute_contDiff_one : ContDiff ℝ 1 (fun x : ℝ ↦ x * |x|) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x ↦ (signed_absolute_hasDerivAt x).differentiableAt, ?_⟩
  rw [signed_absolute_deriv]
  exact continuous_const.mul continuous_abs


theorem absoluteCube_hasDerivAt_zero : HasDerivAt absoluteCube 0 0 := by
  apply calculus.Chapter04.Section01LocalExercises.hasDerivAt_zero_of_slope_abs_le
  have hsmall : ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), |y| < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (continuous_abs.continuousAt.eventually (Iio_mem_nhds (show |(0 : ℝ)| < 1 by norm_num)))
  filter_upwards [self_mem_nhdsWithin, hsmall] with y hy hs
  simp only [absoluteCube, abs_zero, zero_pow (by decide : 3 ≠ 0), sub_zero, abs_div,
    abs_pow, abs_abs]
  have heq : |y| ^ 3 / |y| = |y| ^ 2 := by
    field_simp [abs_ne_zero.mpr (show y ≠ 0 from hy)]
  rw [heq]
  nlinarith [abs_nonneg y]


theorem absoluteCube_hasDerivAt (x : ℝ) : HasDerivAt absoluteCube (3 * x * |x|) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h := (hasDerivAt_pow 3 x).neg
    apply (h.congr_deriv (by simp only [Nat.cast_ofNat, Nat.reduceSub, abs_of_neg hx]; ring)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    change |y| ^ 3 = -(y ^ 3)
    rw [abs_of_neg (show y < 0 from hy)]
    ring
  · subst x
    simpa using absoluteCube_hasDerivAt_zero
  · have h := hasDerivAt_pow 3 x
    apply (h.congr_deriv (by simp only [Nat.cast_ofNat, Nat.reduceSub, abs_of_pos hx]; ring)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [absoluteCube, abs_of_pos (show 0 < y from hy)]


theorem absoluteCube_deriv : deriv absoluteCube = fun x ↦ 3 * (x * |x|) := by
  funext x
  rw [(absoluteCube_hasDerivAt x).deriv]
  ring


theorem absoluteCube_second_deriv : deriv (deriv absoluteCube) = fun x ↦ 6 * |x| := by
  rw [absoluteCube_deriv]
  funext x
  have h := (signed_absolute_hasDerivAt x).const_mul (3 : ℝ)
  convert h.deriv using 1
  ring

/-- Bài 19: `|x|³` thuộc `C²`. -/
theorem absoluteCube_domainC_two : DomainC 2 absoluteCube univ := by
  apply (domainC_iff_contDiffOn 2 _ isOpen_univ).mpr
  apply ContDiff.contDiffOn
  change ContDiff ℝ (1 + 1) absoluteCube
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun x ↦ (absoluteCube_hasDerivAt x).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · rw [absoluteCube_deriv]
    exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ (3 : ℝ))).mul
      signed_absolute_contDiff_one

/-- Bài 19: đạo hàm cấp ba không tồn tại tại 0, nên hàm không thuộc C³. -/
theorem absoluteCube_not_domainC_three : ¬ DomainC 3 absoluteCube univ := by
  intro hf
  have h3 : ContDiff ℝ 3 absoluteCube := contDiffOn_univ.mp
    ((domainC_iff_contDiffOn 3 _ isOpen_univ).mp hf)
  have h2 : ContDiff ℝ 2 (deriv absoluteCube) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (2 + 1) absoluteCube from h3)).2.2
  have h1 : ContDiff ℝ 1 (deriv (deriv absoluteCube)) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) (deriv absoluteCube) from h2)).2.2
  have hd := (contDiff_one_iff_deriv.mp h1).1 (0 : ℝ)
  rw [absoluteCube_second_deriv] at hd
  have hscaled := hd.const_mul (1 / 6 : ℝ)
  apply not_differentiableAt_abs_zero
  exact hscaled.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ by
    simp only
    ring)


/-- Bài 26: nghiệm của `f′ = g ∘ f` trơn trên `I` khi `g` trơn và `f(I) ⊆ I`. -/
theorem autonomous_equation_domainSmooth_repaired {f g : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hf : DifferentiableOn ℝ f I) (hg : DomainSmooth g I)
    (hmaps : MapsTo f I I) (heq : ∀ x ∈ I, deriv f x = g (f x)) : DomainSmooth f I := by
  apply (domainSmooth_iff_contDiffOn _ hI).mpr
  apply contDiffOn_infty.mpr
  have hgc := (domainSmooth_iff_contDiffOn g hI).mp hg
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = n + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen hI]
    refine ⟨hf, by simp, ?_⟩
    have hgcn : ContDiffOn ℝ n g I := hgc.of_le (WithTop.coe_le_coe.mpr le_top)
    exact (hgcn.comp ih hmaps).congr heq

end calculus.Chapter04.Section01HigherExercises
