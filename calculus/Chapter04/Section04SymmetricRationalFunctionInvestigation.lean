import calculus.Chapter04.Section04RationalFunctionInvestigationSupport
import calculus.Chapter04.Section04AsymptoteCollectionExercises

/-!
# Bài 4.4.14(a): khảo sát 2x²/(x²−1)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2758–2761.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04SymmetricRationalFunctionInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03
open calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04RationalFunctionInvestigationSupport
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport
open calculus.Chapter04.Section04AsymptoteCollectionExercises


def twoMulSquareDivSquareSubOne (x : ℝ) : ℝ := 2 * x ^ 2 / (x ^ 2 - 1)


def twoMulSquareDivSquareSubOneDomain : Set ℝ := {x | x ^ 2 - 1 ≠ 0}

def twoMulSquareDivSquareSubOneFirstDeriv (x : ℝ) : ℝ := -4 * x / (x ^ 2 - 1) ^ 2

def twoMulSquareDivSquareSubOneSecondDeriv (x : ℝ) : ℝ := 4 * (3 * x ^ 2 + 1) / (x ^ 2 - 1) ^ 3

theorem twoMulSquareDivSquareSubOne_domain_iff (x : ℝ) :
    x ∈ twoMulSquareDivSquareSubOneDomain ↔ x ≠ -1 ∧ x ≠ 1 := by
  change x ^ 2 - 1 ≠ 0 ↔ _
  constructor
  · intro h
    constructor <;> intro hx <;> subst x <;> norm_num at h
  · rintro ⟨hl, hr⟩ hz
    have hf : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · exact hr (by linarith)
    · exact hl (by linarith)

theorem twoMulSquareDivSquareSubOne_domain_open : IsOpen twoMulSquareDivSquareSubOneDomain := by
  exact isOpen_ne.preimage ((continuous_id.pow 2).sub continuous_const)

theorem twoMulSquareDivSquareSubOne_hasDerivAt {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    HasDerivAt twoMulSquareDivSquareSubOne (twoMulSquareDivSquareSubOneFirstDeriv x) x := by
  have h := (((hasDerivAt_id x).fun_pow 2).const_mul 2).div
    (((hasDerivAt_id x).fun_pow 2).sub_const 1) hx
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  apply h.congr_deriv
  dsimp only [twoMulSquareDivSquareSubOneFirstDeriv]
  field_simp [hx]
  ring

theorem twoMulSquareDivSquareSubOneFirstDeriv_hasDerivAt {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    HasDerivAt twoMulSquareDivSquareSubOneFirstDeriv (twoMulSquareDivSquareSubOneSecondDeriv x) x := by
  have h := ((hasDerivAt_id x).const_mul (-4)).div
    ((((hasDerivAt_id x).fun_pow 2).sub_const 1).fun_pow 2) (pow_ne_zero 2 hx)
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  apply h.congr_deriv
  dsimp only [twoMulSquareDivSquareSubOneSecondDeriv]
  field_simp [hx]
  ring

theorem twoMulSquareDivSquareSubOne_second_hasDerivAt {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    HasDerivAt (deriv twoMulSquareDivSquareSubOne) (twoMulSquareDivSquareSubOneSecondDeriv x) x :=
  hasDerivAt_deriv_of_open_formula twoMulSquareDivSquareSubOne_domain_open hx
    (fun _ hy ↦ twoMulSquareDivSquareSubOne_hasDerivAt hy) (twoMulSquareDivSquareSubOneFirstDeriv_hasDerivAt hx)

theorem twoMulSquareDivSquareSubOne_deriv {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    deriv twoMulSquareDivSquareSubOne x = twoMulSquareDivSquareSubOneFirstDeriv x := (twoMulSquareDivSquareSubOne_hasDerivAt hx).deriv

theorem twoMulSquareDivSquareSubOne_second_deriv {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    deriv (deriv twoMulSquareDivSquareSubOne) x = twoMulSquareDivSquareSubOneSecondDeriv x :=
  (twoMulSquareDivSquareSubOne_second_hasDerivAt hx).deriv

theorem twoMulSquareDivSquareSubOne_second_continuousAt {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    ContinuousAt (deriv (deriv twoMulSquareDivSquareSubOne)) x := by
  have h : ContinuousAt twoMulSquareDivSquareSubOneSecondDeriv x := by
    unfold twoMulSquareDivSquareSubOneSecondDeriv
    fun_prop (disch := exact pow_ne_zero 3 hx)
  apply h.congr_of_eventuallyEq
  filter_upwards [twoMulSquareDivSquareSubOne_domain_open.mem_nhds hx] with y hy
  exact twoMulSquareDivSquareSubOne_second_deriv hy

theorem twoMulSquareDivSquareSubOne_derivative_signs {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    (0 < deriv twoMulSquareDivSquareSubOne x ↔ x < 0) ∧
      (deriv twoMulSquareDivSquareSubOne x < 0 ↔ 0 < x) ∧
      (deriv twoMulSquareDivSquareSubOne x = 0 ↔ x = 0) := by
  rw [twoMulSquareDivSquareSubOne_deriv hx]
  have hd : 0 < (x ^ 2 - 1) ^ 2 := sq_pos_of_ne_zero hx
  unfold twoMulSquareDivSquareSubOneFirstDeriv
  constructor
  · rw [lt_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  constructor
  · rw [div_lt_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact False.elim ((pow_ne_zero 2 hx) h)
    · rintro rfl
      exact Or.inl (by norm_num)

theorem twoMulSquareDivSquareSubOne_second_signs {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    (0 < deriv (deriv twoMulSquareDivSquareSubOne) x ↔ 1 < x ^ 2) ∧
      (deriv (deriv twoMulSquareDivSquareSubOne) x < 0 ↔ x ^ 2 < 1) ∧
      deriv (deriv twoMulSquareDivSquareSubOne) x ≠ 0 := by
  rw [twoMulSquareDivSquareSubOne_second_deriv hx]
  have hn : 0 < 4 * (3 * x ^ 2 + 1) := by nlinarith [sq_nonneg x]
  unfold twoMulSquareDivSquareSubOneSecondDeriv
  have hp : 0 < (x ^ 2 - 1) ^ 3 ↔ 1 < x ^ 2 := by
    constructor
    · intro h
      by_contra hn'
      have hle : x ^ 2 - 1 ≤ 0 := by linarith
      have hc : (x ^ 2 - 1) ^ 3 ≤ 0 := by
        rw [pow_succ]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
      exact h.not_ge hc
    · intro h
      exact pow_pos (by linarith) 3
  have hm : (x ^ 2 - 1) ^ 3 < 0 ↔ x ^ 2 < 1 := by
    constructor
    · intro h
      by_contra hn'
      have hc := pow_nonneg (show 0 ≤ x ^ 2 - 1 by linarith) 3
      exact h.not_ge hc
    · intro h
      rw [pow_succ]
      exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hx) (by linarith)
  refine ⟨(div_pos_iff_of_pos_left hn).trans hp, ?_, div_ne_zero hn.ne' (pow_ne_zero 3 hx)⟩
  constructor
  · intro h
    rcases div_neg_iff.mp h with ⟨_, hneg⟩ | ⟨hneg, _⟩
    · exact hm.mp hneg
    · exact False.elim (hn.not_ge hneg.le)
  · intro h
    exact div_neg_of_pos_of_neg hn (hm.mpr h)

theorem twoMulSquareDivSquareSubOne_variation :
    StrictMonoOn twoMulSquareDivSquareSubOne (Iio (-1 : ℝ)) ∧
      StrictMonoOn twoMulSquareDivSquareSubOne (Ioo (-1 : ℝ) 0) ∧
      StrictAntiOn twoMulSquareDivSquareSubOne (Ioo (0 : ℝ) 1) ∧
      StrictAntiOn twoMulSquareDivSquareSubOne (Ioi (1 : ℝ)) := by
  have hf := fun (x : ℝ) (hx : x ∈ twoMulSquareDivSquareSubOneDomain) ↦ (twoMulSquareDivSquareSubOne_hasDerivAt hx).differentiableAt
  have hleft : Iio (-1 : ℝ) ⊆ twoMulSquareDivSquareSubOneDomain := by
    intro x hx
    apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
    constructor <;> linarith [mem_Iio.mp hx]
  have hmidL : Ioo (-1 : ℝ) 0 ⊆ twoMulSquareDivSquareSubOneDomain := by
    intro x hx
    apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
    constructor <;> linarith [hx.1, hx.2]
  have hmidR : Ioo (0 : ℝ) 1 ⊆ twoMulSquareDivSquareSubOneDomain := by
    intro x hx
    apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
    constructor <;> linarith [hx.1, hx.2]
  have hright : Ioi (1 : ℝ) ⊆ twoMulSquareDivSquareSubOneDomain := by
    intro x hx
    apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
    constructor <;> linarith [mem_Ioi.mp hx]
  refine ⟨strictMonoOn_of_domain_derivative (convex_Iio _) hleft hf ?_,
    strictMonoOn_of_domain_derivative (convex_Ioo _ _) hmidL hf ?_,
    strictAntiOn_of_domain_derivative (convex_Ioo _ _) hmidR hf ?_,
    strictAntiOn_of_domain_derivative (convex_Ioi _) hright hf ?_⟩
  · intro x hx
    exact (twoMulSquareDivSquareSubOne_derivative_signs (hleft hx)).1.mpr (by linarith [mem_Iio.mp hx])
  · intro x hx
    exact (twoMulSquareDivSquareSubOne_derivative_signs (hmidL hx)).1.mpr hx.2
  · intro x hx
    exact (twoMulSquareDivSquareSubOne_derivative_signs (hmidR hx)).2.1.mpr hx.1
  · intro x hx
    exact (twoMulSquareDivSquareSubOne_derivative_signs (hright hx)).2.1.mpr (by linarith [mem_Ioi.mp hx])

theorem twoMulSquareDivSquareSubOne_zero : twoMulSquareDivSquareSubOne 0 = 0 := by simp [twoMulSquareDivSquareSubOne]

theorem twoMulSquareDivSquareSubOne_zero_iff {x : ℝ} (hx : x ∈ twoMulSquareDivSquareSubOneDomain) :
    twoMulSquareDivSquareSubOne x = 0 ↔ x = 0 := by
  unfold twoMulSquareDivSquareSubOne
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))
    · exact False.elim (hx h)
  · rintro rfl
    exact Or.inl (by norm_num)

theorem twoMulSquareDivSquareSubOne_exterior_gt_two {x : ℝ} (hx : 1 < x ^ 2) :
    2 < twoMulSquareDivSquareSubOne x := by
  unfold twoMulSquareDivSquareSubOne
  apply (lt_div_iff₀ (show 0 < x ^ 2 - 1 by linarith)).mpr
  nlinarith

theorem twoMulSquareDivSquareSubOne_inner_square_lt_one {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    x ^ 2 < 1 := by
  have h := mul_pos (show 0 < x + 1 by linarith [hx.1])
    (show 0 < 1 - x by linarith [hx.2])
  nlinarith

theorem twoMulSquareDivSquareSubOne_inner_nonpos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    twoMulSquareDivSquareSubOne x ≤ 0 := by
  have hd : x ^ 2 - 1 < 0 := by linarith [twoMulSquareDivSquareSubOne_inner_square_lt_one hx]
  exact div_nonpos_of_nonneg_of_nonpos (by positivity) hd.le

theorem twoMulSquareDivSquareSubOne_inner_neg {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hne : x ≠ 0) :
    twoMulSquareDivSquareSubOne x < 0 := by
  have hd : x ^ 2 - 1 < 0 := by linarith [twoMulSquareDivSquareSubOne_inner_square_lt_one hx]
  exact div_neg_of_pos_of_neg (mul_pos (by norm_num) (sq_pos_of_ne_zero hne)) hd

theorem twoMulSquareDivSquareSubOne_extrema :
    (∀ x : ℝ, IsLocalMaximumOn twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain x ↔ x = 0) ∧
      (∀ x : ℝ, ¬ IsLocalMinimumOn twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain x) := by
  have hmax : IsLocalMaximumOn twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain 0 := by
    refine ⟨by norm_num [twoMulSquareDivSquareSubOneDomain], 1, by norm_num, ?_⟩
    intro x hx
    rw [twoMulSquareDivSquareSubOne_zero]
    exact twoMulSquareDivSquareSubOne_inner_nonpos (by simpa using hx.1)
  have hnotmin : ¬ IsLocalMinimumOn twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain 0 := by
    apply no_local_minimum_of_right_decrease (b := 1) (by norm_num)
    · intro x hx
      apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
      constructor <;> linarith [hx.1, hx.2]
    · intro x hx
      rw [twoMulSquareDivSquareSubOne_zero]
      exact twoMulSquareDivSquareSubOne_inner_neg ⟨by linarith [hx.1], hx.2⟩ hx.1.ne'
  constructor
  · intro x
    constructor
    · intro h
      exact (twoMulSquareDivSquareSubOne_derivative_signs h.1).2.2.mp
        (fermat twoMulSquareDivSquareSubOne_domain_open (Or.inr h)
          (twoMulSquareDivSquareSubOne_hasDerivAt h.1).differentiableAt)
    · rintro rfl
      exact hmax
  · intro x h
    have hx := (twoMulSquareDivSquareSubOne_derivative_signs h.1).2.2.mp
      (fermat twoMulSquareDivSquareSubOne_domain_open (Or.inl h)
        (twoMulSquareDivSquareSubOne_hasDerivAt h.1).differentiableAt)
    subst x
    exact hnotmin h

theorem twoMulSquareDivSquareSubOne_convexity :
    ConvexOn ℝ (Iio (-1 : ℝ)) twoMulSquareDivSquareSubOne ∧
      ConcaveOnOpenInterval twoMulSquareDivSquareSubOne (-1) 1 ∧
      ConvexOn ℝ (Ioi (1 : ℝ)) twoMulSquareDivSquareSubOne := by
  have hf := fun (x : ℝ) (hx : x ∈ twoMulSquareDivSquareSubOneDomain) ↦ (twoMulSquareDivSquareSubOne_hasDerivAt hx).differentiableAt
  have hg := fun (x : ℝ) (hx : x ∈ twoMulSquareDivSquareSubOneDomain) ↦ (twoMulSquareDivSquareSubOne_second_hasDerivAt hx).differentiableAt
  have hleft : Iio (-1 : ℝ) ⊆ twoMulSquareDivSquareSubOneDomain := by
    intro x hx; apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
    constructor <;> linarith [mem_Iio.mp hx]
  have hmid : Ioo (-1 : ℝ) 1 ⊆ twoMulSquareDivSquareSubOneDomain := by
    intro x hx; apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
    constructor <;> linarith [hx.1, hx.2]
  have hright : Ioi (1 : ℝ) ⊆ twoMulSquareDivSquareSubOneDomain := by
    intro x hx; apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
    constructor <;> linarith [mem_Ioi.mp hx]
  refine ⟨convexOn_of_deriv2_nonneg' (convex_Iio _)
    (fun x hx ↦ (hf x (hleft hx)).differentiableWithinAt)
    (fun x hx ↦ (hg x (hleft hx)).differentiableWithinAt) ?_,
    concaveOnOpenInterval_of_second_deriv_nonpos twoMulSquareDivSquareSubOne (-1) 1
      (source_two_of_pointwise hmid hf hg) ?_,
    convexOn_of_deriv2_nonneg' (convex_Ioi _)
      (fun x hx ↦ (hf x (hright hx)).differentiableWithinAt)
      (fun x hx ↦ (hg x (hright hx)).differentiableWithinAt) ?_⟩
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      ((twoMulSquareDivSquareSubOne_second_signs (hleft hx)).1.mpr (by nlinarith [mem_Iio.mp hx, sq_nonneg (x + 1)])).le
  · intro x hx
    exact ((twoMulSquareDivSquareSubOne_second_signs (hmid hx)).2.1.mpr
      (twoMulSquareDivSquareSubOne_inner_square_lt_one hx)).le
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      ((twoMulSquareDivSquareSubOne_second_signs (hright hx)).1.mpr (by nlinarith [mem_Ioi.mp hx, sq_nonneg (x - 1)])).le


theorem twoMulSquareDivSquareSubOne_no_inflection {a b c : ℝ}
    (hI : Ioo a b ⊆ twoMulSquareDivSquareSubOneDomain) :
    ¬ SourceInflectionOn twoMulSquareDivSquareSubOne a b c := by
  intro h
  have hc := hI h.1
  exact (twoMulSquareDivSquareSubOne_second_signs hc).2.2
    (second_zero_of_sourceInflection hI
      (fun _ hx ↦ (twoMulSquareDivSquareSubOne_hasDerivAt hx).differentiableAt)
      (fun _ hx ↦ (twoMulSquareDivSquareSubOne_second_hasDerivAt hx).differentiableAt)
      (twoMulSquareDivSquareSubOne_second_continuousAt hc) h)

theorem twoMulSquareDivSquareSubOne_even (x : ℝ) : twoMulSquareDivSquareSubOne (-x) = twoMulSquareDivSquareSubOne x := by
  simp [twoMulSquareDivSquareSubOne]

theorem twoMulSquareDivSquareSubOne_graph_iff (x y : ℝ) :
    (x ∈ twoMulSquareDivSquareSubOneDomain ∧ twoMulSquareDivSquareSubOne x = y) ↔
      (x ^ 2 - 1) * y = 2 * x ^ 2 := by
  constructor
  · rintro ⟨hx, hy⟩
    have h := (div_eq_iff hx).mp hy
    simpa only [mul_comm] using h.symm
  · intro h
    have hx : x ∈ twoMulSquareDivSquareSubOneDomain := by
      change x ^ 2 - 1 ≠ 0
      intro hz
      rw [hz, zero_mul] at h
      nlinarith
    exact ⟨hx, (div_eq_iff hx).mpr (by simpa only [mul_comm] using h.symm)⟩

theorem twoMulSquareDivSquareSubOne_range (y : ℝ) :
    (∃ x ∈ twoMulSquareDivSquareSubOneDomain, twoMulSquareDivSquareSubOne x = y) ↔ y ≤ 0 ∨ 2 < y := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have he := (twoMulSquareDivSquareSubOne_graph_iff x y).mp ⟨hx, hxy⟩
    rcases lt_or_gt_of_ne hx with hn | hp
    · exact Or.inl (nonpos_of_mul_nonneg_right (show 0 ≤ (x ^ 2 - 1) * y by
        rw [he]; positivity) hn)
    · right
      have h : 0 < (x ^ 2 - 1) * (y - 2) := by nlinarith [he]
      have := pos_of_mul_pos_right h hp.le
      linarith
  · intro hy
    have hd : y - 2 ≠ 0 := by rcases hy with hy | hy <;> linarith
    have ht : 0 ≤ y / (y - 2) := by
      rcases hy with hn | hp
      · exact div_nonneg_of_nonpos hn (by linarith)
      · exact div_nonneg (by linarith) (by linarith)
    let x : ℝ := Real.sqrt (y / (y - 2))
    have hx2 : x ^ 2 = y / (y - 2) := Real.sq_sqrt ht
    have he : (x ^ 2 - 1) * y = 2 * x ^ 2 := by
      rw [hx2]
      field_simp [hd]
      ring
    exact ⟨x, (twoMulSquareDivSquareSubOne_graph_iff x y).mpr he⟩

theorem twoMulSquareDivSquareSubOne_domain_tail_top : ∀ᶠ x : ℝ in atTop, x ∈ twoMulSquareDivSquareSubOneDomain := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
  constructor <;> linarith

theorem twoMulSquareDivSquareSubOne_domain_tail_bot : ∀ᶠ x : ℝ in atBot, x ∈ twoMulSquareDivSquareSubOneDomain := by
  filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
  apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
  constructor <;> linarith

theorem twoMulSquareDivSquareSubOne_eq_scaled (x : ℝ) : twoMulSquareDivSquareSubOne x = -2 * quadraticRational x := by
  unfold twoMulSquareDivSquareSubOne quadraticRational
  rw [show 1 - x ^ 2 = -(x ^ 2 - 1) by ring, div_neg]
  ring

theorem twoMulSquareDivSquareSubOne_limit_top : Tendsto twoMulSquareDivSquareSubOne atTop (𝓝 (2 : ℝ)) := by
  have h := quadraticRational_limit_atTop.const_mul (-2)
  norm_num at h
  exact h.congr (fun x ↦ by rw [twoMulSquareDivSquareSubOne_eq_scaled]; ring)

theorem twoMulSquareDivSquareSubOne_limit_bot : Tendsto twoMulSquareDivSquareSubOne atBot (𝓝 (2 : ℝ)) := by
  have h := quadraticRational_limit_atBot.const_mul (-2)
  norm_num at h
  exact h.congr (fun x ↦ by rw [twoMulSquareDivSquareSubOne_eq_scaled]; ring)


theorem twoMulSquareDivSquareSubOne_pole_top {F : Filter ℝ}
    (hd : Tendsto (fun x : ℝ ↦ x ^ 2 - 1) F (𝓝[>] (0 : ℝ)))
    (hn : Tendsto (fun x : ℝ ↦ 2 * x ^ 2) F (𝓝 (2 : ℝ))) :
    Tendsto twoMulSquareDivSquareSubOne F atTop := by
  have h := (tendsto_inv_nhdsGT_zero.comp hd).atTop_mul_pos (by norm_num : (0 : ℝ) < 2) hn
  exact h.congr (fun x ↦ by dsimp [Function.comp_def, twoMulSquareDivSquareSubOne]; ring)

theorem twoMulSquareDivSquareSubOne_pole_bot {F : Filter ℝ}
    (hd : Tendsto (fun x : ℝ ↦ x ^ 2 - 1) F (𝓝[<] (0 : ℝ)))
    (hn : Tendsto (fun x : ℝ ↦ 2 * x ^ 2) F (𝓝 (2 : ℝ))) :
    Tendsto twoMulSquareDivSquareSubOne F atBot := by
  have h := (tendsto_inv_nhdsLT_zero.comp hd).atBot_mul_pos (by norm_num : (0 : ℝ) < 2) hn
  exact h.congr (fun x ↦ by dsimp [Function.comp_def, twoMulSquareDivSquareSubOne]; ring)

theorem twoMulSquareDivSquareSubOne_four_pole_limits :
    Tendsto twoMulSquareDivSquareSubOne (𝓝[<] (-1 : ℝ)) atTop ∧
      Tendsto twoMulSquareDivSquareSubOne (𝓝[>] (-1 : ℝ)) atBot ∧
      Tendsto twoMulSquareDivSquareSubOne (𝓝[<] (1 : ℝ)) atBot ∧
      Tendsto twoMulSquareDivSquareSubOne (𝓝[>] (1 : ℝ)) atTop := by
  have hden (a : ℝ) : Tendsto (fun x : ℝ ↦ x ^ 2 - 1) (𝓝 a) (𝓝 (a ^ 2 - 1)) :=
    ((continuousAt_id.pow 2).sub continuousAt_const).tendsto
  have hnum (a : ℝ) : Tendsto (fun x : ℝ ↦ 2 * x ^ 2) (𝓝 a) (𝓝 (2 * a ^ 2)) :=
    (continuousAt_const.mul (continuousAt_id.pow 2)).tendsto
  refine ⟨twoMulSquareDivSquareSubOne_pole_top ?_ ?_, twoMulSquareDivSquareSubOne_pole_bot ?_ ?_,
    twoMulSquareDivSquareSubOne_pole_bot ?_ ?_, twoMulSquareDivSquareSubOne_pole_top ?_ ?_⟩
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (hden (-1)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < -1)
    change 0 < x ^ 2 - 1
    nlinarith [sq_nonneg (x + 1)]
  · simpa using (hnum (-1)).mono_left (nhdsWithin_le_nhds : 𝓝[<] (-1 : ℝ) ≤ 𝓝 (-1 : ℝ))
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (hden (-1)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with x (hx : -1 < x) (hy : x < 0)
    change x ^ 2 - 1 < 0
    linarith [twoMulSquareDivSquareSubOne_inner_square_lt_one
      (show x ∈ Ioo (-1 : ℝ) 1 from ⟨hx, by linarith⟩)]
  · simpa using (hnum (-1)).mono_left (nhdsWithin_le_nhds : 𝓝[>] (-1 : ℝ) ≤ 𝓝 (-1 : ℝ))
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (hden 1).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x (hx : x < 1) (hy : 0 < x)
    change x ^ 2 - 1 < 0
    linarith [twoMulSquareDivSquareSubOne_inner_square_lt_one
      (show x ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith, hx⟩)]
  · simpa using (hnum 1).mono_left (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ))
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (hden 1).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    change 0 < x ^ 2 - 1
    nlinarith [sq_nonneg (x - 1)]
  · simpa using (hnum 1).mono_left (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ))

theorem twoMulSquareDivSquareSubOne_asymptotes :
    (∀ a : ℝ, HasVerticalAsymptoteWithinAt twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain a ↔
      a = -1 ∨ a = 1) ∧
      (∀ b : ℝ, HasHorizontalAsymptoteWithin twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain b ↔ b = 2) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain m b) := by
  have hparsT (m b : ℝ) :
      Tendsto (fun x ↦ twoMulSquareDivSquareSubOne x - (m * x + b)) atTop (𝓝 0) ↔ m = 0 ∧ b = 2 := by
    apply affine_parameters_iff tendsto_inv_atTop_zero punctured_domain_atTop
    simpa using twoMulSquareDivSquareSubOne_limit_top.sub_const 2
  have hparsB (m b : ℝ) :
      Tendsto (fun x ↦ twoMulSquareDivSquareSubOne x - (m * x + b)) atBot (𝓝 0) ↔ m = 0 ∧ b = 2 := by
    apply affine_parameters_iff tendsto_inv_atBot_zero punctured_domain_atBot
    simpa using twoMulSquareDivSquareSubOne_limit_bot.sub_const 2
  refine ⟨?_, ?_, ?_⟩
  · intro a
    constructor
    · intro h
      by_contra hn
      have ha := (twoMulSquareDivSquareSubOne_domain_iff a).mpr
        ⟨fun h ↦ hn (Or.inl h), fun h ↦ hn (Or.inr h)⟩
      exact no_vertical_of_continuousAt (twoMulSquareDivSquareSubOne_hasDerivAt ha).continuousAt h
    · rintro (rfl | rfl)
      · have hD : ∀ᶠ x in 𝓝[<] (-1 : ℝ), x ∈ twoMulSquareDivSquareSubOneDomain := by
          filter_upwards [self_mem_nhdsWithin] with x (hx : x < -1)
          apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
          constructor <;> linarith
        have h := twoMulSquareDivSquareSubOne_four_pole_limits.1
        have heq : 𝓝[twoMulSquareDivSquareSubOneDomain ∩ Iio (-1 : ℝ)] (-1) = 𝓝[<] (-1 : ℝ) := by
          simpa only [Set.ofPred_mem_eq] using nhdsWithin_inter_of_mem hD
        rw [hasVerticalAsymptoteWithinAt_iff, heq]
        exact Or.inr ⟨inferInstance, Or.inl h⟩
      · apply vertical_of_right_top _ twoMulSquareDivSquareSubOne_four_pole_limits.2.2.2
        filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
        apply (twoMulSquareDivSquareSubOne_domain_iff x).mpr
        constructor <;> linarith
  · intro b
    rw [full_tail_horizontal_iff twoMulSquareDivSquareSubOne_domain_tail_top
      twoMulSquareDivSquareSubOne_domain_tail_bot, HasHorizontalAsymptote]
    constructor
    · rintro (h | h)
      · exact tendsto_nhds_unique h twoMulSquareDivSquareSubOne_limit_top
      · exact tendsto_nhds_unique h twoMulSquareDivSquareSubOne_limit_bot
    · rintro rfl
      exact Or.inl twoMulSquareDivSquareSubOne_limit_top
  · intro m b
    rw [full_tail_oblique_iff twoMulSquareDivSquareSubOne_domain_tail_top
      twoMulSquareDivSquareSubOne_domain_tail_bot, HasObliqueAsymptote]
    rintro ⟨hm, h | h⟩
    · exact hm ((hparsT m b).mp h).1
    · exact hm ((hparsB m b).mp h).1

/-- Bài 14(a): khảo sát `2x²/(x²−1)` trên `x ≠ ±1`. -/
theorem source_symmetric_rational_function_investigation :
    (∀ x : ℝ, x ∈ twoMulSquareDivSquareSubOneDomain ↔ x ≠ -1 ∧ x ≠ 1) ∧
      (∀ x ∈ twoMulSquareDivSquareSubOneDomain,
        HasDerivAt twoMulSquareDivSquareSubOne (-4 * x / (x ^ 2 - 1) ^ 2) x ∧
          HasDerivAt (deriv twoMulSquareDivSquareSubOne) (4 * (3 * x ^ 2 + 1) / (x ^ 2 - 1) ^ 3) x) ∧
      (StrictMonoOn twoMulSquareDivSquareSubOne (Iio (-1 : ℝ)) ∧
        StrictMonoOn twoMulSquareDivSquareSubOne (Ioo (-1 : ℝ) 0) ∧
        StrictAntiOn twoMulSquareDivSquareSubOne (Ioo (0 : ℝ) 1) ∧
        StrictAntiOn twoMulSquareDivSquareSubOne (Ioi (1 : ℝ))) ∧
      ((∀ x : ℝ, IsLocalMaximumOn twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain x ↔ x = 0) ∧
        ∀ x : ℝ, ¬ IsLocalMinimumOn twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain x) ∧
      (ConvexOn ℝ (Iio (-1 : ℝ)) twoMulSquareDivSquareSubOne ∧
        ConcaveOnOpenInterval twoMulSquareDivSquareSubOne (-1) 1 ∧
        ConvexOn ℝ (Ioi (1 : ℝ)) twoMulSquareDivSquareSubOne) ∧
      (∀ a b c : ℝ, Ioo a b ⊆ twoMulSquareDivSquareSubOneDomain →
        ¬ SourceInflectionOn twoMulSquareDivSquareSubOne a b c) ∧
      (Tendsto twoMulSquareDivSquareSubOne (𝓝[<] (-1 : ℝ)) atTop ∧
        Tendsto twoMulSquareDivSquareSubOne (𝓝[>] (-1 : ℝ)) atBot ∧
        Tendsto twoMulSquareDivSquareSubOne (𝓝[<] (1 : ℝ)) atBot ∧
        Tendsto twoMulSquareDivSquareSubOne (𝓝[>] (1 : ℝ)) atTop) ∧
      (Tendsto twoMulSquareDivSquareSubOne atTop (𝓝 (2 : ℝ)) ∧ Tendsto twoMulSquareDivSquareSubOne atBot (𝓝 (2 : ℝ))) ∧
      ((∀ a : ℝ, HasVerticalAsymptoteWithinAt twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain a ↔ a = -1 ∨ a = 1) ∧
        (∀ b : ℝ, HasHorizontalAsymptoteWithin twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain b ↔ b = 2) ∧
        ∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin twoMulSquareDivSquareSubOne twoMulSquareDivSquareSubOneDomain m b) ∧
      (∀ x : ℝ, twoMulSquareDivSquareSubOne (-x) = twoMulSquareDivSquareSubOne x) ∧ twoMulSquareDivSquareSubOne 0 = 0 ∧
      (∀ x ∈ twoMulSquareDivSquareSubOneDomain, twoMulSquareDivSquareSubOne x = 0 ↔ x = 0) ∧
      (∀ x : ℝ, 1 < x ^ 2 → 2 < twoMulSquareDivSquareSubOne x) ∧
      (∀ x y : ℝ, (x ∈ twoMulSquareDivSquareSubOneDomain ∧ twoMulSquareDivSquareSubOne x = y) ↔
        (x ^ 2 - 1) * y = 2 * x ^ 2) ∧
      (∀ y : ℝ, (∃ x ∈ twoMulSquareDivSquareSubOneDomain, twoMulSquareDivSquareSubOne x = y) ↔ y ≤ 0 ∨ 2 < y) :=
  ⟨twoMulSquareDivSquareSubOne_domain_iff, fun _ hx ↦ ⟨twoMulSquareDivSquareSubOne_hasDerivAt hx,
    twoMulSquareDivSquareSubOne_second_hasDerivAt hx⟩, twoMulSquareDivSquareSubOne_variation,
    twoMulSquareDivSquareSubOne_extrema, twoMulSquareDivSquareSubOne_convexity,
    fun _ _ _ hI ↦ twoMulSquareDivSquareSubOne_no_inflection hI,
    twoMulSquareDivSquareSubOne_four_pole_limits, ⟨twoMulSquareDivSquareSubOne_limit_top, twoMulSquareDivSquareSubOne_limit_bot⟩,
    twoMulSquareDivSquareSubOne_asymptotes, twoMulSquareDivSquareSubOne_even, twoMulSquareDivSquareSubOne_zero,
    fun _ hx ↦ twoMulSquareDivSquareSubOne_zero_iff hx, fun _ hx ↦ twoMulSquareDivSquareSubOne_exterior_gt_two hx,
    twoMulSquareDivSquareSubOne_graph_iff, twoMulSquareDivSquareSubOne_range⟩

end calculus.Chapter04.Section04SymmetricRationalFunctionInvestigation
