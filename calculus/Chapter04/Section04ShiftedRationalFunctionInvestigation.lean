import calculus.Chapter04.Section04RationalFunctionInvestigationSupport
import calculus.Chapter04.Section04AsymptoteCollectionExercises

/-!
# Bài 4.4.14(b): khảo sát x²/(x−1)²

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2758–2762.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04ShiftedRationalFunctionInvestigation
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

def squareDivSubOneSq (x : ℝ) : ℝ := x ^ 2 / (x - 1) ^ 2

def squareDivSubOneSqDomain : Set ℝ := {x | x ≠ 1}

def squareDivSubOneSqFirstDeriv (x : ℝ) : ℝ := -2 * x / (x - 1) ^ 3

def squareDivSubOneSqSecondDeriv (x : ℝ) : ℝ := 2 * (2 * x + 1) / (x - 1) ^ 4


theorem squareDivSubOneSq_domain_iff (x : ℝ) :
    x ∈ squareDivSubOneSqDomain ↔ (x - 1) ^ 2 ≠ 0 := by
  change x ≠ 1 ↔ _
  rw [pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0), sub_ne_zero]

theorem squareDivSubOneSq_domain_open : IsOpen squareDivSubOneSqDomain := isOpen_ne

theorem squareDivSubOneSq_hasDerivAt {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    HasDerivAt squareDivSubOneSq (squareDivSubOneSqFirstDeriv x) x := by
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have h := ((hasDerivAt_id x).fun_pow 2).div
    (((hasDerivAt_id x).sub_const 1).fun_pow 2) (pow_ne_zero 2 hd)
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  apply h.congr_deriv
  dsimp only [squareDivSubOneSqFirstDeriv]
  field_simp [hd]
  ring

theorem squareDivSubOneSqFirstDeriv_hasDerivAt {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    HasDerivAt squareDivSubOneSqFirstDeriv (squareDivSubOneSqSecondDeriv x) x := by
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have h := ((hasDerivAt_id x).const_mul (-2)).div
    (((hasDerivAt_id x).sub_const 1).fun_pow 3) (pow_ne_zero 3 hd)
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  apply h.congr_deriv
  dsimp only [squareDivSubOneSqSecondDeriv]
  field_simp [hd]
  ring

theorem squareDivSubOneSq_second_hasDerivAt {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    HasDerivAt (deriv squareDivSubOneSq) (squareDivSubOneSqSecondDeriv x) x :=
  hasDerivAt_deriv_of_open_formula squareDivSubOneSq_domain_open hx
    (fun _ hy ↦ squareDivSubOneSq_hasDerivAt hy) (squareDivSubOneSqFirstDeriv_hasDerivAt hx)

theorem squareDivSubOneSq_deriv {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    deriv squareDivSubOneSq x = squareDivSubOneSqFirstDeriv x := (squareDivSubOneSq_hasDerivAt hx).deriv

theorem squareDivSubOneSq_second_deriv {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    deriv (deriv squareDivSubOneSq) x = squareDivSubOneSqSecondDeriv x :=
  (squareDivSubOneSq_second_hasDerivAt hx).deriv

theorem squareDivSubOneSq_second_continuousAt {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    ContinuousAt (deriv (deriv squareDivSubOneSq)) x := by
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have h : ContinuousAt squareDivSubOneSqSecondDeriv x := by
    unfold squareDivSubOneSqSecondDeriv
    fun_prop (disch := exact pow_ne_zero 4 hd)
  apply h.congr_of_eventuallyEq
  filter_upwards [squareDivSubOneSq_domain_open.mem_nhds hx] with y hy
  exact squareDivSubOneSq_second_deriv hy

theorem squareDivSubOneSq_cube_signs {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    (0 < (x - 1) ^ 3 ↔ 1 < x) ∧ ((x - 1) ^ 3 < 0 ↔ x < 1) := by
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hs : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero hd
  rw [pow_succ]
  constructor
  · rw [mul_pos_iff_of_pos_left hs]
    exact sub_pos
  · constructor
    · intro h
      by_contra! hn
      exact h.not_ge (mul_nonneg hs.le (sub_nonneg.mpr hn))
    · intro h
      exact mul_neg_of_pos_of_neg hs (sub_neg.mpr h)

theorem squareDivSubOneSq_derivative_signs {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    (deriv squareDivSubOneSq x < 0 ↔ x < 0 ∨ 1 < x) ∧
      (0 < deriv squareDivSubOneSq x ↔ 0 < x ∧ x < 1) ∧
      (deriv squareDivSubOneSq x = 0 ↔ x = 0) := by
  rw [squareDivSubOneSq_deriv hx]
  have hcube := squareDivSubOneSq_cube_signs hx
  have hd : (x - 1) ^ 3 ≠ 0 := pow_ne_zero 3 (sub_ne_zero.mpr hx)
  unfold squareDivSubOneSqFirstDeriv
  constructor
  · constructor
    · intro h
      rcases div_neg_iff.mp h with ⟨hn, hs⟩ | ⟨hn, hs⟩
      · exact Or.inl (by linarith)
      · exact Or.inr (hcube.1.mp hs)
    · rintro (h | h)
      · exact div_neg_of_pos_of_neg (by linarith) (hcube.2.mpr (by linarith))
      · exact div_neg_of_neg_of_pos (by linarith) (hcube.1.mpr h)
  constructor
  · constructor
    · intro h
      rcases div_pos_iff.mp h with ⟨hn, hs⟩ | ⟨hn, hs⟩
      · have hlarge := hcube.1.mp hs
        exfalso
        linarith
      · exact ⟨by linarith, hcube.2.mp hs⟩
    · rintro ⟨hp, hl⟩
      exact div_pos_of_neg_of_neg (by linarith) (hcube.2.mpr hl)
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact False.elim (hd h)
    · rintro rfl
      exact Or.inl (by norm_num)

theorem squareDivSubOneSq_second_signs {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    (deriv (deriv squareDivSubOneSq) x < 0 ↔ x < -1 / 2) ∧
      (0 < deriv (deriv squareDivSubOneSq) x ↔ -1 / 2 < x) ∧
      (deriv (deriv squareDivSubOneSq) x = 0 ↔ x = -1 / 2) := by
  rw [squareDivSubOneSq_second_deriv hx]
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hp : 0 < (x - 1) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hd) 2
  unfold squareDivSubOneSqSecondDeriv
  constructor
  · rw [div_lt_iff₀ hp]
    constructor <;> intro h <;> nlinarith
  constructor
  · rw [lt_div_iff₀ hp]
    constructor <;> intro h <;> nlinarith
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact False.elim (hp.ne' h)
    · rintro rfl
      exact Or.inl (by norm_num)

theorem squareDivSubOneSq_variation :
    StrictAntiOn squareDivSubOneSq (Iio (0 : ℝ)) ∧
      StrictMonoOn squareDivSubOneSq (Ioo (0 : ℝ) 1) ∧
      StrictAntiOn squareDivSubOneSq (Ioi (1 : ℝ)) := by
  have hf := fun (x : ℝ) (hx : x ∈ squareDivSubOneSqDomain) ↦ (squareDivSubOneSq_hasDerivAt hx).differentiableAt
  have hleft : Iio (0 : ℝ) ⊆ squareDivSubOneSqDomain := by intro x hx; change x ≠ 1; linarith [mem_Iio.mp hx]
  have hmid : Ioo (0 : ℝ) 1 ⊆ squareDivSubOneSqDomain := by
    intro x hx; change x ≠ 1; exact hx.2.ne
  have hright : Ioi (1 : ℝ) ⊆ squareDivSubOneSqDomain := by intro x hx; exact hx.ne'
  refine ⟨strictAntiOn_of_domain_derivative (convex_Iio _) hleft hf ?_,
    strictMonoOn_of_domain_derivative (convex_Ioo _ _) hmid hf ?_,
    strictAntiOn_of_domain_derivative (convex_Ioi _) hright hf ?_⟩
  · intro x hx
    exact (squareDivSubOneSq_derivative_signs (hleft hx)).1.mpr (Or.inl hx)
  · intro x hx
    exact (squareDivSubOneSq_derivative_signs (hmid hx)).2.1.mpr hx
  · intro x hx
    exact (squareDivSubOneSq_derivative_signs (hright hx)).1.mpr (Or.inr hx)

theorem squareDivSubOneSq_zero : squareDivSubOneSq 0 = 0 := by simp [squareDivSubOneSq]

theorem squareDivSubOneSq_zero_iff {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    squareDivSubOneSq x = 0 ↔ x = 0 := by
  unfold squareDivSubOneSq
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact sq_eq_zero_iff.mp h
    · exact False.elim (((squareDivSubOneSq_domain_iff x).mp hx) h)
  · rintro rfl
    exact Or.inl (by norm_num)

theorem squareDivSubOneSq_nonneg (x : ℝ) : 0 ≤ squareDivSubOneSq x :=
  div_nonneg (sq_nonneg x) (sq_nonneg (x - 1))

theorem squareDivSubOneSq_pos {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) (hne : x ≠ 0) :
    0 < squareDivSubOneSq x :=
  div_pos (sq_pos_of_ne_zero hne) (sq_pos_of_ne_zero (sub_ne_zero.mpr hx))

theorem squareDivSubOneSq_extrema :
    (∀ x : ℝ, IsLocalMinimumOn squareDivSubOneSq squareDivSubOneSqDomain x ↔ x = 0) ∧
      (∀ x : ℝ, ¬ IsLocalMaximumOn squareDivSubOneSq squareDivSubOneSqDomain x) := by
  have hmin : IsLocalMinimumOn squareDivSubOneSq squareDivSubOneSqDomain 0 := by
    refine ⟨by norm_num [squareDivSubOneSqDomain], 1, by norm_num, ?_⟩
    intro x _
    rw [squareDivSubOneSq_zero]
    exact squareDivSubOneSq_nonneg x
  have hnotmax : ¬ IsLocalMaximumOn squareDivSubOneSq squareDivSubOneSqDomain 0 := by
    apply no_local_maximum_of_right_increase (b := 1) (by norm_num)
    · intro x hx; change x ≠ 1; exact hx.2.ne
    · intro x hx
      rw [squareDivSubOneSq_zero]
      exact squareDivSubOneSq_pos hx.2.ne hx.1.ne'
  constructor
  · intro x
    constructor
    · intro h
      exact (squareDivSubOneSq_derivative_signs h.1).2.2.mp
        (fermat squareDivSubOneSq_domain_open (Or.inl h)
          (squareDivSubOneSq_hasDerivAt h.1).differentiableAt)
    · rintro rfl
      exact hmin
  · intro x h
    have hx := (squareDivSubOneSq_derivative_signs h.1).2.2.mp
      (fermat squareDivSubOneSq_domain_open (Or.inr h)
        (squareDivSubOneSq_hasDerivAt h.1).differentiableAt)
    subst x
    exact hnotmax h

theorem squareDivSubOneSq_convexity :
    ConcaveOn ℝ (Iio (-1 / 2 : ℝ)) squareDivSubOneSq ∧
      ConvexOnOpenInterval squareDivSubOneSq (-1 / 2) 1 ∧
      ConvexOn ℝ (Ioi (1 : ℝ)) squareDivSubOneSq := by
  have hf := fun (x : ℝ) (hx : x ∈ squareDivSubOneSqDomain) ↦ (squareDivSubOneSq_hasDerivAt hx).differentiableAt
  have hg := fun (x : ℝ) (hx : x ∈ squareDivSubOneSqDomain) ↦ (squareDivSubOneSq_second_hasDerivAt hx).differentiableAt
  have hleft : Iio (-1 / 2 : ℝ) ⊆ squareDivSubOneSqDomain := by intro x hx; change x ≠ 1; linarith [mem_Iio.mp hx]
  have hmid : Ioo (-1 / 2 : ℝ) 1 ⊆ squareDivSubOneSqDomain := by intro x hx; exact hx.2.ne
  have hright : Ioi (1 : ℝ) ⊆ squareDivSubOneSqDomain := by intro x hx; exact hx.ne'
  refine ⟨concaveOn_of_deriv2_nonpos' (convex_Iio _)
    (fun x hx ↦ (hf x (hleft hx)).differentiableWithinAt)
    (fun x hx ↦ (hg x (hleft hx)).differentiableWithinAt) ?_,
    (convexOnOpenInterval_iff_second_deriv_nonneg squareDivSubOneSq (-1 / 2) 1
      (source_two_of_pointwise hmid hf hg)).mpr ?_,
    convexOn_of_deriv2_nonneg' (convex_Ioi _)
      (fun x hx ↦ (hf x (hright hx)).differentiableWithinAt)
      (fun x hx ↦ (hg x (hright hx)).differentiableWithinAt) ?_⟩
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      ((squareDivSubOneSq_second_signs (hleft hx)).1.mpr hx).le
  · intro x hx
    exact ((squareDivSubOneSq_second_signs (hmid hx)).2.1.mpr hx.1).le
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      ((squareDivSubOneSq_second_signs (hright hx)).2.1.mpr (by linarith [mem_Ioi.mp hx])).le


theorem squareDivSubOneSq_inflection_at_neg_half :
    SourceInflectionOn squareDivSubOneSq (-3 / 4) (-1 / 4) (-1 / 2) := by
  have hf := fun (x : ℝ) (hx : x ∈ squareDivSubOneSqDomain) ↦ (squareDivSubOneSq_hasDerivAt hx).differentiableAt
  have hg := fun (x : ℝ) (hx : x ∈ squareDivSubOneSqDomain) ↦ (squareDivSubOneSq_second_hasDerivAt hx).differentiableAt
  have hl : Ioo ((-1 / 2 : ℝ) - 1 / 4) (-1 / 2) ⊆ squareDivSubOneSqDomain := by
    intro x hx; change x ≠ 1; linarith [hx.2]
  have hr : Ioo (-1 / 2 : ℝ) (-1 / 2 + 1 / 4) ⊆ squareDivSubOneSqDomain := by
    intro x hx; change x ≠ 1; linarith [hx.2]
  have h := sourceInflectionOn_of_second_deriv_neg_pos
    (f := squareDivSubOneSq) (x₀ := -1 / 2) (δ := 1 / 4) (by norm_num)
    (source_two_of_pointwise hl hf hg) (source_two_of_pointwise hr hf hg)
    (Or.inl (squareDivSubOneSq_hasDerivAt (by norm_num [squareDivSubOneSqDomain] : (-1 / 2 : ℝ) ∈ squareDivSubOneSqDomain)).differentiableAt)
    (fun x hx ↦ (squareDivSubOneSq_second_signs (hl hx)).1.mpr hx.2)
    (fun x hx ↦ (squareDivSubOneSq_second_signs (hr hx)).2.1.mpr hx.1)
  norm_num at h ⊢
  exact h

theorem squareDivSubOneSq_inflection_iff (c : ℝ) :
    (∃ a b : ℝ, Ioo a b ⊆ squareDivSubOneSqDomain ∧ SourceInflectionOn squareDivSubOneSq a b c) ↔
      c = -1 / 2 := by
  constructor
  · rintro ⟨a, b, hI, hu⟩
    have hc := hI hu.1
    exact (squareDivSubOneSq_second_signs hc).2.2.mp
      (second_zero_of_sourceInflection hI
        (fun _ hx ↦ (squareDivSubOneSq_hasDerivAt hx).differentiableAt)
        (fun _ hx ↦ (squareDivSubOneSq_second_hasDerivAt hx).differentiableAt)
        (squareDivSubOneSq_second_continuousAt hc) hu)
  · rintro rfl
    refine ⟨-3 / 4, -1 / 4, ?_, squareDivSubOneSq_inflection_at_neg_half⟩
    intro x hx
    change x ≠ 1
    linarith [hx.2]

theorem squareDivSubOneSq_inflection_value_and_slope :
    squareDivSubOneSq (-1 / 2) = 1 / 9 ∧ deriv squareDivSubOneSq (-1 / 2) = -8 / 27 := by
  rw [squareDivSubOneSq_deriv (by norm_num [squareDivSubOneSqDomain] : (-1 / 2 : ℝ) ∈ squareDivSubOneSqDomain)]
  norm_num [squareDivSubOneSq, squareDivSubOneSqFirstDeriv]

theorem squareDivSubOneSq_graph_iff (x y : ℝ) :
    (x ∈ squareDivSubOneSqDomain ∧ squareDivSubOneSq x = y) ↔ (x - 1) ^ 2 * y = x ^ 2 := by
  constructor
  · rintro ⟨hx, hy⟩
    have h := (div_eq_iff ((squareDivSubOneSq_domain_iff x).mp hx)).mp hy
    simpa only [mul_comm] using h.symm
  · intro h
    have hx : x ∈ squareDivSubOneSqDomain := by
      change x ≠ 1
      intro hz
      subst x
      norm_num at h
    exact ⟨hx, (div_eq_iff ((squareDivSubOneSq_domain_iff x).mp hx)).mpr
      (by simpa only [mul_comm] using h.symm)⟩

theorem squareDivSubOneSq_range (y : ℝ) :
    (∃ x ∈ squareDivSubOneSqDomain, squareDivSubOneSq x = y) ↔ 0 ≤ y := by
  constructor
  · rintro ⟨x, _, rfl⟩
    exact squareDivSubOneSq_nonneg x
  · intro hy
    let t : ℝ := Real.sqrt y
    have ht : 0 ≤ t := Real.sqrt_nonneg y
    have ht2 : t ^ 2 = y := Real.sq_sqrt hy
    have hd : t + 1 ≠ 0 := by linarith
    let x : ℝ := t / (t + 1)
    have he : (x - 1) ^ 2 * y = x ^ 2 := by
      dsimp only [x]
      field_simp [hd]
      nlinarith [ht2]
    exact ⟨x, (squareDivSubOneSq_graph_iff x y).mpr he⟩

theorem squareDivSubOneSq_horizontal_crossing {x : ℝ} (hx : x ∈ squareDivSubOneSqDomain) :
    (squareDivSubOneSq x < 1 ↔ x < 1 / 2) ∧
      (1 < squareDivSubOneSq x ↔ 1 / 2 < x) ∧
      (squareDivSubOneSq x = 1 ↔ x = 1 / 2) := by
  have hd : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  unfold squareDivSubOneSq
  constructor
  · rw [div_lt_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  constructor
  · rw [lt_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  · rw [div_eq_iff hd.ne']
    constructor <;> intro h <;> nlinarith

theorem squareDivSubOneSq_domain_tail_top : ∀ᶠ x : ℝ in atTop, x ∈ squareDivSubOneSqDomain := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact hx.ne'

theorem squareDivSubOneSq_domain_tail_bot : ∀ᶠ x : ℝ in atBot, x ∈ squareDivSubOneSqDomain := by
  filter_upwards [eventually_lt_atBot (1 : ℝ)] with x hx
  exact hx.ne

theorem squareDivSubOneSq_limit_of_sub_one_reciprocal_tendsto_zero {F : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ (x - 1)⁻¹) F (𝓝 0))
    (hD : ∀ᶠ x : ℝ in F, x ∈ squareDivSubOneSqDomain) :
    Tendsto squareDivSubOneSq F (𝓝 (1 : ℝ)) := by
  have h := (hi.const_add 1).pow 2
  norm_num at h
  apply h.congr'
  filter_upwards [hD] with x hx
  have hd : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  dsimp only [squareDivSubOneSq]
  field_simp [hd]
  ring

theorem squareDivSubOneSq_limit_top : Tendsto squareDivSubOneSq atTop (𝓝 (1 : ℝ)) := by
  have harg : Tendsto (fun x : ℝ ↦ x - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using! tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  apply squareDivSubOneSq_limit_of_sub_one_reciprocal_tendsto_zero _ squareDivSubOneSq_domain_tail_top
  simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp harg

theorem squareDivSubOneSq_limit_bot : Tendsto squareDivSubOneSq atBot (𝓝 (1 : ℝ)) := by
  have harg : Tendsto (fun x : ℝ ↦ x - 1) atBot atBot := by
    simpa only [sub_eq_add_neg] using! tendsto_atBot_add_const_right atBot (-1 : ℝ) tendsto_id
  apply squareDivSubOneSq_limit_of_sub_one_reciprocal_tendsto_zero _ squareDivSubOneSq_domain_tail_bot
  simpa only [Function.comp_def] using tendsto_inv_atBot_zero.comp harg

theorem squareDivSubOneSq_pole {F : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ x) F (𝓝 (1 : ℝ)))
    (hD : ∀ᶠ x : ℝ in F, x ∈ squareDivSubOneSqDomain) :
    Tendsto squareDivSubOneSq F atTop := by
  have hd : Tendsto (fun x : ℝ ↦ (x - 1) ^ 2) F (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (hi.sub_const 1).pow 2, ?_⟩
    exact hD.mono fun x hx ↦ sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  have hn : Tendsto (fun x : ℝ ↦ x ^ 2) F (𝓝 (1 : ℝ)) := by simpa using hi.pow 2
  have h := (tendsto_inv_nhdsGT_zero.comp hd).atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hn
  exact h.congr (fun x ↦ by dsimp [Function.comp_def, squareDivSubOneSq]; ring)

theorem squareDivSubOneSq_both_pole_limits :
    Tendsto squareDivSubOneSq (𝓝[<] (1 : ℝ)) atTop ∧
      Tendsto squareDivSubOneSq (𝓝[>] (1 : ℝ)) atTop := by
  constructor
  · apply squareDivSubOneSq_pole (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
    exact hx.ne
  · apply squareDivSubOneSq_pole (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    exact hx.ne'

theorem squareDivSubOneSq_asymptotes :
    (∀ a : ℝ, HasVerticalAsymptoteWithinAt squareDivSubOneSq squareDivSubOneSqDomain a ↔ a = 1) ∧
      (∀ b : ℝ, HasHorizontalAsymptoteWithin squareDivSubOneSq squareDivSubOneSqDomain b ↔ b = 1) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin squareDivSubOneSq squareDivSubOneSqDomain m b) := by
  have hparsT (m b : ℝ) :
      Tendsto (fun x ↦ squareDivSubOneSq x - (m * x + b)) atTop (𝓝 0) ↔ m = 0 ∧ b = 1 := by
    apply affine_parameters_iff tendsto_inv_atTop_zero punctured_domain_atTop
    simpa using squareDivSubOneSq_limit_top.sub_const 1
  have hparsB (m b : ℝ) :
      Tendsto (fun x ↦ squareDivSubOneSq x - (m * x + b)) atBot (𝓝 0) ↔ m = 0 ∧ b = 1 := by
    apply affine_parameters_iff tendsto_inv_atBot_zero punctured_domain_atBot
    simpa using squareDivSubOneSq_limit_bot.sub_const 1
  refine ⟨?_, ?_, ?_⟩
  · intro a
    constructor
    · intro h
      by_contra ha
      exact no_vertical_of_continuousAt (squareDivSubOneSq_hasDerivAt ha).continuousAt h
    · rintro rfl
      apply vertical_of_right_top _ squareDivSubOneSq_both_pole_limits.2
      filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
      exact hx.ne'
  · intro b
    rw [full_tail_horizontal_iff squareDivSubOneSq_domain_tail_top
      squareDivSubOneSq_domain_tail_bot, HasHorizontalAsymptote]
    constructor
    · rintro (h | h)
      · exact tendsto_nhds_unique h squareDivSubOneSq_limit_top
      · exact tendsto_nhds_unique h squareDivSubOneSq_limit_bot
    · rintro rfl
      exact Or.inl squareDivSubOneSq_limit_top
  · intro m b
    rw [full_tail_oblique_iff squareDivSubOneSq_domain_tail_top
      squareDivSubOneSq_domain_tail_bot, HasObliqueAsymptote]
    rintro ⟨hm, h | h⟩
    · exact hm ((hparsT m b).mp h).1
    · exact hm ((hparsB m b).mp h).1

/-- Bài 14(b): khảo sát `x²/(x−1)²` trên `x ≠ 1`. -/
theorem source_shifted_rational_function_investigation :
    (∀ x : ℝ, x ∈ squareDivSubOneSqDomain ↔ (x - 1) ^ 2 ≠ 0) ∧
      (∀ x ∈ squareDivSubOneSqDomain,
        HasDerivAt squareDivSubOneSq (-2 * x / (x - 1) ^ 3) x ∧
          HasDerivAt (deriv squareDivSubOneSq) (2 * (2 * x + 1) / (x - 1) ^ 4) x) ∧
      (StrictAntiOn squareDivSubOneSq (Iio (0 : ℝ)) ∧
        StrictMonoOn squareDivSubOneSq (Ioo (0 : ℝ) 1) ∧ StrictAntiOn squareDivSubOneSq (Ioi (1 : ℝ))) ∧
      ((∀ x : ℝ, IsLocalMinimumOn squareDivSubOneSq squareDivSubOneSqDomain x ↔ x = 0) ∧
        ∀ x : ℝ, ¬ IsLocalMaximumOn squareDivSubOneSq squareDivSubOneSqDomain x) ∧
      (∀ x ∈ squareDivSubOneSqDomain, 0 ≤ squareDivSubOneSq x) ∧ squareDivSubOneSq 0 = 0 ∧
      (∀ x ∈ squareDivSubOneSqDomain, squareDivSubOneSq x = 0 ↔ x = 0) ∧
      (ConcaveOn ℝ (Iio (-1 / 2 : ℝ)) squareDivSubOneSq ∧
        ConvexOnOpenInterval squareDivSubOneSq (-1 / 2) 1 ∧ ConvexOn ℝ (Ioi (1 : ℝ)) squareDivSubOneSq) ∧
      (∀ c : ℝ, (∃ a b : ℝ, Ioo a b ⊆ squareDivSubOneSqDomain ∧
        SourceInflectionOn squareDivSubOneSq a b c) ↔ c = -1 / 2) ∧
      (squareDivSubOneSq (-1 / 2) = 1 / 9 ∧ deriv squareDivSubOneSq (-1 / 2) = -8 / 27) ∧
      (Tendsto squareDivSubOneSq (𝓝[<] (1 : ℝ)) atTop ∧ Tendsto squareDivSubOneSq (𝓝[>] (1 : ℝ)) atTop) ∧
      (Tendsto squareDivSubOneSq atTop (𝓝 (1 : ℝ)) ∧ Tendsto squareDivSubOneSq atBot (𝓝 (1 : ℝ))) ∧
      ((∀ a : ℝ, HasVerticalAsymptoteWithinAt squareDivSubOneSq squareDivSubOneSqDomain a ↔ a = 1) ∧
        (∀ b : ℝ, HasHorizontalAsymptoteWithin squareDivSubOneSq squareDivSubOneSqDomain b ↔ b = 1) ∧
        ∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin squareDivSubOneSq squareDivSubOneSqDomain m b) ∧
      (∀ x y : ℝ, (x ∈ squareDivSubOneSqDomain ∧ squareDivSubOneSq x = y) ↔ (x - 1) ^ 2 * y = x ^ 2) ∧
      (∀ y : ℝ, (∃ x ∈ squareDivSubOneSqDomain, squareDivSubOneSq x = y) ↔ 0 ≤ y) ∧
      (∀ x ∈ squareDivSubOneSqDomain,
        (squareDivSubOneSq x < 1 ↔ x < 1 / 2) ∧
        (1 < squareDivSubOneSq x ↔ 1 / 2 < x) ∧ (squareDivSubOneSq x = 1 ↔ x = 1 / 2)) :=
  ⟨squareDivSubOneSq_domain_iff, fun _ hx ↦ ⟨squareDivSubOneSq_hasDerivAt hx,
    squareDivSubOneSq_second_hasDerivAt hx⟩, squareDivSubOneSq_variation,
    squareDivSubOneSq_extrema, fun x _ ↦ squareDivSubOneSq_nonneg x, squareDivSubOneSq_zero,
    fun _ hx ↦ squareDivSubOneSq_zero_iff hx,
    squareDivSubOneSq_convexity, squareDivSubOneSq_inflection_iff, squareDivSubOneSq_inflection_value_and_slope,
    squareDivSubOneSq_both_pole_limits, ⟨squareDivSubOneSq_limit_top, squareDivSubOneSq_limit_bot⟩,
    squareDivSubOneSq_asymptotes, squareDivSubOneSq_graph_iff, squareDivSubOneSq_range,
    fun _ hx ↦ squareDivSubOneSq_horizontal_crossing hx⟩

end calculus.Chapter04.Section04ShiftedRationalFunctionInvestigation
