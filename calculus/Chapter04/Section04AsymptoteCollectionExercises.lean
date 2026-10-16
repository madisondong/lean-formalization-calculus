import calculus.Chapter04.Section04AsymptoteClassificationSupport

/-!
# Bài 4.4.13: bốn bộ tiệm cận trên miền tự nhiên

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2748–2756.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04AsymptoteCollectionExercises
open Set Filter
open scoped Topology
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport

def puncturedRealDomain : Set ℝ := {x | x ≠ 0}
def rationalPoleDomain : Set ℝ := {x | 1 - x ^ 2 ≠ 0}
def identityAddSineDivIdentity (x : ℝ) : ℝ := x + Real.sin x / x
def halfIdentityAddExpNegMulSine (x : ℝ) : ℝ := x / 2 + Real.exp (-x) * Real.sin x
def squareExponentialReciprocal (x : ℝ) : ℝ := x ^ 2 * Real.exp (1 / x)
def quadraticRational (x : ℝ) : ℝ := x ^ 2 / (1 - x ^ 2)

theorem punctured_domain_atTop : ∀ᶠ x : ℝ in atTop, x ∈ puncturedRealDomain :=
  (eventually_gt_atTop (0 : ℝ)).mono (fun _ hx ↦ hx.ne')

theorem punctured_domain_atBot : ∀ᶠ x : ℝ in atBot, x ∈ puncturedRealDomain :=
  (eventually_lt_atBot (0 : ℝ)).mono (fun _ hx ↦ hx.ne)

theorem rational_domain_atTop : ∀ᶠ x : ℝ in atTop, x ∈ rationalPoleDomain := by
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  change 1 - x ^ 2 ≠ 0
  intro h
  nlinarith

theorem rational_domain_atBot : ∀ᶠ x : ℝ in atBot, x ∈ rationalPoleDomain := by
  filter_upwards [eventually_lt_atBot (-2 : ℝ)] with x hx
  change 1 - x ^ 2 ≠ 0
  intro h
  nlinarith

theorem sine_quotient_at_zero :
    Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  simpa only [slope_fun_def_field, sub_zero, Real.sin_zero, Real.cos_zero] using!
    (Real.hasDerivAt_sin 0).tendsto_slope

theorem identityAddSineDivIdentity_continuousAt {a : ℝ} (ha : a ≠ 0) : ContinuousAt identityAddSineDivIdentity a := by
  simpa only [identityAddSineDivIdentity] using! continuousAt_id.add
    (Real.continuous_sin.continuousAt.div continuousAt_id ha)

theorem identityAddSineDivIdentity_finite_sides_zero :
    Tendsto identityAddSineDivIdentity (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      Tendsto identityAddSineDivIdentity (𝓝[<] (0 : ℝ)) (𝓝 1) := by
  have hr : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (fun x hx ↦ by simpa only [mem_compl_iff, mem_singleton_iff] using hx.ne')
  have hl : 𝓝[<] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (fun x hx ↦ by simpa only [mem_compl_iff, mem_singleton_iff] using hx.ne)
  constructor
  · change Tendsto (fun x : ℝ ↦ x + Real.sin x / x) (𝓝[>] 0) (𝓝 1)
    simpa only [id_eq, zero_add] using
      ((continuousAt_id : ContinuousAt (fun x : ℝ ↦ x) 0).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).add (sine_quotient_at_zero.mono_left hr)
  · change Tendsto (fun x : ℝ ↦ x + Real.sin x / x) (𝓝[<] 0) (𝓝 1)
    simpa only [id_eq, zero_add] using
      ((continuousAt_id : ContinuousAt (fun x : ℝ ↦ x) 0).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0)).add (sine_quotient_at_zero.mono_left hl)

theorem identityAddSineDivIdentity_no_vertical (a : ℝ) :
    ¬ HasVerticalAsymptoteWithinAt identityAddSineDivIdentity puncturedRealDomain a := by
  by_cases ha : a = 0
  · subst a
    exact no_vertical_of_finite_sides identityAddSineDivIdentity_finite_sides_zero.1 identityAddSineDivIdentity_finite_sides_zero.2
  · exact no_vertical_of_continuousAt (identityAddSineDivIdentity_continuousAt ha)

theorem identityAddSineDivIdentity_residual_atTop :
    Tendsto (fun x : ℝ ↦ identityAddSineDivIdentity x - (1 * x + 0)) atTop (𝓝 0) := by
  have h := sine_product_tendsto_zero tendsto_inv_atTop_zero
  exact h.congr (fun x ↦ by dsimp [identityAddSineDivIdentity]; ring)

theorem identityAddSineDivIdentity_residual_atBot :
    Tendsto (fun x : ℝ ↦ identityAddSineDivIdentity x - (1 * x + 0)) atBot (𝓝 0) := by
  have h := sine_product_tendsto_zero tendsto_inv_atBot_zero
  exact h.congr (fun x ↦ by dsimp [identityAddSineDivIdentity]; ring)

theorem identityAddSineDivIdentity_parameters_atTop (m b : ℝ) :
    Tendsto (fun x ↦ identityAddSineDivIdentity x - (m * x + b)) atTop (𝓝 0) ↔ m = 1 ∧ b = 0 :=
  affine_parameters_iff tendsto_inv_atTop_zero punctured_domain_atTop identityAddSineDivIdentity_residual_atTop m b

theorem identityAddSineDivIdentity_parameters_atBot (m b : ℝ) :
    Tendsto (fun x ↦ identityAddSineDivIdentity x - (m * x + b)) atBot (𝓝 0) ↔ m = 1 ∧ b = 0 :=
  affine_parameters_iff tendsto_inv_atBot_zero punctured_domain_atBot identityAddSineDivIdentity_residual_atBot m b

/-- Bài 13(a): tiệm cận xiên duy nhất y=x; không có tiệm cận đứng hay ngang. -/
theorem source_identity_add_sine_div_identity_asymptotes :
    (∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt identityAddSineDivIdentity puncturedRealDomain a) ∧
      (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin identityAddSineDivIdentity puncturedRealDomain b) ∧
      (∀ m b : ℝ, HasObliqueAsymptoteWithin identityAddSineDivIdentity puncturedRealDomain m b ↔
        m = 1 ∧ b = 0) := by
  refine ⟨identityAddSineDivIdentity_no_vertical, ?_, ?_⟩
  · intro b
    rw [full_tail_horizontal_iff punctured_domain_atTop punctured_domain_atBot,
      HasHorizontalAsymptote]
    rintro (h | h)
    · exact no_horizontal_at_end_of_nonzero_affine (by norm_num : (1 : ℝ) ≠ 0)
        identityAddSineDivIdentity_parameters_atTop b h
    · exact no_horizontal_at_end_of_nonzero_affine (by norm_num : (1 : ℝ) ≠ 0)
        identityAddSineDivIdentity_parameters_atBot b h
  · intro m b
    rw [full_tail_oblique_iff punctured_domain_atTop punctured_domain_atBot,
      HasObliqueAsymptote, identityAddSineDivIdentity_parameters_atTop, identityAddSineDivIdentity_parameters_atBot, or_self]
    constructor
    · exact fun h ↦ h.2
    · rintro ⟨rfl, rfl⟩
      exact ⟨by norm_num, rfl, rfl⟩

theorem halfIdentityAddExpNegMulSine_continuous : Continuous halfIdentityAddExpNegMulSine := by
  simpa only [halfIdentityAddExpNegMulSine] using! (continuous_id.div_const (2 : ℝ)).add
    ((Real.continuous_exp.comp continuous_id.neg).mul Real.continuous_sin)

theorem halfIdentityAddExpNegMulSine_residual_atTop :
    Tendsto (fun x : ℝ ↦ halfIdentityAddExpNegMulSine x - ((1 / 2) * x + 0)) atTop (𝓝 0) := by
  have h := sine_product_tendsto_zero Real.tendsto_exp_neg_atTop_nhds_zero
  exact h.congr (fun x ↦ by dsimp [halfIdentityAddExpNegMulSine]; ring)

theorem identity_times_exp_atBot :
    Tendsto (fun x : ℝ ↦ x * Real.exp x) atBot (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_neg_atBot_atTop).neg
  simpa only [Function.comp_def, pow_one, neg_neg, neg_mul, neg_zero] using! h


theorem halfIdentityAddExpNegMulSine_no_residual_atBot (m b : ℝ) :
    ¬ Tendsto (fun x ↦ halfIdentityAddExpNegMulSine x - (m * x + b)) atBot (𝓝 0) := by
  intro h
  have hw := h.mul Real.tendsto_exp_atBot
  simp only [mul_zero] at hw
  have hlin : Tendsto (fun x : ℝ ↦ (x / 2 - (m * x + b)) * Real.exp x) atBot (𝓝 0) := by
    have hh := (identity_times_exp_atBot.const_mul (1 / 2 - m)).sub
      (Real.tendsto_exp_atBot.const_mul b)
    simp only [mul_zero, sub_zero] at hh
    exact hh.congr (fun x ↦ by ring)
  have hs : Tendsto Real.sin atBot (𝓝 0) := by
    have hh := hw.sub hlin
    simp only [sub_zero] at hh
    apply hh.congr
    intro x
    dsimp [halfIdentityAddExpNegMulSine]
    have he : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = (Real.exp (-x) * Real.exp x) * Real.sin x := by ring
      _ = Real.sin x := by rw [he, one_mul]
  exact sine_not_tendsto_zero_atBot hs

theorem halfIdentityAddExpNegMulSine_parameters_atTop (m b : ℝ) :
    Tendsto (fun x ↦ halfIdentityAddExpNegMulSine x - (m * x + b)) atTop (𝓝 0) ↔
      m = 1 / 2 ∧ b = 0 :=
  affine_parameters_iff tendsto_inv_atTop_zero
    ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne')
    halfIdentityAddExpNegMulSine_residual_atTop m b

/-- Bài 13(b): tiệm cận duy nhất là `y = x/2` tại `+∞`. -/
theorem source_half_identity_add_exp_neg_mul_sine_asymptotes :
    (∀ a : ℝ, ¬ HasVerticalAsymptoteWithinAt halfIdentityAddExpNegMulSine univ a) ∧
      (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin halfIdentityAddExpNegMulSine univ b) ∧
      (∀ m b : ℝ, HasObliqueAsymptoteWithin halfIdentityAddExpNegMulSine univ m b ↔
        m = 1 / 2 ∧ b = 0) := by
  refine ⟨fun a ↦ no_vertical_of_continuousAt halfIdentityAddExpNegMulSine_continuous.continuousAt, ?_, ?_⟩
  · intro b
    rw [hasHorizontalAsymptoteWithin_univ_iff, HasHorizontalAsymptote]
    rintro (h | h)
    · exact no_horizontal_at_end_of_nonzero_affine (by norm_num : (1 / 2 : ℝ) ≠ 0)
        halfIdentityAddExpNegMulSine_parameters_atTop b h
    · apply halfIdentityAddExpNegMulSine_no_residual_atBot 0 b
      simpa only [zero_mul, zero_add, sub_self] using h.sub_const b
  · intro m b
    rw [hasObliqueAsymptoteWithin_univ_iff, HasObliqueAsymptote]
    constructor
    · rintro ⟨_, h | h⟩
      · exact (halfIdentityAddExpNegMulSine_parameters_atTop m b).mp h
      · exact False.elim (halfIdentityAddExpNegMulSine_no_residual_atBot m b h)
    · rintro ⟨rfl, rfl⟩
      exact ⟨by norm_num, Or.inl halfIdentityAddExpNegMulSine_residual_atTop⟩

theorem squareExponentialReciprocal_continuousAt {a : ℝ} (ha : a ≠ 0) :
    ContinuousAt squareExponentialReciprocal a := by
  change ContinuousAt (fun x : ℝ ↦ x ^ 2 * Real.exp (1 / x)) a
  exact (continuousAt_id.pow 2).mul
    (Real.continuous_exp.continuousAt.comp (continuousAt_const.div continuousAt_id ha))

theorem squareExponentialReciprocal_right_top_zero :
    Tendsto squareExponentialReciprocal (𝓝[>] (0 : ℝ)) atTop := by
  have h := (Real.tendsto_exp_div_pow_atTop 2).comp tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx.ne'
  dsimp only [Function.comp_def, squareExponentialReciprocal]
  rw [one_div]
  field_simp [hx0]

theorem squareExponentialReciprocal_left_zero :
    Tendsto squareExponentialReciprocal (𝓝[<] (0 : ℝ)) (𝓝 0) := by
  have he : Tendsto (fun x : ℝ ↦ Real.exp (1 / x)) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using
      Real.tendsto_exp_atBot.comp tendsto_inv_nhdsLT_zero
  have hs : Tendsto (fun x : ℝ ↦ x ^ 2) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    simpa only [Pi.pow_apply, id_eq, zero_pow (by decide : (2 : ℕ) ≠ 0)] using!
      ((continuousAt_id : ContinuousAt (fun x : ℝ ↦ x) 0).pow 2).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0)
  change Tendsto (fun x : ℝ ↦ x ^ 2 * Real.exp (1 / x)) (𝓝[<] (0 : ℝ)) (𝓝 0)
  simpa only [mul_zero] using hs.mul he

theorem squareExponentialReciprocal_vertical_iff (a : ℝ) :
    HasVerticalAsymptoteWithinAt squareExponentialReciprocal puncturedRealDomain a ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    exact no_vertical_of_continuousAt (squareExponentialReciprocal_continuousAt ha) h
  · rintro rfl
    apply vertical_of_right_top _ squareExponentialReciprocal_right_top_zero
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx.ne'

theorem squareExponentialReciprocal_quotient_atTop :
    Tendsto (fun x : ℝ ↦ squareExponentialReciprocal x / x) atTop atTop := by
  have he : Tendsto (fun x : ℝ ↦ Real.exp (x⁻¹)) atTop (𝓝 1) :=
    Real.tendsto_exp_nhds_zero_nhds_one.comp tendsto_inv_atTop_zero
  have h := tendsto_id.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) he
  apply h.congr'
  filter_upwards [punctured_domain_atTop] with x hx
  dsimp only [squareExponentialReciprocal, id_eq]
  rw [one_div]
  field_simp [show x ≠ 0 from hx]

theorem squareExponentialReciprocal_quotient_atBot :
    Tendsto (fun x : ℝ ↦ squareExponentialReciprocal x / x) atBot atBot := by
  have he : Tendsto (fun x : ℝ ↦ Real.exp (x⁻¹)) atBot (𝓝 1) :=
    Real.tendsto_exp_nhds_zero_nhds_one.comp tendsto_inv_atBot_zero
  have h := tendsto_id.atBot_mul_pos (by norm_num : (0 : ℝ) < 1) he
  apply h.congr'
  filter_upwards [punctured_domain_atBot] with x hx
  dsimp only [squareExponentialReciprocal, id_eq]
  rw [one_div]
  field_simp [show x ≠ 0 from hx]

theorem squareExponentialReciprocal_no_residual_atTop (m b : ℝ) :
    ¬ Tendsto (fun x ↦ squareExponentialReciprocal x - (m * x + b)) atTop (𝓝 0) := by
  intro h
  have hq := (affine_residual_limit_atTop_iff squareExponentialReciprocal m b).mp h
  exact not_tendsto_nhds_of_tendsto_atTop squareExponentialReciprocal_quotient_atTop m hq.1

theorem squareExponentialReciprocal_no_residual_atBot (m b : ℝ) :
    ¬ Tendsto (fun x ↦ squareExponentialReciprocal x - (m * x + b)) atBot (𝓝 0) := by
  intro h
  have hq := (affine_residual_limit_atBot_iff squareExponentialReciprocal m b).mp h
  exact not_tendsto_nhds_of_tendsto_atBot squareExponentialReciprocal_quotient_atBot m hq.1

/-- Bài 13(c): tiệm cận đứng duy nhất x=0; không có tiệm cận ngang hay xiên. -/
theorem source_square_exponential_reciprocal_asymptotes :
    (∀ a : ℝ, HasVerticalAsymptoteWithinAt squareExponentialReciprocal puncturedRealDomain a ↔ a = 0) ∧
      (∀ b : ℝ, ¬ HasHorizontalAsymptoteWithin squareExponentialReciprocal puncturedRealDomain b) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin squareExponentialReciprocal puncturedRealDomain m b) := by
  refine ⟨squareExponentialReciprocal_vertical_iff, ?_, ?_⟩
  · intro b
    rw [full_tail_horizontal_iff punctured_domain_atTop punctured_domain_atBot,
      HasHorizontalAsymptote]
    rintro (h | h)
    · apply squareExponentialReciprocal_no_residual_atTop 0 b
      simpa only [zero_mul, zero_add, sub_self] using h.sub_const b
    · apply squareExponentialReciprocal_no_residual_atBot 0 b
      simpa only [zero_mul, zero_add, sub_self] using h.sub_const b
  · intro m b
    rw [full_tail_oblique_iff punctured_domain_atTop punctured_domain_atBot,
      HasObliqueAsymptote]
    rintro ⟨_, h | h⟩
    · exact squareExponentialReciprocal_no_residual_atTop m b h
    · exact squareExponentialReciprocal_no_residual_atBot m b h

theorem quadraticRational_continuousAt {a : ℝ} (ha : a ∈ rationalPoleDomain) :
    ContinuousAt quadraticRational a := by
  simpa only [quadraticRational] using! (continuousAt_id.pow 2).div
    (continuousAt_const.sub (continuousAt_id.pow 2)) ha

theorem quadraticRational_right_bot_one :
    Tendsto quadraticRational (𝓝[>] (1 : ℝ)) atBot := by
  have hd : Tendsto (fun x : ℝ ↦ 1 - x ^ 2) (𝓝[>] (1 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun x : ℝ ↦ 1 - x ^ 2) (1 : ℝ) :=
        continuousAt_const.sub (continuousAt_id.pow 2)
      simpa only [one_pow, sub_self] using hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : (1 : ℝ) < x := hx
      change 1 - x ^ 2 < 0
      nlinarith
  have hi := tendsto_inv_nhdsLT_zero.comp hd
  have hs : Tendsto (fun x : ℝ ↦ x ^ 2) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    simpa only [Pi.pow_apply, id_eq, one_pow] using!
      ((continuousAt_id : ContinuousAt (fun x : ℝ ↦ x) (1 : ℝ)).pow 2).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  have h := hi.atBot_mul_pos (by norm_num : (0 : ℝ) < 1) hs
  exact h.congr (fun x ↦ by dsimp [Function.comp_def, quadraticRational]; ring)

theorem quadraticRational_left_bot_neg_one :
    Tendsto quadraticRational (𝓝[<] (-1 : ℝ)) atBot := by
  have hd : Tendsto (fun x : ℝ ↦ 1 - x ^ 2) (𝓝[<] (-1 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun x : ℝ ↦ 1 - x ^ 2) (-1 : ℝ) :=
        continuousAt_const.sub (continuousAt_id.pow 2)
      simpa only [neg_one_sq, sub_self] using hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (-1 : ℝ) ≤ 𝓝 (-1 : ℝ))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x < (-1 : ℝ) := hx
      change 1 - x ^ 2 < 0
      nlinarith
  have hi := tendsto_inv_nhdsLT_zero.comp hd
  have hs : Tendsto (fun x : ℝ ↦ x ^ 2) (𝓝[<] (-1 : ℝ)) (𝓝 1) := by
    simpa only [Pi.pow_apply, id_eq, neg_one_sq] using!
      ((continuousAt_id : ContinuousAt (fun x : ℝ ↦ x) (-1 : ℝ)).pow 2).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (-1 : ℝ) ≤ 𝓝 (-1 : ℝ))
  have h := hi.atBot_mul_pos (by norm_num : (0 : ℝ) < 1) hs
  exact h.congr (fun x ↦ by dsimp [Function.comp_def, quadraticRational]; ring)

theorem quadraticRational_vertical_iff (a : ℝ) :
    HasVerticalAsymptoteWithinAt quadraticRational rationalPoleDomain a ↔ a = -1 ∨ a = 1 := by
  constructor
  · intro h
    by_contra hn
    have ha : a ∈ rationalPoleDomain := by
      change 1 - a ^ 2 ≠ 0
      intro hz
      have hf : (a - 1) * (a + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hf with hf | hf
      · exact hn (Or.inr (by linarith))
      · exact hn (Or.inl (by linarith))
    exact no_vertical_of_continuousAt (quadraticRational_continuousAt ha) h
  · rintro (rfl | rfl)
    · apply vertical_of_left_bot _ quadraticRational_left_bot_neg_one
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x < (-1 : ℝ) := hx
      change 1 - x ^ 2 ≠ 0
      intro h
      nlinarith
    · apply vertical_of_right_bot _ quadraticRational_right_bot_one
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : (1 : ℝ) < x := hx
      change 1 - x ^ 2 ≠ 0
      intro h
      nlinarith

theorem quadraticRational_limit_at_end {F : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ x⁻¹) F (𝓝 0))
    (hD : ∀ᶠ x : ℝ in F, x ∈ rationalPoleDomain) (hNe : ∀ᶠ x : ℝ in F, x ≠ 0) :
    Tendsto quadraticRational F (𝓝 (-1 : ℝ)) := by
  have hd := (hi.pow 2).sub_const 1
  norm_num only [zero_pow, zero_sub] at hd
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) F (𝓝 1)).div hd
    (by norm_num : (-1 : ℝ) ≠ 0)
  norm_num only [div_neg, div_one] at h
  apply h.congr'
  filter_upwards [hD, hNe] with x hx hx0
  have hxD : 1 - x ^ 2 ≠ 0 := hx
  have hinv : x⁻¹ ^ 2 - 1 ≠ 0 := by
    intro hz
    have he : x⁻¹ ^ 2 * x ^ 2 = 1 := by field_simp [hx0]
    rw [show x⁻¹ ^ 2 = 1 by linarith] at he
    apply hxD
    nlinarith
  change (1 : ℝ) / (x⁻¹ ^ 2 - 1) = x ^ 2 / (1 - x ^ 2)
  field_simp [hx0, hxD, hinv]

theorem quadraticRational_limit_atTop : Tendsto quadraticRational atTop (𝓝 (-1 : ℝ)) :=
  quadraticRational_limit_at_end tendsto_inv_atTop_zero rational_domain_atTop punctured_domain_atTop

theorem quadraticRational_limit_atBot : Tendsto quadraticRational atBot (𝓝 (-1 : ℝ)) :=
  quadraticRational_limit_at_end tendsto_inv_atBot_zero rational_domain_atBot punctured_domain_atBot

theorem quadraticRational_residual_atTop :
    Tendsto (fun x : ℝ ↦ quadraticRational x - (0 * x + (-1))) atTop (𝓝 0) := by
  simpa only [zero_mul, zero_add, sub_self] using quadraticRational_limit_atTop.sub_const (-1)

theorem quadraticRational_residual_atBot :
    Tendsto (fun x : ℝ ↦ quadraticRational x - (0 * x + (-1))) atBot (𝓝 0) := by
  simpa only [zero_mul, zero_add, sub_self] using quadraticRational_limit_atBot.sub_const (-1)

theorem quadraticRational_parameters_atTop (m b : ℝ) :
    Tendsto (fun x ↦ quadraticRational x - (m * x + b)) atTop (𝓝 0) ↔ m = 0 ∧ b = -1 :=
  affine_parameters_iff tendsto_inv_atTop_zero punctured_domain_atTop quadraticRational_residual_atTop m b

theorem quadraticRational_parameters_atBot (m b : ℝ) :
    Tendsto (fun x ↦ quadraticRational x - (m * x + b)) atBot (𝓝 0) ↔ m = 0 ∧ b = -1 :=
  affine_parameters_iff tendsto_inv_atBot_zero punctured_domain_atBot quadraticRational_residual_atBot m b

/-- Bài 13(d): tiệm cận đứng tại `±1`, tiệm cận ngang duy nhất `y = −1`, không có tiệm cận xiên. -/
theorem source_quadratic_rational_asymptotes :
    (∀ a : ℝ, HasVerticalAsymptoteWithinAt quadraticRational rationalPoleDomain a ↔ a = -1 ∨ a = 1) ∧
      (∀ b : ℝ, HasHorizontalAsymptoteWithin quadraticRational rationalPoleDomain b ↔ b = -1) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin quadraticRational rationalPoleDomain m b) := by
  refine ⟨quadraticRational_vertical_iff, ?_, ?_⟩
  · intro b
    rw [full_tail_horizontal_iff rational_domain_atTop rational_domain_atBot,
      HasHorizontalAsymptote]
    constructor
    · rintro (h | h)
      · exact tendsto_nhds_unique h quadraticRational_limit_atTop
      · exact tendsto_nhds_unique h quadraticRational_limit_atBot
    · rintro rfl
      exact Or.inl quadraticRational_limit_atTop
  · intro m b
    rw [full_tail_oblique_iff rational_domain_atTop rational_domain_atBot, HasObliqueAsymptote]
    rintro ⟨hm, h | h⟩
    · exact hm ((quadraticRational_parameters_atTop m b).mp h).1
    · exact hm ((quadraticRational_parameters_atBot m b).mp h).1

end calculus.Chapter04.Section04AsymptoteCollectionExercises
