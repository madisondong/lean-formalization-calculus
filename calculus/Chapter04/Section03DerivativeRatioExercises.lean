import calculus.Chapter04.Section04InfiniteExtensions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# §4.3, Bài tập 10: giới hạn đạo hàm và thương f(x)/x

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1135–1142. Các đạo hàm thông thường chỉ xét ở `x > 0`; cả hai mệnh đề đảo đều sai.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter04.Section03DerivativeRatioExercises
open calculus.Chapter04.Section04InfiniteExtensions


theorem hasDerivAt_of_differentiableOn_nonnegative {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt f (deriv f x) x :=
  (hf.differentiableAt (Ici_mem_nhds hx)).hasDerivAt


theorem function_ratio_limit_of_derivative_limit {f : ℝ → ℝ} {l : Filter ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0))
    (hl : Tendsto (deriv f) atTop l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / x) atTop l := by
  have hq : Tendsto (fun x ↦ deriv f x / (1 : ℝ)) atTop l := by
    simpa only [div_one] using hl
  exact lhopital_infinite_atTop_hasDerivAt
    (a := 0) (f := f) (f' := deriv f) (g := fun x ↦ x) (g' := fun _ ↦ 1)
    (fun _ hx ↦ hasDerivAt_of_differentiableOn_nonnegative hf hx)
    (fun x _ ↦ hasDerivAt_id x) (fun _ _ ↦ one_ne_zero)
    (Or.inl tendsto_id) hq hlt

/-- Bài 10(a): nếu `f′ → a` hữu hạn thì `f(x)/x → a`. -/
theorem function_ratio_limit_of_finite_derivative_limit {f : ℝ → ℝ} {a : ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0))
    (ha : Tendsto (deriv f) atTop (𝓝 a)) :
    Tendsto (fun x ↦ f x / x) atTop (𝓝 a) :=
  function_ratio_limit_of_derivative_limit hf ha (Or.inl ⟨a, rfl⟩)

/-- Bài 10(b): `f′(x) → +∞` kéo theo `f(x)/x → +∞` khi `x → +∞`. -/
theorem function_ratio_atTop_of_derivative_atTop {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0))
    (ha : Tendsto (deriv f) atTop atTop) :
    Tendsto (fun x ↦ f x / x) atTop atTop :=
  function_ratio_limit_of_derivative_limit hf ha (Or.inr (Or.inl rfl))


noncomputable def twoPiSequence (n : ℕ) : ℝ := (n : ℝ) * (2 * Real.pi)


noncomputable def oddPiSequence (n : ℕ) : ℝ := Real.pi + (n : ℝ) * (2 * Real.pi)

theorem twoPiSequence_tendsto_atTop : Tendsto twoPiSequence atTop atTop := by
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by positivity)

theorem oddPiSequence_tendsto_atTop : Tendsto oddPiSequence atTop atTop := by
  exact tendsto_atTop_add_const_left atTop Real.pi twoPiSequence_tendsto_atTop


theorem oddPiSequence_positive (n : ℕ) : 0 < oddPiSequence n := by
  unfold oddPiSequence
  positivity


theorem sine_div_identity_tendsto_zero :
    Tendsto (fun x : ℝ ↦ Real.sin x / x) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x : ℝ ↦ 1 / x) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    simpa only [Real.norm_eq_abs, abs_div, abs_of_pos hpos] using
      div_le_div_of_nonneg_right (Real.abs_sin_le_one x) hpos.le
  · simpa only [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))


theorem cosine_no_finite_limit_atTop :
    ¬ ∃ a : ℝ, Tendsto Real.cos atTop (𝓝 a) := by
  rintro ⟨a, ha⟩
  have hOne : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, twoPiSequence, Real.cos_nat_mul_two_pi] using
      ha.comp twoPiSequence_tendsto_atTop
  have hNegOne : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, oddPiSequence, Real.cos_add_nat_mul_two_pi,
      Real.cos_pi] using ha.comp oddPiSequence_tendsto_atTop
  have h1 : (1 : ℝ) = a := tendsto_nhds_unique tendsto_const_nhds hOne
  have hm1 : (-1 : ℝ) = a := tendsto_nhds_unique tendsto_const_nhds hNegOne
  linarith


theorem finite_derivative_ratio_converse_counterexample :
    ∃ f : ℝ → ℝ, DifferentiableOn ℝ f (Ici 0) ∧
      Tendsto (fun x ↦ f x / x) atTop (𝓝 0) ∧
      ¬ ∃ a : ℝ, Tendsto (deriv f) atTop (𝓝 a) := by
  refine ⟨Real.sin, Real.differentiable_sin.differentiableOn,
    sine_div_identity_tendsto_zero, ?_⟩
  simpa only [Real.deriv_sin] using cosine_no_finite_limit_atTop


noncomputable def squareAddTwoXSin (x : ℝ) : ℝ := x ^ 2 + 2 * x * Real.sin x


theorem squareAddTwoXSin_hasDerivAt (x : ℝ) :
    HasDerivAt squareAddTwoXSin
      (2 * x + (2 * Real.sin x + 2 * x * Real.cos x)) x := by
  have hsquare : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id x).fun_pow 2
  have hterm : HasDerivAt (fun y : ℝ ↦ 2 * y * Real.sin y)
      (2 * Real.sin x + 2 * x * Real.cos x) x := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id x).const_mul 2).fun_mul (Real.hasDerivAt_sin x)
  exact hsquare.fun_add hterm

theorem squareAddTwoXSin_deriv (x : ℝ) :
    deriv squareAddTwoXSin x = 2 * x + (2 * Real.sin x + 2 * x * Real.cos x) :=
  (squareAddTwoXSin_hasDerivAt x).deriv


theorem squareAddTwoXSin_div_identity_tendsto_atTop :
    Tendsto (fun x : ℝ ↦ squareAddTwoXSin x / x) atTop atTop := by
  have hlow : ∀ᶠ x : ℝ in atTop, x - 2 ≤ squareAddTwoXSin x / x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hne : x ≠ 0 := (lt_of_lt_of_le zero_lt_one hx).ne'
    have he : squareAddTwoXSin x / x = x + 2 * Real.sin x := by
      unfold squareAddTwoXSin
      field_simp [hne]
    rw [he]
    linarith [Real.neg_one_le_sin x]
  apply tendsto_atTop_mono' atTop hlow
  simpa only [sub_eq_add_neg, id_eq] using
    tendsto_atTop_add_const_right atTop (-2 : ℝ) tendsto_id


theorem squareAddTwoXSin_derivative_zero_oddPiSequence (n : ℕ) :
    deriv squareAddTwoXSin (oddPiSequence n) = 0 := by
  rw [squareAddTwoXSin_deriv]
  simp only [oddPiSequence, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi,
    Real.sin_pi, Real.cos_pi, mul_zero, zero_add, mul_neg_one]
  ring


theorem squareAddTwoXSin_derivative_not_tendsto_atTop :
    ¬ Tendsto (deriv squareAddTwoXSin) atTop atTop := by
  intro h
  have hz : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, squareAddTwoXSin_derivative_zero_oddPiSequence] using
      h.comp oddPiSequence_tendsto_atTop
  exact not_tendsto_const_atTop (0 : ℝ) atTop hz


theorem infinite_derivative_ratio_converse_counterexample :
    ∃ f : ℝ → ℝ, DifferentiableOn ℝ f (Ici 0) ∧
      Tendsto (fun x ↦ f x / x) atTop atTop ∧
      ¬ Tendsto (deriv f) atTop atTop := by
  have hd : Differentiable ℝ squareAddTwoXSin :=
    fun x ↦ (squareAddTwoXSin_hasDerivAt x).differentiableAt
  exact ⟨squareAddTwoXSin, hd.differentiableOn,
    squareAddTwoXSin_div_identity_tendsto_atTop, squareAddTwoXSin_derivative_not_tendsto_atTop⟩

/-- Bài 10(c): cả hai mệnh đề đảo đều có phản ví dụ. -/
theorem derivative_ratio_converse_answers :
    (∃ f : ℝ → ℝ, DifferentiableOn ℝ f (Ici 0) ∧
      Tendsto (fun x ↦ f x / x) atTop (𝓝 0) ∧
      ¬ ∃ a : ℝ, Tendsto (deriv f) atTop (𝓝 a)) ∧
    (∃ f : ℝ → ℝ, DifferentiableOn ℝ f (Ici 0) ∧
      Tendsto (fun x ↦ f x / x) atTop atTop ∧
      ¬ Tendsto (deriv f) atTop atTop) :=
  ⟨finite_derivative_ratio_converse_counterexample,
    infinite_derivative_ratio_converse_counterexample⟩

end calculus.Chapter04.Section03DerivativeRatioExercises
