import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith

/-!
# Tiêu chuẩn cực trị theo dấu đạo hàm và ví dụ x²cosx

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1766–1774, dòng 1823–1825. Tiêu chuẩn đổi dấu không cần đạo hàm tại điểm xét; phần (iii) yêu cầu đạo hàm cùng dấu và khác 0 ở hai phía.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04ExtremumTests
open Set Filter
open scoped Topology

/-- Định lí 4.4.11(i): đạo hàm đổi từ dương sang âm. -/
theorem first_derivative_local_max {f : ℝ → ℝ} {x₀ : ℝ}
    (hc : ContinuousAt f x₀)
    (hd : ∀ᶠ x in 𝓝[≠] x₀, DifferentiableAt ℝ f x)
    (hl : ∀ᶠ x in 𝓝[<] x₀, 0 < deriv f x)
    (hr : ∀ᶠ x in 𝓝[>] x₀, deriv f x < 0) : IsLocalMax f x₀ :=
  isLocalMax_of_deriv hc hd (hl.mono fun _ hx ↦ hx.le) (hr.mono fun _ hx ↦ hx.le)

/-- Định lí 4.4.11(ii): đạo hàm đổi từ âm sang dương. -/
theorem first_derivative_local_min {f : ℝ → ℝ} {x₀ : ℝ}
    (hc : ContinuousAt f x₀)
    (hd : ∀ᶠ x in 𝓝[≠] x₀, DifferentiableAt ℝ f x)
    (hl : ∀ᶠ x in 𝓝[<] x₀, deriv f x < 0)
    (hr : ∀ᶠ x in 𝓝[>] x₀, 0 < deriv f x) : IsLocalMin f x₀ :=
  isLocalMin_of_deriv hc hd (hl.mono fun _ hx ↦ hx.le) (hr.mono fun _ hx ↦ hx.le)


theorem no_local_extremum_of_positive_deriv_repaired {f : ℝ → ℝ} {a b x₀ : ℝ}
    (ha : a < x₀) (hb : x₀ < b) (hc : ContinuousAt f x₀)
    (hd : ∀ x ∈ Ioo a b, x ≠ x₀ → DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Ioo a b, x ≠ x₀ → 0 < deriv f x) : ¬ IsLocalExtr f x₀ := by
  have hleft : ∀ x ∈ Ioo a x₀, f x < f x₀ := by
    intro x hx
    have hcont : ContinuousOn f (Icc x x₀) := by
      intro y hy
      rcases eq_or_lt_of_le hy.2 with he | he
      · subst y
        exact hc.continuousWithinAt
      · exact (hd y ⟨hx.1.trans_le hy.1, he.trans hb⟩ he.ne).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Ioo x x₀) := by
      intro y hy
      exact (hd y ⟨hx.1.trans hy.1, hy.2.trans hb⟩ hy.2.ne).differentiableWithinAt
    obtain ⟨c, hc', hsl⟩ := exists_deriv_eq_slope f hx.2 hcont hdiff
    have hs := hp c ⟨hx.1.trans hc'.1, hc'.2.trans hb⟩ hc'.2.ne
    rw [hsl] at hs
    exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hx.2)).mp hs)
  have hright : ∀ x ∈ Ioo x₀ b, f x₀ < f x := by
    intro x hx
    have hcont : ContinuousOn f (Icc x₀ x) := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with he | he
      · rw [← he]
        exact hc.continuousWithinAt
      · exact (hd y ⟨ha.trans he, hy.2.trans_lt hx.2⟩ he.ne').continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Ioo x₀ x) := by
      intro y hy
      exact (hd y ⟨ha.trans hy.1, hy.2.trans hx.2⟩ hy.1.ne').differentiableWithinAt
    obtain ⟨c, hc', hsl⟩ := exists_deriv_eq_slope f hx.1 hcont hdiff
    have hs := hp c ⟨ha.trans hc'.1, hc'.2.trans hx.2⟩ hc'.1.ne'
    rw [hsl] at hs
    exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hx.1)).mp hs)
  have hl : ∀ᶠ x in 𝓝[<] x₀, f x < f x₀ :=
    Filter.Eventually.mono (Ioo_mem_nhdsLT ha) fun x hx ↦ hleft x hx
  have hr : ∀ᶠ x in 𝓝[>] x₀, f x₀ < f x :=
    Filter.Eventually.mono (Ioo_mem_nhdsGT hb) fun x hx ↦ hright x hx
  rintro (hmin | hmax)
  · change ∀ᶠ x in 𝓝 x₀, f x₀ ≤ f x at hmin
    obtain ⟨x, hx, hneg⟩ := (hmin.filter_mono nhdsWithin_le_nhds).and hl |>.exists
    exact hneg.not_ge hx
  · change ∀ᶠ x in 𝓝 x₀, f x ≤ f x₀ at hmax
    obtain ⟨x, hx, hpos⟩ := (hmax.filter_mono nhdsWithin_le_nhds).and hr |>.exists
    exact hpos.not_ge hx


theorem no_local_extremum_of_negative_deriv_repaired {f : ℝ → ℝ} {a b x₀ : ℝ}
    (ha : a < x₀) (hb : x₀ < b) (hc : ContinuousAt f x₀)
    (hd : ∀ x ∈ Ioo a b, x ≠ x₀ → DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Ioo a b, x ≠ x₀ → deriv f x < 0) : ¬ IsLocalExtr f x₀ := by
  have hn : ¬ IsLocalExtr (fun x ↦ -f x) x₀ :=
    no_local_extremum_of_positive_deriv_repaired ha hb hc.neg
      (fun x hx hne ↦ (hd x hx hne).neg) (by
        intro x hx hne
        simpa only [deriv.fun_neg, neg_pos] using hp x hx hne)
  intro h
  exact hn h.neg


theorem constant_derivative_zero_has_local_extrema (c x₀ : ℝ) :
    (∀ x : ℝ, deriv (fun _ : ℝ ↦ c) x = 0) ∧
      IsLocalMin (fun _ : ℝ ↦ c) x₀ ∧ IsLocalMax (fun _ : ℝ ↦ c) x₀ :=
  ⟨fun x ↦ deriv_const x c, isLocalMin_const, isLocalMax_const⟩


def squareCosine (x : ℝ) : ℝ := x ^ 2 * Real.cos x


theorem squareCosine_hasDerivAt (x : ℝ) :
    HasDerivAt squareCosine (2 * x * Real.cos x - x ^ 2 * Real.sin x) x := by
  have h := (hasDerivAt_pow 2 x).mul (Real.hasDerivAt_cos x)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  ring

theorem squareCosine_deriv : deriv squareCosine =
    fun x ↦ 2 * x * Real.cos x - x ^ 2 * Real.sin x := by
  funext x
  exact (squareCosine_hasDerivAt x).deriv


theorem squareCosine_second_hasDerivAt (x : ℝ) :
    HasDerivAt (deriv squareCosine)
      (2 * Real.cos x - 4 * x * Real.sin x - x ^ 2 * Real.cos x) x := by
  rw [squareCosine_deriv]
  have h1 := ((hasDerivAt_id x).const_mul (2 : ℝ)).mul (Real.hasDerivAt_cos x)
  have h2 := (hasDerivAt_pow 2 x).mul (Real.hasDerivAt_sin x)
  apply ((h1.sub h2).congr_of_eventuallyEq
    (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  simp only [id_eq]
  ring

theorem squareCosine_second_deriv : deriv (deriv squareCosine) =
    fun x ↦ 2 * Real.cos x - 4 * x * Real.sin x - x ^ 2 * Real.cos x := by
  funext x
  exact (squareCosine_second_hasDerivAt x).deriv

/-- Ví dụ 4.4.13: giá trị tại 0, hai đạo hàm và cực tiểu địa phương. -/
theorem squareCosine_source_example :
    squareCosine 0 = 0 ∧ deriv squareCosine 0 = 0 ∧
      deriv (deriv squareCosine) 0 = 2 ∧ IsLocalMin squareCosine 0 := by
  have hf : deriv squareCosine 0 = 0 := by simp [squareCosine_deriv]
  have hff : deriv (deriv squareCosine) 0 = 2 := by simp [squareCosine_second_deriv]
  exact ⟨by simp [squareCosine], hf, hff,
    isLocalMin_of_deriv_deriv_pos (by rw [hff]; norm_num) hf
      (squareCosine_hasDerivAt 0).continuousAt⟩

end calculus.Chapter04.Section04ExtremumTests
