import calculus.Chapter04.Section01Rules
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# 4.1.6: biểu diễn tham số và đạo hàm theo x

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 405–425. Công thức đạo hàm theo hoành độ dùng hàm ngược của hàm hoành độ trên ảnh một khoảng.
-/
namespace calculus.Chapter04.Section01Parametric
open Set Filter calculus.Chapter04.Section01Rules
open scoped Topology


def parametricPoint (φ ψ : ℝ → ℝ) (t : ℝ) : ℝ × ℝ := (φ t, ψ t)

def parametricCurve (φ ψ : ℝ → ℝ) (I : Set ℝ) : Set (ℝ × ℝ) :=
  parametricPoint φ ψ '' I

theorem parametricPoint_unique (φ ψ : ℝ → ℝ) (t : ℝ) :
    ∃! p : ℝ × ℝ, p.1 = φ t ∧ p.2 = ψ t := by
  refine ⟨(φ t, ψ t), ⟨rfl, rfl⟩, ?_⟩
  rintro p ⟨h1, h2⟩
  exact Prod.ext h1 h2


theorem unit_circle_parameter {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) :
    ∃ t ∈ Icc (0 : ℝ) (2 * Real.pi), Real.cos t = u ∧ Real.sin t = v := by
  have hu1 : -1 ≤ u := by nlinarith [sq_nonneg v, sq_nonneg (u + 1)]
  have hu2 : u ≤ 1 := by nlinarith [sq_nonneg v, sq_nonneg (u - 1)]
  have hv : 1 - u ^ 2 = v ^ 2 := by nlinarith
  by_cases hv0 : 0 ≤ v
  · refine ⟨Real.arccos u, ⟨Real.arccos_nonneg u, ?_⟩, Real.cos_arccos hu1 hu2, ?_⟩
    · linarith [Real.arccos_le_pi u, Real.pi_pos]
    · rw [Real.sin_arccos, hv, Real.sqrt_sq hv0]
  · refine ⟨2 * Real.pi - Real.arccos u, ⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [Real.arccos_le_pi u, Real.pi_pos]
    · linarith [Real.arccos_nonneg u]
    · rw [Real.cos_two_pi_sub, Real.cos_arccos hu1 hu2]
    · rw [Real.sin_two_pi_sub, Real.sin_arccos, hv, Real.sqrt_sq_eq_abs,
        abs_of_neg (lt_of_not_ge hv0), neg_neg]


theorem circle_parametric_image (x₀ y₀ r : ℝ) (hr : 0 < r) :
    parametricCurve (fun t ↦ x₀ + r * Real.cos t) (fun t ↦ y₀ + r * Real.sin t)
      (Icc 0 (2 * Real.pi)) = {p | (p.1 - x₀) ^ 2 + (p.2 - y₀) ^ 2 = r ^ 2} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    change (x₀ + r * Real.cos t - x₀) ^ 2 + (y₀ + r * Real.sin t - y₀) ^ 2 = r ^ 2
    nlinarith [Real.sin_sq_add_cos_sq t]
  · intro hp
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hunit : ((p.1 - x₀) / r) ^ 2 + ((p.2 - y₀) / r) ^ 2 = 1 := by
      change (p.1 - x₀) ^ 2 + (p.2 - y₀) ^ 2 = r ^ 2 at hp
      field_simp
      exact hp
    obtain ⟨t, ht, hc, hs⟩ := unit_circle_parameter hunit
    refine ⟨t, ht, ?_⟩
    apply Prod.ext
    · change x₀ + r * Real.cos t = p.1
      rw [hc]
      field_simp
      ring
    · change y₀ + r * Real.sin t = p.2
      rw [hs]
      field_simp
      ring


theorem ellipse_parametric_image (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    parametricCurve (fun t ↦ a * Real.cos t) (fun t ↦ b * Real.sin t)
      (Icc 0 (2 * Real.pi)) = {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 = 1} := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    change (a * Real.cos t) ^ 2 / a ^ 2 + (b * Real.sin t) ^ 2 / b ^ 2 = 1
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq t]
  · intro hp
    have hunit : (p.1 / a) ^ 2 + (p.2 / b) ^ 2 = 1 := by
      change p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 = 1 at hp
      simpa only [div_pow] using hp
    obtain ⟨t, ht, hc, hs⟩ := unit_circle_parameter hunit
    refine ⟨t, ht, ?_⟩
    apply Prod.ext
    · change a * Real.cos t = p.1
      rw [hc, mul_div_cancel₀ _ ha0]
    · change b * Real.sin t = p.2
      rw [hs, mul_div_cancel₀ _ hb0]


theorem interval_image_mem_nhds {φ : ℝ → ℝ} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hcont : ContinuousOn φ (Ioo a b)) (hinj : InjOn φ (Ioo a b)) :
    φ '' Ioo a b ∈ 𝓝 (φ t) := by
  let l := (a + t) / 2
  let r := (t + b) / 2
  have hl : l ∈ Ioo a b := by dsimp [l]; constructor <;> linarith [ht.1, ht.2]
  have hr : r ∈ Ioo a b := by dsimp [r]; constructor <;> linarith [ht.1, ht.2]
  have hlt : l < t := by dsimp [l]; linarith [ht.1]
  have htr : t < r := by dsimp [r]; linarith [ht.2]
  have hsub : Icc l r ⊆ Ioo a b := fun y hy ↦ ⟨lt_of_lt_of_le hl.1 hy.1, lt_of_le_of_lt hy.2 hr.2⟩
  have hsub' : Ioo l r ⊆ Ioo a b := (Ioo_subset_Icc_self).trans hsub
  rcases hcont.strictMonoOn_of_injOn_Ioo (lt_trans ht.1 ht.2) hinj with hm | hm
  · have hi := (hcont.mono hsub).image_Ioo_of_strictMonoOn (le_of_lt (hlt.trans htr)) (hm.mono hsub)
    have hx : φ t ∈ Ioo (φ l) (φ r) := ⟨hm hl ht hlt, hm ht hr htr⟩
    apply mem_of_superset (isOpen_Ioo.mem_nhds hx)
    rw [← hi]
    exact image_mono hsub'
  · have hi := (hcont.mono hsub).image_Ioo_of_strictAntiOn (le_of_lt (hlt.trans htr)) (hm.mono hsub)
    have hx : φ t ∈ Ioo (φ r) (φ l) := ⟨hm ht hr htr, hm hl ht hlt⟩
    apply mem_of_superset (isOpen_Ioo.mem_nhds hx)
    rw [← hi]
    exact image_mono hsub'


theorem parametric_inverse_continuousAt {φ g : ℝ → ℝ} {a b t : ℝ}
    (ht : t ∈ Ioo a b) (hcont : ContinuousOn φ (Ioo a b))
    (hgf : LeftInvOn g φ (Ioo a b)) : ContinuousAt g (φ t) := by
  have hinj : InjOn φ (Ioo a b) := by
    intro x hx y hy he
    have := congrArg g he
    simpa only [hgf hx, hgf hy] using this
  let J := φ '' Ioo a b
  have hgm : MapsTo g J (Ioo a b) := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [hgf hx] using hx
  have hfg : RightInvOn g φ J := by
    rintro y ⟨x, hx, rfl⟩
    rw [hgf hx]
  have himage : g '' J = Ioo a b := by
    apply Subset.antisymm
    · exact hgm.image_subset
    · intro x hx
      exact ⟨φ x, ⟨x, hx, rfl⟩, hgf hx⟩
  have hJ : J ∈ 𝓝 (φ t) := interval_image_mem_nhds ht hcont hinj
  have hGI : g '' J ∈ 𝓝 (g (φ t)) := by
    rw [himage, hgf ht]
    exact isOpen_Ioo.mem_nhds ht
  rcases hcont.strictMonoOn_of_injOn_Ioo (lt_trans ht.1 ht.2) hinj with hm | ha
  · have hmg : StrictMonoOn g J := by
      intro y hy z hz hyz
      apply (hm.lt_iff_lt (hgm hy) (hgm hz)).mp
      simpa only [hfg hy, hfg hz] using hyz
    exact hmg.continuousAt_of_image_mem_nhds hJ hGI
  · have hmg : StrictMonoOn (β := ℝᵒᵈ) g J := by
      intro y hy z hz hyz
      change g z < g y
      apply lt_of_not_ge
      intro hge
      have hbad := ha.antitoneOn (hgm hy) (hgm hz) hge
      exact hyz.not_ge (by simpa only [hfg hy, hfg hz] using hbad)
    exact hmg.continuousAt_of_image_mem_nhds hJ hGI


theorem parametric_inverse_hasDerivAt {φ g : ℝ → ℝ} {a b t : ℝ}
    (hφ : DifferentiableOn ℝ φ (Ioo a b)) (hgf : LeftInvOn g φ (Ioo a b))
    (ht : t ∈ Ioo a b) (hne : deriv φ t ≠ 0) :
    HasDerivAt g (1 / deriv φ t) (φ t) := by
  have hcont := hφ.continuousOn
  have hφat := (hφ t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
  have hinj : InjOn φ (Ioo a b) := by
    intro x hx y hy he
    have := congrArg g he
    simpa only [hgf hx, hgf hy] using this
  have hJ : φ '' Ioo a b ∈ 𝓝 (φ t) := interval_image_mem_nhds ht hcont hinj
  have hright : ∀ᶠ y in 𝓝 (φ t), φ (g y) = y := by
    filter_upwards [hJ] with y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hgf hx]
  exact inverse_derivative_of_continuous_inverse hφat.hasDerivAt hne
    (parametric_inverse_continuousAt ht hcont hgf) (hgf ht) hright


theorem parametric_derivative {φ ψ g : ℝ → ℝ} {a b : ℝ}
    (hφ : DifferentiableOn ℝ φ (Ioo a b)) (hψ : DifferentiableOn ℝ ψ (Ioo a b))
    (hgf : LeftInvOn g φ (Ioo a b)) (hφne : ∀ t ∈ Ioo a b, deriv φ t ≠ 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (ψ ∘ g) (deriv ψ t / deriv φ t) (φ t) := by
  have hψat := (hψ t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
  have hg := parametric_inverse_hasDerivAt hφ hgf ht (hφne t ht)
  have hψg : HasDerivAt ψ (deriv ψ t) (g (φ t)) := by
    simpa only [hgf ht] using hψat.hasDerivAt
  simpa only [div_eq_mul_inv, one_mul] using hψg.comp (φ t) hg


theorem parametric_derivative_chain {φ ψ g : ℝ → ℝ} {a b : ℝ}
    (hφ : DifferentiableOn ℝ φ (Ioo a b)) (hψ : DifferentiableOn ℝ ψ (Ioo a b))
    (hgf : LeftInvOn g φ (Ioo a b)) (hφne : ∀ t ∈ Ioo a b, deriv φ t ≠ 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    deriv (ψ ∘ g) (φ t) = deriv ψ (g (φ t)) * deriv g (φ t) ∧
      deriv (ψ ∘ g) (φ t) = deriv ψ t / deriv φ t := by
  have hfinal := (parametric_derivative hφ hψ hgf hφne ht).deriv
  refine ⟨?_, hfinal⟩
  rw [hfinal, (parametric_inverse_hasDerivAt hφ hgf ht (hφne t ht)).deriv, hgf ht]
  simp only [div_eq_mul_inv, one_mul]


theorem parametric_graph_relation {φ ψ g : ℝ → ℝ} {a b t : ℝ}
    (hgf : LeftInvOn g φ (Ioo a b)) (ht : t ∈ Ioo a b) :
    ψ (g (φ t)) = ψ t := congrArg ψ (hgf ht)

end calculus.Chapter04.Section01Parametric
