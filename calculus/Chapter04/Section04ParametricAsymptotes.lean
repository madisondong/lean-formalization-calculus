import calculus.Chapter04.Section04Asymptotes

/-!
# §4.4: tiệm cận của đường cong theo tham số

Nguồn: dòng 2231–2239. Bộ lọc `L` chỉ hướng tiếp cận trong miền tham số; khoảng cách đến tiệm cận là khoảng cách Euclid.
-/

set_option autoImplicit false
open Filter Set Topology
namespace calculus.Chapter04.Section04ParametricAsymptotes

/-- Hoành độ tiến tới một giá trị hữu hạn; tung độ tiến tới vô cùng. -/
def ParametricVerticalAsymptote (φ ψ : ℝ → ℝ) (L : Filter ℝ) (a : ℝ) : Prop :=
  Tendsto (fun t ↦ |φ t - a|) L (𝓝 0) ∧
    (Tendsto ψ L atTop ∨ Tendsto ψ L atBot)

/-- Tung độ tiến tới một giá trị hữu hạn; hoành độ tiến tới vô cùng. -/
def ParametricHorizontalAsymptote (φ ψ : ℝ → ℝ) (L : Filter ℝ) (b : ℝ) : Prop :=
  Tendsto (fun t ↦ |ψ t - b|) L (𝓝 0) ∧
    (Tendsto φ L atTop ∨ Tendsto φ L atBot)

/-- Tiệm cận `y = mx+b`, với `m ≠ 0`, được xét theo khoảng cách Euclid đến đường thẳng. -/
def ParametricObliqueAsymptote (φ ψ : ℝ → ℝ) (L : Filter ℝ) (m b : ℝ) : Prop :=
  m ≠ 0 ∧ (Tendsto φ L atTop ∨ Tendsto φ L atBot) ∧
    Tendsto (fun t ↦ |ψ t - (m * φ t + b)| / Real.sqrt (m ^ 2 + 1)) L (𝓝 0)

theorem vertical_asymptote_from_coordinates {φ ψ : ℝ → ℝ} {L : Filter ℝ} {a : ℝ}
    (hφ : Tendsto φ L (𝓝 a)) (hψ : Tendsto ψ L atTop) :
    ParametricVerticalAsymptote φ ψ L a := by
  refine ⟨?_, Or.inl hψ⟩
  simpa only [sub_self, abs_zero] using! (hφ.sub_const a).abs

theorem horizontal_asymptote_from_coordinates {φ ψ : ℝ → ℝ} {L : Filter ℝ} {b : ℝ}
    (hφ : Tendsto φ L atTop) (hψ : Tendsto ψ L (𝓝 b)) :
    ParametricHorizontalAsymptote φ ψ L b := by
  refine ⟨?_, Or.inl hφ⟩
  simpa only [sub_self, abs_zero] using! (hψ.sub_const b).abs


theorem oblique_asymptote_from_printed_conditions {φ ψ : ℝ → ℝ} {L : Filter ℝ}
    [NeBot L] {m b : ℝ} (hφ : Tendsto φ L atTop) (hψ : Tendsto ψ L atTop)
    (hq : Tendsto (fun t ↦ φ t / ψ t) L (𝓝 m))
    (hr : Tendsto (fun t ↦ ψ t - m * φ t) L (𝓝 b)) :
    Tendsto (fun t ↦ φ t / ψ t) L (𝓝 m) ∧ ParametricObliqueAsymptote φ ψ L m b := by
  have hm : m ≠ 0 := by
    intro hz
    have hb : Tendsto ψ L (𝓝 b) := by simpa only [hz, zero_mul, sub_zero] using! hr
    exact not_tendsto_nhds_of_tendsto_atTop hψ b hb
  have hzero : Tendsto (fun t ↦ ψ t - (m * φ t + b)) L (𝓝 0) := by
    apply (show Tendsto (fun t ↦ (ψ t - m * φ t) - b) L (𝓝 0) from by
      simpa only [sub_self] using! hr.sub_const b).congr
    intro t
    ring
  refine ⟨hq, hm, Or.inl hφ, ?_⟩
  simpa only [abs_zero, zero_div] using! hzero.abs.div_const (Real.sqrt (m ^ 2 + 1))


theorem source_parametric_asymptote_criteria (φ ψ : ℝ → ℝ) (L : Filter ℝ) [NeBot L] :
    (∀ a, Tendsto φ L (𝓝 a) → Tendsto ψ L atTop → ParametricVerticalAsymptote φ ψ L a) ∧
    (∀ b, Tendsto φ L atTop → Tendsto ψ L (𝓝 b) → ParametricHorizontalAsymptote φ ψ L b) ∧
    (∀ m b, Tendsto φ L atTop → Tendsto ψ L atTop →
      Tendsto (fun t ↦ φ t / ψ t) L (𝓝 m) →
      Tendsto (fun t ↦ ψ t - m * φ t) L (𝓝 b) → ParametricObliqueAsymptote φ ψ L m b) :=
  ⟨fun _ hφ hψ ↦ vertical_asymptote_from_coordinates hφ hψ,
    fun _ hφ hψ ↦ horizontal_asymptote_from_coordinates hφ hψ,
    fun _ _ hφ hψ hq hr ↦ (oblique_asymptote_from_printed_conditions hφ hψ hq hr).2⟩

end calculus.Chapter04.Section04ParametricAsymptotes
