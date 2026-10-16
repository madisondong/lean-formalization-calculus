import calculus.Chapter04.Section04PolarEquations
import Mathlib.Tactic.Ring

/-!
# §4.4: đối xứng trong tọa độ cực

Nguồn: nhận xét dòng 2592–2594. Góc chạy trên ℝ; bán kính có dấu, kể cả tại gốc.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section04PolarSymmetry
open Set
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations

def polarAxisReflection (z : ℂ) : ℂ := Complex.mk z.re (-z.im)

def perpendicularAxisReflection (z : ℂ) : ℂ := Complex.mk (-z.re) z.im

theorem polar_axis_reflection_involution (z : ℂ) :
    polarAxisReflection (polarAxisReflection z) = z := by
  apply Complex.ext <;> simp [polarAxisReflection]

theorem perpendicular_axis_reflection_involution (z : ℂ) :
    perpendicularAxisReflection (perpendicularAxisReflection z) = z := by
  apply Complex.ext <;> simp [perpendicularAxisReflection]

theorem signed_polar_neg_angle (r θ : ℝ) :
    signedPolarPoint r (-θ) = polarAxisReflection (signedPolarPoint r θ) := by
  apply Complex.ext
  · simp [signedPolarPoint_re, polarAxisReflection, Real.cos_neg]
  · simp [signedPolarPoint_im, polarAxisReflection, Real.sin_neg]

theorem signed_polar_pi_sub_angle (r θ : ℝ) :
    signedPolarPoint r (Real.pi-θ) = perpendicularAxisReflection (signedPolarPoint r θ) := by
  apply Complex.ext
  · simp [signedPolarPoint_re, perpendicularAxisReflection, Real.cos_pi_sub]
  · simp [signedPolarPoint_im, perpendicularAxisReflection, Real.sin_pi_sub]

theorem signed_polar_add_pi (r θ : ℝ) :
    signedPolarPoint r (θ+Real.pi) = -signedPolarPoint r θ := by
  rw [← signedPolarPoint_neg_radius_eq_add_pi, signedPolarPoint_neg_radius]

/-- Dòng 2592: bất biến khi đổi dấu góc cho đối xứng toàn quỹ tích qua trục cực. -/
theorem source_polar_axis_symmetry (E : ℝ → ℝ → Prop)
    (hE : ∀ r θ : ℝ, E r (-θ) ↔ E r θ) :
    ∀ z : ℂ, z ∈ polarLocus E ↔ polarAxisReflection z ∈ polarLocus E := by
  have preserve : ∀ z : ℂ, z ∈ polarLocus E → polarAxisReflection z ∈ polarLocus E := by
    rintro z ⟨r, θ, he, hz⟩
    refine ⟨r, -θ, (hE r θ).mpr he, ?_⟩
    rw [signed_polar_neg_angle, hz]
  intro z
  exact ⟨preserve z, fun h ↦ by
    simpa only [polar_axis_reflection_involution] using preserve (polarAxisReflection z) h⟩

theorem central_symmetry_of_radius_invariance (E : ℝ → ℝ → Prop)
    (hE : ∀ r θ : ℝ, E (-r) θ ↔ E r θ) :
    ∀ z : ℂ, z ∈ polarLocus E ↔ -z ∈ polarLocus E := by
  have preserve : ∀ z : ℂ, z ∈ polarLocus E → -z ∈ polarLocus E := by
    rintro z ⟨r, θ, he, hz⟩
    refine ⟨-r, θ, (hE r θ).mpr he, ?_⟩
    rw [signedPolarPoint_neg_radius, hz]
  intro z
  exact ⟨preserve z, fun h ↦ by simpa only [neg_neg] using preserve (-z) h⟩

theorem central_symmetry_of_angle_invariance (E : ℝ → ℝ → Prop)
    (hE : ∀ r θ : ℝ, E r (θ+Real.pi) ↔ E r θ) :
    ∀ z : ℂ, z ∈ polarLocus E ↔ -z ∈ polarLocus E := by
  have preserve : ∀ z : ℂ, z ∈ polarLocus E → -z ∈ polarLocus E := by
    rintro z ⟨r, θ, he, hz⟩
    refine ⟨r, θ+Real.pi, (hE r θ).mpr he, ?_⟩
    rw [signed_polar_add_pi, hz]
  intro z
  exact ⟨preserve z, fun h ↦ by simpa only [neg_neg] using preserve (-z) h⟩

/-- Dòng 2593: hai điều kiện đủ cho quỹ tích đối xứng qua gốc. -/
theorem source_polar_origin_symmetry (E : ℝ → ℝ → Prop)
    (hE : (∀ r θ : ℝ, E (-r) θ ↔ E r θ) ∨
      (∀ r θ : ℝ, E r (θ+Real.pi) ↔ E r θ)) :
    ∀ z : ℂ, z ∈ polarLocus E ↔ -z ∈ polarLocus E := by
  rcases hE with hr | hθ
  · exact central_symmetry_of_radius_invariance E hr
  · exact central_symmetry_of_angle_invariance E hθ

/-- Dòng 2594: đường thẳng vuông góc trục cực là trục y Descartes. -/
theorem source_polar_perpendicular_axis_symmetry (E : ℝ → ℝ → Prop)
    (hE : ∀ r θ : ℝ, E r (Real.pi-θ) ↔ E r θ) :
    ∀ z : ℂ, z ∈ polarLocus E ↔ perpendicularAxisReflection z ∈ polarLocus E := by
  have preserve : ∀ z : ℂ, z ∈ polarLocus E → perpendicularAxisReflection z ∈ polarLocus E := by
    rintro z ⟨r, θ, he, hz⟩
    refine ⟨r, Real.pi-θ, (hE r θ).mpr he, ?_⟩
    rw [signed_polar_pi_sub_angle, hz]
  intro z
  exact ⟨preserve z, fun h ↦ by
    simpa only [perpendicular_axis_reflection_involution] using preserve (perpendicularAxisReflection z) h⟩

end calculus.Chapter04.Section04PolarSymmetry
