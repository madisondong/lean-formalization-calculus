import calculus.Chapter03.Section03Exercises
import calculus.Chapter04.Section01Parametric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

/-!
# §4.4: tiếp tuyến trong tọa độ cực

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2571–2576. Giới hạn dây cung xét trong miền `D`, trên miền mẫu khác 0 và có điểm tụ. Bán kính có dấu; tiếp tuyến đứng dùng giới hạn `Δx/Δy → 0`, không quy định dấu vô cùng của `dy/dx`.
-/

set_option autoImplicit false

namespace calculus.Chapter04.Section04PolarTangents

open Set Filter
open scoped Topology
open calculus.Chapter03.Section02
open calculus.Chapter03.Section03Exercises
open calculus.Chapter04.Section01Parametric


noncomputable def polarX (r : ℝ → ℝ) (φ : ℝ) : ℝ := r φ * Real.cos φ


noncomputable def polarY (r : ℝ → ℝ) (φ : ℝ) : ℝ := r φ * Real.sin φ

/-- Công thức, dòng 2572: hai tọa độ Descartes của đường cong cực. -/
theorem polar_cartesian_parametrization (r : ℝ → ℝ) (φ : ℝ) :
    parametricPoint (polarX r) (polarY r) φ =
      (r φ * Real.cos φ, r φ * Real.sin φ) := rfl


theorem polarX_hasDerivAt {r : ℝ → ℝ} {r' φ : ℝ}
    (hr : HasDerivAt r r' φ) :
    HasDerivAt (polarX r) (r' * Real.cos φ - r φ * Real.sin φ) φ := by
  change HasDerivAt (fun t : ℝ ↦ r t * Real.cos t)
    (r' * Real.cos φ - r φ * Real.sin φ) φ
  exact (hr.mul (Real.hasDerivAt_cos φ)).congr_deriv (by ring)


theorem polarY_hasDerivAt {r : ℝ → ℝ} {r' φ : ℝ}
    (hr : HasDerivAt r r' φ) :
    HasDerivAt (polarY r) (r' * Real.sin φ + r φ * Real.cos φ) φ := by
  change HasDerivAt (fun t : ℝ ↦ r t * Real.sin t)
    (r' * Real.sin φ + r φ * Real.cos φ) φ
  exact hr.mul (Real.hasDerivAt_sin φ)

/-- Dòng 2575: đạo hàm hai tọa độ của đường cong cực. -/
theorem polar_coordinate_derivatives {r : ℝ → ℝ} {r' φ : ℝ}
    (hr : HasDerivAt r r' φ) :
    deriv (polarX r) φ = r' * Real.cos φ - r φ * Real.sin φ ∧
      deriv (polarY r) φ = r' * Real.sin φ + r φ * Real.cos φ :=
  ⟨(polarX_hasDerivAt hr).deriv, (polarY_hasDerivAt hr).deriv⟩

/-- Dòng 2575: thương hai đạo hàm tọa độ khi mẫu khác 0. -/
theorem polar_derivative_ratio {r : ℝ → ℝ} {r' φ : ℝ}
    (hr : HasDerivAt r r' φ)
    (hx : r' * Real.cos φ - r φ * Real.sin φ ≠ 0) :
    deriv (polarX r) φ ≠ 0 ∧
      deriv (polarY r) φ / deriv (polarX r) φ =
        (r' * Real.sin φ + r φ * Real.cos φ) /
          (r' * Real.cos φ - r φ * Real.sin φ) := by
  constructor
  · rw [(polarX_hasDerivAt hr).deriv]
    exact hx
  · rw [(polarY_hasDerivAt hr).deriv, (polarX_hasDerivAt hr).deriv]


def xSecantDomain (D : Set ℝ) (r : ℝ → ℝ) (φ : ℝ) : Set ℝ :=
  {t : ℝ | t ∈ D ∧ polarX r t - polarX r φ ≠ 0}


def ySecantDomain (D : Set ℝ) (r : ℝ → ℝ) (φ : ℝ) : Set ℝ :=
  {t : ℝ | t ∈ D ∧ polarY r t - polarY r φ ≠ 0}


theorem xSecantDomain_accumulation {D : Set ℝ} {r : ℝ → ℝ} {r' φ : ℝ}
    (hD : D ∈ 𝓝 φ) (hr : HasDerivAt r r' φ)
    (hx : r' * Real.cos φ - r φ * Real.sin φ ≠ 0) :
    AccumulationPointOf (xSecantDomain D r φ) φ := by
  have hc := (polarX_hasDerivAt hr).sub_const (polarX r φ)
  have ha := derivative_quotient_domain_accumulation hc (sub_self (polarX r φ)) hx
  apply accumulationPointOf_mono (accumulationPointOf_inter_nhds ha hD)
  intro t ht
  exact ⟨ht.2, ht.1⟩


theorem ySecantDomain_accumulation {D : Set ℝ} {r : ℝ → ℝ} {r' φ : ℝ}
    (hD : D ∈ 𝓝 φ) (hr : HasDerivAt r r' φ)
    (hy : r' * Real.sin φ + r φ * Real.cos φ ≠ 0) :
    AccumulationPointOf (ySecantDomain D r φ) φ := by
  have hc := (polarY_hasDerivAt hr).sub_const (polarY r φ)
  have ha := derivative_quotient_domain_accumulation hc (sub_self (polarY r φ)) hy
  apply accumulationPointOf_mono (accumulationPointOf_inter_nhds ha hD)
  intro t ht
  exact ⟨ht.2, ht.1⟩


theorem polar_secant_slope_limit {D : Set ℝ} {r : ℝ → ℝ} {r' φ : ℝ}
    (hD : D ∈ 𝓝 φ) (hr : HasDerivAt r r' φ)
    (hx : r' * Real.cos φ - r φ * Real.sin φ ≠ 0) :
    DomainLimit (xSecantDomain D r φ)
      (fun t ↦ (polarY r t - polarY r φ) / (polarX r t - polarX r φ)) φ
      ((r' * Real.sin φ + r φ * Real.cos φ) /
        (r' * Real.cos φ - r φ * Real.sin φ)) := by
  exact ratio_of_derivative_slopes (xSecantDomain_accumulation hD hr hx)
    ((polarY_hasDerivAt hr).sub_const (polarY r φ))
    ((polarX_hasDerivAt hr).sub_const (polarX r φ))
    (sub_self (polarY r φ)) (sub_self (polarX r φ)) hx


theorem polar_inverse_secant_slope_limit {D : Set ℝ} {r : ℝ → ℝ} {r' φ : ℝ}
    (hD : D ∈ 𝓝 φ) (hr : HasDerivAt r r' φ)
    (hy : r' * Real.sin φ + r φ * Real.cos φ ≠ 0) :
    DomainLimit (ySecantDomain D r φ)
      (fun t ↦ (polarX r t - polarX r φ) / (polarY r t - polarY r φ)) φ
      ((r' * Real.cos φ - r φ * Real.sin φ) /
        (r' * Real.sin φ + r φ * Real.cos φ)) := by
  exact ratio_of_derivative_slopes (ySecantDomain_accumulation hD hr hy)
    ((polarX_hasDerivAt hr).sub_const (polarX r φ))
    ((polarY_hasDerivAt hr).sub_const (polarY r φ))
    (sub_self (polarX r φ)) (sub_self (polarY r φ)) hy


def HasHorizontalPolarTangent (D : Set ℝ) (r : ℝ → ℝ) (φ : ℝ) : Prop :=
  DomainLimit (xSecantDomain D r φ)
    (fun t ↦ (polarY r t - polarY r φ) / (polarX r t - polarX r φ)) φ 0


def HasVerticalPolarTangent (D : Set ℝ) (r : ℝ → ℝ) (φ : ℝ) : Prop :=
  DomainLimit (ySecantDomain D r φ)
    (fun t ↦ (polarX r t - polarX r φ) / (polarY r t - polarY r φ)) φ 0


theorem horizontal_polar_tangent_iff {D : Set ℝ} {r : ℝ → ℝ} {r' φ : ℝ}
    (hD : D ∈ 𝓝 φ) (hr : HasDerivAt r r' φ)
    (hx : r' * Real.cos φ - r φ * Real.sin φ ≠ 0) :
    HasHorizontalPolarTangent D r φ ↔ r' * Real.sin φ + r φ * Real.cos φ = 0 := by
  constructor
  · intro h
    have hzero := domainLimit_unique (polar_secant_slope_limit hD hr hx) h
    exact (div_eq_zero_iff.mp hzero).resolve_right hx
  · intro hy
    change DomainLimit (xSecantDomain D r φ)
      (fun t ↦ (polarY r t - polarY r φ) / (polarX r t - polarX r φ)) φ 0
    simpa only [hy, zero_div] using polar_secant_slope_limit hD hr hx


theorem vertical_polar_tangent_iff {D : Set ℝ} {r : ℝ → ℝ} {r' φ : ℝ}
    (hD : D ∈ 𝓝 φ) (hr : HasDerivAt r r' φ)
    (hy : r' * Real.sin φ + r φ * Real.cos φ ≠ 0) :
    HasVerticalPolarTangent D r φ ↔ r' * Real.cos φ - r φ * Real.sin φ = 0 := by
  constructor
  · intro h
    have hzero := domainLimit_unique (polar_inverse_secant_slope_limit hD hr hy) h
    exact (div_eq_zero_iff.mp hzero).resolve_right hy
  · intro hx
    change DomainLimit (ySecantDomain D r φ)
      (fun t ↦ (polarX r t - polarX r φ) / (polarY r t - polarY r φ)) φ 0
    simpa only [hx, zero_div] using polar_inverse_secant_slope_limit hD hr hy

/-- Dòng 2576: điều kiện tiếp tuyến ngang của đường cong cực. -/
theorem source_horizontal_polar_tangent {D : Set ℝ} {r : ℝ → ℝ} {r' φ : ℝ}
    (hD : D ∈ 𝓝 φ) (hr : HasDerivAt r r' φ)
    (hy : r' * Real.sin φ + r φ * Real.cos φ = 0)
    (hx : r' * Real.cos φ - r φ * Real.sin φ ≠ 0) :
    HasHorizontalPolarTangent D r φ :=
  (horizontal_polar_tangent_iff hD hr hx).mpr hy

/-- Dòng 2576: điều kiện tiếp tuyến đứng, không quy định dấu vô cùng của `dy/dx`. -/
theorem source_vertical_polar_tangent {D : Set ℝ} {r : ℝ → ℝ} {r' φ : ℝ}
    (hD : D ∈ 𝓝 φ) (hr : HasDerivAt r r' φ)
    (hx : r' * Real.cos φ - r φ * Real.sin φ = 0)
    (hy : r' * Real.sin φ + r φ * Real.cos φ ≠ 0) :
    HasVerticalPolarTangent D r φ :=
  (vertical_polar_tangent_iff hD hr hy).mpr hx


theorem polar_graph_hasDerivAt {r g : ℝ → ℝ} {a b φ : ℝ}
    (hr : DifferentiableOn ℝ r (Ioo a b))
    (hgf : LeftInvOn g (polarX r) (Ioo a b)) (hφ : φ ∈ Ioo a b)
    (hx : deriv r φ * Real.cos φ - r φ * Real.sin φ ≠ 0) :
    HasDerivAt (polarY r ∘ g)
      ((deriv r φ * Real.sin φ + r φ * Real.cos φ) /
        (deriv r φ * Real.cos φ - r φ * Real.sin φ)) (polarX r φ) := by
  have hX : DifferentiableOn ℝ (polarX r) (Ioo a b) := by
    intro t ht
    have hrt := ((hr t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
    exact (polarX_hasDerivAt hrt).differentiableAt.differentiableWithinAt
  have hrat := ((hr φ hφ).differentiableAt (isOpen_Ioo.mem_nhds hφ)).hasDerivAt
  have hXderiv := (polarX_hasDerivAt hrat).deriv
  have hXne : deriv (polarX r) φ ≠ 0 := by
    rw [hXderiv]
    exact hx
  have hg := parametric_inverse_hasDerivAt hX hgf hφ hXne
  have hY : HasDerivAt (polarY r)
      (deriv r φ * Real.sin φ + r φ * Real.cos φ) (g (polarX r φ)) := by
    simpa only [hgf hφ] using polarY_hasDerivAt hrat
  have hcomp := hY.comp (polarX r φ) hg
  rw [hXderiv] at hcomp
  simpa only [div_eq_mul_inv, one_mul] using hcomp

end calculus.Chapter04.Section04PolarTangents
