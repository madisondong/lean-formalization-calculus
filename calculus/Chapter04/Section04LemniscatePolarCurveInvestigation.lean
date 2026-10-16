import calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Bài 4.4.16(d): lemniscate r²=2cos(2φ)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2796. Xét `cos(2φ) ≥ 0`, với cả hai bán kính `±√(2cos(2φ))`.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04LemniscatePolarCurveInvestigation
open Set Filter
open scoped Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter04.Section03
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarSymmetry
open calculus.Chapter04.Section04PolarTangents
open calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport

def lemniscateDomain : Set ℝ := {θ | 0 ≤ Real.cos (2 * θ)}
def lemniscateInterior : Set ℝ := {θ | 0 < Real.cos (2 * θ)}
def lemniscateRadius (σ θ : ℝ) : ℝ := σ * Real.sqrt (2 * Real.cos (2 * θ))
def lemniscateDR (σ θ : ℝ) : ℝ := -2 * Real.sin (2 * θ) / lemniscateRadius σ θ
def lemniscateDDR (σ θ : ℝ) : ℝ :=
  -4 * Real.cos (2 * θ) / lemniscateRadius σ θ -
    4 * Real.sin (2 * θ) ^ 2 / lemniscateRadius σ θ ^ 3
def lemniscateDX (σ θ : ℝ) : ℝ := lemniscateDR σ θ * Real.cos θ - lemniscateRadius σ θ * Real.sin θ
def lemniscateDY (σ θ : ℝ) : ℝ := lemniscateDR σ θ * Real.sin θ + lemniscateRadius σ θ * Real.cos θ
def lemniscateDDX (σ θ : ℝ) : ℝ :=
  (lemniscateDDR σ θ - lemniscateRadius σ θ) * Real.cos θ - 2 * lemniscateDR σ θ * Real.sin θ
def lemniscateDDY (σ θ : ℝ) : ℝ :=
  (lemniscateDDR σ θ - lemniscateRadius σ θ) * Real.sin θ + 2 * lemniscateDR σ θ * Real.cos θ

def lemniscateCurve : Set ℂ := polarLocus (fun r θ ↦ r ^ 2 = 2 * Real.cos (2 * θ))
def lemniscateRightLoop : Set ℂ := {z | z ∈ lemniscateCurve ∧ 0 ≤ z.re}
def lemniscateLeftLoop : Set ℂ := {z | z ∈ lemniscateCurve ∧ z.re ≤ 0}


theorem lemniscate_natural_domain (θ : ℝ) :
    (∃ r : ℝ, r ^ 2 = 2 * Real.cos (2 * θ)) ↔ θ ∈ lemniscateDomain := by
  constructor
  · rintro ⟨r, hr⟩
    change 0 ≤ Real.cos (2 * θ)
    nlinarith [sq_nonneg r]
  · intro hθ
    change 0 ≤ Real.cos (2 * θ) at hθ
    exact ⟨Real.sqrt (2 * Real.cos (2 * θ)), Real.sq_sqrt (by linarith [hθ])⟩

theorem lemniscate_radial_branches {r θ : ℝ} :
    r ^ 2 = 2 * Real.cos (2 * θ) ↔ θ ∈ lemniscateDomain ∧
      (r = lemniscateRadius 1 θ ∨ r = lemniscateRadius (-1) θ) := by
  constructor
  · intro hr
    have hθ := (lemniscate_natural_domain θ).mp ⟨r, hr⟩
    change 0 ≤ Real.cos (2 * θ) at hθ
    have hs : Real.sqrt (2 * Real.cos (2 * θ)) ^ 2 = 2 * Real.cos (2 * θ) :=
      Real.sq_sqrt (by linarith [hθ])
    refine ⟨hθ, ?_⟩
    simpa only [lemniscateRadius, one_mul, neg_one_mul] using sq_eq_sq_iff_eq_or_eq_neg.mp (hr.trans hs.symm)
  · rintro ⟨hθ, hr | hr⟩ <;> change 0 ≤ Real.cos (2 * θ) at hθ <;> rw [hr] <;>
      simp only [lemniscateRadius, one_mul, neg_one_mul, neg_sq] <;>
      exact Real.sq_sqrt (by linarith [hθ])


theorem lemniscate_complete_branch_image (z : ℂ) :
    z ∈ lemniscateCurve ↔ ∃ θ : ℝ, θ ∈ lemniscateDomain ∧
      (signedPolarPoint (lemniscateRadius 1 θ) θ = z ∨
        signedPolarPoint (lemniscateRadius (-1) θ) θ = z) := by
  constructor
  · rintro ⟨r, θ, hr, hz⟩
    obtain ⟨hθ, hr | hr⟩ := lemniscate_radial_branches.mp hr
    · exact ⟨θ, hθ, Or.inl (hr ▸ hz)⟩
    · exact ⟨θ, hθ, Or.inr (hr ▸ hz)⟩
  · rintro ⟨θ, hθ, hz | hz⟩
    · exact ⟨lemniscateRadius 1 θ, θ, lemniscate_radial_branches.mpr ⟨hθ, Or.inl rfl⟩, hz⟩
    · exact ⟨lemniscateRadius (-1) θ, θ, lemniscate_radial_branches.mpr ⟨hθ, Or.inr rfl⟩, hz⟩


theorem lemniscate_quartic_polar (r θ : ℝ) :
    ((signedPolarPoint r θ).re ^ 2 + (signedPolarPoint r θ).im ^ 2) ^ 2 -
      2 * ((signedPolarPoint r θ).re ^ 2 - (signedPolarPoint r θ).im ^ 2) =
      r ^ 2 * (r ^ 2 - 2 * Real.cos (2 * θ)) := by
  rw [signed_polar_square_sum, signedPolarPoint_re, signedPolarPoint_im, Real.cos_two_mul]
  nlinarith [congrArg (fun q : ℝ ↦ 2 * r ^ 2 * q) (Real.sin_sq_add_cos_sq θ)]


theorem lemniscate_mem_curve_iff (z : ℂ) :
    z ∈ lemniscateCurve ↔ (z.re ^ 2 + z.im ^ 2) ^ 2 = 2 * (z.re ^ 2 - z.im ^ 2) := by
  constructor
  · rintro ⟨r, θ, hr, rfl⟩
    have h := lemniscate_quartic_polar r θ
    rw [hr, sub_self, mul_zero] at h
    exact sub_eq_zero.mp h
  · intro h
    by_cases hz : z = 0
    · subst z
      refine ⟨0, Real.pi / 4, ?_, signedPolarPoint_zero_radius _⟩
      change (0 : ℝ) ^ 2 = 2 * Real.cos (2 * (Real.pi / 4))
      rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
      norm_num
    · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hq := lemniscate_quartic_polar ‖z‖ (nonnegativePolarAngle z)
      rw [signedPolarPoint_norm_nonnegativePolarAngle, h, sub_self] at hq
      have hr : ‖z‖ ^ 2 = 2 * Real.cos (2 * nonnegativePolarAngle z) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hq.symm).resolve_left (pow_ne_zero 2 hp.ne'))
      exact ⟨‖z‖, nonnegativePolarAngle z, hr, signedPolarPoint_norm_nonnegativePolarAngle z⟩


theorem lemniscate_distance (z : ℂ) (hz : z ∈ lemniscateCurve) :
    ‖z‖ ^ 2 ≤ 2 ∧ (‖z‖ ^ 2 = 2 ↔ z.im = 0 ∧ z ≠ 0) := by
  have h := (lemniscate_mem_curve_iff z).mp hz
  have hs : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
  have hp : z.re ^ 2 + z.im ^ 2 ≤ 2 := by
    by_contra hp
    have hpos : 0 < (z.re ^ 2 + z.im ^ 2) * (z.re ^ 2 + z.im ^ 2 - 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg z.im]
  refine ⟨by rwa [hs], ?_⟩
  rw [hs]
  constructor
  · intro he
    have hi : z.im ^ 2 = 0 := by nlinarith
    refine ⟨sq_eq_zero_iff.mp hi, ?_⟩
    intro hz
    rw [hz] at he
    norm_num at he
  · rintro ⟨hi, hnz⟩
    rw [hi] at h ⊢
    have hx : z.re ≠ 0 := by
      intro hx
      apply hnz
      exact Complex.ext (by simpa using hx) (by simpa using hi)
    have he : z.re ^ 2 * (z.re ^ 2 - 2) = 0 := by nlinarith
    have ht := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hx)
    nlinarith


theorem lemniscate_axes (x y : ℝ) :
    ((⟨x, 0⟩ : ℂ) ∈ lemniscateCurve ↔ x = 0 ∨ x = Real.sqrt 2 ∨ x = -Real.sqrt 2) ∧
      ((⟨0, y⟩ : ℂ) ∈ lemniscateCurve ↔ y = 0) := by
  rw [lemniscate_mem_curve_iff, lemniscate_mem_curve_iff]
  constructor
  · constructor
    · intro h
      change (x ^ 2 + 0 ^ 2) ^ 2 = 2 * (x ^ 2 - 0 ^ 2) at h
      have hp : x ^ 2 * (x ^ 2 - 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp with hx | hx
      · exact Or.inl (sq_eq_zero_iff.mp hx)
      · have hs : x ^ 2 = Real.sqrt 2 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; linarith
        exact Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp hs)
    · rintro (rfl | rfl | rfl) <;>
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · constructor
    · intro h
      change (0 ^ 2 + y ^ 2) ^ 2 = 2 * (0 ^ 2 - y ^ 2) at h
      have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg (y ^ 2), sq_nonneg y]
      exact sq_eq_zero_iff.mp hy
    · rintro rfl
      norm_num


theorem lemniscate_loops :
    lemniscateRightLoop ∪ lemniscateLeftLoop = lemniscateCurve ∧
      lemniscateRightLoop ∩ lemniscateLeftLoop = {0} := by
  constructor
  · ext z
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total (0 : ℝ) z.re with hp | hn
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, hn⟩
  · apply subset_antisymm
    · intro z hz
      have hx : z.re = 0 := le_antisymm hz.2.2 hz.1.2
      have h := (lemniscate_mem_curve_iff z).mp hz.1.1
      rw [hx] at h
      have hy : z.im = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (z.im ^ 2), sq_nonneg z.im])
      rw [mem_singleton_iff]
      exact Complex.ext hx hy
    · intro z hz
      rw [mem_singleton_iff] at hz
      subst z
      have h0 : (0 : ℂ) ∈ lemniscateCurve := (lemniscate_mem_curve_iff 0).mpr (by norm_num)
      exact ⟨⟨h0, le_rfl⟩, ⟨h0, le_rfl⟩⟩

theorem lemniscate_symmetries (z : ℂ) :
    (z ∈ lemniscateCurve ↔ polarAxisReflection z ∈ lemniscateCurve) ∧
      (z ∈ lemniscateCurve ↔ perpendicularAxisReflection z ∈ lemniscateCurve) ∧
      (z ∈ lemniscateCurve ↔ -z ∈ lemniscateCurve) := by
  simp only [lemniscate_mem_curve_iff, polarAxisReflection, perpendicularAxisReflection,
    Complex.neg_re, Complex.neg_im, neg_sq]
  exact ⟨trivial, trivial, trivial⟩


theorem lemniscate_radius_square {σ θ : ℝ} (hσ : σ ^ 2 = 1) (hθ : θ ∈ lemniscateDomain) :
    lemniscateRadius σ θ ^ 2 = 2 * Real.cos (2 * θ) := by
  change 0 ≤ Real.cos (2 * θ) at hθ
  rw [lemniscateRadius, mul_pow, hσ, one_mul, Real.sq_sqrt (by linarith [hθ])]

theorem lemniscate_radius_ne_zero {σ θ : ℝ} (hσ : σ ^ 2 = 1) (hθ : θ ∈ lemniscateInterior) :
    lemniscateRadius σ θ ≠ 0 := by
  change 0 < Real.cos (2 * θ) at hθ
  have hs : σ ≠ 0 := by intro hs; rw [hs] at hσ; norm_num at hσ
  exact mul_ne_zero hs (Real.sqrt_pos.mpr (by linarith [hθ])).ne'


theorem lemniscate_actual_first_derivatives {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hθ : θ ∈ lemniscateInterior) :
    HasDerivAt (lemniscateRadius σ) (lemniscateDR σ θ) θ ∧
      HasDerivAt (polarX (lemniscateRadius σ)) (lemniscateDX σ θ) θ ∧
      HasDerivAt (polarY (lemniscateRadius σ)) (lemniscateDY σ θ) θ := by
  change 0 < Real.cos (2 * θ) at hθ
  have hp : 0 < 2 * Real.cos (2 * θ) := by linarith [hθ]
  have hn := lemniscate_radius_ne_zero hσ hθ
  have hs : Real.sqrt (2 * Real.cos (2 * θ)) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hr : HasDerivAt (lemniscateRadius σ) (lemniscateDR σ θ) θ := by
    have h := ((((hasDerivAt_id θ).const_mul 2).cos).const_mul 2).sqrt hp.ne' |>.const_mul σ
    apply h.congr_deriv
    simp only [id_eq, mul_one, lemniscateDR, lemniscateRadius]
    have hsn : σ ≠ 0 := by intro hz; rw [hz] at hσ; norm_num at hσ
    field_simp [hs, hn, hsn]
    nlinarith [congrArg (fun q : ℝ ↦ q * Real.sin (2 * θ)) hσ]
  exact ⟨hr, polarX_hasDerivAt hr, polarY_hasDerivAt hr⟩


theorem lemniscate_interior_nhds {θ : ℝ} (hθ : θ ∈ lemniscateInterior) :
    lemniscateInterior ∈ 𝓝 θ := by
  change 0 < Real.cos (2 * θ) at hθ
  have hc : ContinuousAt (fun t : ℝ ↦ Real.cos (2 * t)) θ := by fun_prop
  exact hc.tendsto.eventually (eventually_gt_nhds hθ)

theorem lemniscate_DR_hasDerivAt {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hθ : θ ∈ lemniscateInterior) :
    HasDerivAt (lemniscateDR σ) (lemniscateDDR σ θ) θ := by
  change 0 < Real.cos (2 * θ) at hθ
  have hn := lemniscate_radius_ne_zero hσ hθ
  have hS : HasDerivAt (fun t : ℝ ↦ -2 * Real.sin (2 * t)) (-4 * Real.cos (2 * θ)) θ := by
    have h := (((hasDerivAt_id θ).const_mul 2).sin).const_mul (-2)
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring
  have h := hS.fun_div (lemniscate_actual_first_derivatives hσ hθ).1 hn
  apply h.congr_deriv
  dsimp only [lemniscateDR, lemniscateDDR]
  field_simp [hn]
  ring


theorem lemniscate_actual_second_derivatives {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hθ : θ ∈ lemniscateInterior) :
    HasDerivAt (deriv (polarX (lemniscateRadius σ))) (lemniscateDDX σ θ) θ ∧
      HasDerivAt (deriv (polarY (lemniscateRadius σ))) (lemniscateDDY σ θ) θ := by
  change 0 < Real.cos (2 * θ) at hθ
  have hr := (lemniscate_actual_first_derivatives hσ hθ).1
  have hdr := lemniscate_DR_hasDerivAt hσ hθ
  have hX : HasDerivAt (lemniscateDX σ) (lemniscateDDX σ θ) θ := by
    have h := (hdr.fun_mul (Real.hasDerivAt_cos θ)).fun_sub (hr.fun_mul (Real.hasDerivAt_sin θ))
    apply h.congr_deriv
    dsimp only [lemniscateDDX]
    ring
  have hY : HasDerivAt (lemniscateDY σ) (lemniscateDDY σ θ) θ := by
    have h := (hdr.fun_mul (Real.hasDerivAt_sin θ)).fun_add (hr.fun_mul (Real.hasDerivAt_cos θ))
    apply h.congr_deriv
    dsimp only [lemniscateDDY]
    ring
  constructor
  · apply hX.congr_of_eventuallyEq
    filter_upwards [lemniscate_interior_nhds hθ] with t ht
    exact (lemniscate_actual_first_derivatives hσ ht).2.1.deriv
  · apply hY.congr_of_eventuallyEq
    filter_upwards [lemniscate_interior_nhds hθ] with t ht
    exact (lemniscate_actual_first_derivatives hσ ht).2.2.deriv


theorem lemniscate_speed_sq_and_curvature_numerator {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hθ : θ ∈ lemniscateInterior) :
    lemniscateDX σ θ ^ 2 + lemniscateDY σ θ ^ 2 = 4 / lemniscateRadius σ θ ^ 2 ∧
      lemniscateDX σ θ * lemniscateDDY σ θ - lemniscateDY σ θ * lemniscateDDX σ θ =
        12 / lemniscateRadius σ θ ^ 2 ∧
      0 < 4 / lemniscateRadius σ θ ^ 2 ∧ 0 < 12 / lemniscateRadius σ θ ^ 2 := by
  change 0 < Real.cos (2 * θ) at hθ
  have hn := lemniscate_radius_ne_zero hσ hθ
  have hR := lemniscate_radius_square hσ (show θ ∈ lemniscateDomain by exact le_of_lt hθ)
  have hR4 : lemniscateRadius σ θ ^ 4 = 4 * Real.cos (2 * θ) ^ 2 := by
    calc
      _ = (lemniscateRadius σ θ ^ 2) ^ 2 := by ring
      _ = 4 * Real.cos (2 * θ) ^ 2 := by rw [hR]; ring
  have hV : lemniscateDX σ θ ^ 2 + lemniscateDY σ θ ^ 2 =
      lemniscateDR σ θ ^ 2 + lemniscateRadius σ θ ^ 2 := by
    dsimp only [lemniscateDX, lemniscateDY]
    nlinarith [congrArg (fun q : ℝ ↦ lemniscateDR σ θ ^ 2 * q) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun q : ℝ ↦ lemniscateRadius σ θ ^ 2 * q) (Real.sin_sq_add_cos_sq θ)]
  have hK : lemniscateDX σ θ * lemniscateDDY σ θ - lemniscateDY σ θ * lemniscateDDX σ θ =
      lemniscateRadius σ θ ^ 2 + 2 * lemniscateDR σ θ ^ 2 - lemniscateRadius σ θ * lemniscateDDR σ θ := by
    dsimp only [lemniscateDX, lemniscateDY, lemniscateDDX, lemniscateDDY]
    nlinarith [congrArg (fun q : ℝ ↦ lemniscateRadius σ θ ^ 2 * q) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun q : ℝ ↦ 2 * lemniscateDR σ θ ^ 2 * q) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun q : ℝ ↦ lemniscateRadius σ θ * lemniscateDDR σ θ * q) (Real.sin_sq_add_cos_sq θ)]
  refine ⟨?_, ?_, div_pos (by norm_num) (sq_pos_of_ne_zero hn),
    div_pos (by norm_num) (sq_pos_of_ne_zero hn)⟩
  · rw [hV]
    dsimp only [lemniscateDR]
    field_simp [hn]
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ)]
  · rw [hK]
    dsimp only [lemniscateDR, lemniscateDDR]
    field_simp [hn]
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ),
      congrArg (fun q : ℝ ↦ 2 * lemniscateRadius σ θ ^ 2 * q) hR]


theorem lemniscate_pole_directions {θ : ℝ} (hc : Real.cos (2 * θ) = 0) :
    Real.cos θ ≠ 0 ∧ Real.sin θ ≠ 0 ∧ (Real.sin θ / Real.cos θ) ^ 2 = 1 := by
  have h2 := Real.cos_two_mul θ
  have ht := Real.sin_sq_add_cos_sq θ
  have hcos : Real.cos θ ^ 2 = 1 / 2 := by rw [hc] at h2; nlinarith
  have hsin : Real.sin θ ^ 2 = 1 / 2 := by nlinarith
  have hn : Real.cos θ ≠ 0 := by intro h; rw [h] at hcos; norm_num at hcos
  refine ⟨hn, ?_, ?_⟩
  · intro h
    rw [h] at hsin
    norm_num at hsin
  · rw [div_pow, hcos, hsin]
    norm_num


theorem lemniscate_pole_interior_accumulation {θ : ℝ} (hc : Real.cos (2 * θ) = 0) :
    AccumulationPointOf lemniscateInterior θ := by
  have hs : Real.sin (2 * θ) = 1 ∨ Real.sin (2 * θ) = -1 := by
    have ht := Real.sin_sq_add_cos_sq (2 * θ)
    rw [hc] at ht
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (by nlinarith : Real.sin (2 * θ) ^ 2 = (1 : ℝ) ^ 2)
  intro δ hδ
  let u : ℝ := min (δ / 2) (Real.pi / 4)
  have hu : 0 < u := lt_min (by linarith) (by positivity)
  have hud : u < δ := (min_le_left _ _).trans_lt (by linarith)
  have hup : 2 * u < Real.pi := by
    have h := min_le_right (δ / 2) (Real.pi / 4)
    change u ≤ Real.pi / 4 at h
    linarith [Real.pi_pos]
  have hsu := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < 2 * u) hup
  rcases hs with hs | hs
  · refine ⟨θ - u, ?_, by linarith, by linarith, by linarith⟩
    change 0 < Real.cos (2 * (θ - u))
    rw [show 2 * (θ - u) = 2 * θ - 2 * u by ring, Real.cos_sub, hc, hs]
    simpa only [zero_mul, one_mul, zero_add] using hsu
  · refine ⟨θ + u, ?_, by linarith, by linarith, by linarith⟩
    change 0 < Real.cos (2 * (θ + u))
    rw [show 2 * (θ + u) = 2 * θ + 2 * u by ring, Real.cos_add, hc, hs]
    simpa only [zero_mul, neg_one_mul, zero_sub, neg_neg] using hsu


theorem lemniscate_pole_tangent {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hc : Real.cos (2 * θ) = 0) :
    DomainLimit (xSecantDomain lemniscateDomain (lemniscateRadius σ) θ)
      (fun t ↦ (polarY (lemniscateRadius σ) t - polarY (lemniscateRadius σ) θ) /
        (polarX (lemniscateRadius σ) t - polarX (lemniscateRadius σ) θ)) θ
      (Real.sin θ / Real.cos θ) := by
  have hcn := (lemniscate_pole_directions hc).1
  have hr0 : lemniscateRadius σ θ = 0 := by rw [lemniscateRadius, hc]; simp only [mul_zero, Real.sqrt_zero]
  have hx0 : polarX (lemniscateRadius σ) θ = 0 := by rw [polarX, hr0, zero_mul]
  have hy0 : polarY (lemniscateRadius σ) θ = 0 := by rw [polarY, hr0, zero_mul]
  have hcos : {t : ℝ | Real.cos t ≠ 0} ∈ 𝓝 θ := Real.continuous_cos.continuousAt.tendsto.eventually_ne hcn
  have ha : AccumulationPointOf (xSecantDomain lemniscateDomain (lemniscateRadius σ) θ) θ := by
    apply accumulationPointOf_mono (accumulationPointOf_inter_nhds (lemniscate_pole_interior_accumulation hc) hcos)
    intro t ht
    refine ⟨(show 0 < Real.cos (2 * t) from ht.1).le, ?_⟩
    rw [hx0, sub_zero]
    exact mul_ne_zero (lemniscate_radius_ne_zero hσ ht.1) ht.2
  apply (domainLimit_iff_tendsto ha).mpr
  have hl : Tendsto (fun t : ℝ ↦ Real.sin t / Real.cos t) (𝓝 θ)
      (𝓝 (Real.sin θ / Real.cos θ)) := by
    simpa only using! Real.continuous_sin.continuousAt.tendsto.div
      Real.continuous_cos.continuousAt.tendsto hcn
  apply (hl.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hx : lemniscateRadius σ t * Real.cos t ≠ 0 := by
    simpa only [polarX, hr0, zero_mul, sub_zero] using ht.1.2
  rw [hx0, hy0]
  dsimp only [polarX, polarY]
  simp only [sub_zero]
  field_simp [(mul_ne_zero_iff.mp hx).1, (mul_ne_zero_iff.mp hx).2]


theorem lemniscate_pole_not_horizontal {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hc : Real.cos (2 * θ) = 0) :
    ¬ HasHorizontalPolarTangent lemniscateDomain (lemniscateRadius σ) θ := by
  intro h
  have hs := domainLimit_unique (lemniscate_pole_tangent hσ hc) h
  have hp := (lemniscate_pole_directions hc).2.2
  rw [hs] at hp
  norm_num at hp


theorem lemniscate_pole_inverse_tangent {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hc : Real.cos (2 * θ) = 0) :
    DomainLimit (ySecantDomain lemniscateDomain (lemniscateRadius σ) θ)
      (fun t ↦ (polarX (lemniscateRadius σ) t - polarX (lemniscateRadius σ) θ) /
        (polarY (lemniscateRadius σ) t - polarY (lemniscateRadius σ) θ)) θ
      (Real.cos θ / Real.sin θ) := by
  have hsn := (lemniscate_pole_directions hc).2.1
  have hr0 : lemniscateRadius σ θ = 0 := by rw [lemniscateRadius, hc]; simp only [mul_zero, Real.sqrt_zero]
  have hx0 : polarX (lemniscateRadius σ) θ = 0 := by rw [polarX, hr0, zero_mul]
  have hy0 : polarY (lemniscateRadius σ) θ = 0 := by rw [polarY, hr0, zero_mul]
  have hsin : {t : ℝ | Real.sin t ≠ 0} ∈ 𝓝 θ := Real.continuous_sin.continuousAt.tendsto.eventually_ne hsn
  have ha : AccumulationPointOf (ySecantDomain lemniscateDomain (lemniscateRadius σ) θ) θ := by
    apply accumulationPointOf_mono (accumulationPointOf_inter_nhds (lemniscate_pole_interior_accumulation hc) hsin)
    intro t ht
    refine ⟨(show 0 < Real.cos (2 * t) from ht.1).le, ?_⟩
    rw [hy0, sub_zero]
    exact mul_ne_zero (lemniscate_radius_ne_zero hσ ht.1) ht.2
  apply (domainLimit_iff_tendsto ha).mpr
  have hl : Tendsto (fun t : ℝ ↦ Real.cos t / Real.sin t) (𝓝 θ)
      (𝓝 (Real.cos θ / Real.sin θ)) := by
    simpa only using! Real.continuous_cos.continuousAt.tendsto.div
      Real.continuous_sin.continuousAt.tendsto hsn
  apply (hl.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hy : lemniscateRadius σ t * Real.sin t ≠ 0 := by
    simpa only [polarY, hr0, zero_mul, sub_zero] using ht.1.2
  rw [hx0, hy0]
  dsimp only [polarX, polarY]
  simp only [sub_zero]
  field_simp [(mul_ne_zero_iff.mp hy).1, (mul_ne_zero_iff.mp hy).2]

theorem lemniscate_pole_not_vertical {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hc : Real.cos (2 * θ) = 0) :
    ¬ HasVerticalPolarTangent lemniscateDomain (lemniscateRadius σ) θ := by
  intro h
  have hs := domainLimit_unique (lemniscate_pole_inverse_tangent hσ hc) h
  have hcos := (lemniscate_pole_directions hc).1
  have hsin := (lemniscate_pole_directions hc).2.1
  exact hcos ((div_eq_zero_iff.mp hs).resolve_right hsin)


theorem lemniscate_coordinate_phase {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hθ : θ ∈ lemniscateInterior) :
    lemniscateDX σ θ = -2 * Real.sin (3 * θ) / lemniscateRadius σ θ ∧
      lemniscateDY σ θ = 2 * Real.cos (3 * θ) / lemniscateRadius σ θ := by
  change 0 < Real.cos (2 * θ) at hθ
  have hn := lemniscate_radius_ne_zero hσ hθ
  have hr := lemniscate_radius_square hσ (show θ ∈ lemniscateDomain from le_of_lt hθ)
  have he : 3 * θ = 2 * θ + θ := by ring
  constructor
  · dsimp only [lemniscateDX, lemniscateDR]
    rw [he, Real.sin_add]
    field_simp [hn]
    nlinarith [congrArg (fun q : ℝ ↦ q * Real.sin θ) hr]
  · dsimp only [lemniscateDY, lemniscateDR]
    rw [he, Real.cos_add]
    field_simp [hn]
    nlinarith [congrArg (fun q : ℝ ↦ q * Real.cos θ) hr]


theorem lemniscate_tangents_iff {σ θ : ℝ} (hσ : σ ^ 2 = 1) (hθ : θ ∈ lemniscateDomain) :
    (HasHorizontalPolarTangent lemniscateDomain (lemniscateRadius σ) θ ↔
      θ ∈ lemniscateInterior ∧ Real.cos (3 * θ) = 0) ∧
    (HasVerticalPolarTangent lemniscateDomain (lemniscateRadius σ) θ ↔
      θ ∈ lemniscateInterior ∧ Real.sin (3 * θ) = 0) := by
  change 0 ≤ Real.cos (2 * θ) at hθ
  by_cases h0 : Real.cos (2 * θ) = 0
  · have hnH := lemniscate_pole_not_horizontal hσ h0
    have hnV := lemniscate_pole_not_vertical hσ h0
    have hnI : θ ∉ lemniscateInterior := by change ¬ 0 < Real.cos (2 * θ); rw [h0]; exact lt_irrefl 0
    simp only [hnH, hnV, hnI, false_and]
    exact ⟨trivial, trivial⟩
  · have hi : θ ∈ lemniscateInterior := lt_of_le_of_ne hθ (Ne.symm h0)
    have hD : lemniscateDomain ∈ 𝓝 θ := mem_of_superset (lemniscate_interior_nhds hi) (fun t h ↦ (show 0 < Real.cos (2 * t) from h).le)
    have hn := lemniscate_radius_ne_zero hσ hi
    have hP := lemniscate_coordinate_phase hσ hi
    have hA := lemniscate_actual_first_derivatives hσ hi
    have hV := (lemniscate_speed_sq_and_curvature_numerator hσ hi).1
    have hpos := (lemniscate_speed_sq_and_curvature_numerator hσ hi).2.2.1
    constructor
    · constructor
      · intro h
        have hy := secant_zero_implies_deriv_zero hA.2.2 hA.2.1 h
        rw [hP.2] at hy
        have hz : Real.cos (3 * θ) = 0 := by
          have hh := (div_eq_zero_iff.mp hy).resolve_right hn
          linarith
        exact ⟨hi, hz⟩
      · rintro ⟨_, hc⟩
        have hy : lemniscateDY σ θ = 0 := by rw [hP.2, hc, mul_zero, zero_div]
        apply source_horizontal_polar_tangent hD hA.1 hy
        change lemniscateDX σ θ ≠ 0
        intro hx
        rw [hx, hy] at hV
        nlinarith
    · constructor
      · intro h
        have hx := secant_zero_implies_deriv_zero hA.2.1 hA.2.2 h
        rw [hP.1] at hx
        have hz : Real.sin (3 * θ) = 0 := by
          have hh := (div_eq_zero_iff.mp hx).resolve_right hn
          linarith
        exact ⟨hi, hz⟩
      · rintro ⟨_, hs⟩
        have hx : lemniscateDX σ θ = 0 := by rw [hP.1, hs, mul_zero, zero_div]
        apply source_vertical_polar_tangent hD hA.1 hx
        change lemniscateDY σ θ ≠ 0
        intro hy
        rw [hx, hy] at hV
        nlinarith


theorem lemniscate_coordinate_extrema {σ θ : ℝ} (hσ : σ ^ 2 = 1) (hθ : θ ∈ lemniscateInterior) :
    ((IsLocalMinimumOn (polarX (lemniscateRadius σ)) univ θ ↔
      lemniscateDX σ θ = 0 ∧ 0 < lemniscateDDX σ θ) ∧
    (IsLocalMaximumOn (polarX (lemniscateRadius σ)) univ θ ↔
      lemniscateDX σ θ = 0 ∧ lemniscateDDX σ θ < 0)) ∧
    ((IsLocalMinimumOn (polarY (lemniscateRadius σ)) univ θ ↔
      lemniscateDY σ θ = 0 ∧ 0 < lemniscateDDY σ θ) ∧
    (IsLocalMaximumOn (polarY (lemniscateRadius σ)) univ θ ↔
      lemniscateDY σ θ = 0 ∧ lemniscateDDY σ θ < 0)) := by
  change 0 < Real.cos (2 * θ) at hθ
  have hk : 0 < lemniscateDX σ θ * lemniscateDDY σ θ - lemniscateDY σ θ * lemniscateDDX σ θ := by
    rw [(lemniscate_speed_sq_and_curvature_numerator hσ hθ).2.1]
    exact (lemniscate_speed_sq_and_curvature_numerator hσ hθ).2.2.2
  have hA := lemniscate_actual_first_derivatives hσ hθ
  have hB := lemniscate_actual_second_derivatives hσ hθ
  have hx : deriv (polarX (lemniscateRadius σ)) θ = 0 →
      deriv (deriv (polarX (lemniscateRadius σ))) θ ≠ 0 := by
    rw [hA.2.1.deriv, hB.1.deriv]
    intro h1 h2
    rw [h1, h2] at hk
    norm_num at hk
  have hy : deriv (polarY (lemniscateRadius σ)) θ = 0 →
      deriv (deriv (polarY (lemniscateRadius σ))) θ ≠ 0 := by
    rw [hA.2.2.deriv, hB.2.deriv]
    intro h1 h2
    rw [h1, h2] at hk
    norm_num at hk
  have hX := nondegenerate_extrema_iff hA.2.1.differentiableAt hx
  have hY := nondegenerate_extrema_iff hA.2.2.differentiableAt hy
  rw [hA.2.1.deriv, hB.1.deriv] at hX
  rw [hA.2.2.deriv, hB.2.deriv] at hY
  exact ⟨hX, hY⟩


theorem lemniscate_signed_radius_bounds {θ : ℝ} (hθ : θ ∈ lemniscateDomain) :
    0 ≤ lemniscateRadius 1 θ ∧ lemniscateRadius 1 θ ≤ Real.sqrt 2 ∧
      -Real.sqrt 2 ≤ lemniscateRadius (-1) θ ∧ lemniscateRadius (-1) θ ≤ 0 ∧
      (lemniscateRadius 1 θ = 0 ↔ Real.cos (2 * θ) = 0) ∧
      (lemniscateRadius 1 θ = Real.sqrt 2 ↔ Real.cos (2 * θ) = 1) := by
  change 0 ≤ Real.cos (2 * θ) at hθ
  have hp : 0 ≤ 2 * Real.cos (2 * θ) := by linarith [hθ]
  have hb : Real.sqrt (2 * Real.cos (2 * θ)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by linarith [Real.cos_le_one (2 * θ)])
  have hnon := Real.sqrt_nonneg (2 * Real.cos (2 * θ))
  simp only [lemniscateRadius, one_mul, neg_one_mul]
  refine ⟨hnon, hb, neg_le_neg hb, neg_nonpos.mpr hnon, ?_, ?_⟩
  · constructor
    · intro h
      have hs := Real.sq_sqrt hp
      rw [h] at hs
      nlinarith
    · intro h
      rw [h, mul_zero, Real.sqrt_zero]
  · constructor
    · intro h
      have hs := Real.sq_sqrt hp
      rw [h, Real.sq_sqrt (by norm_num)] at hs
      linarith
    · intro h
      rw [h, mul_one]


theorem lemniscate_interior_extrema_domain {f : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ lemniscateInterior) :
    (IsLocalMinimumOn f lemniscateDomain θ ↔ IsLocalMinimumOn f univ θ) ∧
      (IsLocalMaximumOn f lemniscateDomain θ ↔ IsLocalMaximumOn f univ θ) := by
  change 0 < Real.cos (2 * θ) at hθ
  have hD : lemniscateDomain ∈ 𝓝 θ :=
    mem_of_superset (lemniscate_interior_nhds hθ) (fun t h ↦ (show 0 < Real.cos (2 * t) from h).le)
  simp only [isLocalMinimumOn_iff, isLocalMaximumOn_iff, IsLocalMinOn,
    IsLocalMaxOn, nhdsWithin_eq_nhds.mpr hD, nhdsWithin_univ, mem_univ,
    show θ ∈ lemniscateDomain from le_of_lt hθ, true_and, and_self]


theorem lemniscate_pole_product_extrema {σ θ : ℝ} {g : ℝ → ℝ}
    (hσ : σ ^ 2 = 1) (hc : Real.cos (2 * θ) = 0)
    (hg : ContinuousAt g θ) (hgn : g θ ≠ 0) :
    (IsLocalMinimumOn (fun t ↦ lemniscateRadius σ t * g t) lemniscateDomain θ ↔
      0 < σ * g θ) ∧
    (IsLocalMaximumOn (fun t ↦ lemniscateRadius σ t * g t) lemniscateDomain θ ↔
      σ * g θ < 0) := by
  have hsn : σ ≠ 0 := by intro h; rw [h] at hσ; norm_num at hσ
  have hfn : σ * g θ ≠ 0 := mul_ne_zero hsn hgn
  have hD : θ ∈ lemniscateDomain := by change 0 ≤ Real.cos (2 * θ); rw [hc]
  have hzero : lemniscateRadius σ θ * g θ = 0 := by
    rw [lemniscateRadius, hc]
    simp only [mul_zero, Real.sqrt_zero, zero_mul]
  have hrewrite (t : ℝ) : lemniscateRadius σ t * g t =
      Real.sqrt (2 * Real.cos (2 * t)) * (σ * g t) := by
    dsimp only [lemniscateRadius]
    ring
  have hcont : ContinuousAt (fun t ↦ σ * g t) θ := continuousAt_const.mul hg
  rcases lt_or_gt_of_ne hfn with hneg | hpos
  · have he : ∀ᶠ t : ℝ in 𝓝 θ, σ * g t < 0 := hcont.tendsto.eventually (eventually_lt_nhds hneg)
    obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
    have hmax : IsLocalMaximumOn (fun t ↦ lemniscateRadius σ t * g t) lemniscateDomain θ := by
      refine ⟨hD, ε, hε, ?_⟩
      rintro t ⟨ht, _⟩
      change lemniscateRadius σ t * g t ≤ lemniscateRadius σ θ * g θ
      rw [hzero, hrewrite]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _)
      exact (he (by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).le
    have hnmin : ¬ IsLocalMinimumOn (fun t ↦ lemniscateRadius σ t * g t) lemniscateDomain θ := by
      rintro ⟨_, δ, hδ, hmin⟩
      obtain ⟨t, ht, _, htl, htr⟩ := lemniscate_pole_interior_accumulation hc
        (min δ ε) (lt_min hδ hε)
      change 0 < Real.cos (2 * t) at ht
      have hsmall : dist t θ < ε := by
        rw [Real.dist_eq]
        apply abs_lt.mpr
        have hm := min_le_right δ ε
        constructor <;> linarith
      have hlt : lemniscateRadius σ t * g t < 0 := by
        rw [hrewrite]
        exact mul_neg_of_pos_of_neg (Real.sqrt_pos.mpr (by linarith [ht])) (he hsmall)
      have hbound := hmin t ⟨⟨by linarith [min_le_left δ ε], by linarith [min_le_left δ ε]⟩, le_of_lt ht⟩
      change lemniscateRadius σ θ * g θ ≤ lemniscateRadius σ t * g t at hbound
      rw [hzero] at hbound
      exact not_le_of_gt hlt hbound
    simp only [hnmin, hmax, hneg, not_lt_of_gt hneg, iff_self, and_self]
  · have he : ∀ᶠ t : ℝ in 𝓝 θ, 0 < σ * g t := hcont.tendsto.eventually (eventually_gt_nhds hpos)
    obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
    have hmin : IsLocalMinimumOn (fun t ↦ lemniscateRadius σ t * g t) lemniscateDomain θ := by
      refine ⟨hD, ε, hε, ?_⟩
      rintro t ⟨ht, _⟩
      change lemniscateRadius σ θ * g θ ≤ lemniscateRadius σ t * g t
      rw [hzero, hrewrite]
      apply mul_nonneg (Real.sqrt_nonneg _)
      exact (he (by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).le
    have hnmax : ¬ IsLocalMaximumOn (fun t ↦ lemniscateRadius σ t * g t) lemniscateDomain θ := by
      rintro ⟨_, δ, hδ, hmax⟩
      obtain ⟨t, ht, _, htl, htr⟩ := lemniscate_pole_interior_accumulation hc
        (min δ ε) (lt_min hδ hε)
      change 0 < Real.cos (2 * t) at ht
      have hsmall : dist t θ < ε := by
        rw [Real.dist_eq]
        apply abs_lt.mpr
        have hm := min_le_right δ ε
        constructor <;> linarith
      have hlt : 0 < lemniscateRadius σ t * g t := by
        rw [hrewrite]
        exact mul_pos (Real.sqrt_pos.mpr (by linarith [ht])) (he hsmall)
      have hbound := hmax t ⟨⟨by linarith [min_le_left δ ε], by linarith [min_le_left δ ε]⟩, le_of_lt ht⟩
      change lemniscateRadius σ t * g t ≤ lemniscateRadius σ θ * g θ at hbound
      rw [hzero] at hbound
      exact not_le_of_gt hlt hbound
    simp only [hmin, hnmax, hpos, not_lt_of_gt hpos, iff_self, and_self]


theorem lemniscate_pole_coordinate_extrema {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hc : Real.cos (2 * θ) = 0) :
    ((IsLocalMinimumOn (polarX (lemniscateRadius σ)) lemniscateDomain θ ↔
      0 < σ * Real.cos θ) ∧
    (IsLocalMaximumOn (polarX (lemniscateRadius σ)) lemniscateDomain θ ↔
      σ * Real.cos θ < 0)) ∧
    ((IsLocalMinimumOn (polarY (lemniscateRadius σ)) lemniscateDomain θ ↔
      0 < σ * Real.sin θ) ∧
    (IsLocalMaximumOn (polarY (lemniscateRadius σ)) lemniscateDomain θ ↔
      σ * Real.sin θ < 0)) := by
  refine ⟨?_, ?_⟩
  · exact lemniscate_pole_product_extrema hσ hc Real.continuous_cos.continuousAt
      (lemniscate_pole_directions hc).1
  · exact lemniscate_pole_product_extrema hσ hc Real.continuous_sin.continuousAt
      (lemniscate_pole_directions hc).2.1


theorem lemniscate_natural_domain_coordinate_extrema {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hθ : θ ∈ lemniscateDomain) :
    ((IsLocalMinimumOn (polarX (lemniscateRadius σ)) lemniscateDomain θ ↔
      (θ ∈ lemniscateInterior ∧ lemniscateDX σ θ = 0 ∧ 0 < lemniscateDDX σ θ) ∨
      (Real.cos (2 * θ) = 0 ∧ 0 < σ * Real.cos θ)) ∧
    (IsLocalMaximumOn (polarX (lemniscateRadius σ)) lemniscateDomain θ ↔
      (θ ∈ lemniscateInterior ∧ lemniscateDX σ θ = 0 ∧ lemniscateDDX σ θ < 0) ∨
      (Real.cos (2 * θ) = 0 ∧ σ * Real.cos θ < 0))) ∧
    ((IsLocalMinimumOn (polarY (lemniscateRadius σ)) lemniscateDomain θ ↔
      (θ ∈ lemniscateInterior ∧ lemniscateDY σ θ = 0 ∧ 0 < lemniscateDDY σ θ) ∨
      (Real.cos (2 * θ) = 0 ∧ 0 < σ * Real.sin θ)) ∧
    (IsLocalMaximumOn (polarY (lemniscateRadius σ)) lemniscateDomain θ ↔
      (θ ∈ lemniscateInterior ∧ lemniscateDY σ θ = 0 ∧ lemniscateDDY σ θ < 0) ∨
      (Real.cos (2 * θ) = 0 ∧ σ * Real.sin θ < 0))) := by
  change 0 ≤ Real.cos (2 * θ) at hθ
  by_cases hc : Real.cos (2 * θ) = 0
  · have hi : θ ∉ lemniscateInterior := by change ¬ 0 < Real.cos (2 * θ); rw [hc]; exact lt_irrefl 0
    simpa only [hi, hc, true_and, false_and, false_or] using lemniscate_pole_coordinate_extrema hσ hc
  · have hi : θ ∈ lemniscateInterior := lt_of_le_of_ne hθ (Ne.symm hc)
    have hX := (lemniscate_interior_extrema_domain (f := polarX (lemniscateRadius σ)) hi)
    have hY := (lemniscate_interior_extrema_domain (f := polarY (lemniscateRadius σ)) hi)
    have he := lemniscate_coordinate_extrema hσ hi
    rw [hX.1, hX.2, hY.1, hY.2]
    simpa only [hi, hc, true_and, false_and, or_false] using he


theorem lemniscate_radius_second_derivative {σ θ : ℝ} (hσ : σ ^ 2 = 1)
    (hθ : θ ∈ lemniscateInterior) :
    HasDerivAt (deriv (lemniscateRadius σ)) (lemniscateDDR σ θ) θ := by
  change 0 < Real.cos (2 * θ) at hθ
  apply (lemniscate_DR_hasDerivAt hσ hθ).congr_of_eventuallyEq
  filter_upwards [lemniscate_interior_nhds hθ] with t ht
  exact (lemniscate_actual_first_derivatives hσ ht).1.deriv


theorem lemniscate_positive_radius_stationary {θ : ℝ} (hθ : θ ∈ lemniscateInterior)
    (hd : lemniscateDR 1 θ = 0) :
    Real.cos (2 * θ) = 1 ∧ lemniscateDDR 1 θ < 0 := by
  change 0 < Real.cos (2 * θ) at hθ
  have hn := lemniscate_radius_ne_zero (by norm_num : (1 : ℝ)^2=1) hθ
  have hs : Real.sin (2 * θ) = 0 := by
    change -2 * Real.sin (2 * θ) / lemniscateRadius 1 θ = 0 at hd
    have h := (div_eq_zero_iff.mp hd).resolve_right hn
    linarith
  have hc : Real.cos (2 * θ) = 1 := by
    have ht := Real.sin_sq_add_cos_sq (2 * θ)
    rw [hs] at ht
    nlinarith [hθ, Real.cos_le_one (2 * θ)]
  refine ⟨hc, ?_⟩
  dsimp only [lemniscateDDR]
  rw [hs, hc]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div, sub_zero, mul_one]
  apply div_neg_of_neg_of_pos (by norm_num)
  dsimp only [lemniscateRadius]
  rw [one_mul]
  exact Real.sqrt_pos.mpr (by linarith [hθ])


theorem lemniscate_positive_radius_interior_extrema {θ : ℝ} (hθ : θ ∈ lemniscateInterior) :
    ¬ IsLocalMinimumOn (lemniscateRadius 1) univ θ ∧
      (IsLocalMaximumOn (lemniscateRadius 1) univ θ ↔ Real.cos (2 * θ) = 1) := by
  change 0 < Real.cos (2 * θ) at hθ
  have hA := (lemniscate_actual_first_derivatives (by norm_num : (1 : ℝ)^2=1) hθ).1
  have hB := lemniscate_radius_second_derivative (by norm_num : (1 : ℝ)^2=1) hθ
  have hne : deriv (lemniscateRadius 1) θ = 0 → deriv (deriv (lemniscateRadius 1)) θ ≠ 0 := by
    rw [hA.deriv, hB.deriv]
    intro hd
    exact (lemniscate_positive_radius_stationary hθ hd).2.ne
  have he := nondegenerate_extrema_iff hA.differentiableAt hne
  rw [hA.deriv, hB.deriv] at he
  constructor
  · intro hm
    obtain ⟨hd, hp⟩ := he.1.mp hm
    exact not_lt_of_gt (lemniscate_positive_radius_stationary hθ hd).2 hp
  · rw [he.2]
    constructor
    · rintro ⟨hd, _⟩
      exact (lemniscate_positive_radius_stationary hθ hd).1
    · intro hc
      have hs : Real.sin (2 * θ) = 0 := by
        have ht := Real.sin_sq_add_cos_sq (2 * θ)
        rw [hc] at ht
        exact sq_eq_zero_iff.mp (by nlinarith)
      have hd : lemniscateDR 1 θ = 0 := by
        dsimp only [lemniscateDR]
        rw [hs, mul_zero, zero_div]
      exact ⟨hd, (lemniscate_positive_radius_stationary hθ hd).2⟩


theorem lemniscate_natural_domain_radius_extrema {θ : ℝ} (hθ : θ ∈ lemniscateDomain) :
    (IsLocalMinimumOn (lemniscateRadius 1) lemniscateDomain θ ↔ Real.cos (2 * θ) = 0) ∧
      (IsLocalMaximumOn (lemniscateRadius 1) lemniscateDomain θ ↔ Real.cos (2 * θ) = 1) ∧
      (IsLocalMinimumOn (lemniscateRadius (-1)) lemniscateDomain θ ↔ Real.cos (2 * θ) = 1) ∧
      (IsLocalMaximumOn (lemniscateRadius (-1)) lemniscateDomain θ ↔ Real.cos (2 * θ) = 0) := by
  change 0 ≤ Real.cos (2 * θ) at hθ
  have hneg : lemniscateRadius (-1) = fun t ↦ -lemniscateRadius 1 t := by
    funext t
    simp only [lemniscateRadius, one_mul, neg_one_mul]
  have hnegMin : IsLocalMinimumOn (lemniscateRadius (-1)) lemniscateDomain θ ↔
      IsLocalMaximumOn (lemniscateRadius 1) lemniscateDomain θ := by
    rw [hneg]
    simp only [IsLocalMinimumOn, IsLocalMaximumOn, neg_le_neg_iff]
  have hnegMax : IsLocalMaximumOn (lemniscateRadius (-1)) lemniscateDomain θ ↔
      IsLocalMinimumOn (lemniscateRadius 1) lemniscateDomain θ := by
    rw [hneg]
    simp only [IsLocalMinimumOn, IsLocalMaximumOn, neg_le_neg_iff]
  have hpos :
      (IsLocalMinimumOn (lemniscateRadius 1) lemniscateDomain θ ↔ Real.cos (2 * θ) = 0) ∧
      (IsLocalMaximumOn (lemniscateRadius 1) lemniscateDomain θ ↔ Real.cos (2 * θ) = 1) := by
    by_cases hc : Real.cos (2 * θ) = 0
    · have h := lemniscate_pole_product_extrema (σ := 1) (g := fun _ ↦ (1 : ℝ))
        (by norm_num) hc continuousAt_const (by norm_num)
      simp only [mul_one, zero_lt_one, not_lt_of_gt zero_lt_one, iff_true, iff_false] at h
      simpa only [hc, mul_one, zero_ne_one, iff_true, iff_false] using h
    · have hi : θ ∈ lemniscateInterior := lt_of_le_of_ne hθ (Ne.symm hc)
      have hb := lemniscate_interior_extrema_domain (f := lemniscateRadius 1) hi
      have he := lemniscate_positive_radius_interior_extrema hi
      rw [hb.1, hb.2]
      exact ⟨by simpa only [hc, iff_false] using he.1, he.2⟩
  exact ⟨hpos.1, hpos.2, hnegMin.trans hpos.2, hnegMax.trans hpos.1⟩


theorem source_lemniscate_complete_polar_curve_investigation :
    (∀ θ : ℝ, (∃ r : ℝ, r ^ 2 = 2 * Real.cos (2 * θ)) ↔ θ ∈ lemniscateDomain) ∧
    (∀ z : ℂ, z ∈ lemniscateCurve ↔ (z.re ^ 2 + z.im ^ 2) ^ 2 = 2 * (z.re ^ 2 - z.im ^ 2)) ∧
    (∀ z : ℂ, z ∈ lemniscateCurve ↔ ∃ θ : ℝ, θ ∈ lemniscateDomain ∧
      (signedPolarPoint (lemniscateRadius 1 θ) θ = z ∨ signedPolarPoint (lemniscateRadius (-1) θ) θ = z)) ∧
    (lemniscateRightLoop ∪ lemniscateLeftLoop = lemniscateCurve ∧
      lemniscateRightLoop ∩ lemniscateLeftLoop = {0}) ∧
    (∀ σ θ : ℝ, σ ^ 2 = 1 → Real.cos (2 * θ) = 0 →
      DomainLimit (xSecantDomain lemniscateDomain (lemniscateRadius σ) θ)
        (fun t ↦ (polarY (lemniscateRadius σ) t - polarY (lemniscateRadius σ) θ) /
          (polarX (lemniscateRadius σ) t - polarX (lemniscateRadius σ) θ)) θ
        (Real.sin θ / Real.cos θ)) :=
  ⟨lemniscate_natural_domain, lemniscate_mem_curve_iff, lemniscate_complete_branch_image,
    lemniscate_loops, fun _ _ hσ hc ↦ lemniscate_pole_tangent hσ hc⟩

end calculus.Chapter04.Section04LemniscatePolarCurveInvestigation
