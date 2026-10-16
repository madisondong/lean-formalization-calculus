import calculus.Chapter04.Section04PolarEquations
import calculus.Chapter04.Section04PolarSymmetry
import calculus.Chapter04.Section04PolarTangents
import calculus.Chapter04.Section03
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Khảo sát hai đường cong cực Bài 4.4.16(a,b)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2791–2794. Góc chạy trên ℝ; bán kính có dấu.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport
open Set Filter
open scoped Topology
open calculus.Chapter03.Section02
open calculus.Chapter04.Section03
open calculus.Chapter04.Section04PolarRepresentation
open calculus.Chapter04.Section04PolarEquations
open calculus.Chapter04.Section04PolarSymmetry
open calculus.Chapter04.Section04PolarTangents


def cosineRadius (a θ : ℝ) : ℝ := 1 + a * Real.cos θ

def cosineXFirst (a θ : ℝ) : ℝ := -Real.sin θ * (1 + 2 * a * Real.cos θ)

def cosineYFirst (a θ : ℝ) : ℝ :=
  Real.cos θ + a * (Real.cos θ ^ 2 - Real.sin θ ^ 2)

def cosineXSecond (a θ : ℝ) : ℝ :=
  -Real.cos θ - 2 * a * (Real.cos θ ^ 2 - Real.sin θ ^ 2)

def cosineYSecond (a θ : ℝ) : ℝ :=
  -Real.sin θ * (1 + 4 * a * Real.cos θ)

def cosineXThird (a θ : ℝ) : ℝ := Real.sin θ * (1 + 8 * a * Real.cos θ)

def cosineYThird (a θ : ℝ) : ℝ :=
  -Real.cos θ - 4 * a * (Real.cos θ ^ 2 - Real.sin θ ^ 2)

def cosineCartesian (a : ℝ) (z : ℂ) : Prop :=
  (z.re ^ 2 + z.im ^ 2 - a * z.re) ^ 2 = z.re ^ 2 + z.im ^ 2


def cosineClosedBranch (a : ℝ) (negative : Bool) : Set ℂ :=
  {z | ∃ θ : ℝ, (if negative then cosineRadius a θ ≤ 0 else 0 ≤ cosineRadius a θ) ∧
    signedPolarPoint (cosineRadius a θ) θ = z}

theorem cosineRadius_hasDerivAt (a θ : ℝ) :
    HasDerivAt (cosineRadius a) (-a * Real.sin θ) θ := by
  simpa only [cosineRadius, mul_neg, neg_mul] using! (Real.hasDerivAt_cos θ).const_mul a |>.const_add 1

theorem cosineRadius_second_hasDerivAt (a θ : ℝ) :
    HasDerivAt (deriv (cosineRadius a)) (-a * Real.cos θ) θ := by
  apply ((Real.hasDerivAt_sin θ).const_mul (-a)).congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (cosineRadius_hasDerivAt a t).deriv

theorem cosineX_hasDerivAt (a θ : ℝ) :
    HasDerivAt (polarX (cosineRadius a)) (cosineXFirst a θ) θ := by
  apply (polarX_hasDerivAt (cosineRadius_hasDerivAt a θ)).congr_deriv
  simp only [cosineXFirst, cosineRadius]
  ring

theorem cosineY_hasDerivAt (a θ : ℝ) :
    HasDerivAt (polarY (cosineRadius a)) (cosineYFirst a θ) θ := by
  apply (polarY_hasDerivAt (cosineRadius_hasDerivAt a θ)).congr_deriv
  simp only [cosineYFirst, cosineRadius]
  ring

theorem cosineXFirst_hasDerivAt (a θ : ℝ) :
    HasDerivAt (cosineXFirst a) (cosineXSecond a θ) θ := by
  have h := (Real.hasDerivAt_sin θ).neg.mul
    ((Real.hasDerivAt_cos θ).const_mul (2 * a) |>.const_add 1)
  apply h.congr_deriv
  simp only [cosineXSecond, Pi.neg_apply]
  ring

theorem cosineYFirst_hasDerivAt (a θ : ℝ) :
    HasDerivAt (cosineYFirst a) (cosineYSecond a θ) θ := by
  have h := (Real.hasDerivAt_cos θ).add
    (((Real.hasDerivAt_cos θ).fun_pow 2).sub ((Real.hasDerivAt_sin θ).fun_pow 2) |>.const_mul a)
  apply h.congr_deriv
  simp only [cosineYSecond]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem cosineX_second_hasDerivAt (a θ : ℝ) :
    HasDerivAt (deriv (polarX (cosineRadius a))) (cosineXSecond a θ) θ := by
  apply (cosineXFirst_hasDerivAt a θ).congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (cosineX_hasDerivAt a t).deriv

theorem cosineY_second_hasDerivAt (a θ : ℝ) :
    HasDerivAt (deriv (polarY (cosineRadius a))) (cosineYSecond a θ) θ := by
  apply (cosineYFirst_hasDerivAt a θ).congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (cosineY_hasDerivAt a t).deriv

theorem cosineXSecond_hasDerivAt (a θ : ℝ) :
    HasDerivAt (cosineXSecond a) (cosineXThird a θ) θ := by
  have h := (Real.hasDerivAt_cos θ).neg.sub
    (((Real.hasDerivAt_cos θ).fun_pow 2).sub ((Real.hasDerivAt_sin θ).fun_pow 2) |>.const_mul (2 * a))
  apply h.congr_deriv
  simp only [cosineXThird]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem cosineYSecond_hasDerivAt (a θ : ℝ) :
    HasDerivAt (cosineYSecond a) (cosineYThird a θ) θ := by
  have h := (Real.hasDerivAt_sin θ).neg.mul
    ((Real.hasDerivAt_cos θ).const_mul (4 * a) |>.const_add 1)
  apply h.congr_deriv
  simp only [cosineYThird, Pi.neg_apply]
  ring

theorem cosineX_third_hasDerivAt (a θ : ℝ) :
    HasDerivAt (deriv (deriv (polarX (cosineRadius a)))) (cosineXThird a θ) θ := by
  apply (cosineXSecond_hasDerivAt a θ).congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (cosineX_second_hasDerivAt a t).deriv

theorem cosineY_third_hasDerivAt (a θ : ℝ) :
    HasDerivAt (deriv (deriv (polarY (cosineRadius a)))) (cosineYThird a θ) θ := by
  apply (cosineYSecond_hasDerivAt a θ).congr_of_eventuallyEq
  exact Eventually.of_forall fun t ↦ (cosineY_second_hasDerivAt a t).deriv


theorem cosine_speed_square (a θ : ℝ) :
    cosineXFirst a θ ^ 2 + cosineYFirst a θ ^ 2 = 1 + a ^ 2 + 2 * a * Real.cos θ := by
  dsimp only [cosineXFirst, cosineYFirst]
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) *
        (1 + 2 * a * Real.cos θ + a ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2)) := by ring
    _ = 1 + a ^ 2 + 2 * a * Real.cos θ := by
      rw [Real.sin_sq_add_cos_sq]
      ring

theorem cosine_point_periodic (a θ : ℝ) :
    signedPolarPoint (cosineRadius a (θ + 2 * Real.pi)) (θ + 2 * Real.pi) =
      signedPolarPoint (cosineRadius a θ) θ := by
  rw [cosineRadius, Real.cos_add_two_pi, signedPolarPoint_add_two_pi]
  rfl

theorem cosine_axis_symmetry (a : ℝ) :
    ∀ z : ℂ, z ∈ polarCurveImage (cosineRadius a) ↔
      polarAxisReflection z ∈ polarCurveImage (cosineRadius a) := by
  apply source_polar_axis_symmetry
  intro r θ
  simp only [cosineRadius, Real.cos_neg]


theorem cosine_signed_radius_identity (a θ : ℝ) :
    (signedPolarPoint (cosineRadius a θ) θ).re ^ 2 +
      (signedPolarPoint (cosineRadius a θ) θ).im ^ 2 -
      a * (signedPolarPoint (cosineRadius a θ) θ).re = cosineRadius a θ := by
  rw [signed_polar_square_sum, signedPolarPoint_re]
  dsimp only [cosineRadius]
  ring


theorem cosine_mem_curve_image_iff (a : ℝ) (hzero : ∃ θ : ℝ, cosineRadius a θ = 0) (z : ℂ) :
    z ∈ polarCurveImage (cosineRadius a) ↔ cosineCartesian a z := by
  constructor
  · rw [source_polar_explicit_membership]
    rintro ⟨θ, rfl⟩
    unfold cosineCartesian
    rw [cosine_signed_radius_identity]
    exact (signed_polar_square_sum _ _).symm
  · intro hz
    by_cases h0 : z = 0
    · subst z
      obtain ⟨θ, hθ⟩ := hzero
      rw [source_polar_explicit_membership]
      exact ⟨θ, by rw [hθ, signedPolarPoint_zero_radius]⟩
    · have hp : 0 < ‖z‖ := norm_pos_iff.mpr h0
      have hs : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have he : (‖z‖ ^ 2 - a * z.re) ^ 2 = ‖z‖ ^ 2 := by
        change (z.re ^ 2 + z.im ^ 2 - a * z.re) ^ 2 = z.re ^ 2 + z.im ^ 2 at hz
        rwa [← hs] at hz
      have hx : ‖z‖ * Real.cos (nonnegativePolarAngle z) = z.re := by
        have h := congrArg Complex.re (signedPolarPoint_norm_nonnegativePolarAngle z)
        simpa only [signedPolarPoint_re] using h
      rw [source_polar_explicit_membership]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with hq | hq
      · have hr : ‖z‖ = cosineRadius a (nonnegativePolarAngle z) := by
          have hmul : ‖z‖ * (‖z‖ - (1 + a * Real.cos (nonnegativePolarAngle z))) = 0 := by
            nlinarith [hq, congrArg (fun x : ℝ ↦ a * x) hx]
          exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hp.ne')
        exact ⟨nonnegativePolarAngle z, by rw [← hr]; exact signedPolarPoint_norm_nonnegativePolarAngle z⟩
      · have hr : -‖z‖ = cosineRadius a (nonnegativePolarAngle z + Real.pi) := by
          rw [cosineRadius, Real.cos_add_pi]
          have hmul : ‖z‖ * (‖z‖ + 1 - a * Real.cos (nonnegativePolarAngle z)) = 0 := by
            nlinarith [hq, congrArg (fun x : ℝ ↦ a * x) hx]
          have hh := (mul_eq_zero.mp hmul).resolve_left hp.ne'
          linarith
        refine ⟨nonnegativePolarAngle z + Real.pi, ?_⟩
        rw [← hr, signedPolarPoint_neg_radius_eq_add_pi,
          show nonnegativePolarAngle z + Real.pi + Real.pi = nonnegativePolarAngle z + 2 * Real.pi by ring,
          signedPolarPoint_add_two_pi]
        exact signedPolarPoint_norm_nonnegativePolarAngle z


theorem cosine_closed_branches_iff (a : ℝ) (z : ℂ) :
    (z ∈ cosineClosedBranch a false ↔ z ∈ polarCurveImage (cosineRadius a) ∧
      0 ≤ z.re ^ 2 + z.im ^ 2 - a * z.re) ∧
    (z ∈ cosineClosedBranch a true ↔ z ∈ polarCurveImage (cosineRadius a) ∧
      z.re ^ 2 + z.im ^ 2 - a * z.re ≤ 0) := by
  constructor <;> constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨(source_polar_explicit_membership _ _).mpr ⟨θ, rfl⟩,
      by simpa only [cosine_signed_radius_identity, Bool.false_eq_true, if_false] using hθ⟩
  · rintro ⟨hz, hsign⟩
    obtain ⟨θ, rfl⟩ := (source_polar_explicit_membership _ _).mp hz
    exact ⟨θ, by simpa only [cosine_signed_radius_identity, Bool.false_eq_true, if_false] using hsign, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨(source_polar_explicit_membership _ _).mpr ⟨θ, rfl⟩,
      by simpa only [cosine_signed_radius_identity, if_true] using hθ⟩
  · rintro ⟨hz, hsign⟩
    obtain ⟨θ, rfl⟩ := (source_polar_explicit_membership _ _).mp hz
    exact ⟨θ, by simpa only [cosine_signed_radius_identity, if_true] using hsign, rfl⟩


theorem secant_zero_implies_deriv_zero {f g : ℝ → ℝ} {D : Set ℝ} {a df dg : ℝ}
    (hf : HasDerivAt f df a) (hg : HasDerivAt g dg a)
    (h : DomainLimit {t | t ∈ D ∧ g t - g a ≠ 0}
      (fun t ↦ (f t - f a) / (g t - g a)) a 0) : df = 0 := by
  let F := 𝓝[({t | t ∈ D ∧ g t - g a ≠ 0} : Set ℝ) \ {a}] a
  let : NeBot F := accumulationPointOf_iff_neBot.mp h.1
  have hle : F ≤ 𝓝[≠] a := nhdsWithin_mono a (by
    intro t ht
    exact ht.2)
  have hfl : Tendsto (fun t ↦ (f t - f a) / (t - a)) F (𝓝 df) := by
    simpa only [slope_fun_def_field] using hf.tendsto_slope.mono_left hle
  have hgl : Tendsto (fun t ↦ (g t - g a) / (t - a)) F (𝓝 dg) := by
    simpa only [slope_fun_def_field] using hg.tendsto_slope.mono_left hle
  have hl := (domainLimit_iff_tendsto h.1).mp h
  have hp : Tendsto (fun t ↦ (f t - f a) / (t - a)) F (𝓝 0) := by
    have hh := hl.mul hgl
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hden : g t - g a ≠ 0 := ht.1.2
    have hta : t - a ≠ 0 := sub_ne_zero.mpr (by
      simpa only [mem_singleton_iff] using ht.2)
    field_simp [hden, hta]
  exact tendsto_nhds_unique hfl hp

theorem cosine_horizontal_necessary {a θ : ℝ}
    (h : HasHorizontalPolarTangent univ (cosineRadius a) θ) : cosineYFirst a θ = 0 :=
  secant_zero_implies_deriv_zero (cosineY_hasDerivAt a θ) (cosineX_hasDerivAt a θ) h

theorem cosine_vertical_necessary {a θ : ℝ}
    (h : HasVerticalPolarTangent univ (cosineRadius a) θ) : cosineXFirst a θ = 0 :=
  secant_zero_implies_deriv_zero (cosineX_hasDerivAt a θ) (cosineY_hasDerivAt a θ) h

theorem source_minimum_univ_iff (f : ℝ → ℝ) (θ : ℝ) :
    IsLocalMinimumOn f univ θ ↔ IsLocalMin f θ := by
  rw [isLocalMinimumOn_iff]
  simp only [mem_univ, true_and, IsLocalMinOn, nhdsWithin_univ, IsLocalMin]

theorem source_maximum_univ_iff (f : ℝ → ℝ) (θ : ℝ) :
    IsLocalMaximumOn f univ θ ↔ IsLocalMax f θ := by
  rw [isLocalMaximumOn_iff]
  simp only [mem_univ, true_and, IsLocalMaxOn, nhdsWithin_univ, IsLocalMax]

theorem second_zero_of_both_extrema {f : ℝ → ℝ} {θ : ℝ}
    (hm : IsLocalMinimumOn f univ θ) (hM : IsLocalMaximumOn f univ θ) :
    deriv (deriv f) θ = 0 := by
  have hmin := (source_minimum_univ_iff f θ).mp hm
  have hmax := (source_maximum_univ_iff f θ).mp hM
  have he : f =ᶠ[𝓝 θ] (fun _ ↦ f θ) := by
    filter_upwards [hmin, hmax] with t ht ht'
    exact le_antisymm ht' ht
  simpa only [deriv_const'] using he.deriv.deriv_eq

theorem nondegenerate_extrema_iff {f : ℝ → ℝ} {θ : ℝ}
    (hf : DifferentiableAt ℝ f θ)
    (hne : deriv f θ = 0 → deriv (deriv f) θ ≠ 0) :
    (IsLocalMinimumOn f univ θ ↔ deriv f θ = 0 ∧ 0 < deriv (deriv f) θ) ∧
      (IsLocalMaximumOn f univ θ ↔ deriv f θ = 0 ∧ deriv (deriv f) θ < 0) := by
  constructor
  · constructor
    · intro hm
      have hd := fermat isOpen_univ (Or.inl hm) hf
      refine ⟨hd, ?_⟩
      by_contra hp
      have hn : deriv (deriv f) θ < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hne hd)
      have hM := (source_maximum_univ_iff f θ).mpr
        (isLocalMax_of_deriv_deriv_neg hn hd hf.continuousAt)
      exact hne hd (second_zero_of_both_extrema hm hM)
    · rintro ⟨hd, hp⟩
      exact (source_minimum_univ_iff f θ).mpr
        (isLocalMin_of_deriv_deriv_pos hp hd hf.continuousAt)
  · constructor
    · intro hM
      have hd := fermat isOpen_univ (Or.inr hM) hf
      refine ⟨hd, ?_⟩
      by_contra hn
      have hp : 0 < deriv (deriv f) θ := lt_of_le_of_ne (le_of_not_gt hn) (hne hd).symm
      have hm := (source_minimum_univ_iff f θ).mpr
        (isLocalMin_of_deriv_deriv_pos hp hd hf.continuousAt)
      exact hne hd (second_zero_of_both_extrema hm hM)
    · rintro ⟨hd, hn⟩
      exact (source_maximum_univ_iff f θ).mpr
        (isLocalMax_of_deriv_deriv_neg hn hd hf.continuousAt)


theorem cosine_radius_extrema (a θ : ℝ) (ha : 0 < a) :
    (IsLocalMinimumOn (cosineRadius a) univ θ ↔ Real.cos θ = -1) ∧
      (IsLocalMaximumOn (cosineRadius a) univ θ ↔ Real.cos θ = 1) := by
  have hne : deriv (cosineRadius a) θ = 0 → deriv (deriv (cosineRadius a)) θ ≠ 0 := by
    intro hd
    rw [(cosineRadius_hasDerivAt a θ).deriv] at hd
    have hs : Real.sin θ = 0 := (mul_eq_zero.mp hd).resolve_left (neg_ne_zero.mpr ha.ne')
    rw [(cosineRadius_second_hasDerivAt a θ).deriv]
    rcases Real.sin_eq_zero_iff_cos_eq.mp hs with h | h
    · rw [h, mul_one]
      exact neg_ne_zero.mpr ha.ne'
    · rw [h, mul_neg_one, neg_neg]
      exact ha.ne'
  have h := nondegenerate_extrema_iff (cosineRadius_hasDerivAt a θ).differentiableAt hne
  rw [(cosineRadius_hasDerivAt a θ).deriv, (cosineRadius_second_hasDerivAt a θ).deriv] at h
  constructor
  · rw [h.1]
    constructor
    · rintro ⟨hs, hp⟩
      have hs0 : Real.sin θ = 0 := (mul_eq_zero.mp hs).resolve_left (neg_ne_zero.mpr ha.ne')
      rcases Real.sin_eq_zero_iff_cos_eq.mp hs0 with hc | hc
      · rw [hc] at hp
        nlinarith
      · exact hc
    · intro hc
      have hs := (Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc))
      rw [hs, hc]
      simp only [mul_zero, mul_neg_one, neg_neg, true_and]
      exact ha
  · rw [h.2]
    constructor
    · rintro ⟨hs, hn⟩
      have hs0 : Real.sin θ = 0 := (mul_eq_zero.mp hs).resolve_left (neg_ne_zero.mpr ha.ne')
      rcases Real.sin_eq_zero_iff_cos_eq.mp hs0 with hc | hc
      · exact hc
      · rw [hc] at hn
        nlinarith
    · intro hc
      have hs := (Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl hc))
      rw [hs, hc]
      simp only [mul_zero, mul_one, true_and]
      exact neg_neg_of_pos ha


theorem cosine_curvature_numerator (a θ : ℝ) :
    cosineXFirst a θ * cosineYSecond a θ - cosineYFirst a θ * cosineXSecond a θ =
      1 + 2 * a ^ 2 + 3 * a * Real.cos θ := by
  dsimp only [cosineXFirst, cosineYFirst, cosineXSecond, cosineYSecond]
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) *
        (1 + 3 * a * Real.cos θ + 2 * a ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2)) := by ring
    _ = 1 + 2 * a ^ 2 + 3 * a * Real.cos θ := by
      rw [Real.sin_sq_add_cos_sq]
      ring


theorem cosine_horizontal_of {a θ : ℝ}
    (hy : cosineYFirst a θ = 0) (hx : cosineXFirst a θ ≠ 0) :
    HasHorizontalPolarTangent univ (cosineRadius a) θ := by
  have heX : -a * Real.sin θ * Real.cos θ - cosineRadius a θ * Real.sin θ =
      cosineXFirst a θ := by dsimp only [cosineRadius, cosineXFirst]; ring
  have heY : -a * Real.sin θ * Real.sin θ + cosineRadius a θ * Real.cos θ =
      cosineYFirst a θ := by dsimp only [cosineRadius, cosineYFirst]; ring
  apply source_horizontal_polar_tangent (Filter.univ_mem) (cosineRadius_hasDerivAt a θ)
  · rwa [heY]
  · rwa [heX]


theorem cosine_vertical_of {a θ : ℝ}
    (hx : cosineXFirst a θ = 0) (hy : cosineYFirst a θ ≠ 0) :
    HasVerticalPolarTangent univ (cosineRadius a) θ := by
  have heX : -a * Real.sin θ * Real.cos θ - cosineRadius a θ * Real.sin θ =
      cosineXFirst a θ := by dsimp only [cosineRadius, cosineXFirst]; ring
  have heY : -a * Real.sin θ * Real.sin θ + cosineRadius a θ * Real.cos θ =
      cosineYFirst a θ := by dsimp only [cosineRadius, cosineYFirst]; ring
  apply source_vertical_polar_tangent (Filter.univ_mem) (cosineRadius_hasDerivAt a θ)
  · rwa [heX]
  · rwa [heY]


theorem cosine_point_injective_off_pole {a θ ψ : ℝ}
    (hθ : θ ∈ Ico 0 (2 * Real.pi)) (hψ : ψ ∈ Ico 0 (2 * Real.pi))
    (hn : cosineRadius a θ ≠ 0)
    (he : signedPolarPoint (cosineRadius a θ) θ = signedPolarPoint (cosineRadius a ψ) ψ) :
    θ = ψ := by
  have hr : cosineRadius a θ = cosineRadius a ψ := by
    have h := congrArg (fun z : ℂ ↦ z.re ^ 2 + z.im ^ 2 - a * z.re) he
    simpa only [cosine_signed_radius_identity] using h
  rw [← hr] at he
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hθ hψ
  apply Circle.ext
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hn) he


theorem cosine_branches_partition (a : ℝ) :
    cosineClosedBranch a false ∪ cosineClosedBranch a true = polarCurveImage (cosineRadius a) ∧
      cosineClosedBranch a false ∩ cosineClosedBranch a true ⊆ {0} := by
  constructor
  · ext z
    rw [mem_union, (cosine_closed_branches_iff a z).1, (cosine_closed_branches_iff a z).2]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total (0 : ℝ) (z.re ^ 2 + z.im ^ 2 - a * z.re) with hp | hn
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, hn⟩
  · intro z hz
    have hp := ((cosine_closed_branches_iff a z).1.mp hz.1).2
    have hn := ((cosine_closed_branches_iff a z).2.mp hz.2).2
    obtain ⟨θ, rfl⟩ := (source_polar_explicit_membership _ _).mp
      ((cosine_closed_branches_iff a z).1.mp hz.1).1
    rw [cosine_signed_radius_identity] at hp hn
    rw [mem_singleton_iff]
    rw [le_antisymm hn hp, signedPolarPoint_zero_radius]


theorem cosine_coordinate_extrema {a θ : ℝ}
    (hcurv : 0 < cosineXFirst a θ * cosineYSecond a θ -
      cosineYFirst a θ * cosineXSecond a θ) :
    ((IsLocalMinimumOn (polarX (cosineRadius a)) univ θ ↔
      cosineXFirst a θ = 0 ∧ 0 < cosineXSecond a θ) ∧
    (IsLocalMaximumOn (polarX (cosineRadius a)) univ θ ↔
      cosineXFirst a θ = 0 ∧ cosineXSecond a θ < 0)) ∧
    ((IsLocalMinimumOn (polarY (cosineRadius a)) univ θ ↔
      cosineYFirst a θ = 0 ∧ 0 < cosineYSecond a θ) ∧
    (IsLocalMaximumOn (polarY (cosineRadius a)) univ θ ↔
      cosineYFirst a θ = 0 ∧ cosineYSecond a θ < 0)) := by
  have hx : deriv (polarX (cosineRadius a)) θ = 0 →
      deriv (deriv (polarX (cosineRadius a))) θ ≠ 0 := by
    rw [(cosineX_hasDerivAt a θ).deriv, (cosineX_second_hasDerivAt a θ).deriv]
    intro hx hx2
    rw [hx, hx2] at hcurv
    norm_num at hcurv
  have hy : deriv (polarY (cosineRadius a)) θ = 0 →
      deriv (deriv (polarY (cosineRadius a))) θ ≠ 0 := by
    rw [(cosineY_hasDerivAt a θ).deriv, (cosineY_second_hasDerivAt a θ).deriv]
    intro hy hy2
    rw [hy, hy2] at hcurv
    norm_num at hcurv
  have hX := nondegenerate_extrema_iff (cosineX_hasDerivAt a θ).differentiableAt hx
  have hY := nondegenerate_extrema_iff (cosineY_hasDerivAt a θ).differentiableAt hy
  rw [(cosineX_hasDerivAt a θ).deriv, (cosineX_second_hasDerivAt a θ).deriv] at hX
  rw [(cosineY_hasDerivAt a θ).deriv, (cosineY_second_hasDerivAt a θ).deriv] at hY
  exact ⟨hX, hY⟩

end calculus.Chapter04.Section04AffineCosinePolarCurveInvestigationSupport
