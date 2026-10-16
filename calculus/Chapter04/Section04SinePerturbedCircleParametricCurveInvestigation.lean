import calculus.Chapter04.Section01Parametric
import calculus.Chapter04.Section04
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 15(i): đường tròn nhiễu sin và các trường hợp suy biến

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2784, `x=a cos t`, `y=a sin t−b sin(nt)`, `a,b>0`, `n` nguyên dương, `0≤t≤2π`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04SinePerturbedCircleParametricCurveInvestigation
open calculus.Chapter04.Section01Parametric
open Polynomial.Chebyshev

def sinePerturbedCircleX (a t : ℝ) : ℝ := a * Real.cos t
def sinePerturbedCircleY (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  a * Real.sin t - b * Real.sin ((n : ℝ) * t)
def sinePerturbedCircleDomain : Set ℝ := Icc 0 (2 * Real.pi)
def sinePerturbedCircleCurve (a b : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  parametricCurve (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) sinePerturbedCircleDomain
def sinePerturbedCircleCoefficient (a b : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  a - b * (U ℝ ((n : ℤ) - 1)).eval u
def sinePerturbedCircleHorizontalPolynomial (a b : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  a * u - (n : ℝ) * b * (T ℝ (n : ℤ)).eval u
def sinePerturbedCircleSignedCurvatureNumeratorPolynomial (a b : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  a * (a - (n : ℝ) * b * (u * (T ℝ (n : ℤ)).eval u +
    (n : ℝ) * (1 - u ^ 2) * (U ℝ ((n : ℤ) - 1)).eval u))
def sinePerturbedCircleImplicit (a b : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  {p | |p.1 / a| ≤ 1 ∧ p.2 ^ 2 =
    (1 - (p.1 / a) ^ 2) * sinePerturbedCircleCoefficient a b n (p.1 / a) ^ 2}
def sinePerturbedCircleTangent (a b : ℝ) (n : ℕ) (t : ℝ) : Set (ℝ × ℝ) :=
  {p | deriv (sinePerturbedCircleY a b n) t * (p.1 - sinePerturbedCircleX a t) =
    deriv (sinePerturbedCircleX a) t * (p.2 - sinePerturbedCircleY a b n t)}
def sinePerturbedCircleSignedCurvature (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (deriv (sinePerturbedCircleX a) t * deriv (deriv (sinePerturbedCircleY a b n)) t -
    deriv (sinePerturbedCircleY a b n) t * deriv (deriv (sinePerturbedCircleX a)) t) /
    Real.sqrt (deriv (sinePerturbedCircleX a) t ^ 2 + deriv (sinePerturbedCircleY a b n) t ^ 2) ^ 3

theorem sine_perturbed_circle_positive_integer_bridge {m : ℤ} (hm : 0 < m) :
    ∃ n : ℕ, 0 < n ∧ (n : ℤ) = m := by
  refine ⟨m.toNat, ?_, Int.toNat_of_nonneg hm.le⟩
  have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm.le
  exact_mod_cast (show 0 < (m.toNat : ℤ) from by rw [he]; exact hm)

theorem sine_perturbed_circle_chebyshev_identities (n : ℕ) (t : ℝ) :
    (T ℝ (n : ℤ)).eval (Real.cos t) = Real.cos ((n : ℝ) * t) ∧
    (U ℝ ((n : ℤ) - 1)).eval (Real.cos t) * Real.sin t =
      Real.sin ((n : ℝ) * t) := by
  constructor
  · simpa only [Int.cast_natCast] using T_real_cos t (n : ℤ)
  · simpa only [Int.cast_sub, Int.cast_one, Int.cast_natCast, sub_add_cancel] using U_real_cos t ((n : ℤ) - 1)

theorem sine_perturbed_circle_y_factored (a b t : ℝ) (n : ℕ) :
    sinePerturbedCircleY a b n t = Real.sin t * sinePerturbedCircleCoefficient a b n (Real.cos t) := by
  unfold sinePerturbedCircleY sinePerturbedCircleCoefficient
  rw [← (sine_perturbed_circle_chebyshev_identities n t).2]
  ring

theorem sine_perturbed_circle_complete_implicit_image {a : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ) :
    sinePerturbedCircleCurve a b n = sinePerturbedCircleImplicit a b n := by
  ext p
  constructor
  · rintro ⟨t, _, rfl⟩
    change |(a * Real.cos t) / a| ≤ 1 ∧ sinePerturbedCircleY a b n t ^ 2 =
      (1 - ((a * Real.cos t) / a) ^ 2) *
        sinePerturbedCircleCoefficient a b n ((a * Real.cos t) / a) ^ 2
    rw [mul_div_cancel_left₀ _ ha.ne', sine_perturbed_circle_y_factored]
    refine ⟨Real.abs_cos_le_one t, ?_⟩
    have hs : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    rw [mul_pow, hs]
  · intro hp
    change |p.1 / a| ≤ 1 ∧ p.2 ^ 2 =
      (1 - (p.1 / a) ^ 2) * sinePerturbedCircleCoefficient a b n (p.1 / a) ^ 2 at hp
    let u := p.1 / a
    let q := sinePerturbedCircleCoefficient a b n u
    have hu : u ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one u).mpr hp.1
    have hxy : p.2 ^ 2 = (1 - u ^ 2) * q ^ 2 := hp.2
    by_cases hq : q = 0
    · have hy : p.2 = 0 := by rw [hq] at hxy; nlinarith [sq_nonneg p.2]
      have hv : u ^ 2 + Real.sqrt (1 - u ^ 2) ^ 2 = 1 := by
        rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - u ^ 2)]
        ring
      obtain ⟨t, ht, hc, _⟩ := unit_circle_parameter hv
      refine ⟨t, ht, ?_⟩
      apply Prod.ext
      · change a * Real.cos t = p.1
        rw [hc]
        exact mul_div_cancel₀ _ ha.ne'
      · change sinePerturbedCircleY a b n t = p.2
        rw [sine_perturbed_circle_y_factored, hc]
        change Real.sin t * q = p.2
        rw [hq, hy, mul_zero]
    · have hv : u ^ 2 + (p.2 / q) ^ 2 = 1 := by
        field_simp [hq]
        nlinarith [hxy]
      obtain ⟨t, ht, hc, hs⟩ := unit_circle_parameter hv
      refine ⟨t, ht, ?_⟩
      apply Prod.ext
      · change a * Real.cos t = p.1
        rw [hc]
        exact mul_div_cancel₀ _ ha.ne'
      · change sinePerturbedCircleY a b n t = p.2
        rw [sine_perturbed_circle_y_factored, hc, hs]
        exact div_mul_cancel₀ _ hq

theorem sine_perturbed_circle_actual_coordinate_derivatives (a b t : ℝ) (n : ℕ) :
    HasDerivAt (sinePerturbedCircleX a) (-a * Real.sin t) t ∧
    HasDerivAt (sinePerturbedCircleY a b n)
      (a * Real.cos t - (n : ℝ) * b * Real.cos ((n : ℝ) * t)) t := by
  constructor
  · unfold sinePerturbedCircleX
    convert! (Real.hasDerivAt_cos t).const_mul a using 1
    ring
  · unfold sinePerturbedCircleY
    convert! ((Real.hasDerivAt_sin t).const_mul a).sub
      (((Real.hasDerivAt_sin ((n : ℝ) * t)).comp t
        ((hasDerivAt_id t).const_mul (n : ℝ))).const_mul b) using 1
    ring

theorem sine_perturbed_circle_actual_derivative_values (a b t : ℝ) (n : ℕ) :
    deriv (sinePerturbedCircleX a) t = -a * Real.sin t ∧
    deriv (sinePerturbedCircleY a b n) t = a * Real.cos t - (n : ℝ) * b * Real.cos ((n : ℝ) * t) :=
  ⟨(sine_perturbed_circle_actual_coordinate_derivatives a b t n).1.deriv,
    (sine_perturbed_circle_actual_coordinate_derivatives a b t n).2.deriv⟩

theorem sine_perturbed_circle_actual_second_derivatives (a b t : ℝ) (n : ℕ) :
    HasDerivAt (deriv (sinePerturbedCircleX a)) (-a * Real.cos t) t ∧
    HasDerivAt (deriv (sinePerturbedCircleY a b n))
      (-a * Real.sin t + (n : ℝ) ^ 2 * b * Real.sin ((n : ℝ) * t)) t := by
  have hx : deriv (sinePerturbedCircleX a) = (fun u : ℝ ↦ -a * Real.sin u) :=
    funext (fun u ↦ (sine_perturbed_circle_actual_derivative_values a b u n).1)
  have hy : deriv (sinePerturbedCircleY a b n) =
      (fun u : ℝ ↦ a * Real.cos u - (n : ℝ) * b * Real.cos ((n : ℝ) * u)) :=
    funext (fun u ↦ (sine_perturbed_circle_actual_derivative_values a b u n).2)
  rw [hx, hy]
  constructor
  · simpa using! (Real.hasDerivAt_sin t).const_mul (-a)
  · convert! ((Real.hasDerivAt_cos t).const_mul a).sub
      (((Real.hasDerivAt_cos ((n : ℝ) * t)).comp t
        ((hasDerivAt_id t).const_mul (n : ℝ))).const_mul ((n : ℝ) * b)) using 1
    ring

theorem sine_perturbed_circle_actual_third_derivatives (a b t : ℝ) (n : ℕ) :
    HasDerivAt (deriv (deriv (sinePerturbedCircleX a))) (a * Real.sin t) t ∧
    HasDerivAt (deriv (deriv (sinePerturbedCircleY a b n)))
      (-a * Real.cos t + (n : ℝ) ^ 3 * b * Real.cos ((n : ℝ) * t)) t := by
  have hx : deriv (deriv (sinePerturbedCircleX a)) = (fun u : ℝ ↦ -a * Real.cos u) :=
    funext (fun u ↦ (sine_perturbed_circle_actual_second_derivatives a b u n).1.deriv)
  have hy : deriv (deriv (sinePerturbedCircleY a b n)) =
      (fun u : ℝ ↦ -a * Real.sin u + (n : ℝ) ^ 2 * b * Real.sin ((n : ℝ) * u)) :=
    funext (fun u ↦ (sine_perturbed_circle_actual_second_derivatives a b u n).2.deriv)
  rw [hx, hy]
  constructor
  · convert! (Real.hasDerivAt_cos t).const_mul (-a) using 1
    ring
  · convert! ((Real.hasDerivAt_sin t).const_mul (-a)).add
      (((Real.hasDerivAt_sin ((n : ℝ) * t)).comp t
        ((hasDerivAt_id t).const_mul (n : ℝ))).const_mul ((n : ℝ) ^ 2 * b)) using 1
    ring

theorem sine_perturbed_circle_continuous_compact (a b : ℝ) (n : ℕ) :
    Continuous (sinePerturbedCircleX a) ∧ Continuous (sinePerturbedCircleY a b n) ∧ IsCompact (sinePerturbedCircleCurve a b n) := by
  have hx : Continuous (sinePerturbedCircleX a) := Real.continuous_cos.const_mul a
  have hy : Continuous (sinePerturbedCircleY a b n) := (Real.continuous_sin.const_mul a).sub
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul b)
  exact ⟨hx, hy, isCompact_Icc.image (hx.prodMk hy)⟩

theorem sine_perturbed_circle_coordinate_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) (t : ℝ) :
    |sinePerturbedCircleX a t| ≤ a ∧ |sinePerturbedCircleY a b n t| ≤ a + b := by
  constructor
  · unfold sinePerturbedCircleX
    rw [abs_mul, abs_of_pos ha]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) ha.le
  · calc
      |sinePerturbedCircleY a b n t| ≤ |a * Real.sin t| + |b * Real.sin ((n : ℝ) * t)| := abs_sub _ _
      _ ≤ a + b := by
        rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
        exact add_le_add
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) ha.le)
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one ((n : ℝ) * t)) hb.le)

theorem sine_perturbed_circle_period_and_reflection (a b t : ℝ) (n : ℕ) :
    parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) (t + 2 * Real.pi) =
      parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) t ∧
    parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) (2 * Real.pi - t) =
      (sinePerturbedCircleX a t, -sinePerturbedCircleY a b n t) := by
  have he1 : (n : ℝ) * (t + 2 * Real.pi) = (n : ℝ) * t + (n : ℝ) * (2 * Real.pi) := by ring
  have he2 : (n : ℝ) * (2 * Real.pi - t) = (n : ℝ) * (2 * Real.pi) - (n : ℝ) * t := by ring
  simp only [parametricPoint, sinePerturbedCircleX, sinePerturbedCircleY, he1, he2,
    Real.cos_add_two_pi, Real.sin_add_two_pi, Real.sin_add_nat_mul_two_pi,
    Real.cos_two_pi_sub, Real.sin_two_pi_sub, Real.sin_nat_mul_two_pi_sub]
  constructor
  · trivial
  · apply Prod.ext <;> dsimp
    ring

theorem sine_perturbed_circle_parity_reflection (a b t : ℝ) (n : ℕ) :
    sinePerturbedCircleX a (Real.pi - t) = -sinePerturbedCircleX a t ∧
    sinePerturbedCircleY a b n (Real.pi - t) =
      a * Real.sin t + b * (-1 : ℝ) ^ n * Real.sin ((n : ℝ) * t) := by
  have he : (n : ℝ) * (Real.pi - t) = (n : ℝ) * Real.pi - (n : ℝ) * t := by ring
  simp only [sinePerturbedCircleX, sinePerturbedCircleY, Real.cos_pi_sub, Real.sin_pi_sub, he,
    Real.sin_nat_mul_pi_sub]
  constructor <;> ring

theorem sine_perturbed_circle_odd_vertical_symmetry (a b t : ℝ) {n : ℕ} (hn : Odd n) :
    parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) (Real.pi - t) =
      (-sinePerturbedCircleX a t, sinePerturbedCircleY a b n t) := by
  apply Prod.ext
  · exact (sine_perturbed_circle_parity_reflection a b t n).1
  · dsimp [parametricPoint]
    rw [(sine_perturbed_circle_parity_reflection a b t n).2, hn.neg_one_pow]
    unfold sinePerturbedCircleY
    ring

theorem sine_perturbed_circle_whole_curve_horizontal_symmetry (a b : ℝ) (n : ℕ) :
    ∀ p ∈ sinePerturbedCircleCurve a b n, (p.1, -p.2) ∈ sinePerturbedCircleCurve a b n := by
  rintro p ⟨t, ht, rfl⟩
  refine ⟨2 * Real.pi - t, ?_, (sine_perturbed_circle_period_and_reflection a b t n).2⟩
  change 0 ≤ 2 * Real.pi - t ∧ 2 * Real.pi - t ≤ 2 * Real.pi
  change 0 ≤ t ∧ t ≤ 2 * Real.pi at ht
  constructor <;> linarith [ht.1, ht.2]

theorem sine_perturbed_circle_odd_whole_curve_vertical_symmetry (a b : ℝ) {n : ℕ} (hn : Odd n) :
    ∀ p ∈ sinePerturbedCircleCurve a b n, (-p.1, p.2) ∈ sinePerturbedCircleCurve a b n := by
  rintro p ⟨t, ht, rfl⟩
  change 0 ≤ t ∧ t ≤ 2 * Real.pi at ht
  by_cases htπ : t ≤ Real.pi
  · refine ⟨Real.pi - t, ?_, sine_perturbed_circle_odd_vertical_symmetry a b t hn⟩
    change 0 ≤ Real.pi - t ∧ Real.pi - t ≤ 2 * Real.pi
    constructor <;> linarith [ht.1, htπ, Real.pi_pos]
  · refine ⟨(Real.pi - t) + 2 * Real.pi, ?_, ?_⟩
    · change 0 ≤ (Real.pi - t) + 2 * Real.pi ∧ (Real.pi - t) + 2 * Real.pi ≤ 2 * Real.pi
      constructor <;> linarith [ht.2, lt_of_not_ge htπ, Real.pi_pos]
    · rw [(sine_perturbed_circle_period_and_reflection a b (Real.pi - t) n).1]
      exact sine_perturbed_circle_odd_vertical_symmetry a b t hn

theorem sine_perturbed_circle_endpoint_and_midpoint_values (a b : ℝ) (n : ℕ) :
    parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) 0 = (a, 0) ∧
    parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) Real.pi = (-a, 0) ∧
    parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) (2 * Real.pi) = (a, 0) := by
  simp only [parametricPoint, sinePerturbedCircleX, sinePerturbedCircleY, mul_zero, Real.sin_zero, Real.cos_zero,
    mul_one, sub_self, Real.sin_pi, Real.cos_pi, Real.sin_nat_mul_pi,
    Real.sin_two_pi, Real.cos_two_pi]
  have hn2 : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa only [sub_zero, Real.sin_zero, neg_zero] using Real.sin_nat_mul_two_pi_sub (0 : ℝ) n
  norm_num [hn2]

theorem sine_perturbed_circle_x_strict_branches {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (sinePerturbedCircleX a) (Icc 0 Real.pi) ∧
    StrictMonoOn (sinePerturbedCircleX a) (Icc Real.pi (2 * Real.pi)) := by
  constructor
  · intro s hs t ht hst
    exact mul_lt_mul_of_pos_left (Real.strictAntiOn_cos hs ht hst) ha
  · intro s hs t ht hst
    have h := Real.strictAntiOn_cos
      (show 2 * Real.pi - t ∈ Icc 0 Real.pi from ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      (show 2 * Real.pi - s ∈ Icc 0 Real.pi from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (by linarith : 2 * Real.pi - t < 2 * Real.pi - s)
    rw [Real.cos_two_pi_sub, Real.cos_two_pi_sub] at h
    exact mul_lt_mul_of_pos_left h ha

theorem sine_perturbed_circle_each_half_is_injective {a : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ) :
    InjOn (parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n)) (Icc 0 Real.pi) ∧
    InjOn (parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n)) (Icc Real.pi (2 * Real.pi)) := by
  constructor
  · intro s hs t ht he
    exact (sine_perturbed_circle_x_strict_branches ha).1.injOn hs ht (congrArg Prod.fst he)
  · intro s hs t ht he
    exact (sine_perturbed_circle_x_strict_branches ha).2.injOn hs ht (congrArg Prod.fst he)

theorem sine_perturbed_circle_equal_cos_on_original_interval {s t : ℝ}
    (hs : s ∈ sinePerturbedCircleDomain) (ht : t ∈ sinePerturbedCircleDomain) :
    Real.cos s = Real.cos t ↔ s = t ∨ s + t = 2 * Real.pi := by
  change 0 ≤ s ∧ s ≤ 2 * Real.pi at hs
  change 0 ≤ t ∧ t ≤ 2 * Real.pi at ht
  constructor
  · intro hc
    by_cases hsπ : s ≤ Real.pi
    · by_cases htπ : t ≤ Real.pi
      · exact Or.inl (Real.injOn_cos ⟨hs.1, hsπ⟩ ⟨ht.1, htπ⟩ hc)
      · have he := Real.injOn_cos ⟨hs.1, hsπ⟩
          (show 2 * Real.pi - t ∈ Icc 0 Real.pi from
            ⟨by linarith [ht.2], by linarith [lt_of_not_ge htπ]⟩)
          (by simpa only [Real.cos_two_pi_sub] using hc)
        exact Or.inr (by linarith)
    · by_cases htπ : t ≤ Real.pi
      · have he := Real.injOn_cos
          (show 2 * Real.pi - s ∈ Icc 0 Real.pi from
            ⟨by linarith [hs.2], by linarith [lt_of_not_ge hsπ]⟩)
          ⟨ht.1, htπ⟩ (by simpa only [Real.cos_two_pi_sub] using hc)
        exact Or.inr (by linarith)
      · have he := Real.injOn_cos
          (show 2 * Real.pi - s ∈ Icc 0 Real.pi from
            ⟨by linarith [hs.2], by linarith [lt_of_not_ge hsπ]⟩)
          (show 2 * Real.pi - t ∈ Icc 0 Real.pi from
            ⟨by linarith [ht.2], by linarith [lt_of_not_ge htπ]⟩)
          (by simpa only [Real.cos_two_pi_sub] using hc)
        exact Or.inl (by linarith)
  · rintro (rfl | he)
    · rfl
    · have hs' : s = 2 * Real.pi - t := by linarith
      rw [hs', Real.cos_two_pi_sub]

theorem sine_perturbed_circle_complete_same_point_criterion {a s t : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ)
    (hs : s ∈ sinePerturbedCircleDomain) (ht : t ∈ sinePerturbedCircleDomain) :
    parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) s =
      parametricPoint (sinePerturbedCircleX a) (sinePerturbedCircleY a b n) t ↔
      s = t ∨ (s + t = 2 * Real.pi ∧ sinePerturbedCircleY a b n s = 0) := by
  constructor
  · intro he
    have hc : Real.cos s = Real.cos t :=
      mul_left_cancel₀ ha.ne' (congrArg Prod.fst he)
    rcases (sine_perturbed_circle_equal_cos_on_original_interval hs ht).mp hc with hst | hsum
    · exact Or.inl hst
    · have ht' : t = 2 * Real.pi - s := by linarith
      have hy : sinePerturbedCircleY a b n s = -sinePerturbedCircleY a b n s := by
        have h := congrArg Prod.snd he
        rw [ht'] at h
        have hr := congrArg Prod.snd (sine_perturbed_circle_period_and_reflection a b s n).2
        change sinePerturbedCircleY a b n (2 * Real.pi - s) = -sinePerturbedCircleY a b n s at hr
        change sinePerturbedCircleY a b n s = sinePerturbedCircleY a b n (2 * Real.pi - s) at h
        rw [hr] at h
        exact h
      exact Or.inr ⟨hsum, by linarith⟩
  · rintro (rfl | ⟨hsum, hy⟩)
    · rfl
    · have ht' : t = 2 * Real.pi - s := by linarith
      rw [ht', (sine_perturbed_circle_period_and_reflection a b s n).2]
      change (sinePerturbedCircleX a s, sinePerturbedCircleY a b n s) = (sinePerturbedCircleX a s, -sinePerturbedCircleY a b n s)
      rw [hy, neg_zero]

theorem sine_perturbed_circle_interior_axis_crossings (a b : ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo 0 Real.pi) :
    sinePerturbedCircleY a b n t = 0 ↔ sinePerturbedCircleCoefficient a b n (Real.cos t) = 0 := by
  rw [sine_perturbed_circle_y_factored]
  exact mul_eq_zero.trans (or_iff_right (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne')

theorem sine_perturbed_circle_derivative_polynomial (a b t : ℝ) (n : ℕ) :
    deriv (sinePerturbedCircleY a b n) t = sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) := by
  rw [(sine_perturbed_circle_actual_derivative_values a b t n).2]
  unfold sinePerturbedCircleHorizontalPolynomial
  rw [(sine_perturbed_circle_chebyshev_identities n t).1]

theorem sine_perturbed_circle_regular_and_tangent_criteria {a : ℝ} (ha : 0 < a) (b t : ℝ) (n : ℕ) :
    (deriv (sinePerturbedCircleX a) t ≠ 0 ∨ deriv (sinePerturbedCircleY a b n) t ≠ 0 ↔
      Real.sin t ≠ 0 ∨ sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) ≠ 0) ∧
    (deriv (sinePerturbedCircleX a) t = 0 ∧ deriv (sinePerturbedCircleY a b n) t ≠ 0 ↔
      Real.sin t = 0 ∧ sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) ≠ 0) ∧
    (deriv (sinePerturbedCircleY a b n) t = 0 ∧ deriv (sinePerturbedCircleX a) t ≠ 0 ↔
      sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) = 0 ∧ Real.sin t ≠ 0) := by
  rw [(sine_perturbed_circle_actual_derivative_values a b t n).1, sine_perturbed_circle_derivative_polynomial]
  simp only [ne_eq, mul_eq_zero, neg_eq_zero, ha.ne', false_or]
  exact ⟨trivial, trivial, trivial⟩

theorem sine_perturbed_circle_actual_regular_tangent {a t : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ)
    (hs : Real.sin t ≠ 0) (p : ℝ × ℝ) :
    p ∈ sinePerturbedCircleTangent a b n t ↔ p.2 = sinePerturbedCircleY a b n t +
      sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) / (-a * Real.sin t) *
        (p.1 - sinePerturbedCircleX a t) := by
  have hx : -a * Real.sin t ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ha.ne') hs
  change deriv (sinePerturbedCircleY a b n) t * (p.1 - sinePerturbedCircleX a t) =
    deriv (sinePerturbedCircleX a) t * (p.2 - sinePerturbedCircleY a b n t) ↔ _
  rw [(sine_perturbed_circle_actual_derivative_values a b t n).1, sine_perturbed_circle_derivative_polynomial]
  constructor
  · intro h
    field_simp [hx]
    all_goals nlinarith [h]
  · intro h
    rw [h]
    field_simp [hx]
    ring

theorem sine_perturbed_circle_actual_vertical_tangent {a t : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ)
    (hs : Real.sin t = 0)
    (hy : sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) ≠ 0) (p : ℝ × ℝ) :
    p ∈ sinePerturbedCircleTangent a b n t ↔ p.1 = sinePerturbedCircleX a t := by
  have hv : deriv (sinePerturbedCircleX a) t = 0 ∧ deriv (sinePerturbedCircleY a b n) t ≠ 0 :=
    (sine_perturbed_circle_regular_and_tangent_criteria ha b t n).2.1.mpr ⟨hs, hy⟩
  change deriv (sinePerturbedCircleY a b n) t * (p.1 - sinePerturbedCircleX a t) =
    deriv (sinePerturbedCircleX a) t * (p.2 - sinePerturbedCircleY a b n t) ↔ _
  rw [hv.1]
  simp only [zero_mul, mul_eq_zero, hv.2, false_or, sub_eq_zero]

theorem sine_perturbed_circle_y_strict_branches (a b : ℝ) (n : ℕ) {D : Set ℝ} (hD : Convex ℝ D) :
    (∀ t ∈ interior D, 0 < sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t)) →
      StrictMonoOn (sinePerturbedCircleY a b n) D := by
  intro h
  apply strictMonoOn_of_deriv_pos hD (sine_perturbed_circle_continuous_compact a b n).2.1.continuousOn
  intro t ht
  rw [sine_perturbed_circle_derivative_polynomial]
  exact h t ht

theorem sine_perturbed_circle_y_strict_anti_branches (a b : ℝ) (n : ℕ) {D : Set ℝ} (hD : Convex ℝ D) :
    (∀ t ∈ interior D, sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) < 0) →
      StrictAntiOn (sinePerturbedCircleY a b n) D := by
  intro h
  apply strictAntiOn_of_deriv_neg hD (sine_perturbed_circle_continuous_compact a b n).2.1.continuousOn
  intro t ht
  rw [sine_perturbed_circle_derivative_polynomial]
  exact h t ht

theorem sine_perturbed_circle_signed_curvature_numerator (a b t : ℝ) (n : ℕ) :
    deriv (sinePerturbedCircleX a) t * deriv (deriv (sinePerturbedCircleY a b n)) t -
      deriv (sinePerturbedCircleY a b n) t * deriv (deriv (sinePerturbedCircleX a)) t =
        a ^ 2 - a * (n : ℝ) * b * (Real.cos t * Real.cos ((n : ℝ) * t) +
          (n : ℝ) * Real.sin t * Real.sin ((n : ℝ) * t)) := by
  rw [(sine_perturbed_circle_actual_derivative_values a b t n).1,
    (sine_perturbed_circle_actual_derivative_values a b t n).2,
    (sine_perturbed_circle_actual_second_derivatives a b t n).1.deriv,
    (sine_perturbed_circle_actual_second_derivatives a b t n).2.deriv]
  nlinarith [congrArg (fun z : ℝ ↦ a ^ 2 * z) (Real.sin_sq_add_cos_sq t)]

theorem sine_perturbed_circle_signed_curvature_numerator_polynomial_exact (a b t : ℝ) (n : ℕ) :
    deriv (sinePerturbedCircleX a) t * deriv (deriv (sinePerturbedCircleY a b n)) t -
      deriv (sinePerturbedCircleY a b n) t * deriv (deriv (sinePerturbedCircleX a)) t =
        sinePerturbedCircleSignedCurvatureNumeratorPolynomial a b n (Real.cos t) := by
  rw [sine_perturbed_circle_signed_curvature_numerator]
  unfold sinePerturbedCircleSignedCurvatureNumeratorPolynomial
  rw [(sine_perturbed_circle_chebyshev_identities n t).1, ← (sine_perturbed_circle_chebyshev_identities n t).2]
  have hs : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  calc
    _ = a * (a - (n : ℝ) * b *
        (Real.cos t * Real.cos ((n : ℝ) * t) +
        (n : ℝ) * Real.sin t ^ 2 * (U ℝ ((n : ℤ) - 1)).eval (Real.cos t))) := by ring
    _ = _ := by rw [hs]

theorem sine_perturbed_circle_regular_speed_positive (a b t : ℝ) (n : ℕ)
    (hr : deriv (sinePerturbedCircleX a) t ≠ 0 ∨ deriv (sinePerturbedCircleY a b n) t ≠ 0) :
    0 < deriv (sinePerturbedCircleX a) t ^ 2 + deriv (sinePerturbedCircleY a b n) t ^ 2 ∧
    0 < Real.sqrt (deriv (sinePerturbedCircleX a) t ^ 2 + deriv (sinePerturbedCircleY a b n) t ^ 2) ^ 3 := by
  have hp : 0 < deriv (sinePerturbedCircleX a) t ^ 2 + deriv (sinePerturbedCircleY a b n) t ^ 2 := by
    rcases hr with hx | hy
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hy)
  exact ⟨hp, pow_pos (Real.sqrt_pos.mpr hp) 3⟩

theorem sine_perturbed_circle_regular_signed_curvature_sign_criteria (a b t : ℝ) (n : ℕ)
    (hr : deriv (sinePerturbedCircleX a) t ≠ 0 ∨ deriv (sinePerturbedCircleY a b n) t ≠ 0) :
    (sinePerturbedCircleSignedCurvature a b n t = 0 ↔ sinePerturbedCircleSignedCurvatureNumeratorPolynomial a b n (Real.cos t) = 0) ∧
    (0 < sinePerturbedCircleSignedCurvature a b n t ↔ 0 < sinePerturbedCircleSignedCurvatureNumeratorPolynomial a b n (Real.cos t)) ∧
    (sinePerturbedCircleSignedCurvature a b n t < 0 ↔ sinePerturbedCircleSignedCurvatureNumeratorPolynomial a b n (Real.cos t) < 0) := by
  have hd := (sine_perturbed_circle_regular_speed_positive a b t n hr).2
  unfold sinePerturbedCircleSignedCurvature
  rw [sine_perturbed_circle_signed_curvature_numerator_polynomial_exact]
  constructor
  · simp only [div_eq_zero_iff, hd.ne', or_false]
  · constructor
    · rw [lt_div_iff₀ hd, zero_mul]
    · rw [div_lt_iff₀ hd, zero_mul]

theorem sine_perturbed_circle_sine_zero_on_original_interval {t : ℝ} (ht : t ∈ sinePerturbedCircleDomain) :
    Real.sin t = 0 ↔ t = 0 ∨ t = Real.pi ∨ t = 2 * Real.pi := by
  change 0 ≤ t ∧ t ≤ 2 * Real.pi at ht
  constructor
  · intro hs
    rcases lt_trichotomy t Real.pi with h | h | h
    · by_cases ht0 : t = 0
      · exact Or.inl ht0
      · exact False.elim ((Real.sin_pos_of_pos_of_lt_pi
          (lt_of_le_of_ne ht.1 (Ne.symm ht0)) h).ne' hs)
    · exact Or.inr (Or.inl h)
    · by_cases ht2 : t = 2 * Real.pi
      · exact Or.inr (Or.inr ht2)
      · have hp := Real.sin_pos_of_pos_of_lt_pi
          (show 0 < 2 * Real.pi - t from sub_pos.mpr (lt_of_le_of_ne ht.2 ht2))
          (by linarith : 2 * Real.pi - t < Real.pi)
        rw [Real.sin_two_pi_sub, hs, neg_zero] at hp
        exact False.elim (lt_irrefl 0 hp)
  · rintro (rfl | rfl | rfl)
    · exact Real.sin_zero
    · exact Real.sin_pi
    · exact Real.sin_two_pi

theorem sine_perturbed_circle_endpoint_derivative_values (a b : ℝ) (n : ℕ) :
    deriv (sinePerturbedCircleX a) 0 = 0 ∧ deriv (sinePerturbedCircleX a) Real.pi = 0 ∧
    deriv (sinePerturbedCircleX a) (2 * Real.pi) = 0 ∧
    deriv (sinePerturbedCircleY a b n) 0 = a - (n : ℝ) * b ∧
    deriv (sinePerturbedCircleY a b n) Real.pi = -a - (n : ℝ) * b * (-1 : ℝ) ^ n ∧
    deriv (sinePerturbedCircleY a b n) (2 * Real.pi) = a - (n : ℝ) * b := by
  rw [(sine_perturbed_circle_actual_derivative_values a b 0 n).1,
    (sine_perturbed_circle_actual_derivative_values a b Real.pi n).1,
    (sine_perturbed_circle_actual_derivative_values a b (2 * Real.pi) n).1,
    (sine_perturbed_circle_actual_derivative_values a b 0 n).2,
    (sine_perturbed_circle_actual_derivative_values a b Real.pi n).2,
    (sine_perturbed_circle_actual_derivative_values a b (2 * Real.pi) n).2]
  simp only [Real.sin_zero, Real.sin_pi, Real.sin_two_pi, Real.cos_zero, Real.cos_pi,
    Real.cos_two_pi, Real.cos_nat_mul_pi, Real.cos_nat_mul_two_pi,
    mul_zero, mul_one, mul_neg, and_self]

theorem sine_perturbed_circle_complete_singular_parameter_classification {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ sinePerturbedCircleDomain) :
    deriv (sinePerturbedCircleX a) t = 0 ∧ deriv (sinePerturbedCircleY a b n) t = 0 ↔
      a = (n : ℝ) * b ∧
        (t = 0 ∨ t = 2 * Real.pi ∨ (Odd n ∧ t = Real.pi)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnb : 0 < (n : ℝ) * b := mul_pos hnR hb
  constructor
  · rintro ⟨hx, hy⟩
    rw [(sine_perturbed_circle_actual_derivative_values a b t n).1] at hx
    have hs : Real.sin t = 0 := (mul_eq_zero.mp hx).resolve_left (neg_ne_zero.mpr ha.ne')
    rcases (sine_perturbed_circle_sine_zero_on_original_interval ht).mp hs with rfl | rfl | rfl
    · rw [(sine_perturbed_circle_endpoint_derivative_values a b n).2.2.2.1] at hy
      exact ⟨sub_eq_zero.mp hy, Or.inl rfl⟩
    · have hp := (sine_perturbed_circle_endpoint_derivative_values a b n).2.2.2.2.1
      rw [hp] at hy
      rcases Nat.even_or_odd n with he | ho
      · rw [he.neg_one_pow] at hy
        nlinarith
      · rw [ho.neg_one_pow] at hy
        exact ⟨by nlinarith, Or.inr (Or.inr ⟨ho, rfl⟩)⟩
    · rw [(sine_perturbed_circle_endpoint_derivative_values a b n).2.2.2.2.2] at hy
      exact ⟨sub_eq_zero.mp hy, Or.inr (Or.inl rfl)⟩
  · rintro ⟨he, rfl | rfl | ⟨ho, rfl⟩⟩
    · exact ⟨(sine_perturbed_circle_endpoint_derivative_values a b n).1,
        by rw [(sine_perturbed_circle_endpoint_derivative_values a b n).2.2.2.1, he, sub_self]⟩
    · exact ⟨(sine_perturbed_circle_endpoint_derivative_values a b n).2.2.1,
        by rw [(sine_perturbed_circle_endpoint_derivative_values a b n).2.2.2.2.2, he, sub_self]⟩
    · refine ⟨(sine_perturbed_circle_endpoint_derivative_values a b n).2.1, ?_⟩
      rw [(sine_perturbed_circle_endpoint_derivative_values a b n).2.2.2.2.1, he, ho.neg_one_pow]
      ring

theorem sine_perturbed_circle_threshold_origin_cusp_jets {a b : ℝ} {n : ℕ}
    (he : a = (n : ℝ) * b) :
    deriv (sinePerturbedCircleX a) 0 = 0 ∧ deriv (sinePerturbedCircleY a b n) 0 = 0 ∧
    deriv (deriv (sinePerturbedCircleX a)) 0 = -a ∧ deriv (deriv (sinePerturbedCircleY a b n)) 0 = 0 ∧
    deriv (deriv (deriv (sinePerturbedCircleX a))) 0 = 0 ∧
    deriv (deriv (deriv (sinePerturbedCircleY a b n))) 0 = a * ((n : ℝ) ^ 2 - 1) := by
  rw [(sine_perturbed_circle_actual_derivative_values a b 0 n).1,
    (sine_perturbed_circle_actual_derivative_values a b 0 n).2,
    (sine_perturbed_circle_actual_second_derivatives a b 0 n).1.deriv,
    (sine_perturbed_circle_actual_second_derivatives a b 0 n).2.deriv,
    (sine_perturbed_circle_actual_third_derivatives a b 0 n).1.deriv,
    (sine_perturbed_circle_actual_third_derivatives a b 0 n).2.deriv]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, mul_one, add_zero]
  rw [he]
  constructor
  · trivial
  · constructor
    · ring
    · constructor
      · trivial
      · constructor
        · trivial
        · constructor
          · trivial
          · ring

theorem sine_perturbed_circle_threshold_odd_midpoint_cusp_jets {a b : ℝ} {n : ℕ}
    (he : a = (n : ℝ) * b) (ho : Odd n) :
    deriv (sinePerturbedCircleX a) Real.pi = 0 ∧ deriv (sinePerturbedCircleY a b n) Real.pi = 0 ∧
    deriv (deriv (sinePerturbedCircleX a)) Real.pi = a ∧
    deriv (deriv (sinePerturbedCircleY a b n)) Real.pi = 0 ∧
    deriv (deriv (deriv (sinePerturbedCircleX a))) Real.pi = 0 ∧
    deriv (deriv (deriv (sinePerturbedCircleY a b n))) Real.pi = -a * ((n : ℝ) ^ 2 - 1) := by
  rw [(sine_perturbed_circle_actual_derivative_values a b Real.pi n).1,
    (sine_perturbed_circle_actual_derivative_values a b Real.pi n).2,
    (sine_perturbed_circle_actual_second_derivatives a b Real.pi n).1.deriv,
    (sine_perturbed_circle_actual_second_derivatives a b Real.pi n).2.deriv,
    (sine_perturbed_circle_actual_third_derivatives a b Real.pi n).1.deriv,
    (sine_perturbed_circle_actual_third_derivatives a b Real.pi n).2.deriv]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
    ho.neg_one_pow, mul_zero, add_zero, mul_neg, mul_one, neg_neg]
  rw [he]
  constructor
  · trivial
  · constructor
    · ring
    · constructor
      · trivial
      · constructor
        · trivial
        · constructor
          · trivial
          · ring

theorem sine_perturbed_circle_genuine_threshold_cusp_jet_independence {a b : ℝ} (ha : 0 < a)
    {n : ℕ} (hn : 1 < n) (he : a = (n : ℝ) * b) :
    deriv (deriv (sinePerturbedCircleX a)) 0 ≠ 0 ∧
    deriv (deriv (sinePerturbedCircleX a)) 0 * deriv (deriv (deriv (sinePerturbedCircleY a b n))) 0 -
      deriv (deriv (sinePerturbedCircleY a b n)) 0 * deriv (deriv (deriv (sinePerturbedCircleX a))) 0 < 0 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have h2 : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hj := sine_perturbed_circle_threshold_origin_cusp_jets he
  rw [hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2]
  refine ⟨neg_ne_zero.mpr ha.ne', ?_⟩
  simp only [zero_mul, sub_zero]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ha) (mul_pos ha h2)

theorem sine_perturbed_circle_genuine_odd_midpoint_cusp_jet_independence {a b : ℝ} (ha : 0 < a)
    {n : ℕ} (hn : 1 < n) (he : a = (n : ℝ) * b) (ho : Odd n) :
    deriv (deriv (sinePerturbedCircleX a)) Real.pi ≠ 0 ∧
    deriv (deriv (sinePerturbedCircleX a)) Real.pi * deriv (deriv (deriv (sinePerturbedCircleY a b n))) Real.pi -
      deriv (deriv (sinePerturbedCircleY a b n)) Real.pi * deriv (deriv (deriv (sinePerturbedCircleX a))) Real.pi < 0 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have h2 : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hj := sine_perturbed_circle_threshold_odd_midpoint_cusp_jets he ho
  rw [hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2]
  refine ⟨ha.ne', ?_⟩
  simp only [zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg ha (mul_neg_of_neg_of_pos (neg_lt_zero.mpr ha) h2)

theorem sine_perturbed_circle_sine_eventually_nonzero_at_zero {t₀ : ℝ} (hs : Real.sin t₀ = 0) :
    ∀ᶠ t : ℝ in 𝓝[≠] t₀, Real.sin t ≠ 0 := by
  have hI0 : ∀ᶠ t : ℝ in 𝓝 t₀, t ∈ Ioo (t₀ - Real.pi) (t₀ + Real.pi) :=
    Ioo_mem_nhds (sub_lt_self _ Real.pi_pos) (lt_add_of_pos_right _ Real.pi_pos)
  have hI : ∀ᶠ t : ℝ in 𝓝[≠] t₀, t ∈ Ioo (t₀ - Real.pi) (t₀ + Real.pi) :=
    hI0.filter_mono nhdsWithin_le_nhds
  filter_upwards [hI, self_mem_nhdsWithin] with t ht hne
  have hn : t ≠ t₀ := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  intro hzero
  have hd : Real.sin (t - t₀) = 0 := by rw [Real.sin_sub, hs, hzero]; ring
  have he := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [ht.1] : -Real.pi < t - t₀)
    (by linarith [ht.2] : t - t₀ < Real.pi)).mp hd
  exact hn (by linarith)

theorem sine_perturbed_circle_actual_singular_secant_tangent {a t₀ : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ)
    (hs : Real.sin t₀ = 0) (hns : Real.sin ((n : ℝ) * t₀) = 0)
    (hy : deriv (sinePerturbedCircleY a b n) t₀ = 0) :
    Tendsto (fun t : ℝ ↦ (sinePerturbedCircleY a b n t - sinePerturbedCircleY a b n t₀) /
      (sinePerturbedCircleX a t - sinePerturbedCircleX a t₀)) (𝓝[≠] t₀) (𝓝 0) := by
  have hc : Real.cos t₀ ≠ 0 := by nlinarith [Real.sin_sq_add_cos_sq t₀]
  have hx0 : deriv (sinePerturbedCircleX a) t₀ = 0 := by
    rw [(sine_perturbed_circle_actual_derivative_values a b t₀ n).1, hs, mul_zero]
  have hdx : Continuous (deriv (sinePerturbedCircleX a)) := by
    have he := funext (fun u ↦ (sine_perturbed_circle_actual_derivative_values a b u n).1)
    rw [he]
    exact Real.continuous_sin.const_mul (-a)
  have hdy : Continuous (deriv (sinePerturbedCircleY a b n)) := by
    have he := funext (fun u ↦ (sine_perturbed_circle_actual_derivative_values a b u n).2)
    rw [he]
    exact (Real.continuous_cos.const_mul a).sub
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul ((n : ℝ) * b))
  have hddx : ContinuousAt (fun t : ℝ ↦ -a * Real.cos t) t₀ :=
    (Real.continuous_cos.const_mul (-a)).continuousAt
  have hddy : ContinuousAt
      (fun t : ℝ ↦ -a * Real.sin t + (n : ℝ) ^ 2 * b * Real.sin ((n : ℝ) * t)) t₀ :=
    ((Real.continuous_sin.const_mul (-a)).add
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul
        ((n : ℝ) ^ 2 * b))).continuousAt
  have hddx0 : -a * Real.cos t₀ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ha.ne') hc
  have hratio : Tendsto (fun t : ℝ ↦
      (-a * Real.sin t + (n : ℝ) ^ 2 * b * Real.sin ((n : ℝ) * t)) / (-a * Real.cos t))
      (𝓝[≠] t₀) (𝓝 0) := by
    have h := (hddy.div hddx hddx0).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
    simpa only [Pi.div_apply, hs, hns, mul_zero, neg_zero, zero_add, zero_div] using! h
  have hfirst : Tendsto (fun t : ℝ ↦ deriv (sinePerturbedCircleY a b n) t / deriv (sinePerturbedCircleX a) t)
      (𝓝[≠] t₀) (𝓝 0) := by
    apply calculus.Chapter04.Section04.lhopital_zero_punctured
      (Eventually.of_forall (fun t ↦ (sine_perturbed_circle_actual_second_derivatives a b t n).2))
      (Eventually.of_forall (fun t ↦ (sine_perturbed_circle_actual_second_derivatives a b t n).1))
      ((hddx.tendsto.eventually_ne hddx0).filter_mono nhdsWithin_le_nhds)
    · simpa only [hy] using (hdy.continuousAt (x := t₀)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
    · simpa only [hx0] using (hdx.continuousAt (x := t₀)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
    · exact hratio
  apply calculus.Chapter04.Section04.lhopital_zero_punctured
    (Eventually.of_forall (fun t ↦ (sine_perturbed_circle_actual_coordinate_derivatives a b t n).2.sub_const _))
    (Eventually.of_forall (fun t ↦ (sine_perturbed_circle_actual_coordinate_derivatives a b t n).1.sub_const _))
  · filter_upwards [sine_perturbed_circle_sine_eventually_nonzero_at_zero hs] with t ht
    exact mul_ne_zero (neg_ne_zero.mpr ha.ne') ht
  · have hC : ContinuousAt (fun t : ℝ ↦ sinePerturbedCircleY a b n t - sinePerturbedCircleY a b n t₀) t₀ :=
      ((sine_perturbed_circle_continuous_compact a b n).2.1.continuousAt (x := t₀)).sub_const
        (sinePerturbedCircleY a b n t₀)
    have h : Tendsto (fun t : ℝ ↦ sinePerturbedCircleY a b n t - sinePerturbedCircleY a b n t₀)
        (𝓝 t₀) (𝓝 0) := by simpa only [sub_self] using hC.tendsto
    exact h.mono_left (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
  · have hC : ContinuousAt (fun t : ℝ ↦ sinePerturbedCircleX a t - sinePerturbedCircleX a t₀) t₀ :=
      ((sine_perturbed_circle_continuous_compact a b n).1.continuousAt (x := t₀)).sub_const
        (sinePerturbedCircleX a t₀)
    have h : Tendsto (fun t : ℝ ↦ sinePerturbedCircleX a t - sinePerturbedCircleX a t₀)
        (𝓝 t₀) (𝓝 0) := by simpa only [sub_self] using hC.tendsto
    exact h.mono_left (nhdsWithin_le_nhds : 𝓝[≠] t₀ ≤ 𝓝 t₀)
  · have he : (fun t ↦ (a * Real.cos t - (n : ℝ) * b * Real.cos ((n : ℝ) * t)) /
        (-a * Real.sin t)) = (fun t ↦ deriv (sinePerturbedCircleY a b n) t / deriv (sinePerturbedCircleX a) t) := by
      funext t
      rw [(sine_perturbed_circle_actual_derivative_values a b t n).1,
        (sine_perturbed_circle_actual_derivative_values a b t n).2]
    rw [he]
    exact hfirst

theorem sine_perturbed_circle_all_original_singular_tangent_directions {a : ℝ} (ha : 0 < a)
    (b : ℝ) (n : ℕ) {t₀ : ℝ} (ht₀ : t₀ ∈ sinePerturbedCircleDomain)
    (hzero : deriv (sinePerturbedCircleX a) t₀ = 0 ∧ deriv (sinePerturbedCircleY a b n) t₀ = 0) :
    sinePerturbedCircleY a b n t₀ = 0 ∧
    Tendsto (fun t : ℝ ↦ sinePerturbedCircleY a b n t / (sinePerturbedCircleX a t - sinePerturbedCircleX a t₀))
      (𝓝[≠] t₀) (𝓝 0) := by
  have hs : Real.sin t₀ = 0 := by
    have h := hzero.1
    rw [(sine_perturbed_circle_actual_derivative_values a b t₀ n).1] at h
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr ha.ne')
  have hns : Real.sin ((n : ℝ) * t₀) = 0 := by
    rcases (sine_perturbed_circle_sine_zero_on_original_interval ht₀).mp hs with rfl | rfl | rfl
    · simp only [mul_zero, Real.sin_zero]
    · exact Real.sin_nat_mul_pi n
    · simpa only [sub_zero, Real.sin_zero, neg_zero] using Real.sin_nat_mul_two_pi_sub (0 : ℝ) n
  have hy : sinePerturbedCircleY a b n t₀ = 0 := by
    unfold sinePerturbedCircleY
    rw [hs, hns, mul_zero, mul_zero, sub_self]
  refine ⟨hy, ?_⟩
  simpa only [hy, sub_zero] using sine_perturbed_circle_actual_singular_secant_tangent ha b n hs hns hzero.2

theorem sine_perturbed_circle_n_one_coordinates (a b t : ℝ) :
    sinePerturbedCircleY a b 1 t = (a - b) * Real.sin t := by
  unfold sinePerturbedCircleY
  norm_num
  ring

theorem sine_perturbed_circle_n_one_collapsed_segment {a : ℝ} (ha : 0 < a) :
    sinePerturbedCircleCurve a a 1 = {p | |p.1| ≤ a ∧ p.2 = 0} := by
  ext p
  constructor
  · rintro ⟨t, _, rfl⟩
    refine ⟨(sine_perturbed_circle_coordinate_bounds ha ha 1 t).1, ?_⟩
    change sinePerturbedCircleY a a 1 t = 0
    rw [sine_perturbed_circle_n_one_coordinates, sub_self, zero_mul]
  · rintro ⟨hx, hy⟩
    have hu : -1 ≤ p.1 / a ∧ p.1 / a ≤ 1 := by
      have h := abs_le.mp hx
      exact ⟨(le_div_iff₀ ha).mpr (by linarith [h.1]),
        (div_le_iff₀ ha).mpr (by linarith [h.2])⟩
    refine ⟨Real.arccos (p.1 / a), ⟨Real.arccos_nonneg _,
      by linarith [Real.arccos_le_pi (p.1 / a), Real.pi_pos]⟩, ?_⟩
    apply Prod.ext
    · change a * Real.cos (Real.arccos (p.1 / a)) = p.1
      rw [Real.cos_arccos hu.1 hu.2, mul_div_cancel₀ _ ha.ne']
    · change sinePerturbedCircleY a a 1 (Real.arccos (p.1 / a)) = p.2
      rw [sine_perturbed_circle_n_one_coordinates, sub_self, zero_mul, hy]

theorem sine_perturbed_circle_n_one_complete_ellipse {a b : ℝ} (ha : 0 < a) (hab : a ≠ b) :
    sinePerturbedCircleCurve a b 1 = {p | (p.1 / a) ^ 2 + (p.2 / (a - b)) ^ 2 = 1} := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  ext p
  constructor
  · rintro ⟨t, _, rfl⟩
    change ((a * Real.cos t) / a) ^ 2 + (sinePerturbedCircleY a b 1 t / (a - b)) ^ 2 = 1
    rw [sine_perturbed_circle_n_one_coordinates, mul_div_cancel_left₀ _ ha.ne', mul_div_cancel_left₀ _ hd]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · intro hp
    obtain ⟨t, ht, hc, hs⟩ := unit_circle_parameter hp
    refine ⟨t, ht, ?_⟩
    apply Prod.ext
    · change a * Real.cos t = p.1
      rw [hc, mul_div_cancel₀ _ ha.ne']
    · change sinePerturbedCircleY a b 1 t = p.2
      rw [sine_perturbed_circle_n_one_coordinates, hs, mul_div_cancel₀ _ hd]

theorem sine_perturbed_circle_n_one_regular_iff {a : ℝ} (ha : 0 < a) (b t : ℝ) :
    deriv (sinePerturbedCircleX a) t ≠ 0 ∨ deriv (sinePerturbedCircleY a b 1) t ≠ 0 ↔
      Real.sin t ≠ 0 ∨ a ≠ b := by
  rw [(sine_perturbed_circle_actual_derivative_values a b t 1).1,
    (sine_perturbed_circle_actual_derivative_values a b t 1).2]
  norm_num only [Nat.cast_one, one_mul]
  have hf : a * Real.cos t - b * Real.cos t = (a - b) * Real.cos t := by ring
  rw [hf]
  constructor
  · rintro (hx | hy)
    · exact Or.inl (fun hs ↦ hx (by rw [hs, mul_zero]))
    · exact Or.inr (fun he ↦ hy (by rw [he, sub_self, zero_mul]))
  · rintro (hs | hab)
    · exact Or.inl (mul_ne_zero (neg_ne_zero.mpr ha.ne') hs)
    · by_cases hs : Real.sin t = 0
      · have hc : Real.cos t ≠ 0 := by nlinarith [Real.sin_sq_add_cos_sq t]
        exact Or.inr (mul_ne_zero (sub_ne_zero.mpr hab) hc)
      · exact Or.inl (mul_ne_zero (neg_ne_zero.mpr ha.ne') hs)

theorem sine_perturbed_circle_n_one_signed_curvature_numerator (a b t : ℝ) :
    deriv (sinePerturbedCircleX a) t * deriv (deriv (sinePerturbedCircleY a b 1)) t -
      deriv (sinePerturbedCircleY a b 1) t * deriv (deriv (sinePerturbedCircleX a)) t = a * (a - b) := by
  rw [sine_perturbed_circle_signed_curvature_numerator]
  norm_num
  nlinarith [congrArg (fun z : ℝ ↦ a * b * z) (Real.sin_sq_add_cos_sq t)]

theorem sine_perturbed_circle_reflected_velocity (a b t : ℝ) (n : ℕ) :
    deriv (sinePerturbedCircleX a) (2 * Real.pi - t) = -deriv (sinePerturbedCircleX a) t ∧
    deriv (sinePerturbedCircleY a b n) (2 * Real.pi - t) = deriv (sinePerturbedCircleY a b n) t := by
  rw [(sine_perturbed_circle_actual_derivative_values a b (2 * Real.pi - t) n).1,
    (sine_perturbed_circle_actual_derivative_values a b (2 * Real.pi - t) n).2,
    (sine_perturbed_circle_actual_derivative_values a b t n).1,
    (sine_perturbed_circle_actual_derivative_values a b t n).2]
  have he : (n : ℝ) * (2 * Real.pi - t) = (n : ℝ) * (2 * Real.pi) - (n : ℝ) * t := by ring
  rw [Real.sin_two_pi_sub, Real.cos_two_pi_sub, he, Real.cos_nat_mul_two_pi_sub]
  constructor <;> ring

theorem sine_perturbed_circle_first_three_jets_periodic (a b t : ℝ) (n : ℕ) :
    deriv (sinePerturbedCircleX a) (t + 2 * Real.pi) = deriv (sinePerturbedCircleX a) t ∧
    deriv (sinePerturbedCircleY a b n) (t + 2 * Real.pi) = deriv (sinePerturbedCircleY a b n) t ∧
    deriv (deriv (sinePerturbedCircleX a)) (t + 2 * Real.pi) = deriv (deriv (sinePerturbedCircleX a)) t ∧
    deriv (deriv (sinePerturbedCircleY a b n)) (t + 2 * Real.pi) = deriv (deriv (sinePerturbedCircleY a b n)) t ∧
    deriv (deriv (deriv (sinePerturbedCircleX a))) (t + 2 * Real.pi) = deriv (deriv (deriv (sinePerturbedCircleX a))) t ∧
    deriv (deriv (deriv (sinePerturbedCircleY a b n))) (t + 2 * Real.pi) =
      deriv (deriv (deriv (sinePerturbedCircleY a b n))) t := by
  rw [(sine_perturbed_circle_actual_derivative_values a b (t + 2 * Real.pi) n).1,
    (sine_perturbed_circle_actual_derivative_values a b (t + 2 * Real.pi) n).2,
    (sine_perturbed_circle_actual_second_derivatives a b (t + 2 * Real.pi) n).1.deriv,
    (sine_perturbed_circle_actual_second_derivatives a b (t + 2 * Real.pi) n).2.deriv,
    (sine_perturbed_circle_actual_third_derivatives a b (t + 2 * Real.pi) n).1.deriv,
    (sine_perturbed_circle_actual_third_derivatives a b (t + 2 * Real.pi) n).2.deriv,
    (sine_perturbed_circle_actual_derivative_values a b t n).1,
    (sine_perturbed_circle_actual_derivative_values a b t n).2,
    (sine_perturbed_circle_actual_second_derivatives a b t n).1.deriv,
    (sine_perturbed_circle_actual_second_derivatives a b t n).2.deriv,
    (sine_perturbed_circle_actual_third_derivatives a b t n).1.deriv,
    (sine_perturbed_circle_actual_third_derivatives a b t n).2.deriv]
  have he : (n : ℝ) * (t + 2 * Real.pi) = (n : ℝ) * t + (n : ℝ) * (2 * Real.pi) := by ring
  simp only [he, Real.sin_add_two_pi, Real.cos_add_two_pi,
    Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi, and_self]

theorem sine_perturbed_circle_crossing_transversality {a : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    deriv (sinePerturbedCircleX a) t * deriv (sinePerturbedCircleY a b n) (2 * Real.pi - t) -
      deriv (sinePerturbedCircleY a b n) t * deriv (sinePerturbedCircleX a) (2 * Real.pi - t) ≠ 0 ↔
        sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) ≠ 0 := by
  rw [(sine_perturbed_circle_reflected_velocity a b t n).1, (sine_perturbed_circle_reflected_velocity a b t n).2,
    (sine_perturbed_circle_actual_derivative_values a b t n).1, sine_perturbed_circle_derivative_polynomial]
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have hf : -a * Real.sin t * sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) -
      sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) * -(-a * Real.sin t) =
      (-2 * a * Real.sin t) * sinePerturbedCircleHorizontalPolynomial a b n (Real.cos t) := by ring
  rw [hf]
  exact (mul_ne_zero_iff).trans (and_iff_right
    (mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') hs))

theorem source_sine_perturbed_circle_parametric_curve_investigation {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {n : ℕ} (hn : 0 < n) :
    sinePerturbedCircleCurve a b n = sinePerturbedCircleImplicit a b n ∧ IsCompact (sinePerturbedCircleCurve a b n) ∧
    (∀ t : ℝ, |sinePerturbedCircleX a t| ≤ a ∧ |sinePerturbedCircleY a b n t| ≤ a + b) ∧
    (∀ t ∈ sinePerturbedCircleDomain,
      deriv (sinePerturbedCircleX a) t = 0 ∧ deriv (sinePerturbedCircleY a b n) t = 0 ↔
        a = (n : ℝ) * b ∧ (t = 0 ∨ t = 2 * Real.pi ∨ (Odd n ∧ t = Real.pi))) :=
  ⟨sine_perturbed_circle_complete_implicit_image ha b n, (sine_perturbed_circle_continuous_compact a b n).2.2,
    sine_perturbed_circle_coordinate_bounds ha hb n,
    fun t ht ↦ sine_perturbed_circle_complete_singular_parameter_classification (t := t) ha hb hn ht⟩

end calculus.Chapter04.Section04SinePerturbedCircleParametricCurveInvestigation
