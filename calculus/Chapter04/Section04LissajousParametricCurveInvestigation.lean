import calculus.Chapter04.Section01Parametric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Field.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 15(g): họ Lissajous với bốn tham số thực

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2782, `x=A sin(at+π/2)`, `y=B sin(bt)`, `A,B,a,b∈ℝ`, `t∈ℝ`. Tham số có thể bằng 0; ảnh và bao đóng của ảnh có thể khác nhau.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04LissajousParametricCurveInvestigation
open calculus.Chapter04.Section01Parametric

def lissajousX (A a t : ℝ) : ℝ := A * Real.cos (a * t)
def lissajousY (B b t : ℝ) : ℝ := B * Real.sin (b * t)
def lissajousPoint (A B a b t : ℝ) : ℝ × ℝ :=
  (lissajousX A a t, lissajousY B b t)
def lissajousCurve (A B a b : ℝ) : Set (ℝ × ℝ) :=
  range (lissajousPoint A B a b)
def lissajousRectangle (A B : ℝ) : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ |A| ∧ |p.2| ≤ |B|}
def lissajousConstantX (A a : ℝ) : ℝ := if a = 0 then A else 0

def lissajousTangent (A B a b t : ℝ) : Set (ℝ × ℝ) :=
  {p | deriv (lissajousY B b) t * (p.1 - lissajousX A a t) =
    deriv (lissajousX A a) t * (p.2 - lissajousY B b t)}


def lissajousPhaseLocus (A B a b : ℝ) : Set (ℝ × ℝ) :=
  {p | |p.1 / A| ≤ 1 ∧ |p.2 / B| ≤ 1 ∧
    ∃ m n : ℤ, ∃ u v : ℝ,
      (u = Real.arccos (p.1 / A) ∨ u = -Real.arccos (p.1 / A)) ∧
      (v = Real.arcsin (p.2 / B) ∨ v = Real.pi - Real.arcsin (p.2 / B)) ∧
      b * (u + 2 * Real.pi * m) = a * (v + 2 * Real.pi * n)}

theorem lissajous_printed_coordinates (A B a b t : ℝ) :
    lissajousX A a t = A * Real.sin (a * t + Real.pi / 2) ∧
      lissajousY B b t = B * Real.sin (b * t) := by
  simp only [lissajousX, lissajousY, Real.sin_add_pi_div_two, and_self]

theorem lissajous_full_natural_domain (A B a b : ℝ) :
    lissajousCurve A B a b =
      parametricCurve (lissajousX A a) (lissajousY B b) univ := by
  unfold lissajousCurve parametricCurve
  rw [image_univ]
  rfl

theorem lissajous_actual_coordinate_derivatives (A B a b t : ℝ) :
    HasDerivAt (lissajousX A a) (-A * a * Real.sin (a * t)) t ∧
      HasDerivAt (lissajousY B b) (B * b * Real.cos (b * t)) t := by
  constructor
  · unfold lissajousX
    convert! (((hasDerivAt_id t).const_mul a).cos).const_mul A using 1
    simp only [id_eq]
    all_goals ring
  · unfold lissajousY
    convert! (((hasDerivAt_id t).const_mul b).sin).const_mul B using 1
    simp only [id_eq]
    all_goals ring

theorem lissajous_actual_derivative_values (A B a b t : ℝ) :
    deriv (lissajousX A a) t = -A * a * Real.sin (a * t) ∧
      deriv (lissajousY B b) t = B * b * Real.cos (b * t) :=
  ⟨(lissajous_actual_coordinate_derivatives A B a b t).1.deriv,
    (lissajous_actual_coordinate_derivatives A B a b t).2.deriv⟩

theorem lissajous_actual_second_derivatives (A B a b t : ℝ) :
    HasDerivAt (deriv (lissajousX A a)) (-A * a ^ 2 * Real.cos (a * t)) t ∧
      HasDerivAt (deriv (lissajousY B b)) (-B * b ^ 2 * Real.sin (b * t)) t := by
  have hx : deriv (lissajousX A a) = (fun u : ℝ ↦ -A * a * Real.sin (a * u)) :=
    funext (fun u ↦ (lissajous_actual_derivative_values A B a b u).1)
  have hy : deriv (lissajousY B b) = (fun u : ℝ ↦ B * b * Real.cos (b * u)) :=
    funext (fun u ↦ (lissajous_actual_derivative_values A B a b u).2)
  rw [hx, hy]
  constructor
  · convert! (((hasDerivAt_id t).const_mul a).sin).const_mul (-A * a) using 1
    simp only [id_eq]
    all_goals ring
  · convert! (((hasDerivAt_id t).const_mul b).cos).const_mul (B * b) using 1
    simp only [id_eq]
    all_goals ring

theorem lissajous_continuous (A B a b : ℝ) :
    Continuous (lissajousPoint A B a b) := by
  exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul A).prodMk
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul B)

theorem lissajous_bounded_rectangle (A B a b : ℝ) :
    lissajousCurve A B a b ⊆ lissajousRectangle A B := by
  rintro p ⟨t, rfl⟩
  change |A * Real.cos (a * t)| ≤ |A| ∧ |B * Real.sin (b * t)| ≤ |B|
  rw [abs_mul, abs_mul]
  exact ⟨by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (a * t)) (abs_nonneg A),
    by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (b * t)) (abs_nonneg B)⟩

theorem lissajous_horizontal_axis_reflection (A B a b t : ℝ) :
    lissajousPoint A B a b (-t) =
      (lissajousX A a t, -lissajousY B b t) := by
  simp only [lissajousPoint, lissajousX, lissajousY, mul_neg,
    Real.cos_neg, Real.sin_neg]

theorem lissajous_regular_parameter_iff (A B a b t : ℝ) :
    (deriv (lissajousX A a) t ≠ 0 ∨ deriv (lissajousY B b) t ≠ 0) ↔
      (A ≠ 0 ∧ a ≠ 0 ∧ Real.sin (a * t) ≠ 0) ∨
        (B ≠ 0 ∧ b ≠ 0 ∧ Real.cos (b * t) ≠ 0) := by
  rw [(lissajous_actual_derivative_values A B a b t).1,
    (lissajous_actual_derivative_values A B a b t).2]
  simp only [mul_ne_zero_iff, neg_ne_zero, and_assoc]

theorem lissajous_vertical_horizontal_tangent_criteria (A B a b t : ℝ) :
    ((deriv (lissajousX A a) t = 0 ∧ deriv (lissajousY B b) t ≠ 0) ↔
      (A = 0 ∨ a = 0 ∨ Real.sin (a * t) = 0) ∧
        B ≠ 0 ∧ b ≠ 0 ∧ Real.cos (b * t) ≠ 0) ∧
    ((deriv (lissajousY B b) t = 0 ∧ deriv (lissajousX A a) t ≠ 0) ↔
      (B = 0 ∨ b = 0 ∨ Real.cos (b * t) = 0) ∧
        A ≠ 0 ∧ a ≠ 0 ∧ Real.sin (a * t) ≠ 0) := by
  rw [(lissajous_actual_derivative_values A B a b t).1,
    (lissajous_actual_derivative_values A B a b t).2]
  simp only [mul_eq_zero, mul_ne_zero_iff, neg_eq_zero, neg_ne_zero, or_assoc, and_assoc]
  exact ⟨trivial, trivial⟩

theorem lissajous_regular_tangent_slope {A B a b t : ℝ}
    (hx : deriv (lissajousX A a) t ≠ 0) (p : ℝ × ℝ) :
    p ∈ lissajousTangent A B a b t ↔
      p.2 = lissajousY B b t +
        (deriv (lissajousY B b) t / deriv (lissajousX A a) t) *
          (p.1 - lissajousX A a t) := by
  change _ = _ ↔ _
  constructor
  · intro h
    have heq : (deriv (lissajousY B b) t * (p.1 - lissajousX A a t)) /
        deriv (lissajousX A a) t = p.2 - lissajousY B b t :=
      (div_eq_iff hx).mpr (h.trans (mul_comm _ _))
    have hquot : (deriv (lissajousY B b) t / deriv (lissajousX A a) t) *
        (p.1 - lissajousX A a t) = p.2 - lissajousY B b t := by
      rw [div_mul_eq_mul_div]; exact heq
    linarith [hquot]
  · intro h
    rw [h]
    field_simp [hx]
    all_goals ring

theorem lissajous_actual_vertical_tangent {A B a b t : ℝ}
    (hx : deriv (lissajousX A a) t = 0) (hy : deriv (lissajousY B b) t ≠ 0)
    (p : ℝ × ℝ) :
    p ∈ lissajousTangent A B a b t ↔ p.1 = lissajousX A a t := by
  change deriv (lissajousY B b) t * (p.1 - lissajousX A a t) =
    deriv (lissajousX A a) t * (p.2 - lissajousY B b t) ↔ _
  rw [hx, zero_mul, mul_eq_zero]
  simp only [hy, false_or, sub_eq_zero]

theorem lissajous_actual_horizontal_tangent {A B a b t : ℝ}
    (hy : deriv (lissajousY B b) t = 0) (hx : deriv (lissajousX A a) t ≠ 0)
    (p : ℝ × ℝ) :
    p ∈ lissajousTangent A B a b t ↔ p.2 = lissajousY B b t := by
  change deriv (lissajousY B b) t * (p.1 - lissajousX A a t) =
    deriv (lissajousX A a) t * (p.2 - lissajousY B b t) ↔ _
  rw [hy, zero_mul, eq_comm, mul_eq_zero]
  simp only [hx, false_or, sub_eq_zero]

theorem lissajous_signed_curvature_numerator (A B a b t : ℝ) :
    deriv (lissajousX A a) t * deriv (deriv (lissajousY B b)) t -
        deriv (lissajousY B b) t * deriv (deriv (lissajousX A a)) t =
      A * B * a * b * (b * Real.sin (a * t) * Real.sin (b * t) +
        a * Real.cos (a * t) * Real.cos (b * t)) := by
  rw [(lissajous_actual_derivative_values A B a b t).1,
    (lissajous_actual_derivative_values A B a b t).2,
    (lissajous_actual_second_derivatives A B a b t).1.deriv,
    (lissajous_actual_second_derivatives A B a b t).2.deriv]
  ring

theorem lissajous_strict_coordinate_branches (A B a b : ℝ) (I : Set ℝ)
    (hI : Convex ℝ I) :
    ((∀ t ∈ interior I, 0 < -A * a * Real.sin (a * t)) →
      StrictMonoOn (lissajousX A a) I) ∧
    ((∀ t ∈ interior I, -A * a * Real.sin (a * t) < 0) →
      StrictAntiOn (lissajousX A a) I) ∧
    ((∀ t ∈ interior I, 0 < B * b * Real.cos (b * t)) →
      StrictMonoOn (lissajousY B b) I) ∧
    ((∀ t ∈ interior I, B * b * Real.cos (b * t) < 0) →
      StrictAntiOn (lissajousY B b) I) := by
  have hX : Continuous (lissajousX A a) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul A
  have hY : Continuous (lissajousY B b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply strictMonoOn_of_deriv_pos hI hX.continuousOn
    intro t ht
    rw [(lissajous_actual_derivative_values A B a b t).1]
    exact h t ht
  · intro h
    apply strictAntiOn_of_deriv_neg hI hX.continuousOn
    intro t ht
    rw [(lissajous_actual_derivative_values A B a b t).1]
    exact h t ht
  · intro h
    apply strictMonoOn_of_deriv_pos hI hY.continuousOn
    intro t ht
    rw [(lissajous_actual_derivative_values A B a b t).2]
    exact h t ht
  · intro h
    apply strictAntiOn_of_deriv_neg hI hY.continuousOn
    intro t ht
    rw [(lissajous_actual_derivative_values A B a b t).2]
    exact h t ht


theorem lissajous_same_point_iff {A B a b s t : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) :
    lissajousPoint A B a b s = lissajousPoint A B a b t ↔
      (∃ m : ℤ, a * t = 2 * m * Real.pi + a * s ∨
        a * t = 2 * m * Real.pi - a * s) ∧
      (∃ n : ℤ, b * t = 2 * n * Real.pi + b * s ∨
        b * t = (2 * n + 1) * Real.pi - b * s) := by
  simp only [lissajousPoint, Prod.mk.injEq]
  change (A * Real.cos (a * s) = A * Real.cos (a * t) ∧
    B * Real.sin (b * s) = B * Real.sin (b * t)) ↔ _
  rw [mul_right_inj' hA, mul_right_inj' hB,
    Real.cos_eq_cos_iff, Real.sin_eq_sin_iff]


theorem lissajous_period_iff (A B a b T : ℝ) :
    Function.Periodic (lissajousPoint A B a b) T ↔
      (A = 0 ∨ ∃ m : ℤ, a * T = 2 * Real.pi * m) ∧
      (B = 0 ∨ ∃ n : ℤ, b * T = 2 * Real.pi * n) := by
  constructor
  · intro hp
    constructor
    · by_cases hA : A = 0
      · exact Or.inl hA
      · right
        have h := congrArg Prod.fst (hp 0)
        change A * Real.cos (a * (0 + T)) = A * Real.cos (a * 0) at h
        simp only [zero_add, mul_zero, Real.cos_zero, mul_one] at h
        have hc : Real.cos (a * T) = 1 := (mul_left_cancel₀ hA (h.trans (mul_one A).symm))
        obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff (a * T)).mp hc
        exact ⟨m, by linarith⟩
    · by_cases hB : B = 0
      · exact Or.inl hB
      · right
        by_cases hb : b = 0
        · exact ⟨0, by simp only [hb, zero_mul, Int.cast_zero, mul_zero]⟩
        · have h := congrArg Prod.snd (hp (Real.pi / (2 * b)))
          change B * Real.sin (b * (Real.pi / (2 * b) + T)) =
            B * Real.sin (b * (Real.pi / (2 * b))) at h
          have hbθ : b * (Real.pi / (2 * b)) = Real.pi / 2 := by
            field_simp [hb]
          have hbθT : b * (Real.pi / (2 * b) + T) = b * T + Real.pi / 2 := by
            rw [mul_add, hbθ]; ring
          rw [hbθT, hbθ, Real.sin_add_pi_div_two, Real.sin_pi_div_two, mul_one] at h
          have hc : Real.cos (b * T) = 1 := (mul_left_cancel₀ hB (h.trans (mul_one B).symm))
          obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (b * T)).mp hc
          exact ⟨n, by linarith⟩
  · rintro ⟨hX, hY⟩ t
    apply Prod.ext
    · change A * Real.cos (a * (t + T)) = A * Real.cos (a * t)
      rcases hX with rfl | ⟨m, hm⟩
      · simp only [zero_mul]
      · rw [mul_add, hm, show 2 * Real.pi * (m : ℝ) = m * (2 * Real.pi) by ring,
          Real.cos_add_int_mul_two_pi]
    · change B * Real.sin (b * (t + T)) = B * Real.sin (b * t)
      rcases hY with rfl | ⟨n, hn⟩
      · simp only [zero_mul]
      · rw [mul_add, hn, show 2 * Real.pi * (n : ℝ) = n * (2 * Real.pi) by ring,
          Real.sin_add_int_mul_two_pi]

theorem lissajous_rational_ratio_has_nonzero_period {a : ℝ} (ha : a ≠ 0)
    (A B b : ℝ) (q : ℚ) (hq : b / a = q) :
    ∃ T : ℝ, T ≠ 0 ∧ Function.Periodic (lissajousPoint A B a b) T := by
  let T : ℝ := 2 * Real.pi * q.den / a
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hT : T ≠ 0 := div_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) hden) ha
  have hq' : b / a = (q.num : ℝ) / q.den := hq.trans (Rat.cast_def q)
  have haT : a * T = 2 * Real.pi * (q.den : ℝ) := by
    dsimp [T]; field_simp [ha]
  have hbT : b * T = 2 * Real.pi * (q.num : ℝ) := by
    calc
      b * T = 2 * Real.pi * ((b / a) * q.den) := by dsimp [T]; ring
      _ = 2 * Real.pi * (q.num : ℝ) := by rw [hq']; field_simp [hden]
  refine ⟨T, hT, (lissajous_period_iff A B a b T).mpr ?_⟩
  exact ⟨Or.inr ⟨q.den, by simpa only [Int.cast_natCast] using haT⟩,
    Or.inr ⟨q.num, hbT⟩⟩

theorem lissajous_irrational_ratio_aperiodic {A B a b T : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (hT : T ≠ 0)
    (hirr : Irrational (b / a)) :
    ¬ Function.Periodic (lissajousPoint A B a b) T := by
  intro hp
  obtain ⟨m, hm⟩ := ((lissajous_period_iff A B a b T).mp hp).1.resolve_left hA
  obtain ⟨n, hn⟩ := ((lissajous_period_iff A B a b T).mp hp).2.resolve_left hB
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    exact (mul_ne_zero ha hT) hm
  have hrel : b * (m : ℝ) = a * (n : ℝ) := by
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    calc
      (2 * Real.pi) * (b * m) = b * (2 * Real.pi * m) := by ring
      _ = b * (a * T) := by rw [← hm]
      _ = a * (b * T) := by ring
      _ = a * (2 * Real.pi * n) := by rw [hn]
      _ = (2 * Real.pi) * (a * n) := by ring
  exact hirr.ne_rational n m ((div_eq_div_iff ha hm0).mpr (hrel.trans (mul_comm _ _)))

theorem lissajous_periodic_whole_image_compact {A B a b T : ℝ}
    (hT : T ≠ 0) (hp : Function.Periodic (lissajousPoint A B a b) T) :
    lissajousCurve A B a b = lissajousPoint A B a b '' uIcc 0 T ∧
      IsCompact (lissajousCurve A B a b) := by
  have heq := hp.image_uIcc hT (0 : ℝ)
  simp only [zero_add] at heq
  refine ⟨heq.symm, ?_⟩
  rw [show lissajousCurve A B a b = lissajousPoint A B a b '' uIcc 0 T from heq.symm]
  exact isCompact_uIcc.image (lissajous_continuous A B a b)


theorem lissajous_exact_phase_image {A B a b : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) :
    lissajousCurve A B a b = lissajousPhaseLocus A B a b := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    have hx : lissajousX A a t / A = Real.cos (a * t) := by
      unfold lissajousX; exact mul_div_cancel_left₀ _ hA
    have hy : lissajousY B b t / B = Real.sin (b * t) := by
      unfold lissajousY; exact mul_div_cancel_left₀ _ hB
    change |lissajousX A a t / A| ≤ 1 ∧ |lissajousY B b t / B| ≤ 1 ∧ _
    dsimp only [lissajousPoint]
    rw [hx, hy]
    refine ⟨Real.abs_cos_le_one _, Real.abs_sin_le_one _, ?_⟩
    have hc : Real.cos (Real.arccos (Real.cos (a * t))) = Real.cos (a * t) :=
      Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)
    have hs : Real.sin (Real.arcsin (Real.sin (b * t))) = Real.sin (b * t) :=
      Real.sin_arcsin (Real.neg_one_le_sin _) (Real.sin_le_one _)
    obtain ⟨m, hm | hm⟩ := Real.cos_eq_cos_iff.mp hc
    · obtain ⟨n, hn | hn⟩ := Real.sin_eq_sin_iff.mp hs
      · refine ⟨m, n, Real.arccos (Real.cos (a * t)), Real.arcsin (Real.sin (b * t)),
          Or.inl rfl, Or.inl rfl, ?_⟩
        nlinarith [congrArg (fun x : ℝ ↦ b * x) hm, congrArg (fun x : ℝ ↦ a * x) hn]
      · refine ⟨m, n, Real.arccos (Real.cos (a * t)), Real.pi - Real.arcsin (Real.sin (b * t)),
          Or.inl rfl, Or.inr rfl, ?_⟩
        nlinarith [congrArg (fun x : ℝ ↦ b * x) hm, congrArg (fun x : ℝ ↦ a * x) hn]
    · obtain ⟨n, hn | hn⟩ := Real.sin_eq_sin_iff.mp hs
      · refine ⟨m, n, -Real.arccos (Real.cos (a * t)), Real.arcsin (Real.sin (b * t)),
          Or.inr rfl, Or.inl rfl, ?_⟩
        nlinarith [congrArg (fun x : ℝ ↦ b * x) hm, congrArg (fun x : ℝ ↦ a * x) hn]
      · refine ⟨m, n, -Real.arccos (Real.cos (a * t)), Real.pi - Real.arcsin (Real.sin (b * t)),
          Or.inr rfl, Or.inr rfl, ?_⟩
        nlinarith [congrArg (fun x : ℝ ↦ b * x) hm, congrArg (fun x : ℝ ↦ a * x) hn]
  · rintro ⟨hx, hy, m, n, u, v, hu, hv, hrel⟩
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    let t : ℝ := (u + 2 * Real.pi * m) / a
    have hat : a * t = u + 2 * Real.pi * m := by dsimp [t]; field_simp [ha]
    have hbt : b * t = v + 2 * Real.pi * n := by
      calc
        b * t = (b * (u + 2 * Real.pi * m)) / a := by dsimp [t]; ring
        _ = (a * (v + 2 * Real.pi * n)) / a := by rw [hrel]
        _ = v + 2 * Real.pi * n := mul_div_cancel_left₀ _ ha
    have hcos : Real.cos u = p.1 / A := by
      rcases hu with rfl | rfl
      · exact Real.cos_arccos hx'.1 hx'.2
      · rw [Real.cos_neg]; exact Real.cos_arccos hx'.1 hx'.2
    have hsin : Real.sin v = p.2 / B := by
      rcases hv with rfl | rfl
      · exact Real.sin_arcsin hy'.1 hy'.2
      · rw [Real.sin_pi_sub]; exact Real.sin_arcsin hy'.1 hy'.2
    refine ⟨t, ?_⟩
    apply Prod.ext
    · change A * Real.cos (a * t) = p.1
      rw [hat, show u + 2 * Real.pi * (m : ℝ) = u + m * (2 * Real.pi) by ring,
        Real.cos_add_int_mul_two_pi, hcos, mul_div_cancel₀ _ hA]
    · change B * Real.sin (b * t) = p.2
      rw [hbt, show v + 2 * Real.pi * (n : ℝ) = v + n * (2 * Real.pi) by ring,
        Real.sin_add_int_mul_two_pi, hsin, mul_div_cancel₀ _ hB]

theorem lissajous_inactive_x_constant {A a : ℝ} (h : A = 0 ∨ a = 0) (t : ℝ) :
    lissajousX A a t = lissajousConstantX A a := by
  rcases h with rfl | rfl
  · simp only [lissajousX, lissajousConstantX, zero_mul]
    split_ifs <;> rfl
  · simp only [lissajousX, lissajousConstantX, zero_mul, Real.cos_zero, mul_one, if_true]

theorem lissajous_inactive_y_zero {B b : ℝ} (h : B = 0 ∨ b = 0) (t : ℝ) :
    lissajousY B b t = 0 := by
  rcases h with rfl | rfl <;> simp only [lissajousY, zero_mul, Real.sin_zero, mul_zero]

theorem lissajous_both_inactive_point {A B a b : ℝ}
    (hX : A = 0 ∨ a = 0) (hY : B = 0 ∨ b = 0) :
    lissajousCurve A B a b = {(lissajousConstantX A a, 0)} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    simp only [lissajousPoint, lissajous_inactive_x_constant hX,
      lissajous_inactive_y_zero hY, mem_singleton_iff]
  · intro h
    rw [mem_singleton_iff] at h
    refine ⟨0, ?_⟩
    rw [h]
    simp only [lissajousPoint, lissajous_inactive_x_constant hX, lissajous_inactive_y_zero hY]

theorem lissajous_inactive_x_vertical_segment {A B a b : ℝ}
    (hX : A = 0 ∨ a = 0) (hB : B ≠ 0) (hb : b ≠ 0) :
    lissajousCurve A B a b =
      {p | p.1 = lissajousConstantX A a ∧ |p.2| ≤ |B|} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨lissajous_inactive_x_constant hX t,
      (lissajous_bounded_rectangle A B a b ⟨t, rfl⟩).2⟩
  · rintro ⟨hx, hy⟩
    have hy' : |p.2 / B| ≤ 1 := by
      rw [abs_div]; exact (div_le_one₀ (abs_pos.mpr hB)).mpr hy
    have hy'' := abs_le.mp hy'
    let t : ℝ := Real.arcsin (p.2 / B) / b
    have hbt : b * t = Real.arcsin (p.2 / B) := by dsimp [t]; field_simp [hb]
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact (lissajous_inactive_x_constant hX t).trans hx.symm
    · change B * Real.sin (b * t) = p.2
      rw [hbt, Real.sin_arcsin hy''.1 hy''.2, mul_div_cancel₀ _ hB]

theorem lissajous_inactive_y_horizontal_segment {A B a b : ℝ}
    (hY : B = 0 ∨ b = 0) (hA : A ≠ 0) (ha : a ≠ 0) :
    lissajousCurve A B a b = {p | |p.1| ≤ |A| ∧ p.2 = 0} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(lissajous_bounded_rectangle A B a b ⟨t, rfl⟩).1,
      lissajous_inactive_y_zero hY t⟩
  · rintro ⟨hx, hy⟩
    have hx' : |p.1 / A| ≤ 1 := by
      rw [abs_div]; exact (div_le_one₀ (abs_pos.mpr hA)).mpr hx
    have hx'' := abs_le.mp hx'
    let t : ℝ := Real.arccos (p.1 / A) / a
    have hat : a * t = Real.arccos (p.1 / A) := by dsimp [t]; field_simp [ha]
    refine ⟨t, ?_⟩
    apply Prod.ext
    · change A * Real.cos (a * t) = p.1
      rw [hat, Real.cos_arccos hx''.1 hx''.2, mul_div_cancel₀ _ hA]
    · exact (lissajous_inactive_y_zero hY t).trans hy.symm


theorem lissajous_irrational_rectangle_closure {A B a b : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (hirr : Irrational (b / a)) :
    closure (lissajousCurve A B a b) = lissajousRectangle A B := by
  apply Subset.antisymm
  · apply closure_minimal (lissajous_bounded_rectangle A B a b)
    exact (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).inter
      (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)
  · intro p hp
    change |p.1| ≤ |A| ∧ |p.2| ≤ |B| at hp
    have hx : |p.1 / A| ≤ 1 := by
      rw [abs_div]; exact (div_le_one₀ (abs_pos.mpr hA)).mpr hp.1
    have hy : |p.2 / B| ≤ 1 := by
      rw [abs_div]; exact (div_le_one₀ (abs_pos.mpr hB)).mpr hp.2
    let θ : ℝ := Real.arccos (p.1 / A)
    let ψ : ℝ := Real.arcsin (p.2 / B)
    let δ : ℝ := 2 * Real.pi * (b / a)
    let u : ℝ := (b / a) * θ
    let η : Real.Angle := ((ψ - u : ℝ) : Real.Angle)
    let F : Real.Angle → ℝ × ℝ := fun z ↦ (p.1, B * Real.Angle.sin (z + (u : Real.Angle)))
    have hδ : δ / (2 * Real.pi) = b / a := by
      dsimp [δ]; field_simp [Real.pi_ne_zero]
    have hdense : DenseRange (fun n : ℤ ↦ n • (δ : Real.Angle)) :=
      (AddCircle.denseRange_zsmul_coe_iff (a := δ) (p := 2 * Real.pi)).mpr
        (by rw [hδ]; exact hirr)
    have hF : Continuous F := by
      exact continuous_const.prodMk
        ((Real.Angle.continuous_sin.comp (continuous_id.add continuous_const)).const_mul B)
    have htarget : F η = p := by
      apply Prod.ext
      · rfl
      · change B * Real.Angle.sin (((ψ - u : ℝ) : Real.Angle) + (u : Real.Angle)) = p.2
        rw [← Real.Angle.coe_add, sub_add_cancel, Real.Angle.sin_coe]
        dsimp [ψ]
        rw [Real.sin_arcsin (abs_le.mp hy).1 (abs_le.mp hy).2, mul_div_cancel₀ _ hB]
    have hsub : F '' range (fun n : ℤ ↦ n • (δ : Real.Angle)) ⊆ lissajousCurve A B a b := by
      rintro q ⟨z, ⟨n, rfl⟩, rfl⟩
      let t : ℝ := (θ + 2 * Real.pi * n) / a
      have hat : a * t = θ + 2 * Real.pi * n := by dsimp [t]; field_simp [ha]
      refine ⟨t, ?_⟩
      apply Prod.ext
      · change A * Real.cos (a * t) = p.1
        rw [hat, show θ + 2 * Real.pi * (n : ℝ) = θ + n * (2 * Real.pi) by ring,
          Real.cos_add_int_mul_two_pi]
        dsimp [θ]
        rw [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2, mul_div_cancel₀ _ hA]
      · change B * Real.sin (b * t) =
          B * Real.Angle.sin (n • (δ : Real.Angle) + (u : Real.Angle))
        rw [← Real.Angle.coe_zsmul, ← Real.Angle.coe_add, Real.Angle.sin_coe, zsmul_eq_mul]
        congr 1
        congr 1
        dsimp [t, δ, u]
        ring
    rw [← htarget]
    exact closure_mono hsub (mem_closure_image hF.continuousAt (hdense η))

theorem lissajous_active_period_exists_iff_rational {A B a b : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) :
    (∃ T : ℝ, T ≠ 0 ∧ Function.Periodic (lissajousPoint A B a b) T) ↔
      ¬ Irrational (b / a) := by
  constructor
  · rintro ⟨T, hT, hp⟩ hirr
    exact lissajous_irrational_ratio_aperiodic hA hB ha hT hirr hp
  · intro hr
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hr
    exact lissajous_rational_ratio_has_nonzero_period ha A B b q hq


theorem lissajous_equal_absolute_frequency_ellipse {A B a b : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (hb : b = a ∨ b = -a) :
    lissajousCurve A B a b = {p | (p.1 / A) ^ 2 + (p.2 / B) ^ 2 = 1} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    change (A * Real.cos (a * t) / A) ^ 2 + (B * Real.sin (b * t) / B) ^ 2 = 1
    rw [mul_div_cancel_left₀ _ hA, mul_div_cancel_left₀ _ hB]
    rcases hb with hb | hb
    · rw [hb]
      nlinarith [Real.sin_sq_add_cos_sq (a * t)]
    · rw [hb, neg_mul, Real.sin_neg, neg_sq]
      nlinarith [Real.sin_sq_add_cos_sq (a * t)]
  · intro hp
    change (p.1 / A) ^ 2 + (p.2 / B) ^ 2 = 1 at hp
    rcases hb with hb | hb
    · rw [hb]
      obtain ⟨θ, _, hc, hs⟩ := unit_circle_parameter hp
      refine ⟨θ / a, ?_⟩
      have hat : a * (θ / a) = θ := mul_div_cancel₀ θ ha
      apply Prod.ext
      · change A * Real.cos (a * (θ / a)) = p.1
        rw [hat, hc, mul_div_cancel₀ _ hA]
      · change B * Real.sin (a * (θ / a)) = p.2
        rw [hat, hs, mul_div_cancel₀ _ hB]
    · rw [hb]
      have hp' : (p.1 / A) ^ 2 + (-(p.2 / B)) ^ 2 = 1 := by rw [neg_sq]; exact hp
      obtain ⟨θ, _, hc, hs⟩ := unit_circle_parameter hp'
      refine ⟨θ / a, ?_⟩
      have hat : a * (θ / a) = θ := mul_div_cancel₀ θ ha
      apply Prod.ext
      · change A * Real.cos (a * (θ / a)) = p.1
        rw [hat, hc, mul_div_cancel₀ _ hA]
      · change B * Real.sin ((-a) * (θ / a)) = p.2
        rw [neg_mul, hat, Real.sin_neg, hs, neg_neg, mul_div_cancel₀ _ hB]


theorem lissajous_irrational_corner_missing {A B a b : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (hirr : Irrational (b / a)) :
    (A, B) ∉ lissajousCurve A B a b := by
  rintro ⟨t, ht⟩
  have hx := congrArg Prod.fst ht
  have hy := congrArg Prod.snd ht
  change A * Real.cos (a * t) = A at hx
  change B * Real.sin (b * t) = B at hy
  have hc : Real.cos (a * t) = 1 := mul_left_cancel₀ hA (hx.trans (mul_one A).symm)
  have hs : Real.sin (b * t) = 1 := mul_left_cancel₀ hB (hy.trans (mul_one B).symm)
  have ht0 : t ≠ 0 := by intro h; rw [h, mul_zero, Real.sin_zero] at hs; norm_num at hs
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff (a * t)).mp hc
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hm
    exact (mul_ne_zero ha ht0) hm.symm
  have hc' : Real.cos (b * t - Real.pi / 2) = 1 := by
    rw [Real.cos_sub_pi_div_two]; exact hs
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (b * t - Real.pi / 2)).mp hc'
  have hbt : b * t = 2 * Real.pi * n + Real.pi / 2 := by linarith [hn]
  have hrel : b * (4 * (m : ℝ)) = a * (4 * (n : ℝ) + 1) := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    calc
      Real.pi * (b * (4 * m)) = 2 * b * (m * (2 * Real.pi)) := by ring
      _ = 2 * b * (a * t) := by rw [hm]
      _ = 2 * a * (b * t) := by ring
      _ = 2 * a * (2 * Real.pi * n + Real.pi / 2) := by rw [hbt]
      _ = Real.pi * (a * (4 * n + 1)) := by ring
  have hrat : b / a = (((4 * n + 1 : ℤ) : ℝ) / ((4 * m : ℤ) : ℝ)) := by
    push_cast
    exact (div_eq_div_iff ha (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hm0)).mpr
      (hrel.trans (mul_comm _ _))
  exact hirr.ne_rational (4 * n + 1) (4 * m) hrat

theorem lissajous_irrational_image_proper_dense {A B a b : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (hirr : Irrational (b / a)) :
    closure (lissajousCurve A B a b) = lissajousRectangle A B ∧
      lissajousCurve A B a b ≠ lissajousRectangle A B := by
  refine ⟨lissajous_irrational_rectangle_closure hA hB ha hirr, ?_⟩
  intro heq
  apply lissajous_irrational_corner_missing hA hB ha hirr
  rw [heq]
  exact ⟨le_rfl, le_rfl⟩


theorem source_lissajous_parametric_curve_investigation (A B a b : ℝ) :
    (∀ t : ℝ, lissajousX A a t = A * Real.sin (a * t + Real.pi / 2) ∧
      lissajousY B b t = B * Real.sin (b * t)) ∧
    (lissajousCurve A B a b ⊆ lissajousRectangle A B) ∧
    (∀ t : ℝ, HasDerivAt (lissajousX A a) (-A * a * Real.sin (a * t)) t ∧
      HasDerivAt (lissajousY B b) (B * b * Real.cos (b * t)) t) ∧
    (∀ T : ℝ, Function.Periodic (lissajousPoint A B a b) T ↔
      (A = 0 ∨ ∃ m : ℤ, a * T = 2 * Real.pi * m) ∧
      (B = 0 ∨ ∃ n : ℤ, b * T = 2 * Real.pi * n)) ∧
    ((A = 0 ∨ a = 0) → (B = 0 ∨ b = 0) →
      lissajousCurve A B a b = {(lissajousConstantX A a, 0)}) ∧
    ((A = 0 ∨ a = 0) → B ≠ 0 → b ≠ 0 →
      lissajousCurve A B a b = {p | p.1 = lissajousConstantX A a ∧ |p.2| ≤ |B|}) ∧
    ((B = 0 ∨ b = 0) → A ≠ 0 → a ≠ 0 →
      lissajousCurve A B a b = {p | |p.1| ≤ |A| ∧ p.2 = 0}) ∧
    (A ≠ 0 → B ≠ 0 → a ≠ 0 →
      lissajousCurve A B a b = lissajousPhaseLocus A B a b) ∧
    (A ≠ 0 → B ≠ 0 → a ≠ 0 → Irrational (b / a) →
      closure (lissajousCurve A B a b) = lissajousRectangle A B) := by
  exact ⟨lissajous_printed_coordinates A B a b, lissajous_bounded_rectangle A B a b,
    lissajous_actual_coordinate_derivatives A B a b, lissajous_period_iff A B a b,
    lissajous_both_inactive_point, lissajous_inactive_x_vertical_segment,
    lissajous_inactive_y_horizontal_segment, lissajous_exact_phase_image,
    lissajous_irrational_rectangle_closure⟩

end calculus.Chapter04.Section04LissajousParametricCurveInvestigation
