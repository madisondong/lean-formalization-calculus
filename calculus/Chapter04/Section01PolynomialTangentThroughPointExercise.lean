import calculus.Chapter04.Section01PolynomialTangentExercise
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bài 4.1.7(b): tiếp tuyến đi qua (1,2)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 485 và dòng 488.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology

namespace calculus.Chapter04.Section01PolynomialTangentThroughPointExercise

open calculus.Chapter04.Section01PolynomialTangentExercise
open calculus.Chapter04.Section01Derivatives
open calculus.Chapter04.Section01Geometry

/-- Phương trình hoành độ tiếp điểm suy ra từ điều kiện đi qua (1,2). -/
def contactPolynomial (t : ℝ) : ℝ := 4 * t ^ 5 - 5 * t ^ 4 + 3


theorem contactPolynomial_hasDerivAt (t : ℝ) :
    HasDerivAt contactPolynomial (20 * t ^ 3 * (t - 1)) t := by
  change HasDerivAt (fun u : ℝ ↦ 4 * u ^ 5 - 5 * u ^ 4 + 3)
    (20 * t ^ 3 * (t - 1)) t
  have h : HasDerivAt (fun u : ℝ ↦ 4 * u ^ 5 - 5 * u ^ 4 + 3)
      (4 * (5 * t ^ 4) - 5 * (4 * t ^ 3)) t := by
    simpa only [Pi.sub_def, Nat.cast_ofNat, Nat.reduceSub] using
      (((hasDerivAt_pow 5 t).const_mul 4).sub
        ((hasDerivAt_pow 4 t).const_mul 5)).add_const 3
  exact h.congr_deriv (by ring)


theorem contactPolynomial_continuous : Continuous contactPolynomial :=
  (show Differentiable ℝ contactPolynomial from
    fun t ↦ (contactPolynomial_hasDerivAt t).differentiableAt).continuous

theorem contactPolynomial_at_minus_one : contactPolynomial (-1) = -6 := by
  norm_num [contactPolynomial]

theorem contactPolynomial_at_zero : contactPolynomial 0 = 3 := by
  norm_num [contactPolynomial]


theorem contactPolynomial_factorization (t : ℝ) :
    contactPolynomial t =
      2 + (t - 1) ^ 2 * (4 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1) := by
  unfold contactPolynomial
  ring

theorem contactPolynomial_pos_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 < contactPolynomial t := by
  have hp : 0 ≤ 4 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1 := by positivity
  have hs := mul_nonneg (sq_nonneg (t - 1)) hp
  rw [contactPolynomial_factorization]
  linarith


theorem contactPolynomial_deriv_pos_of_neg {t : ℝ} (ht : t < 0) :
    0 < deriv contactPolynomial t := by
  rw [(contactPolynomial_hasDerivAt t).deriv]
  have hc : t ^ 3 < 0 := by
    rw [show t ^ 3 = t ^ 2 * t by ring]
    exact mul_neg_of_pos_of_neg (sq_pos_of_neg ht) ht
  have hm : t - 1 < 0 := by linarith
  simpa only [mul_assoc] using
    mul_pos (by norm_num : (0 : ℝ) < 20) (mul_pos_of_neg_of_neg hc hm)


theorem contactPolynomial_strictMonoOn : StrictMonoOn contactPolynomial (Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic (0 : ℝ))
    contactPolynomial_continuous.continuousOn
  intro t ht
  have ht0 : t < 0 := by simpa only [interior_Iic, mem_Iio] using ht
  exact contactPolynomial_deriv_pos_of_neg ht0


theorem contactPolynomial_root_negative {t : ℝ} (ht : contactPolynomial t = 0) :
    t < 0 := by
  by_contra hn
  have hp := contactPolynomial_pos_of_nonneg (le_of_not_gt hn)
  rw [ht] at hp
  exact (lt_irrefl (0 : ℝ)) hp


theorem contactPolynomial_exists_root :
    ∃ t ∈ Ioo (-1 : ℝ) 0, contactPolynomial t = 0 := by
  have hv : (0 : ℝ) ∈ Icc (contactPolynomial (-1)) (contactPolynomial 0) := by
    rw [contactPolynomial_at_minus_one, contactPolynomial_at_zero]
    norm_num
  obtain ⟨t, ht, hq⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 0)
    contactPolynomial_continuous.continuousOn hv
  have hne : t ≠ (-1 : ℝ) := by
    intro h
    rw [h, contactPolynomial_at_minus_one] at hq
    norm_num at hq
  have hleft : (-1 : ℝ) < t := by
    rcases lt_or_eq_of_le ht.1 with h | h
    · exact h
    · exact False.elim (hne h.symm)
  exact ⟨t, ⟨hleft, contactPolynomial_root_negative hq⟩, hq⟩


theorem contactPolynomial_existsUnique_root : ∃! t : ℝ, contactPolynomial t = 0 := by
  obtain ⟨t, ht, hq⟩ := contactPolynomial_exists_root
  refine ⟨t, hq, ?_⟩
  intro u hu
  exact contactPolynomial_strictMonoOn.injOn
    (contactPolynomial_root_negative hu).le ht.2.le (hu.trans hq.symm)


theorem tangent_through_point_iff (t : ℝ) :
    tangentLine quinticPolynomial t (deriv quinticPolynomial t) 1 = 2 ↔
      contactPolynomial t = 0 := by
  have hid : tangentLine quinticPolynomial t (deriv quinticPolynomial t) 1 - 2 =
      -contactPolynomial t := by
    rw [(quinticPolynomial_hasDerivAt t).deriv]
    simp only [tangentLine, quinticPolynomial, contactPolynomial]
    ring
  constructor
  · intro h
    rw [h] at hid
    linarith
  · intro h
    rw [h] at hid
    linarith


theorem tangent_through_point_equation {t : ℝ} (ht : contactPolynomial t = 0) :
    ∀ x : ℝ, tangentLine quinticPolynomial t (deriv quinticPolynomial t) x =
      2 + (5 * t ^ 4 - 2) * (x - 1) := by
  intro x
  have hline : tangentLine quinticPolynomial t (deriv quinticPolynomial t) x =
      tangentLine quinticPolynomial t (deriv quinticPolynomial t) 1 +
        deriv quinticPolynomial t * (x - 1) := by
    simp only [tangentLine]
    ring
  rw [hline, (tangent_through_point_iff t).mpr ht,
    (quinticPolynomial_hasDerivAt t).deriv]


theorem quinticPolynomial_hasDerivativeWithinAt (t : ℝ) :
    HasDerivativeWithinAt quinticPolynomial univ t (5 * t ^ 4 - 2) :=
  (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen quinticPolynomial univ isOpen_univ t (5 * t ^ 4 - 2)
    (mem_univ t)).mpr (quinticPolynomial_hasDerivAt t)


theorem secants_tendsto_tangent_through_point {t : ℝ} (ht : contactPolynomial t = 0)
    (x : ℝ) :
    Tendsto (fun z : ℝ ↦ secantLine quinticPolynomial t z x)
      (𝓝[univ \ {t}] t) (𝓝 (2 + (5 * t ^ 4 - 2) * (x - 1))) := by
  have h := secantLine_tendsto_tangent (quinticPolynomial_hasDerivativeWithinAt t) x
  have he : tangentLine quinticPolynomial t (5 * t ^ 4 - 2) x =
      2 + (5 * t ^ 4 - 2) * (x - 1) := by
    simpa only [(quinticPolynomial_hasDerivAt t).deriv] using
      tangent_through_point_equation ht x
  rw [he] at h
  exact h

/-- Bài 7(b): tồn tại duy nhất tiếp tuyến đi qua `(1, 2)`. -/
theorem source_tangent_through_point :
    ∃ t ∈ Ioo (-1 : ℝ) 0, contactPolynomial t = 0 ∧
      HasDerivAt quinticPolynomial (5 * t ^ 4 - 2) t ∧
      tangentLine quinticPolynomial t (deriv quinticPolynomial t) 1 = 2 ∧
      (∀ x : ℝ, tangentLine quinticPolynomial t (deriv quinticPolynomial t) x =
        2 + (5 * t ^ 4 - 2) * (x - 1)) ∧
      (∀ u : ℝ, tangentLine quinticPolynomial u (deriv quinticPolynomial u) 1 = 2 ↔ u = t) := by
  obtain ⟨t, ht, hq⟩ := contactPolynomial_exists_root
  refine ⟨t, ht, hq, quinticPolynomial_hasDerivAt t,
    (tangent_through_point_iff t).mpr hq, tangent_through_point_equation hq, ?_⟩
  intro u
  rw [tangent_through_point_iff]
  constructor
  · intro hu
    exact contactPolynomial_strictMonoOn.injOn
      (contactPolynomial_root_negative hu).le ht.2.le (hu.trans hq.symm)
  · intro hu
    rw [hu]
    exact hq

end calculus.Chapter04.Section01PolynomialTangentThroughPointExercise
