import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Bài 13(f,g): điều kiện ghép tại 0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 582–591.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section01GluingExercises
open Filter Set
open scoped Topology


def spliceZero (left right : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ 0 then left x else right x


theorem spliceZero_zero (left right : ℝ → ℝ) : spliceZero left right 0 = left 0 := by
  simp [spliceZero]


theorem spliceZero_eq_left {left right : ℝ → ℝ} {x : ℝ} (hx : x ≤ 0) :
    spliceZero left right x = left x := by
  exact if_pos hx


theorem spliceZero_eq_right {left right : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    spliceZero left right x = right x := by
  exact if_neg (not_le.mpr hx)


theorem spliceZero_hasDerivAt {left right : ℝ → ℝ} {d : ℝ}
    (hl : HasDerivAt left d 0) (hr : HasDerivAt right d 0) (hv : left 0 = right 0) :
    HasDerivAt (spliceZero left right) d 0 := by
  have hleft : HasDerivWithinAt (spliceZero left right) d (Iic 0) 0 := by
    apply hl.hasDerivWithinAt.congr
    · intro x hx
      exact spliceZero_eq_left hx
    · exact spliceZero_zero left right
  have hright : HasDerivWithinAt (spliceZero left right) d (Ici 0) 0 := by
    apply hr.hasDerivWithinAt.congr
    · intro x hx
      by_cases hx0 : x = 0
      · subst x
        exact (spliceZero_zero left right).trans hv
      · exact spliceZero_eq_right (lt_of_le_of_ne (show 0 ≤ x from hx) (Ne.symm hx0))
    · exact (spliceZero_zero left right).trans hv
  have hunion : Iic (0 : ℝ) ∪ Ici 0 = univ := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x 0
  have h := hleft.union hright
  rw [hunion] at h
  exact hasDerivWithinAt_univ.mp h


theorem spliceZero_values_equal_of_continuousAt {left right : ℝ → ℝ}
    (hr : ContinuousAt right 0) (hf : ContinuousAt (spliceZero left right) 0) :
    left 0 = right 0 := by
  have hlim : Tendsto (spliceZero left right) (𝓝[>] (0 : ℝ)) (𝓝 (left 0)) := by
    simpa only [spliceZero_zero] using hf.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto right (𝓝[>] (0 : ℝ)) (𝓝 (left 0)) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact spliceZero_eq_right hx
  exact tendsto_nhds_unique hright (hr.tendsto.mono_left nhdsWithin_le_nhds)


theorem spliceZero_differentiableAt_iff {left right : ℝ → ℝ} {dl dr : ℝ}
    (hl : HasDerivAt left dl 0) (hr : HasDerivAt right dr 0) :
    DifferentiableAt ℝ (spliceZero left right) 0 ↔ left 0 = right 0 ∧ dl = dr := by
  constructor
  · intro hf
    have hv := spliceZero_values_equal_of_continuousAt hr.continuousAt hf.continuousAt
    have hleft : HasDerivWithinAt (spliceZero left right) dl (Iic 0) 0 := by
      apply hl.hasDerivWithinAt.congr
      · intro x hx
        exact spliceZero_eq_left hx
      · exact spliceZero_zero left right
    have hright : HasDerivWithinAt (spliceZero left right) dr (Ici 0) 0 := by
      apply hr.hasDerivWithinAt.congr
      · intro x hx
        by_cases hx0 : x = 0
        · subst x
          exact (spliceZero_zero left right).trans hv
        · exact spliceZero_eq_right (lt_of_le_of_ne (show 0 ≤ x from hx) (Ne.symm hx0))
      · exact (spliceZero_zero left right).trans hv
    have hdl : deriv (spliceZero left right) 0 = dl :=
      (hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic 0)).symm.trans
        (hleft.derivWithin (uniqueDiffWithinAt_Iic 0))
    have hdr : deriv (spliceZero left right) 0 = dr :=
      (hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
        (hright.derivWithin (uniqueDiffWithinAt_Ici 0))
    exact ⟨hv, hdl.symm.trans hdr⟩
  · rintro ⟨hv, hd⟩
    rw [← hd] at hr
    exact (spliceZero_hasDerivAt hl hr hv).differentiableAt


def hyperbolicAffineJoin (a b : ℝ) : ℝ → ℝ :=
  spliceZero (fun x ↦ a * Real.cosh x + b * Real.sinh x) (fun x ↦ a * x + b)


theorem hyperbolic_left_hasDerivAt_zero (a b : ℝ) :
    HasDerivAt (fun x : ℝ ↦ a * Real.cosh x + b * Real.sinh x) b 0 := by
  have h := ((Real.hasDerivAt_cosh 0).const_mul a).add ((Real.hasDerivAt_sinh 0).const_mul b)
  apply (h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
  simp


theorem affine_hasDerivAt_zero (a b : ℝ) :
    HasDerivAt (fun x : ℝ ↦ a * x + b) a 0 := by
  simpa only [id_eq, mul_one, add_zero] using ((hasDerivAt_id (0 : ℝ)).const_mul a).add_const b

/-- Bài 13(f): khả vi tại 0 khi và chỉ khi `a = b`. -/
theorem hyperbolicAffineJoin_differentiableAt_zero_iff (a b : ℝ) :
    DifferentiableAt ℝ (hyperbolicAffineJoin a b) 0 ↔ a = b := by
  have h := spliceZero_differentiableAt_iff (hyperbolic_left_hasDerivAt_zero a b)
    (affine_hasDerivAt_zero a b)
  simpa [hyperbolicAffineJoin, eq_comm] using h


theorem hyperbolicAffineJoin_hasDerivAt_zero (a b : ℝ) (hab : a = b) :
    HasDerivAt (hyperbolicAffineJoin a b) a 0 := by
  apply spliceZero_hasDerivAt
  · simpa only [← hab] using hyperbolic_left_hasDerivAt_zero a b
  · exact affine_hasDerivAt_zero a b
  · simp [hab]


def arctangentAffineJoin (a b : ℝ) : ℝ → ℝ :=
  spliceZero Real.arctan (fun x ↦ a * x + b)


theorem arctangent_hasDerivAt_zero : HasDerivAt Real.arctan 1 0 := by
  simpa using Real.hasDerivAt_arctan (0 : ℝ)

/-- Bài 13(g): khả vi tại 0 khi và chỉ khi `a = 1`, `b = 0`. -/
theorem arctangentAffineJoin_differentiableAt_zero_iff (a b : ℝ) :
    DifferentiableAt ℝ (arctangentAffineJoin a b) 0 ↔ a = 1 ∧ b = 0 := by
  have h := spliceZero_differentiableAt_iff arctangent_hasDerivAt_zero (affine_hasDerivAt_zero a b)
  simpa [arctangentAffineJoin, eq_comm, and_comm] using h


theorem arctangentAffineJoin_hasDerivAt_zero (a b : ℝ) (ha : a = 1) (hb : b = 0) :
    HasDerivAt (arctangentAffineJoin a b) 1 0 := by
  apply spliceZero_hasDerivAt
  · exact arctangent_hasDerivAt_zero
  · simpa only [ha] using affine_hasDerivAt_zero a b
  · simp [hb]

end calculus.Chapter04.Section01GluingExercises
