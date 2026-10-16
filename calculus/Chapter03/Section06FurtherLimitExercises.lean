import calculus.Chapter03.Section06Limits
import calculus.Chapter03.Section02OneSided
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# §3.6 — Bài tập 6(c) và 7(d)

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3160 và dòng 3171.
-/

set_option autoImplicit false
noncomputable section

namespace calculus.Chapter03.Section06FurtherLimitExercises

open Set Filter
open scoped Topology
open calculus.Chapter03.Section02
open calculus.Chapter03.Section02OneSided


theorem arctangent_reciprocal_right_accumulation :
    RightAccumulationPointOf (univ \ {(1 : ℝ)}) 1 := by
  intro δ hδ
  refine ⟨1 + δ / 2, ?_, by linarith, by linarith⟩
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]
  linarith

/-- Bài tập 3.6.6(c): arctan(1/(x−1))→π/2 khi x→1⁺. -/
theorem exercise06_arctangent_reciprocal_right :
    DomainRightLimit (univ \ {(1 : ℝ)})
      (fun x : ℝ ↦ Real.arctan (1 / (x - 1))) 1 (Real.pi / 2) := by
  apply (domainRightLimit_iff_tendsto
    arctangent_reciprocal_right_accumulation).mpr
  have hshift : Tendsto (fun x : ℝ ↦ x - 1)
      (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa only [sub_self, id_eq] using
          ((tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 (1 : ℝ)) (𝓝 (1 : ℝ))).sub_const 1)
      exact ht.mono_left
        (show (𝓝[>] (1 : ℝ)) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (show (1 : ℝ) < x from hx)
  have hinv : Tendsto (fun x : ℝ ↦ (x - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hshift
  have harctan : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right
      (show (𝓝[<] (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) from nhdsWithin_le_nhds)
  have ht : Tendsto (fun x : ℝ ↦ Real.arctan (1 / (x - 1)))
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.pi / 2)) := by
    simpa only [Function.comp_def, one_div] using harctan.comp hinv
  exact ht.mono_left (nhdsWithin_mono (1 : ℝ)
    (show (univ \ {(1 : ℝ)}) ∩ Ioi (1 : ℝ) ⊆ Ioi (1 : ℝ) from
      fun _ hx ↦ hx.2))

/-- Bài tập 3.6.7(d): giới hạn tại 3 bằng 27 ln 3−27. -/
theorem exercise07_exponential_cubic_quotient :
    DomainLimit (univ \ {(3 : ℝ)})
      (fun x : ℝ ↦ ((3 : ℝ) ^ x - x ^ 3) / (x - 3))
      3 (27 * Real.log 3 - 27) := by
  apply (domainLimit_iff_tendsto (univ_diff_accumulation 3)).mpr
  have hExp : HasDerivAt (fun x : ℝ ↦ (3 : ℝ) ^ x)
      (27 * Real.log 3) (3 : ℝ) := by
    have h := (Real.hasStrictDerivAt_const_rpow
      (a := (3 : ℝ)) (by norm_num) (3 : ℝ)).hasDerivAt
    norm_num [Real.rpow_ofNat] at h
    exact h
  have hCube : HasDerivAt (fun x : ℝ ↦ x ^ 3) 27 (3 : ℝ) := by
    have h := hasDerivAt_pow 3 (3 : ℝ)
    norm_num at h
    exact h
  have hd : HasDerivAt (fun x : ℝ ↦ (3 : ℝ) ^ x - x ^ 3)
      (27 * Real.log 3 - 27) (3 : ℝ) :=
    HasDerivAt.sub hExp hCube
  have hzero : (3 : ℝ) ^ (3 : ℝ) - (3 : ℝ) ^ 3 = 0 := by
    norm_num [Real.rpow_ofNat]
  have ht : Tendsto (fun x : ℝ ↦ ((3 : ℝ) ^ x - x ^ 3) / (x - 3))
      (𝓝[≠] (3 : ℝ)) (𝓝 (27 * Real.log 3 - 27)) := by
    simpa only [slope_fun_def_field, hzero, sub_zero] using hd.tendsto_slope
  exact ht.mono_left (nhdsWithin_mono (3 : ℝ)
    (show (univ \ {(3 : ℝ)}) \ {(3 : ℝ)} ⊆ {(3 : ℝ)}ᶜ from
      fun _ hx ↦ hx.2))

end calculus.Chapter03.Section06FurtherLimitExercises
