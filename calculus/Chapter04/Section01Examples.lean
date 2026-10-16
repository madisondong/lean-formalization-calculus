import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.Irrational
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Ví dụ 4.1.6: hàm phân nhánh theo tính hữu tỉ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 79–96.
-/
namespace calculus.Chapter04.Section01Examples
open Filter Set
open scoped Topology


noncomputable def rationalSwitch (x : ℝ) : ℝ := by
  classical
  exact if Irrational x then x ^ 2 else 0


theorem rationalSwitch_zero : rationalSwitch 0 = 0 := by simp [rationalSwitch]


theorem rationalSwitch_slope_bound (y : ℝ) :
    |(rationalSwitch y - rationalSwitch 0) / (y - 0)| ≤ |y| := by
  classical
  rw [rationalSwitch_zero]
  simp only [sub_zero]
  by_cases hy : Irrational y
  · rw [rationalSwitch, if_pos hy]
    have hn : y ≠ 0 := hy.ne_zero
    have he : y ^ 2 / y = y := by field_simp
    rw [he]
  · simp [rationalSwitch, hy]


theorem rationalSwitch_hasDerivAt_zero : HasDerivAt rationalSwitch 0 0 := by
  have hb : Tendsto (fun y : ℝ ↦ |y|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using continuous_abs.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := {(0 : ℝ)}ᶜ))
  have ha : Tendsto (fun y : ℝ ↦ |(rationalSwitch y - rationalSwitch 0) / (y - 0)|)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun y ↦ abs_nonneg _)
      (Eventually.of_forall rationalSwitch_slope_bound) hb
  have ht : Tendsto (fun y : ℝ ↦ (rationalSwitch y - rationalSwitch 0) / (y - 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs, abs_div] using ha)
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hs : slope rationalSwitch 0 = (fun y ↦ (rationalSwitch y - rationalSwitch 0) / (y - 0)) :=
    funext (slope_def_field rationalSwitch 0)
  simpa only [hs] using ht


theorem rationalSwitch_deriv_zero : deriv rationalSwitch 0 = 0 := rationalSwitch_hasDerivAt_zero.deriv


theorem rationalSwitch_not_continuousAt (x : ℝ) (hx : x ≠ 0) :
    ¬ ContinuousAt rationalSwitch x := by
  classical
  intro hc
  let R : Set ℝ := Set.range (fun q : ℚ ↦ (q : ℝ))
  have : (𝓝[R] x).NeBot := Rat.denseRange_cast.nhdsWithin_neBot x
  have ht0 : Tendsto rationalSwitch (𝓝[R] x) (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    rcases hy with ⟨q, rfl⟩
    simp [rationalSwitch]
  have hzero : rationalSwitch x = 0 :=
    tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) ht0
  let J : Set ℝ := {y : ℝ | Irrational y}
  have : (𝓝[J] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (dense_irrational x)
  have ht2 : Tendsto rationalSwitch (𝓝[J] x) (𝓝 (x ^ 2)) := by
    apply ((continuousAt_id.pow 2).tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [rationalSwitch, show Irrational y from hy]
  have hsquare : rationalSwitch x = x ^ 2 :=
    tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) ht2
  exact hx (sq_eq_zero_iff.mp (hsquare.symm.trans hzero))

/-- Ví dụ 4.1.6: đạo hàm tại 0 bằng 0; hàm không liên tục tại mọi điểm khác 0. -/
theorem rationalSwitch_complete :
    HasDerivAt rationalSwitch 0 0 ∧ deriv rationalSwitch 0 = 0 ∧
      ContinuousAt rationalSwitch 0 ∧ ∀ x : ℝ, x ≠ 0 → ¬ ContinuousAt rationalSwitch x :=
  ⟨rationalSwitch_hasDerivAt_zero, rationalSwitch_deriv_zero,
    rationalSwitch_hasDerivAt_zero.continuousAt, rationalSwitch_not_continuousAt⟩

end calculus.Chapter04.Section01Examples
