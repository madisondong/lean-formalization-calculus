import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

/-!
# Bài tập 4.3.9: giới hạn hữu hạn của đạo hàm bằng 0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1131–1133. Hai giới hạn trong giả thiết đều hữu hạn.
-/
namespace calculus.Chapter04.Section03AsymptoticExercises
open Set Filter
open scoped Topology


theorem derivative_limit_eq_zero {f : ℝ → ℝ} {L d : ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0))
    (hl : Tendsto f atTop (𝓝 L)) (hd : Tendsto (deriv f) atTop (𝓝 d)) : d = 0 := by
  classical
  have hw (x : ℝ) (hx : 0 < x) :
      ∃ c ∈ Ioo x (x + 1), deriv f c = f (x + 1) - f x := by
    have hsub : Icc x (x + 1) ⊆ Ici 0 := fun y hy ↦ hx.le.trans hy.1
    obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope f (by linarith : x < x + 1)
      (hf.continuousOn.mono hsub)
      (hf.mono (Ioo_subset_Icc_self.trans hsub))
    refine ⟨c, hc, ?_⟩
    simpa only [add_sub_cancel_left, div_one] using he
  let c : ℝ → ℝ := fun x ↦ if hx : 0 < x then (hw x hx).choose else 0
  have hc (x : ℝ) (hx : 0 < x) :
      c x ∈ Ioo x (x + 1) ∧ deriv f (c x) = f (x + 1) - f x := by
    simpa only [c, dif_pos hx] using (hw x hx).choose_spec
  have hct : Tendsto c atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (hc x hx).1.1.le
  have hstep : Tendsto (fun x : ℝ ↦ f (x + 1) - f x) atTop (𝓝 0) := by
    simpa only [sub_self, Function.comp_apply, id_eq] using (hl.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)).sub hl
  have hder : Tendsto (fun x ↦ deriv f (c x)) atTop (𝓝 0) := by
    apply hstep.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (hc x hx).2.symm
  exact tendsto_nhds_unique (hd.comp hct) hder

end calculus.Chapter04.Section03AsymptoticExercises
