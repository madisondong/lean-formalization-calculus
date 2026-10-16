import calculus.Chapter04.Section04InfiniteExtensions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# §4.3, Bài 12(a): giới hạn khi f+f′ tiến tới 0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1146–1150.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section03FirstOrderStableLimitExercise
open Set Filter
open scoped Topology
open calculus.Chapter04.Section04InfiniteExtensions


theorem first_order_stable_limit {f d : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Ioi 0, HasDerivAt f (d x) x)
    (hl : Tendsto (fun x ↦ f x + d x) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  have hd (x : ℝ) (hx : x ∈ Ioi 0) :
      HasDerivAt (fun y ↦ f y * Real.exp y)
        ((f x + d x) * Real.exp x) x := by
    apply ((hf x hx).fun_mul (Real.hasDerivAt_exp x)).congr_deriv
    ring
  have hq : Tendsto (fun x ↦ ((f x + d x) * Real.exp x) / Real.exp x)
      atTop (𝓝 L) := by
    simpa only [mul_div_cancel_right₀ _ (Real.exp_ne_zero _)] using hl
  have ht := lhopital_infinite_atTop_hasDerivAt hd
    (fun x _ ↦ Real.hasDerivAt_exp x) (fun x _ ↦ Real.exp_ne_zero x)
    (Or.inl Real.tendsto_exp_atTop) hq (Or.inl ⟨L, rfl⟩)
  simpa only [mul_div_cancel_right₀ _ (Real.exp_ne_zero _)] using ht

/-- Bài 12(a): `f + f′ → 0` kéo theo `f → 0` trên nửa trục. -/
theorem source_first_order_stable_zero_limit {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0))
    (hl : Tendsto (fun x ↦ f x + deriv f x) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  apply first_order_stable_limit _ hl
  intro x hx
  exact ((hf x (mem_Ici.mpr (mem_Ioi.mp hx).le)).differentiableAt (Ici_mem_nhds hx)).hasDerivAt

end calculus.Chapter04.Section03FirstOrderStableLimitExercise
