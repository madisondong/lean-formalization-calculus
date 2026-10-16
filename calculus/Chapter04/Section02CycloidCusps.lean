import calculus.Chapter04.Section02Cycloid
import calculus.Chapter04.Section01ParametricExercises

/-!
# §4.2 Bài tập 4: điểm chính quy và điểm nhọn của cycloid

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 854–862.
-/
set_option autoImplicit false
open Filter Topology
namespace calculus.Chapter04.Section02CycloidCusps
open calculus.Chapter04.Section02Cycloid


theorem cycloid_graph_not_differentiable_at_cusp {r t : ℝ}
    (hr : r ≠ 0) (ht : Real.cos t = 1) :
    ¬ DifferentiableAt ℝ (cycloidGraphFunction r) (cycloidX r t) := by
  apply calculus.Chapter04.Section01ParametricExercises.cycloid_singular_no_differentiable_graph
    r t hr ht (cycloidGraphFunction r)
  apply Filter.Eventually.of_forall
  intro s
  change cycloidY r s = cycloidGraphFunction r (cycloidX r s)
  exact (cycloidGraphFunction_apply_cycloidX hr s).symm


theorem cycloid_first_derivative_full_answer {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    (DifferentiableAt ℝ (cycloidGraphFunction r) (cycloidX r t) ↔ Real.cos t ≠ 1) ∧
      (Real.cos t ≠ 1 → deriv (cycloidGraphFunction r) (cycloidX r t) =
        Real.sin t / (1 - Real.cos t)) := by
  have hregular : Real.cos t ≠ 1 → 1 - Real.cos t ≠ 0 := by
    intro ht hz
    exact ht (by linarith)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hf ht
    exact cycloid_graph_not_differentiable_at_cusp hr ht hf
  · intro ht
    exact (cycloidGraphFunction_hasDerivAt hr (hregular ht)).differentiableAt
  · intro ht
    exact (cycloidGraphFunction_hasDerivAt hr (hregular ht)).deriv


theorem cycloid_second_derivative_full_answer {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    ((DifferentiableAt ℝ (cycloidGraphFunction r) (cycloidX r t) ∧
      DifferentiableAt ℝ (deriv (cycloidGraphFunction r)) (cycloidX r t)) ↔ Real.cos t ≠ 1) ∧
      (Real.cos t ≠ 1 → deriv (deriv (cycloidGraphFunction r)) (cycloidX r t) =
        -1 / (r * (1 - Real.cos t) ^ 2)) := by
  have hregular : Real.cos t ≠ 1 → 1 - Real.cos t ≠ 0 := by
    intro ht hz
    exact ht (by linarith)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hf
    exact (cycloid_first_derivative_full_answer hr t).1.mp hf.1
  · intro ht
    exact ⟨(cycloidGraphFunction_hasDerivAt hr (hregular ht)).differentiableAt,
      (cycloidGraphFunction_deriv_hasDerivAt hr (hregular ht)).differentiableAt⟩
  · intro ht
    exact (cycloidGraphFunction_deriv_hasDerivAt hr (hregular ht)).deriv

end calculus.Chapter04.Section02CycloidCusps
