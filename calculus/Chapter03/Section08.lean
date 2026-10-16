import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.NormNum

/-!
# §3.8 — liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3766–3777, Định nghĩa 3.8.1, Ví dụ 3.8.2 và Định lí 3.8.3.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08


def UniformContinuityConditionOn (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ u ∈ D, ∀ v ∈ D, |u - v| < δ → |f u - f v| < ε

/-- Định nghĩa 3.8.1: D≠∅; δ chỉ phụ thuộc ε, không phụ thuộc hai điểm trong D. -/
def NonemptyUniformContinuousOn (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  D.Nonempty ∧ UniformContinuityConditionOn D f


theorem uniformContinuityConditionOn_iff (D : Set ℝ) (f : ℝ → ℝ) :
    UniformContinuityConditionOn D f ↔ UniformContinuousOn f D := by
  simp only [UniformContinuityConditionOn, Metric.uniformContinuousOn_iff, Real.dist_eq]


theorem nonemptyUniformContinuousOn_iff (D : Set ℝ) (f : ℝ → ℝ) :
    NonemptyUniformContinuousOn D f ↔ D.Nonempty ∧ UniformContinuousOn f D := by
  rw [NonemptyUniformContinuousOn, uniformContinuityConditionOn_iff]

/-- Ví dụ 3.8.2: hàm hằng liên tục đều trên miền không rỗng. -/
theorem nonemptyUniformContinuousOn_const (D : Set ℝ) (hD : D.Nonempty) (c : ℝ) :
    NonemptyUniformContinuousOn D (fun _ ↦ c) := by
  refine ⟨hD, ?_⟩
  intro ε hε
  exact ⟨1, by norm_num, fun _ _ _ _ _ ↦ by simpa using hε⟩

/-- Định lí 3.8.3: liên tục đều suy ra liên tục trên cùng miền. -/
theorem nonemptyUniformContinuousOn_continuousOn {D : Set ℝ} {f : ℝ → ℝ}
    (hf : NonemptyUniformContinuousOn D f) : ContinuousOn f D :=
  ((uniformContinuityConditionOn_iff D f).mp hf.2).continuousOn

end calculus.Chapter03.Section08
