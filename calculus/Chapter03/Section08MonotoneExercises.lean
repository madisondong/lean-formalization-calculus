import calculus.Chapter03.Section01Properties
import calculus.Chapter03.Section04
import calculus.Chapter03.Section08OpenIntervalExtension
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.ExtendFrom

/-!
# §3.8 — hàm đơn điệu bị chặn trên khoảng mở

Nguồn: Bài tập 3.8.7(b), `source/Ch3_gioihanhamso.tex`, dòng 3950–3956; Chương 2, dòng 119–133.
-/

set_option autoImplicit false
open Set

namespace calculus.Chapter03.Section08MonotoneExercises
open calculus.Chapter03.Section01Properties
open calculus.Chapter03.Section04
open calculus.Chapter03.Section08
open calculus.Chapter03.Section08OpenIntervalExtension


def openIntervalDomain (a b : ℝ) : IntervalDomain :=
  ⟨Ioo a b, Set.ordConnected_Ioo⟩


theorem continuous_bounded_monotoneOn_exists_extension
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Ioo a b))
    (hbound : FunctionBoundedOn (Ioo a b) f)
    (hmono : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b)) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Icc a b) ∧ ∀ x ∈ Ioo a b, F x = f x := by
  obtain ⟨m, M, hbounds⟩ := hbound
  have hbelow : BddBelow (f '' Ioo a b) := by
    refine ⟨m, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (hbounds x hx).1
  have habove : BddAbove (f '' Ioo a b) := by
    refine ⟨M, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (hbounds x hx).2
  have hne : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
  have hF : ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) := by
    rcases hmono with hi | hd
    · exact continuousOn_Icc_extendFrom_Ioo hcont
        (MonotoneOn.tendsto_nhdsWithin_Ioo_right hne hi hbelow)
        (MonotoneOn.tendsto_nhdsWithin_Ioo_left hne hi habove)
    · exact continuousOn_Icc_extendFrom_Ioo hcont
        (AntitoneOn.tendsto_nhdsWithin_Ioo_right hne hd habove)
        (AntitoneOn.tendsto_nhdsWithin_Ioo_left hne hd hbelow)
  exact ⟨extendFrom (Ioo a b) f, hF, extendFrom_extends hcont⟩

/-- Bài tập 3.8.7(b): hàm liên tục, bị chặn và đơn điệu trên (a,b), a<b, thì liên tục đều. -/
theorem sourceContinuous_bounded_functionMonotonic_uniformContinuous
    {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hc : DomainContinuousOn (Ioo a b) f)
    (hb : FunctionBoundedOn (Ioo a b) f)
    (hm : FunctionMonotonic (openIntervalDomain a b) f) :
    NonemptyUniformContinuousOn (Ioo a b) f := by
  have hcont : ContinuousOn f (Ioo a b) :=
    (domainContinuousOn_iff_continuousOn (nonempty_Ioo.mpr hab)).mp hc
  have hmono : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b) := by
    rcases hm with hi | hd
    · exact Or.inl ((function_increasing_iff_monotoneOn (openIntervalDomain a b) f).mp hi)
    · exact Or.inr ((function_decreasing_iff_antitoneOn (openIntervalDomain a b) f).mp hd)
  exact (nonemptyUniformContinuousOn_openInterval_iff_continuous_extension hab f).mpr
    (continuous_bounded_monotoneOn_exists_extension hab hcont hb hmono)

end calculus.Chapter03.Section08MonotoneExercises
