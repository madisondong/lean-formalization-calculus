import calculus.Chapter03.Section08
import calculus.Chapter03.Section04
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# §3.8 — liên tục đều trên đoạn

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 3861–3874, Định lí 3.8.14; Định nghĩa 2.1.6, `source/Ch2_dayso.tex`, dòng 119–133.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08HeineCantor
open calculus.Chapter03.Section08
open calculus.Chapter03.Section04


theorem continuousOn_closedInterval_nonemptyUniformContinuousOn {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : ContinuousOn f (Icc a b)) :
    NonemptyUniformContinuousOn (Icc a b) f := by
  apply (nonemptyUniformContinuousOn_iff (Icc a b) f).mpr
  exact ⟨hD, isCompact_Icc.uniformContinuousOn_of_continuous hf⟩


theorem domainContinuousOn_closedInterval_nonemptyUniformContinuousOn {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f) :
    NonemptyUniformContinuousOn (Icc a b) f :=
  continuousOn_closedInterval_nonemptyUniformContinuousOn hD
    ((domainContinuousOn_iff_continuousOn hD).mp hf)

/-- Định lí 3.8.14: hàm liên tục trên đoạn a<b thì liên tục đều. -/
theorem domainContinuousOn_closedInterval_nonemptyUniformContinuousOn_of_lt
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : DomainContinuousOn (Icc a b) f) :
    NonemptyUniformContinuousOn (Icc a b) f :=
  domainContinuousOn_closedInterval_nonemptyUniformContinuousOn (nonempty_Icc.mpr hab.le) hf

end calculus.Chapter03.Section08HeineCantor
