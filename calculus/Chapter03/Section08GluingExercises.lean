import calculus.Chapter03.Section08
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith

/-!
# §3.8 — Bài tập 3.8.13(a,b): ghép miền liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3984–3989.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08GluingExercises
open calculus.Chapter03.Section08

/-- Bài tập 3.8.13(a): ghép tính liên tục đều qua điểm chung b. -/
theorem nonemptyUniformContinuousOn_adjacent_halfOpenIntervals
    {a b c : ℝ} {f : ℝ → ℝ}
    (hleft : NonemptyUniformContinuousOn (Ioc a b) f)
    (hright : NonemptyUniformContinuousOn (Ico b c) f) :
    NonemptyUniformContinuousOn (Ioo a c) f := by
  have hab : a < b := nonempty_Ioc.mp hleft.1
  have hbc : b < c := nonempty_Ico.mp hright.1
  refine ⟨⟨b, by exact ⟨hab, hbc⟩⟩, ?_⟩
  intro ε hε
  have hεhalf : 0 < ε / 2 := by linarith
  obtain ⟨δL, hδL, hL⟩ := hleft.2 (ε / 2) hεhalf
  obtain ⟨δR, hδR, hR⟩ := hright.2 (ε / 2) hεhalf
  refine ⟨min δL δR, lt_min hδL hδR, ?_⟩
  have hordered : ∀ u ∈ Ioo a c, ∀ v ∈ Ioo a c, u ≤ v →
      |u - v| < min δL δR → |f u - f v| < ε := by
    intro u hu v hv huv hdist
    change a < u ∧ u < c at hu
    change a < v ∧ v < c at hv
    have hdistL : |u - v| < δL := lt_of_lt_of_le hdist (min_le_left δL δR)
    have hdistR : |u - v| < δR := lt_of_lt_of_le hdist (min_le_right δL δR)
    by_cases hvb : v ≤ b
    · have huL : u ∈ Ioc a b := by exact ⟨hu.1, huv.trans hvb⟩
      have hvL : v ∈ Ioc a b := by exact ⟨hv.1, hvb⟩
      have hsmall := hL u huL v hvL hdistL
      linarith
    · by_cases hbu : b ≤ u
      · have huR : u ∈ Ico b c := by exact ⟨hbu, hu.2⟩
        have hvR : v ∈ Ico b c := by exact ⟨hbu.trans huv, hv.2⟩
        have hsmall := hR u huR v hvR hdistR
        linarith
      · have hub : u < b := lt_of_not_ge hbu
        have hbv : b < v := lt_of_not_ge hvb
        have huL : u ∈ Ioc a b := by exact ⟨hu.1, hub.le⟩
        have hvR : v ∈ Ico b c := by exact ⟨hbv.le, hv.2⟩
        have hbL : b ∈ Ioc a b := by exact ⟨hab, le_rfl⟩
        have hbR : b ∈ Ico b c := by exact ⟨le_rfl, hbc⟩
        have hubdist : |u - b| < δL := by
          rw [abs_of_nonpos (sub_nonpos.mpr hub.le)]
          rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hdistL
          linarith
        have hbvdist : |b - v| < δR := by
          rw [abs_of_nonpos (sub_nonpos.mpr hbv.le)]
          rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hdistR
          linarith
        have hsmallL := hL u huL b hbL hubdist
        have hsmallR := hR b hbR v hvR hbvdist
        calc
          |f u - f v| ≤ |f u - f b| + |f b - f v| := abs_sub_le (f u) (f b) (f v)
          _ < ε := by linarith
  intro u hu v hv hdist
  obtain huv | hvu := le_total u v
  · exact hordered u hu v hv huv hdist
  · have hdist' : |v - u| < min δL δR := by
      simpa only [abs_sub_comm] using hdist
    simpa only [abs_sub_comm] using hordered v hv u hu hvu hdist'

/-- Bài tập 3.8.13(b): liên tục đều trên hợp hai đoạn đóng. -/
theorem nonemptyUniformContinuousOn_union_closedIntervals
    {a b c d : ℝ} {f : ℝ → ℝ}
    (hleft : NonemptyUniformContinuousOn (Icc a b) f)
    (hright : NonemptyUniformContinuousOn (Icc c d) f) :
    NonemptyUniformContinuousOn (Icc a b ∪ Icc c d) f := by
  have hcL : ContinuousOn f (Icc a b) := nonemptyUniformContinuousOn_continuousOn hleft
  have hcR : ContinuousOn f (Icc c d) := nonemptyUniformContinuousOn_continuousOn hright
  have hcont : ContinuousOn f (Icc a b ∪ Icc c d) :=
    hcL.union_of_isClosed hcR isClosed_Icc isClosed_Icc
  have hcompact : IsCompact (Icc a b ∪ Icc c d) := isCompact_Icc.union isCompact_Icc
  apply (nonemptyUniformContinuousOn_iff (Icc a b ∪ Icc c d) f).mpr
  exact ⟨hleft.1.mono subset_union_left, hcompact.uniformContinuousOn_of_continuous hcont⟩

/-- Bài tập 3.8.13(b): liên tục đều trên từng đoạn [a,b], [c,d] thì liên tục đều trên hợp của chúng, với a<b và c<d (Chương 2, dòng 119–133). -/
theorem nonemptyUniformContinuousOn_union_closed_intervals_of_lt
    {a b c d : ℝ} {f : ℝ → ℝ} (hab : a < b) (hcd : c < d)
    (hleft : NonemptyUniformContinuousOn (Icc a b) f)
    (hright : NonemptyUniformContinuousOn (Icc c d) f) :
    NonemptyUniformContinuousOn (Icc a b ∪ Icc c d) f := by
  exact nonemptyUniformContinuousOn_union_closedIntervals
    ⟨nonempty_Icc.mpr hab.le, hleft.2⟩ ⟨nonempty_Icc.mpr hcd.le, hright.2⟩

end calculus.Chapter03.Section08GluingExercises
