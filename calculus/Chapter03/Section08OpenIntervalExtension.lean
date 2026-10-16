import calculus.Chapter03.Section08
import calculus.Chapter03.Section08HeineCantor
import calculus.Chapter03.Section01Properties
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.ContinuousOn

/-!
# §3.8 — mở rộng liên tục từ khoảng lên đoạn

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 3876–3893, Định lí 3.8.15; Chương 2, dòng 119–133.
-/

set_option autoImplicit false
open Set

namespace calculus.Chapter03.Section08OpenIntervalExtension
open calculus.Chapter03.Section08
open calculus.Chapter03.Section08HeineCantor


theorem openInterval_inclusion_denseRange {a b : ℝ} (hab : a < b) :
    DenseRange (inclusion (Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b)) := by
  apply (denseRange_inclusion_iff (Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b)).mpr
  simpa only [closure_Ioo hab.ne] using (Subset.rfl : Icc a b ⊆ Icc a b)


theorem uniformContinuousOn_openInterval_exists_continuous_extension
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hf : UniformContinuousOn f (Ioo a b)) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Icc a b) ∧ ∀ x ∈ Ioo a b, F x = f x := by
  classical
  let hsub : Ioo a b ⊆ Icc a b := Ioo_subset_Icc_self
  let i : Ioo a b → Icc a b := inclusion hsub
  have hi : IsUniformInducing i :=
    (isUniformEmbedding_set_inclusion hsub).isUniformInducing
  have hd : DenseRange i := openInterval_inclusion_denseRange hab
  let fr : Ioo a b → ℝ := (Ioo a b).domRestrict f
  have hfr : UniformContinuous fr := uniformContinuousOn_iff_restrict.mp hf
  let g : Icc a b → ℝ := (hi.isDenseInducing hd).extend fr
  have hg : UniformContinuous g := uniformContinuous_uniformly_extend hi hd hfr
  let F : ℝ → ℝ := fun x ↦ if hx : x ∈ Icc a b then g ⟨x, hx⟩ else 0
  refine ⟨F, ?_, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    have hrest : (Icc a b).domRestrict F = g := by
      funext x
      exact dif_pos x.property
    rw [hrest]
    exact hg.continuous
  · intro x hx
    have hxc : x ∈ Icc a b := hsub hx
    have hext : g (i ⟨x, hx⟩) = fr ⟨x, hx⟩ :=
      uniformly_extend_of_ind hi hd hfr ⟨x, hx⟩
    have hFx : F x = g ⟨x, hxc⟩ := dif_pos hxc
    exact hFx.trans hext

/-- Định lí 3.8.15: liên tục đều trên (a,b) tương đương tồn tại mở rộng liên tục lên [a,b], với a<b. -/
theorem nonemptyUniformContinuousOn_openInterval_iff_continuous_extension
    {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    NonemptyUniformContinuousOn (Ioo a b) f ↔
      ∃ F : ℝ → ℝ, ContinuousOn F (Icc a b) ∧ ∀ x ∈ Ioo a b, F x = f x := by
  constructor
  · intro hf
    exact uniformContinuousOn_openInterval_exists_continuous_extension hab
      ((nonemptyUniformContinuousOn_iff (Ioo a b) f).mp hf).2
  · rintro ⟨F, hF, hEq⟩
    have hFuc : NonemptyUniformContinuousOn (Icc a b) F :=
      continuousOn_closedInterval_nonemptyUniformContinuousOn (nonempty_Icc.mpr hab.le) hF
    apply (nonemptyUniformContinuousOn_iff (Ioo a b) f).mpr
    refine ⟨nonempty_Ioo.mpr hab, ?_⟩
    exact (((nonemptyUniformContinuousOn_iff (Icc a b) F).mp hFuc).2.mono
      (Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b)).congr hEq

/-- Bài tập 3.8.7(a), dòng 3953: hàm liên tục đều trên khoảng hữu hạn thì bị chặn. -/
theorem nonemptyUniformContinuousOn_openInterval_bounded
    {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hf : NonemptyUniformContinuousOn (Ioo a b) f) :
    calculus.Chapter03.Section01Properties.FunctionBoundedOn (Ioo a b) f := by
  obtain ⟨F, hF, hEq⟩ :=
    (nonemptyUniformContinuousOn_openInterval_iff_continuous_extension hab f).mp hf
  obtain ⟨m, hm⟩ := isCompact_Icc.bddBelow_image hF
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hF
  refine ⟨m, M, ?_⟩
  intro x hx
  have hxc : x ∈ Icc a b := Ioo_subset_Icc_self hx
  simpa only [hEq x hx] using And.intro (hm ⟨x, hxc, rfl⟩) (hM ⟨x, hxc, rfl⟩)

end calculus.Chapter03.Section08OpenIntervalExtension
