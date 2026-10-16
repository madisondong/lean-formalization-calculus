import calculus.Chapter03.Section01Properties
import calculus.Chapter03.Section02Infinite
import calculus.Chapter03.Section04
import calculus.Chapter03.Section08
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# §3.8 — Bài tập 3.8.8: giới hạn hữu hạn tại +∞

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3958–3965; các câu (a), (b), (c).
-/

set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section08AtInfinityExercises
open calculus.Chapter03.Section01Properties calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section04 calculus.Chapter03.Section08


theorem domainAtTopLimit_Ici_tendsto_atTop {a c : ℝ} {f : ℝ → ℝ}
    (hlim : DomainAtTopLimit (Ici a) f c) : Tendsto f atTop (𝓝 c) := by
  have hwithin := (domainAtTopLimit_iff_tendsto (not_bddAbove_Ici a)).mp hlim
  have hfilter : (atTop : Filter ℝ) ⊓ 𝓟 (Ici a) = atTop :=
    inf_eq_left.mpr (le_principal_iff.mpr (Ici_mem_atTop a))
  simpa only [hfilter] using hwithin


theorem domainAtTopLimit_Ici_tendsto_cocompact {a c : ℝ} {f : ℝ → ℝ}
    (hlim : DomainAtTopLimit (Ici a) f c) :
    Tendsto (fun x : Ici a ↦ f x) (cocompact (Ici a)) (𝓝 c) := by
  let : Inhabited (Ici a) := ⟨⟨a, self_mem_Ici⟩⟩
  rw [cocompact_eq_atTop]
  exact tendsto_comp_val_Ici_atTop.mpr (domainAtTopLimit_Ici_tendsto_atTop hlim)

/-- Bài tập 3.8.8(a): hàm liên tục trên [a,+∞) có giới hạn hữu hạn tại +∞ thì bị chặn. -/
theorem domainContinuousOn_Ici_bounded_of_domainAtTopLimit {a c : ℝ} {f : ℝ → ℝ}
    (hf : DomainContinuousOn (Ici a) f) (hlim : DomainAtTopLimit (Ici a) f c) :
    FunctionBoundedOn (Ici a) f := by
  have hc : ContinuousOn f (Ici a) :=
    (domainContinuousOn_iff_continuousOn ⟨a, self_mem_Ici⟩).mp hf
  let g : Ici a → ℝ := fun x ↦ f x
  have hg : Continuous g := hc.domRestrict
  have ht : Tendsto g (cocompact (Ici a)) (𝓝 c) :=
    domainAtTopLimit_Ici_tendsto_cocompact hlim
  have hk : IsCompact (insert c (range g)) :=
    ht.isCompact_insert_range_of_cocompact hg
  obtain ⟨m, hm⟩ := hk.bddBelow
  obtain ⟨M, hM⟩ := hk.bddAbove
  refine ⟨m, M, ?_⟩
  intro x hx
  have hmem : f x ∈ insert c (range g) := Or.inr ⟨⟨x, hx⟩, rfl⟩
  exact ⟨hm hmem, hM hmem⟩

/-- Bài tập 3.8.8(b): hàm liên tục trên [a,+∞) có giới hạn hữu hạn tại +∞ thì liên tục đều. -/
theorem domainContinuousOn_Ici_nonemptyUniformContinuousOn_of_domainAtTopLimit
    {a c : ℝ} {f : ℝ → ℝ} (hf : DomainContinuousOn (Ici a) f)
    (hlim : DomainAtTopLimit (Ici a) f c) : NonemptyUniformContinuousOn (Ici a) f := by
  have hc : ContinuousOn f (Ici a) :=
    (domainContinuousOn_iff_continuousOn ⟨a, self_mem_Ici⟩).mp hf
  apply (nonemptyUniformContinuousOn_iff (Ici a) f).mpr
  refine ⟨⟨a, self_mem_Ici⟩, ?_⟩
  apply uniformContinuousOn_iff_restrict.mpr
  exact hc.domRestrict.uniformContinuous_of_tendsto_cocompact
    (domainAtTopLimit_Ici_tendsto_cocompact hlim)

/-- Bài tập 3.8.8(c): hàm liên tục trên [a,+∞) có giới hạn c>f(a) tại +∞ thì đạt giá trị nhỏ nhất. -/
theorem domainContinuousOn_Ici_exists_eq_sInf_of_domainAtTopLimit
    {a c : ℝ} {f : ℝ → ℝ} (hf : DomainContinuousOn (Ici a) f)
    (hlim : DomainAtTopLimit (Ici a) f c) (hca : f a < c) :
    ∃ x₀ ∈ Ici a, f x₀ = sInf (f '' Ici a) := by
  have hc : ContinuousOn f (Ici a) :=
    (domainContinuousOn_iff_continuousOn ⟨a, self_mem_Ici⟩).mp hf
  have hg : Continuous (fun x : Ici a ↦ f x) := hc.domRestrict
  have htail : ∀ᶠ x : Ici a in cocompact (Ici a), f a ≤ f x :=
    ((domainAtTopLimit_Ici_tendsto_cocompact hlim).eventually
      (eventually_gt_nhds hca)).mono fun _ hx ↦ hx.le
  obtain ⟨x₀, hmin⟩ := hg.exists_forall_le' ⟨a, self_mem_Ici⟩ htail
  refine ⟨(x₀ : ℝ), x₀.property, ?_⟩
  have hleast : IsLeast (f '' Ici a) (f x₀) := by
    refine ⟨⟨(x₀ : ℝ), x₀.property, rfl⟩, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hmin ⟨x, hx⟩
  exact hleast.csInf_eq.symm

end calculus.Chapter03.Section08AtInfinityExercises
