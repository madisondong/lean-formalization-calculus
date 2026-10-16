import calculus.Chapter03.Section08AtInfinityExercises
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! §3.8 — Bài tập 3.8.14. Nguồn: dòng 3993–3994. Câu (a) xét ℝ; câu (b) thiếu miền xác định ngoài [a,+∞). -/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08TwoTailExercises
open calculus.Chapter03.Section02Infinite calculus.Chapter03.Section04
open calculus.Chapter03.Section08 calculus.Chapter03.Section08AtInfinityExercises


theorem uniformContinuityCondition_glue_rays {a : ℝ} {f : ℝ → ℝ}
    (hl : UniformContinuityConditionOn (Iic a) f)
    (hr : UniformContinuityConditionOn (Ici a) f) :
    UniformContinuityConditionOn univ f := by
  intro ε hε
  obtain ⟨δl, hδl, hbl⟩ := hl (ε / 2) (half_pos hε)
  obtain ⟨δr, hδr, hbr⟩ := hr (ε / 2) (half_pos hε)
  let δ := min δl δr
  have hδ : 0 < δ := lt_min hδl hδr
  have hordered : ∀ u v : ℝ, u ≤ v → |u - v| < δ → |f u - f v| < ε := by
    intro u v huv hnear
    by_cases hva : v ≤ a
    · exact (hbl u (huv.trans hva) v hva
        (hnear.trans_le (min_le_left δl δr))).trans (by linarith)
    · by_cases hau : a ≤ u
      · exact (hbr u hau v (hau.trans huv)
          (hnear.trans_le (min_le_right δl δr))).trans (by linarith)
      · have hua : u < a := lt_of_not_ge hau
        have hav : a < v := lt_of_not_ge hva
        have hh := abs_lt.mp hnear
        have hleft : |u - a| < δl := by
          rw [abs_of_nonpos (sub_nonpos.mpr hua.le)]
          have hδle : δ ≤ δl := min_le_left _ _
          linarith
        have hright : |a - v| < δr := by
          rw [abs_of_nonpos (sub_nonpos.mpr hav.le)]
          have hδle : δ ≤ δr := min_le_right _ _
          linarith
        have h1 := hbl u hua.le a self_mem_Iic hleft
        have h2 := hbr a self_mem_Ici v hav.le hright
        calc
          |f u - f v| = |(f u - f a) + (f a - f v)| := by congr 1; ring
          _ ≤ |f u - f a| + |f a - f v| := abs_add_le _ _
          _ < ε := by linarith
  refine ⟨δ, hδ, fun u _ v _ hnear ↦ ?_⟩
  by_cases huv : u ≤ v
  · exact hordered u v huv hnear
  · have hh := hordered v u (le_of_not_ge huv)
        (by simpa only [abs_sub_comm v u] using hnear)
    simpa only [abs_sub_comm (f v) (f u)] using hh

/-- Bài tập 3.8.14(a): hàm liên tục trên ℝ có hai giới hạn hữu hạn tại ±∞ thì liên tục đều. -/
theorem domainContinuousOn_univ_nonemptyUniformContinuousOn_of_finite_tail_limits
    {f : ℝ → ℝ} (hf : DomainContinuousOn univ f)
    (hleft : ∃ A : ℝ, DomainAtBotLimit univ f A)
    (hright : ∃ B : ℝ, DomainAtTopLimit univ f B) :
    NonemptyUniformContinuousOn univ f := by
  obtain ⟨A, hA⟩ := hleft
  obtain ⟨B, hB⟩ := hright
  have hc : Continuous f := continuousOn_univ.mp
    ((domainContinuousOn_iff_continuousOn univ_nonempty).mp hf)
  have hrightLimit : DomainAtTopLimit (Ici (0 : ℝ)) f B := by
    refine ⟨not_bddAbove_Ici 0, ?_⟩
    intro ε hε
    obtain ⟨M, hM⟩ := hB.2 ε hε
    exact ⟨M, fun x _ hx ↦ hM x (mem_univ x) hx⟩
  have hrightUC : NonemptyUniformContinuousOn (Ici (0 : ℝ)) f :=
    domainContinuousOn_Ici_nonemptyUniformContinuousOn_of_domainAtTopLimit
      ((domainContinuousOn_iff_continuousOn ⟨0, self_mem_Ici⟩).mpr hc.continuousOn)
      hrightLimit
  have hneg : Continuous (fun x : ℝ ↦ f (-x)) := hc.comp continuous_neg
  have hnegLimit : DomainAtTopLimit (Ici (0 : ℝ)) (fun x ↦ f (-x)) A := by
    refine ⟨not_bddAbove_Ici 0, ?_⟩
    intro ε hε
    obtain ⟨M, hM⟩ := hA.2 ε hε
    refine ⟨-M, fun x _ hx ↦ ?_⟩
    exact hM (-x) (mem_univ (-x)) (by linarith)
  have hnegUC : NonemptyUniformContinuousOn (Ici (0 : ℝ)) (fun x ↦ f (-x)) :=
    domainContinuousOn_Ici_nonemptyUniformContinuousOn_of_domainAtTopLimit
      ((domainContinuousOn_iff_continuousOn ⟨0, self_mem_Ici⟩).mpr hneg.continuousOn)
      hnegLimit
  have hleftCondition : UniformContinuityConditionOn (Iic (0 : ℝ)) f := by
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hnegUC.2 ε hε
    refine ⟨δ, hδ, fun u hu v hv huv ↦ ?_⟩
    have heq : -u - -v = -(u - v) := by ring
    have hh := hb (-u) (show 0 ≤ -u from neg_nonneg.mpr hu)
      (-v) (show 0 ≤ -v from neg_nonneg.mpr hv)
      (by rw [heq, abs_neg]; exact huv)
    simpa only [neg_neg] using hh
  exact ⟨univ_nonempty,
    uniformContinuityCondition_glue_rays hleftCondition hrightUC.2⟩

end calculus.Chapter03.Section08TwoTailExercises
