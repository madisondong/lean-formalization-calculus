import calculus.Chapter03.Section04
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# §3.4 — các ví dụ gián đoạn

Nguồn: dòng 2564–2579.
-/
namespace calculus.Chapter03.Section04Supplement

open Set Filter Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section04 calculus.Chapter02.Section03


noncomputable def sineQuotientPatch (m x : ℝ) : ℝ :=
  if x=0 then m else Real.sin x/x


theorem sine_quotient_patch_limit (m : ℝ) : DomainLimit univ (sineQuotientPatch m) 0 1 := by
  have hs : DomainLimit univ Real.sinc 0 1 := by
    simpa only [Real.sinc_zero] using
      (domainContinuousAt_iff_limit (mem_univ 0) (univ_accumulation 0)).mp
        ((domainContinuousAt_univ Real.sinc 0).mpr Real.continuous_sinc.continuousAt)
  apply (domainLimit_congr_punctured (f := Real.sinc) ?_).mp hs
  intro x _ hx
  simp only [sineQuotientPatch,if_neg hx,Real.sinc_of_ne_zero hx]

/-- Mục `C03-S04-example-003` (a): m≠1 cho điểm gián đoạn bỏ được. -/
theorem sine_quotient_patch_removable {m : ℝ} (hm : m≠1) :
    DomainRemovableDiscontinuityAt univ (sineQuotientPatch m) 0 := by
  refine ⟨not_domain_continuous_of_limit_ne_value (sine_quotient_patch_limit m) ?_,
    1,sine_quotient_patch_limit m⟩
  simpa [sineQuotientPatch] using hm.symm


theorem not_domain_continuous_of_distinct_side_limits {f : ℝ → ℝ} {a L R : ℝ}
    (hL : DomainLeftLimit univ f a L) (hR : DomainRightLimit univ f a R) (hne : L≠R) :
    NotDomainContinuousAt univ f a := by
  intro hc
  have h := (domainLimit_iff_left_right (leftAccumulation_univ a) (rightAccumulation_univ a)).mp
    ((domainContinuousAt_iff_limit (mem_univ a) (univ_accumulation a)).mp hc)
  exact hne ((domainLeftLimit_unique hL h.1).trans (domainRightLimit_unique h.2 hR))

/-- Mục `C03-S04-example-003` (b): hàm dấu có bước nhảy 2 từ −1 lên 1. -/
theorem sign_jump_at_zero : DomainJumpDiscontinuityAt univ Real.sign 0 ∧
    DomainLeftLimit univ Real.sign 0 (-1) ∧ DomainRightLimit univ Real.sign 0 1 ∧
    jumpAmount (-1) 1=2 := by
  have h := sign_one_sided_limits
  refine ⟨⟨not_domain_continuous_of_distinct_side_limits h.1 h.2 (by norm_num),
    -1,1,h.1,h.2,by norm_num⟩,h.1,h.2,?_⟩
  norm_num [jumpAmount]

/-- Mục `C03-S04-example-003` (c): cos(1/x) được gán giá trị 1 tại 0. -/
noncomputable def cosineReciprocalPatch (x : ℝ) : ℝ :=
  if x=0 then 1 else Real.cos (1/x)


theorem cosine_reciprocal_patch_no_right_limit :
    ¬∃ L : ℝ, DomainRightLimit univ cosineReciprocalPatch 0 L := by
  rintro ⟨L,hL⟩
  have hseq := (domainRightLimit_iff_sequences (rightAccumulation_univ 0)).mp hL
    reciprocalPi (fun n hn => ⟨mem_univ _,(reciprocalPi_positive hn).ne',reciprocalPi_positive hn⟩)
    reciprocalPi_converges
  have heq : ∀ n, 1≤n → cosineReciprocalPatch (reciprocalPi n)=(-1:ℝ)^n := by
    intro n hn
    rw [cosineReciprocalPatch,if_neg (reciprocalPi_positive hn).ne',cosine_reciprocalPi]
  apply alternating_sequence_divergent
  refine ⟨L,?_⟩
  intro ε hε
  obtain ⟨N,hN,h⟩ := hseq ε hε
  refine ⟨N,hN,fun n hn => ?_⟩
  simpa only [heq n (hN.trans hn)] using h n hn

/-- Mục `C03-S04-example-003` (c): không có giới hạn hữu hạn bên phải tại 0, nên 0 là điểm gián đoạn loại hai. -/
theorem cosine_reciprocal_patch_second_kind :
    DomainSecondKindDiscontinuityAt univ cosineReciprocalPatch 0 := by
  refine ⟨?_,Or.inr cosine_reciprocal_patch_no_right_limit⟩
  intro hc
  have h := (domainLimit_iff_left_right (leftAccumulation_univ 0) (rightAccumulation_univ 0)).mp
    ((domainContinuousAt_iff_limit (mem_univ 0) (univ_accumulation 0)).mp hc)
  exact cosine_reciprocal_patch_no_right_limit ⟨cosineReciprocalPatch 0,h.2⟩


theorem dirichlet_no_right_limit (a : ℝ) :
    ¬∃ L : ℝ, DomainRightLimit univ dirichletFunction a L := by
  classical
  rintro ⟨L,hL⟩
  obtain ⟨δ,hδ,h⟩ := hL.2 (1/2) (by norm_num)
  obtain ⟨q,hqa,hqδ⟩ := exists_rat_btwn (show a<a+δ by linarith)
  obtain ⟨r,hri,hra,hrδ⟩ := exists_irrational_btwn (show a<a+δ by linarith)
  have hq : dirichletFunction q=1 := by unfold dirichletFunction; exact if_pos ⟨q,rfl⟩
  have hr : dirichletFunction r=0 := by unfold dirichletFunction; exact if_neg hri
  have hbq := h q (mem_univ _) hqa hqδ
  have hbr := h r (mem_univ _) hra hrδ
  rw [hq,abs_lt] at hbq
  rw [hr,abs_lt] at hbr
  linarith [hbq.2,hbr.1]

/-- Mục `C03-S04-example-003` (d): hàm Dirichlet gián đoạn loại hai tại mọi điểm. -/
theorem dirichlet_second_kind_everywhere (a : ℝ) :
    DomainSecondKindDiscontinuityAt univ dirichletFunction a :=
  ⟨not_domain_continuous_of_no_limit_at_accumulation (mem_univ a) (univ_accumulation a)
    (dirichletFunction_no_domainLimit a),Or.inr (dirichlet_no_right_limit a)⟩

end calculus.Chapter03.Section04Supplement
