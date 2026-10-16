import calculus.Chapter03.Section02OneSided
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# §3.4 — tính liên tục

Nguồn: dòng 2413–2606.
-/
namespace calculus.Chapter03.Section04

open Set Filter Topology
open calculus.Chapter03.Section02
open calculus.Chapter03.Section02OneSided
open calculus.Chapter02.Section03


noncomputable def domainRestriction (D : Set ℝ) (f : ℝ → ℝ) : D → ℝ := fun x => f x

/-- Mục `C03-S04-definition-001`: a∈D và điều kiện ε–δ, cho phép x=a. -/
def DomainContinuousAt (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  a∈D ∧ ∀ ε > 0, ∃ δ > 0, ∀ x∈D, |x-a|<δ → |f x-f a|<ε

/-- Mục `C03-S04-remark-002` (i): phủ định tính liên tục, kể cả khi a∉D. -/
def NotDomainContinuousAt (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ¬DomainContinuousAt D f a


def DomainContinuousOn (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ a∈D, DomainContinuousAt D f a


theorem domainContinuousAt_iff_within {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ} (ha : a∈D) :
    DomainContinuousAt D f a ↔ ContinuousWithinAt f D a := by
  simp only [DomainContinuousAt,ha,true_and,Metric.continuousWithinAt_iff,Real.dist_eq]


theorem domainContinuousOn_iff_continuousOn {D : Set ℝ} {f : ℝ → ℝ} (_hD : D.Nonempty) :
    DomainContinuousOn D f ↔ ContinuousOn f D := by
  constructor
  · intro h a ha
    exact (domainContinuousAt_iff_within ha).mp (h a ha)
  · intro h a ha
    exact (domainContinuousAt_iff_within ha).mpr (h a ha)


theorem domainContinuousAt_univ (f : ℝ → ℝ) (a : ℝ) :
    DomainContinuousAt univ f a ↔ ContinuousAt f a := by
  rw [domainContinuousAt_iff_within (mem_univ a),continuousWithinAt_univ]

/-- Mục `C03-S04-remark-001`: mọi hàm đều liên tục tại điểm cô lập thuộc miền xác định. -/
theorem domainContinuousAt_of_isolated {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : IsolatedPointOf D a) : DomainContinuousAt D f a := by
  refine ⟨ha.1,?_⟩
  have hn := ha.2
  unfold AccumulationPointOf at hn
  push Not at hn
  obtain ⟨δ,hδ,hno⟩ := hn
  intro ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx hdist
  have he : x=a := by
    by_contra hne
    have hb := abs_lt.mp hdist
    have hh := hno x hx hne (by linarith [hb.1])
    linarith [hb.2]
  rw [he,sub_self,abs_zero]
  exact hε


theorem affine_three_two_explicit_continuity (a : ℝ) :
    ∀ ε > 0, ∃ δ > 0, δ=ε/3 ∧ ∀ x : ℝ, |x-a|<δ → |(3*x+2)-(3*a+2)|<ε := by
  intro ε hε
  refine ⟨ε/3,by positivity,rfl,?_⟩
  intro x hx
  have he : (3*x+2)-(3*a+2)=3*(x-a) := by ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)]
  linarith

/-- Mục `C03-S04-example-001`: hàm afin liên tục trên ℝ. -/
theorem affine_three_two_domain_continuous : DomainContinuousOn univ (fun x : ℝ => 3*x+2) := by
  intro a ha
  refine ⟨ha,?_⟩
  intro ε hε
  obtain ⟨δ,hδ,_,hx⟩ := affine_three_two_explicit_continuity a ε hε
  exact ⟨δ,hδ,fun x _ => hx x⟩

/-- Mục `C03-S04-theorem-001`: tại điểm tụ a∈D, liên tục tương đương lim f(x)=f(a). -/
theorem domainContinuousAt_iff_limit {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : a∈D) (hacc : AccumulationPointOf D a) :
    DomainContinuousAt D f a ↔ DomainLimit D f a (f a) := by
  constructor
  · rintro ⟨_,h⟩
    exact ⟨hacc,fun ε hε => by
      obtain ⟨δ,hδ,hx⟩ := h ε hε
      exact ⟨δ,hδ,fun x hD _ => hx x hD⟩⟩
  · rintro ⟨_,h⟩
    refine ⟨ha,?_⟩
    intro ε hε
    obtain ⟨δ,hδ,hx⟩ := h ε hε
    refine ⟨δ,hδ,?_⟩
    intro x hD hdist
    by_cases he : x=a
    · rw [he,sub_self,abs_zero]
      exact hε
    · exact hx x hD (abs_pos.mpr (sub_ne_zero.mpr he)) hdist

/-- Mục `C03-S04-example-002`: đa thức liên tục và có giới hạn tại mọi điểm. -/
theorem quadratic_three_two_one_domain_continuous :
    DomainContinuousOn univ (fun x : ℝ => 3*x^2-2*x+1) ∧
      ∀ a, DomainLimit univ (fun x : ℝ => 3*x^2-2*x+1) a (3*a^2-2*a+1) := by
  have hc : Continuous (fun x : ℝ => 3*x^2-2*x+1) :=
    ((continuous_const.mul (continuous_id.pow 2)).sub (continuous_const.mul continuous_id)).add continuous_const
  have hs : DomainContinuousOn univ (fun x : ℝ => 3*x^2-2*x+1) :=
    fun a _ => (domainContinuousAt_univ _ a).mpr hc.continuousAt
  exact ⟨hs,fun a => (domainContinuousAt_iff_limit (mem_univ a) (univ_accumulation a)).mp (hs a (mem_univ a))⟩

/-- Mục `C03-S04-remark-002` (i): điểm ngoài miền không thỏa định nghĩa liên tục của giáo trình. -/
theorem undefined_point_not_domain_continuous {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : a∉D) : NotDomainContinuousAt D f a := fun h => ha h.1

/-- Mục `C03-S04-remark-002` (ii): tập một điểm bác bỏ phát biểu thiếu giả thiết điểm tụ. -/
theorem no_limit_discontinuity_claim_counterexample :
    DomainContinuousAt {0} (fun _ : ℝ => 0) 0 ∧ ¬HasDomainLimit {0} (fun _ : ℝ => 0) 0 := by
  constructor
  · refine ⟨by simp,fun ε hε => ⟨1,by norm_num,fun x _ _ => ?_⟩⟩
    simpa only [sub_self,abs_zero] using hε
  · rintro ⟨L,hL⟩
    obtain ⟨x,hx,hn,_,_⟩ := hL.1 1 (by norm_num)
    exact hn (by simpa only [mem_singleton_iff] using hx)

/-- Mục `C03-S04-remark-002` (ii): tại điểm tụ a∈D, hàm không có giới hạn hữu hạn thì không liên tục. -/
theorem not_domain_continuous_of_no_limit_at_accumulation {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : a∈D) (hacc : AccumulationPointOf D a) (hn : ¬HasDomainLimit D f a) :
    NotDomainContinuousAt D f a := fun hc => hn ⟨f a,(domainContinuousAt_iff_limit ha hacc).mp hc⟩

/-- Mục `C03-S04-remark-002` (iii): giới hạn khác giá trị hàm suy ra hàm không liên tục tại điểm đó. -/
theorem not_domain_continuous_of_limit_ne_value {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (hL : DomainLimit D f a L) (hne : L≠f a) : NotDomainContinuousAt D f a := by
  intro hc
  exact hne (domainLimit_unique hL ((domainContinuousAt_iff_limit hc.1 hL.1).mp hc))

/-- Mục `C03-S04-definition-002` (a): gián đoạn bỏ được, với giới hạn hữu hạn. -/
def DomainRemovableDiscontinuityAt (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  NotDomainContinuousAt D f a ∧ ∃ L : ℝ, DomainLimit D f a L

/-- Mục `C03-S04-definition-002` (b): hai giới hạn hữu hạn một phía tồn tại và khác nhau. -/
def DomainJumpDiscontinuityAt (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  NotDomainContinuousAt D f a ∧ ∃ L R : ℝ, DomainLeftLimit D f a L ∧ DomainRightLimit D f a R ∧ L≠R


def jumpAmount (L R : ℝ) : ℝ := R-L

/-- Mục `C03-S04-definition-002` (c): gián đoạn loại hai là không liên tục và ít nhất một phía không có giới hạn hữu hạn. -/
def DomainSecondKindDiscontinuityAt (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  NotDomainContinuousAt D f a ∧ ((¬∃ L : ℝ, DomainLeftLimit D f a L) ∨ (¬∃ R : ℝ, DomainRightLimit D f a R))

/-- Mục `C03-S04-theorem-002`: tiêu chuẩn dãy, cho phép xₙ=a. -/
theorem domainContinuousAt_iff_sequences {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : a∈D) : DomainContinuousAt D f a ↔
      ∀ u : ℕ → ℝ, (∀ n, 1≤n → u n∈D) → ConvergesTo u a → ConvergesTo (fun n => f (u n)) (f a) := by
  classical
  rw [domainContinuousAt_iff_within ha]
  constructor
  · intro hf u hu ht
    apply convergesTo_iff_tendsto.mpr
    have hm : ∀ᶠ n in atTop, u n∈D := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact hu n hn
    exact hf.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨convergesTo_iff_tendsto.mp ht,hm⟩)
  · intro h
    apply tendsto_iff_seq_tendsto.mpr
    intro u hu
    have hm : ∀ᶠ n in atTop, u n∈D := (tendsto_nhdsWithin_iff.mp hu).2
    let v : ℕ → ℝ := fun n => if u n∈D then u n else a
    have huv : u=ᶠ[atTop]v := hm.mono fun n hn => by simp only [v,if_pos hn]
    have hv : ConvergesTo v a := convergesTo_iff_tendsto.mpr ((hu.mono_right nhdsWithin_le_nhds).congr' huv)
    have hfv := convergesTo_iff_tendsto.mp (h v (fun n _ => by
      by_cases hn : u n∈D
      · simpa only [v,if_pos hn] using hn
      · simpa only [v,if_neg hn] using ha) hv)
    exact hfv.congr' (huv.symm.mono fun n hn => congrArg f hn)

/-- Mục `C03-S04-theorem-003` (i): tính liên tục của tổng và tích trên miền D. -/
theorem domain_continuity_add_mul {D : Set ℝ} {f g : ℝ → ℝ} {a : ℝ}
    (hf : DomainContinuousAt D f a) (hg : DomainContinuousAt D g a) :
    DomainContinuousAt D (fun x => f x+g x) a ∧ DomainContinuousAt D (fun x => f x*g x) a := by
  have hfw := (domainContinuousAt_iff_within hf.1).mp hf
  have hgw := (domainContinuousAt_iff_within hg.1).mp hg
  exact ⟨(domainContinuousAt_iff_within hf.1).mpr (hfw.add hgw),(domainContinuousAt_iff_within hf.1).mpr (hfw.mul hgw)⟩

/-- Mục `C03-S04-theorem-003` (ii): tính liên tục khi nhân với hằng số thực. -/
theorem domain_continuity_const_mul {D : Set ℝ} {f : ℝ → ℝ} {a c : ℝ}
    (hf : DomainContinuousAt D f a) : DomainContinuousAt D (fun x => c*f x) a :=
  (domainContinuousAt_iff_within hf.1).mpr (((domainContinuousAt_iff_within hf.1).mp hf).const_mul c)

/-- Mục `C03-S04-theorem-003` (iii): thương trên D′={x∈D|gx≠0}. -/
theorem domain_continuity_div {D : Set ℝ} {f g : ℝ → ℝ} {a : ℝ}
    (hf : DomainContinuousAt D f a) (hg : DomainContinuousAt D g a) (hga : g a≠0) :
    DomainContinuousAt {x | x∈D ∧ g x≠0} (fun x => f x/g x) a := by
  have ha : a∈{x | x∈D ∧ g x≠0} := ⟨hf.1,hga⟩
  apply (domainContinuousAt_iff_within ha).mpr
  have hs : {x | x∈D ∧ g x≠0}⊆D := fun _ hx => hx.1
  exact (((domainContinuousAt_iff_within hf.1).mp hf).mono hs).div
    (((domainContinuousAt_iff_within hg.1).mp hg).mono hs) hga

/-- Mục `C03-S04-theorem-004`: hàm hợp, với f(D)⊆E và g liên tục tại f(a). -/
theorem domain_continuity_comp {D E : Set ℝ} {f g : ℝ → ℝ} {a : ℝ}
    (hmap : MapsTo f D E) (hf : DomainContinuousAt D f a) (hg : DomainContinuousAt E g (f a)) :
    DomainContinuousAt D (fun x => g (f x)) a :=
  (domainContinuousAt_iff_within hf.1).mpr (((domainContinuousAt_iff_within hg.1).mp hg).comp
    ((domainContinuousAt_iff_within hf.1).mp hf) hmap)

end calculus.Chapter03.Section04
