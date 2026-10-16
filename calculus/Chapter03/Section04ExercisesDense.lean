import calculus.Chapter03.Section04
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Instances.Rat

/-!
# §3.4 — tính trù mật và hàm liên tục

Nguồn: dòng 2717–2764, trừ Bài tập 10(b).
-/
namespace calculus.Chapter03.Section04ExercisesDense

open Set Filter Topology
open calculus.Chapter03.Section04 calculus.Chapter03.Section02
open calculus.Chapter02.Section03


noncomputable def rationalMixture (g h : ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x∈range ((↑) : ℚ → ℝ) then g x else h x


theorem irrational_accumulation (a : ℝ) : AccumulationPointOf {x | Irrational x} a := by
  intro δ hδ
  obtain ⟨x,hx,hax,hxa⟩ := exists_irrational_btwn (show a<a+δ by linarith)
  exact ⟨x,hx,ne_of_gt hax,by linarith,hxa⟩


theorem domain_continuous_agreement_at_accumulation {D : Set ℝ} {f g : ℝ → ℝ} {a : ℝ}
    (hD : AccumulationPointOf D a) (hf : DomainContinuousAt univ f a)
    (hg : ContinuousAt g a) (he : EqOn f g D) : f a=g a := by
  have hfl : DomainLimit D f a (f a) := (domainLimit_iff_tendsto hD).mpr
    (((domainContinuousAt_univ f a).mp hf).tendsto.mono_left nhdsWithin_le_nhds)
  have hgl : DomainLimit D g a (g a) := (domainLimit_iff_tendsto hD).mpr
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
  exact domainLimit_unique ((domainLimit_congr_punctured (fun x hx _ => he hx)).mp hfl) hgl


theorem rational_mixture_continuity_iff {g h : ℝ → ℝ} {a : ℝ}
    (hg : ContinuousAt g a) (hh : ContinuousAt h a) :
    DomainContinuousAt univ (rationalMixture g h) a ↔ g a=h a := by
  classical
  constructor
  · intro hf
    have hfg : rationalMixture g h a=g a :=
      domain_continuous_agreement_at_accumulation (rational_accumulation a) hf hg (by
        intro x hx
        exact if_pos hx)
    have hfh : rationalMixture g h a=h a :=
      domain_continuous_agreement_at_accumulation (irrational_accumulation a) hf hh (by
        intro x hx
        exact if_neg hx)
    exact hfg.symm.trans hfh
  · intro he
    have hga := (domainContinuousAt_univ g a).mpr hg
    have hha := (domainContinuousAt_univ h a).mpr hh
    have hvalue : rationalMixture g h a=g a := by
      unfold rationalMixture
      split_ifs <;> simp only [he]
    refine ⟨mem_univ _,fun ε hε => ?_⟩
    obtain ⟨δg,hδg,hgδ⟩ := hga.2 ε hε
    obtain ⟨δh,hδh,hhδ⟩ := hha.2 ε hε
    refine ⟨min δg δh,lt_min hδg hδh,?_⟩
    intro x hx hdist
    rw [hvalue]
    unfold rationalMixture
    split_ifs with hr
    · exact hgδ x hx (hdist.trans_le (min_le_left _ _))
    · rw [he]
      exact hhδ x hx (hdist.trans_le (min_le_right _ _))

/-- Bài tập 6(a): hàm ghép hai hằng số 1 và −1 gián đoạn tại mọi điểm. -/
theorem exercise06_constant_mixture_nowhere (a : ℝ) :
    ¬DomainContinuousAt univ (rationalMixture (fun _ => 1) (fun _ => -1)) a := by
  rw [rational_mixture_continuity_iff continuousAt_const continuousAt_const]
  norm_num

/-- Bài tập 6(b): hàm liên tục khi và chỉ khi x=0. -/
theorem exercise06_identity_zero (a : ℝ) :
    DomainContinuousAt univ (rationalMixture id (fun _ => 0)) a ↔ a=0 := by
  simpa only [id_eq] using rational_mixture_continuity_iff
    (g := id) (h := fun _ => 0) continuousAt_id continuousAt_const

/-- Bài tập 6(c): hàm liên tục khi và chỉ khi x=1/2. -/
theorem exercise06_identity_reflection (a : ℝ) :
    DomainContinuousAt univ (rationalMixture id (fun x => 1-x)) a ↔ a=1/2 := by
  have hh : ContinuousAt (fun x : ℝ => 1-x) a := continuousAt_const.sub continuousAt_id
  rw [rational_mixture_continuity_iff (g := id) (h := fun x => 1-x) continuousAt_id hh]
  change a=1-a ↔ a=1/2
  constructor <;> intro h <;> linarith

/-- Bài tập 7: nếu g,h liên tục trên ℝ và g(a)=h(a), hàm ghép liên tục tại a. -/
theorem exercise07_mixture_continuous {g h : ℝ → ℝ} {a : ℝ}
    (hg : DomainContinuousOn univ g) (hh : DomainContinuousOn univ h) (he : g a=h a) :
    DomainContinuousAt univ (rationalMixture g h) a :=
  (rational_mixture_continuity_iff
    ((domainContinuousAt_univ g a).mp (hg a (mem_univ a)))
    ((domainContinuousAt_univ h a).mp (hh a (mem_univ a)))).mpr he


theorem exercise08_absolute_continuous {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hf : DomainContinuousAt D f a) : DomainContinuousAt D (fun x =>  |f x| ) a :=
  (domainContinuousAt_iff_within hf.1).mpr (((domainContinuousAt_iff_within hf.1).mp hf).abs)

/-- Bài tập 8: chiều ngược sai; |f|=1 trên ℝ nhưng f không liên tục tại 0. -/
theorem exercise08_converse_counterexample :
    ∃ f : ℝ → ℝ, DomainContinuousAt univ (fun x =>  |f x| ) 0 ∧
      ¬DomainContinuousAt univ f 0 := by
  classical
  let f := rationalMixture (fun _ => 1) (fun _ => -1)
  have he : (fun x =>  |f x| )=fun _ : ℝ => 1 := by
    funext x
    dsimp only [f,rationalMixture]
    split_ifs <;> norm_num
  refine ⟨f,?_,exercise06_constant_mixture_nowhere 0⟩
  rw [he]
  exact (domainContinuousAt_univ _ 0).mpr continuousAt_const

/-- Bài tập 9: hai hàm liên tục trùng nhau trên ℚ thì trùng nhau trên ℝ. -/
theorem exercise09_equal_on_rationals {f g : ℝ → ℝ}
    (hf : DomainContinuousOn univ f) (hg : DomainContinuousOn univ g)
    (he : ∀ q : ℚ, f q=g q) : f=g := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun a =>
    (domainContinuousAt_univ f a).mp (hf a (mem_univ a))
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun a =>
    (domainContinuousAt_univ g a).mp (hg a (mem_univ a))
  exact Rat.isDenseEmbedding_coe_real.dense.equalizer hfc hgc (funext he)

/-- Bài tập 10(a): nghiệm là các hàm hằng. -/
theorem exercise10_scaling_iff_constant (f : ℝ → ℝ) :
    (DomainContinuousAt univ f 0 ∧ ∀ x, f x=f (3*x)) ↔ ∃ c, ∀ x, f x=c := by
  constructor
  · rintro ⟨hc,hscale⟩
    refine ⟨f 0,fun x => ?_⟩
    have hstep (t : ℝ) : f (t/3)=f t := by
      simpa only [show 3*(t/3)=t by ring] using hscale (t/3)
    have heq : ∀ n : ℕ, f (x/(3:ℝ)^n)=f x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ,div_mul_eq_div_div,hstep,ih]
    have hu : ConvergesTo (fun n : ℕ => x/(3:ℝ)^n) 0 := by
      apply convergesTo_iff_tendsto.mpr
      simpa only [mul_zero,div_eq_mul_inv,one_mul] using
        tendsto_const_nhds.mul (convergesTo_iff_tendsto.mp (reciprocal_geometric_converges 3 (by norm_num)))
    have hfu := (domainContinuousAt_iff_sequences (mem_univ 0)).mp hc
      (fun n => x/(3:ℝ)^n) (fun _ _ => mem_univ _) hu
    have hconstant : ConvergesTo (fun n : ℕ => f (x/(3:ℝ)^n)) (f x) := by
      simpa only [heq] using constant_converges (f x)
    exact limit_unique hconstant hfu
  · rintro ⟨c,hc⟩
    have he : f=fun _ => c := funext hc
    rw [he]
    exact ⟨(domainContinuousAt_univ _ 0).mpr continuousAt_const,fun _ => rfl⟩

/-- Bài tập 11: nghiệm liên tục của phương trình cộng tính trên ℝ có dạng f(x)=cx. -/
theorem exercise11_additive_continuous_iff (f : ℝ → ℝ) :
    (DomainContinuousOn univ f ∧ ∀ x y, f (x+y)=f x+f y) ↔
      ∃ c : ℝ, ∀ x, f x=c*x := by
  constructor
  · rintro ⟨hc,hadd⟩
    have hzero : f 0=0 := by have h := hadd 0 0; norm_num at h; linarith
    let H : ℝ →+ ℝ := { toFun := f, map_zero' := hzero, map_add' := hadd }
    have hcont : Continuous H := continuous_iff_continuousAt.mpr fun a =>
      (domainContinuousAt_univ f a).mp (hc a (mem_univ a))
    refine ⟨f 1,fun x => ?_⟩
    have h := map_real_smul H hcont x (1:ℝ)
    change f (x * 1) = x * f 1 at h
    simpa only [mul_one,mul_comm] using h
  · rintro ⟨c,hc⟩
    have he : f=fun x => c*x := funext hc
    rw [he]
    refine ⟨fun a _ => (domainContinuousAt_univ _ a).mpr
      (continuous_const.mul continuous_id).continuousAt,fun x y => ?_⟩
    ring

end calculus.Chapter03.Section04ExercisesDense
