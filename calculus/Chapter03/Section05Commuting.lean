import calculus.Chapter03.Section05Exercises
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# §3.5 — Bài tập 8: điểm bất động chung

Nguồn: dòng 2969–2971.
-/
namespace calculus.Chapter03.Section05Commuting
open Set Filter Topology
open calculus.Chapter03.Section04 calculus.Chapter03.Section05
open calculus.Chapter03.Section05Exercises calculus.Chapter03.Section01Properties


theorem monotone_interval_common_fixed_point
    (F G : Icc (0:ℝ) 1 → Icc (0:ℝ) 1) (hF : Continuous F) (hG : Continuous G)
    (hm : Monotone F) (hcomm : Function.Commute F G)
    (c : Icc (0:ℝ) 1) (hc : G c=c) : ∃ z, F z=z ∧ G z=z := by
  let : Fact ((0:ℝ)≤1) := ⟨by norm_num⟩
  let u : ℕ → Icc (0:ℝ) 1 := fun n => F^[n] c
  have hlim : ∃ z, Tendsto u atTop (𝓝 z) := by
    rcases le_total c (F c) with hup | hdown
    · have hu : Monotone u := monotone_nat_of_le_succ (fun n => by
        simpa only [u,Function.iterate_succ_apply] using (hm.iterate n) hup)
      exact ⟨_,tendsto_atTop_iSup hu⟩
    · have hu : Antitone u := antitone_nat_of_succ_le (fun n => by
        simpa only [u,Function.iterate_succ_apply] using (hm.iterate n) hdown)
      exact ⟨_,tendsto_atTop_iInf hu⟩
  obtain ⟨z,hz⟩ := hlim
  have hstep : ∀ n, F (u n)=u (n+1) := fun n =>
    (Function.iterate_succ_apply' F n c).symm
  have hGfix : ∀ n, G (u n)=u n := by
    intro n
    have hh := (hcomm.iterate_left n).eq c
    simpa only [hc,u] using hh.symm
  have hFz : F z=z := by
    have hFseq := hF.continuousAt.tendsto.comp hz
    have hshift := hz.comp (tendsto_add_atTop_nat 1)
    have heq : Tendsto (fun n => F (u n)) atTop (𝓝 z) :=
      hshift.congr' (Eventually.of_forall (fun n => (hstep n).symm))
    exact tendsto_nhds_unique hFseq heq
  have hGz : G z=z := by
    have hGseq := hG.continuousAt.tendsto.comp hz
    have heq : Tendsto (fun n => G (u n)) atTop (𝓝 z) :=
      hz.congr' (Eventually.of_forall (fun n => (hGfix n).symm))
    exact tendsto_nhds_unique hGseq heq
  exact ⟨z,hFz,hGz⟩

/-- Bài tập 8: hai ánh xạ liên tục [0,1]→[0,1] giao hoán có điểm bất động chung nếu f đơn điệu. -/
theorem exercise08_commuting_common_fixed_point {f g : ℝ → ℝ}
    (hf : DomainContinuousOn (Icc (0:ℝ) 1) f)
    (hg : DomainContinuousOn (Icc (0:ℝ) 1) g)
    (hmf : MapsTo f (Icc (0:ℝ) 1) (Icc (0:ℝ) 1))
    (hmg : MapsTo g (Icc (0:ℝ) 1) (Icc (0:ℝ) 1))
    (hcomm : ∀ x∈Icc (0:ℝ) 1, f (g x)=g (f x))
    (hmono : FunctionMonotonic (closedIntervalDomain 0 1) f) :
    ∃ c∈Icc (0:ℝ) 1, f c=c ∧ g c=c := by
  have hD : (Icc (0:ℝ) 1).Nonempty := by norm_num
  rcases hmono with hinc | hdec
  · let F : Icc (0:ℝ) 1 → Icc (0:ℝ) 1 := fun x => ⟨f x,hmf x.property⟩
    let G : Icc (0:ℝ) 1 → Icc (0:ℝ) 1 := fun x => ⟨g x,hmg x.property⟩
    have hF : Continuous F := ((domainContinuousOn_iff_continuousOn hD).mp hf).domRestrict.subtype_mk _
    have hG : Continuous G := ((domainContinuousOn_iff_continuousOn hD).mp hg).domRestrict.subtype_mk _
    have hm : Monotone F := by
      intro x y hxy
      rcases hxy.eq_or_lt with he | hlt
      · exact le_of_eq (congrArg F he)
      · exact hinc x x.property y y.property hlt
    have hC : Function.Commute F G := by
      intro x
      apply Subtype.ext
      exact hcomm x x.property
    obtain ⟨c,hcD,hc⟩ := exercise06_fixed_point hD hg hmg
    have hc' : G ⟨c,hcD⟩=⟨c,hcD⟩ := Subtype.ext hc
    obtain ⟨z,hFz,hGz⟩ := monotone_interval_common_fixed_point F G hF hG hm hC ⟨c,hcD⟩ hc'
    exact ⟨z,z.property,congrArg Subtype.val hFz,congrArg Subtype.val hGz⟩
  · obtain ⟨c,hcD,hfc⟩ := exercise06_fixed_point hD hf hmf
    have hgcD : g c∈Icc (0:ℝ) 1 := hmg hcD
    have hfgc : f (g c)=g c := by simpa only [hfc] using hcomm c hcD
    have he : g c=c := by
      rcases lt_trichotomy (g c) c with hlt | he | hgt
      · have hh := hdec (g c) hgcD c hcD hlt
        rw [hfc,hfgc] at hh
        exact (not_le_of_gt hlt hh).elim
      · exact he
      · have hh := hdec c hcD (g c) hgcD hgt
        rw [hfc,hfgc] at hh
        exact (not_le_of_gt hgt hh).elim
    exact ⟨c,hcD,hfc,he⟩

end calculus.Chapter03.Section05Commuting
