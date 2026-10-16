import calculus.Chapter03.Section04Supplement
import Mathlib.Topology.Algebra.Order.Floor

/-!
# §3.4 — Bài tập 5: điểm gián đoạn nhảy và bước nhảy

Nguồn: dòng 2708–2715.
-/
namespace calculus.Chapter03.Section04ExercisesJumps
open Set Filter Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section04 calculus.Chapter03.Section04Supplement


noncomputable def quadraticSign (x : ℝ) : ℝ := Real.sign (x-x^2)


theorem sign_composition_continuous_at_nonzero {p : ℝ → ℝ} {a : ℝ}
    (hp : ContinuousAt p a) (hne : p a≠0) :
    DomainContinuousAt univ (fun x => Real.sign (p x)) a := by
  have hs := (domainContinuousAt_univ p a).mpr hp
  refine ⟨mem_univ a,fun ε hε => ?_⟩
  obtain ⟨δ,hδ,h⟩ := hs.2 ( |p a| /2) (by positivity)
  refine ⟨δ,hδ,fun x hx hd => ?_⟩
  have hb := abs_lt.mp (h x hx hd)
  have he : Real.sign (p x)=Real.sign (p a) := by
    rcases hne.lt_or_gt with hn | hp
    · rw [abs_of_neg hn] at hb
      rw [Real.sign_of_neg hn,Real.sign_of_neg (by linarith : p x<0)]
    · rw [abs_of_pos hp] at hb
      rw [Real.sign_of_pos hp,Real.sign_of_pos (by linarith : 0<p x)]
  simpa only [he,sub_self,abs_zero] using hε

/-- Bài tập 5(a): hàm liên tục ngoài hai điểm 0 và 1. -/
theorem quadratic_sign_continuous_away {a : ℝ} (h0 : a≠0) (h1 : a≠1) :
    DomainContinuousAt univ quadraticSign a := by
  apply sign_composition_continuous_at_nonzero (continuous_id.sub (continuous_id.pow 2)).continuousAt
  have hprod : a*(1-a)≠0 := mul_ne_zero h0 (sub_ne_zero.mpr h1.symm)
  change a-a^2 ≠ 0
  simpa only [mul_sub,mul_one,pow_two] using hprod


theorem quadratic_sign_side_limits :
    DomainLeftLimit univ quadraticSign 0 (-1) ∧ DomainRightLimit univ quadraticSign 0 1 ∧
    DomainLeftLimit univ quadraticSign 1 1 ∧ DomainRightLimit univ quadraticSign 1 (-1) := by
  refine ⟨⟨leftAccumulation_univ 0,?_⟩,⟨rightAccumulation_univ 0,?_⟩,
    ⟨leftAccumulation_univ 1,?_⟩,⟨rightAccumulation_univ 1,?_⟩⟩
  · intro ε hε
    refine ⟨1,by norm_num,fun x hx hl hr => ?_⟩
    have hp : x-x^2<0 := by nlinarith [sq_nonneg x]
    simp only [quadraticSign,Real.sign_of_neg hp,sub_self,abs_zero]
    exact hε
  · intro ε hε
    refine ⟨1,by norm_num,fun x hx hl hr => ?_⟩
    have hx1 : x<1 := by linarith
    have hp : 0<x-x^2 := by nlinarith [mul_pos hl (sub_pos.mpr hx1)]
    simp only [quadraticSign,Real.sign_of_pos hp,sub_self,abs_zero]
    exact hε
  · intro ε hε
    refine ⟨1,by norm_num,fun x hx hl hr => ?_⟩
    have hx0 : 0<x := by linarith
    have hp : 0<x-x^2 := by nlinarith [mul_pos hx0 (sub_pos.mpr hr)]
    simp only [quadraticSign,Real.sign_of_pos hp,sub_self,abs_zero]
    exact hε
  · intro ε hε
    refine ⟨1,by norm_num,fun x hx hl hr => ?_⟩
    have hp : x-x^2<0 := by nlinarith [mul_pos (show 0<x by linarith) (sub_pos.mpr hl)]
    simp only [quadraticSign,Real.sign_of_neg hp,sub_self,abs_zero]
    exact hε

/-- Bài tập 5(a): bước nhảy tại 0 và 1 lần lượt bằng 2 và −2. -/
theorem exercise05_quadratic_sign_jumps (a : ℝ) :
    (DomainJumpDiscontinuityAt univ quadraticSign a ↔ a=0 ∨ a=1) ∧
    jumpAmount (-1) 1=2 ∧ jumpAmount 1 (-1)= -2 := by
  have h := quadratic_sign_side_limits
  refine ⟨⟨?_,?_⟩,by norm_num [jumpAmount],by norm_num [jumpAmount]⟩
  · intro hj
    by_contra hnone
    push Not at hnone
    exact hj.1 (quadratic_sign_continuous_away hnone.1 hnone.2)
  · rintro (rfl | rfl)
    · exact ⟨not_domain_continuous_of_distinct_side_limits h.1 h.2.1 (by norm_num),
        -1,1,h.1,h.2.1,by norm_num⟩
    · exact ⟨not_domain_continuous_of_distinct_side_limits h.2.2.1 h.2.2.2 (by norm_num),
        1,-1,h.2.2.1,h.2.2.2,by norm_num⟩


theorem floor_integer_side_limits (z : ℤ) :
    DomainLeftLimit univ (fun x => (⌊x⌋ : ℝ)) z ((z:ℝ)-1) ∧
    DomainRightLimit univ (fun x => (⌊x⌋ : ℝ)) z z := by
  constructor
  · refine ⟨leftAccumulation_univ z,fun ε hε => ⟨1,by norm_num,fun x hx hl hr => ?_⟩⟩
    have he : ⌊x⌋=z-1 := Int.floor_eq_iff.mpr
      ⟨by simpa using hl.le,by simpa using hr⟩
    simp only [he,Int.cast_sub,Int.cast_one,sub_self,abs_zero]
    exact hε
  · refine ⟨rightAccumulation_univ z,fun ε hε => ⟨1,by norm_num,fun x hx hl hr => ?_⟩⟩
    have he : ⌊x⌋=z := Int.floor_eq_iff.mpr ⟨hl.le,hr⟩
    simp only [he,sub_self,abs_zero]
    exact hε


theorem floor_continuous_at_noninteger {a : ℝ} (ha : a∉range (Int.cast : ℤ → ℝ)) :
    DomainContinuousAt univ (fun x => (⌊x⌋ : ℝ)) a := by
  have hlo : (⌊a⌋:ℝ)<a := Int.floor_lt_self_iff.mpr ha
  have hhi : a<(⌊a⌋:ℝ)+1 := Int.lt_floor_add_one a
  refine ⟨mem_univ a,fun ε hε => ?_⟩
  let δ := min (a-(⌊a⌋:ℝ)) ((⌊a⌋:ℝ)+1-a)
  have hδ : 0<δ := lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  refine ⟨δ,hδ,fun x hx hd => ?_⟩
  have hb := abs_lt.mp hd
  have hδ₁ : δ≤a-(⌊a⌋:ℝ) := min_le_left _ _
  have hδ₂ : δ≤(⌊a⌋:ℝ)+1-a := min_le_right _ _
  have he : ⌊x⌋=⌊a⌋ := Int.floor_eq_iff.mpr
    ⟨by linarith [hb.1],by linarith [hb.2]⟩
  simp only [he,sub_self,abs_zero]
  exact hε

/-- Bài tập 5(b): các điểm gián đoạn nhảy là các số nguyên; mỗi bước nhảy bằng 1. -/
theorem exercise05_floor_jumps (a : ℝ) :
    (DomainJumpDiscontinuityAt univ (fun x => (⌊x⌋ : ℝ)) a ↔ a∈range (Int.cast : ℤ → ℝ)) ∧
    (∀ z : ℤ, jumpAmount ((z:ℝ)-1) z=1) := by
  refine ⟨⟨?_,?_⟩,fun z => by simp [jumpAmount]⟩
  · intro hj
    by_contra hnot
    exact hj.1 (floor_continuous_at_noninteger hnot)
  · rintro ⟨z,rfl⟩
    have h := floor_integer_side_limits z
    exact ⟨not_domain_continuous_of_distinct_side_limits h.1 h.2 (by linarith),
      (z:ℝ)-1,z,h.1,h.2,by linarith⟩

end calculus.Chapter03.Section04ExercisesJumps
