import calculus.Chapter03.Section04

/-!
# §3.4 — bài tập ε–δ cơ bản

Nguồn: dòng 2653–2674.
-/
namespace calculus.Chapter03.Section04ExercisesBasic

open Set
open calculus.Chapter03.Section04


theorem affine_epsilon_delta (A B a : ℝ) :
    ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ,  |x-a| <δ →  |(A*x+B)-(A*a+B)| <ε := by
  intro ε hε
  have hA : 0< |A| +1 := by positivity
  refine ⟨ε/( |A| +1),div_pos hε hA,?_⟩
  intro x hx
  rw [show (A*x+B)-(A*a+B)=A*(x-a) by ring,abs_mul]
  calc
     |A| * |x-a|  ≤ ( |A| +1)* |x-a|  := by nlinarith [abs_nonneg (x-a)]
    _ < ( |A| +1)*(ε/( |A| +1)) := mul_lt_mul_of_pos_left hx hA
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hA)


theorem square_add_epsilon_delta (B a : ℝ) :
    ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ,  |x-a| <δ →  |(x^2+B)-(a^2+B)| <ε := by
  intro ε hε
  have ha : 0<2* |a| +1 := by positivity
  refine ⟨min 1 (ε/(2* |a| +1)),lt_min zero_lt_one (div_pos hε ha),?_⟩
  intro x hx
  have hx1 :  |x-a| <1 := hx.trans_le (min_le_left _ _)
  have hxε :  |x-a| <ε/(2* |a| +1) := hx.trans_le (min_le_right _ _)
  have hxsum :  |x+a| ≤2* |a| +1 := by
    calc
       |x+a|  =  |(x-a)+2*a|  := by congr 1; ring
      _ ≤  |x-a| + |2*a|  := abs_add_le _ _
      _ ≤ 2* |a| +1 := by rw [abs_mul]; norm_num; linarith
  rw [show (x^2+B)-(a^2+B)=(x-a)*(x+a) by ring,abs_mul]
  calc
     |x-a| * |x+a|  ≤  |x-a| *(2* |a| +1) := mul_le_mul_of_nonneg_left hxsum (abs_nonneg _)
    _ < (ε/(2* |a| +1))*(2* |a| +1) := mul_lt_mul_of_pos_right hxε ha
    _ = ε := div_mul_cancel₀ ε (ne_of_gt ha)

/-- Bài tập 1(a,b): điều kiện ε–δ tại các điểm 3 và 2. -/
theorem exercise01_affine_quadratic :
    DomainContinuousAt univ (fun x : ℝ => 3*x-7) 3 ∧
      DomainContinuousAt univ (fun x : ℝ => x^2+1) 2 := by
  constructor
  · refine ⟨mem_univ _,fun ε hε => ?_⟩
    obtain ⟨δ,hδ,h⟩ := affine_epsilon_delta 3 (-7) 3 ε hε
    exact ⟨δ,hδ,fun x _ => by simpa only [sub_eq_add_neg] using h x⟩
  · refine ⟨mem_univ _,fun ε hε => ?_⟩
    obtain ⟨δ,hδ,h⟩ := square_add_epsilon_delta 1 2 ε hε
    exact ⟨δ,hδ,fun x _ => h x⟩

/-- Bài tập 1(c): δ=min(1,ε) trên miền x≠−1. -/
theorem exercise01_rational :
    DomainContinuousAt (univ \ {(-1:ℝ)}) (fun x => (x+3)/(x+1)) 1 := by
  refine ⟨by norm_num,fun ε hε => ⟨min 1 ε,lt_min zero_lt_one hε,?_⟩⟩
  intro x _ hx
  have hx1 := (abs_lt.mp (hx.trans_le (min_le_left _ _))).1
  have hxpos : 0<x := by linarith
  have hd : 0<x+1 := by linarith
  have he : (x+3)/(x+1)-(1+3)/(1+1)=-(x-1)/(x+1) := by
    field_simp
    ring
  rw [he,abs_div,abs_neg,abs_of_pos hd]
  apply (div_lt_iff₀ hd).mpr
  have hsmall := hx.trans_le (min_le_right _ _)
  nlinarith

/-- Bài tập 2(a): hàm afin liên tục trên ℝ. -/
theorem exercise02_affine (A B : ℝ) : DomainContinuousOn univ (fun x => A*x+B) := by
  intro a ha
  refine ⟨ha,fun ε hε => ?_⟩
  obtain ⟨δ,hδ,h⟩ := affine_epsilon_delta A B a ε hε
  exact ⟨δ,hδ,fun x _ => h x⟩

/-- Bài tập 2(b): x²−3 liên tục trên ℝ. -/
theorem exercise02_square : DomainContinuousOn univ (fun x : ℝ => x^2-3) := by
  intro a ha
  refine ⟨ha,fun ε hε => ?_⟩
  obtain ⟨δ,hδ,h⟩ := square_add_epsilon_delta (-3) a ε hε
  exact ⟨δ,hδ,fun x _ => by simpa only [sub_eq_add_neg] using h x⟩

/-- Bài tập 2(c): |x| liên tục với δ=ε. -/
theorem exercise02_absolute : DomainContinuousOn univ (fun x : ℝ =>  |x| ) := by
  intro a ha
  refine ⟨ha,fun ε hε => ⟨ε,hε,fun x _ hx => ?_⟩⟩
  exact (abs_abs_sub_abs_le_abs_sub x a).trans_lt hx


theorem sqrt_difference_square_bound {x a : ℝ} (hx : 0≤x) (ha : 0≤a) :
     |Real.sqrt x-Real.sqrt a| ^2≤ |x-a|  := by
  rw [sq_abs]
  have hsx := Real.sqrt_nonneg x
  have hsa := Real.sqrt_nonneg a
  have hxx := Real.sq_sqrt hx
  have haa := Real.sq_sqrt ha
  rcases le_total a x with hax | hxa
  · rw [abs_of_nonneg (sub_nonneg.mpr hax)]
    have hs := Real.sqrt_le_sqrt hax
    nlinarith [mul_nonneg hsa (sub_nonneg.mpr hs)]
  · rw [abs_of_nonpos (sub_nonpos.mpr hxa)]
    have hs := Real.sqrt_le_sqrt hxa
    nlinarith [mul_nonneg hsx (sub_nonneg.mpr hs)]

/-- Bài tập 2(d): √x liên tục trên [0,+∞), với δ=ε². -/
theorem exercise02_square_root : DomainContinuousOn (Ici (0:ℝ)) Real.sqrt := by
  intro a ha
  refine ⟨ha,fun ε hε => ⟨ε^2,sq_pos_of_pos hε,fun x hx hdist => ?_⟩⟩
  have hb := sqrt_difference_square_bound hx ha
  have hn := abs_nonneg (Real.sqrt x-Real.sqrt a)
  nlinarith

/-- Bài tập 2(e): 1/x liên tục trên ℝ\{0}. -/
theorem exercise02_reciprocal :
    DomainContinuousOn (univ \ {(0:ℝ)}) (fun x => 1/x) := by
  intro a ha
  have ha0 : a≠0 := ha.2
  have hap : 0< |a|  := abs_pos.mpr ha0
  refine ⟨ha,fun ε hε => ⟨min ( |a| /2) (ε* |a| ^2/2),
    lt_min (by positivity) (by positivity),fun x hx hdist => ?_⟩⟩
  have hx0 : x≠0 := hx.2
  have hxp : 0< |x|  := abs_pos.mpr hx0
  have hsmall := hdist.trans_le (min_le_right _ _)
  have hhalf := hdist.trans_le (min_le_left _ _)
  have htri :  |a| ≤ |x-a| + |x|  := by
    calc
       |a|  =  |(a-x)+x|  := by congr 1; ring
      _ ≤  |a-x| + |x|  := abs_add_le _ _
      _ =  |x-a| + |x|  := by rw [abs_sub_comm]
  have he : 1/x-1/a=(a-x)/(x*a) := by field_simp
  rw [he,abs_div,abs_mul,abs_sub_comm]
  apply (div_lt_iff₀ (mul_pos hxp hap)).mpr
  have hm := mul_pos hε hap
  nlinarith

end calculus.Chapter03.Section04ExercisesBasic
