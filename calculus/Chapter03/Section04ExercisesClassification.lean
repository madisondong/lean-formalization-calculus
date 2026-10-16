import calculus.Chapter03.Section04Supplement
import Mathlib.Topology.Piecewise
import calculus.Chapter03.Section02Infinite

/-!
# §3.4 — hàm được gán lại giá trị tại một điểm và điều kiện tham số

Nguồn: dòng 2676–2706.
-/
namespace calculus.Chapter03.Section04ExercisesClassification

open Set Filter Topology
open calculus.Chapter03.Section04 calculus.Chapter03.Section04Supplement
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided


theorem patch_domain_continuous_away {F : ℝ → ℝ} {m a : ℝ} (ha : a≠0)
    (hc : ContinuousAt F a) : DomainContinuousAt univ (fun x => if x=0 then m else F x) a := by
  have hF := (domainContinuousAt_univ F a).mpr hc
  refine ⟨mem_univ a,fun ε hε => ?_⟩
  obtain ⟨δ,hδ,h⟩ := hF.2 ε hε
  refine ⟨min δ ( |a| /2),lt_min hδ (by positivity),?_⟩
  intro x hx hdist
  have hxa := hdist.trans_le (min_le_right _ _)
  have hx0 : x≠0 := by
    intro he
    rw [he,zero_sub,abs_neg] at hxa
    linarith [abs_pos.mpr ha]
  simp only [if_neg hx0,if_neg ha]
  exact h x hx (hdist.trans_le (min_le_left _ _))


noncomputable def oscillatingProductPatch (x : ℝ) : ℝ :=
  if x=0 then 0 else x*Real.sin (1/x)

/-- Bài tập 3(a): hàm liên tục trên ℝ. -/
theorem exercise03_product_continuous : DomainContinuousOn univ oscillatingProductPatch := by
  intro a ha
  by_cases ha0 : a=0
  · subst a
    refine ⟨ha,fun ε hε => ⟨ε,hε,?_⟩⟩
    intro x _ hx
    by_cases hx0 : x=0
    · simpa [oscillatingProductPatch,hx0] using hε
    · simp only [oscillatingProductPatch,if_true,if_neg hx0,sub_zero,abs_mul] at *
      calc
         |x| * |Real.sin (1/x)|  ≤  |x| *1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ < ε := by simpa only [mul_one] using hx
  · exact patch_domain_continuous_away ha0
      (continuousAt_id.mul (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.div continuousAt_id ha0)))


noncomputable def absoluteSineQuotientPatch (x : ℝ) : ℝ :=
  if x=0 then 1 else  |Real.sin x/x| 

/-- Bài tập 3(b): hàm liên tục trên ℝ. -/
theorem exercise03_absolute_quotient_continuous :
    DomainContinuousOn univ absoluteSineQuotientPatch := by
  have he : absoluteSineQuotientPatch=fun x =>  |Real.sinc x|  := by
    funext x
    by_cases hx : x=0 <;> simp [absoluteSineQuotientPatch,Real.sinc,hx]
  rw [he]
  exact fun a _ => (domainContinuousAt_univ _ a).mpr Real.continuous_sinc.abs.continuousAt


noncomputable def sineAbsoluteDenominatorPatch (x : ℝ) : ℝ :=
  if x=0 then 1 else Real.sin x/ |x| 


theorem sine_absolute_denominator_side_limits :
    DomainLeftLimit univ sineAbsoluteDenominatorPatch 0 (-1) ∧
      DomainRightLimit univ sineAbsoluteDenominatorPatch 0 1 := by
  have hs : DomainContinuousAt univ Real.sinc 0 :=
    (domainContinuousAt_univ _ 0).mpr Real.continuous_sinc.continuousAt
  constructor
  · refine ⟨leftAccumulation_univ 0,fun ε hε => ?_⟩
    obtain ⟨δ,hδ,h⟩ := hs.2 ε hε
    refine ⟨δ,hδ,fun x hx hxl hxr => ?_⟩
    have hd :  |x-0| <δ := abs_lt.mpr ⟨by linarith,by linarith⟩
    have hb := h x hx hd
    have he : sineAbsoluteDenominatorPatch x= -Real.sinc x := by
      simp only [sineAbsoluteDenominatorPatch,if_neg (ne_of_lt hxr),abs_of_neg hxr,
        Real.sinc_of_ne_zero (ne_of_lt hxr),div_neg]
    rw [he,Real.sinc_zero] at *
    simpa only [show -Real.sinc x-(-1)=-(Real.sinc x-1) by ring,abs_neg] using hb
  · refine ⟨rightAccumulation_univ 0,fun ε hε => ?_⟩
    obtain ⟨δ,hδ,h⟩ := hs.2 ε hε
    refine ⟨δ,hδ,fun x hx hxl hxr => ?_⟩
    have hd :  |x-0| <δ := abs_lt.mpr ⟨by linarith,by linarith⟩
    have hb := h x hx hd
    have he : sineAbsoluteDenominatorPatch x=Real.sinc x := by
      simp only [sineAbsoluteDenominatorPatch,if_neg (ne_of_gt hxl),abs_of_pos hxl,
        Real.sinc_of_ne_zero (ne_of_gt hxl)]
    simpa only [he,Real.sinc_zero] using hb

/-- Bài tập 3(c): hàm liên tục khi và chỉ khi x≠0. -/
theorem exercise03_sine_absolute_denominator_continuity (a : ℝ) :
    DomainContinuousAt univ sineAbsoluteDenominatorPatch a ↔ a≠0 := by
  constructor
  · intro hc ha
    subst a
    have h := sine_absolute_denominator_side_limits
    exact not_domain_continuous_of_distinct_side_limits h.1 h.2 (by norm_num) hc
  · intro ha
    exact patch_domain_continuous_away ha
      (Real.continuous_sin.continuousAt.div continuousAt_id.abs (abs_ne_zero.mpr ha))

/-- Bài tập 3(d): hai điều kiện chồng lấn cho công thức mâu thuẫn. -/
theorem exercise03_printed_overlap_no_function :
    ¬∃ f : ℝ → ℝ, (∀ x, x≤1 → f x=Real.cos (Real.pi*x/2)) ∧
      (∀ x, 0<x → f x= |x-1| ) := by
  rintro ⟨f,hleft,hright⟩
  have hl := hleft (1/2) (by norm_num)
  have hr := hright (1/2) (by norm_num)
  have he : Real.cos (Real.pi*(1/2)/2)=(1/2:ℝ) := by
    rw [←hl,hr]
    norm_num
  rw [show Real.pi*(1/2)/2=Real.pi/4 by ring,Real.cos_pi_div_four] at he
  have hh : Real.sqrt 2=1 := by linarith
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  rw [hh] at hs
  norm_num at hs


noncomputable def parameterQuadraticPatch (A x : ℝ) : ℝ :=
  if 2<x then x^2+A else A*x-1


theorem parameter_quadratic_right_limit (A : ℝ) :
    DomainRightLimit univ (parameterQuadraticPatch A) 2 (4+A) := by
  have hc : Continuous (fun x : ℝ => x^2+A) := (continuous_id.pow 2).add continuous_const
  have hs := (domainContinuousAt_univ _ 2).mpr hc.continuousAt
  refine ⟨rightAccumulation_univ 2,fun ε hε => ?_⟩
  obtain ⟨δ,hδ,h⟩ := hs.2 ε hε
  refine ⟨δ,hδ,fun x hx hxl hxr => ?_⟩
  have hd :  |x-2| <δ := abs_lt.mpr ⟨by linarith,by linarith⟩
  simpa only [parameterQuadraticPatch,if_pos hxl,show (2:ℝ)^2=4 by norm_num] using h x hx hd

/-- Bài tập 4: hàm liên tục trên ℝ khi và chỉ khi A=5. -/
theorem exercise04_parameter_iff (A : ℝ) :
    DomainContinuousOn univ (parameterQuadraticPatch A) ↔ A=5 := by
  constructor
  · intro h
    have hs := (domainContinuousAt_iff_limit (mem_univ 2) (univ_accumulation 2)).mp (h 2 (mem_univ 2))
    have hr := ((domainLimit_iff_left_right (leftAccumulation_univ 2) (rightAccumulation_univ 2)).mp hs).2
    have he := domainRightLimit_unique (parameter_quadratic_right_limit A) hr
    norm_num [parameterQuadraticPatch] at he
    linarith
  · intro hA
    subst A
    have hc : Continuous (parameterQuadraticPatch 5) := by
      apply Continuous.if
      · intro a ha
        change a ∈ frontier (Ioi (2 : ℝ)) at ha
        have he : a=2 := by simpa only [frontier_Ioi,mem_singleton_iff] using ha
        subst a
        norm_num
      · exact (continuous_id.pow 2).add continuous_const
      · exact (continuous_const.mul continuous_id).sub continuous_const
    exact fun a _ => (domainContinuousAt_univ _ a).mpr hc.continuousAt


theorem exercise03_printed_bound_variable_limit {n : ℕ} (hn : 1≤n) :
    calculus.Chapter03.Section02Infinite.DomainAtTopLimit univ
      (fun x : ℝ => Real.sin (Real.pi/(2*(1+x^(2*n))))) 0 := by
  apply (calculus.Chapter03.Section02Infinite.domainAtTopLimit_iff_tendsto
    not_bddAbove_univ).mpr
  simp only [principal_univ,inf_top_eq]
  have hp : Tendsto (fun x : ℝ => x^(2*n)) atTop atTop := tendsto_pow_atTop (by omega)
  have hs : Tendsto (fun x : ℝ => 1+x^(2*n)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hp
  have hd : Tendsto (fun x : ℝ => 2*(1+x^(2*n))) atTop atTop :=
    hs.const_mul_atTop (by norm_num : (0:ℝ)<2)
  have hq : Tendsto (fun x : ℝ => Real.pi/(2*(1+x^(2*n)))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using tendsto_const_nhds.mul hd.inv_tendsto_atTop
  simpa only [Function.comp_def,Real.sin_zero] using Real.continuous_sin.continuousAt.tendsto.comp hq

/-- Bài tập 3(e): công thức giới hạn xác định hàm hằng 0, liên tục trên ℝ. -/
theorem exercise03_printed_limit_function_continuous :
    DomainContinuousOn univ (fun _ : ℝ => (0:ℝ)) := by
  intro a ha
  exact (domainContinuousAt_univ _ a).mpr continuous_const.continuousAt

end calculus.Chapter03.Section04ExercisesClassification
