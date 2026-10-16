import calculus.Chapter03.Section04ExercisesBasic
import calculus.Chapter03.Section01Hyperbolic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# §3.6 — Bài tập 1: chứng minh bằng định nghĩa ε–δ

Nguồn: dòng 3088–3096.
-/
namespace calculus.Chapter03.Section06ExercisesDefinition

open Set
open calculus.Chapter03.Section04 calculus.Chapter03.Section04ExercisesBasic

/-- Bài tập 1(a): điều kiện ε–δ cho nghịch đảo bình phương trên ℝ\{0}. -/
theorem exercise01_reciprocal_square :
    DomainContinuousOn (univ \ {(0:ℝ)}) (fun x : ℝ => 1/x^2) := by
  intro a ha
  refine ⟨ha,fun ε hε => ?_⟩
  obtain ⟨η,hη,hpow⟩ := square_add_epsilon_delta 0 (1/a) ε hε
  obtain ⟨δ,hδ,hinv⟩ := (exercise02_reciprocal a ha).2 η hη
  refine ⟨δ,hδ,fun x hx hd => ?_⟩
  have hh := hpow (1/x) (hinv x hx hd)
  simpa [div_pow] using hh


theorem logarithm_epsilon_delta {a : ℝ} (ha : 0<a) :
    ∀ ε>0, ∃ δ>0, ∀ x : ℝ, 0<x →  |x-a| <δ →  |Real.log x-Real.log a| <ε := by
  intro ε hε
  have hel : Real.exp (-ε)<1 := by
    simpa using Real.exp_lt_exp.mpr (show -ε<0 by linarith)
  have her : 1<Real.exp ε := by
    simpa using Real.exp_lt_exp.mpr hε
  have hδl : 0<a-a*Real.exp (-ε) := by nlinarith
  have hδr : 0<a*Real.exp ε-a := by nlinarith
  refine ⟨min (a-a*Real.exp (-ε)) (a*Real.exp ε-a),lt_min hδl hδr,?_⟩
  intro x hx hd
  have hlo : a*Real.exp (-ε)<x := by
    have hh := (abs_lt.mp (hd.trans_le (min_le_left _ _))).1
    linarith
  have hhi : x<a*Real.exp ε := by
    have hh := (abs_lt.mp (hd.trans_le (min_le_right _ _))).2
    linarith
  have hl := Real.log_lt_log (mul_pos ha (Real.exp_pos (-ε))) hlo
  have hr := Real.log_lt_log hx hhi
  rw [Real.log_mul ha.ne' (Real.exp_ne_zero (-ε)),Real.log_exp] at hl
  rw [Real.log_mul ha.ne' (Real.exp_ne_zero ε),Real.log_exp] at hr
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- Bài tập 1(b): điều kiện ε–δ của logarit trên (0,+∞). -/
theorem exercise01_logarithm : DomainContinuousOn (Ioi (0:ℝ)) Real.log := by
  intro a ha
  exact ⟨ha,fun ε hε => by
    obtain ⟨δ,hδ,h⟩ := logarithm_epsilon_delta ha ε hε
    exact ⟨δ,hδ,fun x hx hd => h x hx hd⟩⟩


theorem exponential_epsilon_delta (a : ℝ) :
    ∀ ε>0, ∃ δ>0, ∀ x : ℝ,  |x-a| <δ →  |Real.exp x-Real.exp a| <ε := by
  intro ε hε
  let η := min ε (Real.exp a/2)
  have hη : 0<η := lt_min hε (by positivity)
  have hηε : η≤ε := min_le_left _ _
  have hηhalf : η≤Real.exp a/2 := min_le_right _ _
  have hp : 0<Real.exp a-η := by linarith [Real.exp_pos a]
  have hq : 0<Real.exp a+η := by positivity
  have hl : Real.log (Real.exp a-η)<a := by
    have hh := Real.log_lt_log hp (show Real.exp a-η<Real.exp a by linarith)
    simpa using hh
  have hr : a<Real.log (Real.exp a+η) := by
    have hh := Real.log_lt_log (Real.exp_pos a) (show Real.exp a<Real.exp a+η by linarith)
    simpa using hh
  refine ⟨min (a-Real.log (Real.exp a-η)) (Real.log (Real.exp a+η)-a),
    lt_min (by linarith) (by linarith),?_⟩
  intro x hd
  have hxl : Real.log (Real.exp a-η)<x := by
    have hh := (abs_lt.mp (hd.trans_le (min_le_left _ _))).1
    linarith
  have hxr : x<Real.log (Real.exp a+η) := by
    have hh := (abs_lt.mp (hd.trans_le (min_le_right _ _))).2
    linarith
  have hexpl := Real.exp_lt_exp.mpr hxl
  have hexpr := Real.exp_lt_exp.mpr hxr
  rw [Real.exp_log hp] at hexpl
  rw [Real.exp_log hq] at hexpr
  exact (abs_lt.mpr ⟨by linarith,by linarith⟩).trans_le hηε

/-- Bài tập 1(c): điều kiện ε–δ của cosh trên ℝ. -/
theorem exercise01_hyperbolic_cosine : DomainContinuousOn univ Real.cosh := by
  intro a ha
  refine ⟨ha,fun ε hε => ?_⟩
  obtain ⟨δp,hδp,hp⟩ := exponential_epsilon_delta a ε hε
  obtain ⟨δm,hδm,hm⟩ := exponential_epsilon_delta (-a) ε hε
  refine ⟨min δp δm,lt_min hδp hδm,fun x hx hd => ?_⟩
  have hplus := hp x (hd.trans_le (min_le_left _ _))
  have hminus := hm (-x) (by
    rw [show (-x)-(-a)=-(x-a) by ring,abs_neg]
    exact hd.trans_le (min_le_right _ _))
  have he : Real.cosh x-Real.cosh a=
      ((Real.exp x-Real.exp a)+(Real.exp (-x)-Real.exp (-a)))/2 := by
    rw [Real.cosh_eq,Real.cosh_eq]
    ring
  rw [he,abs_div]
  norm_num
  have htri := abs_add_le (Real.exp x-Real.exp a) (Real.exp (-x)-Real.exp (-a))
  linarith

end calculus.Chapter03.Section06ExercisesDefinition
