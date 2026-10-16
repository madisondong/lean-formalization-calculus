import calculus.Chapter03.Section04
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# §3.4 — Bài tập 10(b): phương trình hàm với tính liên tục tại 0

Nguồn: dòng 2758.
-/
namespace calculus.Chapter03.Section04Functional

open Set Filter Topology
open calculus.Chapter03.Section04 calculus.Chapter02.Section03


theorem quadratic_functional_normalized {f : ℝ → ℝ} (hf : ∀ x, f (3*x)= -f (x^2))
    (x : ℝ) : f x= -f (x^2/9) := by
  have h := hf (x/3)
  simpa only [show 3*(x/3)=x by ring,show (x/3)^2=x^2/9 by ring] using h


theorem quadratic_functional_zero {f : ℝ → ℝ} (hf : ∀ x, f (3*x)= -f (x^2)) : f 0=0 := by
  have h := hf 0
  norm_num at h
  linarith


theorem quadratic_functional_even {f : ℝ → ℝ} (hf : ∀ x, f (3*x)= -f (x^2))
    (x : ℝ) : f (-x)=f x := by
  have h1 := quadratic_functional_normalized hf x
  have h2 := quadratic_functional_normalized hf (-x)
  rw [neg_sq] at h2
  exact h2.trans h1.symm


theorem quadratic_functional_absolute {f : ℝ → ℝ} (hf : ∀ x, f (3*x)= -f (x^2))
    (x : ℝ) : f  |x| =f x := by
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    exact quadratic_functional_even hf x


theorem quadratic_functional_zero_on_interval {f : ℝ → ℝ}
    (hc : DomainContinuousAt univ f 0) (hf : ∀ x, f (3*x)= -f (x^2))
    {x : ℝ} (hx :  |x| ≤9) : f x=0 := by
  have habs := quadratic_functional_absolute hf x
  have hz := quadratic_functional_zero hf
  by_cases hx9 :  |x| =9
  · have h := quadratic_functional_normalized hf 9
    norm_num at h
    rw [hx9] at habs
    linarith
  · have hlt :  |x| <9 := lt_of_le_of_ne hx hx9
    let r : ℝ :=  |x| /9
    let u : ℕ → ℝ := fun n => 9*r^(2^n)
    have hr : 0≤r := by dsimp only [r]; positivity
    have hr1 : r<1 := by dsimp only [r]; linarith
    have hut : Tendsto u atTop (𝓝 0) := by
      have hpow : Tendsto (fun n : ℕ => (2:ℕ)^n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      simpa only [u,Function.comp_apply,mul_zero] using tendsto_const_nhds.mul
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).comp hpow)
    have hstep (n : ℕ) : u (n+1)=(u n)^2/9 := by
      dsimp only [u]
      rw [pow_succ,pow_mul]
      ring
    have hfa : ∀ n : ℕ,  |f (u n)| = |f x|  := by
      intro n
      induction n with
      | zero =>
        have hu0 : u 0= |x|  := by dsimp [u,r]; ring
        rw [hu0,habs]
      | succ n ih =>
        have h := quadratic_functional_normalized hf (u n)
        have he : f (u (n+1))= -f (u n) := by rw [hstep]; linarith
        rw [he,abs_neg,ih]
    have hfu := (domainContinuousAt_iff_sequences (mem_univ 0)).mp hc u
      (fun _ _ => mem_univ _) (convergesTo_iff_tendsto.mpr hut)
    have habslim : ConvergesTo (fun n =>  |f (u n)| ) 0 := by
      simpa only [hz,abs_zero] using abs_converges hfu
    have hconst : ConvergesTo (fun n =>  |f (u n)| )  |f x|  := by
      simpa only [hfa] using constant_converges  |f x| 
    exact abs_eq_zero.mp (limit_unique hconst habslim)


def LogTwoAntiperiodic (g : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, g (t+Real.log 2)= -g t


noncomputable def logarithmicSolution (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if  |x| ≤9 then 0 else g (Real.log (Real.log ( |x| /9)))


theorem logarithmic_solution_continuous_zero (g : ℝ → ℝ) :
    DomainContinuousAt univ (logarithmicSolution g) 0 := by
  refine ⟨mem_univ _,fun ε hε => ⟨9,by norm_num,fun x _ hx => ?_⟩⟩
  have hsmall :  |x| ≤9 := by simpa only [sub_zero] using hx.le
  simpa only [logarithmicSolution,if_pos hsmall,abs_zero,show (0:ℝ)≤9 by norm_num,
    if_pos,sub_self,abs_zero] using hε


theorem logarithmic_solution_equation {g : ℝ → ℝ} (hg : LogTwoAntiperiodic g) :
    ∀ x : ℝ, logarithmicSolution g (3*x)= -logarithmicSolution g (x^2) := by
  intro x
  have hn := abs_nonneg x
  by_cases hx :  |x| ≤3
  · have h3 :  |3*x| ≤9 := by rw [abs_mul]; norm_num; linarith
    have h2 :  |x^2| ≤9 := by rw [abs_pow]; nlinarith
    simp only [logarithmicSolution,if_pos h3,if_pos h2,neg_zero]
  · have hx3 : 3< |x|  := lt_of_not_ge hx
    have h3 : ¬ |3*x| ≤9 := by rw [abs_mul]; norm_num; linarith
    have h2 : ¬ |x^2| ≤9 := by rw [abs_pow]; nlinarith
    have harg3 :  |3*x| /9= |x| /3 := by rw [abs_mul]; norm_num; ring
    have harg2 :  |x^2| /9=( |x| /3)^2 := by rw [abs_pow]; ring
    have hv : 1< |x| /3 := by linarith
    have hlv : 0<Real.log ( |x| /3) := Real.log_pos hv
    have hlogs : Real.log (Real.log ( |x^2| /9))=
        Real.log (Real.log ( |3*x| /9))+Real.log 2 := by
      rw [harg2,harg3,Real.log_pow,Real.log_mul (by norm_num) (ne_of_gt hlv)]
      norm_num
      ring
    simp only [logarithmicSolution,if_neg h3,if_neg h2,hlogs]
    rw [hg _,neg_neg]

/-- Bài tập 10(b): phân loại nghiệm bằng hàm g thỏa g(t+log 2)=−g(t). -/
theorem exercise10_quadratic_complete_characterization (f : ℝ → ℝ) :
    (DomainContinuousAt univ f 0 ∧ ∀ x, f (3*x)= -f (x^2)) ↔
      ∃ g : ℝ → ℝ, LogTwoAntiperiodic g ∧ f=logarithmicSolution g := by
  constructor
  · rintro ⟨hc,hf⟩
    let g : ℝ → ℝ := fun t => f (9*Real.exp (Real.exp t))
    refine ⟨g,?_,?_⟩
    · intro t
      have he : 9*Real.exp (Real.exp (t+Real.log 2))=
          (9*Real.exp (Real.exp t))^2/9 := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),
          show Real.exp t*2=Real.exp t+Real.exp t by ring,Real.exp_add]
        ring
      dsimp only [g]
      rw [he]
      have h := quadratic_functional_normalized hf (9*Real.exp (Real.exp t))
      linarith
    · funext x
      by_cases hx :  |x| ≤9
      · rw [logarithmicSolution,if_pos hx]
        exact quadratic_functional_zero_on_interval hc hf hx
      · have hx9 : 9< |x|  := lt_of_not_ge hx
        have hr : 1< |x| /9 := by linarith
        have hlog : 0<Real.log ( |x| /9) := Real.log_pos hr
        rw [logarithmicSolution,if_neg hx]
        dsimp only [g]
        rw [Real.exp_log hlog,Real.exp_log (by linarith : (0:ℝ)< |x| /9),
          show 9*( |x| /9)= |x|  by ring]
        exact (quadratic_functional_absolute hf x).symm
  · rintro ⟨g,hg,rfl⟩
    exact ⟨logarithmic_solution_continuous_zero g,logarithmic_solution_equation hg⟩


theorem logarithmic_solution_parameter_value (g : ℝ → ℝ) (t : ℝ) :
    logarithmicSolution g (9*Real.exp (Real.exp t))=g t := by
  have hp : 0<9*Real.exp (Real.exp t) := by positivity
  have he : 1<Real.exp (Real.exp t) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (Real.exp_pos t)
  have hcut : ¬ |9*Real.exp (Real.exp t)| ≤9 := by rw [abs_of_pos hp]; linarith
  rw [logarithmicSolution,if_neg hcut,abs_of_pos hp,
    show 9*Real.exp (Real.exp t)/9=Real.exp (Real.exp t) by ring,
    Real.log_exp,Real.log_exp]

/-- Bài tập 10(b) có nghiệm khác 0 bên ngoài [−9,9]. -/
theorem quadratic_functional_nonzero_solution :
    ∃ f : ℝ → ℝ, DomainContinuousAt univ f 0 ∧
      (∀ x, f (3*x)= -f (x^2)) ∧ ∃ x, f x=1 := by
  let g : ℝ → ℝ := fun t => Real.sin (Real.pi*t/Real.log 2)
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hg : LogTwoAntiperiodic g := by
    intro t
    have he : Real.pi*(t+Real.log 2)/Real.log 2=Real.pi*t/Real.log 2+Real.pi := by
      field_simp
    dsimp only [g]
    rw [he,Real.sin_add_pi]
  refine ⟨logarithmicSolution g,logarithmic_solution_continuous_zero g,
    logarithmic_solution_equation hg,9*Real.exp (Real.exp (Real.log 2/2)),?_⟩
  rw [logarithmic_solution_parameter_value]
  dsimp only [g]
  have he : Real.pi*(Real.log 2/2)/Real.log 2=Real.pi/2 := by
    field_simp
  rw [he,Real.sin_pi_div_two]

end calculus.Chapter03.Section04Functional
