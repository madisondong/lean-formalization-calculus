import calculus.Chapter03.Section04Supplement
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §3.6 — giả thiết của mục `C03-S06-remark-001`

Nguồn: dòng 3052–3058.
-/
namespace calculus.Chapter03.Section06SourceIssues

open Set Filter Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02Infinite


noncomputable def expNegReciprocalSquare (x : ℝ) : ℝ := Real.exp (-(1/x^2))


noncomputable def rationalIndicatorScaledExponent (x : ℝ) : ℝ := x^2*dirichletFunction x


theorem dirichlet_function_zero_or_one (x : ℝ) :
    dirichletFunction x=0 ∨ dirichletFunction x=1 := by
  classical
  unfold dirichletFunction
  split_ifs <;> simp


theorem exp_neg_reciprocal_square_positive (x : ℝ) : 0<expNegReciprocalSquare x :=
  Real.exp_pos _


theorem exp_neg_reciprocal_square_limit :
    DomainLimit (univ \ {0}) expNegReciprocalSquare 0 0 := by
  apply (domainLimit_iff_tendsto (univ_diff_accumulation 0)).mpr
  have ht := (reciprocal_even_power_point_top 0 2 (by omega) (by decide)).2
  have hn := tendsto_neg_atTop_atBot.comp ht
  change Tendsto (fun x : ℝ => Real.exp (-(1/x^2)))
    (𝓝[(univ \ {0}) \ {0}] 0) (𝓝 0)
  simpa [Function.comp_def,one_div] using Real.tendsto_exp_atBot.comp hn


theorem rational_indicator_scaled_exponent_limit :
    DomainLimit (univ \ {0}) rationalIndicatorScaledExponent 0 0 := by
  apply (domainLimit_iff_tendsto (univ_diff_accumulation 0)).mpr
  have hd (x : ℝ) : 0≤rationalIndicatorScaledExponent x ∧ rationalIndicatorScaledExponent x≤x^2 := by
    rcases dirichlet_function_zero_or_one x with h | h <;>
      simp [rationalIndicatorScaledExponent,h,sq_nonneg]
  have hp : Tendsto (fun x : ℝ => x^2) (𝓝[(univ \ {0}) \ {0}] 0) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ => x^2) := continuous_id.pow 2
    simpa using (hc.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[(univ \ {0}) \ {0}] (0:ℝ) ≤ 𝓝 0)
  exact squeeze_zero (fun x => (hd x).1) (fun x => (hd x).2) hp


theorem oscillating_power_log_product {x : ℝ} (hx : x≠0) :
    rationalIndicatorScaledExponent x*Real.log (expNegReciprocalSquare x)= -dirichletFunction x := by
  simp only [rationalIndicatorScaledExponent,expNegReciprocalSquare,Real.log_exp]
  field_simp [hx]


theorem oscillating_power_value {x : ℝ} (hx : x≠0) :
    (expNegReciprocalSquare x)^(rationalIndicatorScaledExponent x)=Real.exp (-dirichletFunction x) := by
  rw [Real.rpow_def_of_pos (exp_neg_reciprocal_square_positive x)]
  rw [mul_comm,oscillating_power_log_product hx]


theorem oscillating_power_no_limit :
    ¬HasDomainLimit (univ \ {0})
      (fun x : ℝ => (expNegReciprocalSquare x)^(rationalIndicatorScaledExponent x)) 0 := by
  classical
  rintro ⟨L,hL⟩
  have he : Real.exp (-1)<1 := by
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  let ε := (1-Real.exp (-1))/2
  have hε : 0<ε := by dsimp [ε]; linarith
  obtain ⟨δ,hδ,h⟩ := hL.2 ε hε
  obtain ⟨q,hq0,hqδ⟩ := exists_rat_btwn (show (0:ℝ)<δ from hδ)
  obtain ⟨r,hri,hr0,hrδ⟩ := exists_irrational_btwn (show (0:ℝ)<δ from hδ)
  have hq : dirichletFunction q=1 := by unfold dirichletFunction; exact if_pos ⟨q,rfl⟩
  have hr : dirichletFunction r=0 := by unfold dirichletFunction; exact if_neg hri
  have hqD : (q:ℝ)∈univ \ {0} := ⟨mem_univ _,by simpa using hq0.ne'⟩
  have hrD : r∈univ \ {0} := ⟨mem_univ _,by simpa using hr0.ne'⟩
  have hbq := h q hqD (by simpa [abs_of_pos hq0] using hq0)
    (by simpa [abs_of_pos hq0] using hqδ)
  have hbr := h r hrD (by simpa [abs_of_pos hr0] using hr0)
    (by simpa [abs_of_pos hr0] using hrδ)
  change |expNegReciprocalSquare (q:ℝ)^rationalIndicatorScaledExponent (q:ℝ)-L|<ε at hbq
  change |expNegReciprocalSquare r^rationalIndicatorScaledExponent r-L|<ε at hbr
  rw [oscillating_power_value hq0.ne',hq,abs_lt] at hbq
  rw [oscillating_power_value hr0.ne',hr,neg_zero,Real.exp_zero,abs_lt] at hbr
  dsimp [ε] at hbq hbr
  linarith [hbq.2,hbr.1]

/-- Mục `C03-S06-remark-001`: hai giới hạn riêng không bảo đảm giới hạn lũy thừa tồn tại. -/
theorem printed_power_limit_hypotheses_counterexample :
    (∀ x∈univ \ {(0:ℝ)}, 0<expNegReciprocalSquare x) ∧
    DomainLimit (univ \ {0}) expNegReciprocalSquare 0 0 ∧
    DomainLimit (univ \ {0}) rationalIndicatorScaledExponent 0 0 ∧
    ¬HasDomainLimit (univ \ {0})
      (fun x : ℝ => (expNegReciprocalSquare x)^(rationalIndicatorScaledExponent x)) 0 :=
  ⟨fun x _ => exp_neg_reciprocal_square_positive x,
    exp_neg_reciprocal_square_limit,rational_indicator_scaled_exponent_limit,oscillating_power_no_limit⟩

/-- Nếu {x | 0<f(x)}∈l và g·ln f→L∈ℝ theo lọc l thì f^g→exp L. -/
theorem power_limit_of_log_product {α : Type*} {l : Filter α}
    {f g : α → ℝ} {L : ℝ} (hpos : ∀ᶠ x in l, 0<f x)
    (hprod : Tendsto (fun x => g x*Real.log (f x)) l (𝓝 L)) :
    Tendsto (fun x => (f x)^(g x)) l (𝓝 (Real.exp L)) := by
  apply ((Real.continuous_exp.tendsto L).comp hprod).congr'
  filter_upwards [hpos] with x hx
  change Real.exp (g x*Real.log (f x))=(f x)^(g x)
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

end calculus.Chapter03.Section06SourceIssues
