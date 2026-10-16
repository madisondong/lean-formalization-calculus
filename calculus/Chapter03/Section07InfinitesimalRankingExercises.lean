import calculus.Chapter03.Section07ExercisesCubicTrigonometricParts
import calculus.Chapter03.Section07ExercisesLinearLeadingParts
import calculus.Chapter03.Section07ComposedQuadraticRatioExercises
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.LHopital

/-!
§3.7 — Bài tập 3.7.9(a,b)

Nguồn: dòng 3557–3560.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07InfinitesimalRankingExercises
open calculus.Chapter03.Section02 calculus.Chapter03.Section07
open calculus.Chapter03.Section07Orders calculus.Chapter03.Section07Examples
open calculus.Chapter03.Section07Fundamental
open calculus.Chapter03.Section07ExercisesCubicTrigonometricParts
open calculus.Chapter03.Section07ExercisesLinearLeadingParts
open calculus.Chapter03.Section07ComposedQuadraticRatioExercises
open calculus.Chapter03.Section03Exercises


def squareRootCosineRankingDomain : Set ℝ := {x | 0 ≤ Real.cos x}


theorem square_root_cosine_ranking_domain_nhds : squareRootCosineRankingDomain ∈ 𝓝 (0 : ℝ) := by
  have hp : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), 0 < Real.cos x :=
    (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.eventually
      (Ioi_mem_nhds (by simp : 0 < Real.cos (0 : ℝ)))
  exact hp.mono (fun _ hx ↦ hx.le)


theorem square_root_cosine_ranking_filter :
    domainApproachFilter squareRootCosineRankingDomain (.point 0) = domainApproachFilter univ (.point 0) := by
  have hE : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x ∈ squareRootCosineRankingDomain :=
    square_root_cosine_ranking_domain_nhds
  exact domainApproachFilter_eq_univ_of_eventually_mem (hE.filter_mono nhdsWithin_le_nhds)


theorem sine_sub_identity_div_cube_at_zero :
    Tendsto (fun x : ℝ ↦ (Real.sin x - x) / x ^ 3)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 6 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto Real.sin (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.sin_zero] using! (Real.continuous_sin.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hff : ∀ᶠ x in domainApproachFilter univ (.point 0),
      HasDerivAt (fun y : ℝ ↦ Real.sin y - y) (Real.cos x - 1) x :=
    Eventually.of_forall (fun x ↦ by simpa only [id_eq] using! (Real.hasDerivAt_sin x).sub (hasDerivAt_id x))
  have hgg : ∀ᶠ x in domainApproachFilter univ (.point 0),
      HasDerivAt (fun y : ℝ ↦ y ^ 3) (3 * x ^ 2) x :=
    Eventually.of_forall (fun x ↦ by simpa using! (hasDerivAt_id x).pow 3)
  have hgne : ∀ᶠ x in domainApproachFilter univ (.point 0), 3 * x ^ 2 ≠ 0 :=
    punctured_zero_eventually_ne.mono (fun _ hx ↦ mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero 2 hx))
  have hf : Tendsto (fun x : ℝ ↦ Real.sin x - x) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_zero] using! hs.sub hi
  have hg : Tendsto (fun x : ℝ ↦ x ^ 3) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using! hi.pow 3
  have hratio : Tendsto (fun x : ℝ ↦ (Real.cos x - 1) / (3 * x ^ 2))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 6 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ -((1 - Real.cos x) / x ^ 2) / 3)
        (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 6 : ℝ)) := by
      simpa only [show -(1 / 2 : ℝ) / 3 = -1 / 6 by norm_num] using!
        one_sub_cos_div_square_tendsto.neg.div_const 3
    apply ht.congr
    intro x
    rw [← neg_div, neg_sub, div_div, mul_comm (x ^ 2) 3]
  have he : domainApproachFilter univ (.point 0) = 𝓝[≠] (0 : ℝ) := by
    simp only [domainApproachFilter, compl_eq_univ_sdiff]
  rw [he] at hff hgg hgne hf hg hratio ⊢
  exact HasDerivAt.lhopital_zero_nhdsNE hff hgg hgne hf hg hratio


theorem polynomial_sine_linear_principal_part :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ Real.sin (x ^ 2 - 2 * x)) (fun x ↦ x) 1 (-2) := by
  have hd : HasDerivAt (fun x : ℝ ↦ Real.sin (x ^ 2 - 2 * x)) (-2) 0 := by
    simpa using!
      (((hasDerivAt_id (0 : ℝ)).pow 2).sub ((hasDerivAt_id (0 : ℝ)).const_mul 2)).sin
  exact hasPowerPrincipalPartAlong_one_of_hasDerivAt (univ_accumulation 0) hd (by simp) (by norm_num)


theorem arctangent_square_product_principal_part :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ (1 - Real.sin x) * Real.arctan (x ^ 2)) (fun x ↦ x) 2 1 := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ x ^ 2) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using! hi.pow 2
  have hn : Tendsto (fun x : ℝ ↦ x ^ 2 / x ^ 2) (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    rw [div_self (pow_ne_zero 2 hx)]
  have ha : HasDerivAt Real.arctan 1 0 := by simpa using Real.hasDerivAt_arctan 0
  have hat : Tendsto (fun x : ℝ ↦ Real.arctan (x ^ 2) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [one_mul] using! normalized_composition_increment 2 ha Real.arctan_zero hu hn one_ne_zero
  have hs : Tendsto (fun x : ℝ ↦ 1 - Real.sin x) (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Real.sin_zero, sub_zero] using!
      ((Real.hasDerivAt_sin 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_sub 1
  apply hasPowerPrincipalPartAlong_nat_of_tendsto (univ_accumulation 0) (by decide : 0 < (2 : ℕ)) one_ne_zero
  · have hc : ContinuousAt (fun x : ℝ ↦ (1 - Real.sin x) * Real.arctan (x ^ 2)) 0 := by fun_prop
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), Real.arctan_zero, mul_zero] using!
      hc.tendsto.mono_left nhdsWithin_le_nhds
  · simpa only [Pi.mul_apply, one_mul, mul_div_assoc] using! hs.mul hat


theorem sine_square_sub_square_quartic_principal_part :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ Real.sin x ^ 2 - x ^ 2) (fun x ↦ x) 4 (-1 / 3) := by
  have hs : Tendsto (fun x : ℝ ↦ (Real.sin x + x) / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    have ht : Tendsto (fun x : ℝ ↦ Real.sin x / x + 1)
        (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
      simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using! sine_equivalent_identity_zero.2.2.add_const 1
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    rw [add_div, div_self hx]
  have ht : Tendsto (fun x : ℝ ↦ ((Real.sin x - x) / x ^ 3) * ((Real.sin x + x) / x))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 3 : ℝ)) := by
    simpa only [Pi.mul_apply, show (-1 / 6 : ℝ) * 2 = -1 / 3 by norm_num] using!
      sine_sub_identity_div_cube_at_zero.mul hs
  apply hasPowerPrincipalPartAlong_nat_of_tendsto (univ_accumulation 0)
    (by decide : 0 < (4 : ℕ)) (by norm_num : (-1 / 3 : ℝ) ≠ 0)
  · have hc : ContinuousAt (fun x : ℝ ↦ Real.sin x ^ 2 - x ^ 2) 0 := by fun_prop
    simpa only [Real.sin_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using!
      hc.tendsto.mono_left nhdsWithin_le_nhds
  · apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    field_simp [hx]
    ring

/-- Bài tập 9(a): bậc của f,g,h lần lượt là 1,2,4. -/
theorem first_infinitesimal_ranking :
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ Real.sin (x ^ 2 - 2 * x)) (fun x ↦ x) 1 (-2) ∧
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ (1 - Real.sin x) * Real.arctan (x ^ 2)) (fun x ↦ x) 2 1 ∧
    HasPowerPrincipalPartAlong univ (.point 0)
      (fun x ↦ Real.sin x ^ 2 - x ^ 2) (fun x ↦ x) 4 (-1 / 3) ∧
    (1 : ℝ) < 2 ∧ (2 : ℝ) < 4 :=
  ⟨polynomial_sine_linear_principal_part, arctangent_square_product_principal_part,
    sine_square_sub_square_quartic_principal_part, by norm_num, by norm_num⟩


theorem square_root_cosine_sub_one_div_square_at_zero :
    Tendsto (fun x : ℝ ↦ (Real.sqrt (Real.cos x) - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 4 : ℝ)) := by
  have hs : Tendsto (fun x : ℝ ↦ Real.sqrt (Real.cos x))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ ↦ Real.sqrt (Real.cos x)) 0 := by fun_prop
    simpa only [Real.cos_zero, Real.sqrt_one] using! hc.tendsto.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun x : ℝ ↦ Real.sqrt (Real.cos x) + 1)
      (domainApproachFilter univ (.point 0)) (𝓝 (2 : ℝ)) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using! hs.add_const 1
  have ht : Tendsto (fun x : ℝ ↦ -((1 - Real.cos x) / x ^ 2) / (Real.sqrt (Real.cos x) + 1))
      (domainApproachFilter univ (.point 0)) (𝓝 (-1 / 4 : ℝ)) := by
    simpa only [Pi.div_apply, show -(1 / 2 : ℝ) / 2 = -1 / 4 by norm_num] using!
      one_sub_cos_div_square_tendsto.neg.div hd (by norm_num : (2 : ℝ) ≠ 0)
  apply ht.congr'
  have hE : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x ∈ squareRootCosineRankingDomain :=
    square_root_cosine_ranking_domain_nhds
  filter_upwards [punctured_zero_eventually_ne,
    hE.filter_mono nhdsWithin_le_nhds,
    hd.eventually_ne (by norm_num : (2 : ℝ) ≠ 0)] with x hx hcos hden
  have hsq := Real.sq_sqrt hcos
  generalize Real.sqrt (Real.cos x) = y at hsq hden ⊢
  field_simp [hx, hden]
  nlinarith [hsq]


theorem hyperbolic_cosine_sub_one_div_square_at_zero :
    Tendsto (fun x : ℝ ↦ (Real.cosh x - 1) / x ^ 2)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
  have hi : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun x : ℝ ↦ Real.sinh x / x)
      (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
    simpa only [Real.sinh_zero, sub_zero, Real.cosh_zero] using! derivative_quotient_zero (Real.hasDerivAt_sinh 0)
  have hff : ∀ᶠ x in domainApproachFilter univ (.point 0),
      HasDerivAt (fun y : ℝ ↦ Real.cosh y - 1) (Real.sinh x) x :=
    Eventually.of_forall (fun x ↦ (Real.hasDerivAt_cosh x).sub_const 1)
  have hgg : ∀ᶠ x in domainApproachFilter univ (.point 0),
      HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x :=
    Eventually.of_forall (fun x ↦ by simpa using! (hasDerivAt_id x).pow 2)
  have hgne : ∀ᶠ x in domainApproachFilter univ (.point 0), 2 * x ≠ 0 :=
    punctured_zero_eventually_ne.mono (fun _ hx ↦ mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hx)
  have hf : Tendsto (fun x : ℝ ↦ Real.cosh x - 1)
      (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.cosh_zero, sub_self] using!
      ((Real.hasDerivAt_cosh 0).sub_const 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun x : ℝ ↦ x ^ 2) (domainApproachFilter univ (.point 0)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using! hi.pow 2
  have hratio : Tendsto (fun x : ℝ ↦ Real.sinh x / (2 * x))
      (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
    apply (hs.div_const 2).congr
    intro x
    rw [div_div, mul_comm x 2]
  have he : domainApproachFilter univ (.point 0) = 𝓝[≠] (0 : ℝ) := by
    simp only [domainApproachFilter, compl_eq_univ_sdiff]
  rw [he] at hff hgg hgne hf hg hratio ⊢
  exact HasDerivAt.lhopital_zero_nhdsNE hff hgg hgne hf hg hratio


theorem hyperbolic_cubic_principal_part :
    HasPowerPrincipalPartAlong squareRootCosineRankingDomain (.point 0)
      (fun x ↦ x * (Real.sinh x ^ 2 - Real.cosh x + 1)) (fun x ↦ x) 3 (1 / 2) := by
  have ha : AccumulationPointOf squareRootCosineRankingDomain 0 := by
    simpa only [univ_inter] using accumulationPointOf_inter_nhds (univ_accumulation 0) square_root_cosine_ranking_domain_nhds
  apply hasPowerPrincipalPartAlong_nat_of_tendsto ha (by decide : 0 < (3 : ℕ)) (by norm_num : (1 / 2 : ℝ) ≠ 0)
  · have hc : ContinuousAt (fun x : ℝ ↦ x * (Real.sinh x ^ 2 - Real.cosh x + 1)) 0 := by fun_prop
    simpa only [zero_mul] using! hc.tendsto.mono_left nhdsWithin_le_nhds
  · rw [square_root_cosine_ranking_filter]
    have hc : Tendsto Real.cosh (domainApproachFilter univ (.point 0)) (𝓝 (1 : ℝ)) := by
      simpa only [Real.cosh_zero] using! (Real.hasDerivAt_cosh 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have ht : Tendsto (fun x : ℝ ↦ Real.cosh x * ((Real.cosh x - 1) / x ^ 2))
        (domainApproachFilter univ (.point 0)) (𝓝 (1 / 2 : ℝ)) := by
      simpa only [Pi.mul_apply, one_mul] using! hc.mul hyperbolic_cosine_sub_one_div_square_at_zero
    apply ht.congr'
    filter_upwards [punctured_zero_eventually_ne] with x hx
    have hid : Real.sinh x ^ 2 - Real.cosh x + 1 = Real.cosh x * (Real.cosh x - 1) := by
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    rw [hid]
    field_simp [hx]

/-- Bài tập 9(b): bậc của g,f,h lần lượt là 1,2,3. -/
theorem second_infinitesimal_ranking :
    HasPowerPrincipalPartAlong squareRootCosineRankingDomain (.point 0)
      (fun x ↦ Real.exp (x * (x + 1)) - 1) (fun x ↦ x) 1 1 ∧
    HasPowerPrincipalPartAlong squareRootCosineRankingDomain (.point 0)
      (fun x ↦ Real.sqrt (Real.cos x) - 1) (fun x ↦ x) 2 (-1 / 4) ∧
    HasPowerPrincipalPartAlong squareRootCosineRankingDomain (.point 0)
      (fun x ↦ x * (Real.sinh x ^ 2 - Real.cosh x + 1)) (fun x ↦ x) 3 (1 / 2) ∧
    (1 : ℝ) < 2 ∧ (2 : ℝ) < 3 := by
  have ha : AccumulationPointOf squareRootCosineRankingDomain 0 := by
    simpa only [univ_inter] using accumulationPointOf_inter_nhds (univ_accumulation 0) square_root_cosine_ranking_domain_nhds
  have hg : HasDerivAt (fun x : ℝ ↦ Real.exp (x * (x + 1)) - 1) 1 0 := by
    simpa only [Pi.mul_apply, id_eq, zero_add, zero_mul, mul_zero, add_zero, one_mul, Real.exp_zero, mul_one] using!
      ((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).add_const 1)).exp.sub_const 1
  refine ⟨hasPowerPrincipalPartAlong_one_of_hasDerivAt ha hg (by simp) one_ne_zero, ?_,
    hyperbolic_cubic_principal_part, by norm_num, by norm_num⟩
  apply hasPowerPrincipalPartAlong_nat_of_tendsto ha (by decide : 0 < (2 : ℕ)) (by norm_num : (-1 / 4 : ℝ) ≠ 0)
  · have hc : ContinuousAt (fun x : ℝ ↦ Real.sqrt (Real.cos x) - 1) 0 := by fun_prop
    simpa only [Real.cos_zero, Real.sqrt_one, sub_self] using! hc.tendsto.mono_left nhdsWithin_le_nhds
  · rw [square_root_cosine_ranking_filter]
    exact square_root_cosine_sub_one_div_square_at_zero

end calculus.Chapter03.Section07InfinitesimalRankingExercises
