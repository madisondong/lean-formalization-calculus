import calculus.Chapter03.Section07NegativeBasePowerDomainObstruction
import calculus.Chapter03.Section07Orders

/-!
§3.7 — Nhận xét 3.7.19: bậc nguyên và điều kiện miền

Nguồn: dòng 3374–3376; bảng miền dòng 548–559; điều kiện điểm tụ dòng 1406–1407.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07NegativeBasePowerOrderObstruction

open calculus.Chapter03.Section02 calculus.Chapter03.Section07
open calculus.Chapter03.Section07Orders calculus.Chapter03.Section07NegativeBasePowerDomainObstruction


theorem negativeAbs_cubic_power_order :
    InfinitesimalPowerOrderAlong univ (.point 0) negativeAbsCube negativeAbs 3 := by
  have hp : NontrivialDomainApproach univ (.point 0) := univ_zero_punctured_neBot
  refine ⟨by norm_num, ⟨hp, ?_⟩, ⟨hp, ?_⟩, ?_, hp, ?_, 1, one_ne_zero, ?_⟩
  · exact (domainLimit_iff_tendsto univ_zero_accumulation).mp
      negativeAbsCube_domainLimit_zero
  · exact (domainLimit_iff_tendsto univ_zero_accumulation).mp
      negativeAbs_domainLimit_zero
  · exact Filter.Eventually.of_forall negativeAbs_cubic_real_power_admissible
  · have hmem : ∀ᶠ x in domainApproachFilter univ (.point 0),
        x ∈ (univ : Set ℝ) \ {(0 : ℝ)} := self_mem_nhdsWithin
    filter_upwards [hmem] with x hx
    have hx₀ : x ≠ (0 : ℝ) := by
      simpa only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] using hx
    exact cubic_real_power_ne_zero hx₀
  · exact (domainLimit_iff_tendsto univ_zero_accumulation).mp
      cubic_quotient_domainLimit_one


theorem negativeAbs_three_halves_not_admissible :
    ¬ EventuallyRealPowerDefinedAlong univ (.point 0) negativeAbs ((3 : ℝ) / 2) :=
  three_halves_not_eventually_admissible


theorem alpha_order_does_not_imply_universal_admissibility :
    ¬ (∀ f φ : ℝ → ℝ,
      InfinitesimalPowerOrderAlong univ (.point 0) f φ 3 →
      ∀ β : ℝ, EventuallyRealPowerDefinedAlong univ (.point 0) φ β) := by
  intro h
  exact negativeAbs_three_halves_not_admissible
    (h negativeAbsCube negativeAbs negativeAbs_cubic_power_order ((3 : ℝ) / 2))

end calculus.Chapter03.Section07NegativeBasePowerOrderObstruction
