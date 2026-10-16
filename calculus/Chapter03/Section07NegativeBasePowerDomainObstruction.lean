import calculus.Chapter03.Section01Powers
import calculus.Chapter03.Section02
import Mathlib.Topology.Algebra.Order.Group

/-!
§3.7 — Nhận xét 3.7.19: lượng từ số mũ và miền lũy thừa

Nguồn: dòng 3374–3376; bảng miền dòng 548–559; điều kiện điểm tụ dòng 1406–1407.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology

namespace calculus.Chapter03.Section07NegativeBasePowerDomainObstruction

open calculus.Chapter03.Section01Powers calculus.Chapter03.Section02


def negativeAbs (x : ℝ) : ℝ := -|x|


def negativeAbsCube (x : ℝ) : ℝ := negativeAbs x ^ (3 : ℕ)


def negativeAbsThreeHalvesPowerDomain : Set ℝ :=
  {x | negativeAbs x ∈ realPowerDomain ((3 : ℝ) / 2)}


theorem three_halves_not_integer : ¬ IntegerExponent ((3 : ℝ) / 2) := by
  rintro ⟨z, hz⟩
  have hz₁ : (1 : ℤ) < z := by
    exact_mod_cast (show (1 : ℝ) < (z : ℝ) by linarith)
  have hz₂ : z < (2 : ℤ) := by
    exact_mod_cast (show (z : ℝ) < 2 by linarith)
  omega


theorem three_halves_real_power_domain :
    realPowerDomain ((3 : ℝ) / 2) = Ioi 0 :=
  noninteger_power_domain three_halves_not_integer


theorem negativeAbs_nonpos (x : ℝ) : negativeAbs x ≤ 0 :=
  neg_nonpos.mpr (abs_nonneg x)


theorem negativeAbs_three_halves_undefined (x : ℝ) :
    negativeAbs x ∉ realPowerDomain ((3 : ℝ) / 2) := by
  rw [three_halves_real_power_domain]
  exact not_lt_of_ge (negativeAbs_nonpos x)


theorem negativeAbsThreeHalvesPowerDomain_empty : negativeAbsThreeHalvesPowerDomain = ∅ := by
  ext x
  constructor
  · exact negativeAbs_three_halves_undefined x
  · intro hx
    exact False.elim hx


theorem negativeAbsThreeHalvesPowerDomain_no_accumulation (a : ℝ) :
    ¬ AccumulationPointOf negativeAbsThreeHalvesPowerDomain a := by
  intro h
  obtain ⟨x, hx, _⟩ := h 1 zero_lt_one
  rw [negativeAbsThreeHalvesPowerDomain_empty] at hx
  exact hx


theorem negativeAbsThreeHalvesPowerDomain_no_domainLimit (f : ℝ → ℝ) (a L : ℝ) :
    ¬ DomainLimit negativeAbsThreeHalvesPowerDomain f a L :=
  fun h ↦ negativeAbsThreeHalvesPowerDomain_no_accumulation a h.1


theorem univ_zero_accumulation : AccumulationPointOf (univ : Set ℝ) 0 :=
  univ_accumulation 0


theorem univ_zero_punctured_neBot :
    (𝓝[(univ : Set ℝ) \ {(0 : ℝ)}] (0 : ℝ)).NeBot :=
  accumulationPointOf_iff_neBot.mp univ_zero_accumulation


theorem negativeAbs_ne_zero {x : ℝ} (hx : x ≠ 0) : negativeAbs x ≠ 0 :=
  neg_ne_zero.mpr (abs_ne_zero.mpr hx)


theorem negativeAbs_tendsto_zero :
    Tendsto negativeAbs (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun x : ℝ ↦ -|x|) (𝓝 (0 : ℝ)) (𝓝 (-|(0 : ℝ)|)) :=
    (tendsto_id.abs).neg
  simpa only [negativeAbs, abs_zero, neg_zero] using! h


theorem negativeAbsCube_tendsto_zero :
    Tendsto negativeAbsCube (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  simpa only [negativeAbsCube, zero_pow (by decide : (3 : ℕ) ≠ 0)] using!
    negativeAbs_tendsto_zero.pow 3


theorem negativeAbs_domainLimit_zero : DomainLimit univ negativeAbs 0 0 := by
  apply (domainLimit_iff_tendsto univ_zero_accumulation).mpr
  exact negativeAbs_tendsto_zero.mono_left
    (nhdsWithin_le_nhds : 𝓝[(univ : Set ℝ) \ {(0 : ℝ)}] (0 : ℝ) ≤ 𝓝 0)


theorem negativeAbsCube_domainLimit_zero : DomainLimit univ negativeAbsCube 0 0 := by
  apply (domainLimit_iff_tendsto univ_zero_accumulation).mpr
  exact negativeAbsCube_tendsto_zero.mono_left
    (nhdsWithin_le_nhds : 𝓝[(univ : Set ℝ) \ {(0 : ℝ)}] (0 : ℝ) ≤ 𝓝 0)


theorem negativeAbs_cubic_real_power_admissible (x : ℝ) :
    negativeAbs x ∈ realPowerDomain (3 : ℝ) := by
  have h := (natural_power_domain_and_value 3 (by norm_num) (negativeAbs x)).2
  change negativeAbs x ∈ realPowerDomain (3 : ℝ) at h
  exact h


theorem cubic_real_power_eq (x : ℝ) :
    negativeAbs x ^ (3 : ℝ) = negativeAbsCube x := by
  have h := (natural_power_domain_and_value 3 (by norm_num) (negativeAbs x)).1
  change negativeAbs x ^ (3 : ℝ) = negativeAbsCube x at h
  exact h


theorem cubic_real_power_ne_zero {x : ℝ} (hx : x ≠ 0) :
    negativeAbs x ^ (3 : ℝ) ≠ 0 := by
  rw [cubic_real_power_eq]
  exact pow_ne_zero 3 (negativeAbs_ne_zero hx)


theorem cubic_quotient_eq_one {x : ℝ} (hx : x ≠ 0) :
    negativeAbsCube x / negativeAbs x ^ (3 : ℝ) = 1 := by
  rw [cubic_real_power_eq]
  exact div_self (pow_ne_zero 3 (negativeAbs_ne_zero hx))


theorem cubic_quotient_domainLimit_one :
    DomainLimit univ (fun x ↦ negativeAbsCube x / negativeAbs x ^ (3 : ℝ)) 0 1 := by
  refine (domainLimit_congr_punctured (D := univ) (f := fun _ ↦ 1)
    (g := fun x ↦ negativeAbsCube x / negativeAbs x ^ (3 : ℝ))
    (a := 0) (L := 1) ?_).mp (constant_domainLimit 1 0)
  intro x _ hx
  exact (cubic_quotient_eq_one hx).symm


theorem three_halves_not_eventually_admissible :
    ¬ (∀ᶠ x in 𝓝[(univ : Set ℝ) \ {(0 : ℝ)}] (0 : ℝ),
      negativeAbs x ∈ realPowerDomain ((3 : ℝ) / 2)) := by
  let : (𝓝[(univ : Set ℝ) \ {(0 : ℝ)}] (0 : ℝ)).NeBot :=
    univ_zero_punctured_neBot
  intro h
  have hfalse : ∀ᶠ _x in 𝓝[(univ : Set ℝ) \ {(0 : ℝ)}] (0 : ℝ), False :=
    h.mono fun x hx ↦ negativeAbs_three_halves_undefined x hx
  exact Filter.eventually_const.mp hfalse

end calculus.Chapter03.Section07NegativeBasePowerDomainObstruction
