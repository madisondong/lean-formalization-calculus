import calculus.Chapter04.Section01Parametric
import calculus.Chapter03.Section03Exercises
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.4 Bài 15(b): lá Descartes

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2773–2777.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section04FoliumParametricCurveInvestigation
open calculus.Chapter04.Section01Parametric
open calculus.Chapter03.Section03Exercises

def foliumParameterDomain : Set ℝ := {t | t ≠ -1}
def foliumX (t : ℝ) : ℝ := 3 * t / (1 + t ^ 3)
def foliumY (t : ℝ) : ℝ := 3 * t ^ 2 / (1 + t ^ 3)
def foliumDX (t : ℝ) : ℝ := 3 * (1 - 2 * t ^ 3) / (1 + t ^ 3) ^ 2
def foliumDY (t : ℝ) : ℝ := 3 * t * (2 - t ^ 3) / (1 + t ^ 3) ^ 2
def foliumDDX (t : ℝ) : ℝ := 18 * t ^ 2 * (t ^ 3 - 2) / (1 + t ^ 3) ^ 3
def foliumDDY (t : ℝ) : ℝ := 6 * (t ^ 6 - 7 * t ^ 3 + 1) / (1 + t ^ 3) ^ 3
def foliumCurve : Set (ℝ × ℝ) := parametricCurve foliumX foliumY foliumParameterDomain
def foliumTangent (t : ℝ) : Set (ℝ × ℝ) :=
  {p | foliumDY t * (p.1 - foliumX t) = foliumDX t * (p.2 - foliumY t)}
def foliumVerticalParameter : ℝ := realNthRoot 3 (1 / 2)
def foliumHorizontalParameter : ℝ := realNthRoot 3 2
def foliumAsymptoteDistance (t : ℝ) : ℝ := |foliumX t + foliumY t + 1| / Real.sqrt 2
def foliumAffineLineDistance (m b t : ℝ) : ℝ :=
  |foliumY t - (m * foliumX t + b)| / Real.sqrt (m ^ 2 + 1)

theorem folium_positive_quadratic_factor (t : ℝ) : 0 < t ^ 2 - t + 1 := by
  nlinarith [sq_nonneg (t - 1 / 2)]

theorem folium_denominator_zero_iff (t : ℝ) : 1 + t ^ 3 = 0 ↔ t = -1 := by
  have hfactor : 1 + t ^ 3 = (t + 1) * (t ^ 2 - t + 1) := by ring
  rw [hfactor, mul_eq_zero]
  have hq : t ^ 2 - t + 1 ≠ 0 := (folium_positive_quadratic_factor t).ne'
  simp only [hq, or_false]
  constructor <;> intro h <;> linarith

theorem folium_denominator_ne_zero {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    1 + t ^ 3 ≠ 0 := by
  intro h
  exact ht ((folium_denominator_zero_iff t).mp h)

theorem folium_actual_first_derivatives {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    HasDerivAt foliumX (foliumDX t) t ∧ HasDerivAt foliumY (foliumDY t) t := by
  have hd := folium_denominator_ne_zero ht
  have hden : HasDerivAt (fun u : ℝ ↦ 1 + u ^ 3) (3 * t ^ 2) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using! (hasDerivAt_pow 3 t).const_add 1
  constructor
  · change HasDerivAt (fun u : ℝ ↦ 3 * u / (1 + u ^ 3)) (foliumDX t) t
    apply (((hasDerivAt_id t).const_mul 3).fun_div hden hd).congr_deriv
    simp only [id_eq, mul_one, foliumDX]
    ring
  · change HasDerivAt (fun u : ℝ ↦ 3 * u ^ 2 / (1 + u ^ 3)) (foliumDY t) t
    apply (((hasDerivAt_pow 2 t).const_mul 3).fun_div hden hd).congr_deriv
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, foliumDY]
    ring

theorem folium_actual_derivative_values {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    deriv foliumX t = foliumDX t ∧ deriv foliumY t = foliumDY t :=
  ⟨(folium_actual_first_derivatives ht).1.deriv, (folium_actual_first_derivatives ht).2.deriv⟩

theorem folium_actual_formula_second_derivatives {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    HasDerivAt foliumDX (foliumDDX t) t ∧ HasDerivAt foliumDY (foliumDDY t) t := by
  have hd := folium_denominator_ne_zero ht
  have hden : HasDerivAt (fun u : ℝ ↦ 1 + u ^ 3) (3 * t ^ 2) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using! (hasDerivAt_pow 3 t).const_add 1
  have hnumX : HasDerivAt (fun u : ℝ ↦ 3 * (1 - 2 * u ^ 3)) (-18 * t ^ 2) t := by
    have h := (((hasDerivAt_pow 3 t).const_mul 2).const_sub 1).const_mul 3
    apply h.congr_deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSub]
    ring
  have hnumY : HasDerivAt (fun u : ℝ ↦ 3 * u * (2 - u ^ 3)) (6 - 12 * t ^ 3) t := by
    have h := ((hasDerivAt_id t).const_mul 3).fun_mul ((hasDerivAt_pow 3 t).const_sub 2)
    apply h.congr_deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, id_eq, mul_one]
    ring
  constructor
  · change HasDerivAt (fun u : ℝ ↦ 3 * (1 - 2 * u ^ 3) / (1 + u ^ 3) ^ 2) (foliumDDX t) t
    apply (hnumX.fun_div (hden.fun_pow 2) (pow_ne_zero 2 hd)).congr_deriv
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, foliumDDX]
    field_simp [hd]
    ring
  · change HasDerivAt (fun u : ℝ ↦ 3 * u * (2 - u ^ 3) / (1 + u ^ 3) ^ 2) (foliumDDY t) t
    apply (hnumY.fun_div (hden.fun_pow 2) (pow_ne_zero 2 hd)).congr_deriv
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, foliumDDY]
    field_simp [hd]
    ring

theorem folium_actual_second_derivatives {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    HasDerivAt (deriv foliumX) (foliumDDX t) t ∧
      HasDerivAt (deriv foliumY) (foliumDDY t) t := by
  have hE : ∀ᶠ u : ℝ in 𝓝 t, u ∈ foliumParameterDomain := eventually_ne_nhds ht
  have hX : deriv foliumX =ᶠ[𝓝 t] foliumDX :=
    hE.mono (fun _ hu ↦ (folium_actual_derivative_values hu).1)
  have hY : deriv foliumY =ᶠ[𝓝 t] foliumDY :=
    hE.mono (fun _ hu ↦ (folium_actual_derivative_values hu).2)
  exact ⟨(folium_actual_formula_second_derivatives ht).1.congr_of_eventuallyEq hX,
    (folium_actual_formula_second_derivatives ht).2.congr_of_eventuallyEq hY⟩

theorem folium_coordinate_continuity_on_source :
    ContinuousOn foliumX foliumParameterDomain ∧ ContinuousOn foliumY foliumParameterDomain :=
  ⟨fun _ ht ↦ (folium_actual_first_derivatives ht).1.continuousAt.continuousWithinAt,
    fun _ ht ↦ (folium_actual_first_derivatives ht).2.continuousAt.continuousWithinAt⟩

theorem folium_implicit_equation {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    (foliumX t) ^ 3 + (foliumY t) ^ 3 = 3 * foliumX t * foliumY t := by
  unfold foliumX foliumY
  field_simp [folium_denominator_ne_zero ht]

theorem folium_origin_and_coordinate_zero {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    (foliumX t = 0 ↔ t = 0) ∧ (foliumY t = 0 ↔ t = 0) ∧
      parametricPoint foliumX foliumY 0 = (0, 0) := by
  have hd := folium_denominator_ne_zero ht
  refine ⟨?_, ?_, ?_⟩
  · simp only [foliumX, div_eq_zero_iff, hd, or_false]
    constructor
    · intro h
      nlinarith
    · intro h
      rw [h, mul_zero]
  · simp only [foliumY, div_eq_zero_iff, hd, or_false]
    constructor
    · intro h
      nlinarith [sq_nonneg t]
    · intro h
      rw [h]
      norm_num
  · norm_num only [parametricPoint, foliumX, foliumY]

theorem folium_every_implicit_point {x y : ℝ} (hxy : x ^ 3 + y ^ 3 = 3 * x * y) :
    ∃ t ∈ foliumParameterDomain, foliumX t = x ∧ foliumY t = y := by
  by_cases hx : x = 0
  · have hy : y = 0 := by
      apply (show Odd (3 : ℕ) by decide).pow_injective
      rw [hx] at hxy
      simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), zero_add, mul_zero, zero_mul] using hxy
    refine ⟨0, by norm_num [foliumParameterDomain], ?_, ?_⟩ <;> simp [foliumX, foliumY, hx, hy]
  · have hy : y ≠ 0 := by
      intro hy
      apply hx
      apply (show Odd (3 : ℕ) by decide).pow_injective
      rw [hy] at hxy
      simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), add_zero, mul_zero] using hxy
    let t : ℝ := y / x
    have hden : 1 + t ^ 3 = 3 * y / x ^ 2 := by
      dsimp only [t]
      field_simp [hx]
      nlinarith [hxy]
    have hd : 1 + t ^ 3 ≠ 0 := by
      rw [hden]
      exact div_ne_zero (mul_ne_zero (by norm_num) hy) (pow_ne_zero 2 hx)
    refine ⟨t, ?_, ?_, ?_⟩
    · intro ht
      apply hd
      exact (folium_denominator_zero_iff t).mpr ht
    · unfold foliumX
      rw [hden]
      dsimp only [t]
      field_simp [hx, hy]
    · unfold foliumY
      rw [hden]
      dsimp only [t]
      field_simp [hx, hy]

theorem folium_complete_image :
    foliumCurve = {p : ℝ × ℝ | p.1 ^ 3 + p.2 ^ 3 = 3 * p.1 * p.2} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact folium_implicit_equation ht
  · intro hp
    obtain ⟨t, ht, hx, hy⟩ := folium_every_implicit_point hp
    exact ⟨t, ht, Prod.ext hx hy⟩

theorem folium_parameter_recovery {t : ℝ} (ht : t ∈ foliumParameterDomain) (ht0 : t ≠ 0) :
    foliumY t / foliumX t = t := by
  unfold foliumX foliumY
  field_simp [folium_denominator_ne_zero ht, ht0]

theorem folium_finite_parameter_injective :
    InjOn (parametricPoint foliumX foliumY) foliumParameterDomain := by
  intro s hs t ht heq
  have hX : foliumX s = foliumX t := congrArg Prod.fst heq
  have hY : foliumY s = foliumY t := congrArg Prod.snd heq
  by_cases hs0 : s = 0
  · have ht0 : t = 0 := (folium_origin_and_coordinate_zero ht).1.mp (by rw [← hX, hs0]; norm_num [foliumX])
    exact hs0.trans ht0.symm
  · have ht0 : t ≠ 0 := by
      intro h
      apply hs0
      exact (folium_origin_and_coordinate_zero hs).1.mp (by rw [hX, h]; norm_num [foliumX])
    calc
      s = foliumY s / foliumX s := (folium_parameter_recovery hs hs0).symm
      _ = foliumY t / foliumX t := by rw [hX, hY]
      _ = t := folium_parameter_recovery ht ht0


theorem folium_unique_implicit_singular_point (x y : ℝ) :
    (x ^ 3 + y ^ 3 = 3 * x * y ∧ 3 * x ^ 2 - 3 * y = 0 ∧
      3 * y ^ 2 - 3 * x = 0) ↔ x = 0 ∧ y = 0 := by
  constructor
  · rintro ⟨hxy, hx, hy⟩
    have hxx : x ^ 2 = y := by linarith
    have hyy : y ^ 2 = x := by linarith
    have hcX : x ^ 3 = x * y := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ = x * y := by rw [hxx]
    have hcY : y ^ 3 = x * y := by
      calc
        y ^ 3 = y ^ 2 * y := by ring
        _ = x * y := by rw [hyy]
    have hz : x * y = 0 := by nlinarith [hxy, hcX, hcY]
    rcases mul_eq_zero.mp hz with hx0 | hy0
    · refine ⟨hx0, ?_⟩
      rw [hx0] at hyy
      nlinarith [sq_nonneg y]
    · refine ⟨?_, hy0⟩
      rw [hy0] at hxx
      nlinarith [sq_nonneg x]
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem folium_reciprocal_chart {t : ℝ} (ht : t ∈ foliumParameterDomain) (ht0 : t ≠ 0) :
    t⁻¹ ∈ foliumParameterDomain ∧ foliumX t⁻¹ = foliumY t ∧ foliumY t⁻¹ = foliumX t := by
  have hi : t⁻¹ ≠ -1 := by
    intro h
    apply ht
    have hh := congrArg Inv.inv h
    simpa only [inv_inv, inv_neg, inv_one] using hh
  refine ⟨hi, ?_, ?_⟩
  · unfold foliumX foliumY
    field_simp [ht0, folium_denominator_ne_zero ht, folium_denominator_ne_zero hi]
    have hden : t ^ 3 + 1 ≠ 0 := by
      simpa only [add_comm] using folium_denominator_ne_zero ht
    field_simp [hden]
    all_goals ring
  · unfold foliumX foliumY
    field_simp [ht0, folium_denominator_ne_zero ht, folium_denominator_ne_zero hi]
    have hden : t ^ 3 + 1 ≠ 0 := by
      simpa only [add_comm] using folium_denominator_ne_zero ht
    field_simp [hden]
    all_goals ring

theorem folium_critical_parameter_cubes :
    foliumVerticalParameter ^ 3 = 1 / 2 ∧ foliumHorizontalParameter ^ 3 = 2 ∧
      0 < foliumVerticalParameter ∧ foliumVerticalParameter < 1 ∧ 1 < foliumHorizontalParameter := by
  have ha : foliumVerticalParameter ^ 3 = 1 / 2 :=
    realNthRoot_pow (by decide : 1 ≤ (3 : ℕ)) (Or.inl (by decide : Odd (3 : ℕ)))
  have hb : foliumHorizontalParameter ^ 3 = 2 :=
    realNthRoot_pow (by decide : 1 ≤ (3 : ℕ)) (Or.inl (by decide : Odd (3 : ℕ)))
  have hodd : Odd (3 : ℕ) := by decide
  refine ⟨ha, hb, ?_, ?_, ?_⟩
  · apply hodd.pow_lt_pow.mp
    rw [ha]
    norm_num
  · apply hodd.pow_lt_pow.mp
    rw [ha]
    norm_num
  · apply hodd.pow_lt_pow.mp
    rw [hb]
    norm_num

theorem folium_full_first_derivative_signs {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    (0 < foliumDX t ↔ t ^ 3 < 1 / 2) ∧
    (foliumDX t = 0 ↔ t ^ 3 = 1 / 2) ∧
    (foliumDX t < 0 ↔ 1 / 2 < t ^ 3) ∧
    (0 < foliumDY t ↔ 0 < t ∧ t ^ 3 < 2) ∧
    (foliumDY t = 0 ↔ t = 0 ∨ t ^ 3 = 2) ∧
    (foliumDY t < 0 ↔ t < 0 ∨ 2 < t ^ 3) := by
  have hd : 0 < (1 + t ^ 3) ^ 2 := sq_pos_of_ne_zero (folium_denominator_ne_zero ht)
  have hcneg : t ^ 3 < 0 ↔ t < 0 := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using (show Odd (3 : ℕ) by decide).pow_lt_pow (a := t) (b := 0)
  have hcpos : 0 < t ^ 3 ↔ 0 < t := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using (show Odd (3 : ℕ) by decide).pow_lt_pow (a := 0) (b := t)
  have hcle : t ^ 3 ≤ 0 ↔ t ≤ 0 := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using (show Odd (3 : ℕ) by decide).pow_le_pow (a := t) (b := 0)
  unfold foliumDX foliumDY
  simp only [div_pos_iff_of_pos_right hd, div_lt_iff₀ hd, zero_mul,
    div_eq_zero_iff, hd.ne', or_false]
  refine ⟨by constructor <;> intro h <;> linarith,
    by constructor <;> intro h <;> linarith,
    by constructor <;> intro h <;> linarith, ?_, ?_, ?_⟩
  · constructor
    · intro h
      by_cases htpos : 0 < t
      · refine ⟨htpos, ?_⟩
        by_contra hc
        have hmul := mul_nonpos_of_nonneg_of_nonpos
          (by linarith : 0 ≤ 3 * t) (by linarith : 2 - t ^ 3 ≤ 0)
        linarith
      · have htc : t ^ 3 ≤ 0 := hcle.mpr (le_of_not_gt htpos)
        have hmul := mul_nonpos_of_nonpos_of_nonneg
          (by linarith : 3 * t ≤ 0) (by linarith : 0 ≤ 2 - t ^ 3)
        linarith
    · rintro ⟨htpos, hc⟩
      exact mul_pos (mul_pos (by norm_num) htpos) (by linarith)
  · constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · left
        nlinarith
      · right
        linarith
    · rintro (rfl | hc)
      · ring
      · rw [hc]
        ring
  · constructor
    · intro h
      by_cases hn : t < 0
      · exact Or.inl hn
      · right
        by_contra hc
        have hp := mul_nonneg (by linarith : 0 ≤ 3 * t) (by linarith : 0 ≤ 2 - t ^ 3)
        linarith
    · rintro (hn | hc)
      · exact mul_neg_of_neg_of_pos (by linarith) (by linarith [hcneg.mpr hn])
      · exact mul_neg_of_pos_of_neg (by linarith [hcpos.mp (by linarith : 0 < t ^ 3)]) (by linarith)

theorem folium_regular_every_source_parameter {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    foliumDX t ≠ 0 ∨ foliumDY t ≠ 0 := by
  by_cases hX : foliumDX t = 0
  · right
    intro hY
    have hx := (folium_full_first_derivative_signs ht).2.1.mp hX
    rcases (folium_full_first_derivative_signs ht).2.2.2.2.1.mp hY with h0 | h2
    · rw [h0] at hx
      norm_num at hx
    · linarith
  · exact Or.inl hX

theorem folium_monotonic_branches :
    StrictMonoOn foliumX (Iio (-1 : ℝ)) ∧
    StrictMonoOn foliumX (Ioo (-1 : ℝ) foliumVerticalParameter) ∧
    StrictAntiOn foliumX (Ioi foliumVerticalParameter) ∧
    StrictAntiOn foliumY (Iio (-1 : ℝ)) ∧
    StrictAntiOn foliumY (Ioo (-1 : ℝ) 0) ∧
    StrictMonoOn foliumY (Ioo (0 : ℝ) foliumHorizontalParameter) ∧
    StrictAntiOn foliumY (Ioi foliumHorizontalParameter) := by
  have ha := folium_critical_parameter_cubes.1
  have hb := folium_critical_parameter_cubes.2.1
  have ha0 := folium_critical_parameter_cubes.2.2.1
  have hb1 := folium_critical_parameter_cubes.2.2.2.2
  have hodd : Odd (3 : ℕ) := by decide
  have hMX (D : Set ℝ) (hcv : Convex ℝ D) (hD : D ⊆ foliumParameterDomain)
      (hp : ∀ t ∈ D, 0 < foliumDX t) : StrictMonoOn foliumX D := by
    apply strictMonoOn_of_deriv_pos hcv (folium_coordinate_continuity_on_source.1.mono hD)
    intro t ht
    rw [(folium_actual_derivative_values (hD (interior_subset ht))).1]
    exact hp t (interior_subset ht)
  have hAX (D : Set ℝ) (hcv : Convex ℝ D) (hD : D ⊆ foliumParameterDomain)
      (hp : ∀ t ∈ D, foliumDX t < 0) : StrictAntiOn foliumX D := by
    apply strictAntiOn_of_deriv_neg hcv (folium_coordinate_continuity_on_source.1.mono hD)
    intro t ht
    rw [(folium_actual_derivative_values (hD (interior_subset ht))).1]
    exact hp t (interior_subset ht)
  have hMY (D : Set ℝ) (hcv : Convex ℝ D) (hD : D ⊆ foliumParameterDomain)
      (hp : ∀ t ∈ D, 0 < foliumDY t) : StrictMonoOn foliumY D := by
    apply strictMonoOn_of_deriv_pos hcv (folium_coordinate_continuity_on_source.2.mono hD)
    intro t ht
    rw [(folium_actual_derivative_values (hD (interior_subset ht))).2]
    exact hp t (interior_subset ht)
  have hAY (D : Set ℝ) (hcv : Convex ℝ D) (hD : D ⊆ foliumParameterDomain)
      (hp : ∀ t ∈ D, foliumDY t < 0) : StrictAntiOn foliumY D := by
    apply strictAntiOn_of_deriv_neg hcv (folium_coordinate_continuity_on_source.2.mono hD)
    intro t ht
    rw [(folium_actual_derivative_values (hD (interior_subset ht))).2]
    exact hp t (interior_subset ht)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hMX _ (convex_Iio (-1 : ℝ))
      (fun t ht ↦ show t ≠ -1 from (show t < -1 from ht).ne)
    intro t ht
    apply (folium_full_first_derivative_signs
      (show t ≠ -1 from (show t < -1 from ht).ne)).1.mpr
    have hc : t ^ 3 < (-1 : ℝ) ^ 3 := hodd.pow_lt_pow.mpr ht
    norm_num at hc
    linarith
  · apply hMX _ (convex_Ioo (-1 : ℝ) foliumVerticalParameter)
      (fun t ht ↦ by change t ≠ -1; linarith [ht.1])
    intro t ht
    apply (folium_full_first_derivative_signs (by change t ≠ -1; linarith [ht.1])).1.mpr
    rw [← ha]
    exact hodd.pow_lt_pow.mpr ht.2
  · apply hAX _ (convex_Ioi foliumVerticalParameter)
      (fun t ht ↦ by change t ≠ -1; have h : foliumVerticalParameter < t := ht; linarith)
    intro t ht
    apply (folium_full_first_derivative_signs
      (by change t ≠ -1; have h : foliumVerticalParameter < t := ht; linarith)).2.2.1.mpr
    rw [← ha]
    exact hodd.pow_lt_pow.mpr ht
  · apply hAY _ (convex_Iio (-1 : ℝ))
      (fun t ht ↦ show t ≠ -1 from (show t < -1 from ht).ne)
    intro t ht
    exact (folium_full_first_derivative_signs
      (show t ≠ -1 from (show t < -1 from ht).ne)).2.2.2.2.2.mpr
      (Or.inl (lt_trans (show t < -1 from ht) (by norm_num : (-1 : ℝ) < 0)))
  · apply hAY _ (convex_Ioo (-1 : ℝ) 0)
      (fun t ht ↦ by change t ≠ -1; linarith [ht.1])
    intro t ht
    exact (folium_full_first_derivative_signs (by change t ≠ -1; linarith [ht.1])).2.2.2.2.2.mpr
      (Or.inl ht.2)
  · apply hMY _ (convex_Ioo (0 : ℝ) foliumHorizontalParameter)
      (fun t ht ↦ by change t ≠ -1; linarith [ht.1])
    intro t ht
    apply (folium_full_first_derivative_signs (by change t ≠ -1; linarith [ht.1])).2.2.2.1.mpr
    refine ⟨ht.1, ?_⟩
    rw [← hb]
    exact hodd.pow_lt_pow.mpr ht.2
  · apply hAY _ (convex_Ioi foliumHorizontalParameter)
      (fun t ht ↦ by change t ≠ -1; have h : foliumHorizontalParameter < t := ht; linarith)
    intro t ht
    apply (folium_full_first_derivative_signs
      (by change t ≠ -1; have h : foliumHorizontalParameter < t := ht; linarith)).2.2.2.2.2.mpr
    right
    rw [← hb]
    exact hodd.pow_lt_pow.mpr ht

theorem folium_critical_points_and_tangents (p : ℝ × ℝ) :
    parametricPoint foliumX foliumY foliumVerticalParameter =
      (2 * foliumVerticalParameter, 2 * foliumVerticalParameter ^ 2) ∧
    parametricPoint foliumX foliumY foliumHorizontalParameter =
      (foliumHorizontalParameter, foliumHorizontalParameter ^ 2) ∧
    (p ∈ foliumTangent 0 ↔ p.2 = 0) ∧
    (p ∈ foliumTangent foliumVerticalParameter ↔ p.1 = 2 * foliumVerticalParameter) ∧
    (p ∈ foliumTangent foliumHorizontalParameter ↔ p.2 = foliumHorizontalParameter ^ 2) := by
  have ha := folium_critical_parameter_cubes.1
  have hb := folium_critical_parameter_cubes.2.1
  have haD : foliumVerticalParameter ∈ foliumParameterDomain := by
    intro he
    rw [he] at ha
    norm_num at ha
  have hbD : foliumHorizontalParameter ∈ foliumParameterDomain := by
    intro he
    rw [he] at hb
    norm_num at hb
  have hpa : parametricPoint foliumX foliumY foliumVerticalParameter =
      (2 * foliumVerticalParameter, 2 * foliumVerticalParameter ^ 2) := by
    apply Prod.ext <;> simp only [parametricPoint, foliumX, foliumY, ha] <;> ring
  have hpb : parametricPoint foliumX foliumY foliumHorizontalParameter =
      (foliumHorizontalParameter, foliumHorizontalParameter ^ 2) := by
    apply Prod.ext <;> simp only [parametricPoint, foliumX, foliumY, hb] <;> ring
  have hXa : foliumDX foliumVerticalParameter = 0 := (folium_full_first_derivative_signs haD).2.1.mpr ha
  have hYa : foliumDY foliumVerticalParameter ≠ 0 := by
    rcases folium_regular_every_source_parameter haD with h | h
    · exact False.elim (h hXa)
    · exact h
  have hYb : foliumDY foliumHorizontalParameter = 0 :=
    (folium_full_first_derivative_signs hbD).2.2.2.2.1.mpr (Or.inr hb)
  have hXb : foliumDX foliumHorizontalParameter ≠ 0 := by
    rcases folium_regular_every_source_parameter hbD with h | h
    · exact h
    · exact False.elim (h hYb)
  refine ⟨hpa, hpb, ?_, ?_, ?_⟩
  · norm_num only [foliumTangent, mem_ofPred_eq, foliumDX, foliumDY, foliumX, foliumY]
    constructor <;> intro h <;> linarith
  · change foliumDY foliumVerticalParameter * (p.1 - foliumX foliumVerticalParameter) =
      foliumDX foliumVerticalParameter * (p.2 - foliumY foliumVerticalParameter) ↔ _
    rw [hXa, zero_mul]
    simp only [mul_eq_zero, hYa, false_or, sub_eq_zero]
    rw [show foliumX foliumVerticalParameter = 2 * foliumVerticalParameter from congrArg Prod.fst hpa]
  · change foliumDY foliumHorizontalParameter * (p.1 - foliumX foliumHorizontalParameter) =
      foliumDX foliumHorizontalParameter * (p.2 - foliumY foliumHorizontalParameter) ↔ _
    rw [hYb, zero_mul, eq_comm]
    simp only [mul_eq_zero, hXb, false_or, sub_eq_zero]
    rw [show foliumY foliumHorizontalParameter = foliumHorizontalParameter ^ 2 from congrArg Prod.snd hpb]

theorem folium_curvature_numerator {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    deriv foliumX t * deriv (deriv foliumY) t -
      deriv (deriv foliumX) t * deriv foliumY t = 18 / (1 + t ^ 3) ^ 2 ∧
      0 < 18 / (1 + t ^ 3) ^ 2 := by
  rw [(folium_actual_derivative_values ht).1, (folium_actual_derivative_values ht).2,
    (folium_actual_second_derivatives ht).1.deriv, (folium_actual_second_derivatives ht).2.deriv]
  constructor
  · unfold foliumDX foliumDY foliumDDX foliumDDY
    field_simp [folium_denominator_ne_zero ht]
    ring
  · exact div_pos (by norm_num) (sq_pos_of_ne_zero (folium_denominator_ne_zero ht))

theorem folium_source_quadrants {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    (t < -1 → 0 < foliumX t ∧ foliumY t < 0) ∧
    (-1 < t ∧ t < 0 → foliumX t < 0 ∧ 0 < foliumY t) ∧
    (0 < t → 0 < foliumX t ∧ 0 < foliumY t) := by
  have hodd : Odd (3 : ℕ) := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    have hcube : t ^ 3 < -1 := by simpa only [show (-1 : ℝ) ^ 3 = -1 by norm_num] using hodd.pow_lt_pow.mpr hn
    have hd : 1 + t ^ 3 < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg (by linarith : 3 * t < 0) hd,
      div_neg_of_pos_of_neg (mul_pos (by norm_num) (sq_pos_of_ne_zero (by linarith : t ≠ 0))) hd⟩
  · rintro ⟨hl, hr⟩
    have hcube : -1 < t ^ 3 := by simpa only [show (-1 : ℝ) ^ 3 = -1 by norm_num] using hodd.pow_lt_pow.mpr hl
    have hd : 0 < 1 + t ^ 3 := by linarith
    exact ⟨div_neg_of_neg_of_pos (by linarith : 3 * t < 0) hd,
      div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hr.ne)) hd⟩
  · intro hp
    have hd : 0 < 1 + t ^ 3 :=
      lt_of_le_of_ne (by positivity : 0 ≤ 1 + t ^ 3) (folium_denominator_ne_zero ht).symm
    exact ⟨div_pos (mul_pos (by norm_num) hp) hd,
      div_pos (mul_pos (by norm_num) (sq_pos_of_pos hp)) hd⟩

theorem folium_coordinates_at_parameter_infinity {L : Filter ℝ}
    (hi : Tendsto (fun t : ℝ ↦ t⁻¹) L (𝓝 0))
    (h0 : ∀ᶠ t : ℝ in L, t ≠ 0) (hD : ∀ᶠ t : ℝ in L, t ∈ foliumParameterDomain) :
    Tendsto foliumX L (𝓝 0) ∧ Tendsto foliumY L (𝓝 0) := by
  have hd : Tendsto (fun t : ℝ ↦ 1 + (t⁻¹) ^ 3) L (𝓝 1) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), add_zero] using! (hi.pow 3).const_add 1
  constructor
  · have h : Tendsto (fun t : ℝ ↦ (3 * (t⁻¹) ^ 2) / (1 + (t⁻¹) ^ 3)) L (𝓝 0) := by
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div] using!
        ((hi.pow 2).const_mul 3).div hd one_ne_zero
    apply h.congr'
    filter_upwards [h0, hD] with t ht0 ht
    unfold foliumX
    field_simp [ht0, folium_denominator_ne_zero ht]
    have hden : t ^ 3 + 1 ≠ 0 := by
      simpa only [add_comm] using folium_denominator_ne_zero ht
    field_simp [hden]
    all_goals ring
  · have h : Tendsto (fun t : ℝ ↦ (3 * t⁻¹) / (1 + (t⁻¹) ^ 3)) L (𝓝 0) := by
      simpa only [mul_zero, zero_div] using! (hi.const_mul 3).div hd one_ne_zero
    apply h.congr'
    filter_upwards [h0, hD] with t ht0 ht
    unfold foliumY
    field_simp [ht0, folium_denominator_ne_zero ht]
    have hden : t ^ 3 + 1 ≠ 0 := by
      simpa only [add_comm] using folium_denominator_ne_zero ht
    field_simp [hden]
    all_goals ring

theorem folium_both_parameter_infinite_ends_return_origin :
    Tendsto foliumX atTop (𝓝 0) ∧ Tendsto foliumY atTop (𝓝 0) ∧
      Tendsto foliumX atBot (𝓝 0) ∧ Tendsto foliumY atBot (𝓝 0) := by
  have hT := folium_coordinates_at_parameter_infinity tendsto_inv_atTop_zero
    ((eventually_gt_atTop (0 : ℝ)).mono (fun _ h ↦ h.ne'))
    ((eventually_gt_atTop (0 : ℝ)).mono (fun _ h he ↦ by rw [he] at h; norm_num at h))
  have hB := folium_coordinates_at_parameter_infinity tendsto_inv_atBot_zero
    ((eventually_lt_atBot (-2 : ℝ)).mono (fun _ h ↦ by linarith))
    ((eventually_lt_atBot (-2 : ℝ)).mono (fun _ h he ↦ by rw [he] at h; norm_num at h))
  exact ⟨hT.1, hT.2, hB.1, hB.2⟩

theorem folium_origin_two_regular_tangent_directions :
    HasDerivAt foliumX 3 0 ∧ HasDerivAt foliumY 0 0 ∧
      HasDerivAt (fun u : ℝ ↦ foliumY u) 0 0 ∧ HasDerivAt (fun u : ℝ ↦ foliumX u) 3 0 := by
  have h := folium_actual_first_derivatives (t := 0) (by norm_num [foliumParameterDomain])
  norm_num only [foliumDX, foliumDY] at h
  exact ⟨h.1, h.2, h.2, h.1⟩

theorem folium_origin_chart_tangent_axes (p : ℝ × ℝ) :
    (p ∈ foliumTangent 0 ↔ p.2 = 0) ∧
    (deriv foliumX 0 * (p.1 - foliumY 0) =
      deriv foliumY 0 * (p.2 - foliumX 0) ↔ p.1 = 0) := by
  refine ⟨(folium_critical_points_and_tangents p).2.2.1, ?_⟩
  rw [folium_origin_two_regular_tangent_directions.1.deriv,
    folium_origin_two_regular_tangent_directions.2.1.deriv]
  norm_num only [foliumX, foliumY]
  constructor <;> intro h <;> linarith


theorem folium_affine_residual_identity {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    foliumX t + foliumY t + 1 = (t + 1) ^ 2 / (t ^ 2 - t + 1) := by
  unfold foliumX foliumY
  generalize hdEq : 1 + t ^ 3 = d
  generalize hqEq : t ^ 2 - t + 1 = q
  have hd : d ≠ 0 := by rw [← hdEq]; exact folium_denominator_ne_zero ht
  have hq : q ≠ 0 := by rw [← hqEq]; exact (folium_positive_quadratic_factor t).ne'
  have hfactor : d = (t + 1) * q := by rw [← hdEq, ← hqEq]; ring
  field_simp [hd, hq]
  rw [hfactor, ← hqEq]
  ring

theorem folium_strictly_above_asymptote {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    0 < foliumX t + foliumY t + 1 := by
  rw [folium_affine_residual_identity ht]
  apply div_pos _ (folium_positive_quadratic_factor t)
  exact sq_pos_of_ne_zero (by intro h; apply ht; linarith)

theorem folium_diagonal_loop_point :
    parametricPoint foliumX foliumY 1 = (3 / 2, 3 / 2) := by
  norm_num [parametricPoint, foliumX, foliumY]

theorem folium_pole_affine_residual_tendsto_zero :
    Tendsto (fun t : ℝ ↦ foliumX t + foliumY t + 1) (𝓝[≠] (-1 : ℝ)) (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ ↦ t) (𝓝[≠] (-1 : ℝ)) (𝓝 (-1 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun t : ℝ ↦ (t + 1) ^ 2) (𝓝[≠] (-1 : ℝ)) (𝓝 0) := by
    simpa only [show (-1 : ℝ) + 1 = 0 by norm_num, zero_pow (by decide : (2 : ℕ) ≠ 0)] using! (hi.add_const 1).pow 2
  have hd : Tendsto (fun t : ℝ ↦ t ^ 2 - t + 1) (𝓝[≠] (-1 : ℝ)) (𝓝 3) := by
    convert! ((hi.pow 2).sub hi).add_const 1 using 1
    norm_num
  have h := hn.div hd (by norm_num : (3 : ℝ) ≠ 0)
  apply (show Tendsto (fun t : ℝ ↦ (t + 1) ^ 2 / (t ^ 2 - t + 1))
    (𝓝[≠] (-1 : ℝ)) (𝓝 0) from by simpa only [zero_div] using! h).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (folium_affine_residual_identity
    (by change t ≠ -1; simpa only [mem_compl_iff, mem_singleton_iff] using ht)).symm

theorem folium_pole_coordinate_factorization {t : ℝ} (ht : t ∈ foliumParameterDomain) :
    foliumX t = (3 * t / (t ^ 2 - t + 1)) * (t + 1)⁻¹ ∧
      foliumY t = (3 * t ^ 2 / (t ^ 2 - t + 1)) * (t + 1)⁻¹ := by
  have hfactor : 1 + t ^ 3 = (t + 1) * (t ^ 2 - t + 1) := by ring
  have hd := folium_denominator_ne_zero ht
  have hq : t ^ 2 - t + 1 ≠ 0 := (folium_positive_quadratic_factor t).ne'
  have h1 : t + 1 ≠ 0 := by intro h; apply ht; linarith
  unfold foliumX foliumY
  constructor
  · apply (div_eq_iff hd).mpr
    rw [hfactor]
    calc
      3 * t = (3 * t / (t ^ 2 - t + 1)) * (t ^ 2 - t + 1) :=
        (div_mul_cancel₀ _ hq).symm
      _ = (3 * t / (t ^ 2 - t + 1)) * ((t + 1)⁻¹ * (t + 1)) * (t ^ 2 - t + 1) := by
        rw [inv_mul_cancel₀ h1, mul_one]
      _ = (3 * t / (t ^ 2 - t + 1)) * (t + 1)⁻¹ * ((t + 1) * (t ^ 2 - t + 1)) := by ring
  · apply (div_eq_iff hd).mpr
    rw [hfactor]
    calc
      3 * t ^ 2 = (3 * t ^ 2 / (t ^ 2 - t + 1)) * (t ^ 2 - t + 1) :=
        (div_mul_cancel₀ _ hq).symm
      _ = (3 * t ^ 2 / (t ^ 2 - t + 1)) * ((t + 1)⁻¹ * (t + 1)) * (t ^ 2 - t + 1) := by
        rw [inv_mul_cancel₀ h1, mul_one]
      _ = (3 * t ^ 2 / (t ^ 2 - t + 1)) * (t + 1)⁻¹ * ((t + 1) * (t ^ 2 - t + 1)) := by ring

theorem folium_shifted_inverse_right_pole :
    Tendsto (fun t : ℝ ↦ (t + 1)⁻¹) (𝓝[>] (-1 : ℝ)) atTop := by
  have hs : Tendsto (fun t : ℝ ↦ t + 1) (𝓝[>] (-1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [show (-1 : ℝ) + 1 = 0 by norm_num] using!
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (-1 : ℝ) ≤ 𝓝 (-1))).add_const 1
    · filter_upwards [self_mem_nhdsWithin] with t (ht : -1 < t)
      change 0 < t + 1
      linarith
  simpa only [Function.comp_def] using! tendsto_inv_nhdsGT_zero.comp hs

theorem folium_shifted_inverse_left_pole :
    Tendsto (fun t : ℝ ↦ (t + 1)⁻¹) (𝓝[<] (-1 : ℝ)) atBot := by
  have hs : Tendsto (fun t : ℝ ↦ t + 1) (𝓝[<] (-1 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [show (-1 : ℝ) + 1 = 0 by norm_num] using!
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[<] (-1 : ℝ) ≤ 𝓝 (-1))).add_const 1
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < -1)
      change t + 1 < 0
      linarith
  simpa only [Function.comp_def] using! tendsto_inv_nhdsLT_zero.comp hs

theorem folium_pole_coordinate_finite_factors :
    Tendsto (fun t : ℝ ↦ 3 * t / (t ^ 2 - t + 1)) (𝓝 (-1 : ℝ)) (𝓝 (-1 : ℝ)) ∧
      Tendsto (fun t : ℝ ↦ 3 * t ^ 2 / (t ^ 2 - t + 1)) (𝓝 (-1 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun t : ℝ ↦ t) (𝓝 (-1 : ℝ)) (𝓝 (-1 : ℝ)) := tendsto_id
  have hd : Tendsto (fun t : ℝ ↦ t ^ 2 - t + 1) (𝓝 (-1 : ℝ)) (𝓝 (3 : ℝ)) := by
    convert! ((hi.pow 2).sub hi).add_const 1 using 1
    norm_num
  constructor
  · convert! (hi.const_mul 3).div hd (by norm_num : (3 : ℝ) ≠ 0) using 1
    norm_num
  · convert! ((hi.pow 2).const_mul 3).div hd (by norm_num : (3 : ℝ) ≠ 0) using 1
    norm_num

theorem folium_actual_two_sided_pole_limits :
    Tendsto foliumX (𝓝[>] (-1 : ℝ)) atBot ∧ Tendsto foliumY (𝓝[>] (-1 : ℝ)) atTop ∧
      Tendsto foliumX (𝓝[<] (-1 : ℝ)) atTop ∧ Tendsto foliumY (𝓝[<] (-1 : ℝ)) atBot := by
  have hf := folium_pole_coordinate_finite_factors
  have hrX := (hf.1.mono_left (nhdsWithin_le_nhds : 𝓝[>] (-1 : ℝ) ≤ 𝓝 (-1))).neg_mul_atTop
    (by norm_num : (-1 : ℝ) < 0) folium_shifted_inverse_right_pole
  have hrY := (hf.2.mono_left (nhdsWithin_le_nhds : 𝓝[>] (-1 : ℝ) ≤ 𝓝 (-1))).pos_mul_atTop
    (by norm_num : (0 : ℝ) < 1) folium_shifted_inverse_right_pole
  have hlX := (hf.1.mono_left (nhdsWithin_le_nhds : 𝓝[<] (-1 : ℝ) ≤ 𝓝 (-1))).neg_mul_atBot
    (by norm_num : (-1 : ℝ) < 0) folium_shifted_inverse_left_pole
  have hlY := (hf.2.mono_left (nhdsWithin_le_nhds : 𝓝[<] (-1 : ℝ) ≤ 𝓝 (-1))).pos_mul_atBot
    (by norm_num : (0 : ℝ) < 1) folium_shifted_inverse_left_pole
  refine ⟨hrX.congr' ?_, hrY.congr' ?_, hlX.congr' ?_, hlY.congr' ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t (ht : -1 < t)
    exact (folium_pole_coordinate_factorization ht.ne').1.symm
  · filter_upwards [self_mem_nhdsWithin] with t (ht : -1 < t)
    exact (folium_pole_coordinate_factorization ht.ne').2.symm
  · filter_upwards [self_mem_nhdsWithin] with t (ht : t < -1)
    exact (folium_pole_coordinate_factorization ht.ne).1.symm
  · filter_upwards [self_mem_nhdsWithin] with t (ht : t < -1)
    exact (folium_pole_coordinate_factorization ht.ne).2.symm

theorem folium_geometric_asymptote_both_sides :
    Tendsto foliumAsymptoteDistance (𝓝[>] (-1 : ℝ)) (𝓝 0) ∧
      Tendsto foliumAsymptoteDistance (𝓝[<] (-1 : ℝ)) (𝓝 0) := by
  have h := folium_pole_affine_residual_tendsto_zero.abs.div_const (Real.sqrt 2)
  have hh : Tendsto foliumAsymptoteDistance (𝓝[≠] (-1 : ℝ)) (𝓝 0) := by
    simpa only [foliumAsymptoteDistance, abs_zero, zero_div] using! h
  exact ⟨hh.mono_left (nhdsGT_le_nhdsNE (-1 : ℝ)), hh.mono_left (nhdsLT_le_nhdsNE (-1 : ℝ))⟩

theorem folium_entire_asymptote_line_excluded {x y : ℝ}
    (hxy : x ^ 3 + y ^ 3 = 3 * x * y) : x + y + 1 ≠ 0 := by
  intro h
  have hy : y = -1 - x := by linarith
  rw [hy] at hxy
  nlinarith [hxy]


theorem folium_affine_asymptote_coefficients_unique {L : Filter ℝ} [L.NeBot]
    (hi : Tendsto (fun t : ℝ ↦ (foliumX t)⁻¹) L (𝓝 0))
    (hne : ∀ᶠ t : ℝ in L, foliumX t ≠ 0)
    (hslope : Tendsto (fun t : ℝ ↦ foliumY t / foliumX t) L (𝓝 (-1 : ℝ)))
    (hsum : Tendsto (fun t : ℝ ↦ foliumX t + foliumY t) L (𝓝 (-1 : ℝ)))
    (m b : ℝ) (hr : Tendsto (fun t : ℝ ↦ foliumY t - (m * foliumX t + b)) L (𝓝 0)) :
    m = -1 ∧ b = -1 := by
  have hq : Tendsto (fun t : ℝ ↦ foliumY t / foliumX t) L (𝓝 m) := by
    have hh := ((hr.mul hi).add (hi.const_mul b)).add_const m
    have hh' : Tendsto (fun t : ℝ ↦
        (foliumY t - (m * foliumX t + b)) * (foliumX t)⁻¹ + b * (foliumX t)⁻¹ + m)
        L (𝓝 m) := by simpa only [mul_zero, zero_add] using! hh
    apply hh'.congr'
    filter_upwards [hne] with t ht
    field_simp [ht]
    ring
  have hm : m = -1 := tendsto_nhds_unique hq hslope
  refine ⟨hm, ?_⟩
  rw [hm] at hr
  have hh : Tendsto (fun t : ℝ ↦ foliumY t - ((-1) * foliumX t + b))
      L (𝓝 ((-1 : ℝ) - b)) := by
    apply (hsum.sub_const b).congr'
    filter_upwards with t
    ring
  have hb : (-1 : ℝ) - b = 0 := tendsto_nhds_unique hh hr
  linarith

theorem folium_pole_affine_asymptote_unique (m b : ℝ) :
    (Tendsto (fun t : ℝ ↦ foliumY t - (m * foliumX t + b)) (𝓝[>] (-1 : ℝ)) (𝓝 0) ↔
      m = -1 ∧ b = -1) ∧
    (Tendsto (fun t : ℝ ↦ foliumY t - (m * foliumX t + b)) (𝓝[<] (-1 : ℝ)) (𝓝 0) ↔
      m = -1 ∧ b = -1) := by
  have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[≠] (-1 : ℝ)) (𝓝 (-1 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hD : ∀ᶠ t : ℝ in 𝓝[≠] (-1 : ℝ), t ∈ foliumParameterDomain := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t ≠ -1
    simpa only [mem_compl_iff, mem_singleton_iff] using ht
  have ht0 : ∀ᶠ t : ℝ in 𝓝[≠] (-1 : ℝ), t ≠ 0 :=
    (hid.eventually (eventually_lt_nhds (by norm_num : (-1 : ℝ) < 0))).mono (fun _ ht ↦ ht.ne)
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] (-1 : ℝ), foliumX t ≠ 0 := by
    filter_upwards [hD, ht0] with t ht h0
    intro hX
    exact h0 ((folium_origin_and_coordinate_zero ht).1.mp hX)
  have hslope : Tendsto (fun t : ℝ ↦ foliumY t / foliumX t)
      (𝓝[≠] (-1 : ℝ)) (𝓝 (-1 : ℝ)) := by
    apply hid.congr'
    filter_upwards [hD, ht0] with t ht h0
    exact (folium_parameter_recovery ht h0).symm
  have hsum : Tendsto (fun t : ℝ ↦ foliumX t + foliumY t)
      (𝓝[≠] (-1 : ℝ)) (𝓝 (-1 : ℝ)) := by
    have hh := folium_pole_affine_residual_tendsto_zero.sub_const 1
    apply (show Tendsto (fun t : ℝ ↦ (foliumX t + foliumY t + 1) - 1)
      (𝓝[≠] (-1 : ℝ)) (𝓝 (-1 : ℝ)) from by simpa only [zero_sub] using! hh).congr'
    filter_upwards with t
    ring
  have hr := nhdsGT_le_nhdsNE (-1 : ℝ)
  have hl := nhdsLT_le_nhdsNE (-1 : ℝ)
  constructor
  · constructor
    · intro h
      exact folium_affine_asymptote_coefficients_unique
        (tendsto_inv_atBot_zero.comp folium_actual_two_sided_pole_limits.1)
        (Filter.Eventually.filter_mono hr hne) (hslope.mono_left hr) (hsum.mono_left hr) m b h
    · rintro ⟨rfl, rfl⟩
      apply (folium_pole_affine_residual_tendsto_zero.mono_left hr).congr'
      filter_upwards with t
      ring
  · constructor
    · intro h
      exact folium_affine_asymptote_coefficients_unique
        (tendsto_inv_atTop_zero.comp folium_actual_two_sided_pole_limits.2.2.1)
        (Filter.Eventually.filter_mono hl hne) (hslope.mono_left hl) (hsum.mono_left hl) m b h
    · rintro ⟨rfl, rfl⟩
      apply (folium_pole_affine_residual_tendsto_zero.mono_left hl).congr'
      filter_upwards with t
      ring

theorem folium_affine_distance_zero_iff_residual_zero {L : Filter ℝ} (m b : ℝ) :
    Tendsto (foliumAffineLineDistance m b) L (𝓝 0) ↔
      Tendsto (fun t : ℝ ↦ foliumY t - (m * foliumX t + b)) L (𝓝 0) := by
  have hK : Real.sqrt (m ^ 2 + 1) ≠ 0 :=
    (Real.sqrt_pos.2 (by nlinarith [sq_nonneg m] : 0 < m ^ 2 + 1)).ne'
  constructor
  · intro h
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hh := h.mul_const (Real.sqrt (m ^ 2 + 1))
    apply (show Tendsto (fun t : ℝ ↦ foliumAffineLineDistance m b t * Real.sqrt (m ^ 2 + 1))
      L (𝓝 0) from by simpa only [zero_mul] using! hh).congr'
    filter_upwards with t
    exact div_mul_cancel₀ _ hK
  · intro h
    simpa only [foliumAffineLineDistance, abs_zero, zero_div] using!
      h.abs.div_const (Real.sqrt (m ^ 2 + 1))

theorem folium_geometric_asymptote_unique (m b : ℝ) :
    (Tendsto (foliumAffineLineDistance m b) (𝓝[>] (-1 : ℝ)) (𝓝 0) ↔ m = -1 ∧ b = -1) ∧
    (Tendsto (foliumAffineLineDistance m b) (𝓝[<] (-1 : ℝ)) (𝓝 0) ↔ m = -1 ∧ b = -1) := by
  rw [folium_affine_distance_zero_iff_residual_zero, folium_affine_distance_zero_iff_residual_zero]
  exact folium_pole_affine_asymptote_unique m b

theorem folium_pole_vertical_line_distance_diverges (c : ℝ) :
    Tendsto (fun t : ℝ ↦ |foliumX t - c|) (𝓝[>] (-1 : ℝ)) atTop ∧
      Tendsto (fun t : ℝ ↦ |foliumX t - c|) (𝓝[<] (-1 : ℝ)) atTop := by
  have hR : Tendsto (fun t : ℝ ↦ foliumX t - c) (𝓝[>] (-1 : ℝ)) atBot := by
    refine tendsto_atBot.2 (fun b ↦ ?_)
    filter_upwards [folium_actual_two_sided_pole_limits.1.eventually
      (eventually_le_atBot (b + c))] with t ht
    linarith
  have hL : Tendsto (fun t : ℝ ↦ foliumX t - c) (𝓝[<] (-1 : ℝ)) atTop := by
    refine tendsto_atTop.2 (fun b ↦ ?_)
    filter_upwards [folium_actual_two_sided_pole_limits.2.2.1.eventually
      (eventually_ge_atTop (b + c))] with t ht
    linarith
  constructor
  · have hn := tendsto_neg_atBot_atTop.comp hR
    apply hn.congr'
    filter_upwards [hR.eventually (eventually_lt_atBot (0 : ℝ))] with t ht
    simpa only [Function.comp_def] using (abs_of_neg ht).symm
  · apply hL.congr'
    filter_upwards [hL.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    exact (abs_of_pos ht).symm

/-- Bài 15(b): khảo sát lá Descartes, gồm hai nhánh qua gốc và tiệm cận. -/
theorem source_folium_parametric_curve_investigation :
    (foliumCurve = {p : ℝ × ℝ | p.1 ^ 3 + p.2 ^ 3 = 3 * p.1 * p.2}) ∧
    InjOn (parametricPoint foliumX foliumY) foliumParameterDomain ∧
    (∀ t ∈ foliumParameterDomain, HasDerivAt foliumX (foliumDX t) t ∧ HasDerivAt foliumY (foliumDY t) t) ∧
    (∀ t ∈ foliumParameterDomain, foliumDX t ≠ 0 ∨ foliumDY t ≠ 0) ∧
    (∀ t ∈ foliumParameterDomain, (0 < foliumDX t ↔ t ^ 3 < 1 / 2) ∧
      (foliumDX t = 0 ↔ t ^ 3 = 1 / 2) ∧ (foliumDX t < 0 ↔ 1 / 2 < t ^ 3) ∧
      (0 < foliumDY t ↔ 0 < t ∧ t ^ 3 < 2) ∧
      (foliumDY t = 0 ↔ t = 0 ∨ t ^ 3 = 2) ∧ (foliumDY t < 0 ↔ t < 0 ∨ 2 < t ^ 3)) ∧
    (Tendsto foliumX atTop (𝓝 0) ∧ Tendsto foliumY atTop (𝓝 0) ∧
      Tendsto foliumX atBot (𝓝 0) ∧ Tendsto foliumY atBot (𝓝 0)) ∧
    (Tendsto foliumX (𝓝[>] (-1 : ℝ)) atBot ∧ Tendsto foliumY (𝓝[>] (-1 : ℝ)) atTop ∧
      Tendsto foliumX (𝓝[<] (-1 : ℝ)) atTop ∧ Tendsto foliumY (𝓝[<] (-1 : ℝ)) atBot) ∧
    (Tendsto foliumAsymptoteDistance (𝓝[>] (-1 : ℝ)) (𝓝 0) ∧
      Tendsto foliumAsymptoteDistance (𝓝[<] (-1 : ℝ)) (𝓝 0)) ∧
    (∀ x y : ℝ, x ^ 3 + y ^ 3 = 3 * x * y → x + y + 1 ≠ 0) := by
  exact ⟨folium_complete_image, folium_finite_parameter_injective,
    fun _ ht ↦ folium_actual_first_derivatives ht,
    fun _ ht ↦ folium_regular_every_source_parameter ht,
    fun _ ht ↦ folium_full_first_derivative_signs ht,
    folium_both_parameter_infinite_ends_return_origin, folium_actual_two_sided_pole_limits,
    folium_geometric_asymptote_both_sides, fun _ _ h ↦ folium_entire_asymptote_line_excluded h⟩

end calculus.Chapter04.Section04FoliumParametricCurveInvestigation
