import calculus.Chapter03.Section07Orders

/-!
# §3.7 — Bài tập 3.7.2: tổng hai đơn thức tương đương

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 3479–3481. Các số mũ m,n∈ℝ cố định; lũy thừa xét trên miền của §3.1.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section07MonomialSums

open calculus.Chapter03.Section07
open calculus.Chapter03.Section07AlgebraSupplement
open calculus.Chapter03.Section07Orders


theorem nonvanishingAsymptoticEquivalenceAlong_const_mul_coefficient_ne_zero
    {D : Set ℝ} {p : LimitApproach} {f φ : ℝ → ℝ} {C : ℝ}
    (hf : NonvanishingAsymptoticEquivalenceAlong D p f (fun x ↦ C * φ x)) : C ≠ 0 := by
  let : (domainApproachFilter D p).NeBot := hf.1
  obtain ⟨x, hx⟩ := hf.2.1.exists
  exact (mul_ne_zero_iff.mp hx).1


theorem nonvanishingAsymptoticEquivalenceAlong_comparison_infinitesimal
    {D : Set ℝ} {p : LimitApproach} {f g : ℝ → ℝ}
    (hf : InfinitesimalAlong D p f) (hfg : NonvanishingAsymptoticEquivalenceAlong D p f g) :
    InfinitesimalAlong D p g := by
  exact ⟨hf.1, (nonvanishingAsymptoticEquivalenceAlong_mathlib hfg).tendsto_nhds hf.2⟩


theorem nonvanishingAsymptoticEquivalenceAlong_add_of_left_littleO
    {D : Set ℝ} {p : LimitApproach} {f g h : ℝ → ℝ}
    (hf : NonvanishingDenominatorLittleOAlong D p f h) (hg : NonvanishingAsymptoticEquivalenceAlong D p g h) :
    NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ f x + g x) h := by
  refine ⟨hg.1, hg.2.1, ?_⟩
  simpa only [zero_add, add_div] using hf.2.2.add hg.2.2


theorem nonvanishingAsymptoticEquivalenceAlong_add_of_left_dominated
    {D : Set ℝ} {p : LimitApproach} {f g A B : ℝ → ℝ}
    (hf : NonvanishingAsymptoticEquivalenceAlong D p f A) (hg : NonvanishingAsymptoticEquivalenceAlong D p g B)
    (hAB : NonvanishingDenominatorLittleOAlong D p A B) :
    NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ f x + g x) (fun x ↦ A x + B x) := by
  have hBB : NonvanishingAsymptoticEquivalenceAlong D p B B := by
    refine ⟨hg.1, hg.2.1, ?_⟩
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [hg.2.1] with x hx
    exact (div_self hx).symm
  have hsum : NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ f x + g x) B :=
    nonvanishingAsymptoticEquivalenceAlong_add_of_left_littleO (nonvanishingAsymptoticEquivalenceAlong_trans_littleO hf hAB) hg
  have hcomparison : NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ A x + B x) B :=
    nonvanishingAsymptoticEquivalenceAlong_add_of_left_littleO hAB hBB
  exact nonvanishingAsymptoticEquivalenceAlong_trans hsum (nonvanishingAsymptoticEquivalenceAlong_symm hcomparison)


theorem nonvanishingAsymptoticEquivalenceAlong_add_common_basis
    {D : Set ℝ} {p : LimitApproach} {f g φ : ℝ → ℝ} {α β : ℝ}
    (hf : NonvanishingAsymptoticEquivalenceAlong D p f (fun x ↦ α * φ x))
    (hg : NonvanishingAsymptoticEquivalenceAlong D p g (fun x ↦ β * φ x)) (hαβ : α + β ≠ 0) :
    NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ f x + g x) (fun x ↦ α * φ x + β * φ x) := by
  have hα : α ≠ 0 := nonvanishingAsymptoticEquivalenceAlong_const_mul_coefficient_ne_zero hf
  have hβ : β ≠ 0 := nonvanishingAsymptoticEquivalenceAlong_const_mul_coefficient_ne_zero hg
  refine ⟨hf.1, ?_, ?_⟩
  · filter_upwards [hf.2.1] with x hx
    rw [← add_mul]
    exact mul_ne_zero hαβ (mul_ne_zero_iff.mp hx).2
  · have ht : Tendsto
        (fun x ↦ (α * (f x / (α * φ x)) + β * (g x / (β * φ x))) / (α + β))
        (domainApproachFilter D p) (𝓝 1) := by
      have hw := ((tendsto_const_nhds (x := α)).mul hf.2.2).add
        ((tendsto_const_nhds (x := β)).mul hg.2.2)
      simpa only [mul_one, div_self hαβ] using hw.div_const (α + β)
    apply ht.congr'
    exact Eventually.of_forall fun x ↦ by
      change (α * (f x / (α * φ x)) + β * (g x / (β * φ x))) / (α + β) =
        (f x + g x) / (α * φ x + β * φ x)
      rw [← mul_div_assoc α (f x) (α * φ x), mul_div_mul_left (f x) (φ x) hα,
        ← mul_div_assoc β (g x) (β * φ x), mul_div_mul_left (g x) (φ x) hβ,
        ← add_div, div_div, mul_comm (φ x) (α + β), ← add_mul]


theorem infinitesimal_monomial_point_eq_zero
    {D : Set ℝ} {f : ℝ → ℝ} {α m a : ℝ}
    (hf : InfinitesimalAlong D (.point a) f)
    (heq : NonvanishingAsymptoticEquivalenceAlong D (.point a) f (fun x ↦ α * x ^ m))
    (hm : EventuallyRealPowerDefinedAlong D (.point a) (fun x ↦ x) m) : a = 0 := by
  by_contra ha
  let : (domainApproachFilter D (.point a)).NeBot := hf.1
  have hα : α ≠ 0 := nonvanishingAsymptoticEquivalenceAlong_const_mul_coefficient_ne_zero heq
  have hcomparison := nonvanishingAsymptoticEquivalenceAlong_comparison_infinitesimal hf heq
  have hzero : Tendsto (fun x ↦ |α * x ^ m|)
      (domainApproachFilter D (.point a)) (𝓝 0) := by
    simpa only [abs_zero] using hcomparison.2.abs
  have hid : Tendsto (fun x : ℝ ↦ x) (domainApproachFilter D (.point a)) (𝓝 a) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpower : Tendsto (fun x ↦ |x| ^ m)
      (domainApproachFilter D (.point a)) (𝓝 (|a| ^ m)) :=
    hid.abs.rpow_const (Or.inl (abs_ne_zero.mpr ha))
  have hlimit : Tendsto (fun x ↦ |α * x ^ m|)
      (domainApproachFilter D (.point a)) (𝓝 (|α| * |a| ^ m)) := by
    apply ((tendsto_const_nhds (x := |α|)).mul hpower).congr'
    filter_upwards [hm] with x hx

    rw [abs_mul, real_power_abs hx]
  have he : |α| * |a| ^ m = 0 := tendsto_nhds_unique hlimit hzero
  exact (mul_pos (abs_pos.mpr hα) (Real.rpow_pos_of_pos (abs_pos.mpr ha) m)).ne' he


theorem nonvanishingAsymptoticEquivalenceAlong_add_monomials_of_abs_infinite
    {D : Set ℝ} {p : LimitApproach} {f g : ℝ → ℝ} {α β m n : ℝ}
    (hid : InfiniteMagnitudeAlong D p (fun x ↦ x))
    (hm : EventuallyRealPowerDefinedAlong D p (fun x ↦ x) m)
    (hn : EventuallyRealPowerDefinedAlong D p (fun x ↦ x) n)
    (hf : NonvanishingAsymptoticEquivalenceAlong D p f (fun x ↦ α * x ^ m))
    (hg : NonvanishingAsymptoticEquivalenceAlong D p g (fun x ↦ β * x ^ n)) (hmn : m ≠ n) :
    NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ f x + g x) (fun x ↦ α * x ^ m + β * x ^ n) := by
  have hα : α ≠ 0 := nonvanishingAsymptoticEquivalenceAlong_const_mul_coefficient_ne_zero hf
  have hβ : β ≠ 0 := nonvanishingAsymptoticEquivalenceAlong_const_mul_coefficient_ne_zero hg
  have hbase : ∀ᶠ x in domainApproachFilter D p, x ≠ 0 :=
    (hid.2.eventually (eventually_gt_atTop (0 : ℝ))).mono fun x hx ↦ abs_pos.mp hx
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hpow : NonvanishingDenominatorLittleOAlong D p (fun x ↦ x ^ m) (fun x ↦ x ^ n) :=
      infinite_magnitude_powers_littleO hid hm hn hbase hlt
    have hAB : NonvanishingDenominatorLittleOAlong D p (fun x ↦ α * x ^ m) (fun x ↦ β * x ^ n) :=
      nonvanishingDenominatorLittleOAlong_const_mul (nonvanishingDenominatorLittleOAlong_const_mul_right hβ hpow) α
    exact nonvanishingAsymptoticEquivalenceAlong_add_of_left_dominated hf hg hAB
  · have hpow : NonvanishingDenominatorLittleOAlong D p (fun x ↦ x ^ n) (fun x ↦ x ^ m) :=
      infinite_magnitude_powers_littleO hid hn hm hbase hgt
    have hBA : NonvanishingDenominatorLittleOAlong D p (fun x ↦ β * x ^ n) (fun x ↦ α * x ^ m) :=
      nonvanishingDenominatorLittleOAlong_const_mul (nonvanishingDenominatorLittleOAlong_const_mul_right hα hpow) β
    simpa only [add_comm] using nonvanishingAsymptoticEquivalenceAlong_add_of_left_dominated hg hf hBA

/-- Bài tập 3.7.2: cộng hai đơn thức tương đương tại điểm hữu hạn hoặc ±∞. -/
theorem infinitesimal_monomial_sum_equivalent
    {D : Set ℝ} {p : LimitApproach} {f g : ℝ → ℝ} {α β m n : ℝ}
    (hf : InfinitesimalAlong D p f) (hg : InfinitesimalAlong D p g)
    (hm : EventuallyRealPowerDefinedAlong D p (fun x ↦ x) m)
    (hn : EventuallyRealPowerDefinedAlong D p (fun x ↦ x) n)
    (hfEq : NonvanishingAsymptoticEquivalenceAlong D p f (fun x ↦ α * x ^ m))
    (hgEq : NonvanishingAsymptoticEquivalenceAlong D p g (fun x ↦ β * x ^ n))
    (hsep : m ≠ n ∨ α + β ≠ 0) :
    NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ f x + g x) (fun x ↦ α * x ^ m + β * x ^ n) := by
  by_cases hmn : m = n
  · have hsum : α + β ≠ 0 := hsep.resolve_left (fun hne ↦ hne hmn)
    subst n
    exact nonvanishingAsymptoticEquivalenceAlong_add_common_basis hfEq hgEq hsum
  · cases p with
    | point a =>
      have ha : a = 0 := infinitesimal_monomial_point_eq_zero hf hfEq hm
      subst a
      have hid : InfinitesimalAlong D (.point 0) (fun x ↦ x) :=
        ⟨hg.1, tendsto_id.mono_left nhdsWithin_le_nhds⟩
      have hbase : ∀ᶠ x in domainApproachFilter D (.point 0), x ≠ 0 := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact hx.2
      have hα : α ≠ 0 := nonvanishingAsymptoticEquivalenceAlong_const_mul_coefficient_ne_zero hfEq
      have hβ : β ≠ 0 := nonvanishingAsymptoticEquivalenceAlong_const_mul_coefficient_ne_zero hgEq
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have hpow : NonvanishingDenominatorLittleOAlong D (.point 0) (fun x ↦ x ^ n) (fun x ↦ x ^ m) :=
          infinitesimalAlong_powers_littleO hid hn hm hbase hlt
        have hBA : NonvanishingDenominatorLittleOAlong D (.point 0)
            (fun x ↦ β * x ^ n) (fun x ↦ α * x ^ m) :=
          nonvanishingDenominatorLittleOAlong_const_mul (nonvanishingDenominatorLittleOAlong_const_mul_right hα hpow) β
        simpa only [add_comm] using nonvanishingAsymptoticEquivalenceAlong_add_of_left_dominated hgEq hfEq hBA
      · have hpow : NonvanishingDenominatorLittleOAlong D (.point 0) (fun x ↦ x ^ m) (fun x ↦ x ^ n) :=
          infinitesimalAlong_powers_littleO hid hm hn hbase hgt
        have hAB : NonvanishingDenominatorLittleOAlong D (.point 0)
            (fun x ↦ α * x ^ m) (fun x ↦ β * x ^ n) :=
          nonvanishingDenominatorLittleOAlong_const_mul (nonvanishingDenominatorLittleOAlong_const_mul_right hβ hpow) α
        exact nonvanishingAsymptoticEquivalenceAlong_add_of_left_dominated hfEq hgEq hAB
    | positiveInfinity =>
      apply nonvanishingAsymptoticEquivalenceAlong_add_monomials_of_abs_infinite (hm := hm) (hn := hn)
        (hf := hfEq) (hg := hgEq) (hmn := hmn)
      exact ⟨hg.1, tendsto_abs_atTop_atTop.mono_left inf_le_left⟩
    | negativeInfinity =>
      apply nonvanishingAsymptoticEquivalenceAlong_add_monomials_of_abs_infinite (hm := hm) (hn := hn)
        (hf := hfEq) (hg := hgEq) (hmn := hmn)
      exact ⟨hg.1, tendsto_abs_atBot_atTop.mono_left inf_le_left⟩

end calculus.Chapter03.Section07MonomialSums
