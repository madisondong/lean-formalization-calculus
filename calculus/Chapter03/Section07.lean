import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Normed.Field.Lemmas

/-! §3.7 — so sánh bằng thương và các phép toán. Nguồn: dòng 3193–3299. Các quan hệ so sánh dùng lọc tiếp cận khác ⊥. -/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07
open calculus.Chapter03.Section02


inductive LimitApproach where
  | point (a : ℝ)
  | positiveInfinity
  | negativeInfinity


def domainApproachFilter (D : Set ℝ) : LimitApproach → Filter ℝ
  | .point a => 𝓝[D \ {a}] a
  | .positiveInfinity => atTop ⊓ 𝓟 D
  | .negativeInfinity => atBot ⊓ 𝓟 D


def NontrivialDomainApproach (D : Set ℝ) (p : LimitApproach) : Prop :=
  (domainApproachFilter D p).NeBot

theorem properLimitApproach_point_iff (D : Set ℝ) (a : ℝ) :
    NontrivialDomainApproach D (.point a) ↔ AccumulationPointOf D a :=
  accumulationPointOf_iff_neBot.symm

theorem properLimitApproach_positiveInfinity_iff (D : Set ℝ) :
    NontrivialDomainApproach D .positiveInfinity ↔ ¬ BddAbove D := by
  change (atTop ⊓ 𝓟 D : Filter ℝ).NeBot ↔ ¬ BddAbove D
  rw [atTop_basis_Ioi.inf_principal_neBot_iff, not_bddAbove_iff]
  constructor
  · intro h a
    obtain ⟨x, hx⟩ := h (i := a) trivial
    exact ⟨x, hx.2, hx.1⟩
  · intro h a _
    obtain ⟨x, hx, ha⟩ := h a
    exact ⟨x, ha, hx⟩

theorem properLimitApproach_negativeInfinity_iff (D : Set ℝ) :
    NontrivialDomainApproach D .negativeInfinity ↔ ¬ BddBelow D := by
  change (atBot ⊓ 𝓟 D : Filter ℝ).NeBot ↔ ¬ BddBelow D
  rw [atBot_basis_Iio.inf_principal_neBot_iff, not_bddBelow_iff]
  constructor
  · intro h a
    obtain ⟨x, hx⟩ := h (i := a) trivial
    exact ⟨x, hx.2, hx.1⟩
  · intro h a _
    obtain ⟨x, hx, ha⟩ := h a
    exact ⟨x, ha, hx⟩

/-- Định nghĩa 3.7.1(a): f=o(g) khi f/g→0 và g≠0 trên một tập thuộc lọc tiếp cận. -/
def NonvanishingDenominatorLittleOAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  NontrivialDomainApproach D p ∧
    (∀ᶠ x in domainApproachFilter D p, g x ≠ 0) ∧
    Tendsto (fun x ↦ f x / g x) (domainApproachFilter D p) (𝓝 0)

/-- Định nghĩa 3.7.1(b): f và g cùng bậc khi f/g có giới hạn hữu hạn khác 0 và g≠0 trên một tập thuộc lọc tiếp cận. -/
def NonzeroRatioLimitAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  NontrivialDomainApproach D p ∧
    (∀ᶠ x in domainApproachFilter D p, g x ≠ 0) ∧
    ∃ C : ℝ, C ≠ 0 ∧ Tendsto (fun x ↦ f x / g x) (domainApproachFilter D p) (𝓝 C)

/-- Định nghĩa 3.7.1(c): f tương đương g khi f/g→1 và g≠0 trên một tập thuộc lọc tiếp cận. -/
def NonvanishingAsymptoticEquivalenceAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  NontrivialDomainApproach D p ∧
    (∀ᶠ x in domainApproachFilter D p, g x ≠ 0) ∧
    Tendsto (fun x ↦ f x / g x) (domainApproachFilter D p) (𝓝 1)

variable {D : Set ℝ} {p : LimitApproach} {f g h k : ℝ → ℝ}


theorem nonvanishingDenominatorLittleOAlong_iff_mathlib :
    NonvanishingDenominatorLittleOAlong D p f g ↔ NontrivialDomainApproach D p ∧
      (∀ᶠ x in domainApproachFilter D p, g x ≠ 0) ∧
      Asymptotics.IsLittleO (domainApproachFilter D p) f g := by
  unfold NonvanishingDenominatorLittleOAlong
  refine and_congr_right fun _ ↦ and_congr_right fun hg ↦ ?_
  exact (Asymptotics.isLittleO_iff_tendsto' (hg.mono fun _ hx he ↦ (hx he).elim)).symm

/-- Mệnh đề 3.7.4(i): tổng với cùng hàm so sánh. -/
theorem nonvanishingDenominatorLittleOAlong_add (hf : NonvanishingDenominatorLittleOAlong D p f h) (hg : NonvanishingDenominatorLittleOAlong D p g h) :
    NonvanishingDenominatorLittleOAlong D p (fun x ↦ f x + g x) h := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  simpa only [zero_add, add_div] using hf.2.2.add hg.2.2

/-- Mệnh đề 3.7.4(ii): nhân quan hệ o với một hằng số thực. -/
theorem nonvanishingDenominatorLittleOAlong_const_mul (hf : NonvanishingDenominatorLittleOAlong D p f h) (c : ℝ) :
    NonvanishingDenominatorLittleOAlong D p (fun x ↦ c * f x) h := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  simpa only [mul_zero, mul_div_assoc] using (tendsto_const_nhds (x := c)).mul hf.2.2

/-- Mệnh đề 3.7.4(iii): tích hai quan hệ o. -/
theorem nonvanishingDenominatorLittleOAlong_mul (hf : NonvanishingDenominatorLittleOAlong D p f h) (hg : NonvanishingDenominatorLittleOAlong D p g k) :
    NonvanishingDenominatorLittleOAlong D p (fun x ↦ f x * g x) (fun x ↦ h x * k x) := by
  refine ⟨hf.1, ?_, ?_⟩
  · filter_upwards [hf.2.1, hg.2.1] with x hx hk
    exact mul_ne_zero hx hk
  · simpa only [zero_mul, div_mul_div_comm] using hf.2.2.mul hg.2.2

/-- Nhận xét 3.7.5: đặc trưng f=o(1) bằng giới hạn 0. -/
theorem nonvanishingDenominatorLittleOAlong_one_iff :
    NonvanishingDenominatorLittleOAlong D p f (fun _ ↦ 1) ↔
      NontrivialDomainApproach D p ∧ Tendsto f (domainApproachFilter D p) (𝓝 0) := by
  simp [NonvanishingDenominatorLittleOAlong]

/-- Mệnh đề 3.7.6(i): nhân quan hệ cùng bậc với một hằng số khác 0. -/
theorem nonzeroRatioLimitAlong_const_mul (hf : NonzeroRatioLimitAlong D p f h) {c : ℝ} (hc : c ≠ 0) :
    NonzeroRatioLimitAlong D p (fun x ↦ c * f x) h := by
  obtain ⟨C, hC, ht⟩ := hf.2.2
  refine ⟨hf.1, hf.2.1, c * C, mul_ne_zero hc hC, ?_⟩
  simpa only [mul_div_assoc] using (tendsto_const_nhds (x := c)).mul ht

/-- Mệnh đề 3.7.6(ii): tích hai quan hệ cùng bậc. -/
theorem nonzeroRatioLimitAlong_mul (hf : NonzeroRatioLimitAlong D p f h) (hg : NonzeroRatioLimitAlong D p g k) :
    NonzeroRatioLimitAlong D p (fun x ↦ f x * g x) (fun x ↦ h x * k x) := by
  obtain ⟨C, hC, ht⟩ := hf.2.2
  obtain ⟨M, hM, hu⟩ := hg.2.2
  refine ⟨hf.1, ?_, C * M, mul_ne_zero hC hM, ?_⟩
  · filter_upwards [hf.2.1, hg.2.1] with x hx hk
    exact mul_ne_zero hx hk
  · simpa only [div_mul_div_comm] using ht.mul hu

/-- Nhận xét 3.7.7: đặc trưng f cùng bậc với 1 bằng giới hạn hữu hạn khác 0. -/
theorem nonzeroRatioLimitAlong_one_iff :
    NonzeroRatioLimitAlong D p f (fun _ ↦ 1) ↔ NontrivialDomainApproach D p ∧
      ∃ C : ℝ, C ≠ 0 ∧ Tendsto f (domainApproachFilter D p) (𝓝 C) := by
  simp [NonzeroRatioLimitAlong]

/-- Mệnh đề 3.7.8(i): tích các hàm tương đương. -/
theorem nonvanishingAsymptoticEquivalenceAlong_mul (hf : NonvanishingAsymptoticEquivalenceAlong D p f h) (hg : NonvanishingAsymptoticEquivalenceAlong D p g k) :
    NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ f x * g x) (fun x ↦ h x * k x) := by
  refine ⟨hf.1, ?_, ?_⟩
  · filter_upwards [hf.2.1, hg.2.1] with x hx hk
    exact mul_ne_zero hx hk
  · simpa only [one_mul, div_mul_div_comm] using hf.2.2.mul hg.2.2


theorem nonvanishingAsymptoticEquivalenceAlong_eventually_numerator_ne (hf : NonvanishingAsymptoticEquivalenceAlong D p f g) :
    ∀ᶠ x in domainApproachFilter D p, f x ≠ 0 := by
  have hn := hf.2.2.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  filter_upwards [hn] with x hx
  exact (div_ne_zero_iff.mp hx).1

/-- Mệnh đề 3.7.8(ii): tính tương đương của hai hàm nghịch đảo trên miền xác định. -/
theorem nonvanishingAsymptoticEquivalenceAlong_inv (hf : NonvanishingAsymptoticEquivalenceAlong D p f g) :
    NonvanishingAsymptoticEquivalenceAlong D p (fun x ↦ 1 / f x) (fun x ↦ 1 / g x) := by
  refine ⟨hf.1, ?_, ?_⟩
  · exact hf.2.1.mono fun x hx ↦ one_div_ne_zero hx
  · have ht := hf.2.2.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    apply (show Tendsto (fun x ↦ (f x / g x)⁻¹) (domainApproachFilter D p) (𝓝 1) from by simpa using ht).congr'
    filter_upwards [hf.2.1, nonvanishingAsymptoticEquivalenceAlong_eventually_numerator_ne hf] with x hx hfx
    field_simp


theorem nonvanishingAsymptoticEquivalenceAlong_symm (hf : NonvanishingAsymptoticEquivalenceAlong D p f g) :
    NonvanishingAsymptoticEquivalenceAlong D p g f := by
  refine ⟨hf.1, nonvanishingAsymptoticEquivalenceAlong_eventually_numerator_ne hf, ?_⟩
  have ht : Tendsto (fun x ↦ (f x / g x)⁻¹) (domainApproachFilter D p) (𝓝 1) := by
    simpa using hf.2.2.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [hf.2.1, nonvanishingAsymptoticEquivalenceAlong_eventually_numerator_ne hf] with x hx hfx
  field_simp

/-- Bổ đề cho Mệnh đề 3.7.8(iii): f∼g và g=o(h) suy ra f=o(h). -/
theorem nonvanishingAsymptoticEquivalenceAlong_trans_littleO (hf : NonvanishingAsymptoticEquivalenceAlong D p f g) (hg : NonvanishingDenominatorLittleOAlong D p g h) :
    NonvanishingDenominatorLittleOAlong D p f h := by
  refine ⟨hf.1, hg.2.1, ?_⟩
  apply (show Tendsto (fun x ↦ (f x / g x) * (g x / h x))
      (domainApproachFilter D p) (𝓝 0) from by simpa using hf.2.2.mul hg.2.2).congr'
  filter_upwards [hf.2.1] with x hx
  field_simp

/-- Nhận xét 3.7.9(i): quan hệ tương đương có tính bắc cầu. -/
theorem nonvanishingAsymptoticEquivalenceAlong_trans (hf : NonvanishingAsymptoticEquivalenceAlong D p f g) (hg : NonvanishingAsymptoticEquivalenceAlong D p g h) :
    NonvanishingAsymptoticEquivalenceAlong D p f h := by
  refine ⟨hf.1, hg.2.1, ?_⟩
  apply (show Tendsto (fun x ↦ (f x / g x) * (g x / h x))
      (domainApproachFilter D p) (𝓝 1) from by simpa using hf.2.2.mul hg.2.2).congr'
  filter_upwards [hf.2.1] with x hx
  field_simp

/-- Nhận xét 3.7.9(ii): f tương đương g khi và chỉ khi f−g=o(g). -/
theorem nonvanishingAsymptoticEquivalenceAlong_iff_sub_littleO (hp : NontrivialDomainApproach D p)
    (hg : ∀ᶠ x in domainApproachFilter D p, g x ≠ 0) :
    NonvanishingAsymptoticEquivalenceAlong D p f g ↔ NonvanishingDenominatorLittleOAlong D p (fun x ↦ f x - g x) g := by
  constructor
  · intro hf
    refine ⟨hp, hg, ?_⟩
    apply (show Tendsto (fun x ↦ f x / g x - 1) (domainApproachFilter D p) (𝓝 0) from by
      simpa using hf.2.2.sub (tendsto_const_nhds (x := (1 : ℝ)))).congr'
    filter_upwards [hg] with x hx
    field_simp
  · intro hf
    refine ⟨hp, hg, ?_⟩
    apply (show Tendsto (fun x ↦ (f x - g x) / g x + 1) (domainApproachFilter D p) (𝓝 1) from by
      simpa using hf.2.2.add (tendsto_const_nhds (x := (1 : ℝ)))).congr'
    filter_upwards [hg] with x hx
    field_simp
    ring

/-- Định nghĩa 3.7.10: đại lượng vô cùng bé. -/
def InfinitesimalAlong (D : Set ℝ) (p : LimitApproach) (f : ℝ → ℝ) : Prop :=
  NontrivialDomainApproach D p ∧ Tendsto f (domainApproachFilter D p) (𝓝 0)

/-- Định nghĩa 3.7.10: đại lượng vô cùng lớn có trị tuyệt đối tiến đến +∞. -/
def InfiniteMagnitudeAlong (D : Set ℝ) (p : LimitApproach) (f : ℝ → ℝ) : Prop :=
  NontrivialDomainApproach D p ∧ Tendsto (fun x ↦ |f x|) (domainApproachFilter D p) atTop

/-- Dòng 3296: nếu f→0 và f≠0 trên một tập thuộc lọc tiếp cận thì |1/f|→+∞. -/
theorem infinitesimalAlong_reciprocal_infinite (hf : InfinitesimalAlong D p f)
    (hn : ∀ᶠ x in domainApproachFilter D p, f x ≠ 0) :
    InfiniteMagnitudeAlong D p (fun x ↦ 1 / f x) := by
  refine ⟨hf.1, ?_⟩
  have ht : Tendsto f (domainApproachFilter D p) (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hf.2, by simpa only [mem_compl_iff, mem_singleton_iff] using hn⟩
  simpa only [Function.comp_def, Real.norm_eq_abs, one_div] using
    (tendsto_norm_inv_nhdsNE_zero_atTop.comp ht)

/-- Dòng 3297: nghịch đảo của đại lượng vô cùng lớn là vô cùng bé. -/
theorem infiniteMagnitudeAlong_reciprocal_infinitesimal (hf : InfiniteMagnitudeAlong D p f) :
    InfinitesimalAlong D p (fun x ↦ 1 / f x) := by
  refine ⟨hf.1, ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.norm_eq_abs, abs_div, abs_one, one_div, abs_inv] using
    (tendsto_inv_atTop_zero.comp hf.2)


theorem printed_infinitesimal_reciprocal_false (hp : NontrivialDomainApproach D p) :
    InfinitesimalAlong D p (fun _ ↦ 0) ∧
      ¬ InfiniteMagnitudeAlong D p (fun _ ↦ 1 / (0 : ℝ)) := by
  refine ⟨⟨hp, tendsto_const_nhds⟩, ?_⟩
  intro hi
  let : (domainApproachFilter D p).NeBot := hp
  have hh : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (domainApproachFilter D p) atTop := by
    simpa only [div_zero, abs_zero] using hi.2
  exact not_tendsto_nhds_of_tendsto_atTop hh 0 tendsto_const_nhds

/-- Dòng 3300–3307: so sánh các đại lượng vô cùng bé. -/
def HigherOrderInfinitesimalAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  InfinitesimalAlong D p f ∧ InfinitesimalAlong D p g ∧ NonvanishingDenominatorLittleOAlong D p f g

def InfinitesimalsWithNonzeroRatioLimitAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  InfinitesimalAlong D p f ∧ InfinitesimalAlong D p g ∧ NonzeroRatioLimitAlong D p f g

def EquivalentInfinitesimalsAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  InfinitesimalAlong D p f ∧ InfinitesimalAlong D p g ∧ NonvanishingAsymptoticEquivalenceAlong D p f g

/-- Dòng 3343–3350: so sánh các đại lượng vô cùng lớn. -/
def LowerOrderInfiniteMagnitudeAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  InfiniteMagnitudeAlong D p f ∧ InfiniteMagnitudeAlong D p g ∧ NonvanishingDenominatorLittleOAlong D p f g

def InfiniteMagnitudesWithNonzeroRatioLimitAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  InfiniteMagnitudeAlong D p f ∧ InfiniteMagnitudeAlong D p g ∧ NonzeroRatioLimitAlong D p f g

def EquivalentInfiniteMagnitudeFunctionsAlong (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  InfiniteMagnitudeAlong D p f ∧ InfiniteMagnitudeAlong D p g ∧ NonvanishingAsymptoticEquivalenceAlong D p f g


def nonzeroReciprocalDomain (D : Set ℝ) (f : ℝ → ℝ) : Set ℝ :=
  {x ∈ D | f x ≠ 0}


theorem not_properLimitApproach_empty (p : LimitApproach) :
    ¬ NontrivialDomainApproach (∅ : Set ℝ) p := by
  cases p <;> simp [NontrivialDomainApproach, domainApproachFilter]

/-- Dòng 3296: hàm hằng 0 là vô cùng bé nhưng có miền nghịch đảo rỗng. -/
theorem zero_infinitesimal_reciprocal_domain_obstruction
    (hp : NontrivialDomainApproach D p) :
    InfinitesimalAlong D p (fun _ ↦ 0) ∧
      nonzeroReciprocalDomain D (fun _ ↦ 0) = ∅ ∧
      ¬ NontrivialDomainApproach (nonzeroReciprocalDomain D (fun _ ↦ 0)) p := by
  have hd : nonzeroReciprocalDomain D (fun _ ↦ 0) = ∅ := by
    ext x
    simp [nonzeroReciprocalDomain]
  refine ⟨⟨hp, tendsto_const_nhds⟩, hd, ?_⟩
  rw [hd]
  exact not_properLimitApproach_empty p


theorem domainApproachFilter_eq_univ_inf_principal (D : Set ℝ) (p : LimitApproach) :
    domainApproachFilter D p = domainApproachFilter univ p ⊓ 𝓟 D := by
  cases p with
  | point a =>
    simpa only [domainApproachFilter, sdiff_eq, univ_inter, inter_comm] using
      nhdsWithin_inter' a ({a}ᶜ) D
  | positiveInfinity =>
    simp only [domainApproachFilter, principal_univ, inf_top_eq]
  | negativeInfinity =>
    simp only [domainApproachFilter, principal_univ, inf_top_eq]


theorem domainApproachFilter_eq_univ_of_eventually_mem
    (hD : ∀ᶠ x in domainApproachFilter univ p, x ∈ D) :
    domainApproachFilter D p = domainApproachFilter univ p := by
  rw [domainApproachFilter_eq_univ_inf_principal]
  exact inf_eq_left.mpr (le_principal_iff.mpr hD)


theorem nonvanishingDenominatorLittleOAlong_iff_univ_of_eventually_mem
    (hD : ∀ᶠ x in domainApproachFilter univ p, x ∈ D) :
    NonvanishingDenominatorLittleOAlong D p f g ↔ NonvanishingDenominatorLittleOAlong univ p f g := by
  simp only [NonvanishingDenominatorLittleOAlong, NontrivialDomainApproach,
    domainApproachFilter_eq_univ_of_eventually_mem hD]


theorem nonzeroRatioLimitAlong_iff_univ_of_eventually_mem
    (hD : ∀ᶠ x in domainApproachFilter univ p, x ∈ D) :
    NonzeroRatioLimitAlong D p f g ↔ NonzeroRatioLimitAlong univ p f g := by
  simp only [NonzeroRatioLimitAlong, NontrivialDomainApproach,
    domainApproachFilter_eq_univ_of_eventually_mem hD]


theorem nonvanishingAsymptoticEquivalenceAlong_iff_univ_of_eventually_mem
    (hD : ∀ᶠ x in domainApproachFilter univ p, x ∈ D) :
    NonvanishingAsymptoticEquivalenceAlong D p f g ↔ NonvanishingAsymptoticEquivalenceAlong univ p f g := by
  simp only [NonvanishingAsymptoticEquivalenceAlong, NontrivialDomainApproach,
    domainApproachFilter_eq_univ_of_eventually_mem hD]

end calculus.Chapter03.Section07
