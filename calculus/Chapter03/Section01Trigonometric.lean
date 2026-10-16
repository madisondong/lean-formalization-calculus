import calculus.Chapter03.Section01Properties
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# 3.1. Hàm lượng giác và hàm ngược trên miền hạn chế

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 637–979.
-/

namespace calculus.Chapter03.Section01Trigonometric

open Set Function


def cosineNonzeroDomain : Set ℝ := {x | Real.cos x≠0}


def sineNonzeroDomain : Set ℝ := {x | Real.sin x≠0}


def outsideOpenUnitInterval : Set ℝ := (Ioo (-1) 1)ᶜ


noncomputable def cotangent (x : ℝ) : ℝ := Real.cos x/Real.sin x


noncomputable def secantOnDomain : cosineNonzeroDomain → ℝ := fun x => 1/Real.cos x


noncomputable def cosecantOnDomain : sineNonzeroDomain → ℝ := fun x => 1/Real.sin x


theorem cosine_nonzero_domain_iff_not_pole (x : ℝ) :
    x∈cosineNonzeroDomain ↔ ¬∃ k : ℤ, x=Real.pi/2+(k:ℝ)*Real.pi := by
  change (Real.cos x≠0) ↔ _
  rw [ne_eq,Real.cos_eq_zero_iff]
  apply not_congr
  constructor <;> rintro ⟨k,hk⟩ <;> refine ⟨k,?_⟩ <;> nlinarith [hk]


theorem sine_nonzero_domain_iff_not_zero (x : ℝ) :
    x∈sineNonzeroDomain ↔ ¬∃ k : ℤ, x=(k:ℝ)*Real.pi := by
  change (Real.sin x≠0) ↔ _
  rw [ne_eq,Real.sin_eq_zero_iff]
  simp only [eq_comm]


theorem outside_open_unit_iff_abs (x : ℝ) : x∈outsideOpenUnitInterval ↔ 1≤|x| := by
  change ¬(-1<x ∧ x<1) ↔ _
  rw [←abs_lt]
  exact not_lt


theorem outside_open_unit_ne_zero {x : ℝ} (hx : x∈outsideOpenUnitInterval) : x≠0 := by
  intro he
  subst x
  have := (outside_open_unit_iff_abs 0).mp hx
  norm_num at this


theorem inverse_unit_value_outside {x : ℝ} (hx : x≠0) (hb : |x|≤1) :
    x⁻¹∈outsideOpenUnitInterval := by
  rw [outside_open_unit_iff_abs,abs_inv]
  exact (one_le_inv₀ (abs_pos.mpr hx)).mpr hb


theorem inverse_outside_value_bounds {y : ℝ} (hy : y∈outsideOpenUnitInterval) :
    -1≤y⁻¹ ∧ y⁻¹≤1 ∧ y⁻¹≠0 := by
  have hn := outside_open_unit_ne_zero hy
  have hab : |y⁻¹|≤1 := by
    rw [abs_inv]
    exact inv_le_one_of_one_le₀ ((outside_open_unit_iff_abs y).mp hy)
  exact ⟨(abs_le.mp hab).1,(abs_le.mp hab).2,inv_ne_zero hn⟩


theorem sine_cosine_ranges : range Real.sin=Icc (-1) 1 ∧ range Real.cos=Icc (-1) 1 :=
  ⟨Real.range_sin,Real.range_cos⟩


theorem tangent_range_on_domain : range (fun x : cosineNonzeroDomain => Real.tan x)=univ := by
  ext y
  simp only [mem_range,mem_univ,iff_true]
  exact ⟨⟨Real.arctan y,(Real.cos_arctan_pos y).ne'⟩,Real.tan_arctan y⟩


theorem cot_pi_div_two_sub (x : ℝ) : cotangent (Real.pi/2-x)=Real.tan x := by
  rw [cotangent,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,Real.tan_eq_sin_div_cos]


theorem cotangent_range_on_domain : range (fun x : sineNonzeroDomain => cotangent x)=univ := by
  ext y
  simp only [mem_range,mem_univ,iff_true]
  refine ⟨⟨Real.pi/2-Real.arctan y,?_⟩,?_⟩
  · change Real.sin (Real.pi/2-Real.arctan y)≠0
    rw [Real.sin_pi_div_two_sub]
    exact (Real.cos_arctan_pos y).ne'
  · exact (cot_pi_div_two_sub _).trans (Real.tan_arctan y)


theorem secant_range_on_domain : range secantOnDomain=outsideOpenUnitInterval := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    simpa only [secantOnDomain,one_div] using inverse_unit_value_outside x.property (Real.abs_cos_le_one x)
  · intro hy
    obtain ⟨hlo,hhi,hn⟩ := inverse_outside_value_bounds hy
    refine ⟨⟨Real.arccos y⁻¹,?_⟩,?_⟩
    · change Real.cos (Real.arccos y⁻¹)≠0
      rw [Real.cos_arccos hlo hhi]
      exact hn
    · change 1/Real.cos (Real.arccos y⁻¹)=y
      rw [Real.cos_arccos hlo hhi,one_div,inv_inv]


theorem cosecant_range_on_domain : range cosecantOnDomain=outsideOpenUnitInterval := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    simpa only [cosecantOnDomain,one_div] using inverse_unit_value_outside x.property (Real.abs_sin_le_one x)
  · intro hy
    obtain ⟨hlo,hhi,hn⟩ := inverse_outside_value_bounds hy
    refine ⟨⟨Real.arcsin y⁻¹,?_⟩,?_⟩
    · change Real.sin (Real.arcsin y⁻¹)≠0
      rw [Real.sin_arcsin hlo hhi]
      exact hn
    · change 1/Real.sin (Real.arcsin y⁻¹)=y
      rw [Real.sin_arcsin hlo hhi,one_div,inv_inv]


noncomputable def sineInverseEquiv : Icc (-(Real.pi/2)) (Real.pi/2) ≃ Icc (-1:ℝ) 1 :=
  Real.sinOrderIso.toEquiv


noncomputable def cosineInverseEquiv : Icc (0:ℝ) Real.pi ≃ Icc (-1:ℝ) 1 where
  toFun := fun x => ⟨Real.cos x,Real.cos_mem_Icc x⟩
  invFun := fun y => ⟨Real.arccos y,Real.arccos_nonneg y,Real.arccos_le_pi y⟩
  left_inv := fun x => Subtype.ext (Real.arccos_cos x.property.1 x.property.2)
  right_inv := fun y => Subtype.ext (Real.cos_arccos y.property.1 y.property.2)


noncomputable def tangentInverseEquiv : Ioo (-(Real.pi/2)) (Real.pi/2) ≃ ℝ :=
  Real.tanOrderIso.toEquiv

/-- Hàm arccot có miền xác định ℝ và miền giá trị (0,π). -/
noncomputable def arccotangent (y : ℝ) : ℝ := Real.pi/2-Real.arctan y


noncomputable def cotangentInverseEquiv : Ioo (0:ℝ) Real.pi ≃ ℝ where
  toFun := fun x => cotangent x
  invFun := fun y => ⟨arccotangent y,by
    have h := Real.arctan_mem_Ioo y
    dsimp [arccotangent]
    constructor <;> linarith [h.1,h.2]⟩
  left_inv := fun x => Subtype.ext (by
    change Real.pi/2-Real.arctan (cotangent x)=x
    have he : cotangent x=Real.tan (Real.pi/2-x) := by
      have h := cot_pi_div_two_sub (Real.pi/2-x)
      have he : Real.pi/2-(Real.pi/2-(x:ℝ))=x := by ring
      rw [he] at h
      exact h
    rw [he,Real.arctan_tan (by linarith [x.property.2]) (by linarith [x.property.1])]
    ring)
  right_inv := fun y => by
    change cotangent (Real.pi/2-Real.arctan y)=y
    rw [cot_pi_div_two_sub,Real.tan_arctan]

/-- Miền của sec theo bảng: [0,π]\{π/2}. -/
def principalSecantDomain : Set ℝ := {x | x∈Icc 0 Real.pi ∧ x≠Real.pi/2}

/-- Miền sec trong đoạn văn về arcsec: (0,π)\{π/2}. -/
def printedOpenSecDomain : Set ℝ := {x | x∈Ioo 0 Real.pi ∧ x≠Real.pi/2}


def principalCosecantDomain : Set ℝ := {x | x∈Icc (-(Real.pi/2)) (Real.pi/2) ∧ x≠0}


theorem principal_secant_cosine_ne_zero (x : principalSecantDomain) : Real.cos x≠0 := by
  intro he
  have h := Real.arccos_cos x.property.1.1 x.property.1.2
  rw [he,Real.arccos_zero] at h
  exact x.property.2 h.symm


theorem principal_cosecant_sine_ne_zero (x : principalCosecantDomain) : Real.sin x≠0 := by
  intro he
  have h := Real.arcsin_sin x.property.1.1 x.property.1.2
  rw [he,Real.arcsin_zero] at h
  exact x.property.2 h.symm

/-- sec và y↦arccos(1/y) là hai hàm ngược giữa [0,π]\{π/2} và ℝ\(−1,1). -/
noncomputable def correctedSecantInverseEquiv : principalSecantDomain ≃ outsideOpenUnitInterval where
  toFun := fun x => ⟨(Real.cos x)⁻¹,inverse_unit_value_outside (principal_secant_cosine_ne_zero x) (Real.abs_cos_le_one x)⟩
  invFun := fun y => ⟨Real.arccos (y:ℝ)⁻¹,⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩,by
    intro he
    exact (inverse_outside_value_bounds y.property).2.2 (Real.arccos_eq_pi_div_two.mp he)⟩
  left_inv := fun x => Subtype.ext (by
    change Real.arccos ((Real.cos x)⁻¹)⁻¹=x
    rw [inv_inv,Real.arccos_cos x.property.1.1 x.property.1.2])
  right_inv := fun y => Subtype.ext (by
    change (Real.cos (Real.arccos (y:ℝ)⁻¹))⁻¹=y
    rw [Real.cos_arccos (inverse_outside_value_bounds y.property).1
      (inverse_outside_value_bounds y.property).2.1,inv_inv])


noncomputable def cosecantInverseEquiv : principalCosecantDomain ≃ outsideOpenUnitInterval where
  toFun := fun x => ⟨(Real.sin x)⁻¹,inverse_unit_value_outside (principal_cosecant_sine_ne_zero x) (Real.abs_sin_le_one x)⟩
  invFun := fun y => ⟨Real.arcsin (y:ℝ)⁻¹,⟨Real.neg_pi_div_two_le_arcsin _,Real.arcsin_le_pi_div_two _⟩,by
    intro he
    exact (inverse_outside_value_bounds y.property).2.2 (Real.arcsin_eq_zero_iff.mp he)⟩
  left_inv := fun x => Subtype.ext (by
    change Real.arcsin ((Real.sin x)⁻¹)⁻¹=x
    rw [inv_inv,Real.arcsin_sin x.property.1.1 x.property.1.2])
  right_inv := fun y => Subtype.ext (by
    change (Real.sin (Real.arcsin (y:ℝ)⁻¹))⁻¹=y
    rw [Real.sin_arcsin (inverse_outside_value_bounds y.property).1
      (inverse_outside_value_bounds y.property).2.1,inv_inv])

/-- Sec trên (0,π)\{π/2} không nhận giá trị 1. -/
theorem printed_open_secant_misses_one :
    (1:ℝ)∈outsideOpenUnitInterval ∧ ¬∃ x : printedOpenSecDomain, 1/Real.cos x=1 := by
  constructor
  · rw [outside_open_unit_iff_abs]
    norm_num
  · rintro ⟨x,hx⟩
    have hc : Real.cos x=1 := by simpa only [one_div,inv_eq_one] using hx
    have h := Real.arccos_cos x.property.1.1.le x.property.1.2.le
    rw [hc,Real.arccos_one] at h
    have := x.property.1.1
    linarith


theorem equiv_subtype_value_range {A : Type*} {D : Set ℝ} (e : A≃D) :
    range (fun a => (e a : ℝ))=D := by
  ext y
  constructor
  · rintro ⟨a,rfl⟩
    exact (e a).property
  · intro hy
    obtain ⟨a,ha⟩ := e.surjective ⟨y,hy⟩
    exact ⟨a,congrArg Subtype.val ha⟩


theorem inverse_trigonometric_ranges :
    range (fun y => (sineInverseEquiv.symm y : ℝ))=Icc (-(Real.pi/2)) (Real.pi/2) ∧
    range (fun y => (cosineInverseEquiv.symm y : ℝ))=Icc 0 Real.pi ∧
    range (fun y => (tangentInverseEquiv.symm y : ℝ))=Ioo (-(Real.pi/2)) (Real.pi/2) ∧
    range (fun y => (cotangentInverseEquiv.symm y : ℝ))=Ioo 0 Real.pi ∧
    range (fun y => (correctedSecantInverseEquiv.symm y : ℝ))=principalSecantDomain ∧
    range (fun y => (cosecantInverseEquiv.symm y : ℝ))=principalCosecantDomain :=
  ⟨equiv_subtype_value_range _,equiv_subtype_value_range _,equiv_subtype_value_range _,
    equiv_subtype_value_range _,equiv_subtype_value_range _,equiv_subtype_value_range _⟩


theorem sine_inverse_value (y : Icc (-1:ℝ) 1) :
    (sineInverseEquiv.symm y : ℝ)=Real.arcsin y := by
  have h := congrArg Subtype.val (sineInverseEquiv.apply_symm_apply y)
  change Real.sin (sineInverseEquiv.symm y)=y at h
  have hi := Real.arcsin_sin (sineInverseEquiv.symm y).property.1 (sineInverseEquiv.symm y).property.2
  rw [h] at hi
  exact hi.symm


theorem cosine_inverse_value (y : Icc (-1:ℝ) 1) :
    (cosineInverseEquiv.symm y : ℝ)=Real.arccos y := rfl


theorem tangent_inverse_value (y : ℝ) :
    (tangentInverseEquiv.symm y : ℝ)=Real.arctan y := rfl


theorem cotangent_inverse_value (y : ℝ) :
    (cotangentInverseEquiv.symm y : ℝ)=arccotangent y := rfl


theorem corrected_secant_inverse_value (y : outsideOpenUnitInterval) :
    (correctedSecantInverseEquiv.symm y : ℝ)=Real.arccos (1/(y:ℝ)) := by
  simp only [one_div]
  rfl


theorem cosecant_inverse_value (y : outsideOpenUnitInterval) :
    (cosecantInverseEquiv.symm y : ℝ)=Real.arcsin (1/(y:ℝ)) := by
  simp only [one_div]
  rfl


theorem sine_principal_inverse_iff (x : Icc (-(Real.pi/2)) (Real.pi/2)) (y : Icc (-1:ℝ) 1) :
    Real.sin x=y ↔ (x:ℝ)=Real.arcsin y := by
  constructor
  · intro he
    have h := Real.arcsin_sin x.property.1 x.property.2
    rw [he] at h
    exact h.symm
  · intro he
    rw [he,Real.sin_arcsin y.property.1 y.property.2]


theorem cosine_principal_inverse_iff (x : Icc (0:ℝ) Real.pi) (y : Icc (-1:ℝ) 1) :
    Real.cos x=y ↔ (x:ℝ)=Real.arccos y := by
  constructor
  · intro he
    have h := Real.arccos_cos x.property.1 x.property.2
    rw [he] at h
    exact h.symm
  · intro he
    rw [he,Real.cos_arccos y.property.1 y.property.2]


theorem tangent_principal_inverse_iff (x : Ioo (-(Real.pi/2)) (Real.pi/2)) (y : ℝ) :
    Real.tan x=y ↔ (x:ℝ)=Real.arctan y := by
  constructor
  · intro he
    have h := Real.arctan_tan x.property.1 x.property.2
    rw [he] at h
    exact h.symm
  · intro he
    rw [he,Real.tan_arctan]


theorem cotangent_principal_inverse_iff (x : Ioo (0:ℝ) Real.pi) (y : ℝ) :
    cotangent x=y ↔ (x:ℝ)=arccotangent y := by
  constructor
  · intro he
    have h := congrArg Subtype.val (cotangentInverseEquiv.symm_apply_apply x)
    change arccotangent (cotangent x)=x at h
    rw [he] at h
    exact h.symm
  · intro he
    rw [he]
    exact cotangentInverseEquiv.apply_symm_apply y


theorem arcsine_special_values :
    Real.arcsin (1/2)=Real.pi/6 ∧ Real.arcsin (-Real.sqrt 2/2)= -Real.pi/4 := by
  constructor
  · rw [←Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  · have he : -Real.sqrt 2/2=Real.sin (-Real.pi/4) := by
      rw [show -Real.pi/4= -(Real.pi/4) by ring,Real.sin_neg,Real.sin_pi_div_four]
      ring
    rw [he]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])


theorem arccosine_special_values :
    Real.arccos (1/2)=Real.pi/3 ∧ Real.arccos (-Real.sqrt 2/2)=3*Real.pi/4 := by
  constructor
  · rw [←Real.cos_pi_div_three]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  · rw [show -Real.sqrt 2/2= -(Real.sqrt 2/2) by ring,Real.arccos_neg,←Real.cos_pi_div_four,
      Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    ring


theorem positive_forward_period_not_injective {D : Set ℝ} {f : ℝ → ℝ} {T : ℝ}
    (hD : D.Nonempty) (hT : calculus.Chapter03.Section01Properties.HasPositiveForwardPeriodOn D f T) :
    ¬Injective (fun x : D => f x) := by
  intro hi
  obtain ⟨x,hx⟩ := hD
  have he : (⟨x+T,(hT.2 x hx).1⟩ : D)=⟨x,hx⟩ := hi (hT.2 x hx).2
  have hr := congrArg Subtype.val he
  change x+T=x at hr
  linarith [hT.1]


theorem six_trigonometric_positive_forward_periods :
    calculus.Chapter03.Section01Properties.HasPositiveForwardPeriodOn univ Real.sin (2*Real.pi) ∧
    calculus.Chapter03.Section01Properties.HasPositiveForwardPeriodOn univ Real.cos (2*Real.pi) ∧
    calculus.Chapter03.Section01Properties.HasPositiveForwardPeriodOn cosineNonzeroDomain Real.tan (2*Real.pi) ∧
    calculus.Chapter03.Section01Properties.HasPositiveForwardPeriodOn sineNonzeroDomain cotangent (2*Real.pi) ∧
    calculus.Chapter03.Section01Properties.HasPositiveForwardPeriodOn cosineNonzeroDomain (fun x => 1/Real.cos x) (2*Real.pi) ∧
    calculus.Chapter03.Section01Properties.HasPositiveForwardPeriodOn sineNonzeroDomain (fun x => 1/Real.sin x) (2*Real.pi) := by
  refine ⟨calculus.Chapter03.Section01Properties.sine_cosine_positive_forward_period.1,
    calculus.Chapter03.Section01Properties.sine_cosine_positive_forward_period.2,
    ⟨by positivity,?_⟩,⟨by positivity,?_⟩,⟨by positivity,?_⟩,⟨by positivity,?_⟩⟩
  · intro x hx
    refine ⟨?_,?_⟩
    · change Real.cos (x+2*Real.pi)≠0
      rw [Real.cos_add_two_pi]
      exact hx
    · rw [Real.tan_eq_sin_div_cos,Real.sin_add_two_pi,Real.cos_add_two_pi,Real.tan_eq_sin_div_cos]
  · intro x hx
    refine ⟨?_,?_⟩
    · change Real.sin (x+2*Real.pi)≠0
      rw [Real.sin_add_two_pi]
      exact hx
    · simp only [cotangent,Real.sin_add_two_pi,Real.cos_add_two_pi]
  · intro x hx
    refine ⟨?_,?_⟩
    · change Real.cos (x+2*Real.pi)≠0
      rw [Real.cos_add_two_pi]
      exact hx
    · dsimp only
      rw [Real.cos_add_two_pi]
  · intro x hx
    refine ⟨?_,?_⟩
    · change Real.sin (x+2*Real.pi)≠0
      rw [Real.sin_add_two_pi]
      exact hx
    · dsimp only
      rw [Real.sin_add_two_pi]


theorem six_full_trigonometric_functions_not_injective :
    ¬Injective Real.sin ∧ ¬Injective Real.cos ∧
    ¬Injective (fun x : cosineNonzeroDomain => Real.tan x) ∧
    ¬Injective (fun x : sineNonzeroDomain => cotangent x) ∧
    ¬Injective secantOnDomain ∧ ¬Injective cosecantOnDomain := by
  have hc : cosineNonzeroDomain.Nonempty := ⟨0,by norm_num [cosineNonzeroDomain]⟩
  have hs : sineNonzeroDomain.Nonempty := ⟨Real.pi/2,by norm_num [sineNonzeroDomain]⟩
  have hp := six_trigonometric_positive_forward_periods
  refine ⟨?_,?_,positive_forward_period_not_injective hc hp.2.2.1,
    positive_forward_period_not_injective hs hp.2.2.2.1,
    positive_forward_period_not_injective hc hp.2.2.2.2.1,
    positive_forward_period_not_injective hs hp.2.2.2.2.2⟩
  · intro hi
    apply positive_forward_period_not_injective ⟨0,mem_univ _⟩ hp.1
    intro x y he
    exact Subtype.ext (hi he)
  · intro hi
    apply positive_forward_period_not_injective ⟨0,mem_univ _⟩ hp.2.1
    intro x y he
    exact Subtype.ext (hi he)


theorem six_full_trigonometric_functions_not_bijective :
    ¬Bijective Real.sin ∧ ¬Bijective Real.cos ∧
    ¬Bijective (fun x : cosineNonzeroDomain => Real.tan x) ∧
    ¬Bijective (fun x : sineNonzeroDomain => cotangent x) ∧
    ¬Bijective secantOnDomain ∧ ¬Bijective cosecantOnDomain := by
  have h := six_full_trigonometric_functions_not_injective
  exact ⟨fun hh => h.1 hh.1,fun hh => h.2.1 hh.1,fun hh => h.2.2.1 hh.1,
    fun hh => h.2.2.2.1 hh.1,fun hh => h.2.2.2.2.1 hh.1,fun hh => h.2.2.2.2.2 hh.1⟩


noncomputable def printedOpenSecant : printedOpenSecDomain → outsideOpenUnitInterval := fun x =>
  ⟨(Real.cos x)⁻¹,inverse_unit_value_outside
    (principal_secant_cosine_ne_zero ⟨x,⟨x.property.1.1.le,x.property.1.2.le⟩,x.property.2⟩)
    (Real.abs_cos_le_one x)⟩


theorem printed_open_secant_not_surjective : ¬Surjective printedOpenSecant := by
  intro hs
  obtain ⟨x,hx⟩ := hs ⟨1,printed_open_secant_misses_one.1⟩
  have he := congrArg Subtype.val hx
  change (Real.cos x)⁻¹=1 at he
  exact printed_open_secant_misses_one.2 ⟨x,by simpa only [one_div] using he⟩


theorem printed_open_secant_not_bijective : ¬Bijective printedOpenSecant :=
  fun h => printed_open_secant_not_surjective h.2

end calculus.Chapter03.Section01Trigonometric
