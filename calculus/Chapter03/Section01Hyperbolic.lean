import calculus.Chapter03.Section01Properties
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# §3.1 — hàm hyperbol và hàm ngược

Nguồn: `Ch3_gioihanhamso.tex` dòng 984–1189.
-/

namespace calculus.Chapter03.Section01Hyperbolic

open Set
open calculus.Chapter03.Section01Properties


def nonzeroDomain : Set ℝ := {x | x≠0}


def outsideClosedUnitInterval : Set ℝ := (Icc (-1) 1)ᶜ


noncomputable def hyperbolicCotangent (x : ℝ) : ℝ := Real.cosh x/Real.sinh x


noncomputable def hyperbolicSecant (x : ℝ) : ℝ := 1/Real.cosh x


noncomputable def hyperbolicCosecantOnDomain : nonzeroDomain → ℝ := fun x => 1/Real.sinh x


theorem hyperbolic_function_definitions (x : ℝ) :
    Real.sinh x=(Real.exp x-Real.exp (-x))/2 ∧
    Real.cosh x=(Real.exp x+Real.exp (-x))/2 ∧
    Real.tanh x=Real.sinh x/Real.cosh x ∧
    hyperbolicCotangent x=Real.cosh x/Real.sinh x ∧ hyperbolicSecant x=1/Real.cosh x :=
  ⟨Real.sinh_eq x,Real.cosh_eq x,Real.tanh_eq_sinh_div_cosh x,rfl,rfl⟩


theorem outside_closed_unit_iff_abs (y : ℝ) :
    y∈outsideClosedUnitInterval ↔ 1 < |y| := by
  change ¬(-1≤y ∧ y≤1) ↔ _
  rw [←abs_le]
  exact not_le


theorem outside_closed_ne_zero {y : ℝ} (hy : y∈outsideClosedUnitInterval) : y≠0 := by
  intro he
  subst y
  have := (outside_closed_unit_iff_abs 0).mp hy
  norm_num at this


theorem inverse_outside_closed_bounds {y : ℝ} (hy : y∈outsideClosedUnitInterval) :
    y⁻¹∈Ioo (-1) 1 ∧ y⁻¹≠0 := by
  have hn := outside_closed_ne_zero hy
  have hb : |y⁻¹|<1 := by
    rw [abs_inv]
    exact (inv_lt_one₀ (abs_pos.mpr hn)).mpr ((outside_closed_unit_iff_abs y).mp hy)
  exact ⟨abs_lt.mp hb,inv_ne_zero hn⟩


theorem tanh_ne_zero {x : ℝ} (hx : x≠0) : Real.tanh x≠0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_ne_zero (Real.sinh_ne_zero.mpr hx) (Real.cosh_pos x).ne'


theorem coth_eq_reciprocal_tanh (x : ℝ) : hyperbolicCotangent x=(Real.tanh x)⁻¹ := by
  rw [hyperbolicCotangent,Real.tanh_eq_sinh_div_cosh,inv_div]


noncomputable def sinhInverseEquiv : ℝ ≃ ℝ := Real.sinhEquiv


noncomputable def coshInverseEquiv : Ici (0:ℝ) ≃ Ici (1:ℝ) where
  toFun x := ⟨Real.cosh x,Real.one_le_cosh x⟩
  invFun y := ⟨Real.arcosh y,Real.arcosh_nonneg y.property⟩
  left_inv x := Subtype.ext (Real.arcosh_cosh x.property)
  right_inv y := Subtype.ext (Real.cosh_arcosh y.property)


noncomputable def tanhInverseEquiv : ℝ ≃ Ioo (-1:ℝ) 1 where
  toFun x := ⟨Real.tanh x,Real.neg_one_lt_tanh x,Real.tanh_lt_one x⟩
  invFun y := Real.artanh y
  left_inv := Real.artanh_tanh
  right_inv y := Subtype.ext (Real.tanh_artanh y.property)


theorem coth_value_outside {x : ℝ} (hx : x≠0) : hyperbolicCotangent x∈outsideClosedUnitInterval := by
  rw [coth_eq_reciprocal_tanh,outside_closed_unit_iff_abs,abs_inv]
  exact (one_lt_inv₀ (abs_pos.mpr (tanh_ne_zero hx))).mpr (Real.abs_tanh_lt_one x)


noncomputable def inverseHyperbolicCotangent (y : ℝ) : ℝ := Real.artanh y⁻¹


theorem arcoth_ne_zero {y : ℝ} (hy : y∈outsideClosedUnitInterval) : inverseHyperbolicCotangent y≠0 := by
  obtain ⟨hb,hn⟩ := inverse_outside_closed_bounds hy
  intro he
  have ht := Real.tanh_artanh hb
  rw [←inverseHyperbolicCotangent,he,Real.tanh_zero] at ht
  exact hn ht.symm


noncomputable def cothInverseEquiv : nonzeroDomain ≃ outsideClosedUnitInterval where
  toFun x := ⟨hyperbolicCotangent x,coth_value_outside x.property⟩
  invFun y := ⟨inverseHyperbolicCotangent y,arcoth_ne_zero y.property⟩
  left_inv x := by
    apply Subtype.ext
    change Real.artanh (hyperbolicCotangent x)⁻¹=x
    rw [coth_eq_reciprocal_tanh,inv_inv,Real.artanh_tanh]
  right_inv y := by
    apply Subtype.ext
    change hyperbolicCotangent (Real.artanh y.val⁻¹)=y
    rw [coth_eq_reciprocal_tanh,Real.tanh_artanh (inverse_outside_closed_bounds y.property).1,inv_inv]


theorem sech_value_bounds (x : ℝ) : hyperbolicSecant x∈Ioc (0:ℝ) 1 := by
  exact ⟨one_div_pos.mpr (Real.cosh_pos x),by simpa only [hyperbolicSecant,one_div] using inv_le_one_of_one_le₀ (Real.one_le_cosh x)⟩


theorem inverse_sech_target_bounds {y : ℝ} (hy : y∈Ioc (0:ℝ) 1) : 1≤y⁻¹ :=
  (one_le_inv₀ hy.1).mpr hy.2


noncomputable def sechInverseEquiv : Ici (0:ℝ) ≃ Ioc (0:ℝ) 1 where
  toFun x := ⟨hyperbolicSecant x,sech_value_bounds x⟩
  invFun y := ⟨Real.arcosh y.val⁻¹,Real.arcosh_nonneg (inverse_sech_target_bounds y.property)⟩
  left_inv x := by
    apply Subtype.ext
    change Real.arcosh (1/Real.cosh x)⁻¹=x
    rw [one_div,inv_inv,Real.arcosh_cosh x.property]
  right_inv y := by
    apply Subtype.ext
    change 1/Real.cosh (Real.arcosh y.val⁻¹)=y
    rw [Real.cosh_arcosh (inverse_sech_target_bounds y.property),one_div,inv_inv]


theorem csch_value_ne_zero (x : nonzeroDomain) : hyperbolicCosecantOnDomain x≠0 :=
  one_div_ne_zero (Real.sinh_ne_zero.mpr x.property)


theorem inverse_csch_ne_zero {y : ℝ} (hy : y≠0) : Real.arsinh y⁻¹≠0 := by
  intro he
  have hs := Real.sinh_arsinh y⁻¹
  rw [he,Real.sinh_zero] at hs
  exact inv_ne_zero hy hs.symm


noncomputable def cschInverseEquiv : nonzeroDomain ≃ nonzeroDomain where
  toFun x := ⟨hyperbolicCosecantOnDomain x,csch_value_ne_zero x⟩
  invFun y := ⟨Real.arsinh y.val⁻¹,inverse_csch_ne_zero y.property⟩
  left_inv x := by
    apply Subtype.ext
    change Real.arsinh (1/Real.sinh x)⁻¹=x
    rw [one_div,inv_inv,Real.arsinh_sinh]
  right_inv y := by
    apply Subtype.ext
    change 1/Real.sinh (Real.arsinh y.val⁻¹)=y
    rw [Real.sinh_arsinh,one_div,inv_inv]


theorem equiv_subtype_range {D : Type*} {S : Set ℝ} (e : D ≃ S) :
    range (fun x => (e x).val)=S := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact (e x).property
  · intro hy
    exact ⟨e.symm ⟨y,hy⟩,congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)⟩


theorem six_hyperbolic_ranges :
    range Real.sinh=univ ∧ range Real.cosh=Ici 1 ∧ range Real.tanh=Ioo (-1) 1 ∧
    range (fun x : nonzeroDomain => hyperbolicCotangent x)=outsideClosedUnitInterval ∧
    range hyperbolicSecant=Ioc 0 1 ∧ range hyperbolicCosecantOnDomain=nonzeroDomain := by
  refine ⟨?_,?_,equiv_subtype_range tanhInverseEquiv,equiv_subtype_range cothInverseEquiv,?_,equiv_subtype_range cschInverseEquiv⟩
  · exact range_eq_univ.mpr Real.sinh_surjective
  · ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact Real.one_le_cosh x
    · intro hy
      exact ⟨Real.arcosh y,Real.cosh_arcosh hy⟩
  · ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact sech_value_bounds x
    · intro hy
      exact ⟨(sechInverseEquiv.symm ⟨y,hy⟩).val,congrArg Subtype.val (sechInverseEquiv.apply_symm_apply ⟨y,hy⟩)⟩


theorem unit_hyperbola_point (t : ℝ) :
    0<Real.cosh t ∧ Real.cosh t^2-Real.sinh t^2=1 :=
  ⟨Real.cosh_pos t,Real.cosh_sq_sub_sinh_sq t⟩


/-- Mục `C03-S01-proposition-002`: các đẳng thức hyperbol, với x≠0 cho coth và csch. -/
theorem hyperbolic_identities (x y : ℝ) :
    Real.cosh x^2-Real.sinh x^2=1 ∧
    Real.tanh x^2+hyperbolicSecant x^2=1 ∧
    (x≠0 → hyperbolicCotangent x^2-(1/Real.sinh x)^2=1) ∧
    Real.sinh (x+y)=Real.sinh x*Real.cosh y+Real.cosh x*Real.sinh y ∧
    Real.sinh (x-y)=Real.sinh x*Real.cosh y-Real.cosh x*Real.sinh y ∧
    Real.cosh (x+y)=Real.cosh x*Real.cosh y+Real.sinh x*Real.sinh y ∧
    Real.cosh (x-y)=Real.cosh x*Real.cosh y-Real.sinh x*Real.sinh y ∧
    Real.sinh x^2=(-1+Real.cosh (2*x))/2 ∧
    Real.cosh x^2=(1+Real.cosh (2*x))/2 ∧
    Real.sinh (2*x)=2*Real.sinh x*Real.cosh x ∧
    Real.cosh (2*x)=Real.cosh x^2+Real.sinh x^2 := by
  have hc := (Real.cosh_pos x).ne'
  have hs := Real.cosh_sq_sub_sinh_sq x
  refine ⟨hs,?_,?_,Real.sinh_add x y,Real.sinh_sub x y,Real.cosh_add x y,Real.cosh_sub x y,?_,?_,Real.sinh_two_mul x,Real.cosh_two_mul x⟩
  · rw [Real.tanh_eq_sinh_div_cosh,hyperbolicSecant]
    field_simp
    nlinarith
  · intro hn
    rw [hyperbolicCotangent]
    field_simp [Real.sinh_ne_zero.mpr hn]
    nlinarith
  · nlinarith [Real.cosh_two_mul x]
  · nlinarith [Real.cosh_two_mul x]


theorem injective_not_positive_forward_periodic {D : Set ℝ} {f : ℝ → ℝ}
    (hD : D.Nonempty) (hf : Function.Injective (fun x : D => f x)) :
    ¬HasPositiveForwardPeriod D f := by
  rintro ⟨T,hT⟩
  obtain ⟨x,hx⟩ := hD
  obtain ⟨hpos,hperiod⟩ := hT
  obtain ⟨hclosure,hvalue⟩ := hperiod x hx
  have he := congrArg Subtype.val (hf (a₁ := ⟨x+T,hclosure⟩) (a₂ := ⟨x,hx⟩) hvalue)
  change x+T=x at he
  linarith


theorem full_cosh_sech_not_injective :
    ¬Function.Injective Real.cosh ∧ ¬Function.Injective hyperbolicSecant := by
  constructor
  · intro hi
    have he := hi (Real.cosh_neg 1)
    norm_num at he
  · intro hi
    have he := hi (show hyperbolicSecant (-1)=hyperbolicSecant 1 by simp [hyperbolicSecant])
    norm_num at he


theorem six_hyperbolic_bijections :
    Function.Bijective sinhInverseEquiv ∧ Function.Bijective tanhInverseEquiv ∧
    Function.Bijective cothInverseEquiv ∧ Function.Bijective cschInverseEquiv ∧
    Function.Bijective coshInverseEquiv ∧ Function.Bijective sechInverseEquiv :=
  ⟨sinhInverseEquiv.bijective,tanhInverseEquiv.bijective,cothInverseEquiv.bijective,
   cschInverseEquiv.bijective,coshInverseEquiv.bijective,sechInverseEquiv.bijective⟩


theorem cosh_not_periodic : ¬HasPositiveForwardPeriod univ Real.cosh := by
  rintro ⟨T,hT⟩
  have he := (hT.2 0 (mem_univ 0)).2
  simp only [zero_add,Real.cosh_zero] at he
  have hl : 1<Real.cosh T := Real.one_lt_cosh.mpr (ne_of_gt hT.1)
  linarith


theorem sech_not_periodic : ¬HasPositiveForwardPeriod univ hyperbolicSecant := by
  rintro ⟨T,hT⟩
  have he := (hT.2 0 (mem_univ 0)).2
  simp only [zero_add,hyperbolicSecant,Real.cosh_zero,div_one,one_div] at he
  have hc : Real.cosh T=1 := by
    simpa using congrArg Inv.inv he
  have hl : 1<Real.cosh T := Real.one_lt_cosh.mpr (ne_of_gt hT.1)
  linarith


theorem six_hyperbolic_not_periodic :
    ¬HasPositiveForwardPeriod univ Real.sinh ∧ ¬HasPositiveForwardPeriod univ Real.cosh ∧
    ¬HasPositiveForwardPeriod univ Real.tanh ∧ ¬HasPositiveForwardPeriod nonzeroDomain hyperbolicCotangent ∧
    ¬HasPositiveForwardPeriod univ hyperbolicSecant ∧
    ¬HasPositiveForwardPeriod nonzeroDomain (fun x => 1/Real.sinh x) := by
  have hU : (univ : Set ℝ).Nonempty := ⟨0,mem_univ 0⟩
  have hN : nonzeroDomain.Nonempty := ⟨1,by norm_num [nonzeroDomain]⟩
  refine ⟨injective_not_positive_forward_periodic hU ?_,cosh_not_periodic,
    injective_not_positive_forward_periodic hU ?_,injective_not_positive_forward_periodic hN ?_,
    sech_not_periodic,injective_not_positive_forward_periodic hN ?_⟩
  · intro x y he
    exact Subtype.ext (Real.sinh_injective he)
  · intro x y he
    exact Subtype.ext (Real.tanh_injective he)
  · intro x y he
    apply cothInverseEquiv.injective
    exact Subtype.ext he
  · intro x y he
    apply cschInverseEquiv.injective
    exact Subtype.ext he


theorem arsinh_logarithm_formula (x : ℝ) :
    sinhInverseEquiv.symm x=Real.log (x+Real.sqrt (x^2+1)) := by
  change Real.arsinh x=_
  rw [Real.arsinh,add_comm (1:ℝ) (x^2)]


theorem arcosh_logarithm_formula (x : Ici (1:ℝ)) :
    (coshInverseEquiv.symm x).val=Real.log (x.val+Real.sqrt (x.val^2-1)) := rfl


theorem artanh_logarithm_formula (x : Ioo (-1:ℝ) 1) :
    tanhInverseEquiv.symm x=1/2*Real.log ((1+x.val)/(1-x.val)) :=
  Real.artanh_eq_half_log ⟨x.property.1.le,x.property.2.le⟩


theorem arcoth_logarithm_formula (x : outsideClosedUnitInterval) :
    (cothInverseEquiv.symm x).val=1/2*Real.log ((x.val+1)/(x.val-1)) := by
  obtain ⟨hb,_⟩ := inverse_outside_closed_bounds x.property
  change Real.artanh x.val⁻¹=_
  rw [Real.artanh_eq_half_log ⟨hb.1.le,hb.2.le⟩]
  congr 2
  have hn := outside_closed_ne_zero x.property
  have h1 : x.val≠1 := by
    intro he
    have ha := (outside_closed_unit_iff_abs x.val).mp x.property
    rw [he] at ha
    norm_num at ha
  field_simp


theorem arsech_logarithm_formula (x : Ioc (0:ℝ) 1) :
    (sechInverseEquiv.symm x).val=Real.log ((1+Real.sqrt (1-x.val^2))/x.val) := by
  change Real.arcosh x.val⁻¹=_
  rw [Real.arcosh]
  have hn := ne_of_gt x.property.1
  have he : x.val⁻¹^2-1=(1-x.val^2)/x.val^2 := by field_simp
  rw [he,Real.sqrt_div (by nlinarith [x.property.1,x.property.2]) (x.val^2),Real.sqrt_sq_eq_abs,abs_of_pos x.property.1]
  congr 1
  field_simp

/-- Công thức logarit của arcsch trên ℝ\{0}, với |x| ở mẫu. -/
theorem arcsch_logarithm_formula (x : nonzeroDomain) :
    (cschInverseEquiv.symm x).val=Real.log (1/x.val+Real.sqrt (1+x.val^2)/|x.val|) := by
  change Real.arsinh x.val⁻¹=_
  rw [Real.arsinh]
  have hn : x.val≠0 := x.property
  have he : 1+x.val⁻¹^2=(1+x.val^2)/x.val^2 := by field_simp; ring
  rw [he,Real.sqrt_div (by positivity) (x.val^2),Real.sqrt_sq_eq_abs,one_div]

/-- Ví dụ: log(x+√(x²+1)) và sinh là hai hàm ngược trên ℝ. -/
theorem sinh_logarithm_inverse_identities (x : ℝ) :
    Real.log (Real.sinh x+Real.sqrt ((Real.sinh x)^2+1))=x ∧
    Real.sinh (Real.log (x+Real.sqrt (x^2+1)))=x := by
  have h := And.intro (Real.arsinh_sinh x) (Real.sinh_arsinh x)
  simpa only [Real.arsinh,add_comm (1:ℝ)] using h


/-- Tham số hóa đường tròn đơn vị bằng (cos t,sin t). -/
theorem unit_circle_parametrization :
    range (fun t : ℝ => (Real.cos t,Real.sin t))={p : ℝ×ℝ | p.1^2+p.2^2=1} := by
  ext p
  constructor
  · rintro ⟨t,rfl⟩
    exact Real.cos_sq_add_sin_sq t
  · intro hp
    change p.1^2+p.2^2=1 at hp
    have hlo : -1≤p.2 := by nlinarith [sq_nonneg p.1,sq_nonneg (p.2+1)]
    have hhi : p.2≤1 := by nlinarith [sq_nonneg p.1,sq_nonneg (p.2-1)]
    have he : 1-p.2^2=p.1^2 := by linarith
    by_cases hx : 0≤p.1
    · refine ⟨Real.arcsin p.2,Prod.ext ?_ (Real.sin_arcsin hlo hhi)⟩
      change Real.cos (Real.arcsin p.2)=p.1
      rw [Real.cos_arcsin,he,Real.sqrt_sq_eq_abs,abs_of_nonneg hx]
    · refine ⟨Real.pi-Real.arcsin p.2,Prod.ext ?_ ?_⟩
      · change Real.cos (Real.pi-Real.arcsin p.2)=p.1
        rw [Real.cos_pi_sub,Real.cos_arcsin,he,Real.sqrt_sq_eq_abs,abs_of_neg (lt_of_not_ge hx)]
        ring
      · change Real.sin (Real.pi-Real.arcsin p.2)=p.2
        rw [Real.sin_pi_sub,Real.sin_arcsin hlo hhi]

/-- Tham số hóa nửa phải hyperbol đơn vị bằng (cosh t,sinh t). -/
theorem unit_hyperbola_parametrization :
    range (fun t : ℝ => (Real.cosh t,Real.sinh t))=
      {p : ℝ×ℝ | 0<p.1 ∧ p.1^2-p.2^2=1} := by
  ext p
  constructor
  · rintro ⟨t,rfl⟩
    exact unit_hyperbola_point t
  · intro hp
    obtain ⟨hpos,hsq⟩ := hp
    refine ⟨Real.arsinh p.2,Prod.ext ?_ (Real.sinh_arsinh p.2)⟩
    change Real.cosh (Real.arsinh p.2)=p.1
    rw [Real.cosh_arsinh]
    have he : 1+p.2^2=p.1^2 := by linarith
    rw [he,Real.sqrt_sq_eq_abs,abs_of_pos hpos]


theorem inverse_graph_reflection {D S : Set ℝ} (e : D ≃ S) (x : D) (y : S) :
    e x=y ↔ e.symm y=x := by
  constructor
  · intro he
    rw [←he,e.symm_apply_apply]
  · intro he
    rw [←he,e.apply_symm_apply]


theorem hyperbolic_cosecant_on_domain_value (x : nonzeroDomain) : hyperbolicCosecantOnDomain x=1/Real.sinh x := rfl


theorem nonzero_domain_eq_negative_union_positive : nonzeroDomain=Iio (0:ℝ) ∪ Ioi 0 := by
  ext x
  change x≠0 ↔ x<0 ∨ 0<x
  exact ne_iff_lt_or_gt

end calculus.Chapter03.Section01Hyperbolic
