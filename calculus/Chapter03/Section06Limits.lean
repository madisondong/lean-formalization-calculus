import calculus.Chapter03.Section04
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# §3.6 — bốn ví dụ giới hạn mũ và logarit

Nguồn: dòng 3009–3077; mục `C03-S06-remark-001` nêu điều kiện giới hạn lũy thừa.
-/
namespace calculus.Chapter03.Section06Limits

open Set Filter Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section02Infinite


theorem positive_halfline_punctured_accumulation {a c : ℝ} (ha : c<a) :
    AccumulationPointOf (Ioi c \ {a}) a := by
  intro δ hδ
  refine ⟨a+δ/2,⟨show c<a+δ/2 by linarith,by simpa using (show a+δ/2≠a by linarith)⟩,
    by linarith,by linarith,by linarith⟩


theorem logarithmic_increment_filter :
    Tendsto (fun x : ℝ => Real.log (1+x)/x) (𝓝[≠] 0) (𝓝 1) := by
  simpa [Real.log_one,smul_eq_mul,div_eq_mul_inv,mul_comm] using
    (Real.hasDerivAt_log (by norm_num : (1:ℝ)≠0)).tendsto_slope_zero

/-- Mục `C03-S06-example-001`: giới hạn hai phía tại 0, với 1+x>0 và x≠0. -/
theorem example01_one_add_reciprocal_power :
    DomainLimit (Ioi (-1:ℝ) \ {0}) (fun x : ℝ => (1+x)^(1/x)) 0 (Real.exp 1) := by
  apply (domainLimit_iff_tendsto
    (positive_halfline_punctured_accumulation (by norm_num : (-1:ℝ)<0))).mpr
  have hl := logarithmic_increment_filter.mono_left
    (nhdsWithin_mono 0 (show (Ioi (-1:ℝ) \ {0}) \ {0} ⊆ {0}ᶜ from
      fun x hx => hx.2))
  apply ((Real.continuous_exp.tendsto 1).comp hl).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (-1:ℝ)<x := hx.1.1
  have hp : 0<1+x := by linarith
  change Real.exp (Real.log (1+x)/x)=(1+x)^(1/x)
  rw [Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- Mục `C03-S06-example-002`: giới hạn thương logarit, với a>0, a≠1. -/
theorem example02_logarithmic_increment {a : ℝ} (_ha : 0<a) (_ha1 : a≠1) :
    DomainLimit (Ioi (-1:ℝ) \ {0})
      (fun x : ℝ => Real.logb a (1+x)/x) 0 (1/Real.log a) := by
  apply (domainLimit_iff_tendsto
    (positive_halfline_punctured_accumulation (by norm_num : (-1:ℝ)<0))).mpr
  have hl := logarithmic_increment_filter.mono_left
    (nhdsWithin_mono 0 (show (Ioi (-1:ℝ) \ {0}) \ {0} ⊆ {0}ᶜ from
      fun x hx => hx.2))
  apply (hl.div_const (Real.log a)).congr
  intro x
  simp only [Real.logb]
  ring


theorem log_base_e_value (a : ℝ) : Real.logb a (Real.exp 1)=1/Real.log a := by
  simp [Real.logb]

/-- Mục `C03-S06-example-002`: giới hạn thương mũ trên ℝ\{0}. -/
theorem example02_exponential_increment {a : ℝ} (ha : 0<a) (_ha1 : a≠1) :
    DomainLimit (univ \ {0}) (fun x : ℝ => (a^x-1)/x) 0 (Real.log a) := by
  apply (domainLimit_iff_tendsto (univ_diff_accumulation 0)).mpr
  have hd := ((hasDerivAt_id (0:ℝ)).const_rpow ha).tendsto_slope_zero
  have ht : Tendsto (fun x : ℝ => (a^x-1)/x) (𝓝[≠] 0) (𝓝 (Real.log a)) := by
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm] using hd
  exact ht.mono_left (nhdsWithin_mono 0 (fun x hx => hx.2))

/-- Mục `C03-S06-example-003`: giới hạn bằng e⁻² khi x→1 từ hai phía, trên miền x>0 và x≠1. -/
theorem example03_power_at_one :
    DomainLimit (Ioi (0:ℝ) \ {1}) (fun x : ℝ => x^(2/(1-x))) 1 (Real.exp (-2)) := by
  apply (domainLimit_iff_tendsto
    (positive_halfline_punctured_accumulation (by norm_num : (0:ℝ)<1))).mpr
  have hl : Tendsto (fun x : ℝ => Real.log x/(x-1)) (𝓝[≠] 1) (𝓝 1) := by
    have hs := (Real.hasDerivAt_log (by norm_num : (1:ℝ)≠0)).tendsto_slope
    have he : slope Real.log 1=(fun x : ℝ => Real.log x/(x-1)) := by
      funext x
      rw [slope_def_field,Real.log_one,sub_zero]
    rw [he] at hs
    simpa only [inv_one] using hs
  have hrestricted := hl.mono_left
    (nhdsWithin_mono 1 (show (Ioi (0:ℝ) \ {1}) \ {1} ⊆ {1}ᶜ from fun x hx => hx.2))
  have hprod : Tendsto (fun x : ℝ => (-2)* (Real.log x/(x-1)))
      (𝓝[(Ioi (0:ℝ) \ {1}) \ {1}] 1) (𝓝 (-2)) := by
    simpa only [mul_one] using hrestricted.const_mul (-2:ℝ)
  have hexp := (Real.continuous_exp.tendsto (-2)).comp hprod
  apply hexp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change Real.exp ((-2)*(Real.log x/(x-1)))=x^(2/(1-x))
  rw [Real.rpow_def_of_pos hx.1.1]
  congr 1
  have hneg : 1-x= -(x-1) := by ring
  rw [hneg,div_neg]
  ring


def positiveRatioDomain : Set ℝ := Iio (-3:ℝ) ∪ Ioi 1


theorem positive_ratio_domain_unbounded : ¬BddAbove positiveRatioDomain := by
  rintro ⟨M,hM⟩
  have hM1 : M+1≤max 2 (M+1) := le_max_right _ _
  have htwo : (2:ℝ)≤max 2 (M+1) := le_max_left _ _
  have hx : max 2 (M+1)∈positiveRatioDomain :=
    Or.inr (show 1<max 2 (M+1) by linarith)
  have hh := hM hx
  linarith

/-- Mục `C03-S06-example-004`: ((x−1)/(x+3))^(x−2)→e⁻⁴ tại +∞. -/
theorem example04_ratio_power_at_infinity :
    DomainAtTopLimit positiveRatioDomain
      (fun x : ℝ => ((x-1)/(x+3))^(x-2)) (Real.exp (-4)) := by
  apply (domainAtTopLimit_iff_tendsto positive_ratio_domain_unbounded).mpr
  have hshift : Tendsto (fun x : ℝ => x+3) atTop atTop :=
    tendsto_atTop_add_const_right _ 3 tendsto_id
  have hinv : Tendsto (fun x : ℝ => (x+3)⁻¹) atTop (𝓝 0) := hshift.inv_tendsto_atTop
  have hbase : Tendsto (fun x : ℝ => 1+(-4)/(x+3)) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (hinv.const_mul (-4:ℝ))
  have hlog : Tendsto (fun x : ℝ => Real.log (1+(-4)/(x+3))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hbase
  have hmain : Tendsto (fun x : ℝ => (x+3)*Real.log (1+(-4)/(x+3)))
      atTop (𝓝 (-4)) :=
    (Real.tendsto_mul_log_one_add_div_atTop (-4)).comp hshift
  have hprod : Tendsto (fun x : ℝ => (x-2)*Real.log (1+(-4)/(x+3)))
      atTop (𝓝 (-4)) := by
    have ht : Tendsto (fun x : ℝ =>
        (x+3)*Real.log (1+(-4)/(x+3))-5*Real.log (1+(-4)/(x+3)))
        atTop (𝓝 (-4)) := by
      simpa only [mul_zero,sub_zero] using hmain.sub (hlog.const_mul (5:ℝ))
    apply ht.congr
    intro x
    ring
  have he := (Real.continuous_exp.tendsto (-4)).comp hprod
  apply (he.mono_left inf_le_left).congr'
  have hev : ∀ᶠ x : ℝ in atTop ⊓ 𝓟 positiveRatioDomain, 1<x :=
    (eventually_gt_atTop (1:ℝ)).filter_mono inf_le_left
  filter_upwards [hev] with x hx
  have hd : x+3≠0 := by linarith
  have hp : 0<(x-1)/(x+3) := div_pos (by linarith) (by linarith)
  change Real.exp ((x-2)*Real.log (1+(-4)/(x+3)))=((x-1)/(x+3))^(x-2)
  rw [Real.rpow_def_of_pos hp]
  congr 1
  have hratio : 1+(-4)/(x+3)=(x-1)/(x+3) := by field_simp; ring
  rw [hratio]
  ring

end calculus.Chapter03.Section06Limits
