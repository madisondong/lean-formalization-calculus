import calculus.Chapter04.Section01Derivatives
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# 4.3.1: cực trị địa phương và các định lí giá trị trung bình

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 870–1089. Cực trị trên miền `D` yêu cầu điểm xét thuộc `D`.
-/
namespace calculus.Chapter04.Section03
open Set Filter
open scoped Topology


def IsLocalMinimumOn (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) : Prop :=
  c ∈ D ∧ ∃ δ > 0, ∀ x ∈ Ioo (c - δ) (c + δ) ∩ D, f c ≤ f x


def IsLocalMaximumOn (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) : Prop :=
  c ∈ D ∧ ∃ δ > 0, ∀ x ∈ Ioo (c - δ) (c + δ) ∩ D, f x ≤ f c


def IsLocalExtremumOn (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) : Prop :=
  IsLocalMinimumOn f D c ∨ IsLocalMaximumOn f D c


theorem isLocalMinimumOn_iff (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) :
    IsLocalMinimumOn f D c ↔ c ∈ D ∧ IsLocalMinOn f D c := by
  constructor
  · rintro ⟨hc, δ, hδ, hb⟩
    refine ⟨hc, ?_⟩
    change {x | f c ≤ f x} ∈ 𝓝[D] c
    apply Metric.mem_nhdsWithin_iff.mpr
    refine ⟨δ, hδ, ?_⟩
    rintro x ⟨hx, hxD⟩
    have ha : |x - c| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
    have ha' := abs_lt.mp ha
    exact hb x ⟨⟨by linarith [ha'.1], by linarith [ha'.2]⟩, hxD⟩
  · rintro ⟨hc, hm⟩
    change {x | f c ≤ f x} ∈ 𝓝[D] c at hm
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhdsWithin_iff.mp hm
    refine ⟨hc, δ, hδ, ?_⟩
    rintro x ⟨hx, hxD⟩
    apply hb
    refine ⟨?_, hxD⟩
    change |x - c| < δ
    exact abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩


theorem isLocalMaximumOn_iff (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) :
    IsLocalMaximumOn f D c ↔ c ∈ D ∧ IsLocalMaxOn f D c := by
  constructor
  · rintro ⟨hc, δ, hδ, hb⟩
    refine ⟨hc, ?_⟩
    change {x | f x ≤ f c} ∈ 𝓝[D] c
    apply Metric.mem_nhdsWithin_iff.mpr
    refine ⟨δ, hδ, ?_⟩
    rintro x ⟨hx, hxD⟩
    have ha : |x - c| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
    have ha' := abs_lt.mp ha
    exact hb x ⟨⟨by linarith [ha'.1], by linarith [ha'.2]⟩, hxD⟩
  · rintro ⟨hc, hm⟩
    change {x | f x ≤ f c} ∈ 𝓝[D] c at hm
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhdsWithin_iff.mp hm
    refine ⟨hc, δ, hδ, ?_⟩
    rintro x ⟨hx, hxD⟩
    apply hb
    refine ⟨?_, hxD⟩
    change |x - c| < δ
    exact abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩


theorem isLocalExtremumOn_iff (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) :
    IsLocalExtremumOn f D c ↔ c ∈ D ∧ IsLocalExtrOn f D c := by
  simp only [IsLocalExtremumOn, isLocalMinimumOn_iff, isLocalMaximumOn_iff,
    IsLocalExtrOn, IsExtrFilter]
  tauto


theorem fermat {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {c : ℝ}
    (he : IsLocalExtremumOn f I c) (hf : DifferentiableAt ℝ f c) : deriv f c = 0 := by
  obtain ⟨hc, hm⟩ := (isLocalExtremumOn_iff f I c).mp he
  exact (hm.isLocalExtr (hI.mem_nhds hc)).hasDerivAt_eq_zero hf.hasDerivAt


theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (he : f a = f b) : ∃ c ∈ Ioo a b, HasDerivAt f 0 c := by
  obtain ⟨c, hcm, hcz⟩ := exists_hasDerivAt_eq_zero hab hc he
    (fun x hx ↦ ((hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt)
  refine ⟨c, hcm, ?_⟩
  simpa only [hcz] using ((hd c hcm).differentiableAt (isOpen_Ioo.mem_nhds hcm)).hasDerivAt


theorem lagrange {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hc hd


theorem lagrange_increment {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, f b - f a = deriv f c * (b - a) := by
  obtain ⟨c, hcm, he⟩ := lagrange hab hc hd
  refine ⟨c, hcm, ?_⟩
  rw [he, div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]


theorem cauchy {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hgc : ContinuousOn g (Icc a b)) (hgd : DifferentiableOn ℝ g (Ioo a b)) :
    ∃ c ∈ Ioo a b, (f b - f a) * deriv g c = (g b - g a) * deriv f c := by
  obtain ⟨c, hcm, he⟩ := exists_ratio_deriv_eq_ratio_slope f hab hfc hfd g hgc hgd
  exact ⟨c, hcm, he.symm⟩


theorem constant_of_derivative_zero {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hz : ∀ x ∈ Ioo a b, deriv f x = 0) : ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with he | hax
  · rw [← he]
  · have hs : Icc a x ⊆ Icc a b := fun y hy ↦ ⟨hy.1, hy.2.trans hx.2⟩
    have hs' : Ioo a x ⊆ Ioo a b := fun y hy ↦ ⟨hy.1, hy.2.trans_le hx.2⟩
    obtain ⟨c, hcm, he⟩ := lagrange_increment hax (hc.mono hs) (hd.mono hs')
    rw [hz c (hs' hcm), zero_mul] at he
    exact sub_eq_zero.mp he


theorem equal_derivatives_up_to_constant {f g : ℝ → ℝ} {a b : ℝ}
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hgc : ContinuousOn g (Icc a b)) (hgd : DifferentiableOn ℝ g (Ioo a b))
    (he : ∀ x ∈ Ioo a b, deriv f x = deriv g x) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, f x = g x + C := by
  have hz : ∀ x ∈ Ioo a b, deriv (fun y ↦ f y - g y) x = 0 := by
    intro x hx
    rw [deriv_fun_sub ((hfd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx))
      ((hgd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)), he x hx, sub_self]
  have hc := constant_of_derivative_zero (hfc.sub hgc) (hfd.sub hgd) hz
  refine ⟨f a - g a, ?_⟩
  intro x hx
  have h : f x - g x = f a - g a := by
    simpa only [Pi.sub_apply] using hc x hx
  linarith


theorem monotoneOn_of_nonnegative_derivative {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hp : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
  · simpa only [interior_Icc] using hd
  · simpa only [interior_Icc] using hp


theorem strictMonoOn_of_positive_derivative {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hp : ∀ x ∈ Ioo a b, 0 < deriv f x) : StrictMonoOn f (Icc a b) := by
  intro x hx y hy hxy
  have hs : Icc x y ⊆ Icc a b := fun z hz ↦ ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
  have hs' : Ioo x y ⊆ Ioo a b := fun z hz ↦ ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
  obtain ⟨c, hcm, he⟩ := lagrange_increment hxy (hc.mono hs) (hd.mono hs')
  have hpos : 0 < deriv f c * (y - x) := mul_pos (hp c (hs' hcm)) (sub_pos.mpr hxy)
  linarith


theorem antitoneOn_of_nonpositive_derivative {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hp : ∀ x ∈ Ioo a b, deriv f x ≤ 0) : AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hc
  · simpa only [interior_Icc] using hd
  · simpa only [interior_Icc] using hp


theorem strictAntiOn_of_negative_derivative {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hp : ∀ x ∈ Ioo a b, deriv f x < 0) : StrictAntiOn f (Icc a b) := by
  intro x hx y hy hxy
  have hs : Icc x y ⊆ Icc a b := fun z hz ↦ ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
  have hs' : Ioo x y ⊆ Ioo a b := fun z hz ↦ ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
  obtain ⟨c, hcm, he⟩ := lagrange_increment hxy (hc.mono hs) (hd.mono hs')
  have hneg : deriv f c * (y - x) < 0 := mul_neg_of_neg_of_pos (hp c (hs' hcm)) (sub_pos.mpr hxy)
  linarith


theorem sine_abs_le (x : ℝ) : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs (x := x)

end calculus.Chapter04.Section03
