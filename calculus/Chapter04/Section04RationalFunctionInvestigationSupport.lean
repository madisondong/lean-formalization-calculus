import calculus.Chapter04.Section03
import calculus.Chapter04.Section04ConvexityAndInflection
import calculus.Chapter04.Section04AsymptoteClassificationSupport
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Khảo sát hai hàm hữu tỉ Bài 4.4.14(a,b)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2758–2762.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04RationalFunctionInvestigationSupport
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03
open calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section04ConvexityAndInflection


theorem hasDerivAt_deriv_of_open_formula {f g : ℝ → ℝ} {D : Set ℝ} {x v : ℝ}
    (hD : IsOpen D) (hx : x ∈ D) (hf : ∀ y ∈ D, HasDerivAt f (g y) y)
    (hg : HasDerivAt g v x) : HasDerivAt (deriv f) v x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [hD.mem_nhds hx] with y hy
  exact (hf y hy).deriv


theorem source_two_of_pointwise {f : ℝ → ℝ} {D : Set ℝ} {a b : ℝ}
    (hI : Ioo a b ⊆ D) (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ D, DifferentiableAt ℝ (deriv f) x) :
    DifferentiableToOrderOn 2 f (Ioo a b) := by
  apply (differentiableToOrderOn_two f isOpen_Ioo).mpr
  exact ⟨fun x hx ↦ (hf x (hI hx)).differentiableWithinAt,
    fun x hx ↦ (hg x (hI hx)).differentiableWithinAt⟩


theorem second_nonpos_of_concaveOnOpenInterval {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b)) (hc : ConcaveOnOpenInterval f a b)
    {x : ℝ} (hx : x ∈ Ioo a b) : deriv (deriv f) x ≤ 0 := by
  have hm := ((concaveOnOpenInterval_iff_concaveOn f a b).mp hc).antitoneOn_deriv
    (fun y hy ↦ (hf y hy).differentiableAt (isOpen_Ioo.mem_nhds hy))
  have h := hm.derivWithin_nonpos (x := x)
  rwa [derivWithin_of_isOpen isOpen_Ioo hx] at h


theorem second_zero_of_sourceInflection {f : ℝ → ℝ} {D : Set ℝ} {a b c : ℝ}
    (hI : Ioo a b ⊆ D) (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ D, DifferentiableAt ℝ (deriv f) x)
    (hc : ContinuousAt (deriv (deriv f)) c)
    (hu : SourceInflectionOn f a b c) : deriv (deriv f) c = 0 := by
  rcases hu with ⟨_, _, _, δ, hδ, hsub, hswitch⟩
  have hleft : Ioo (c - δ) c ⊆ D := by
    intro x hx
    exact hI (hsub ⟨hx.1, by linarith [hx.2]⟩)
  have hright : Ioo c (c + δ) ⊆ D := by
    intro x hx
    exact hI (hsub ⟨by linarith [hx.1], hx.2⟩)
  have hl2 := source_two_of_pointwise hleft hf hg
  have hr2 := source_two_of_pointwise hright hf hg
  have hlm : ∀ᶠ x in 𝓝[<] c, x ∈ Ioo (c - δ) c := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (show c - δ < c by linarith))]
      with x hx hy
    exact ⟨hy, hx⟩
  have hrm : ∀ᶠ x in 𝓝[>] c, x ∈ Ioo c (c + δ) := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (show c < c + δ by linarith))]
      with x hx hy
    exact ⟨hx, hy⟩
  have hlt := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] c ≤ 𝓝 c)
  have hrt := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] c ≤ 𝓝 c)
  rcases hswitch with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · have hp : 0 ≤ deriv (deriv f) c := ge_of_tendsto hlt
      (hlm.mono fun x hx ↦ (convexOnOpenInterval_iff_second_deriv_nonneg f _ _ hl2).mp hl x hx)
    have hn : deriv (deriv f) c ≤ 0 := le_of_tendsto hrt
      (hrm.mono fun x hx ↦ second_nonpos_of_concaveOnOpenInterval
        (fun y hy ↦ (hf y (hright hy)).differentiableWithinAt) hr hx)
    exact le_antisymm hn hp
  · have hn : deriv (deriv f) c ≤ 0 := le_of_tendsto hlt
      (hlm.mono fun x hx ↦ second_nonpos_of_concaveOnOpenInterval
        (fun y hy ↦ (hf y (hleft hy)).differentiableWithinAt) hl hx)
    have hp : 0 ≤ deriv (deriv f) c := ge_of_tendsto hrt
      (hrm.mono fun x hx ↦ (convexOnOpenInterval_iff_second_deriv_nonneg f _ _ hr2).mp hr x hx)
    exact le_antisymm hn hp


theorem no_local_minimum_of_right_decrease {f : ℝ → ℝ} {D : Set ℝ} {c b : ℝ}
    (hcb : c < b) (hI : Ioo c b ⊆ D) (hdec : ∀ x ∈ Ioo c b, f x < f c) :
    ¬ IsLocalMinimumOn f D c := by
  rintro ⟨_, δ, hδ, hbound⟩
  let t : ℝ := min (δ / 2) ((b - c) / 2)
  have hbc : 0 < b - c := sub_pos.mpr hcb
  have htpos : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htb : t < b - c := (min_le_right _ _).trans_lt (by linarith)
  have hx : c + t ∈ Ioo c b := ⟨by linarith, by linarith⟩
  exact (hdec (c + t) hx).not_ge
    (hbound (c + t) ⟨⟨by linarith, by linarith⟩, hI hx⟩)


theorem no_local_maximum_of_right_increase {f : ℝ → ℝ} {D : Set ℝ} {c b : ℝ}
    (hcb : c < b) (hI : Ioo c b ⊆ D) (hinc : ∀ x ∈ Ioo c b, f c < f x) :
    ¬ IsLocalMaximumOn f D c := by
  rintro ⟨_, δ, hδ, hbound⟩
  let t : ℝ := min (δ / 2) ((b - c) / 2)
  have hbc : 0 < b - c := sub_pos.mpr hcb
  have htpos : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htb : t < b - c := (min_le_right _ _).trans_lt (by linarith)
  have hx : c + t ∈ Ioo c b := ⟨by linarith, by linarith⟩
  exact (hinc (c + t) hx).not_ge
    (hbound (c + t) ⟨⟨by linarith, by linarith⟩, hI hx⟩)


theorem strictMonoOn_of_domain_derivative {f : ℝ → ℝ} {D S : Set ℝ}
    (hS : Convex ℝ S) (hsub : S ⊆ D) (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ S, 0 < deriv f x) : StrictMonoOn f S := by
  apply strictMonoOn_of_deriv_pos hS
  · exact fun x hx ↦ (hf x (hsub hx)).continuousAt.continuousWithinAt
  · exact fun x hx ↦ hp x (interior_subset hx)


theorem strictAntiOn_of_domain_derivative {f : ℝ → ℝ} {D S : Set ℝ}
    (hS : Convex ℝ S) (hsub : S ⊆ D) (hf : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hn : ∀ x ∈ S, deriv f x < 0) : StrictAntiOn f S := by
  apply strictAntiOn_of_deriv_neg hS
  · exact fun x hx ↦ (hf x (hsub hx)).continuousAt.continuousWithinAt
  · exact fun x hx ↦ hn x (interior_subset hx)

end calculus.Chapter04.Section04RationalFunctionInvestigationSupport
