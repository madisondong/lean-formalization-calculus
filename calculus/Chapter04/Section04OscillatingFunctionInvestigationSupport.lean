import calculus.Chapter04.Section03
import calculus.Chapter04.Section04ConvexityAndInflection
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Khảo sát hai hàm dao động của Bài 4.4.12

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2734–2746.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04OscillatingFunctionInvestigationSupport
open Set Filter SignType calculus.Chapter04.Section03
open calculus.Chapter04.Section01Higher calculus.Chapter04.Section04ConvexityAndInflection
open scoped Topology


theorem source_minimum_univ_iff (f : ℝ → ℝ) (x : ℝ) :
    IsLocalMinimumOn f univ x ↔ IsLocalMin f x := by
  rw [isLocalMinimumOn_iff]
  simp only [mem_univ, true_and, IsLocalMinOn, nhdsWithin_univ, IsLocalMin]


theorem source_maximum_univ_iff (f : ℝ → ℝ) (x : ℝ) :
    IsLocalMaximumOn f univ x ↔ IsLocalMax f x := by
  rw [isLocalMaximumOn_iff]
  simp only [mem_univ, true_and, IsLocalMaxOn, nhdsWithin_univ, IsLocalMax]


theorem second_derivative_zero_of_both_extrema {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMinimumOn f univ x) (hmax : IsLocalMaximumOn f univ x) :
    deriv (deriv f) x = 0 := by
  have hm := (source_minimum_univ_iff f x).mp hmin
  have hM := (source_maximum_univ_iff f x).mp hmax
  have he : f =ᶠ[𝓝 x] (fun _ ↦ f x) := by
    filter_upwards [hm, hM] with y hy hy'
    exact le_antisymm hy' hy
  simpa only [deriv_const'] using he.deriv.deriv_eq


theorem nondegenerate_extrema_iff {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hne : deriv f x = 0 → deriv (deriv f) x ≠ 0) :
    (IsLocalMinimumOn f univ x ↔ deriv f x = 0 ∧ 0 < deriv (deriv f) x) ∧
      (IsLocalMaximumOn f univ x ↔ deriv f x = 0 ∧ deriv (deriv f) x < 0) := by
  constructor
  · constructor
    · intro hm
      have hd := fermat isOpen_univ (Or.inl hm) hf
      refine ⟨hd, ?_⟩
      by_contra hp
      have hn : deriv (deriv f) x < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hne hd)
      have hM := (source_maximum_univ_iff f x).mpr
        (isLocalMax_of_deriv_deriv_neg hn hd hf.continuousAt)
      exact hne hd (second_derivative_zero_of_both_extrema hm hM)
    · rintro ⟨hd, hp⟩
      exact (source_minimum_univ_iff f x).mpr
        (isLocalMin_of_deriv_deriv_pos hp hd hf.continuousAt)
  · constructor
    · intro hM
      have hd := fermat isOpen_univ (Or.inr hM) hf
      refine ⟨hd, ?_⟩
      by_contra hn
      have hp : 0 < deriv (deriv f) x := lt_of_le_of_ne (le_of_not_gt hn) (hne hd).symm
      have hm := (source_minimum_univ_iff f x).mpr
        (isLocalMin_of_deriv_deriv_pos hp hd hf.continuousAt)
      exact hne hd (second_derivative_zero_of_both_extrema hm hM)
    · rintro ⟨hd, hn⟩
      exact (source_maximum_univ_iff f x).mpr
        (isLocalMax_of_deriv_deriv_neg hn hd hf.continuousAt)


theorem second_hasDerivAt_off_zero {f d g : ℝ → ℝ}
    (hf : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (d x) x)
    (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt d (g x) x)
    {x : ℝ} (hx : x ≠ 0) : HasDerivAt (deriv f) (g x) x := by
  apply (hd x hx).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact (hf y hy).deriv


theorem twice_differentiable_interval_off_zero {f d g : ℝ → ℝ}
    (hf : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (d x) x)
    (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt d (g x) x)
    {a b : ℝ} (h0 : 0 ∉ Ioo a b) : DifferentiableToOrderOn 2 f (Ioo a b) := by
  apply (differentiableToOrderOn_two f isOpen_Ioo).mpr
  constructor
  · intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; exact h0 hx
    exact (hf x hx0).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; exact h0 hx
    exact (second_hasDerivAt_off_zero hf hd hx0).differentiableAt.differentiableWithinAt


theorem source_convex_second_nonnegative {f : ℝ → ℝ} {a b : ℝ}
    (hc : ConvexOnOpenInterval f a b) (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    {x : ℝ} (hx : x ∈ Ioo a b) : 0 ≤ deriv (deriv f) x := by
  have hm := ((convexOnOpenInterval_iff_convexOn f a b).mp hc).monotoneOn_deriv hf
  have h := hm.derivWithin_nonneg (x := x)
  rwa [derivWithin_of_isOpen isOpen_Ioo hx] at h


theorem source_concave_second_nonpositive {f : ℝ → ℝ} {a b : ℝ}
    (hc : ConcaveOnOpenInterval f a b) (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    {x : ℝ} (hx : x ∈ Ioo a b) : deriv (deriv f) x ≤ 0 := by
  have hm := ((concaveOnOpenInterval_iff_concaveOn f a b).mp hc).antitoneOn_deriv hf
  have h := hm.derivWithin_nonpos (x := x)
  rwa [derivWithin_of_isOpen isOpen_Ioo hx] at h


theorem not_convex_or_concave_right_of_zero {f d g : ℝ → ℝ}
    (hf : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (d x) x)
    (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt d (g x) x)
    (hw : ∀ b : ℝ, 0 < b →
      (∃ u ∈ Ioo 0 b, 0 < g u) ∧ (∃ v ∈ Ioo 0 b, g v < 0))
    {b : ℝ} (hb : 0 < b) : ¬ ConvexOnOpenInterval f 0 b ∧ ¬ ConcaveOnOpenInterval f 0 b := by
  have hdif : ∀ x ∈ Ioo 0 b, DifferentiableAt ℝ f x :=
    fun x hx ↦ (hf x hx.1.ne').differentiableAt
  constructor
  · intro hc
    obtain ⟨v, hv, hneg⟩ := (hw b hb).2
    have hp := source_convex_second_nonnegative hc hdif hv
    rw [(second_hasDerivAt_off_zero hf hd hv.1.ne').deriv] at hp
    exact hneg.not_ge hp
  · intro hc
    obtain ⟨u, hu, hpos⟩ := (hw b hb).1
    have hn := source_concave_second_nonpositive hc hdif hu
    rw [(second_hasDerivAt_off_zero hf hd hu.1.ne').deriv] at hn
    exact not_le_of_gt hpos hn


theorem convexity_intervals_iff_second_deriv_sign {f d g : ℝ → ℝ}
    (hf : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (d x) x)
    (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt d (g x) x)
    (hw : ∀ b : ℝ, 0 < b →
      (∃ u ∈ Ioo 0 b, 0 < g u) ∧ (∃ v ∈ Ioo 0 b, g v < 0))
    (a b : ℝ) :
    (ConvexOnOpenInterval f a b ↔ 0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, 0 ≤ g x) ∧
      (ConcaveOnOpenInterval f a b ↔ 0 ∉ Ioo a b ∧ ∀ x ∈ Ioo a b, g x ≤ 0) := by
  have no_cross_convex : ConvexOnOpenInterval f a b → 0 ∉ Ioo a b := by
    intro hc h0
    have hc' : ConvexOnOpenInterval f 0 b := by
      apply (convexOnOpenInterval_iff_convexOn f 0 b).mpr
      apply ((convexOnOpenInterval_iff_convexOn f a b).mp hc).subset _ (convex_Ioo 0 b)
      intro x hx
      exact ⟨h0.1.trans hx.1, hx.2⟩
    exact (not_convex_or_concave_right_of_zero hf hd hw h0.2).1 hc'
  have no_cross_concave : ConcaveOnOpenInterval f a b → 0 ∉ Ioo a b := by
    intro hc h0
    have hc' : ConcaveOnOpenInterval f 0 b := by
      apply (concaveOnOpenInterval_iff_concaveOn f 0 b).mpr
      apply ((concaveOnOpenInterval_iff_concaveOn f a b).mp hc).subset _ (convex_Ioo 0 b)
      intro x hx
      exact ⟨h0.1.trans hx.1, hx.2⟩
    exact (not_convex_or_concave_right_of_zero hf hd hw h0.2).2 hc'
  constructor
  · constructor
    · intro hc
      have h0 := no_cross_convex hc
      refine ⟨h0, ?_⟩
      intro x hx
      have hx0 : x ≠ 0 := by rintro rfl; exact h0 hx
      have h := source_convex_second_nonnegative hc
        (fun y hy ↦ (hf y (by rintro rfl; exact h0 hy)).differentiableAt) hx
      rwa [(second_hasDerivAt_off_zero hf hd hx0).deriv] at h
    · rintro ⟨h0, hg⟩
      apply (convexOnOpenInterval_iff_second_deriv_nonneg f a b
        (twice_differentiable_interval_off_zero hf hd h0)).mpr
      intro x hx
      rw [(second_hasDerivAt_off_zero hf hd (by rintro rfl; exact h0 hx)).deriv]
      exact hg x hx
  · constructor
    · intro hc
      have h0 := no_cross_concave hc
      refine ⟨h0, ?_⟩
      intro x hx
      have hx0 : x ≠ 0 := by rintro rfl; exact h0 hx
      have h := source_concave_second_nonpositive hc
        (fun y hy ↦ (hf y (by rintro rfl; exact h0 hy)).differentiableAt) hx
      rwa [(second_hasDerivAt_off_zero hf hd hx0).deriv] at h
    · rintro ⟨h0, hg⟩
      apply concaveOnOpenInterval_of_second_deriv_nonpos f a b
        (twice_differentiable_interval_off_zero hf hd h0)
      intro x hx
      rw [(second_hasDerivAt_off_zero hf hd (by rintro rfl; exact h0 hx)).deriv]
      exact hg x hx


theorem second_zero_at_source_inflection {f : ℝ → ℝ} {a b c : ℝ}
    (hi : SourceInflectionOn f a b c) (hg : ContinuousAt (deriv (deriv f)) c) :
    deriv (deriv f) c = 0 := by
  obtain ⟨δ, hδ, hsub, hswitch⟩ := hi.2.2.2
  have hl : ∀ x ∈ Ioo (c - δ) c, DifferentiableAt ℝ f x := by
    intro x hx
    exact hi.2.1 x ⟨hsub ⟨hx.1, hx.2.trans (by linarith)⟩, hx.2.ne⟩
  have hr : ∀ x ∈ Ioo c (c + δ), DifferentiableAt ℝ f x := by
    intro x hx
    exact hi.2.1 x ⟨hsub ⟨(by linarith : c - δ < c).trans hx.1, hx.2⟩, hx.1.ne'⟩
  have hleft : ∀ᶠ x : ℝ in 𝓝[<] c, c - δ < x :=
    (eventually_gt_nhds (by linarith : c - δ < c)).filter_mono nhdsWithin_le_nhds
  have hright : ∀ᶠ x : ℝ in 𝓝[>] c, x < c + δ :=
    (eventually_lt_nhds (by linarith : c < c + δ)).filter_mono nhdsWithin_le_nhds
  rcases hswitch with ⟨hc, hn⟩ | ⟨hn, hc⟩
  · have hp : 0 ≤ deriv (deriv f) c := by
      apply ge_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (deriv (deriv f)) (𝓝[<] c) (𝓝 (deriv (deriv f) c)))
      filter_upwards [hleft, self_mem_nhdsWithin] with x hx hxc
      exact source_convex_second_nonnegative hc hl ⟨hx, hxc⟩
    have hq : deriv (deriv f) c ≤ 0 := by
      apply le_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (deriv (deriv f)) (𝓝[>] c) (𝓝 (deriv (deriv f) c)))
      filter_upwards [hright, self_mem_nhdsWithin] with x hx hxc
      exact source_concave_second_nonpositive hn hr ⟨hxc, hx⟩
    exact le_antisymm hq hp
  · have hp : deriv (deriv f) c ≤ 0 := by
      apply le_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (deriv (deriv f)) (𝓝[<] c) (𝓝 (deriv (deriv f) c)))
      filter_upwards [hleft, self_mem_nhdsWithin] with x hx hxc
      exact source_concave_second_nonpositive hn hl ⟨hx, hxc⟩
    have hq : 0 ≤ deriv (deriv f) c := by
      apply ge_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (deriv (deriv f)) (𝓝[>] c) (𝓝 (deriv (deriv f) c)))
      filter_upwards [hright, self_mem_nhdsWithin] with x hx hxc
      exact source_convex_second_nonnegative hc hr ⟨hxc, hx⟩
    exact le_antisymm hp hq


theorem inflection_of_simple_second_deriv_zero {f d g : ℝ → ℝ}
    (hf : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (d x) x)
    (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt d (g x) x)
    {c H : ℝ} (hc : c ≠ 0) (hg : HasDerivAt g H c) (hgz : g c = 0) (hH : H ≠ 0) :
    ∃ a b : ℝ, SourceInflectionOn f a b c := by
  have hn : ∀ᶠ x : ℝ in 𝓝 c, x ≠ 0 := eventually_ne_nhds hc
  have hcurv : deriv g c = H := hg.deriv
  have hs : ∀ᶠ x : ℝ in 𝓝 c,
      sign (g x) = sign (if 0 < H then x - c else c - x) := by
    by_cases hp : 0 < H
    · simpa only [if_pos hp] using
        eventually_nhdsWithin_sign_eq_of_deriv_pos (by rwa [hcurv]) hgz
    · have hm : H < 0 := lt_of_le_of_ne (le_of_not_gt hp) hH
      simpa only [if_neg hp] using
        eventually_nhdsWithin_sign_eq_of_deriv_neg (by rwa [hcurv]) hgz
  rcases lt_or_gt_of_ne hH with hneg | hpos
  all_goals
    obtain ⟨l, u, hcu, hsign⟩ := (hs.and hn).exists_Ioo_subset
    let δ : ℝ := min (c - l) (u - c) / 2
    have hδ : 0 < δ := by dsimp [δ]; exact div_pos (lt_min (sub_pos.mpr hcu.1) (sub_pos.mpr hcu.2)) (by norm_num)
    have hlδ : δ < c - l := by
      calc
        δ ≤ (c - l) / 2 := by
          dsimp only [δ]
          exact div_le_div_of_nonneg_right (min_le_left (c - l) (u - c)) (by norm_num)
        _ < c - l := half_lt_self (sub_pos.mpr hcu.1)
    have hrδ : δ < u - c := by
      calc
        δ ≤ (u - c) / 2 := by
          dsimp only [δ]
          exact div_le_div_of_nonneg_right (min_le_right (c - l) (u - c)) (by norm_num)
        _ < u - c := half_lt_self (sub_pos.mpr hcu.2)
    have hsub : Ioo (c - δ) (c + δ) ⊆ Ioo l u := by
      intro x hx
      constructor <;> linarith [hx.1, hx.2]
    have h0 : 0 ∉ Ioo (c - δ) (c + δ) := by
      intro hz
      exact (hsign (hsub hz)).2 rfl
    have h0l : 0 ∉ Ioo (c - δ) c := by
      intro hz
      exact h0 ⟨hz.1, hz.2.trans (by linarith)⟩
    have h0r : 0 ∉ Ioo c (c + δ) := by
      intro hz
      exact h0 ⟨(by linarith : c - δ < c).trans hz.1, hz.2⟩
    have hdl := twice_differentiable_interval_off_zero hf hd h0l
    have hdr := twice_differentiable_interval_off_zero hf hd h0r
    have hpoint : DifferentiableAt ℝ f c ∨
        calculus.Chapter04.Section01Derivatives.HasInfiniteDerivativeWithinAt f
          (Ioo (c - δ) (c + δ)) c := Or.inl (hf c hc).differentiableAt
    refine ⟨c - δ, c + δ, ?_⟩
  · apply sourceInflectionOn_of_second_deriv_pos_neg hδ hdl hdr hpoint
    · intro x hx
      rw [(second_hasDerivAt_off_zero hf hd (by rintro rfl; exact h0l hx)).deriv]
      have h := (hsign (hsub ⟨hx.1, hx.2.trans (by linarith)⟩)).1
      simp only [if_neg (by linarith : ¬ 0 < H)] at h
      rw [sign_pos (sub_pos.mpr hx.2)] at h
      exact sign_eq_one_iff.mp h
    · intro x hx
      rw [(second_hasDerivAt_off_zero hf hd (by rintro rfl; exact h0r hx)).deriv]
      have h := (hsign (hsub ⟨(by linarith : c - δ < c).trans hx.1, hx.2⟩)).1
      simp only [if_neg (by linarith : ¬ 0 < H)] at h
      rw [sign_neg (sub_neg.mpr hx.1)] at h
      exact sign_eq_neg_one_iff.mp h
  · apply sourceInflectionOn_of_second_deriv_neg_pos hδ hdl hdr hpoint
    · intro x hx
      rw [(second_hasDerivAt_off_zero hf hd (by rintro rfl; exact h0l hx)).deriv]
      have h := (hsign (hsub ⟨hx.1, hx.2.trans (by linarith)⟩)).1
      simp only [if_pos hpos] at h
      rw [sign_neg (sub_neg.mpr hx.2)] at h
      exact sign_eq_neg_one_iff.mp h
    · intro x hx
      rw [(second_hasDerivAt_off_zero hf hd (by rintro rfl; exact h0r hx)).deriv]
      have h := (hsign (hsub ⟨(by linarith : c - δ < c).trans hx.1, hx.2⟩)).1
      simp only [if_pos hpos] at h
      rw [sign_pos (sub_pos.mpr hx.1)] at h
      exact sign_eq_one_iff.mp h


theorem not_inflection_zero_of_second_deriv_sign_oscillation {f d g : ℝ → ℝ}
    (hf : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (d x) x)
    (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt d (g x) x)
    (hw : ∀ b : ℝ, 0 < b →
      (∃ u ∈ Ioo 0 b, 0 < g u) ∧ (∃ v ∈ Ioo 0 b, g v < 0)) :
    ¬ ∃ a b : ℝ, SourceInflectionOn f a b 0 := by
  rintro ⟨a, b, hi⟩
  obtain ⟨δ, hδ, _, hs⟩ := hi.2.2.2
  have hn := not_convex_or_concave_right_of_zero hf hd hw hδ
  simp only [zero_add] at hs
  rcases hs with ⟨_, hc⟩ | ⟨_, hc⟩
  · exact hn.2 hc
  · exact hn.1 hc


def reciprocalPhase (c : ℝ) (n : ℕ) : ℝ := (c + (n : ℝ) * (2 * Real.pi))⁻¹

theorem reciprocalPhase_pos {c : ℝ} (hc : 0 < c) (n : ℕ) : 0 < reciprocalPhase c n := by
  unfold reciprocalPhase
  positivity

theorem reciprocalPhase_tendsto_zero (c : ℝ) :
    Tendsto (reciprocalPhase c) atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_atTop_add_const_left atTop c
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity : 0 < 2 * Real.pi))

theorem reciprocalPhase_trig (c : ℝ) (n : ℕ) :
    Real.sin (1 / reciprocalPhase c n) = Real.sin c ∧
      Real.cos (1 / reciprocalPhase c n) = Real.cos c := by
  simp only [reciprocalPhase, one_div, inv_inv]
  exact ⟨Real.sin_add_nat_mul_two_pi c n, Real.cos_add_nat_mul_two_pi c n⟩


theorem complete_inflection_points {f d g h : ℝ → ℝ}
    (hf : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (d x) x)
    (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt d (g x) x)
    (hg : ∀ x : ℝ, x ≠ 0 → HasDerivAt g (h x) x)
    (hw : ∀ b : ℝ, 0 < b →
      (∃ u ∈ Ioo 0 b, 0 < g u) ∧ (∃ v ∈ Ioo 0 b, g v < 0))
    (hroot : ∀ x : ℝ, x ≠ 0 → g x = 0 → h x ≠ 0) (x : ℝ) :
    (∃ a b : ℝ, SourceInflectionOn f a b x) ↔ x ≠ 0 ∧ g x = 0 := by
  constructor
  · rintro ⟨a, b, hi⟩
    have hx : x ≠ 0 := by
      rintro rfl
      exact not_inflection_zero_of_second_deriv_sign_oscillation hf hd hw ⟨a, b, hi⟩
    have he : deriv (deriv f) =ᶠ[𝓝 x] g := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      exact (second_hasDerivAt_off_zero hf hd hy).deriv
    have hc := (hg x hx).continuousAt.congr_of_eventuallyEq he
    have hz := second_zero_at_source_inflection hi hc
    rw [(second_hasDerivAt_off_zero hf hd hx).deriv] at hz
    exact ⟨hx, hz⟩
  · rintro ⟨hx, hz⟩
    exact inflection_of_simple_second_deriv_zero hf hd hx (hg x hx) hz (hroot x hx hz)

end calculus.Chapter04.Section04OscillatingFunctionInvestigationSupport
