import calculus.Chapter04.Section01Derivatives
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# 4.1.3: các quy tắc đạo hàm cơ bản

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 158–258. Xét miền mở; quy tắc hàm hợp yêu cầu `f(I) ⊆ J`.
-/
namespace calculus.Chapter04.Section01Rules
open Filter Set Section01Derivatives
open scoped Topology

/-- Định lí 4.1.9(i): đạo hàm của tổng trên miền mở. -/
theorem source_add {f g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x a b : ℝ} (hx : x ∈ I) (hf : HasDerivativeWithinAt f I x a)
    (hg : HasDerivativeWithinAt g I x b) :
    HasDerivativeWithinAt (fun y ↦ f y + g y) I x (a + b) := by
  apply (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen _ I hI x _ hx).mpr
  exact ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen f I hI x a hx).mp hf).add
    ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen g I hI x b hx).mp hg)

/-- Định lí 4.1.9(ii): đạo hàm của tích với hằng số thực tùy ý. -/
theorem source_const_mul {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x a : ℝ} (hx : x ∈ I) (hf : HasDerivativeWithinAt f I x a) (c : ℝ) :
    HasDerivativeWithinAt (fun y ↦ c * f y) I x (c * a) := by
  apply (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen _ I hI x _ hx).mpr
  exact ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen f I hI x a hx).mp hf).const_mul c

/-- Định lí 4.1.9(iii): quy tắc đạo hàm của tích. -/
theorem source_mul {f g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x a b : ℝ} (hx : x ∈ I) (hf : HasDerivativeWithinAt f I x a)
    (hg : HasDerivativeWithinAt g I x b) :
    HasDerivativeWithinAt (fun y ↦ f y * g y) I x (a * g x + f x * b) := by
  apply (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen _ I hI x _ hx).mpr
  exact ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen f I hI x a hx).mp hf).mul
    ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen g I hI x b hx).mp hg)

/-- Định lí 4.1.9(iv): đạo hàm của thương trên miền mẫu khác 0, với `g(x₀) ≠ 0`. -/
theorem source_div {f g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x a b : ℝ} (hx : x ∈ I) (hf : HasDerivativeWithinAt f I x a)
    (hg : HasDerivativeWithinAt g I x b) (hgn : g x ≠ 0) :
    HasDerivativeWithinAt (fun y ↦ f y / g y) (I ∩ {y | g y ≠ 0}) x
      ((a * g x - f x * b) / (g x) ^ 2) := by
  apply (hasDerivativeWithinAt_iff_hasDerivWithinAt _ _ _ _).mpr
  exact (((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen f I hI x a hx).mp hf).fun_div
    ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen g I hI x b hx).mp hg) hgn).hasDerivWithinAt


theorem product_difference_quotient (f g : ℝ → ℝ) (x y : ℝ) (hy : y ≠ x) :
    (f y * g y - f x * g x) / (y - x) =
      (f y - f x) / (y - x) * g y + f x * ((g y - g x) / (y - x)) := by
  field_simp [sub_ne_zero.mpr hy]
  ring


theorem source_denominator_eventually_ne {g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x b : ℝ} (hx : x ∈ I) (hg : HasDerivativeWithinAt g I x b) (hgn : g x ≠ 0) :
    ∀ᶠ y in 𝓝 x, g y ≠ 0 :=
  ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen g I hI x b hx).mp hg).continuousAt.eventually_ne hgn


theorem source_quotient_domain_mem_nhds {g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x b : ℝ} (hx : x ∈ I) (hg : HasDerivativeWithinAt g I x b) (hgn : g x ≠ 0) :
    I ∩ {y | g y ≠ 0} ∈ 𝓝 x :=
  inter_mem (hI.mem_nhds hx) (source_denominator_eventually_ne hI hx hg hgn)

/-- Thương sai phân với giá trị `b` được điền tại tâm. -/
noncomputable def filledDifferenceQuotient (g : ℝ → ℝ) (c b : ℝ) : ℝ → ℝ :=
  Function.update (fun y ↦ (g y - g c) / (y - c)) c b


theorem filledDifferenceQuotient_factor (g : ℝ → ℝ) (c b y : ℝ) :
    g y - g c = filledDifferenceQuotient g c b y * (y - c) := by
  classical
  by_cases hy : y = c
  · simp [hy]
  · simp [filledDifferenceQuotient, Function.update, hy, sub_ne_zero.mpr hy]


theorem filledDifferenceQuotient_continuousAt {g : ℝ → ℝ} {c b : ℝ}
    (hg : HasDerivAt g b c) : ContinuousAt (filledDifferenceQuotient g c b) c := by
  classical
  exact hg.continuousAt_div

/-- Định lí 4.1.10: quy tắc hàm hợp, với `f(I) ⊆ J`. -/
theorem source_comp {f g : ℝ → ℝ} {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)
    {x a b : ℝ} (hx : x ∈ I) (hmap : MapsTo f I J)
    (hf : HasDerivativeWithinAt f I x a) (hg : HasDerivativeWithinAt g J (f x) b) :
    HasDerivativeWithinAt (g ∘ f) I x (b * a) := by
  apply (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen _ I hI x _ hx).mpr
  exact ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen g J hJ (f x) b (hmap hx)).mp hg).comp x
    ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen f I hI x a hx).mp hf)


theorem polynomial_inside_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 5 * y ^ 4 + 4 * y ^ 3 + 1) (20 * x ^ 3 + 12 * x ^ 2) x := by
  convert! (((hasDerivAt_pow 4 x).const_mul 5).add
    ((hasDerivAt_pow 3 x).const_mul 4)).add_const 1 using 1; ring

/-- Ví dụ 4.1.11: đạo hàm của lũy thừa bậc 2023. -/
theorem high_polynomial_power_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (5 * y ^ 4 + 4 * y ^ 3 + 1) ^ 2023)
      (2023 * (5 * x ^ 4 + 4 * x ^ 3 + 1) ^ 2022 * (20 * x ^ 3 + 12 * x ^ 2)) x := by
  simpa using (polynomial_inside_hasDerivAt x).fun_pow 2023


theorem triple_chain_corrected {f g h : ℝ → ℝ} {x a b c : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b (f x))
    (hh : HasDerivAt h c (g (f x))) : HasDerivAt (h ∘ g ∘ f) (c * b * a) x := by
  simpa only [Function.comp_assoc, mul_assoc] using (hh.comp (f x) hg).comp x hf


theorem inverse_derivative_of_continuous_inverse {f g : ℝ → ℝ} {x a : ℝ}
    (hf : HasDerivAt f a x) (ha : a ≠ 0) (hg : ContinuousAt g (f x))
    (hgf : g (f x) = x) (hfg : ∀ᶠ y in 𝓝 (f x), f (g y) = y) :
    HasDerivAt g (1 / a) (f x) := by
  have hf' : HasDerivAt f a (g (f x)) := by simpa only [hgf] using hf
  simpa only [one_div] using hf'.of_local_left_inverse hg ha hfg


theorem interval_inverse_continuousAt {f g : ℝ → ℝ} {a b c d x : ℝ}
    (hx : x ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b))
    (hbij : BijOn f (Ioo a b) (Ioo c d)) (hgmap : MapsTo g (Ioo c d) (Ioo a b))
    (hgf : LeftInvOn g f (Ioo a b)) (hfg : RightInvOn g f (Ioo c d)) :
    ContinuousAt g (f x) := by
  have hfx : f x ∈ Ioo c d := hbij.mapsTo hx
  have himage : g '' Ioo c d = Ioo a b := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hgmap hy
    · intro y hy
      exact ⟨f y, hbij.mapsTo hy, hgf hy⟩
  have hJ : Ioo c d ∈ 𝓝 (f x) := isOpen_Ioo.mem_nhds hfx
  have hGI : g '' Ioo c d ∈ 𝓝 (g (f x)) := by
    rw [himage, hgf hx]
    exact isOpen_Ioo.mem_nhds hx
  rcases hf.strictMonoOn_of_injOn_Ioo (lt_trans hx.1 hx.2) hbij.injOn with hm | ha
  · have hmg : StrictMonoOn g (Ioo c d) := by
      intro y hy z hz hyz
      apply (hm.lt_iff_lt (hgmap hy) (hgmap hz)).mp
      simpa only [hfg hy, hfg hz] using hyz
    exact hmg.continuousAt_of_image_mem_nhds hJ hGI
  · have hmg : StrictMonoOn (β := ℝᵒᵈ) g (Ioo c d) := by
      intro y hy z hz hyz
      change g z < g y
      apply lt_of_not_ge
      intro hge
      have hbad := ha.antitoneOn (hgmap hy) (hgmap hz) hge
      exact hyz.not_ge (by simpa only [hfg hy, hfg hz] using hbad)
    exact hmg.continuousAt_of_image_mem_nhds hJ hGI

/-- Định lí 4.1.14: đạo hàm của hàm ngược trên hai khoảng mở. -/
theorem source_inverse {f g : ℝ → ℝ} {a b c d x L : ℝ}
    (hx : x ∈ Ioo a b) (hfcont : ContinuousOn f (Ioo a b))
    (hbij : BijOn f (Ioo a b) (Ioo c d)) (hgmap : MapsTo g (Ioo c d) (Ioo a b))
    (hgf : LeftInvOn g f (Ioo a b)) (hfg : RightInvOn g f (Ioo c d))
    (hf : HasDerivativeWithinAt f (Ioo a b) x L) (hL : L ≠ 0) :
    HasDerivativeWithinAt g (Ioo c d) (f x) (1 / L) := by
  apply (hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen g _ isOpen_Ioo _ _ (hbij.mapsTo hx)).mpr
  apply inverse_derivative_of_continuous_inverse
    ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen f _ isOpen_Ioo x L hx).mp hf) hL
    (interval_inverse_continuousAt hx hfcont hbij hgmap hgf hfg) (hgf hx)
  filter_upwards [isOpen_Ioo.mem_nhds (hbij.mapsTo hx)] with y hy
  exact hfg hy

/-- Ví dụ 4.1.15: sin và arcsin là hai hàm ngược trên hai khoảng mở tương ứng. -/
theorem sine_arcsine_bijOn :
    BijOn Real.sin (Ioo (-(Real.pi / 2)) (Real.pi / 2)) (Ioo (-1 : ℝ) 1) ∧
      LeftInvOn Real.arcsin Real.sin (Ioo (-(Real.pi / 2)) (Real.pi / 2)) ∧
      RightInvOn Real.arcsin Real.sin (Ioo (-1 : ℝ) 1) := by
  exact ⟨Real.sinPartialHomeomorph.bijOn, Real.sinPartialHomeomorph.leftInvOn,
    Real.sinPartialHomeomorph.rightInvOn⟩


theorem sine_derivative_nonzero_and_inverse_formula {x : ℝ}
    (hx : x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    Real.cos x ≠ 0 ∧ 1 / Real.cos x = 1 / Real.sqrt (1 - Real.sin x ^ 2) := by
  constructor
  · exact ne_of_gt (Real.cos_pos_of_mem_Ioo hx)
  · rw [← Real.cos_arcsin, Real.arcsin_sin hx.1.le hx.2.le]

/-- Ví dụ 4.1.15: đạo hàm của arcsin trên `−1 < y < 1`. -/
theorem arcsine_hasDerivAt_on_open_interval {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.arcsin (1 / Real.sqrt (1 - y ^ 2)) y :=
  Real.hasDerivAt_arcsin (ne_of_gt hy.1) (ne_of_lt hy.2)

end calculus.Chapter04.Section01Rules
