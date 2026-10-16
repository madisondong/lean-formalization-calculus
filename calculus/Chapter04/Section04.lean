import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# §4.4: quy tắc L'Hospital cho dạng 0/0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1432–1490 và chú thích về các phía, tại vô cùng. Xét dạng 0/0, với hai hàm khả vi và đạo hàm mẫu khác 0.
-/
namespace calculus.Chapter04.Section04
open Set Filter
open scoped Topology


theorem lhopital_zero_right {f g : ℝ → ℝ} {a b : ℝ} {l : Filter ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (hne : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (hfl : Tendsto f (𝓝[>] a) (𝓝 0)) (hgl : Tendsto g (𝓝[>] a) (𝓝 0))
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[>] a) l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) l := by
  exact HasDerivAt.lhopital_zero_right_on_Ioo hab
    (fun x hx ↦ ((hf x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt)
    (fun x hx ↦ ((hg x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt)
    hne hfl hgl hl


theorem lhopital_zero_left {f g : ℝ → ℝ} {a b : ℝ} {l : Filter ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (hne : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (hfl : Tendsto f (𝓝[<] b) (𝓝 0)) (hgl : Tendsto g (𝓝[<] b) (𝓝 0))
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[<] b) l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[<] b) l := by
  exact HasDerivAt.lhopital_zero_left_on_Ioo hab
    (fun x hx ↦ ((hf x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt)
    (fun x hx ↦ ((hg x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt)
    hne hfl hgl hl


theorem lhopital_zero_atTop {f g : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hf : DifferentiableOn ℝ f (Ioi a)) (hg : DifferentiableOn ℝ g (Ioi a))
    (hne : ∀ x ∈ Ioi a, deriv g x ≠ 0)
    (hfl : Tendsto f atTop (𝓝 0)) (hgl : Tendsto g atTop (𝓝 0))
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) atTop l) :
    Tendsto (fun x ↦ f x / g x) atTop l := by
  exact HasDerivAt.lhopital_zero_atTop_on_Ioi
    (fun x hx ↦ ((hf x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt)
    (fun x hx ↦ ((hg x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt)
    hne hfl hgl hl


theorem lhopital_zero_atBot {f g : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hf : DifferentiableOn ℝ f (Iio a)) (hg : DifferentiableOn ℝ g (Iio a))
    (hne : ∀ x ∈ Iio a, deriv g x ≠ 0)
    (hfl : Tendsto f atBot (𝓝 0)) (hgl : Tendsto g atBot (𝓝 0))
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) atBot l) :
    Tendsto (fun x ↦ f x / g x) atBot l := by
  exact HasDerivAt.lhopital_zero_atBot_on_Iio
    (fun x hx ↦ ((hf x hx).differentiableAt (isOpen_Iio.mem_nhds hx)).hasDerivAt)
    (fun x hx ↦ ((hg x hx).differentiableAt (isOpen_Iio.mem_nhds hx)).hasDerivAt)
    hne hfl hgl hl


theorem lhopital_zero_punctured {f f' g g' : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hf : ∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x)
    (hne : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (hfl : Tendsto f (𝓝[≠] a) (𝓝 0)) (hgl : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hl : Tendsto (fun x ↦ f' x / g' x) (𝓝[≠] a) l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[≠] a) l :=
  HasDerivAt.lhopital_zero_nhdsNE hf hg hne hfl hgl hl


theorem sine_quotient_right : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[>] 0) (𝓝 1) := by
  simpa only [zero_add, Real.sin_zero, Real.cos_zero, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using (Real.hasDerivAt_sin 0).tendsto_slope_zero_right


theorem one_sub_cosine_div_square_right :
    Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / x ^ 2) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hf (x : ℝ) : HasDerivAt (fun x : ℝ ↦ 1 - Real.cos x) (Real.sin x) x := by
    simpa only [neg_neg] using (Real.hasDerivAt_cos x).const_sub 1
  have hg (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * x) x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq] using
      (hasDerivAt_id x).fun_pow 2
  apply HasDerivAt.lhopital_zero_right_on_Ioo (a := 0) (b := 1) (by norm_num)
    (fun x _ ↦ hf x) (fun x _ ↦ hg x) (fun x hx ↦ mul_ne_zero (by norm_num) hx.1.ne')
  · simpa only [Real.cos_zero, sub_self] using
      (hf 0).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (continuous_pow 2).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · convert sine_quotient_right.div_const 2 using 1
    ext x
    ring


theorem logarithm_div_identity_atTop :
    Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
  simpa only [pow_one, one_mul, add_zero] using
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

end calculus.Chapter04.Section04
