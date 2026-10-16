import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# 4.1.1: đạo hàm hữu hạn và các ví dụ đầu tiên

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 16–120.
-/
namespace calculus.Chapter04.Section01Derivatives
open Filter Set
open scoped Topology


theorem punctured_domain_filter_eq (I : Set ℝ) (hI : IsOpen I) (x : ℝ) (hx : x ∈ I) :
    𝓝[I \ {x}] x = 𝓝[≠] x := by
  rw [sdiff_eq]
  exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hI.mem_nhds hx))


theorem open_domain_accumulation (I : Set ℝ) (hI : IsOpen I) (x : ℝ) (hx : x ∈ I) :
    AccPt x (𝓟 (I \ {x})) := by
  rw [accPt_principal_iff_nhdsWithin]
  have hs : (I \ {x}) \ {x} = I \ {x} := by ext y; simp
  rw [hs, punctured_domain_filter_eq I hI x hx]
  infer_instance


noncomputable def restrictedDifferenceQuotient (f : ℝ → ℝ) (I : Set ℝ) (x : ℝ) : {y : ℝ // y ∈ I \ {x}} → ℝ :=
  fun y ↦ (f y - f x) / ((y : ℝ) - x)


theorem restrictedDifferenceQuotient_denominator_ne_zero (I : Set ℝ) (x : ℝ)
    (y : {z : ℝ // z ∈ I \ {x}}) : (y : ℝ) - x ≠ 0 := by
  exact sub_ne_zero.mpr (by simpa only [Set.mem_singleton_iff] using y.property.2)

/-- Giới hạn hữu hạn của thương sai phân trên `I \ {x₀}`. -/
def HasDerivativeWithinAt (f : ℝ → ℝ) (I : Set ℝ) (x L : ℝ) : Prop :=
  Tendsto (fun y ↦ (f y - f x) / (y - x)) (𝓝[I \ {x}] x) (𝓝 L)


theorem slope_eq_difference_quotient (f : ℝ → ℝ) (x : ℝ) :
    slope f x = (fun y ↦ (f y - f x) / (y - x)) := by
  funext y
  exact slope_def_field f x y


theorem hasDerivativeWithinAt_iff_hasDerivWithinAt (f : ℝ → ℝ) (I : Set ℝ) (x L : ℝ) :
    HasDerivativeWithinAt f I x L ↔ HasDerivWithinAt f L I x := by
  simpa only [HasDerivativeWithinAt, slope_eq_difference_quotient] using
    (hasDerivWithinAt_iff_tendsto_slope (f := f) (f' := L) (s := I) (x := x)).symm


theorem hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen (f : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (x L : ℝ) (hx : x ∈ I) : HasDerivativeWithinAt f I x L ↔ HasDerivAt f L x := by
  rw [hasDerivativeWithinAt_iff_hasDerivWithinAt]
  exact ⟨fun h ↦ h.hasDerivAt (hI.mem_nhds hx), fun h ↦ h.hasDerivWithinAt⟩


def DifferentiableWithinDomainAt (f : ℝ → ℝ) (I : Set ℝ) (x : ℝ) : Prop :=
  ∃ L : ℝ, HasDerivativeWithinAt f I x L


theorem differentiableWithinDomainAt_iff_differentiableAt_of_isOpen (f : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I)
    (x : ℝ) (hx : x ∈ I) : DifferentiableWithinDomainAt f I x ↔ DifferentiableAt ℝ f x := by
  simp only [DifferentiableWithinDomainAt, hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen f I hI x _ hx]
  exact ⟨fun ⟨_, h⟩ ↦ h.differentiableAt, fun h ↦ ⟨deriv f x, h.hasDerivAt⟩⟩


def DifferentiableOnDomain (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, DifferentiableWithinDomainAt f I x


noncomputable def restrictedDerivative (f : ℝ → ℝ) (I : Set ℝ) : I → ℝ :=
  fun x ↦ deriv f x


theorem differentiableOnDomain_iff_differentiableOn_of_isOpen (f : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I) :
    DifferentiableOnDomain f I ↔ DifferentiableOn ℝ f I := by
  constructor
  · intro h x hx
    exact ((differentiableWithinDomainAt_iff_differentiableAt_of_isOpen f I hI x hx).mp (h x hx)).differentiableWithinAt
  · intro h x hx
    apply (differentiableWithinDomainAt_iff_differentiableAt_of_isOpen f I hI x hx).mpr
    exact (h x hx).differentiableAt (hI.mem_nhds hx)


theorem deriv_eq_of_hasDerivativeWithinAt {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x L : ℝ} (hx : x ∈ I) (h : HasDerivativeWithinAt f I x L) : deriv f x = L :=
  ((hasDerivativeWithinAt_iff_hasDerivAt_of_isOpen f I hI x L hx).mp h).deriv

/-- Nhận xét 4.1.2: thay `x = x₀ + h` trong thương sai phân. -/
theorem hasDerivAt_iff_increment_limit (f : ℝ → ℝ) (x L : ℝ) :
    HasDerivAt f L x ↔
      Tendsto (fun h ↦ (f (x + h) - f x) / h) (𝓝[≠] (0 : ℝ)) (𝓝 L) := by
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_iff_tendsto_slope_zero (f := f) (f' := L) (x := x))

/-- Ví dụ 4.1.4(a): đạo hàm của `f(x) = x` bằng 1. -/
theorem identity_hasDerivAt (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y) 1 x := hasDerivAt_id x

/-- Ví dụ 4.1.4(b): đạo hàm của `x²` tại `x₀` bằng `2x₀`. -/
theorem square_hasDerivAt (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_id x).fun_pow 2

/-- Ví dụ 4.1.4(c): đạo hàm của sin bằng cos. -/
theorem sine_hasDerivAt (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x

/-- Ví dụ 4.1.4(d): `|x|` liên tục nhưng không khả vi tại 0. -/
theorem abs_continuous_not_differentiable_zero :
    ContinuousAt (abs : ℝ → ℝ) 0 ∧ ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 :=
  ⟨continuous_abs.continuousAt, not_differentiableAt_abs_zero⟩


theorem abs_slope_right_limit :
    Tendsto (fun y : ℝ ↦ (|y| - |(0 : ℝ)|) / (y - 0)) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hp : 0 < y := hy
  simp [abs_of_pos hp, ne_of_gt hp]


theorem abs_slope_left_limit :
    Tendsto (fun y : ℝ ↦ (|y| - |(0 : ℝ)|) / (y - 0)) (𝓝[<] 0) (𝓝 (-1)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hp : y < 0 := hy
  simp [abs_of_neg hp, ne_of_lt hp]

/-- Định lí 4.1.5: hàm khả vi tại một điểm trong miền mở thì liên tục tại điểm đó. -/
theorem differentiableWithinDomainAt_continuousAt {f : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) {x : ℝ} (hx : x ∈ I) (h : DifferentiableWithinDomainAt f I x) :
    ContinuousAt f x := ((differentiableWithinDomainAt_iff_differentiableAt_of_isOpen f I hI x hx).mp h).continuousAt


def HasRightDerivativeAt (f : ℝ → ℝ) (x L : ℝ) : Prop :=
  Tendsto (fun y ↦ (f y - f x) / (y - x)) (𝓝[>] x) (𝓝 L)


def HasLeftDerivativeAt (f : ℝ → ℝ) (x L : ℝ) : Prop :=
  Tendsto (fun y ↦ (f y - f x) / (y - x)) (𝓝[<] x) (𝓝 L)

/-- Định nghĩa 4.1.7: khả vi trong `(a, b)`, có đạo hàm bên phải tại `a` và bên trái tại `b`. -/
def DifferentiableOnClosedInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) ∧
    (∃ L : ℝ, HasRightDerivativeAt f a L) ∧ (∃ L : ℝ, HasLeftDerivativeAt f b L)

/-- Quy ước 4.1.8(ii): thương sai phân có giới hạn `+∞` hoặc `−∞`. -/
def HasInfiniteDerivativeWithinAt (f : ℝ → ℝ) (I : Set ℝ) (x : ℝ) : Prop :=
  Tendsto (fun y ↦ (f y - f x) / (y - x)) (𝓝[I \ {x}] x) atTop ∨
    Tendsto (fun y ↦ (f y - f x) / (y - x)) (𝓝[I \ {x}] x) atBot

/-- Nhận xét 4.1.8(i): đạo hàm tồn tại khi và chỉ khi hai đạo hàm một bên hữu hạn tồn tại và bằng nhau. -/
theorem hasDerivAt_iff_left_right (f : ℝ → ℝ) (x L : ℝ) :
    HasDerivAt f L x ↔ HasLeftDerivativeAt f x L ∧ HasRightDerivativeAt f x L := by
  simpa only [HasLeftDerivativeAt, HasRightDerivativeAt, slope_eq_difference_quotient] using
    (hasDerivAt_iff_tendsto_slope_left_right (f := f) (f' := L) (x := x))

end calculus.Chapter04.Section01Derivatives
