import calculus.Chapter04.Section01Rules
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# 4.2: vi phân bậc nhất

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 715–762. Vi phân tuyến tính theo số gia `h`; phép chia `df/h` chỉ có ý nghĩa khi `h ≠ 0`.
-/
namespace calculus.Chapter04.Section02
open Filter Set Asymptotics
open scoped Topology


def increment (f : ℝ → ℝ) (x h : ℝ) : ℝ := f (x + h) - f x

/-- Phần dư sau khi trừ `Ah` là vô cùng bé bậc cao so với `h`. -/
def HasLinearApproximation (f : ℝ → ℝ) (x A : ℝ) : Prop :=
  (fun h ↦ increment f x h - A * h) =o[𝓝 0] (fun h : ℝ ↦ h)


noncomputable def firstDifferential (f : ℝ → ℝ) (x h : ℝ) : ℝ := deriv f x * h


theorem valid_increment_eventually {I : Set ℝ} (hI : IsOpen I) {x : ℝ} (hx : x ∈ I) :
    ∀ᶠ h in 𝓝 (0 : ℝ), x + h ∈ I := by
  have ht : Tendsto (fun h : ℝ ↦ x + h) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tendsto_id : Tendsto (fun h : ℝ ↦ h) (𝓝 0) (𝓝 0))
  exact ht.eventually (hI.mem_nhds hx)


theorem hasLinearApproximation_iff_hasDerivAt (f : ℝ → ℝ) (x A : ℝ) :
    HasLinearApproximation f x A ↔ HasDerivAt f A x := by
  simpa only [HasLinearApproximation, increment, smul_eq_mul, mul_comm] using
    (hasDerivAt_iff_isLittleO_nhds_zero (f := f) (f' := A) (x := x)).symm

/-- Mệnh đề 4.2.2: xấp xỉ tuyến tính tồn tại khi và chỉ khi hàm khả vi. -/
theorem exists_linearApproximation_iff (f : ℝ → ℝ) (x : ℝ) :
    (∃ A, HasLinearApproximation f x A) ↔ DifferentiableAt ℝ f x := by
  simp only [hasLinearApproximation_iff_hasDerivAt]
  exact ⟨fun ⟨_, h⟩ ↦ h.differentiableAt, fun h ↦ ⟨deriv f x, h.hasDerivAt⟩⟩


theorem linearApproximation_coefficient {f : ℝ → ℝ} {x A : ℝ}
    (h : HasLinearApproximation f x A) : A = deriv f x :=
  (hasLinearApproximation_iff_hasDerivAt f x A).mp h |>.deriv.symm


theorem firstDifferential_eq {f : ℝ → ℝ} {x A : ℝ}
    (h : HasLinearApproximation f x A) (u : ℝ) : firstDifferential f x u = A * u := by
  rw [firstDifferential, ← linearApproximation_coefficient h]


theorem firstDifferential_id (x h : ℝ) : firstDifferential (fun y : ℝ ↦ y) x h = h := by
  simp [firstDifferential]


theorem derivative_from_differential {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    firstDifferential f x h / h = deriv f x := by
  rw [firstDifferential, mul_div_cancel_right₀ _ hh]


theorem firstDifferential_linear (f : ℝ → ℝ) (x u v c : ℝ) :
    firstDifferential f x (u + v) = firstDifferential f x u + firstDifferential f x v ∧
      firstDifferential f x (c * u) = c * firstDifferential f x u := by
  dsimp [firstDifferential]
  constructor <;> ring


theorem firstDifferential_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h : ℝ) :
    firstDifferential (fun y ↦ f y + g y) x h =
      firstDifferential f x h + firstDifferential g x h := by
  simp only [firstDifferential, (hf.hasDerivAt.fun_add hg.hasDerivAt).deriv, add_mul]


theorem firstDifferential_const_mul {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (c h : ℝ) :
    firstDifferential (fun y ↦ c * f y) x h = c * firstDifferential f x h := by
  simp only [firstDifferential, (hf.hasDerivAt.const_mul c).deriv, mul_assoc]


theorem firstDifferential_mul {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h : ℝ) :
    firstDifferential (fun y ↦ f y * g y) x h =
      f x * firstDifferential g x h + g x * firstDifferential f x h := by
  simp only [firstDifferential, (hf.hasDerivAt.fun_mul hg.hasDerivAt).deriv]
  ring


theorem firstDifferential_div {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hg0 : g x ≠ 0) (h : ℝ) :
    firstDifferential (fun y ↦ f y / g y) x h =
      (g x * firstDifferential f x h - f x * firstDifferential g x h) / g x ^ 2 := by
  simp only [firstDifferential, (hf.hasDerivAt.fun_div hg.hasDerivAt hg0).deriv]
  ring


theorem firstDifferential_comp {f φ : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (φ t)) (hφ : DifferentiableAt ℝ φ t) (h : ℝ) :
    firstDifferential (f ∘ φ) t h = deriv f (φ t) * deriv φ t * h ∧
      firstDifferential (f ∘ φ) t h = firstDifferential f (φ t) (firstDifferential φ t h) := by
  simp only [firstDifferential, (hf.hasDerivAt.comp t hφ.hasDerivAt).deriv, mul_assoc]
  exact ⟨trivial, trivial⟩


theorem linearApproximation_error_bound {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, |h| < δ →
      |f (x + h) - (f x + firstDifferential f x h)| ≤ ε * |h| := by
  have ho := (hasLinearApproximation_iff_hasDerivAt f x (deriv f x)).mpr hf.hasDerivAt
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp (ho.def hε)
  refine ⟨δ, hδ, fun h hh ↦ ?_⟩
  have he : f (x + h) - (f x + firstDifferential f x h) = increment f x h - deriv f x * h := by
    dsimp [increment, firstDifferential]
    ring
  rw [he]
  simpa only [Real.norm_eq_abs] using hb (by simpa only [Real.dist_eq, sub_zero] using hh)

end calculus.Chapter04.Section02
