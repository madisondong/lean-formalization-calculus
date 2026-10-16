import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Tiệm cận đứng, ngang và xiên

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1961–1989. Xét riêng hai phía và hai đầu vô cùng.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04Asymptotes
open Filter Set
open scoped Topology

/-- Định nghĩa 4.4.22: ít nhất một giới hạn một phía bằng `+∞` hoặc `−∞`. -/
def HasVerticalAsymptoteAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  (Tendsto f (𝓝[>] a) atTop ∨ Tendsto f (𝓝[>] a) atBot) ∨
    (Tendsto f (𝓝[<] a) atTop ∨ Tendsto f (𝓝[<] a) atBot)

/-- Đường thẳng `y=b` là tiệm cận ngang ở ít nhất một trong hai đầu vô cùng. -/
def HasHorizontalAsymptote (f : ℝ → ℝ) (b : ℝ) : Prop :=
  Tendsto f atTop (𝓝 b) ∨ Tendsto f atBot (𝓝 b)

/-- Đường thẳng `y=mx+b` là tiệm cận xiên, với `m ≠ 0`. -/
def HasObliqueAsymptote (f : ℝ → ℝ) (m b : ℝ) : Prop :=
  m ≠ 0 ∧ (Tendsto (fun x ↦ f x - (m * x + b)) atTop (𝓝 0) ∨
    Tendsto (fun x ↦ f x - (m * x + b)) atBot (𝓝 0))

/-- Ví dụ 4.4.23(a): giới hạn logarit từ phía phải tại 0. -/
theorem logarithm_vertical_asymptote_zero : HasVerticalAsymptoteAt Real.log 0 :=
  Or.inl (Or.inr Real.tendsto_log_nhdsGT_zero)

/-- Ví dụ 4.4.23(b): hàm mũ tại `−∞`. -/
theorem exponential_horizontal_asymptote_zero : HasHorizontalAsymptote Real.exp 0 :=
  Or.inr Real.tendsto_exp_atBot

/-- Hai kết luận của Ví dụ 4.4.23. -/
theorem source_logarithm_exponential_asymptotes :
    HasVerticalAsymptoteAt Real.log 0 ∧ HasHorizontalAsymptote Real.exp 0 :=
  ⟨logarithm_vertical_asymptote_zero, exponential_horizontal_asymptote_zero⟩


theorem affine_residual_limit_iff {L : Filter ℝ}
    (hInv : Tendsto (fun x : ℝ ↦ x⁻¹) L (𝓝 0))
    (hNe : ∀ᶠ x : ℝ in L, x ≠ 0) (f : ℝ → ℝ) (m b : ℝ) :
    Tendsto (fun x ↦ f x - (m * x + b)) L (𝓝 0) ↔
      Tendsto (fun x ↦ f x / x) L (𝓝 m) ∧
        Tendsto (fun x ↦ f x - m * x) L (𝓝 b) := by
  constructor
  · intro hr
    have hi : Tendsto (fun x ↦ f x - m * x) L (𝓝 b) := by
      have hi0 := hr.add_const b
      simp only [zero_add] at hi0
      exact hi0.congr' (Eventually.of_forall fun x ↦ by ring)
    have hq := (hi.mul hInv).add_const m
    simp only [mul_zero, zero_add] at hq
    refine ⟨?_, hi⟩
    have heq : (fun x ↦ f x / x) =ᶠ[L] (fun x ↦ (f x - m * x) * x⁻¹ + m) := by
      filter_upwards [hNe] with x hx
      field_simp
      ring
    exact hq.congr' heq.symm
  · intro h
    have h0 := h.2.sub_const b
    simp only [sub_self] at h0
    exact h0.congr' (Eventually.of_forall fun x ↦ by ring)

/-- Định lí 4.4.24: tiêu chuẩn giới hạn của tiệm cận tại `+∞`. -/
theorem affine_residual_limit_atTop_iff (f : ℝ → ℝ) (m b : ℝ) :
    Tendsto (fun x ↦ f x - (m * x + b)) atTop (𝓝 0) ↔
      Tendsto (fun x ↦ f x / x) atTop (𝓝 m) ∧
        Tendsto (fun x ↦ f x - m * x) atTop (𝓝 b) :=
  affine_residual_limit_iff tendsto_inv_atTop_zero
    ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne') f m b

/-- Định lí 4.4.24: tiêu chuẩn giới hạn của tiệm cận tại `−∞`. -/
theorem affine_residual_limit_atBot_iff (f : ℝ → ℝ) (m b : ℝ) :
    Tendsto (fun x ↦ f x - (m * x + b)) atBot (𝓝 0) ↔
      Tendsto (fun x ↦ f x / x) atBot (𝓝 m) ∧
        Tendsto (fun x ↦ f x - m * x) atBot (𝓝 b) :=
  affine_residual_limit_iff tendsto_inv_atBot_zero
    ((eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne) f m b


theorem hasObliqueAsymptote_iff (f : ℝ → ℝ) (m b : ℝ) :
    HasObliqueAsymptote f m b ↔ m ≠ 0 ∧
      ((Tendsto (fun x ↦ f x / x) atTop (𝓝 m) ∧
          Tendsto (fun x ↦ f x - m * x) atTop (𝓝 b)) ∨
        (Tendsto (fun x ↦ f x / x) atBot (𝓝 m) ∧
          Tendsto (fun x ↦ f x - m * x) atBot (𝓝 b))) := by
  rw [HasObliqueAsymptote, affine_residual_limit_atTop_iff, affine_residual_limit_atBot_iff]

end calculus.Chapter04.Section04Asymptotes
