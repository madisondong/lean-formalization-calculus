import calculus.Chapter04.Section03
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Bài tập 4.3.21: giá trị đạo hàm không bằng hệ số góc cát tuyến

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1180–1181. Điểm `c` được cố định trước `a, b`; không cần `f″` liên tục.
-/
namespace calculus.Chapter04.Section03MissingSecantExercise
open Filter

/-- Bài 21: không có cát tuyến mang hệ số góc `f′(c)` thì `f″(c) = 0`. -/
theorem second_derivative_zero_of_missing_secant {f : ℝ → ℝ} {c : ℝ}
    (hf : Differentiable ℝ f) (hff : Differentiable ℝ (deriv f))
    (hno : ∀ a b : ℝ, a ≠ b → (f b - f a) / (b - a) ≠ deriv f c) :
    deriv (deriv f) c = 0 := by
  let H : ℝ → ℝ := fun x ↦ f x - deriv f c * x
  have hi : Function.Injective H := by
    intro a b he
    by_contra hne
    apply hno a b hne
    apply (div_eq_iff (sub_ne_zero.mpr (Ne.symm hne))).mpr
    dsimp [H] at he
    nlinarith [he]
  have hc : Continuous H := hf.continuous.sub (continuous_const.mul continuous_id)
  have hd (x : ℝ) : deriv H x = deriv f x - deriv f c := by
    have hh := (hf x).hasDerivAt.fun_sub ((hasDerivAt_id x).const_mul (deriv f c))
    simpa only [H, mul_one, id_eq] using hh.deriv
  rcases hc.strictMono_of_inj hi with hm | hm
  · have hmin : IsLocalMin (deriv f) c := by
      apply Eventually.of_forall
      intro x
      have hh := hm.monotone.deriv_nonneg (x := x)
      rw [hd] at hh
      exact sub_nonneg.mp hh
    exact hmin.hasDerivAt_eq_zero (hff c).hasDerivAt
  · have hmax : IsLocalMax (deriv f) c := by
      apply Eventually.of_forall
      intro x
      have hh := hm.antitone.deriv_nonpos (x := x)
      rw [hd] at hh
      exact sub_nonpos.mp hh
    exact hmax.hasDerivAt_eq_zero (hff c).hasDerivAt

end calculus.Chapter04.Section03MissingSecantExercise
