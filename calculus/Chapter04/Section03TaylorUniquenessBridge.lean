import calculus.Chapter04.Section03Taylor
import calculus.Chapter04.Section03TaylorUniqueness

/-!
# Nhận xét 4.3.12: hệ số Taylor được xác định duy nhất

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1257–1263.
-/
namespace calculus.Chapter04.Section03TaylorUniquenessBridge
open Set Filter calculus.Chapter04.Section03Taylor
open calculus.Chapter04.Section03TaylorUniqueness
open calculus.Chapter04.Section01HigherClosed
open scoped Topology


theorem taylorPolynomialWithin_eq_powerPolynomial (n : ℕ) (f : ℝ → ℝ)
    (I : Set ℝ) (x₀ x : ℝ) :
    taylorPolynomialWithin n f I x₀ x =
      powerPolynomial (fun k ↦ iteratedDerivWithin k f I x₀ / (k.factorial : ℝ))
        n (x - x₀) := rfl


theorem source_taylor_coefficients_unique {n : ℕ} {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval n f a b)
    (hc : ContinuousOn (iteratedDerivWithin n f (Icc a b)) (Icc a b))
    (hx₀ : x₀ ∈ Icc a b) (coeff : ℕ → ℝ)
    (hcoeff : (fun x ↦ f x - powerPolynomial coeff n (x - x₀))
      =o[𝓝[Icc a b] x₀] (fun x ↦ (x - x₀) ^ n)) :
    ∀ k ≤ n, coeff k = iteratedDerivWithin k f (Icc a b) x₀ / (k.factorial : ℝ) := by
  apply coefficients_eq_on_closed_interval hf.1 hx₀ n coeff _ hcoeff
  simpa only [taylorPolynomialWithin_eq_powerPolynomial] using source_taylor_peano hf hc hx₀

/-- Nhận xét 4.3.12: phần dư Peano của khai triển Taylor bậc `n`. -/
theorem source_taylor_remainder_peano (n : ℕ) (_hn : 1 ≤ n) {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval n f a b)
    (hc : ContinuousOn (iteratedDerivWithin n f (Icc a b)) (Icc a b))
    (_hnext : calculus.Chapter04.Section01Higher.DifferentiableToOrderOn (n + 1) f (Ioo a b))
    (hx₀ : x₀ ∈ Icc a b) :
    (fun x ↦ f x - taylorPolynomialWithin n f (Icc a b) x₀ x)
      =o[𝓝[Icc a b] x₀] (fun x ↦ (x - x₀) ^ n) :=
  source_taylor_peano hf hc hx₀

/-- Nhận xét 4.3.12: hệ số khai triển bằng giá trị đạo hàm chia giai thừa. -/
theorem source_taylor_coefficients (n : ℕ) (_hn : 1 ≤ n) {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval n f a b)
    (hc : ContinuousOn (iteratedDerivWithin n f (Icc a b)) (Icc a b))
    (_hnext : calculus.Chapter04.Section01Higher.DifferentiableToOrderOn (n + 1) f (Ioo a b))
    (hx₀ : x₀ ∈ Icc a b) (coeff : ℕ → ℝ)
    (hcoeff : (fun x ↦ f x - powerPolynomial coeff n (x - x₀))
      =o[𝓝[Icc a b] x₀] (fun x ↦ (x - x₀) ^ n)) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      coeff k = iteratedDerivWithin k f (Icc a b) x₀ / (k.factorial : ℝ) := by
  intro k _hk hkn
  exact source_taylor_coefficients_unique hf hc hx₀ coeff hcoeff k hkn

end calculus.Chapter04.Section03TaylorUniquenessBridge
