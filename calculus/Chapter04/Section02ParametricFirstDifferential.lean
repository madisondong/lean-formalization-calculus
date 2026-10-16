import calculus.Chapter04.Section01Parametric
import calculus.Chapter04.Section02

/-!
# §4.2: vi phân theo tham số

Nguồn: công thức dòng 805, `y′ₓ = dy/dx = ψ′(t)/φ′(t)`. Công thức thương yêu cầu `φ′(t) ≠ 0` và `dt ≠ 0`.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter04.Section02ParametricFirstDifferential
open calculus.Chapter04.Section01Parametric calculus.Chapter04.Section02


theorem coordinate_differential_ratio (A B dt : ℝ) (hA : A ≠ 0) (hdt : dt ≠ 0) :
    (B * dt) / (A * dt) = B / A := by
  field_simp


theorem source_parametric_first_differential_formula {φ ψ g : ℝ → ℝ} {a b : ℝ}
    (hφ : DifferentiableOn ℝ φ (Ioo a b)) (hψ : DifferentiableOn ℝ ψ (Ioo a b))
    (hgf : LeftInvOn g φ (Ioo a b)) (hφne : ∀ t ∈ Ioo a b, deriv φ t ≠ 0)
    {t dt : ℝ} (ht : t ∈ Ioo a b) (hdt : dt ≠ 0) :
    ψ (g (φ t)) = ψ t ∧
      HasDerivAt (ψ ∘ g) (deriv ψ t / deriv φ t) (φ t) ∧
      firstDifferential φ t dt ≠ 0 ∧
      deriv (ψ ∘ g) (φ t) = firstDifferential ψ t dt / firstDifferential φ t dt ∧
      firstDifferential ψ t dt / firstDifferential φ t dt = deriv ψ t / deriv φ t := by
  have hd := parametric_derivative hφ hψ hgf hφne ht
  have hr : firstDifferential ψ t dt / firstDifferential φ t dt =
      deriv ψ t / deriv φ t := coordinate_differential_ratio _ _ _ (hφne t ht) hdt
  exact ⟨parametric_graph_relation hgf ht, hd,
    mul_ne_zero (hφne t ht) hdt, hd.deriv.trans hr.symm, hr⟩

end calculus.Chapter04.Section02ParametricFirstDifferential
