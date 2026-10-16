import calculus.Chapter04.Section01Higher
import calculus.Chapter04.Section01Parametric

/-!
# Đạo hàm cấp hai theo tham số

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 807. Mẫu số là `φ′(t)³`, với `φ′(t) ≠ 0`.
-/
namespace calculus.Chapter04.Section02ParametricRepair
open Set Filter calculus.Chapter04.Section01Higher calculus.Chapter04.Section01Parametric
open scoped Topology


theorem parametric_second_derivative {φ ψ g : ℝ → ℝ} {a b : ℝ}
    (hφ : DifferentiableToOrderOn 2 φ (Ioo a b))
    (hψ : DifferentiableToOrderOn 2 ψ (Ioo a b))
    (hgf : LeftInvOn g φ (Ioo a b))
    (hφne : ∀ t ∈ Ioo a b, deriv φ t ≠ 0) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (deriv (ψ ∘ g))
      ((deriv φ t * deriv (deriv ψ) t - deriv (deriv φ) t * deriv ψ t) /
        (deriv φ t) ^ 3) (φ t) := by
  obtain ⟨hφ0, hφ1⟩ := (differentiableToOrderOn_two φ isOpen_Ioo).mp hφ
  obtain ⟨hψ0, hψ1⟩ := (differentiableToOrderOn_two ψ isOpen_Ioo).mp hψ
  have hdφ := ((hφ1 t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have hdψ := ((hψ1 t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have hratio := hdψ.div hdφ (hφne t ht)
  have hratio' : HasDerivAt (fun u ↦ deriv ψ u / deriv φ u)
      ((deriv (deriv ψ) t * deriv φ t - deriv ψ t * deriv (deriv φ) t) /
        (deriv φ t) ^ 2) (g (φ t)) := by
    rw [hgf ht]
    exact hratio
  have hg := parametric_inverse_hasDerivAt hφ0 hgf ht (hφne t ht)
  have hc := hratio'.comp (φ t) hg
  have hc' : HasDerivAt ((fun u ↦ deriv ψ u / deriv φ u) ∘ g)
      ((deriv φ t * deriv (deriv ψ) t - deriv (deriv φ) t * deriv ψ t) /
        (deriv φ t) ^ 3) (φ t) := by
    apply hc.congr_deriv
    field_simp
  apply hc'.congr_of_eventuallyEq
  have hinj : InjOn φ (Ioo a b) := by
    intro u hu v hv he
    have := congrArg g he
    simpa only [hgf hu, hgf hv] using this
  filter_upwards [interval_image_mem_nhds ht hφ0.continuousOn hinj] with x hx
  obtain ⟨u, hu, rfl⟩ := hx
  simpa only [Function.comp_apply, hgf hu] using
    (parametric_derivative hφ0 hψ0 hgf hφne hu).deriv

end calculus.Chapter04.Section02ParametricRepair
