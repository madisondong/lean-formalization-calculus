import calculus.Chapter04.Section02
import calculus.Chapter04.Section01Higher

/-!
# 4.2.4: vi phân cấp cao và đổi biến

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 776–805. Giữ số gia `h` cố định qua các cấp.
-/
namespace calculus.Chapter04.Section02Higher
open Set Filter calculus.Chapter04.Section01Higher calculus.Chapter04.Section02
open scoped Topology


noncomputable def higherDifferential (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) (x h : ℝ) : ℝ :=
  iteratedDerivWithin n f I x * h ^ n


theorem higherDifferential_one {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x : ℝ} (hx : x ∈ I) (h : ℝ) :
    higherDifferential 1 f I x h = firstDifferential f x h := by
  simp only [higherDifferential, iteratedDerivWithin_one, derivWithin_of_isOpen hI hx,
    pow_one, firstDifferential]


theorem higherDifferential_succ (n : ℕ) {f : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hf : DifferentiableToOrderOn (n + 1) f I)
    {x : ℝ} (hx : x ∈ I) (h : ℝ) :
    firstDifferential (fun y ↦ higherDifferential n f I y h) x h =
      higherDifferential (n + 1) f I x h := by
  have hd := ((hf n (Nat.lt_succ_self n)) x hx).differentiableAt (hI.mem_nhds hx)
  unfold firstDifferential higherDifferential
  rw [(hd.hasDerivAt.mul_const (h ^ n)).deriv, iteratedDerivWithin_succ,
    derivWithin_of_isOpen hI hx, pow_succ]
  ring

/-- Vi phân cấp `n` bằng đạo hàm cấp `n` nhân `hⁿ`. -/
theorem higherDifferential_positive_order (n : ℕ) (_hn : 1 ≤ n)
    (f : ℝ → ℝ) (I : Set ℝ) (x h : ℝ) :
    higherDifferential n f I x h = iteratedDerivWithin n f I x * h ^ n := rfl


theorem derivative_from_higherDifferential (n : ℕ) {f : ℝ → ℝ} {I : Set ℝ}
    {x h : ℝ} (hh : h ≠ 0) :
    higherDifferential n f I x h / h ^ n = iteratedDerivWithin n f I x := by
  exact mul_div_cancel_right₀ _ (pow_ne_zero n hh)


theorem second_derivative_comp {f φ : ℝ → ℝ} {I J : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) (hf : DifferentiableToOrderOn 2 f I)
    (hφ : DifferentiableToOrderOn 2 φ J) (hmap : MapsTo φ J I)
    {t : ℝ} (ht : t ∈ J) :
    deriv (deriv (f ∘ φ)) t =
      deriv (deriv f) (φ t) * (deriv φ t) ^ 2 + deriv f (φ t) * deriv (deriv φ) t := by
  obtain ⟨hf0, hf1⟩ := (differentiableToOrderOn_two f hI).mp hf
  obtain ⟨hφ0, hφ1⟩ := (differentiableToOrderOn_two φ hJ).mp hφ
  have hdφ := (hφ0 t ht).differentiableAt (hJ.mem_nhds ht)
  have hddφ := (hφ1 t ht).differentiableAt (hJ.mem_nhds ht)
  have hddf := (hf1 (φ t) (hmap ht)).differentiableAt (hI.mem_nhds (hmap ht))
  have he : deriv (f ∘ φ) =ᶠ[𝓝 t] (fun u ↦ deriv f (φ u) * deriv φ u) := by
    filter_upwards [hJ.mem_nhds ht] with u hu
    exact deriv_comp u ((hf0 (φ u) (hmap hu)).differentiableAt (hI.mem_nhds (hmap hu)))
      ((hφ0 u hu).differentiableAt (hJ.mem_nhds hu))
  have hc := (hddf.hasDerivAt.comp t hdφ.hasDerivAt).fun_mul hddφ.hasDerivAt
  rw [he.deriv_eq]
  have hv : deriv (fun u ↦ deriv f (φ u) * deriv φ u) t =
      (deriv (deriv f) (φ t) * deriv φ t) * deriv φ t +
        deriv f (φ t) * deriv (deriv φ) t := by
    simpa only [Function.comp_apply] using hc.deriv
  rw [hv]
  ring


theorem secondDifferential_comp {f φ : ℝ → ℝ} {I J : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) (hf : DifferentiableToOrderOn 2 f I)
    (hφ : DifferentiableToOrderOn 2 φ J) (hmap : MapsTo φ J I)
    {t : ℝ} (ht : t ∈ J) (h : ℝ) :
    higherDifferential 2 (f ∘ φ) J t h =
      deriv (deriv f) (φ t) * (firstDifferential φ t h) ^ 2 +
        deriv f (φ t) * higherDifferential 2 φ J t h := by
  simp only [higherDifferential, iteratedDerivWithin_of_isOpen hJ ht,
    iteratedDeriv_succ, iteratedDeriv_zero, firstDifferential]
  rw [second_derivative_comp hI hJ hf hφ hmap ht]
  ring


theorem higherDifferential_not_invariant (n : ℕ) (hn : 2 ≤ n) :
    higherDifferential n (fun t : ℝ ↦ t ^ n) univ 1 1 ≠
      higherDifferential n (fun x : ℝ ↦ x) univ 1 (n : ℝ) := by
  simp only [higherDifferential, iteratedDerivWithin_univ, one_pow, mul_one]
  rw [pow_iteratedDeriv_at_degree]
  have hid : (fun x : ℝ ↦ x) = (fun x : ℝ ↦ x ^ (1 : ℕ)) := by funext x; simp
  rw [hid, pow_iteratedDeriv_above_degree 1 n 1 (by omega), zero_mul]
  exact_mod_cast Nat.factorial_ne_zero n

end calculus.Chapter04.Section02Higher
