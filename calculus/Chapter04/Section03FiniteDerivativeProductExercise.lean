import calculus.Chapter04.Section03
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# §4.3, Bài 16: tích các đạo hàm tại những điểm phân biệt

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1162–1163.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section03FiniteDerivativeProductExercise
open Set Filter
open scoped Topology BigOperators
open calculus.Chapter04.Section03


theorem derivative_one_of_ge {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (hd : DifferentiableOn ℝ f (Ioo 0 1))
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hg : ∀ x ∈ Ioo 0 1, 1 ≤ deriv f x) :
    ∀ x ∈ Ioo 0 1, deriv f x = 1 := by
  have hdc (x : ℝ) (hx : x ∈ Ioo 0 1) :
      deriv (fun y : ℝ ↦ f y - y) x = deriv f x - 1 := by
    exact (((hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.sub
      (hasDerivAt_id x)).deriv
  have hm : MonotoneOn (fun y : ℝ ↦ f y - y) (Icc 0 1) :=
    monotoneOn_of_nonnegative_derivative (hc.sub continuousOn_id)
      (hd.sub differentiableOn_id) (fun x hx ↦ by rw [hdc x hx]; linarith [hg x hx])
  have he : EqOn f (fun y : ℝ ↦ y) (Ioo 0 1) := by
    intro x hx
    have hl := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) (Ioo_subset_Icc_self hx) hx.1.le
    have hu := hm (Ioo_subset_Icc_self hx) (by norm_num : (1 : ℝ) ∈ Icc 0 1) hx.2.le
    simp only [h0, h1, sub_self] at hl hu
    linarith
  intro x hx
  simpa only [deriv_id''] using he.deriv isOpen_Ioo hx


theorem derivative_one_of_le {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (hd : DifferentiableOn ℝ f (Ioo 0 1))
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hg : ∀ x ∈ Ioo 0 1, deriv f x ≤ 1) :
    ∀ x ∈ Ioo 0 1, deriv f x = 1 := by
  have hdc (x : ℝ) (hx : x ∈ Ioo 0 1) :
      deriv (fun y : ℝ ↦ f y - y) x = deriv f x - 1 := by
    exact (((hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.sub
      (hasDerivAt_id x)).deriv
  have hm : AntitoneOn (fun y : ℝ ↦ f y - y) (Icc 0 1) :=
    antitoneOn_of_nonpositive_derivative (hc.sub continuousOn_id)
      (hd.sub differentiableOn_id) (fun x hx ↦ by rw [hdc x hx]; linarith [hg x hx])
  have he : EqOn f (fun y : ℝ ↦ y) (Ioo 0 1) := by
    intro x hx
    have hu := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) (Ioo_subset_Icc_self hx) hx.1.le
    have hl := hm (Ioo_subset_Icc_self hx) (by norm_num : (1 : ℝ) ∈ Icc 0 1) hx.2.le
    simp only [h0, h1, sub_self] at hl hu
    linarith
  intro x hx
  simpa only [deriv_id''] using he.deriv isOpen_Ioo hx


theorem finite_positive_targets (n : ℕ) (hn : 0 < n) {l u : ℝ}
    (hl : l < 1) (hu : 1 < u) :
    ∃ v : Fin n → ℝ, Function.Injective v ∧
      (∀ i, v i ∈ Ioo l u) ∧ ∏ i, v i = 1 := by
  classical
  let A : ℝ := (∑ i : Fin n, (i.val : ℝ)) / (n : ℝ)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ i : Fin n, Real.exp (ε * ((i.val : ℝ) - A)) ∈ Ioo l u := by
    rw [Filter.eventually_all]
    intro i
    have ht : Tendsto (fun ε : ℝ ↦ Real.exp (ε * ((i.val : ℝ) - A)))
        (𝓝 0) (𝓝 1) := by
      simpa only [Function.comp_def, id_eq, zero_mul, Real.exp_zero] using
        (Real.continuous_exp.continuousAt.comp
          ((continuousAt_id (x := (0 : ℝ))).mul_const ((i.val : ℝ) - A))).tendsto
    exact ht.eventually (Ioo_mem_nhds hl hu)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε : ℝ := δ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hv : ∀ i : Fin n, Real.exp (ε * ((i.val : ℝ) - A)) ∈ Ioo l u := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp [ε]
    linarith
  refine ⟨fun i ↦ Real.exp (ε * ((i.val : ℝ) - A)), ?_, hv, ?_⟩
  · intro i j hij
    have he := Real.exp_injective hij
    have hijR : (i.val : ℝ) = (j.val : ℝ) := by nlinarith
    apply Fin.ext
    exact_mod_cast hijR
  · have hs : (∑ i : Fin n, ((i.val : ℝ) - A)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      dsimp [A]
      rw [mul_div_cancel₀ _ hnR, sub_self]
    rw [← Real.exp_sum, ← Finset.mul_sum, hs, mul_zero, Real.exp_zero]

/-- Bài 16: với mỗi `n`, có `n` điểm phân biệt trong `(0, 1)` sao cho tích các đạo hàm bằng 1. -/
theorem source_finite_derivative_product {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (hd : DifferentiableOn ℝ f (Ioo 0 1))
    (h0 : f 0 = 0) (h1 : f 1 = 1) (n : ℕ) (hn : 0 < n) :
    ∃ c : Fin n → ℝ, Function.Injective c ∧
      (∀ i, c i ∈ Ioo 0 1) ∧ ∏ i, deriv f (c i) = 1 := by
  classical
  by_cases hall : ∀ x ∈ Ioo 0 1, deriv f x = 1
  · let c : Fin n → ℝ := fun i ↦ ((i.val : ℝ) + 1) / ((n : ℝ) + 1)
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hcm (i : Fin n) : c i ∈ Ioo 0 1 := by
      have hi : (i.val : ℝ) < (n : ℝ) := by exact_mod_cast i.isLt
      dsimp [c]
      constructor
      · apply div_pos _ hden
        positivity
      · rw [div_lt_one hden]
        linarith
    refine ⟨c, ?_, hcm, ?_⟩
    · intro i j hij
      have he : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 := by
        calc
          _ = c i * ((n : ℝ) + 1) := (div_mul_cancel₀ _ hden.ne').symm
          _ = c j * ((n : ℝ) + 1) := congrArg (fun z : ℝ ↦ z * ((n : ℝ) + 1)) hij
          _ = _ := div_mul_cancel₀ _ hden.ne'
      apply Fin.ext
      exact_mod_cast (add_right_cancel he)
    · simp only [hall _ (hcm _), Finset.prod_const_one]
  · have hlo : ∃ a ∈ Ioo (0 : ℝ) 1, deriv f a < 1 := by
      by_contra h
      push Not at h
      exact hall (derivative_one_of_ge hc hd h0 h1 h)
    have hhi : ∃ b ∈ Ioo (0 : ℝ) 1, 1 < deriv f b := by
      by_contra h
      push Not at h
      exact hall (derivative_one_of_le hc hd h0 h1 h)
    obtain ⟨a, ha, hal⟩ := hlo
    obtain ⟨b, hb, hbu⟩ := hhi
    obtain ⟨v, hvInjective, hvRange, hvProduct⟩ := finite_positive_targets n hn hal hbu
    have hDar : OrdConnected (deriv f '' Ioo 0 1) :=
      ordConnected_Ioo.image_deriv
        (fun x hx ↦ (hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx))
    have hw (i : Fin n) : ∃ c ∈ Ioo (0 : ℝ) 1, deriv f c = v i := by
      exact hDar.out (mem_image_of_mem (deriv f) ha)
        (mem_image_of_mem (deriv f) hb) (Ioo_subset_Icc_self (hvRange i))
    choose c hcRange hcDeriv using hw
    refine ⟨c, ?_, hcRange, ?_⟩
    · intro i j hij
      apply hvInjective
      rw [← hcDeriv i, ← hcDeriv j, hij]
    · simpa only [hcDeriv] using hvProduct

end calculus.Chapter04.Section03FiniteDerivativeProductExercise
