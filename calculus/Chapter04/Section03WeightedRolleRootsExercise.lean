import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bài 23: năm nghiệm của f và hai nghiệm của (1+2D)³f

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1188–1193.
-/
namespace calculus.Chapter04.Section03WeightedRolleRootsExercise
open Set calculus.Chapter04.Section01Higher


noncomputable def identityAddTwiceDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ := f x + 2 * deriv f x


theorem identityAddTwiceDerivative_root_between {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {a b : ℝ} (hab : a < b) (ha : f a = 0) (hb : f b = 0) :
    ∃ c ∈ Ioo a b, identityAddTwiceDerivative f c = 0 := by
  have hd (x : ℝ) : HasDerivAt (fun u : ℝ ↦ Real.exp (u / 2) * f u)
      (Real.exp (x / 2) / 2 * identityAddTwiceDerivative f x) x := by
    have h := (((hasDerivAt_id x).div_const 2).exp).fun_mul (hf x).hasDerivAt
    simp only [id_eq] at h
    apply h.congr_deriv
    unfold identityAddTwiceDerivative
    ring
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_zero hab
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hf.continuous).continuousOn
    (by
      change Real.exp (a / 2) * f a = Real.exp (b / 2) * f b
      simp only [ha, hb, mul_zero]) (fun x _ ↦ hd x)
  have hp : Real.exp (c / 2) / 2 ≠ 0 :=
    div_ne_zero (Real.exp_pos _).ne' (by norm_num)
  exact ⟨c, hc, (mul_eq_zero.mp he).resolve_left hp⟩


theorem identityAddTwiceDerivative_differentiable {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f)) :
    Differentiable ℝ (identityAddTwiceDerivative f) := hf.add (hdf.const_mul 2)


theorem identityAddTwiceDerivative_deriv {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f)) :
    deriv (identityAddTwiceDerivative f) = fun x ↦ deriv f x + 2 * deriv (deriv f) x := by
  funext x
  exact ((hf x).hasDerivAt.fun_add ((hdf x).hasDerivAt.const_mul 2)).deriv


theorem identityAddTwiceDerivative_twice {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f)) :
    identityAddTwiceDerivative (identityAddTwiceDerivative f) =
      fun x ↦ f x + 4 * deriv f x + 4 * deriv (deriv f) x := by
  funext x
  change identityAddTwiceDerivative f x + 2 * deriv (identityAddTwiceDerivative f) x = _
  rw [identityAddTwiceDerivative_deriv hf hdf]
  unfold identityAddTwiceDerivative
  ring


theorem identityAddTwiceDerivative_twice_deriv {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f))
    (hddf : Differentiable ℝ (deriv (deriv f))) :
    deriv (identityAddTwiceDerivative (identityAddTwiceDerivative f)) =
      fun x ↦ deriv f x + 4 * deriv (deriv f) x + 4 * deriv (deriv (deriv f)) x := by
  rw [identityAddTwiceDerivative_twice hf hdf]
  funext x
  exact (((hf x).hasDerivAt.fun_add ((hdf x).hasDerivAt.const_mul 4)).fun_add
    ((hddf x).hasDerivAt.const_mul 4)).deriv

/-- Bài 23: biểu thức sau ba lần áp dụng toán tử `1+2D`. -/
theorem identityAddTwiceDerivative_thrice {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f))
    (hddf : Differentiable ℝ (deriv (deriv f))) :
    identityAddTwiceDerivative (identityAddTwiceDerivative (identityAddTwiceDerivative f)) = fun x ↦
      f x + 6 * deriv f x + 12 * deriv (deriv f) x +
        8 * deriv (deriv (deriv f)) x := by
  funext x
  change identityAddTwiceDerivative (identityAddTwiceDerivative f) x +
    2 * deriv (identityAddTwiceDerivative (identityAddTwiceDerivative f)) x = _
  rw [identityAddTwiceDerivative_twice_deriv hf hdf hddf, identityAddTwiceDerivative_twice hf hdf]
  ring


theorem identityAddTwiceDerivative_thrice_has_two_roots_of_ordered {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f))
    (hddf : Differentiable ℝ (deriv (deriv f)))
    (r : Fin 5 → ℝ) (hr : StrictMono r) (hroots : ∀ i, f (r i) = 0) :
    ∃ u v : ℝ, u < v ∧
      f u + 6 * deriv f u + 12 * deriv (deriv f) u + 8 * deriv (deriv (deriv f)) u = 0 ∧
      f v + 6 * deriv f v + 12 * deriv (deriv f) v + 8 * deriv (deriv (deriv f)) v = 0 := by
  have hg1 : Differentiable ℝ (identityAddTwiceDerivative f) := identityAddTwiceDerivative_differentiable hf hdf
  have hdg1 : Differentiable ℝ (deriv (identityAddTwiceDerivative f)) := by
    rw [identityAddTwiceDerivative_deriv hf hdf]
    exact hdf.add (hddf.const_mul 2)
  have hg2 : Differentiable ℝ (identityAddTwiceDerivative (identityAddTwiceDerivative f)) :=
    identityAddTwiceDerivative_differentiable hg1 hdg1
  obtain ⟨z0, hz0, he0⟩ := identityAddTwiceDerivative_root_between hf
    (hr (by decide : (0 : Fin 5) < 1)) (hroots 0) (hroots 1)
  obtain ⟨z1, hz1, he1⟩ := identityAddTwiceDerivative_root_between hf
    (hr (by decide : (1 : Fin 5) < 2)) (hroots 1) (hroots 2)
  obtain ⟨z2, hz2, he2⟩ := identityAddTwiceDerivative_root_between hf
    (hr (by decide : (2 : Fin 5) < 3)) (hroots 2) (hroots 3)
  obtain ⟨z3, hz3, he3⟩ := identityAddTwiceDerivative_root_between hf
    (hr (by decide : (3 : Fin 5) < 4)) (hroots 3) (hroots 4)
  obtain ⟨t0, ht0, hte0⟩ := identityAddTwiceDerivative_root_between hg1
    (hz0.2.trans hz1.1) he0 he1
  obtain ⟨t1, ht1, hte1⟩ := identityAddTwiceDerivative_root_between hg1
    (hz1.2.trans hz2.1) he1 he2
  obtain ⟨t2, ht2, hte2⟩ := identityAddTwiceDerivative_root_between hg1
    (hz2.2.trans hz3.1) he2 he3
  obtain ⟨u, hu, hue⟩ := identityAddTwiceDerivative_root_between hg2
    (ht0.2.trans ht1.1) hte0 hte1
  obtain ⟨v, hv, hve⟩ := identityAddTwiceDerivative_root_between hg2
    (ht1.2.trans ht2.1) hte1 hte2
  refine ⟨u, v, hu.2.trans hv.1, ?_, ?_⟩
  · simpa only [identityAddTwiceDerivative_thrice hf hdf hddf] using hue
  · simpa only [identityAddTwiceDerivative_thrice hf hdf hddf] using hve

/-- Bài 23: năm nghiệm phân biệt của hàm cho hai nghiệm phân biệt của tổ hợp đạo hàm cấp ba. -/
theorem identityAddTwiceDerivative_thrice_has_two_distinct_roots {f : ℝ → ℝ}
    (hf : DifferentiableToOrderOn 3 f univ)
    (hroots : ∃ s : Finset ℝ, s.card = 5 ∧ ∀ x ∈ s, f x = 0) :
    ∃ u v : ℝ, u < v ∧
      f u + 6 * deriv f u + 12 * deriv (deriv f) u + 8 * deriv (deriv (deriv f)) u = 0 ∧
      f v + 6 * deriv f v + 12 * deriv (deriv f) v + 8 * deriv (deriv (deriv f)) v = 0 := by
  classical
  have hfirst : Differentiable ℝ f := by
    simpa only [iteratedDerivWithin_zero, differentiableOn_univ] using hf 0 (by decide)
  have hsecond : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDerivWithin_univ, iteratedDeriv_one, differentiableOn_univ] using
      hf 1 (by decide)
  have hthird : Differentiable ℝ (deriv (deriv f)) := by
    have hh := hf 2 (by decide)
    rw [iteratedDerivWithin_univ, show (2 : ℕ) = 1 + 1 from rfl,
      iteratedDeriv_succ, iteratedDeriv_one] at hh
    exact differentiableOn_univ.mp hh
  obtain ⟨s, hs, hz⟩ := hroots
  let r : Fin 5 ↪o ℝ := s.orderEmbOfFin hs
  exact identityAddTwiceDerivative_thrice_has_two_roots_of_ordered hfirst hsecond hthird r r.strictMono
    (fun i ↦ hz (r i) (s.orderEmbOfFin_mem hs i))

end calculus.Chapter04.Section03WeightedRolleRootsExercise
