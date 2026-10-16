import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bài tập 4.3.22: các số mũ thỏa điều kiện là k<1

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1183–1185. `N` được chọn sau `f` và `k`; đối số `x` là số thực.
-/
namespace calculus.Chapter04.Section03GrowthExercise
open Set


def HasUniversalExponentialLowerBound (k : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Differentiable ℝ f → (∀ x, 0 < f x) → (∀ x, f x < deriv f x) →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x : ℝ, (N : ℝ) < x → Real.exp (k * x) < f x


theorem integrating_factor_strictMono {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hp : ∀ x, f x < deriv f x) : StrictMono (fun x ↦ f x * Real.exp (-x)) := by
  apply strictMono_of_deriv_pos
  intro x
  have hd := (hf x).hasDerivAt.fun_mul ((hasDerivAt_id x).neg.exp)
  simp only [Pi.neg_apply, id_eq] at hd
  rw [hd.deriv]
  have hpos := mul_pos (Real.exp_pos (-x)) (sub_pos.mpr (hp x))
  nlinarith


theorem universal_lower_bound_of_lt_one {k : ℝ} (hk : k < 1) :
    HasUniversalExponentialLowerBound k := by
  intro f hf hp hder
  have hdelta : 0 < 1 - k := sub_pos.mpr hk
  obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log (f 0) / (1 - k))
  refine ⟨N + 1, by omega, ?_⟩
  intro x hx
  have hn : -Real.log (f 0) / (1 - k) < ((N + 1 : ℕ) : ℝ) := by
    have hstep : (N : ℝ) < ((N + 1 : ℕ) : ℝ) := by norm_num
    exact hN.trans hstep
  have hxpos : 0 < x := by
    have hnpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    norm_num only [Nat.cast_add, Nat.cast_one] at hx
    linarith
  have hgap := (div_lt_iff₀ hdelta).mp (hn.trans hx)
  have hexp : Real.exp (k * x) < f 0 * Real.exp x := by
    have hlt : k * x < Real.log (f 0) + x := by nlinarith
    have he := Real.exp_strictMono hlt
    simpa only [Real.exp_add, Real.exp_log (hp 0)] using he
  have hg := (integrating_factor_strictMono hf hder) hxpos
  have hlower : f 0 * Real.exp x < f x := by
    simp only [neg_zero, Real.exp_zero, mul_one] at hg
    have hh := mul_lt_mul_of_pos_right hg (Real.exp_pos x)
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hh
    exact hh
  exact hexp.trans hlower


noncomputable def exponentialLowerBoundCounterexample (x : ℝ) : ℝ :=
  Real.exp x * Real.exp (-Real.exp (-x))

theorem exponentialLowerBoundCounterexample_hasDerivAt (x : ℝ) :
    HasDerivAt exponentialLowerBoundCounterexample
      (exponentialLowerBoundCounterexample x * (1 + Real.exp (-x))) x := by
  have hd := (Real.hasDerivAt_exp x).fun_mul (((hasDerivAt_id x).neg.exp).neg.exp)
  apply hd.congr_deriv
  unfold exponentialLowerBoundCounterexample
  simp only [Pi.neg_apply, id_eq]
  ring

theorem exponentialLowerBoundCounterexample_positive (x : ℝ) : 0 < exponentialLowerBoundCounterexample x :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

theorem exponentialLowerBoundCounterexample_derivative_gt (x : ℝ) :
    exponentialLowerBoundCounterexample x < deriv exponentialLowerBoundCounterexample x := by
  rw [(exponentialLowerBoundCounterexample_hasDerivAt x).deriv]
  nlinarith [exponentialLowerBoundCounterexample_positive x, Real.exp_pos (-x)]

theorem exponentialLowerBoundCounterexample_lt_exp (x : ℝ) : exponentialLowerBoundCounterexample x < Real.exp x := by
  have hs : Real.exp (-Real.exp (-x)) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_strictMono (neg_lt_zero.mpr (Real.exp_pos (-x)))
  unfold exponentialLowerBoundCounterexample
  simpa only [mul_one] using mul_lt_mul_of_pos_left hs (Real.exp_pos x)


theorem not_universal_lower_bound_of_one_le {k : ℝ} (hk : 1 ≤ k) :
    ¬HasUniversalExponentialLowerBound k := by
  intro h
  obtain ⟨N, _, hN⟩ := h exponentialLowerBoundCounterexample
    (fun x ↦ (exponentialLowerBoundCounterexample_hasDerivAt x).differentiableAt)
    exponentialLowerBoundCounterexample_positive exponentialLowerBoundCounterexample_derivative_gt
  let x : ℝ := (N : ℝ) + 1
  have hx : (N : ℝ) < x := by dsimp [x]; linarith
  have hxpos : 0 < x := by dsimp [x]; positivity
  have he : Real.exp x ≤ Real.exp (k * x) :=
    Real.exp_monotone (by nlinarith)
  exact (hN x hx).not_ge ((exponentialLowerBoundCounterexample_lt_exp x).le.trans he)


theorem universal_lower_bound_iff (k : ℝ) : HasUniversalExponentialLowerBound k ↔ k < 1 := by
  constructor
  · intro h
    by_contra hk
    exact not_universal_lower_bound_of_one_le (le_of_not_gt hk) h
  · exact universal_lower_bound_of_lt_one

end calculus.Chapter04.Section03GrowthExercise
