import calculus.Chapter04.Section01HigherClosed
import Mathlib.Analysis.Calculus.Taylor

/-!
# 4.3.10: công thức Taylor

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1203–1236. Đạo hàm cấp `n` liên tục trên đoạn, đạo hàm cấp `n+1` tồn tại trong nội khoảng; đầu mút dùng đạo hàm một bên.
-/
namespace calculus.Chapter04.Section03Taylor
open Set Filter calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section01HigherClosed calculus.Chapter04.Section01Derivatives
open scoped Topology BigOperators


theorem iteratedDerivWithin_Icc_interior (n : ℕ) (f : ℝ → ℝ) {a b x : ℝ}
    (hx : x ∈ Ioo a b) : iteratedDerivWithin n f (Icc a b) x = iteratedDeriv n f x := by
  unfold iteratedDerivWithin iteratedDeriv
  rw [iteratedFDerivWithin_congr_set (Filter.eventuallyEq_univ.mpr
    (Icc_mem_nhds hx.1 hx.2)) n, iteratedFDerivWithin_univ]


theorem iteratedDerivWithin_uIcc_interior (n : ℕ) (f : ℝ → ℝ) {a b x : ℝ}
    (hx : x ∈ uIoo a b) : iteratedDerivWithin n f (uIcc a b) x = iteratedDeriv n f x :=
  iteratedDerivWithin_Icc_interior n f hx


theorem right_order_mono {k n : ℕ} (hkn : k ≤ n) {f : ℝ → ℝ} {a b : ℝ}
    (h : HasRightDerivativesUpToOrder n f a b) : HasRightDerivativesUpToOrder k f a b := by
  induction n with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      trivial
  | succ n ih =>
    by_cases hk : k ≤ n
    · exact ih hk h.1
    · have he : k = n + 1 := by omega
      simpa only [he] using h


theorem left_order_mono {k n : ℕ} (hkn : k ≤ n) {f : ℝ → ℝ} {a b : ℝ}
    (h : HasLeftDerivativesUpToOrder n f a b) : HasLeftDerivativesUpToOrder k f a b := by
  induction n with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      trivial
  | succ n ih =>
    by_cases hk : k ≤ n
    · exact ih hk h.1
    · have he : k = n + 1 := by omega
      simpa only [he] using h


theorem source_closed_to_within {n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval n f a b) :
    DifferentiableToOrderOn n f (Icc a b) := by
  intro k hk x hx
  have hab := hf.1
  rcases eq_or_lt_of_le hx.1 with hax | hax
  · subst x
    obtain ⟨L, hL⟩ := (right_order_mono (Nat.succ_le_of_lt hk) hf.2.2.1).2
    have hs : HasDerivativeWithinAt (iteratedDerivWithin k f (Icc a b)) (Icc a b) a L := by
      simpa only [HasDerivativeWithinAt, Icc_sdiff_left, nhdsWithin_Ioc_eq_nhdsGT hab,
        nhdsWithin_Ioo_eq_nhdsGT hab] using hL
    exact ((hasDerivativeWithinAt_iff_hasDerivWithinAt _ _ _ _).mp hs).differentiableWithinAt
  · rcases eq_or_lt_of_le hx.2 with hxb | hxb
    · subst x
      obtain ⟨L, hL⟩ := (left_order_mono (Nat.succ_le_of_lt hk) hf.2.2.2).2
      have hs : HasDerivativeWithinAt (iteratedDerivWithin k f (Icc a b)) (Icc a b) b L := by
        simpa only [HasDerivativeWithinAt, Icc_sdiff_right, nhdsWithin_Ico_eq_nhdsLT hab,
          nhdsWithin_Ioo_eq_nhdsLT hab] using hL
      exact ((hasDerivativeWithinAt_iff_hasDerivWithinAt _ _ _ _).mp hs).differentiableWithinAt
    · have he : EqOn (iteratedDerivWithin k f (Icc a b))
          (iteratedDerivWithin k f (Ioo a b)) (Ioo a b) := by
        intro y hy
        rw [iteratedDerivWithin_Icc_interior k f hy, iteratedDerivWithin_of_isOpen isOpen_Ioo hy]
      exact (((hf.2.1 k hk).congr he) x ⟨hax, hxb⟩).differentiableAt
        (isOpen_Ioo.mem_nhds ⟨hax, hxb⟩) |>.differentiableWithinAt


theorem source_closed_contDiffOn {n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval n f a b)
    (hc : ContinuousOn (iteratedDerivWithin n f (Icc a b)) (Icc a b)) :
    ContDiffOn ℝ n f (Icc a b) := by
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (uniqueDiffOn_Icc hf.1)]
  have hd := source_closed_to_within hf
  refine ⟨?_, hd⟩
  intro k hk
  by_cases hkn : k < n
  · exact (hd k hkn).continuousOn
  · have he : k = n := by omega
    simpa only [he] using hc


noncomputable def taylorPolynomialWithin (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ)
    (x₀ x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), iteratedDerivWithin k f I x₀ / (k.factorial : ℝ) * (x - x₀) ^ k


theorem taylorPolynomialWithin_eq_taylorWithin (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ)
    (x₀ x : ℝ) : taylorPolynomialWithin n f I x₀ x = taylorWithinEval f n I x₀ x := by
  rw [taylorPolynomialWithin, taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring


theorem taylorPolynomialWithin_self (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) (x₀ : ℝ) :
    taylorPolynomialWithin n f I x₀ x₀ = f x₀ := by
  rw [taylorPolynomialWithin_eq_taylorWithin, taylorWithinEval_self]


theorem source_taylor_peano {n : ℕ} {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval n f a b)
    (hc : ContinuousOn (iteratedDerivWithin n f (Icc a b)) (Icc a b))
    (hx₀ : x₀ ∈ Icc a b) :
    (fun x ↦ f x - taylorPolynomialWithin n f (Icc a b) x₀ x) =o[𝓝[Icc a b] x₀]
      (fun x ↦ (x - x₀) ^ n) := by
  simpa only [taylorPolynomialWithin_eq_taylorWithin] using
    taylor_isLittleO (convex_Icc a b) hx₀ (source_closed_contDiffOn hf hc)


theorem iteratedDerivWithin_subinterval {n k : ℕ} {f : ℝ → ℝ} {a b x₀ x y : ℝ}
    (hkn : k ≤ n) (hab : a < b) (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (Icc a b)) (hs : uIcc x₀ x ⊆ Icc a b)
    (hy : y ∈ uIcc x₀ x) :
    iteratedDerivWithin k f (uIcc x₀ x) y = iteratedDerivWithin k f (Icc a b) y := by
  unfold iteratedDerivWithin
  rw [iteratedFDerivWithin_subset hs (uniqueDiffOn_uIcc hx) (uniqueDiffOn_Icc hab)
    (hf.of_le (by exact_mod_cast hkn)) hy]


theorem source_taylor_lagrange (n : ℕ) (_hn : 1 ≤ n) {f : ℝ → ℝ} {a b x₀ x : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval n f a b)
    (hc : ContinuousOn (iteratedDerivWithin n f (Icc a b)) (Icc a b))
    (hnext : DifferentiableToOrderOn (n + 1) f (Ioo a b))
    (hx₀ : x₀ ∈ Icc a b) (hx : x ∈ Icc a b) (hne : x ≠ x₀) :
    ∃ c ∈ uIoo x₀ x,
      f x = taylorPolynomialWithin n f (Icc a b) x₀ x +
        iteratedDerivWithin (n + 1) f (Icc a b) c * (x - x₀) ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by
  have hC := source_closed_contDiffOn hf hc
  have hsub := uIcc_subset_Icc hx₀ hx
  have hsub' := uIoo_subset_Ioo hx₀ hx
  have he : EqOn (iteratedDerivWithin n f (uIcc x₀ x))
      (iteratedDerivWithin n f (Ioo a b)) (uIoo x₀ x) := by
    intro y hy
    rw [iteratedDerivWithin_uIcc_interior n f hy,
      iteratedDerivWithin_of_isOpen isOpen_Ioo (hsub' hy)]
  have hd : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x) :=
    ((hnext n (Nat.lt_succ_self n)).mono hsub').congr he
  obtain ⟨c, hcm, hr⟩ := taylor_mean_remainder_lagrange hne.symm (hC.mono hsub) hd
  have hp : taylorWithinEval f n (uIcc x₀ x) x₀ x =
      taylorPolynomialWithin n f (Icc a b) x₀ x := by
    rw [taylor_within_apply, taylorPolynomialWithin]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [iteratedDerivWithin_subinterval hkn hf.1 hne.symm hC hsub left_mem_uIcc]
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have hdvalue : iteratedDerivWithin (n + 1) f (uIcc x₀ x) c =
      iteratedDerivWithin (n + 1) f (Icc a b) c := by
    rw [iteratedDerivWithin_uIcc_interior (n + 1) f hcm,
      iteratedDerivWithin_Icc_interior (n + 1) f (hsub' hcm)]
  rw [hp, hdvalue] at hr
  exact ⟨c, hcm, by linarith [hr]⟩

end calculus.Chapter04.Section03Taylor
