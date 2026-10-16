import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# §4.3, Bài 17: n nghiệm phân biệt của f−f′

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1165–1166.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section03PolynomialDerivativeDifferenceExercise
open Polynomial Set Filter
open scoped Topology


theorem polynomial_div_exp_hasDerivAt (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y ↦ p.eval y / Real.exp y)
      ((p.derivative.eval x - p.eval x) / Real.exp x) x := by
  apply ((p.hasDerivAt x).fun_div (Real.hasDerivAt_exp x)
    (Real.exp_ne_zero x)).congr_deriv
  field_simp [Real.exp_ne_zero x]


theorem derivative_difference_root_after {p : ℝ[X]} {r : ℝ} (hr : p.eval r = 0) :
    ∃ z, r < z ∧ (p - p.derivative).eval z = 0 := by
  classical
  let g : ℝ → ℝ := fun x ↦ p.eval x / Real.exp x
  let d : ℝ → ℝ := fun x ↦ (p.derivative.eval x - p.eval x) / Real.exp x
  have hd (x : ℝ) : HasDerivAt g (d x) x := polynomial_div_exp_hasDerivAt p x
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun x ↦ (hd x).continuousAt)
  have hgr : g r = 0 := by simp only [g, hr, zero_div]
  have hlim : Tendsto g atTop (𝓝 0) := p.tendsto_div_exp_atTop
  by_contra hz
  push Not at hz
  have hdne : ∀ x ∈ Ioi r, d x ≠ 0 := by
    intro x hx he
    have hnum : p.derivative.eval x - p.eval x = 0 :=
      (div_eq_zero_iff.mp he).resolve_right (Real.exp_ne_zero x)
    apply hz x hx
    rw [eval_sub]
    linarith
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne
      (convex_Ioi r) (fun x _ ↦ (hd x).hasDerivWithinAt) hdne with hn | hp
  · have hm : StrictAntiOn g (Ici r) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici r) hg.continuousOn
      intro x hx
      have hx' : x ∈ Ioi r := by simpa only [interior_Ici] using hx
      rw [(hd x).deriv]
      exact hn x hx'
    have hneg : g (r + 1) < 0 := by
      rw [← hgr]
      exact hm (by simp : r ∈ Ici r) (by simp : r + 1 ∈ Ici r) (by linarith)
    have hnonneg : 0 ≤ g (r + 1) := le_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop (r + 1)] with x hx
      exact hm.antitoneOn (by simp : r + 1 ∈ Ici r)
        (show x ∈ Ici r by change r ≤ x; linarith) hx)
    exact (not_le_of_gt hneg) hnonneg
  · have hm : StrictMonoOn g (Ici r) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici r) hg.continuousOn
      intro x hx
      have hx' : x ∈ Ioi r := by simpa only [interior_Ici] using hx
      rw [(hd x).deriv]
      exact hp x hx'
    have hpos : 0 < g (r + 1) := by
      rw [← hgr]
      exact hm (by simp : r ∈ Ici r) (by simp : r + 1 ∈ Ici r) (by linarith)
    have hnonpos : g (r + 1) ≤ 0 := ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop (r + 1)] with x hx
      exact hm.monotoneOn (by simp : r + 1 ∈ Ici r)
        (show x ∈ Ici r by change r ≤ x; linarith) hx)
    exact (not_le_of_gt hpos) hnonpos


theorem derivative_difference_root_between {p : ℝ[X]} {x y : ℝ}
    (hxy : x < y) (hx : p.eval x = 0) (hy : p.eval y = 0) :
    ∃ z ∈ Ioo x y, (p - p.derivative).eval z = 0 := by
  let g : ℝ → ℝ := fun t ↦ p.eval t / Real.exp t
  have hgc : ContinuousOn g (Icc x y) :=
    fun t _ ↦ (polynomial_div_exp_hasDerivAt p t).continuousAt.continuousWithinAt
  obtain ⟨z, hzm, hzd⟩ := exists_hasDerivAt_eq_zero hxy hgc
    (by simp only [g, hx, hy, zero_div]) (fun t _ ↦ polynomial_div_exp_hasDerivAt p t)
  refine ⟨z, hzm, ?_⟩
  have hnum := (div_eq_zero_iff.mp hzd).resolve_right (Real.exp_ne_zero z)
  rw [eval_sub]
  linarith

/-- Bài 17: `f − f′` có `n` nghiệm thực phân biệt nếu đa thức bậc `n` có `n` nghiệm thực phân biệt. -/
theorem source_polynomial_derivative_difference_roots (n : ℕ) {p : ℝ[X]}
    (hp : p.natDegree = n) (hr : p.roots.toFinset.card = n) :
    (p - p.derivative).natDegree = n ∧
      (p - p.derivative).roots.toFinset.card = n := by
  classical
  by_cases hn : n = 0
  · have hpd : p.derivative = 0 := derivative_eq_zero.mpr (hp.trans hn)
    simpa only [hpd, sub_zero] using And.intro hp hr
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let q : ℝ[X] := p - p.derivative
    have hqdegree : q.natDegree = n := by
      change (p - p.derivative).natDegree = n
      rw [natDegree_sub_eq_left_of_natDegree_lt
        (natDegree_derivative_lt (by omega : p.natDegree ≠ 0)), hp]
    have hp0 : p ≠ 0 := by intro hz; simp only [hz, natDegree_zero] at hp; omega
    have hq0 : q ≠ 0 := by intro hz; simp only [hz, natDegree_zero] at hqdegree; omega
    let s : Finset ℝ := p.roots.toFinset
    have hs : s.Nonempty := Finset.card_pos.mp (by dsimp [s]; omega)
    let r : ℝ := s.max' hs
    have hrmem : r ∈ s := Finset.max'_mem s hs
    have hreval : p.eval r = 0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp hrmem)
    obtain ⟨z, hrz, hz⟩ := derivative_difference_root_after hreval
    have hzmem : z ∈ q.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hq0).mpr hz)
    have hcard : s.card ≤ (q.roots.toFinset.erase z).card + 1 := by
      apply Finset.card_le_of_interleaved
      intro x hx y hy hxy _
      have hxeval : p.eval x = 0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp hx)
      have hyeval : p.eval y = 0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp hy)
      obtain ⟨t, htm, htq⟩ := derivative_difference_root_between hxy hxeval hyeval
      refine ⟨t, Finset.mem_erase.mpr ⟨?_, ?_⟩, htm⟩
      · have hyr : y ≤ r := Finset.le_max' s y hy
        exact ne_of_lt ((htm.2.trans_le hyr).trans hrz)
      · exact Multiset.mem_toFinset.mpr ((mem_roots hq0).mpr htq)
    have hlow : n ≤ q.roots.toFinset.card := by
      rw [Finset.card_erase_add_one hzmem] at hcard
      simpa only [s, hr] using hcard
    have hup : q.roots.toFinset.card ≤ n := by
      calc
        _ ≤ q.roots.card := Multiset.toFinset_card_le _
        _ ≤ q.natDegree := q.card_roots'
        _ = n := hqdegree
    exact ⟨hqdegree, Nat.le_antisymm hup hlow⟩

end calculus.Chapter04.Section03PolynomialDerivativeDifferenceExercise
