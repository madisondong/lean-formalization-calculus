import calculus.Chapter04.Section03PolynomialDerivativeDifferenceExercise
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# §4.3 Bài 19: toán tử đạo hàm cấp hai và nghiệm thực

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1171–1172. Số nghiệm thực được tính cả bội; đa thức 0 được xét riêng.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Set Finset
namespace calculus.Chapter04.Section03QuadraticDerivativeOperatorRealRoots
open calculus.Chapter04.Section03PolynomialDerivativeDifferenceExercise


theorem derivative_difference_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    p - p.derivative ≠ 0 := by
  by_cases hd : p.natDegree = 0
  · simpa only [derivative_eq_zero.mpr hd, sub_zero] using hp
  · have hdegree : (p - p.derivative).natDegree = p.natDegree :=
      natDegree_sub_eq_left_of_natDegree_lt (natDegree_derivative_lt hd)
    intro hz
    rw [hz, natDegree_zero] at hdegree
    exact hd hdegree.symm


theorem derivative_difference_distinct_sdiff_count {p : ℝ[X]} (hp : p ≠ 0) :
    p.roots.toFinset.card ≤
      ((p - p.derivative).roots.toFinset \ p.roots.toFinset).card := by
  classical
  let q : ℝ[X] := p - p.derivative
  let s : Finset ℝ := p.roots.toFinset
  have hq : q ≠ 0 := derivative_difference_ne_zero hp
  by_cases hs0 : s = ∅
  · change s.card ≤ (q.roots.toFinset \ s).card
    rw [hs0, Finset.card_empty]
    exact Nat.zero_le _
  · have hs : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
    let r : ℝ := s.max' hs
    have hr : r ∈ s := Finset.max'_mem s hs
    have hre : p.eval r = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp hr)
    obtain ⟨z, hrz, hze⟩ := derivative_difference_root_after hre
    have hzq : z ∈ q.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hq).mpr hze)
    have hzs : z ∉ s := by
      intro hz
      exact (not_le_of_gt hrz) (Finset.le_max' s z hz)
    have hcard : s.card ≤ ((q.roots.toFinset.erase z) \ s).card + 1 := by
      apply Finset.card_le_sdiff_of_interleaved
      intro x hx y hy hxy _
      have hxe : p.eval x = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp hx)
      have hye : p.eval y = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp hy)
      obtain ⟨t, htm, hte⟩ := derivative_difference_root_between hxy hxe hye
      refine ⟨t, Finset.mem_erase.mpr ⟨?_, ?_⟩, htm⟩
      · exact ne_of_lt ((htm.2.trans_le (Finset.le_max' s y hy)).trans hrz)
      · exact Multiset.mem_toFinset.mpr ((mem_roots hq).mpr hte)
    rw [Finset.erase_sdiff_comm,
      Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨hzq, hzs⟩)] at hcard
    exact hcard


theorem derivative_difference_root_multiplicity_lower {p : ℝ[X]} (hp : p ≠ 0) (x : ℝ) :
    p.rootMultiplicity x - 1 ≤ (p - p.derivative).rootMultiplicity x := by
  apply (le_rootMultiplicity_iff (derivative_difference_ne_zero hp)).mpr
  exact dvd_sub
    ((pow_dvd_pow (X - C x) (Nat.sub_le (p.rootMultiplicity x) 1)).trans
      (p.pow_rootMultiplicity_dvd x))
    (pow_sub_one_dvd_derivative_of_pow_dvd (p.pow_rootMultiplicity_dvd x))


theorem derivative_difference_real_root_count (p : ℝ[X]) :
    p.roots.card ≤ (p - p.derivative).roots.card := by
  classical
  by_cases hp : p = 0
  · simp only [hp, roots_zero, Multiset.card_zero, Nat.zero_le]
  · let q : ℝ[X] := p - p.derivative
    calc
      p.roots.card = ∑ x ∈ p.roots.toFinset, p.roots.count x :=
        (Multiset.toFinset_sum_count_eq _).symm
      _ = ∑ x ∈ p.roots.toFinset, (p.roots.count x - 1 + 1) :=
        (Eq.symm <| Finset.sum_congr rfl fun _ hx ↦ tsub_add_cancel_of_le <|
          Nat.succ_le_iff.mpr <| Multiset.count_pos.mpr <| Multiset.mem_toFinset.mp hx)
      _ = (∑ x ∈ p.roots.toFinset, (p.rootMultiplicity x - 1)) +
          p.roots.toFinset.card := by
        simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
      _ ≤ (∑ x ∈ p.roots.toFinset, q.rootMultiplicity x) +
          (q.roots.toFinset \ p.roots.toFinset).card :=
        add_le_add
          (Finset.sum_le_sum fun x _ ↦ derivative_difference_root_multiplicity_lower hp x)
          (derivative_difference_distinct_sdiff_count hp)
      _ ≤ (∑ x ∈ p.roots.toFinset, q.roots.count x) +
          (∑ x ∈ q.roots.toFinset \ p.roots.toFinset, q.roots.count x) := by
        simp only [← count_roots]
        apply add_le_add (le_refl _)
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_le_sum
        intro x hx
        exact Nat.succ_le_iff.mpr (Multiset.count_pos.mpr
          (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1))
      _ = q.roots.card := by
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union,
          ← Multiset.toFinset_sum_count_eq,
          ← Finset.sum_subset Finset.subset_union_right]
        intro x _ hx
        simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx


theorem affine_scale_real_root_count (p : ℝ[X]) (r : ℝ) (hr : r ≠ 0) :
    (p.comp (C r * X)).roots.card = p.roots.card := by
  have hh := congrArg Multiset.card
    (p.map_roots_comp_C_mul_X_add_C r 0 (isUnit_iff_ne_zero.mpr hr))
  simpa only [C_0, add_zero, Multiset.card_map] using hh


theorem first_order_operator_real_root_count (p : ℝ[X]) (r : ℝ) :
    p.roots.card ≤ (p - C r * p.derivative).roots.card := by
  by_cases hr : r = 0
  · simp only [hr, C_0, zero_mul, sub_zero, le_refl]
  · have hh := derivative_difference_real_root_count (p.comp (C r * X))
    have he : p.comp (C r * X) - (p.comp (C r * X)).derivative =
        (p - C r * p.derivative).comp (C r * X) := by
      simp only [derivative_comp, derivative_C_mul_X, sub_comp, mul_comp, C_comp]
    rw [he, affine_scale_real_root_count _ r hr, affine_scale_real_root_count _ r hr] at hh
    exact hh


theorem quadratic_real_factor_parameters (a b c : ℝ) (ha : a ≠ 0)
    (hroots : (C a * X ^ 2 + C b * X + C c : ℝ[X]).roots.card = 2) :
    ∃ u v : ℝ, a * (u + v) = -b ∧ a * (u * v) = c := by
  let q : ℝ[X] := C a * X ^ 2 + C b * X + C c
  have hq : q ≠ 0 := by
    intro hz
    have he : q.roots.card = 2 := hroots
    simp only [hz, roots_zero, Multiset.card_zero] at he
    omega
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp
    (show 0 < q.roots.card by change 0 < (C a * X ^ 2 + C b * X + C c : ℝ[X]).roots.card; omega)
  have he : a * u ^ 2 + b * u + c = 0 := by
    simpa only [Polynomial.IsRoot, q, eval_add, eval_mul, eval_pow, eval_C, eval_X] using! (mem_roots hq).mp hu
  let v : ℝ := -b / a - u
  refine ⟨u, v, ?_, ?_⟩
  · dsimp only [v]
    field_simp [ha]
    ring
  · calc
      a * (u * v) = -b * u - a * u ^ 2 := by
        dsimp only [v]
        field_simp [ha]
      _ = c := by nlinarith [he]


theorem quadratic_derivative_operator_factorization (p : ℝ[X]) (a b c u v : ℝ)
    (hsum : a * (u + v) = -b) (hprod : a * (u * v) = c) :
    C a * p + C b * p.derivative + C c * p.derivative.derivative =
      C a * ((p - C u * p.derivative) -
        C v * (p - C u * p.derivative).derivative) := by
  have hs : C a * (C u + C v : ℝ[X]) = -C b := by
    rw [← C_add, ← C_mul, hsum, C_neg]
  have hp : C a * (C u * C v : ℝ[X]) = C c := by
    rw [← C_mul, ← C_mul, hprod]
  rw [derivative_sub, derivative_C_mul]
  calc
    C a * p + C b * p.derivative + C c * p.derivative.derivative =
        C a * p - (C a * (C u + C v)) * p.derivative +
          (C a * (C u * C v)) * p.derivative.derivative := by
      rw [hs, hp]
      ring
    _ = C a * ((p - C u * p.derivative) -
        C v * (p.derivative - C u * p.derivative.derivative)) := by ring

/-- Bài 19: toán tử đạo hàm bảo toàn ít nhất ba nghiệm thực tính cả bội; xét cả đa thức 0. -/
theorem source_quadratic_derivative_operator_real_roots (p : ℝ[X]) (a b c : ℝ)
    (ha : a ≠ 0)
    (hquadratic : (C a * X ^ 2 + C b * X + C c : ℝ[X]).roots.card = 2)
    (hp : p = 0 ∨ 3 ≤ p.roots.card) :
    C a * p + C b * p.derivative + C c * p.derivative.derivative = 0 ∨
      3 ≤ (C a * p + C b * p.derivative + C c * p.derivative.derivative).roots.card := by
  rcases hp with hp | hp
  · left
    simp only [hp, derivative_zero, mul_zero, add_zero]
  · right
    obtain ⟨u, v, hsum, hprod⟩ := quadratic_real_factor_parameters a b c ha hquadratic
    rw [quadratic_derivative_operator_factorization p a b c u v hsum hprod,
      roots_C_mul _ ha]
    exact hp.trans ((first_order_operator_real_root_count p u).trans
      (first_order_operator_real_root_count (p - C u * p.derivative) v))


theorem derivative_difference_distinct_real_root_count (p : ℝ[X]) :
    p.roots.toFinset.card ≤ (p - p.derivative).roots.toFinset.card := by
  classical
  by_cases hp : p = 0
  · simp only [hp, roots_zero, Multiset.toFinset_zero, Finset.card_empty, Nat.zero_le]
  · exact (derivative_difference_distinct_sdiff_count hp).trans
      (Finset.card_le_card Finset.sdiff_subset)


theorem affine_scale_distinct_real_root_count (p : ℝ[X]) (r : ℝ) (hr : r ≠ 0) :
    (p.comp (C r * X)).roots.toFinset.card = p.roots.toFinset.card := by
  classical
  have hh := congrArg (fun s : Multiset ℝ ↦ s.toFinset.card)
    (p.map_roots_comp_C_mul_X_add_C r 0 (isUnit_iff_ne_zero.mpr hr))
  simp only [C_0, add_zero, Multiset.toFinset_map] at hh
  rw [Finset.card_image_of_injective _
    (fun x y h ↦ mul_left_cancel₀ hr (by simpa only [add_zero] using h))] at hh
  exact hh


theorem first_order_operator_distinct_real_root_count (p : ℝ[X]) (r : ℝ) :
    p.roots.toFinset.card ≤ (p - C r * p.derivative).roots.toFinset.card := by
  by_cases hr : r = 0
  · simp only [hr, C_0, zero_mul, sub_zero, le_refl]
  · have hh := derivative_difference_distinct_real_root_count (p.comp (C r * X))
    have he : p.comp (C r * X) - (p.comp (C r * X)).derivative =
        (p - C r * p.derivative).comp (C r * X) := by
      simp only [derivative_comp, derivative_C_mul_X, sub_comp, mul_comp, C_comp]
    rw [he, affine_scale_distinct_real_root_count _ r hr,
      affine_scale_distinct_real_root_count _ r hr] at hh
    exact hh

/-- Bài 19: toán tử đạo hàm bảo toàn ít nhất ba nghiệm thực phân biệt; xét cả đa thức 0. -/
theorem source_quadratic_derivative_operator_distinct_real_roots (p : ℝ[X]) (a b c : ℝ)
    (ha : a ≠ 0)
    (hquadratic : (C a * X ^ 2 + C b * X + C c : ℝ[X]).roots.card = 2)
    (hp : p = 0 ∨ 3 ≤ p.roots.toFinset.card) :
    C a * p + C b * p.derivative + C c * p.derivative.derivative = 0 ∨
      3 ≤ (C a * p + C b * p.derivative + C c * p.derivative.derivative).roots.toFinset.card := by
  rcases hp with hp | hp
  · left
    simp only [hp, derivative_zero, mul_zero, add_zero]
  · right
    obtain ⟨u, v, hsum, hprod⟩ := quadratic_real_factor_parameters a b c ha hquadratic
    rw [quadratic_derivative_operator_factorization p a b c u v hsum hprod,
      roots_C_mul _ ha]
    exact hp.trans ((first_order_operator_distinct_real_root_count p u).trans
      (first_order_operator_distinct_real_root_count (p - C u * p.derivative) v))

end calculus.Chapter04.Section03QuadraticDerivativeOperatorRealRoots
