import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# §4.3, Bài 34: cận đạo hàm cấp hai với hệ số 4

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1389–1390. `f′` ở đầu mút là đạo hàm một bên; `f″` chỉ cần tồn tại trong `(a, b)`.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section03EndpointSecondDerivativeBoundExercise
open Set
open scoped Topology


theorem quadratic_shift_hasDerivWithinAt {f f' : ℝ → ℝ} {a b M x : ℝ}
    (hf : HasDerivWithinAt f (f' x) (Icc a b) x) :
    HasDerivWithinAt (fun y ↦ f y + M / 2 * y ^ 2)
      (f' x + M * x) (Icc a b) x := by
  have hq := ((hasDerivWithinAt_id x (Icc a b)).fun_pow 2).const_mul (M / 2)
  simp only [id_eq] at hq
  apply (hf.fun_add hq).congr_deriv
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring


theorem quadratic_shift_first_hasDerivAt {f' f'' : ℝ → ℝ} {M x : ℝ}
    (hf : HasDerivAt f' (f'' x) x) :
    HasDerivAt (fun y ↦ f' y + M * y) (f'' x + M) x := by
  simpa only [id_eq, mul_one] using! hf.fun_add ((hasDerivAt_id x).const_mul M)


theorem quadratic_shift_strictConvex {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hff : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < f'' x + M) :
    StrictConvexOn ℝ (Icc a b) (fun y ↦ f y + M / 2 * y ^ 2) := by
  let g : ℝ → ℝ := fun y ↦ f y + M / 2 * y ^ 2
  let g' : ℝ → ℝ := fun y ↦ f' y + M * y
  have hgc : ContinuousOn g (Icc a b) :=
    fun x hx ↦ (quadratic_shift_hasDerivWithinAt (M := M) (hf x hx)).continuousWithinAt
  have he : EqOn (deriv g) g' (Ioo a b) := by
    intro x hx
    exact ((quadratic_shift_hasDerivWithinAt (M := M) (hf x (Ioo_subset_Icc_self hx))).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).deriv
  have he2 := he.deriv isOpen_Ioo
  apply strictConvexOn_of_deriv2_pos (convex_Icc a b) hgc
  intro x hx
  have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
  have hv : (deriv^[2] g) x = f'' x + M := by
    change deriv (deriv g) x = _
    rw [he2 hx', (quadratic_shift_first_hasDerivAt (M := M) (hff x hx')).deriv]
  rw [hv]
  exact hpos x hx'


theorem strict_endpoint_lower_bounds {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hff : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (ha : f' a = 0) (hb : f' b = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < f'' x + M) :
    f a - M / 2 * (((a + b) / 2) - a) ^ 2 < f ((a + b) / 2) ∧
    f b - M / 2 * (((a + b) / 2) - b) ^ 2 < f ((a + b) / 2) := by
  let t : ℝ := (a + b) / 2
  have ht : t ∈ Ioo a b := by dsimp [t]; constructor <;> linarith
  have haS : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hbS : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hg := quadratic_shift_strictConvex hf hff hpos
  have hl := hg.lt_slope_of_hasDerivWithinAt haS (Ioo_subset_Icc_self ht) ht.1
    (quadratic_shift_hasDerivWithinAt (M := M) (hf a haS))
  have hu := hg.slope_lt_of_hasDerivWithinAt (Ioo_subset_Icc_self ht) hbS ht.2
    (quadratic_shift_hasDerivWithinAt (M := M) (hf b hbS))
  simp only [ha, hb, zero_add, slope_def_field] at hl hu
  have hl' := (lt_div_iff₀ (sub_pos.mpr ht.1)).mp hl
  have hu' := (div_lt_iff₀ (sub_pos.mpr ht.2)).mp hu
  dsimp [t] at hl' hu' ⊢
  constructor <;> nlinarith

/-- Bài 34: cận của `|f″|` với hệ số 4 khi đạo hàm tại hai đầu mút bằng 0. -/
theorem source_endpoint_second_derivative_bound {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hff : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (ha : f' a = 0) (hb : f' b = 0) :
    ∃ c ∈ Ioo a b, 4 / (b - a) ^ 2 * |f b - f a| ≤ |f'' c| := by
  classical
  let M : ℝ := 4 / (b - a) ^ 2 * |f b - f a|
  by_contra h
  push Not at h
  have hsmall : ∀ x ∈ Ioo a b, |f'' x| < M := h
  have hp : ∀ x ∈ Ioo a b, 0 < f'' x + M := by
    intro x hx
    have hh := (abs_lt.mp (hsmall x hx)).1
    linarith
  have hn : ∀ x ∈ Ioo a b, 0 < -f'' x + M := by
    intro x hx
    have hh := (abs_lt.mp (hsmall x hx)).2
    linarith
  obtain ⟨hla, hlb⟩ := strict_endpoint_lower_bounds hab hf hff ha hb hp
  obtain ⟨hna, hnb⟩ := strict_endpoint_lower_bounds (f := fun x ↦ -f x)
    (f' := fun x ↦ -f' x) (f'' := fun x ↦ -f'' x) hab
    (fun x hx ↦ (hf x hx).neg) (fun x hx ↦ (hff x hx).neg)
    (by simp only [ha, neg_zero]) (by simp only [hb, neg_zero]) hn
  have hwidth : (b - a) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hab.ne')
  have hm : M * (b - a) ^ 2 = 4 * |f b - f a| := by
    dsimp [M]
    field_simp [hwidth, sub_ne_zero.mpr hab.ne']
  rcases le_total (f a) (f b) with habf | hbaf
  · rw [abs_of_nonneg (sub_nonneg.mpr habf)] at hm
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hbaf)] at hm
    nlinarith

end calculus.Chapter04.Section03EndpointSecondDerivativeBoundExercise
