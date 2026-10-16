import calculus.Chapter04.Section01PolynomialExponentialMatching
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.1 Bài 12: ghép ba nhánh

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 544–560. Nhánh trái nhận điểm 0. Tại điểm 1, phần (a) lấy nhánh phải, phần (b) lấy nhánh giữa. Tham số `d` trong phần (a) tự do vì không xuất hiện trong hàm.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section01ThreeBranchMatching
open calculus.Chapter04.Section01PolynomialExponentialMatching


def threeJoin (atMiddleOne : Bool) (l m r : ℝ → ℝ) : ℝ → ℝ :=
  joinAt 0 true l (joinAt 1 atMiddleOne m r)


theorem threeJoin_differentiable_iff {flag : Bool} {l m r ld md rd : ℝ → ℝ}
    (hl : ∀ x, HasDerivAt l (ld x) x) (hm : ∀ x, HasDerivAt m (md x) x)
    (hr : ∀ x, 1 ≤ x → HasDerivAt r (rd x) x) :
    Differentiable ℝ (threeJoin flag l m r) ↔
      (l 0 = m 0 ∧ ld 0 = md 0) ∧ (m 1 = r 1 ∧ md 1 = rd 1) := by
  have hinner0 : HasDerivAt (joinAt 1 flag m r) (md 0) 0 :=
    joinAt_hasDerivAt_of_lt (by norm_num) (hm 0)
  have hinner0value : joinAt 1 flag m r 0 = m 0 := joinAt_of_lt (by norm_num)
  constructor
  · intro hf
    have h0 := (joinAt_differentiableAt_iff (k := 0) (flag := true) (hl 0) hinner0).mp (hf 0)
    have hEq : threeJoin flag l m r =ᶠ[𝓝 (1 : ℝ)] joinAt 1 flag m r := by
      filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
      exact joinAt_of_gt hx
    have h1diff := ((hf 1).hasDerivAt.congr_of_eventuallyEq hEq.symm).differentiableAt
    have h1 := (joinAt_differentiableAt_iff (hm 1) (hr 1 le_rfl)).mp h1diff
    exact ⟨⟨by simpa only [hinner0value] using h0.1, h0.2⟩, h1⟩
  · rintro ⟨⟨hv0, hd0⟩, ⟨hv1, hd1⟩⟩ x
    have hzero : HasDerivAt (threeJoin flag l m r) (ld 0) 0 := by
      apply joinAt_hasDerivAt (hl 0)
      · simpa only [hd0] using hinner0
      · exact hv0.trans hinner0value.symm
    have hone : HasDerivAt (joinAt 1 flag m r) (md 1) 1 :=
      joinAt_hasDerivAt (hm 1) (by simpa only [hd1] using hr 1 le_rfl) hv1
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · exact (joinAt_hasDerivAt_of_lt hx (hl x)).differentiableAt
    · exact hzero.differentiableAt
    · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
      · exact (joinAt_hasDerivAt_of_gt hx (joinAt_hasDerivAt_of_lt hx1 (hm x))).differentiableAt
      · exact (joinAt_hasDerivAt_of_gt hx hone).differentiableAt
      · exact (joinAt_hasDerivAt_of_gt hx (joinAt_hasDerivAt_of_gt hx1 (hr x hx1.le))).differentiableAt


def linearQuadraticAffineJoin (a b c : ℝ) : ℝ → ℝ :=
  threeJoin false (fun x ↦ 4 * x) (fun x ↦ a * x ^ 2 + b * x + c)
    (fun x ↦ 3 - 2 * x)


def affineQuadraticRationalJoin (a b c d : ℝ) : ℝ → ℝ :=
  threeJoin true (fun x ↦ a * x + b) (fun x ↦ c * x ^ 2 + d * x)
    (fun x ↦ (x - 1) / x)

theorem linearQuadraticAffineJoin_source_formula (a b c x : ℝ) :
    linearQuadraticAffineJoin a b c x =
      if x ≤ 0 then 4 * x else if x < 1 then a * x ^ 2 + b * x + c else 3 - 2 * x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [linearQuadraticAffineJoin, threeJoin, joinAt, hx, hx.le]
  · simp [linearQuadraticAffineJoin, threeJoin, joinAt]
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · simp [linearQuadraticAffineJoin, threeJoin, joinAt, hx, hx1, not_le.mpr hx,
        not_lt_of_ge hx.le]
    · norm_num [linearQuadraticAffineJoin, threeJoin, joinAt]
    · simp [linearQuadraticAffineJoin, threeJoin, joinAt, hx, hx1, not_le.mpr hx,
        not_lt_of_ge hx.le, not_lt_of_ge hx1.le]

theorem affineQuadraticRationalJoin_source_formula (a b c d x : ℝ) :
    affineQuadraticRationalJoin a b c d x =
      if x ≤ 0 then a * x + b else if x ≤ 1 then c * x ^ 2 + d * x else (x - 1) / x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [affineQuadraticRationalJoin, threeJoin, joinAt, hx, hx.le]
  · simp [affineQuadraticRationalJoin, threeJoin, joinAt]
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · simp [affineQuadraticRationalJoin, threeJoin, joinAt, hx, hx1, hx1.le,
        not_le.mpr hx, not_lt_of_ge hx.le]
    · norm_num [affineQuadraticRationalJoin, threeJoin, joinAt]
    · simp [affineQuadraticRationalJoin, threeJoin, joinAt, hx, hx1, not_le.mpr hx,
        not_le.mpr hx1, not_lt_of_ge hx.le, not_lt_of_ge hx1.le]

theorem affine_hasDerivAt (a b x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ a * y + b) a x := by
  simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul a).add_const b

theorem quadratic_affine_hasDerivAt (a b c x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ a * y ^ 2 + b * y + c) (2 * a * x + b) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul a).add ((hasDerivAt_id x).const_mul b)).add_const c
  apply h.congr_deriv
  norm_num only [id_eq, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem affine_right_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ 3 - 2 * y) (-2) x := by
  simpa only [id_eq, mul_one, neg_mul, one_mul, sub_eq_add_neg] using
    ((hasDerivAt_id x).const_mul (-2 : ℝ)).const_add 3

theorem rational_right_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ (y - 1) / y) (1 / x ^ 2) x := by
  have h := ((hasDerivAt_id x).sub_const 1).div (hasDerivAt_id x) hx
  apply h.congr_deriv
  simp only [mul_one, one_mul]
  congr 1
  ring

/-- Bài 12(a): khả vi khi và chỉ khi `a = −3`, `b = 4`, `c = 0`. -/
theorem linear_quadratic_affine_parameters_iff (a b c : ℝ) :
    Differentiable ℝ (linearQuadraticAffineJoin a b c) ↔ a = -3 ∧ b = 4 ∧ c = 0 := by
  have hl (x : ℝ) : HasDerivAt (fun y : ℝ ↦ 4 * y) 4 x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (4 : ℝ)
  have hr (x : ℝ) (_hx : 1 ≤ x) : HasDerivAt (fun y : ℝ ↦ 3 - 2 * y) (-2) x :=
    affine_right_hasDerivAt x
  have hh := threeJoin_differentiable_iff (flag := false) hl
    (quadratic_affine_hasDerivAt a b c) hr
  change Differentiable ℝ (linearQuadraticAffineJoin a b c) ↔ _ at hh
  constructor
  · intro hf
    have h := hh.mp hf
    have hc : c = 0 := by simpa using h.1.1.symm
    have hb : b = 4 := by simpa using h.1.2.symm
    have hd : 2 * a + b = -2 := by simpa using h.2.2
    exact ⟨by linarith, hb, hc⟩
  · rintro ⟨ha, hb, hc⟩
    apply hh.mpr
    norm_num [ha, hb, hc]

/-- Bài 12(b): khả vi khi và chỉ khi `a = −1`, `b = 0`, `c = 1`, `d = −1`. -/
theorem source_affine_quadratic_rational_parameters_iff (a b c d : ℝ) :
    Differentiable ℝ (affineQuadraticRationalJoin a b c d) ↔
      a = -1 ∧ b = 0 ∧ c = 1 ∧ d = -1 := by
  have hm (x : ℝ) : HasDerivAt (fun y : ℝ ↦ c * y ^ 2 + d * y) (2 * c * x + d) x := by
    simpa only [add_zero] using quadratic_affine_hasDerivAt c d 0 x
  have hr (x : ℝ) (hx : 1 ≤ x) : HasDerivAt (fun y : ℝ ↦ (y - 1) / y) (1 / x ^ 2) x :=
    rational_right_hasDerivAt (by linarith)
  have hh := threeJoin_differentiable_iff (flag := true) (affine_hasDerivAt a b) hm hr
  change Differentiable ℝ (affineQuadraticRationalJoin a b c d) ↔ _ at hh
  constructor
  · intro hf
    have h := hh.mp hf
    have hb : b = 0 := by simpa using h.1.1
    have had : a = d := by simpa using h.1.2
    have hv : c + d = 0 := by simpa using h.2.1
    have hd : 2 * c + d = 1 := by simpa using h.2.2
    exact ⟨by linarith, hb, by linarith, by linarith⟩
  · rintro ⟨ha, hb, hc, hd⟩
    apply hh.mpr
    norm_num [ha, hb, hc, hd]

end calculus.Chapter04.Section01ThreeBranchMatching
