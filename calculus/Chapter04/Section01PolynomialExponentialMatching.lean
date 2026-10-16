import calculus.Chapter04.Section01Higher
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.1 Bài 10: ghép đa thức và hàm mũ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 514–526. Nhánh trái nhận điểm 0.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section01PolynomialExponentialMatching
open calculus.Chapter04.Section01Higher


def joinAt (k : ℝ) (atLeft : Bool) (left right : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < k then left x else if k < x then right x else if atLeft then left x else right x

theorem joinAt_of_lt {k x : ℝ} {flag : Bool} {l r : ℝ → ℝ} (hx : x < k) :
    joinAt k flag l r x = l x := by simp [joinAt, hx]

theorem joinAt_of_gt {k x : ℝ} {flag : Bool} {l r : ℝ → ℝ} (hx : k < x) :
    joinAt k flag l r x = r x := by simp [joinAt, hx, not_lt_of_ge hx.le]

theorem joinAt_self (k : ℝ) (flag : Bool) (l r : ℝ → ℝ) :
    joinAt k flag l r k = if flag then l k else r k := by simp [joinAt]

theorem joinAt_left_closed {k : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hv : l k = r k) : EqOn (joinAt k flag l r) l (Iic k) := by
  intro x hx
  rcases lt_or_eq_of_le (mem_Iic.mp hx) with h | rfl
  · exact joinAt_of_lt h
  · cases flag <;> simp [joinAt, hv]

theorem joinAt_right_closed {k : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hv : l k = r k) : EqOn (joinAt k flag l r) r (Ici k) := by
  intro x hx
  rcases lt_or_eq_of_le (mem_Ici.mp hx) with h | h
  · exact joinAt_of_gt h
  · subst x
    cases flag <;> simp [joinAt, hv]

theorem joinAt_values_equal_of_continuousAt {k : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hl : ContinuousAt l k) (hr : ContinuousAt r k)
    (hf : ContinuousAt (joinAt k flag l r) k) : l k = r k := by
  have hleft : Tendsto l (𝓝[<] k) (𝓝 (joinAt k flag l r k)) := by
    apply (hf.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact joinAt_of_lt hx
  have hright : Tendsto r (𝓝[>] k) (𝓝 (joinAt k flag l r k)) := by
    apply (hf.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact joinAt_of_gt hx
  have h1 := tendsto_nhds_unique hleft (hl.tendsto.mono_left nhdsWithin_le_nhds)
  have h2 := tendsto_nhds_unique hright (hr.tendsto.mono_left nhdsWithin_le_nhds)
  exact h1.symm.trans h2

theorem joinAt_continuousAt {k : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hl : ContinuousAt l k) (hr : ContinuousAt r k) (hv : l k = r k) :
    ContinuousAt (joinAt k flag l r) k := by
  have hL : ContinuousWithinAt (joinAt k flag l r) (Iic k) k :=
    hl.continuousWithinAt.congr (joinAt_left_closed hv) (joinAt_left_closed hv self_mem_Iic)
  have hR : ContinuousWithinAt (joinAt k flag l r) (Ici k) k :=
    hr.continuousWithinAt.congr (joinAt_right_closed hv) (joinAt_right_closed hv self_mem_Ici)
  have hunion : Iic k ∪ Ici k = univ := by ext x; simp
  have hh := hL.union hR
  rw [hunion] at hh
  exact (continuousWithinAt_univ _ _).mp hh

theorem joinAt_hasDerivAt {k dl : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hl : HasDerivAt l dl k) (hr : HasDerivAt r dl k) (hv : l k = r k) :
    HasDerivAt (joinAt k flag l r) dl k := by
  have hL : HasDerivWithinAt (joinAt k flag l r) dl (Iic k) k :=
    hl.hasDerivWithinAt.congr (joinAt_left_closed hv) (joinAt_left_closed hv self_mem_Iic)
  have hR : HasDerivWithinAt (joinAt k flag l r) dl (Ici k) k :=
    hr.hasDerivWithinAt.congr (joinAt_right_closed hv) (joinAt_right_closed hv self_mem_Ici)
  have hunion : Iic k ∪ Ici k = univ := by ext x; simp
  have hh := hL.union hR
  rw [hunion] at hh
  exact hasDerivWithinAt_univ.mp hh

theorem joinAt_differentiableAt_iff {k dl dr : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hl : HasDerivAt l dl k) (hr : HasDerivAt r dr k) :
    DifferentiableAt ℝ (joinAt k flag l r) k ↔ l k = r k ∧ dl = dr := by
  constructor
  · intro hf
    have hv := joinAt_values_equal_of_continuousAt hl.continuousAt hr.continuousAt hf.continuousAt
    have hL : HasDerivWithinAt (joinAt k flag l r) dl (Iic k) k :=
      hl.hasDerivWithinAt.congr (joinAt_left_closed hv) (joinAt_left_closed hv self_mem_Iic)
    have hR : HasDerivWithinAt (joinAt k flag l r) dr (Ici k) k :=
      hr.hasDerivWithinAt.congr (joinAt_right_closed hv) (joinAt_right_closed hv self_mem_Ici)
    have hdL : deriv (joinAt k flag l r) k = dl :=
      (hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic k)).symm.trans
        (hL.derivWithin (uniqueDiffWithinAt_Iic k))
    have hdR : deriv (joinAt k flag l r) k = dr :=
      (hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici k)).symm.trans
        (hR.derivWithin (uniqueDiffWithinAt_Ici k))
    exact ⟨hv, hdL.symm.trans hdR⟩
  · rintro ⟨hv, hd⟩
    rw [← hd] at hr
    exact (joinAt_hasDerivAt hl hr hv).differentiableAt

theorem joinAt_hasDerivAt_of_lt {k x d : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hx : x < k) (hl : HasDerivAt l d x) : HasDerivAt (joinAt k flag l r) d x := by
  apply hl.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hx] with y hy
  exact joinAt_of_lt hy

theorem joinAt_hasDerivAt_of_gt {k x d : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hx : k < x) (hr : HasDerivAt r d x) : HasDerivAt (joinAt k flag l r) d x := by
  apply hr.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact joinAt_of_gt hy

theorem joinAt_continuous_iff {k : ℝ} {flag : Bool} {l r : ℝ → ℝ}
    (hl : Continuous l) (hr : Continuous r) :
    Continuous (joinAt k flag l r) ↔ l k = r k := by
  constructor
  · intro hf
    exact joinAt_values_equal_of_continuousAt hl.continuousAt hr.continuousAt hf.continuousAt
  · intro hv
    apply continuous_iff_continuousAt.mpr
    intro x
    rcases lt_trichotomy x k with hx | rfl | hx
    · apply hl.continuousAt.congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact joinAt_of_lt hy
    · exact joinAt_continuousAt hl.continuousAt hr.continuousAt hv
    · apply hr.continuousAt.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact joinAt_of_gt hy

theorem joinAt_differentiable_iff {k : ℝ} {flag : Bool} {l r ld rd : ℝ → ℝ}
    (hl : ∀ x, HasDerivAt l (ld x) x) (hr : ∀ x, HasDerivAt r (rd x) x) :
    Differentiable ℝ (joinAt k flag l r) ↔ l k = r k ∧ ld k = rd k := by
  constructor
  · intro hf
    exact (joinAt_differentiableAt_iff (hl k) (hr k)).mp (hf k)
  · rintro ⟨hv, hd⟩ x
    rcases lt_trichotomy x k with hx | hxeq | hx
    · exact (joinAt_hasDerivAt_of_lt hx (hl x)).differentiableAt
    · subst x
      exact (joinAt_hasDerivAt (hl k) (by simpa only [hd] using hr k) hv).differentiableAt
    · exact (joinAt_hasDerivAt_of_gt hx (hr x)).differentiableAt

def quadraticExponentialJoin (a b c : ℝ) : ℝ → ℝ :=
  joinAt 0 true (fun x ↦ a * x ^ 2 + b) (fun x ↦ Real.exp x + c * x)

theorem quadraticExponentialJoin_source_formula (a b c x : ℝ) :
    quadraticExponentialJoin a b c x =
      if x ≤ 0 then a * x ^ 2 + b else Real.exp x + c * x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [quadraticExponentialJoin, joinAt, hx, hx.le]
  · simp [quadraticExponentialJoin, joinAt]
  · simp [quadraticExponentialJoin, joinAt, hx, not_lt_of_ge hx.le, not_le.mpr hx]

theorem quadratic_left_hasDerivAt (a b x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ a * y ^ 2 + b) (2 * a * x) x := by
  have hh := ((hasDerivAt_pow 2 x).const_mul a).add_const b
  apply hh.congr_deriv
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem exponential_right_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp y + c * y) (Real.exp x + c) x := by
  simpa only [id_eq, mul_one] using!
    (Real.hasDerivAt_exp x).add ((hasDerivAt_id x).const_mul c)

/-- Bài 10(a): liên tục trên ℝ khi và chỉ khi `b = 1`; `a, c` tùy ý. -/
theorem source_continuous_parameters_iff (a b c : ℝ) :
    Continuous (quadraticExponentialJoin a b c) ↔ b = 1 := by
  have hl : Continuous (fun x : ℝ ↦ a * x ^ 2 + b) :=
    (show Differentiable ℝ _ from fun x ↦ (quadratic_left_hasDerivAt a b x).differentiableAt).continuous
  have hr : Continuous (fun x : ℝ ↦ Real.exp x + c * x) :=
    (show Differentiable ℝ _ from fun x ↦ (exponential_right_hasDerivAt c x).differentiableAt).continuous
  simpa [quadraticExponentialJoin] using joinAt_continuous_iff (k := 0) (flag := true) hl hr

/-- Bài 10(b): khả vi trên ℝ khi và chỉ khi `b = 1`, `c = −1`; `a` tùy ý. -/
theorem source_differentiable_parameters_iff (a b c : ℝ) :
    Differentiable ℝ (quadraticExponentialJoin a b c) ↔ b = 1 ∧ c = -1 := by
  have hh := joinAt_differentiable_iff (k := 0) (flag := true)
    (quadratic_left_hasDerivAt a b) (exponential_right_hasDerivAt c)
  change Differentiable ℝ (quadraticExponentialJoin a b c) ↔ _ at hh
  constructor
  · intro hf
    have h := hh.mp hf
    refine ⟨by simpa using h.1, ?_⟩
    have hd : (0 : ℝ) = 1 + c := by simpa using h.2
    linarith
  · rintro ⟨hb, hc⟩
    apply hh.mpr
    simp [hb, hc]

def quadraticExponentialDerivative (a : ℝ) : ℝ → ℝ :=
  joinAt 0 true (fun x ↦ 2 * a * x) (fun x ↦ Real.exp x - 1)

theorem quadraticExponentialJoin_hasDerivAt_zero (a : ℝ) :
    HasDerivAt (quadraticExponentialJoin a 1 (-1)) 0 0 := by
  apply joinAt_hasDerivAt
  · simpa using quadratic_left_hasDerivAt a 1 0
  · simpa using exponential_right_hasDerivAt (-1) 0
  · simp

theorem quadraticExponentialJoin_derivative (a : ℝ) :
    deriv (quadraticExponentialJoin a 1 (-1)) = quadraticExponentialDerivative a := by
  funext x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hd := (joinAt_hasDerivAt_of_lt (flag := true) (r := fun y ↦ Real.exp y + (-1) * y)
      hx (quadratic_left_hasDerivAt a 1 x)).deriv
    simpa only [quadraticExponentialJoin, quadraticExponentialDerivative, joinAt_of_lt hx] using hd
  · simpa [quadraticExponentialDerivative, joinAt] using (quadraticExponentialJoin_hasDerivAt_zero a).deriv
  · have hd := (joinAt_hasDerivAt_of_gt (flag := true) (l := fun y ↦ a * y ^ 2 + 1)
      hx (exponential_right_hasDerivAt (-1) x)).deriv
    simpa [quadraticExponentialJoin, quadraticExponentialDerivative, joinAt_of_gt hx, sub_eq_add_neg] using hd

theorem quadraticExponentialDerivative_differentiable_iff (a : ℝ) :
    Differentiable ℝ (quadraticExponentialDerivative a) ↔ 2 * a = 1 := by
  have hl (x : ℝ) : HasDerivAt (fun y : ℝ ↦ 2 * a * y) (2 * a) x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (2 * a)
  have hr (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.exp y - 1) (Real.exp x) x :=
    (Real.hasDerivAt_exp x).sub_const 1
  simpa [quadraticExponentialDerivative] using
    joinAt_differentiable_iff (k := 0) (flag := true) hl hr

/-- Bài 10(c): khả vi hai lần khi và chỉ khi `a = 1/2`, `b = 1`, `c = −1`. -/
theorem source_twice_differentiable_parameters_iff (a b c : ℝ) :
    DifferentiableToOrderOn 2 (quadraticExponentialJoin a b c) univ ↔
      a = 1 / 2 ∧ b = 1 ∧ c = -1 := by
  rw [differentiableToOrderOn_two _ isOpen_univ]
  simp only [differentiableOn_univ]
  constructor
  · rintro ⟨hf, hd⟩
    obtain ⟨hb, hc⟩ := (source_differentiable_parameters_iff a b c).mp hf
    subst b
    subst c
    rw [quadraticExponentialJoin_derivative] at hd
    have ha := (quadraticExponentialDerivative_differentiable_iff a).mp hd
    exact ⟨by linarith, rfl, rfl⟩
  · rintro ⟨ha, hb, hc⟩
    subst a
    subst b
    subst c
    refine ⟨(source_differentiable_parameters_iff _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
    rw [quadraticExponentialJoin_derivative]
    apply (quadraticExponentialDerivative_differentiable_iff _).mpr
    norm_num

end calculus.Chapter04.Section01PolynomialExponentialMatching
