import calculus.Chapter04.Section04RationalFunctionInvestigationSupport
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bài 4.4.14(h): khảo sát ln|1+x|/(1+x)²

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2758–2768.
-/

set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04LogarithmicFunctionInvestigationExercise
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03
open calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section04ConvexityAndInflection
open calculus.Chapter04.Section04RationalFunctionInvestigationSupport
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin
open calculus.Chapter04.Section04AsymptoteClassificationSupport

def logAbsAddOneDivAddOneSq (x : ℝ) : ℝ := Real.log |x + 1| / (x + 1) ^ 2

def logAbsAddOneDivAddOneSqDomain : Set ℝ := {x | x ≠ -1}

def logAbsAddOneDivAddOneSqFirstDeriv (x : ℝ) : ℝ := (1 - 2 * Real.log |x + 1|) / (x + 1) ^ 3

def logAbsAddOneDivAddOneSqSecondDeriv (x : ℝ) : ℝ := (6 * Real.log |x + 1| - 5) / (x + 1) ^ 4

def logAbsAddOneDivAddOneSqCriticalOffset : ℝ := Real.exp (1 / 2)

def logAbsAddOneDivAddOneSqInflectionOffset : ℝ := Real.exp (5 / 6)

def logAbsAddOneDivAddOneSqMaximumValue : ℝ := 1 / (2 * Real.exp 1)

theorem logAbsAddOneDivAddOneSq_domain_iff (x : ℝ) :
    x ∈ logAbsAddOneDivAddOneSqDomain ↔ 0 < |x + 1| ∧ (x + 1) ^ 2 ≠ 0 := by
  change x ≠ -1 ↔ _
  constructor
  · intro hx
    have hd : x + 1 ≠ 0 := by
      intro hzero
      apply hx
      linarith
    exact ⟨abs_pos.mpr hd, pow_ne_zero 2 hd⟩
  · rintro ⟨h, _⟩
    intro hx
    subst x
    norm_num at h

theorem logAbsAddOneDivAddOneSq_domain_open : IsOpen logAbsAddOneDivAddOneSqDomain := isOpen_ne

theorem logAbsAddOneDivAddOneSqOffsets_positive :
    0 < logAbsAddOneDivAddOneSqCriticalOffset ∧ 0 < logAbsAddOneDivAddOneSqInflectionOffset ∧
      logAbsAddOneDivAddOneSqCriticalOffset < logAbsAddOneDivAddOneSqInflectionOffset := by
  refine ⟨Real.exp_pos _, Real.exp_pos _, ?_⟩
  exact Real.exp_lt_exp.mpr (by norm_num)

theorem logAbsAddOneDivAddOneSq_log_hasDerivAt {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    HasDerivAt (fun y : ℝ ↦ Real.log |y + 1|) (x + 1)⁻¹ x := by
  have hd : x + 1 ≠ 0 := by
    change x ≠ -1 at hx
    intro hzero
    apply hx
    linarith
  simpa only [Real.log_abs, Function.comp_def, id_eq, mul_one] using!
    (Real.hasDerivAt_log hd).comp x ((hasDerivAt_id x).add_const 1)

theorem logAbsAddOneDivAddOneSq_hasDerivAt {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    HasDerivAt logAbsAddOneDivAddOneSq (logAbsAddOneDivAddOneSqFirstDeriv x) x := by
  have hd : x + 1 ≠ 0 := by
    change x ≠ -1 at hx
    intro hzero
    apply hx
    linarith
  have h := (logAbsAddOneDivAddOneSq_log_hasDerivAt hx).div
    (((hasDerivAt_id x).add_const 1).fun_pow 2) (pow_ne_zero 2 hd)
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  apply h.congr_deriv
  unfold logAbsAddOneDivAddOneSqFirstDeriv
  field_simp [hd]

theorem logAbsAddOneDivAddOneSqFirstDeriv_hasDerivAt {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    HasDerivAt logAbsAddOneDivAddOneSqFirstDeriv (logAbsAddOneDivAddOneSqSecondDeriv x) x := by
  have hd : x + 1 ≠ 0 := by
    change x ≠ -1 at hx
    intro hzero
    apply hx
    linarith
  have h := (((logAbsAddOneDivAddOneSq_log_hasDerivAt hx).const_mul 2).const_sub 1).div
    (((hasDerivAt_id x).add_const 1).fun_pow 3) (pow_ne_zero 3 hd)
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  apply h.congr_deriv
  unfold logAbsAddOneDivAddOneSqSecondDeriv
  field_simp [hd]
  ring

theorem logAbsAddOneDivAddOneSq_second_hasDerivAt {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    HasDerivAt (deriv logAbsAddOneDivAddOneSq) (logAbsAddOneDivAddOneSqSecondDeriv x) x :=
  hasDerivAt_deriv_of_open_formula logAbsAddOneDivAddOneSq_domain_open hx
    (fun _ hy ↦ logAbsAddOneDivAddOneSq_hasDerivAt hy) (logAbsAddOneDivAddOneSqFirstDeriv_hasDerivAt hx)

theorem logAbsAddOneDivAddOneSq_deriv {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    deriv logAbsAddOneDivAddOneSq x = logAbsAddOneDivAddOneSqFirstDeriv x := (logAbsAddOneDivAddOneSq_hasDerivAt hx).deriv

theorem logAbsAddOneDivAddOneSq_second_deriv {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    deriv (deriv logAbsAddOneDivAddOneSq) x = logAbsAddOneDivAddOneSqSecondDeriv x :=
  (logAbsAddOneDivAddOneSq_second_hasDerivAt hx).deriv

theorem logAbsAddOneDivAddOneSq_second_continuousAt {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    ContinuousAt (deriv (deriv logAbsAddOneDivAddOneSq)) x := by
  have hd : x + 1 ≠ 0 := by
    change x ≠ -1 at hx
    intro hzero
    apply hx
    linarith
  have hc : ContinuousAt logAbsAddOneDivAddOneSqSecondDeriv x := by
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log |y + 1|) x :=
      (logAbsAddOneDivAddOneSq_log_hasDerivAt hx).continuousAt
    exact ((hlog.const_mul 6).sub_const 5).div
      ((continuousAt_id.add_const 1).pow 4) (pow_ne_zero 4 hd)
  apply hc.congr_of_eventuallyEq
  filter_upwards [logAbsAddOneDivAddOneSq_domain_open.mem_nhds hx] with y hy
  exact logAbsAddOneDivAddOneSq_second_deriv hy

theorem logAbsAddOneDivAddOneSq_abs_exp_iff (x a : ℝ) :
    |x + 1| = Real.exp a ↔ x = -1 - Real.exp a ∨ x = -1 + Real.exp a := by
  rw [abs_eq (Real.exp_pos a).le]
  constructor
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

theorem logAbsAddOneDivAddOneSq_log_eq_iff {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) (a : ℝ) :
    Real.log |x + 1| = a ↔ x = -1 - Real.exp a ∨ x = -1 + Real.exp a := by
  have hp := ((logAbsAddOneDivAddOneSq_domain_iff x).mp hx).1
  rw [← logAbsAddOneDivAddOneSq_abs_exp_iff x a]
  constructor
  · intro h
    have he := congrArg Real.exp h
    simpa only [Real.exp_log hp] using he
  · intro h
    rw [h, Real.log_exp]

theorem logAbsAddOneDivAddOneSq_stationary_iff {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    deriv logAbsAddOneDivAddOneSq x = 0 ↔
      x = -1 - logAbsAddOneDivAddOneSqCriticalOffset ∨ x = -1 + logAbsAddOneDivAddOneSqCriticalOffset := by
  have hd : x + 1 ≠ 0 := by
    change x ≠ -1 at hx
    intro hzero
    apply hx
    linarith
  rw [logAbsAddOneDivAddOneSq_deriv hx]
  unfold logAbsAddOneDivAddOneSqFirstDeriv logAbsAddOneDivAddOneSqCriticalOffset
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact (logAbsAddOneDivAddOneSq_log_eq_iff hx (1 / 2)).mp (by linarith)
    · exact False.elim (pow_ne_zero 3 hd h)
  · intro h
    have hl := (logAbsAddOneDivAddOneSq_log_eq_iff hx (1 / 2)).mpr h
    exact Or.inl (by linarith)

theorem logAbsAddOneDivAddOneSq_first_signs {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    (x < -1 - logAbsAddOneDivAddOneSqCriticalOffset → 0 < deriv logAbsAddOneDivAddOneSq x) ∧
      (x ∈ Ioo (-1 - logAbsAddOneDivAddOneSqCriticalOffset) (-1) → deriv logAbsAddOneDivAddOneSq x < 0) ∧
      (x ∈ Ioo (-1) (-1 + logAbsAddOneDivAddOneSqCriticalOffset) → 0 < deriv logAbsAddOneDivAddOneSq x) ∧
      (-1 + logAbsAddOneDivAddOneSqCriticalOffset < x → deriv logAbsAddOneDivAddOneSq x < 0) := by
  have hr := logAbsAddOneDivAddOneSqOffsets_positive.1
  have hp := ((logAbsAddOneDivAddOneSq_domain_iff x).mp hx).1
  rw [logAbsAddOneDivAddOneSq_deriv hx]
  unfold logAbsAddOneDivAddOneSqFirstDeriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hd : x + 1 < 0 := by linarith
    have ha : logAbsAddOneDivAddOneSqCriticalOffset < |x + 1| := by rw [abs_of_neg hd]; linarith
    have hl : (1 / 2 : ℝ) < Real.log |x + 1| := (Real.lt_log_iff_exp_lt hp).mpr ha
    exact div_pos_of_neg_of_neg (by linarith)
      (by rw [pow_succ]; exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hd.ne) hd)
  · intro h
    have hd : x + 1 < 0 := by linarith [h.2]
    have ha : |x + 1| < logAbsAddOneDivAddOneSqCriticalOffset := by rw [abs_of_neg hd]; linarith [h.1]
    have hl : Real.log |x + 1| < (1 / 2 : ℝ) := (Real.log_lt_iff_lt_exp hp).mpr ha
    exact div_neg_of_pos_of_neg (by linarith)
      (by rw [pow_succ]; exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hd.ne) hd)
  · intro h
    have hd : 0 < x + 1 := by linarith [h.1]
    have ha : |x + 1| < logAbsAddOneDivAddOneSqCriticalOffset := by rw [abs_of_pos hd]; linarith [h.2]
    have hl : Real.log |x + 1| < (1 / 2 : ℝ) := (Real.log_lt_iff_lt_exp hp).mpr ha
    exact div_pos (by linarith) (pow_pos hd 3)
  · intro h
    have hd : 0 < x + 1 := by linarith
    have ha : logAbsAddOneDivAddOneSqCriticalOffset < |x + 1| := by rw [abs_of_pos hd]; linarith
    have hl : (1 / 2 : ℝ) < Real.log |x + 1| := (Real.lt_log_iff_exp_lt hp).mpr ha
    exact div_neg_of_neg_of_pos (by linarith) (pow_pos hd 3)

theorem logAbsAddOneDivAddOneSq_variation :
    StrictMonoOn logAbsAddOneDivAddOneSq (Iic (-1 - logAbsAddOneDivAddOneSqCriticalOffset)) ∧
      StrictAntiOn logAbsAddOneDivAddOneSq (Ico (-1 - logAbsAddOneDivAddOneSqCriticalOffset) (-1)) ∧
      StrictMonoOn logAbsAddOneDivAddOneSq (Ioc (-1) (-1 + logAbsAddOneDivAddOneSqCriticalOffset)) ∧
      StrictAntiOn logAbsAddOneDivAddOneSq (Ici (-1 + logAbsAddOneDivAddOneSqCriticalOffset)) := by
  have hr := logAbsAddOneDivAddOneSqOffsets_positive.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Iic _)
      (fun x hx ↦ (logAbsAddOneDivAddOneSq_hasDerivAt (by change x ≠ -1; linarith [mem_Iic.mp hx])).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Iic] at hx
    exact (logAbsAddOneDivAddOneSq_first_signs (by change x ≠ -1; change x < -1 - logAbsAddOneDivAddOneSqCriticalOffset at hx; intro hzero; linarith)).1 hx
  · apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
      (fun x hx ↦ (logAbsAddOneDivAddOneSq_hasDerivAt hx.2.ne).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ico] at hx
    exact (logAbsAddOneDivAddOneSq_first_signs hx.2.ne).2.1 hx
  · apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
      (fun x hx ↦ (logAbsAddOneDivAddOneSq_hasDerivAt hx.1.ne').continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ioc] at hx
    exact (logAbsAddOneDivAddOneSq_first_signs hx.1.ne').2.2.1 hx
  · apply strictAntiOn_of_deriv_neg (convex_Ici _)
      (fun x hx ↦ (logAbsAddOneDivAddOneSq_hasDerivAt (by change x ≠ -1; linarith [mem_Ici.mp hx])).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    exact (logAbsAddOneDivAddOneSq_first_signs (by change x ≠ -1; change -1 + logAbsAddOneDivAddOneSqCriticalOffset < x at hx; intro hzero; linarith)).2.2.2 hx

theorem logAbsAddOneDivAddOneSq_reflection (x : ℝ) : logAbsAddOneDivAddOneSq (-2 - x) = logAbsAddOneDivAddOneSq x := by
  have harg : -2 - x + 1 = -(x + 1) := by ring
  simp only [logAbsAddOneDivAddOneSq, harg, abs_neg, neg_sq]

theorem logAbsAddOneDivAddOneSq_exp_values (a : ℝ) :
    logAbsAddOneDivAddOneSq (-1 - Real.exp a) = a / Real.exp (2 * a) ∧
      logAbsAddOneDivAddOneSq (-1 + Real.exp a) = a / Real.exp (2 * a) := by
  have he : Real.exp a ^ 2 = Real.exp (2 * a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  constructor
  · have harg : -1 - Real.exp a + 1 = -Real.exp a := by ring
    simp only [logAbsAddOneDivAddOneSq, harg, abs_neg, abs_of_pos (Real.exp_pos a), Real.log_exp, neg_sq, he]
  · have harg : -1 + Real.exp a + 1 = Real.exp a := by ring
    simp only [logAbsAddOneDivAddOneSq, harg, abs_of_pos (Real.exp_pos a), Real.log_exp, he]

theorem logAbsAddOneDivAddOneSq_critical_values :
    logAbsAddOneDivAddOneSq (-1 - logAbsAddOneDivAddOneSqCriticalOffset) = logAbsAddOneDivAddOneSqMaximumValue ∧
      logAbsAddOneDivAddOneSq (-1 + logAbsAddOneDivAddOneSqCriticalOffset) = logAbsAddOneDivAddOneSqMaximumValue := by
  have h := logAbsAddOneDivAddOneSq_exp_values (1 / 2)
  norm_num at h
  unfold logAbsAddOneDivAddOneSqCriticalOffset logAbsAddOneDivAddOneSqMaximumValue
  constructor
  · rw [h.1]; ring
  · rw [h.2]; ring

theorem logAbsAddOneDivAddOneSq_global_bound {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    logAbsAddOneDivAddOneSq x ≤ logAbsAddOneDivAddOneSqMaximumValue := by
  have hr := logAbsAddOneDivAddOneSqOffsets_positive.1
  change x ≠ -1 at hx
  rcases lt_or_gt_of_ne hx with hl | hu
  · by_cases hc : x ≤ -1 - logAbsAddOneDivAddOneSqCriticalOffset
    · rw [← logAbsAddOneDivAddOneSq_critical_values.1]
      exact logAbsAddOneDivAddOneSq_variation.1.monotoneOn (mem_Iic.mpr hc) (mem_Iic.mpr (le_refl _)) hc
    · rw [← logAbsAddOneDivAddOneSq_critical_values.1]
      exact logAbsAddOneDivAddOneSq_variation.2.1.antitoneOn ⟨le_refl _, by linarith⟩
        ⟨(lt_of_not_ge hc).le, hl⟩ (lt_of_not_ge hc).le
  · by_cases hc : x ≤ -1 + logAbsAddOneDivAddOneSqCriticalOffset
    · rw [← logAbsAddOneDivAddOneSq_critical_values.2]
      exact logAbsAddOneDivAddOneSq_variation.2.2.1.monotoneOn ⟨hu, hc⟩ ⟨by linarith, le_refl _⟩ hc
    · rw [← logAbsAddOneDivAddOneSq_critical_values.2]
      exact logAbsAddOneDivAddOneSq_variation.2.2.2.antitoneOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr (lt_of_not_ge hc).le) (lt_of_not_ge hc).le

theorem logAbsAddOneDivAddOneSq_extrema :
    (∀ x : ℝ, IsLocalMaximumOn logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain x ↔
      x = -1 - logAbsAddOneDivAddOneSqCriticalOffset ∨ x = -1 + logAbsAddOneDivAddOneSqCriticalOffset) ∧
      (∀ x : ℝ, ¬ IsLocalMinimumOn logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain x) := by
  have hr := logAbsAddOneDivAddOneSqOffsets_positive.1
  have hmaxL : IsLocalMaximumOn logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain (-1 - logAbsAddOneDivAddOneSqCriticalOffset) := by
    refine ⟨by change -1 - logAbsAddOneDivAddOneSqCriticalOffset ≠ -1; linarith, 1, by norm_num, ?_⟩
    intro x hx
    rw [logAbsAddOneDivAddOneSq_critical_values.1]
    exact logAbsAddOneDivAddOneSq_global_bound hx.2
  have hmaxR : IsLocalMaximumOn logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain (-1 + logAbsAddOneDivAddOneSqCriticalOffset) := by
    refine ⟨by change -1 + logAbsAddOneDivAddOneSqCriticalOffset ≠ -1; linarith, 1, by norm_num, ?_⟩
    intro x hx
    rw [logAbsAddOneDivAddOneSq_critical_values.2]
    exact logAbsAddOneDivAddOneSq_global_bound hx.2
  have hnL : ¬ IsLocalMinimumOn logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain (-1 - logAbsAddOneDivAddOneSqCriticalOffset) := by
    apply no_local_minimum_of_right_decrease (b := -1) (by linarith)
    · intro x hx; exact hx.2.ne
    · intro x hx
      exact logAbsAddOneDivAddOneSq_variation.2.1 ⟨le_refl _, by linarith⟩ ⟨hx.1.le, hx.2⟩ hx.1
  have hnR : ¬ IsLocalMinimumOn logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain (-1 + logAbsAddOneDivAddOneSqCriticalOffset) := by
    apply no_local_minimum_of_right_decrease (b := logAbsAddOneDivAddOneSqCriticalOffset) (by linarith)
    · intro x hx; change x ≠ -1; linarith [hx.1]
    · intro x hx
      exact logAbsAddOneDivAddOneSq_variation.2.2.2 (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx.1.le) hx.1
  constructor
  · intro x
    constructor
    · intro h
      exact (logAbsAddOneDivAddOneSq_stationary_iff h.1).mp
        (fermat logAbsAddOneDivAddOneSq_domain_open (Or.inr h) (logAbsAddOneDivAddOneSq_hasDerivAt h.1).differentiableAt)
    · rintro (rfl | rfl)
      · exact hmaxL
      · exact hmaxR
  · intro x h
    have he := (logAbsAddOneDivAddOneSq_stationary_iff h.1).mp
      (fermat logAbsAddOneDivAddOneSq_domain_open (Or.inl h) (logAbsAddOneDivAddOneSq_hasDerivAt h.1).differentiableAt)
    rcases he with he | he
    · subst x; exact hnL h
    · subst x; exact hnR h

theorem logAbsAddOneDivAddOneSq_second_signs {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    (deriv (deriv logAbsAddOneDivAddOneSq) x < 0 ↔ |x + 1| < logAbsAddOneDivAddOneSqInflectionOffset) ∧
      (0 < deriv (deriv logAbsAddOneDivAddOneSq) x ↔ logAbsAddOneDivAddOneSqInflectionOffset < |x + 1|) ∧
      (deriv (deriv logAbsAddOneDivAddOneSq) x = 0 ↔
        x = -1 - logAbsAddOneDivAddOneSqInflectionOffset ∨ x = -1 + logAbsAddOneDivAddOneSqInflectionOffset) := by
  have hp := ((logAbsAddOneDivAddOneSq_domain_iff x).mp hx).1
  have hd : x + 1 ≠ 0 := by
    change x ≠ -1 at hx
    intro hzero
    apply hx
    linarith
  have hb : 0 < (x + 1) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hd) 2
  rw [logAbsAddOneDivAddOneSq_second_deriv hx]
  unfold logAbsAddOneDivAddOneSqSecondDeriv logAbsAddOneDivAddOneSqInflectionOffset
  constructor
  · rw [div_lt_iff₀ hb, ← Real.log_lt_iff_lt_exp hp]
    constructor <;> intro h <;> linarith
  constructor
  · rw [lt_div_iff₀ hb, ← Real.lt_log_iff_exp_lt hp]
    constructor <;> intro h <;> linarith
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · exact (logAbsAddOneDivAddOneSq_log_eq_iff hx (5 / 6)).mp (by linarith)
      · exact False.elim (hb.ne' h)
    · intro h
      have hl := (logAbsAddOneDivAddOneSq_log_eq_iff hx (5 / 6)).mpr h
      exact Or.inl (by linarith)

theorem logAbsAddOneDivAddOneSq_convexity :
    ConvexOn ℝ (Iio (-1 - logAbsAddOneDivAddOneSqInflectionOffset)) logAbsAddOneDivAddOneSq ∧
      ConcaveOnOpenInterval logAbsAddOneDivAddOneSq (-1 - logAbsAddOneDivAddOneSqInflectionOffset) (-1) ∧
      ConcaveOnOpenInterval logAbsAddOneDivAddOneSq (-1) (-1 + logAbsAddOneDivAddOneSqInflectionOffset) ∧
      ConvexOn ℝ (Ioi (-1 + logAbsAddOneDivAddOneSqInflectionOffset)) logAbsAddOneDivAddOneSq := by
  have hr := logAbsAddOneDivAddOneSqOffsets_positive.2.1
  have hf := fun (x : ℝ) (hx : x ∈ logAbsAddOneDivAddOneSqDomain) ↦ (logAbsAddOneDivAddOneSq_hasDerivAt hx).differentiableAt
  have hg := fun (x : ℝ) (hx : x ∈ logAbsAddOneDivAddOneSqDomain) ↦ (logAbsAddOneDivAddOneSq_second_hasDerivAt hx).differentiableAt
  have hL : Iio (-1 - logAbsAddOneDivAddOneSqInflectionOffset) ⊆ logAbsAddOneDivAddOneSqDomain := by
    intro x hx; change x ≠ -1; linarith [mem_Iio.mp hx]
  have hLM : Ioo (-1 - logAbsAddOneDivAddOneSqInflectionOffset) (-1) ⊆ logAbsAddOneDivAddOneSqDomain := fun _ hx ↦ hx.2.ne
  have hRM : Ioo (-1) (-1 + logAbsAddOneDivAddOneSqInflectionOffset) ⊆ logAbsAddOneDivAddOneSqDomain := fun _ hx ↦ hx.1.ne'
  have hR : Ioi (-1 + logAbsAddOneDivAddOneSqInflectionOffset) ⊆ logAbsAddOneDivAddOneSqDomain := by
    intro x hx; change x ≠ -1; linarith [mem_Ioi.mp hx]
  refine ⟨convexOn_of_deriv2_nonneg' (convex_Iio _) (fun x hx ↦ (hf x (hL hx)).differentiableWithinAt)
    (fun x hx ↦ (hg x (hL hx)).differentiableWithinAt) ?_,
    concaveOnOpenInterval_of_second_deriv_nonpos _ _ _ (source_two_of_pointwise hLM hf hg) ?_,
    concaveOnOpenInterval_of_second_deriv_nonpos _ _ _ (source_two_of_pointwise hRM hf hg) ?_,
    convexOn_of_deriv2_nonneg' (convex_Ioi _) (fun x hx ↦ (hf x (hR hx)).differentiableWithinAt)
      (fun x hx ↦ (hg x (hR hx)).differentiableWithinAt) ?_⟩
  · intro x hx
    have hs := (logAbsAddOneDivAddOneSq_second_signs (hL hx)).2.1.mpr
      (by rw [abs_of_neg (show x + 1 < 0 by linarith [mem_Iio.mp hx])]; linarith [mem_Iio.mp hx])
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hs.le
  · intro x hx
    exact ((logAbsAddOneDivAddOneSq_second_signs (hLM hx)).1.mpr
      (by rw [abs_of_neg (show x + 1 < 0 by linarith [hx.2])]; linarith [hx.1])).le
  · intro x hx
    exact ((logAbsAddOneDivAddOneSq_second_signs (hRM hx)).1.mpr
      (by rw [abs_of_pos (show 0 < x + 1 by linarith [hx.1])]; linarith [hx.2])).le
  · intro x hx
    have hs := (logAbsAddOneDivAddOneSq_second_signs (hR hx)).2.1.mpr
      (by rw [abs_of_pos (show 0 < x + 1 by linarith [mem_Ioi.mp hx])]; linarith [mem_Ioi.mp hx])
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hs.le

theorem logAbsAddOneDivAddOneSq_inflections_sufficient :
    (∃ a b : ℝ, Ioo a b ⊆ logAbsAddOneDivAddOneSqDomain ∧
      SourceInflectionOn logAbsAddOneDivAddOneSq a b (-1 - logAbsAddOneDivAddOneSqInflectionOffset)) ∧
      (∃ a b : ℝ, Ioo a b ⊆ logAbsAddOneDivAddOneSqDomain ∧
        SourceInflectionOn logAbsAddOneDivAddOneSq a b (-1 + logAbsAddOneDivAddOneSqInflectionOffset)) := by
  have hr := logAbsAddOneDivAddOneSqOffsets_positive.2.1
  let δ : ℝ := logAbsAddOneDivAddOneSqInflectionOffset / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hf := fun (x : ℝ) (hx : x ∈ logAbsAddOneDivAddOneSqDomain) ↦ (logAbsAddOneDivAddOneSq_hasDerivAt hx).differentiableAt
  have hg := fun (x : ℝ) (hx : x ∈ logAbsAddOneDivAddOneSqDomain) ↦ (logAbsAddOneDivAddOneSq_second_hasDerivAt hx).differentiableAt
  have hL : Ioo (-1 - logAbsAddOneDivAddOneSqInflectionOffset - δ) (-1 - logAbsAddOneDivAddOneSqInflectionOffset + δ) ⊆ logAbsAddOneDivAddOneSqDomain := by
    intro x hx; change x ≠ -1; dsimp [δ] at hx; linarith [hx.2]
  have hR : Ioo (-1 + logAbsAddOneDivAddOneSqInflectionOffset - δ) (-1 + logAbsAddOneDivAddOneSqInflectionOffset + δ) ⊆ logAbsAddOneDivAddOneSqDomain := by
    intro x hx; change x ≠ -1; dsimp [δ] at hx; linarith [hx.1]
  constructor
  · refine ⟨_, _, hL, sourceInflectionOn_of_second_deriv_pos_neg hδ
      (source_two_of_pointwise (fun x hx ↦ hL ⟨hx.1, by linarith [hx.2]⟩) hf hg)
      (source_two_of_pointwise (fun x hx ↦ hL ⟨by linarith [hx.1], hx.2⟩) hf hg)
      (Or.inl (hf _ (by change -1 - logAbsAddOneDivAddOneSqInflectionOffset ≠ -1; linarith))) ?_ ?_⟩
    · intro x hx
      exact (logAbsAddOneDivAddOneSq_second_signs (by change x ≠ -1; linarith [hx.2])).2.1.mpr
        (by rw [abs_of_neg (show x + 1 < 0 by linarith [hx.2])]; linarith [hx.2])
    · intro x hx
      have hxneg : x + 1 < 0 := by dsimp [δ] at hx; linarith [hx.2]
      exact (logAbsAddOneDivAddOneSq_second_signs (by change x ≠ -1; linarith)).1.mpr
        (by rw [abs_of_neg hxneg]; linarith [hx.1])
  · refine ⟨_, _, hR, sourceInflectionOn_of_second_deriv_neg_pos hδ
      (source_two_of_pointwise (fun x hx ↦ hR ⟨hx.1, by linarith [hx.2]⟩) hf hg)
      (source_two_of_pointwise (fun x hx ↦ hR ⟨by linarith [hx.1], hx.2⟩) hf hg)
      (Or.inl (hf _ (by change -1 + logAbsAddOneDivAddOneSqInflectionOffset ≠ -1; linarith))) ?_ ?_⟩
    · intro x hx
      have hxpos : 0 < x + 1 := by dsimp [δ] at hx; linarith [hx.1]
      exact (logAbsAddOneDivAddOneSq_second_signs (by change x ≠ -1; linarith)).1.mpr
        (by rw [abs_of_pos hxpos]; linarith [hx.2])
    · intro x hx
      exact (logAbsAddOneDivAddOneSq_second_signs (by change x ≠ -1; linarith [hx.1])).2.1.mpr
        (by rw [abs_of_pos (show 0 < x + 1 by linarith [hx.1])]; linarith [hx.1])

theorem logAbsAddOneDivAddOneSq_inflection_iff (c : ℝ) :
    (∃ a b : ℝ, Ioo a b ⊆ logAbsAddOneDivAddOneSqDomain ∧ SourceInflectionOn logAbsAddOneDivAddOneSq a b c) ↔
      c = -1 - logAbsAddOneDivAddOneSqInflectionOffset ∨ c = -1 + logAbsAddOneDivAddOneSqInflectionOffset := by
  constructor
  · rintro ⟨a, b, hI, hu⟩
    exact (logAbsAddOneDivAddOneSq_second_signs (hI hu.1)).2.2.mp
      (second_zero_of_sourceInflection hI
        (fun _ hx ↦ (logAbsAddOneDivAddOneSq_hasDerivAt hx).differentiableAt)
        (fun _ hx ↦ (logAbsAddOneDivAddOneSq_second_hasDerivAt hx).differentiableAt)
        (logAbsAddOneDivAddOneSq_second_continuousAt (hI hu.1)) hu)
  · rintro (rfl | rfl)
    · exact logAbsAddOneDivAddOneSq_inflections_sufficient.1
    · exact logAbsAddOneDivAddOneSq_inflections_sufficient.2

theorem logAbsAddOneDivAddOneSq_inflection_values :
    logAbsAddOneDivAddOneSq (-1 - logAbsAddOneDivAddOneSqInflectionOffset) = 5 / (6 * Real.exp (5 / 3)) ∧
      logAbsAddOneDivAddOneSq (-1 + logAbsAddOneDivAddOneSqInflectionOffset) = 5 / (6 * Real.exp (5 / 3)) := by
  have h := logAbsAddOneDivAddOneSq_exp_values (5 / 6)
  norm_num at h
  unfold logAbsAddOneDivAddOneSqInflectionOffset
  constructor
  · rw [h.1]; ring
  · rw [h.2]; ring

theorem logAbsAddOneDivAddOneSq_zero_iff {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    logAbsAddOneDivAddOneSq x = 0 ↔ x = -2 ∨ x = 0 := by
  have hd := ((logAbsAddOneDivAddOneSq_domain_iff x).mp hx).2
  unfold logAbsAddOneDivAddOneSq
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have he := (logAbsAddOneDivAddOneSq_log_eq_iff hx 0).mp h
      simp only [Real.exp_zero] at he
      rcases he with he | he
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · exact False.elim (hd h)
  · rintro (rfl | rfl) <;> norm_num

theorem logAbsAddOneDivAddOneSq_signs {x : ℝ} (hx : x ∈ logAbsAddOneDivAddOneSqDomain) :
    (logAbsAddOneDivAddOneSq x < 0 ↔ -2 < x ∧ x < 0) ∧
      (0 < logAbsAddOneDivAddOneSq x ↔ x < -2 ∨ 0 < x) := by
  have hp := ((logAbsAddOneDivAddOneSq_domain_iff x).mp hx).1
  have hd : 0 < (x + 1) ^ 2 := sq_pos_of_ne_zero (show x + 1 ≠ 0 from by
      change x ≠ -1 at hx
      intro hzero
      apply hx
      linarith)
  unfold logAbsAddOneDivAddOneSq
  constructor
  · rw [div_lt_iff₀ hd, zero_mul, Real.log_neg_iff hp, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · rw [lt_div_iff₀ hd, zero_mul, Real.log_pos_iff hp.le, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)

theorem logAbsAddOneDivAddOneSq_pole {F : Filter ℝ}
    (hi : Tendsto (fun x : ℝ ↦ x + 1) F (𝓝 0))
    (hD : ∀ᶠ x : ℝ in F, x ∈ logAbsAddOneDivAddOneSqDomain) :
    Tendsto logAbsAddOneDivAddOneSq F atBot := by
  have ha : Tendsto (fun x : ℝ ↦ |x + 1|) F (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using hi.abs, hD.mono fun x hx ↦ ((logAbsAddOneDivAddOneSq_domain_iff x).mp hx).1⟩
  have hs : Tendsto (fun x : ℝ ↦ (x + 1) ^ 2) F (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hi.pow 2, ?_⟩
    exact hD.mono fun x hx ↦ sq_pos_of_ne_zero (show x + 1 ≠ 0 from by
      change x ≠ -1 at hx
      intro hzero
      apply hx
      linarith)
  have h := (Real.tendsto_log_nhdsGT_zero.comp ha).atBot_mul_atTop₀
    (tendsto_inv_nhdsGT_zero.comp hs)
  exact h.congr fun x ↦ by dsimp [Function.comp_def, logAbsAddOneDivAddOneSq]; ring

theorem logAbsAddOneDivAddOneSq_pole_limits :
    Tendsto logAbsAddOneDivAddOneSq (𝓝[<] (-1 : ℝ)) atBot ∧
      Tendsto logAbsAddOneDivAddOneSq (𝓝[>] (-1 : ℝ)) atBot := by
  constructor
  · apply logAbsAddOneDivAddOneSq_pole
      (by simpa using (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ ↦ x) (𝓝[<] (-1 : ℝ)) (𝓝 (-1 : ℝ))).add_const 1)
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < -1)
    exact hx.ne
  · apply logAbsAddOneDivAddOneSq_pole
      (by simpa using (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ ↦ x) (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ))).add_const 1)
    filter_upwards [self_mem_nhdsWithin] with x (hx : -1 < x)
    exact hx.ne'

theorem logAbsAddOneDivAddOneSq_end_limit {F : Filter ℝ}
    (ha : Tendsto (fun x : ℝ ↦ |x + 1|) F atTop) : Tendsto logAbsAddOneDivAddOneSq F (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log |x + 1| / |x + 1|) F (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ha
  have hinv : Tendsto (fun x : ℝ ↦ |x + 1|⁻¹) F (𝓝 0) := tendsto_inv_atTop_zero.comp ha
  have h := hlog.mul hinv
  simp only [mul_zero] at h
  apply h.congr
  intro x
  change Real.log |x + 1| / |x + 1| * |x + 1|⁻¹ = Real.log |x + 1| / (x + 1) ^ 2
  rw [← sq_abs (x + 1)]
  ring

theorem logAbsAddOneDivAddOneSq_end_limits :
    Tendsto logAbsAddOneDivAddOneSq atTop (𝓝 0) ∧ Tendsto logAbsAddOneDivAddOneSq atBot (𝓝 0) := by
  constructor
  · apply logAbsAddOneDivAddOneSq_end_limit
    apply (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).congr'
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with x hx
    exact (abs_of_pos (by linarith : 0 < x + 1)).symm
  · apply logAbsAddOneDivAddOneSq_end_limit
    have harg : Tendsto (fun x : ℝ ↦ x + 1) atBot atBot := tendsto_atBot_add_const_right atBot 1 tendsto_id
    apply (tendsto_neg_atBot_atTop.comp harg).congr'
    filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
    exact (abs_of_neg (by linarith : x + 1 < 0)).symm

theorem logAbsAddOneDivAddOneSq_asymptotes :
    (∀ a : ℝ, HasVerticalAsymptoteWithinAt logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain a ↔ a = -1) ∧
      (∀ b : ℝ, HasHorizontalAsymptoteWithin logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain b ↔ b = 0) ∧
      (∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain m b) := by
  have hT : ∀ᶠ x : ℝ in atTop, x ∈ logAbsAddOneDivAddOneSqDomain :=
    (eventually_gt_atTop (-1 : ℝ)).mono fun _ hx ↦ hx.ne'
  have hB : ∀ᶠ x : ℝ in atBot, x ∈ logAbsAddOneDivAddOneSqDomain :=
    (eventually_lt_atBot (-1 : ℝ)).mono fun _ hx ↦ hx.ne
  constructor
  · intro a
    constructor
    · intro h
      by_contra hn
      exact no_vertical_of_continuousAt (logAbsAddOneDivAddOneSq_hasDerivAt hn).continuousAt h
    · rintro rfl
      apply vertical_of_right_bot _ logAbsAddOneDivAddOneSq_pole_limits.2
      filter_upwards [self_mem_nhdsWithin] with x (hx : -1 < x)
      exact hx.ne'
  constructor
  · intro b
    rw [full_tail_horizontal_iff hT hB, HasHorizontalAsymptote]
    constructor
    · rintro (h | h)
      · exact tendsto_nhds_unique h logAbsAddOneDivAddOneSq_end_limits.1
      · exact tendsto_nhds_unique h logAbsAddOneDivAddOneSq_end_limits.2
    · rintro rfl; exact Or.inl logAbsAddOneDivAddOneSq_end_limits.1
  · intro m b
    rw [full_tail_oblique_iff hT hB, HasObliqueAsymptote]
    rintro ⟨hm, h | h⟩
    · have hp : Tendsto (fun x : ℝ ↦ logAbsAddOneDivAddOneSq x - (0 * x + 0)) atTop (𝓝 0) := by
        simpa only [zero_mul, zero_add, sub_zero] using logAbsAddOneDivAddOneSq_end_limits.1
      exact hm ((affine_parameters_iff tendsto_inv_atTop_zero
        ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne') hp m b).mp h).1
    · have hp : Tendsto (fun x : ℝ ↦ logAbsAddOneDivAddOneSq x - (0 * x + 0)) atBot (𝓝 0) := by
        simpa only [zero_mul, zero_add, sub_zero] using logAbsAddOneDivAddOneSq_end_limits.2
      exact hm ((affine_parameters_iff tendsto_inv_atBot_zero
        ((eventually_lt_atBot (0 : ℝ)).mono fun _ hx ↦ hx.ne) hp m b).mp h).1

theorem logAbsAddOneDivAddOneSq_graph_iff (x y : ℝ) :
    (x ∈ logAbsAddOneDivAddOneSqDomain ∧ logAbsAddOneDivAddOneSq x = y) ↔
      x ≠ -1 ∧ (x + 1) ^ 2 * y = Real.log |x + 1| := by
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hx, by simpa only [mul_comm] using ((div_eq_iff ((logAbsAddOneDivAddOneSq_domain_iff x).mp hx).2).mp hy).symm⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, (div_eq_iff ((logAbsAddOneDivAddOneSq_domain_iff x).mp hx).2).mpr
      (by simpa only [mul_comm] using hy.symm)⟩

theorem logAbsAddOneDivAddOneSq_range (y : ℝ) :
    (∃ x ∈ logAbsAddOneDivAddOneSqDomain, logAbsAddOneDivAddOneSq x = y) ↔ y ≤ logAbsAddOneDivAddOneSqMaximumValue := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact logAbsAddOneDivAddOneSq_global_bound hx
  · intro hy
    have hr := logAbsAddOneDivAddOneSqOffsets_positive.1
    have hmem : ∀ᶠ x : ℝ in 𝓝[>] (-1 : ℝ), x ∈ Ioo (-1) (-1 + logAbsAddOneDivAddOneSqCriticalOffset) := by
      filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (show (-1 : ℝ) < -1 + logAbsAddOneDivAddOneSqCriticalOffset by linarith))]
        with x hx hu
      exact ⟨hx, hu⟩
    obtain ⟨a, ha, hay⟩ := (hmem.and (logAbsAddOneDivAddOneSq_pole_limits.2.eventually (eventually_lt_atBot y))).exists
    have hc : ContinuousOn logAbsAddOneDivAddOneSq (Icc a (-1 + logAbsAddOneDivAddOneSqCriticalOffset)) := by
      intro x hx
      exact (logAbsAddOneDivAddOneSq_hasDerivAt (by change x ≠ -1; linarith [ha.1, hx.1])).continuousAt.continuousWithinAt
    have him := intermediate_value_Icc ha.2.le hc
      (show y ∈ Icc (logAbsAddOneDivAddOneSq a) (logAbsAddOneDivAddOneSq (-1 + logAbsAddOneDivAddOneSqCriticalOffset)) from
        ⟨hay.le, by simpa only [logAbsAddOneDivAddOneSq_critical_values.2] using hy⟩)
    rcases him with ⟨x, hx, he⟩
    exact ⟨x, by change x ≠ -1; linarith [ha.1, hx.1], he⟩

/-- Bài 14(h): khảo sát `ln|1+x|/(1+x)²` trên `x ≠ −1`. -/
theorem source_logarithmic_function_investigation :
    (∀ x : ℝ, x ∈ logAbsAddOneDivAddOneSqDomain ↔ 0 < |x + 1| ∧ (x + 1) ^ 2 ≠ 0) ∧
      (∀ x ∈ logAbsAddOneDivAddOneSqDomain, HasDerivAt logAbsAddOneDivAddOneSq (logAbsAddOneDivAddOneSqFirstDeriv x) x ∧
        HasDerivAt (deriv logAbsAddOneDivAddOneSq) (logAbsAddOneDivAddOneSqSecondDeriv x) x) ∧
      (∀ x ∈ logAbsAddOneDivAddOneSqDomain, deriv logAbsAddOneDivAddOneSq x = 0 ↔
        x = -1 - logAbsAddOneDivAddOneSqCriticalOffset ∨ x = -1 + logAbsAddOneDivAddOneSqCriticalOffset) ∧
      (StrictMonoOn logAbsAddOneDivAddOneSq (Iic (-1 - logAbsAddOneDivAddOneSqCriticalOffset)) ∧
        StrictAntiOn logAbsAddOneDivAddOneSq (Ico (-1 - logAbsAddOneDivAddOneSqCriticalOffset) (-1)) ∧
        StrictMonoOn logAbsAddOneDivAddOneSq (Ioc (-1) (-1 + logAbsAddOneDivAddOneSqCriticalOffset)) ∧
        StrictAntiOn logAbsAddOneDivAddOneSq (Ici (-1 + logAbsAddOneDivAddOneSqCriticalOffset))) ∧
      ((∀ x : ℝ, IsLocalMaximumOn logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain x ↔
        x = -1 - logAbsAddOneDivAddOneSqCriticalOffset ∨ x = -1 + logAbsAddOneDivAddOneSqCriticalOffset) ∧
        ∀ x : ℝ, ¬ IsLocalMinimumOn logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain x) ∧
      (logAbsAddOneDivAddOneSq (-1 - logAbsAddOneDivAddOneSqCriticalOffset) = logAbsAddOneDivAddOneSqMaximumValue ∧
        logAbsAddOneDivAddOneSq (-1 + logAbsAddOneDivAddOneSqCriticalOffset) = logAbsAddOneDivAddOneSqMaximumValue) ∧
      (∀ x ∈ logAbsAddOneDivAddOneSqDomain, logAbsAddOneDivAddOneSq x ≤ logAbsAddOneDivAddOneSqMaximumValue) ∧
      (ConvexOn ℝ (Iio (-1 - logAbsAddOneDivAddOneSqInflectionOffset)) logAbsAddOneDivAddOneSq ∧
        ConcaveOnOpenInterval logAbsAddOneDivAddOneSq (-1 - logAbsAddOneDivAddOneSqInflectionOffset) (-1) ∧
        ConcaveOnOpenInterval logAbsAddOneDivAddOneSq (-1) (-1 + logAbsAddOneDivAddOneSqInflectionOffset) ∧
        ConvexOn ℝ (Ioi (-1 + logAbsAddOneDivAddOneSqInflectionOffset)) logAbsAddOneDivAddOneSq) ∧
      (∀ c : ℝ, (∃ a b : ℝ, Ioo a b ⊆ logAbsAddOneDivAddOneSqDomain ∧ SourceInflectionOn logAbsAddOneDivAddOneSq a b c) ↔
        c = -1 - logAbsAddOneDivAddOneSqInflectionOffset ∨ c = -1 + logAbsAddOneDivAddOneSqInflectionOffset) ∧
      (logAbsAddOneDivAddOneSq (-1 - logAbsAddOneDivAddOneSqInflectionOffset) = 5 / (6 * Real.exp (5 / 3)) ∧
        logAbsAddOneDivAddOneSq (-1 + logAbsAddOneDivAddOneSqInflectionOffset) = 5 / (6 * Real.exp (5 / 3))) ∧
      (∀ x : ℝ, logAbsAddOneDivAddOneSq (-2 - x) = logAbsAddOneDivAddOneSq x) ∧
      (∀ x ∈ logAbsAddOneDivAddOneSqDomain, logAbsAddOneDivAddOneSq x = 0 ↔ x = -2 ∨ x = 0) ∧
      (∀ x ∈ logAbsAddOneDivAddOneSqDomain, (logAbsAddOneDivAddOneSq x < 0 ↔ -2 < x ∧ x < 0) ∧
        (0 < logAbsAddOneDivAddOneSq x ↔ x < -2 ∨ 0 < x)) ∧
      (Tendsto logAbsAddOneDivAddOneSq (𝓝[<] (-1 : ℝ)) atBot ∧ Tendsto logAbsAddOneDivAddOneSq (𝓝[>] (-1 : ℝ)) atBot) ∧
      (Tendsto logAbsAddOneDivAddOneSq atTop (𝓝 0) ∧ Tendsto logAbsAddOneDivAddOneSq atBot (𝓝 0)) ∧
      ((∀ a : ℝ, HasVerticalAsymptoteWithinAt logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain a ↔ a = -1) ∧
        (∀ b : ℝ, HasHorizontalAsymptoteWithin logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain b ↔ b = 0) ∧
        ∀ m b : ℝ, ¬ HasObliqueAsymptoteWithin logAbsAddOneDivAddOneSq logAbsAddOneDivAddOneSqDomain m b) ∧
      (∀ x y : ℝ, (x ∈ logAbsAddOneDivAddOneSqDomain ∧ logAbsAddOneDivAddOneSq x = y) ↔
        x ≠ -1 ∧ (x + 1) ^ 2 * y = Real.log |x + 1|) ∧
      (∀ y : ℝ, (∃ x ∈ logAbsAddOneDivAddOneSqDomain, logAbsAddOneDivAddOneSq x = y) ↔ y ≤ logAbsAddOneDivAddOneSqMaximumValue) :=
  ⟨logAbsAddOneDivAddOneSq_domain_iff, fun _ hx ↦ ⟨logAbsAddOneDivAddOneSq_hasDerivAt hx, logAbsAddOneDivAddOneSq_second_hasDerivAt hx⟩,
    fun _ hx ↦ logAbsAddOneDivAddOneSq_stationary_iff hx, logAbsAddOneDivAddOneSq_variation,
    logAbsAddOneDivAddOneSq_extrema, logAbsAddOneDivAddOneSq_critical_values, fun _ hx ↦ logAbsAddOneDivAddOneSq_global_bound hx,
    logAbsAddOneDivAddOneSq_convexity, logAbsAddOneDivAddOneSq_inflection_iff, logAbsAddOneDivAddOneSq_inflection_values,
    logAbsAddOneDivAddOneSq_reflection, fun _ hx ↦ logAbsAddOneDivAddOneSq_zero_iff hx,
    fun _ hx ↦ logAbsAddOneDivAddOneSq_signs hx, logAbsAddOneDivAddOneSq_pole_limits, logAbsAddOneDivAddOneSq_end_limits,
    logAbsAddOneDivAddOneSq_asymptotes, logAbsAddOneDivAddOneSq_graph_iff, logAbsAddOneDivAddOneSq_range⟩

end calculus.Chapter04.Section04LogarithmicFunctionInvestigationExercise
