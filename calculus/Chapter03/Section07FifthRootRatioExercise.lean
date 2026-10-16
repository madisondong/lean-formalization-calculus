import calculus.Chapter03.Section03Exercises

/-!
§3.7 — Bài tập 3.7.11(p)

Nguồn: dòng 3698.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07FifthRootRatioExercise
open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises


def fifthRootRatioDomain : Set ℝ := {x | 32 + x ∈ nthRootDomain 5 ∧ x ≠ 0}


theorem fifth_root_thirty_two : realNthRoot 5 32 = 2 := by
  have hroot : (32 : ℝ) ^ ((5 : ℝ)⁻¹) = 2 := by
    convert! Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 5)
      (by norm_num : (0 : ℝ) ≤ 2) (by decide : (5 : ℕ) ≠ 0) using 1; norm_num
  simpa only [realNthRoot,
    if_neg (show ¬ (Odd (5 : ℕ) ∧ (32 : ℝ) < 0) by
      rintro ⟨_, hneg⟩
      norm_num at hneg), Nat.cast_ofNat] using hroot


theorem fifth_root_hasDerivAt_thirty_two :
    HasDerivAt (realNthRoot 5) (1 / 80) 32 := by
  have hvalue : (32 : ℝ) ^ ((5 : ℝ)⁻¹) = 2 := by
    simpa only [realNthRoot,
    if_neg (show ¬ (Odd (5 : ℕ) ∧ (32 : ℝ) < 0) by
      rintro ⟨_, hneg⟩
      norm_num at hneg), Nat.cast_ofNat] using fifth_root_thirty_two
  have hp : HasDerivAt (fun x : ℝ ↦ x ^ ((5 : ℝ)⁻¹))
      ((5 : ℝ)⁻¹ * (32 : ℝ) ^ ((5 : ℝ)⁻¹ - 1)) (32 : ℝ) :=
    Real.hasDerivAt_rpow_const (Or.inl (by norm_num : (32 : ℝ) ≠ 0))
  rw [Real.rpow_sub_one (by norm_num : (32 : ℝ) ≠ 0), hvalue] at hp
  norm_num at hp
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 32)] with x hx
  unfold realNthRoot
  rw [if_neg (by rintro ⟨_, hneg⟩; exact not_lt_of_ge hx.le hneg)]
  norm_num

/-- Bài tập 3.7.11(p): (⁵√(32+x)−2)/x→1/80. -/
theorem fifth_root_difference_ratio_at_zero :
    DomainLimit fifthRootRatioDomain
      (fun x ↦ (realNthRoot 5 (32 + x) - 2) / x) 0 (1 / 80) := by
  have harg : HasDerivAt (fun x : ℝ ↦ 32 + x) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).const_add 32
  have hr : HasDerivAt (realNthRoot 5) (1 / 80) (32 + (0 : ℝ)) := by
    simpa only [add_zero] using fifth_root_hasDerivAt_thirty_two
  have hf : HasDerivAt (fun x : ℝ ↦ realNthRoot 5 (32 + x) - 2) (1 / 80) 0 := by
    simpa only [Function.comp_def, mul_one] using (hr.comp 0 harg).sub_const 2
  have ha : AccumulationPointOf fifthRootRatioDomain 0 :=
    accumulationPointOf_mono (univ_diff_accumulation 0) (by
      intro x hx
      exact ⟨Or.inl ⟨2, by norm_num⟩, hx.2⟩)
  simpa only [id_eq, div_one] using ratio_of_derivative_slopes ha hf (hasDerivAt_id (0 : ℝ))
    (by simp only [add_zero, fifth_root_thirty_two, sub_self]) (by rfl) one_ne_zero

end calculus.Chapter03.Section07FifthRootRatioExercise
