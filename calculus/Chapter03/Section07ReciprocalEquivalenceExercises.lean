import calculus.Chapter03.Section07ExercisesDerivativeRatios
import calculus.Chapter03.Section07Fundamental
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# §3.7 — tương đương vô cùng bé của hai biểu thức nghịch đảo

Nguồn: Bài tập 3.7.6(a,b), `Ch3_gioihanhamso.tex`, dòng 3523–3528.
-/

set_option autoImplicit false

open Set Filter Topology

namespace calculus.Chapter03.Section07ReciprocalEquivalenceExercises

open calculus.Chapter03.Section02 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section07 calculus.Chapter03.Section07Fundamental
open calculus.Chapter03.Section07ExercisesDerivativeRatios


def reciprocalDifferenceDomain : Set ℝ := {x | 1 + x ≠ 0}


def reciprocalSqrtDifferenceDomain : Set ℝ := {x | 0 < 1 + x}


theorem mem_reciprocalSqrtDifferenceDomain_iff (x : ℝ) :
    x ∈ reciprocalSqrtDifferenceDomain ↔
      0 ≤ 1 + x ∧ Real.sqrt (1 + x) ≠ 0 := by
  change 0 < 1 + x ↔ 0 ≤ 1 + x ∧ Real.sqrt (1 + x) ≠ 0
  constructor
  · intro hx
    exact ⟨hx.le, Real.sqrt_ne_zero'.mpr hx⟩
  · intro hx
    exact Real.sqrt_ne_zero'.mp hx.2


theorem equivalentInfinitesimalsAlong_linear_of_hasDerivAt
    {D : Set ℝ} {f : ℝ → ℝ} {a f' : ℝ}
    (ha : AccumulationPointOf D a) (hf : HasDerivAt f f' a)
    (hf0 : f a = 0) (hf' : f' ≠ 0) :
    EquivalentInfinitesimalsAlong D (.point a) f (fun x ↦ f' * (x - a)) := by
  have he := nonvanishingAsymptoticEquivalenceAlong_linear_of_hasDerivAt ha hf hf0 hf'
  have hc : ContinuousAt (fun x : ℝ ↦ f' * (x - a)) a :=
    continuous_const.continuousAt.mul
      (continuous_id.continuousAt.sub continuous_const.continuousAt)
  apply nonvanishingAsymptoticEquivalenceAlong_infinitesimals_of_comparison_zero he
  refine ⟨he.1, ?_⟩
  simpa only [domainApproachFilter, sub_self, mul_zero] using
    hc.tendsto.mono_left (nhdsWithin_le_nhds (s := D \ {a}))

/-- Bài tập 3.7.6(a): 1−1/(1+x)∼x khi x→0. -/
theorem reciprocal_difference_equivalent_identity :
    EquivalentInfinitesimalsAlong reciprocalDifferenceDomain (.point 0)
      (fun x : ℝ ↦ 1 - 1 / (1 + x)) (fun x ↦ x) := by
  have harg : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).const_add 1
  have hf : HasDerivAt (fun x : ℝ ↦ 1 - 1 / (1 + x)) 1 0 := by
    convert! (harg.inv (by norm_num : (1 : ℝ) + 0 ≠ 0)).const_sub 1 using 1
    · simp only [Pi.inv_def, one_div]
    · norm_num
  have ha : AccumulationPointOf reciprocalDifferenceDomain 0 :=
    accumulationPointOf_mono
      (accumulationPointOf_inter_Ioi (univ_accumulation 0)
        (by norm_num : (-1 : ℝ) < 0)) (by
          intro x hx
          have hxl : (-1 : ℝ) < x := hx.2
          show 1 + x ≠ 0
          linarith)
  simpa only [sub_zero, one_mul] using
    equivalentInfinitesimalsAlong_linear_of_hasDerivAt ha hf
      (by norm_num) (by norm_num)

/-- Bài tập 3.7.6(b): 1−1/√(1+x)∼x/2 khi x→0. -/
theorem reciprocal_sqrt_difference_equivalent_half_identity :
    EquivalentInfinitesimalsAlong reciprocalSqrtDifferenceDomain (.point 0)
      (fun x : ℝ ↦ 1 - 1 / Real.sqrt (1 + x)) (fun x ↦ x / 2) := by
  have harg : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).const_add 1
  have hs : HasDerivAt (fun x : ℝ ↦ Real.sqrt (1 + x)) (1 / 2) 0 := by
    simpa only [add_zero, Real.sqrt_one, mul_one] using
      harg.sqrt (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hf : HasDerivAt (fun x : ℝ ↦ 1 - 1 / Real.sqrt (1 + x)) (1 / 2) 0 := by
    convert! (hs.inv (by norm_num : Real.sqrt ((1 : ℝ) + 0) ≠ 0)).const_sub 1 using 1
    · simp only [Pi.inv_def, one_div]
    · norm_num
  have ha : AccumulationPointOf reciprocalSqrtDifferenceDomain 0 :=
    accumulationPointOf_mono
      (accumulationPointOf_inter_Ioi (univ_accumulation 0)
        (by norm_num : (-1 : ℝ) < 0)) (by
          intro x hx
          have hxl : (-1 : ℝ) < x := hx.2
          show 0 < 1 + x
          linarith)
  have he := equivalentInfinitesimalsAlong_linear_of_hasDerivAt ha hf
    (by norm_num) (by norm_num)
  simpa only [sub_zero, one_div_mul_eq_div] using he

end calculus.Chapter03.Section07ReciprocalEquivalenceExercises
