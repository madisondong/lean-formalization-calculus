import calculus.Chapter03.Section08
import calculus.Chapter03.Section08NonuniformExamples
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# §3.8 — bốn bài tập không liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex`, Bài tập 3.8.2(b,c), dòng 3918–3919; Bài tập 3.8.3(c,f), dòng 3928, 3931.
-/

set_option autoImplicit false
open Set

namespace calculus.Chapter03.Section08NegativeExercises
open calculus.Chapter03.Section08
open calculus.Chapter03.Section08NonuniformExamples

/-- Bài tập 3.8.2(b): sin(1/x) không liên tục đều trên (0,1). -/
theorem sine_reciprocal_not_nonemptyUniformContinuousOn_Ioo :
    ¬ NonemptyUniformContinuousOn (Ioo (0 : ℝ) 1) (fun x : ℝ ↦ Real.sin (1 / x)) := by
  intro hf
  obtain ⟨δ, hδ, hb⟩ := hf.2 1 (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (2 / δ) / (2 * Real.pi))
  let t : ℝ := (n : ℝ) * (2 * Real.pi)
  have ht : max (1 : ℝ) (2 / δ) < t :=
    (div_lt_iff₀ Real.two_pi_pos).mp hn
  have ht1 : 1 < t := (le_max_left _ _).trans_lt ht
  have htd : 2 / δ < t := (le_max_right _ _).trans_lt ht
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.pi / 2 + t := by linarith [Real.pi_pos]
  let u : ℝ := 1 / t
  let v : ℝ := 1 / (Real.pi / 2 + t)
  have hu : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨one_div_pos.mpr ht0, (div_lt_one ht0).mpr ht1⟩
  have hv : v ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨one_div_pos.mpr hs0, (div_lt_one hs0).mpr ?_⟩
    linarith [Real.pi_pos]
  have htwo : 2 < t * δ := (div_lt_iff₀ hδ).mp htd
  have hud : u < δ / 2 := by
    apply (div_lt_iff₀ ht0).mpr
    nlinarith
  have hvd : v < δ / 2 := by
    apply (div_lt_iff₀ hs0).mpr
    nlinarith [mul_pos hδ Real.pi_pos]
  have hclose : |u - v| < δ := by
    apply abs_lt.mpr
    constructor <;> linarith [hu.1, hv.1]
  have hsu : Real.sin (1 / u) = 0 := by
    change Real.sin (1 / (1 / t)) = 0
    simp only [one_div, inv_inv]
    dsimp only [t]
    simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 n
  have hsv : Real.sin (1 / v) = 1 := by
    change Real.sin (1 / (1 / (Real.pi / 2 + t))) = 1
    simp only [one_div, inv_inv]
    dsimp only [t]
    simpa only [Real.sin_pi_div_two] using Real.sin_add_nat_mul_two_pi (Real.pi / 2) n
  have hsmall := hb u hu v hv hclose
  change |Real.sin (1 / u) - Real.sin (1 / v)| < 1 at hsmall
  rw [hsu, hsv] at hsmall
  norm_num at hsmall

/-- Bài tập 3.8.2(c): log x không liên tục đều trên (0,+∞). -/
theorem logarithm_not_nonemptyUniformContinuousOn_Ioi :
    ¬ NonemptyUniformContinuousOn (Ioi (0 : ℝ)) Real.log := by
  intro hf
  have he : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨δ, hδ, hb⟩ := hf.2 (Real.log 2) he
  let d : ℝ := δ / 2
  have hd : 0 < d := div_pos hδ (by norm_num)
  have htwod : 2 * d = δ := by dsimp only [d]; ring
  have hdist : |d - δ| = d := by
    rw [show d - δ = -d by linarith, abs_neg, abs_of_pos hd]
  have hclose : |d - δ| < δ := by rw [hdist]; dsimp only [d]; linarith
  have hlog : Real.log δ = Real.log 2 + Real.log d := by
    rw [← htwod, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hd.ne']
  have habs : |Real.log d - Real.log δ| = Real.log 2 := by
    rw [hlog, show Real.log d - (Real.log 2 + Real.log d) = -Real.log 2 by ring,
      abs_neg, abs_of_pos he]
  have hsmall := hb d hd δ hδ hclose
  rw [habs] at hsmall
  exact (lt_irrefl _) hsmall

/-- Bài tập 3.8.3(c): 1/|x−1| không liên tục đều trên (0,1). -/
theorem shifted_absolute_reciprocal_not_nonemptyUniformContinuousOn_Ioo :
    ¬ NonemptyUniformContinuousOn (Ioo (0 : ℝ) 1) (fun x : ℝ ↦ 1 / |x - 1|) := by
  intro hf
  apply reciprocal_not_nonemptyUniformContinuousOn_Ioo
  refine ⟨⟨1 / 2, by norm_num⟩, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hf.2 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u hu v hv hclose
  have hur : 1 - u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hvr : 1 - v ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hdist : |(1 - u) - (1 - v)| = |u - v| := by
    rw [show (1 - u) - (1 - v) = -(u - v) by ring, abs_neg]
  have hau : |(1 - u) - 1| = u := by
    rw [show (1 - u) - 1 = -u by ring, abs_neg, abs_of_pos hu.1]
  have hav : |(1 - v) - 1| = v := by
    rw [show (1 - v) - 1 = -v by ring, abs_neg, abs_of_pos hv.1]
  have hsmall := hb (1 - u) hur (1 - v) hvr (hdist.trans_lt hclose)
  simpa only [hau, hav] using hsmall

/-- Bài tập 3.8.3(f): cot x không liên tục đều trên (0,1). -/
theorem cotangent_not_nonemptyUniformContinuousOn_Ioo :
    ¬ NonemptyUniformContinuousOn (Ioo (0 : ℝ) 1) Real.cot := by
  intro hf
  obtain ⟨δ, hδ, hb⟩ := hf.2 1 (by norm_num)
  let d : ℝ := min (δ / 2) (1 / 4)
  have hd : 0 < d := lt_min (div_pos hδ (by norm_num)) (by norm_num)
  have hquarter : d ≤ 1 / 4 := min_le_right _ _
  have hhalf : d ≤ δ / 2 := min_le_left _ _
  have htwod : 0 < 2 * d := mul_pos (by norm_num) hd
  have hu : d ∈ Ioo (0 : ℝ) 1 := ⟨hd, by linarith⟩
  have hv : 2 * d ∈ Ioo (0 : ℝ) 1 := ⟨htwod, by linarith⟩
  have hclose : |d - 2 * d| < δ := by
    rw [show d - 2 * d = -d by ring, abs_neg, abs_of_pos hd]
    linarith
  have hs : 0 < Real.sin d := Real.sin_pos_of_pos_of_le_two hd (by linarith)
  have hs2 : 0 < Real.sin (2 * d) :=
    Real.sin_pos_of_pos_of_le_two htwod (by linarith)
  have hid : Real.cos d * Real.sin (2 * d) - Real.cos (2 * d) * Real.sin d =
      Real.sin d := by
    have h := Real.sin_sub (2 * d) d
    rw [show 2 * d - d = d by ring] at h
    nlinarith
  have heq : Real.cot d - Real.cot (2 * d) = 1 / Real.sin (2 * d) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    field_simp [hs.ne', hs2.ne']
    nlinarith [hid]
  have hsinle : Real.sin (2 * d) ≤ 2 * d := Real.sin_le htwod.le
  have hlarge : 2 ≤ |Real.cot d - Real.cot (2 * d)| := by
    rw [heq, abs_of_pos (one_div_pos.mpr hs2)]
    apply (le_div_iff₀ hs2).mpr
    linarith
  exact (not_lt_of_ge (by linarith : 1 ≤ |Real.cot d - Real.cot (2 * d)|))
    (hb d hu (2 * d) hv hclose)

end calculus.Chapter03.Section08NegativeExercises
