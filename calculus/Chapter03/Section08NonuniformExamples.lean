import calculus.Chapter03.Section08
import calculus.Chapter02.Section03
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §3.8 — phản ví dụ cho tính liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3835–3840, dòng 3857–3859, dòng 3915–3921 và dòng 3941–3943.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section08NonuniformExamples
open calculus.Chapter03.Section08
open calculus.Chapter02.Section03


theorem reciprocal_printed_delta_witness (δ : ℝ) (hδ : 0 < δ) :
    let d : ℝ := min (δ / 2) (1 / 4)
    d ∈ Ioo (0 : ℝ) 1 ∧ 2 * d ∈ Ioo (0 : ℝ) 1 ∧
      |d - 2 * d| = d ∧ d < δ ∧
        |1 / d - 1 / (2 * d)| = d / (2 * d ^ 2) ∧
          2 ≤ |1 / d - 1 / (2 * d)| := by
  dsimp only
  let d : ℝ := min (δ / 2) (1 / 4)
  change d ∈ Ioo (0 : ℝ) 1 ∧ 2 * d ∈ Ioo (0 : ℝ) 1 ∧
    |d - 2 * d| = d ∧ d < δ ∧
      |1 / d - 1 / (2 * d)| = d / (2 * d ^ 2) ∧
        2 ≤ |1 / d - 1 / (2 * d)|
  have hd : 0 < d := lt_min (div_pos hδ (by norm_num)) (by norm_num)
  have hquarter : d ≤ 1 / 4 := min_le_right _ _
  have hhalf : d ≤ δ / 2 := min_le_left _ _
  have htwod : 0 < 2 * d := mul_pos (by norm_num) hd
  have hdx : d ∈ Ioo (0 : ℝ) 1 := ⟨hd, by linarith⟩
  have hdy : 2 * d ∈ Ioo (0 : ℝ) 1 := ⟨htwod, by linarith⟩
  have hdist : |d - 2 * d| = d := by
    rw [show d - 2 * d = -d by ring, abs_neg, abs_of_pos hd]
  have hclose : d < δ := by linarith
  have hscale : 1 / d = 2 / (2 * d) := by
    simpa only [mul_one] using
      (mul_div_mul_left (1 : ℝ) d (by norm_num : (2 : ℝ) ≠ 0)).symm
  have he : 1 / d - 1 / (2 * d) = 1 / (2 * d) := by
    rw [hscale, div_sub_div_same]
    norm_num
  have hratio : d / (2 * d ^ 2) = 1 / (2 * d) := by
    calc
      d / (2 * d ^ 2) = d / (d * (2 * d)) := by congr 1; ring
      _ = 1 / (2 * d) := by
        simpa only [mul_one] using mul_div_mul_left (1 : ℝ) (2 * d) hd.ne'
  have habs : |1 / d - 1 / (2 * d)| = 1 / (2 * d) := by
    rw [he, abs_of_pos (one_div_pos.mpr htwod)]
  have hlarge : 2 ≤ |1 / d - 1 / (2 * d)| := by
    rw [habs]
    apply (le_div_iff₀ htwod).mpr
    linarith
  exact ⟨hdx, hdy, hdist, hclose, habs.trans hratio.symm, hlarge⟩

/-- Ví dụ 3.8.11: 1/x không liên tục đều trên (0,1). -/
theorem reciprocal_not_nonemptyUniformContinuousOn_Ioo :
    ¬ NonemptyUniformContinuousOn (Ioo (0 : ℝ) 1) (fun x : ℝ ↦ 1 / x) := by
  intro hf
  obtain ⟨δ, hδ, hb⟩ := hf.2 2 (by norm_num)
  obtain ⟨hu, hv, hdist, hclose, _, hlarge⟩ := reciprocal_printed_delta_witness δ hδ
  have hsmall := hb (min (δ / 2) (1 / 4)) hu
    (2 * min (δ / 2) (1 / 4)) hv (hdist.trans_lt hclose)
  exact (not_lt_of_ge hlarge) hsmall


theorem reciprocal_printed_sequence_membership :
    ∀ n : ℕ, 2 ≤ n →
      1 / ((n : ℝ) + 1) ∈ Ioo (0 : ℝ) 1 ∧ 1 / (n : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  intro n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) + 1 := by linarith
  exact ⟨⟨one_div_pos.mpr hn1, (div_lt_one hn1).mpr (by linarith)⟩,
    ⟨one_div_pos.mpr hn0, (div_lt_one hn0).mpr (by linarith)⟩⟩


theorem reciprocal_printed_input_difference_converges :
    ConvergesTo (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) - 1 / (n : ℝ)) 0 := by
  apply convergesTo_iff_tendsto.mpr
  simpa only [sub_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sub
      (convergesTo_iff_tendsto.mp reciprocal_converges)


theorem reciprocal_printed_image_difference_eq_one (n : ℕ) :
    1 / (1 / ((n : ℝ) + 1)) - 1 / (1 / (n : ℝ)) = 1 := by
  simp only [one_div, inv_inv]
  ring


theorem reciprocal_printed_image_difference_converges :
    ConvergesTo (fun n : ℕ ↦ 1 / (1 / ((n : ℝ) + 1)) - 1 / (1 / (n : ℝ))) 1 := by
  have he : (fun n : ℕ ↦ 1 / (1 / ((n : ℝ) + 1)) - 1 / (1 / (n : ℝ))) =
      fun _ ↦ (1 : ℝ) := by
    funext n
    exact reciprocal_printed_image_difference_eq_one n
  rw [he]
  exact constant_converges 1

/-- Ví dụ 3.8.13: hai dãy có khoảng cách tiến đến 0 nhưng khoảng cách giữa các ảnh không tiến đến 0. -/
theorem reciprocal_printed_sequence_counterexample :
    (∀ n : ℕ, 2 ≤ n → 1 / ((n : ℝ) + 1) ∈ Ioo (0 : ℝ) 1 ∧
      1 / (n : ℝ) ∈ Ioo (0 : ℝ) 1) ∧
    ConvergesTo (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) - 1 / (n : ℝ)) 0 ∧
    ConvergesTo (fun n : ℕ ↦ 1 / (1 / ((n : ℝ) + 1)) - 1 / (1 / (n : ℝ))) 1 ∧
    ¬ NonemptyUniformContinuousOn (Ioo (0 : ℝ) 1) (fun x : ℝ ↦ 1 / x) := by
  refine ⟨reciprocal_printed_sequence_membership,
    reciprocal_printed_input_difference_converges,
    reciprocal_printed_image_difference_converges, ?_⟩
  intro hf
  obtain ⟨δ, hδ, hb⟩ := hf.2 (1 / 2) (by norm_num)
  obtain ⟨N, _, hN⟩ := reciprocal_printed_input_difference_converges δ hδ
  let n : ℕ := max 2 N
  obtain ⟨hu, hv⟩ := reciprocal_printed_sequence_membership n (le_max_left _ _)
  have hclose : |1 / ((n : ℝ) + 1) - 1 / (n : ℝ)| < δ := by
    simpa only [sub_zero] using hN n (le_max_right _ _)
  have hsmall := hb (1 / ((n : ℝ) + 1)) hu (1 / (n : ℝ)) hv hclose
  rw [reciprocal_printed_image_difference_eq_one n] at hsmall
  norm_num at hsmall


theorem square_nonuniform_witness (δ : ℝ) (hδ : 0 < δ) :
    ∃ u v : ℝ, |u - v| < δ ∧ 1 ≤ |u ^ 2 - v ^ 2| := by
  let d : ℝ := δ / 2
  let u : ℝ := 1 / d
  have hd : 0 < d := div_pos hδ (by norm_num)
  have hud : u * d = 1 := one_div_mul_cancel hd.ne'
  refine ⟨u, u + d, ?_, ?_⟩
  · rw [show u - (u + d) = -d by ring, abs_neg, abs_of_pos hd]
    dsimp only [d]
    linarith
  · have he : u ^ 2 - (u + d) ^ 2 = -(2 + d ^ 2) := by nlinarith
    rw [he, abs_neg, abs_of_nonneg (by nlinarith [sq_nonneg d])]
    nlinarith [sq_nonneg d]

/-- Bài tập 3.8.2(a): x² không liên tục đều trên ℝ. -/
theorem square_not_nonemptyUniformContinuousOn_univ :
    ¬ NonemptyUniformContinuousOn univ (fun x : ℝ ↦ x ^ 2) := by
  intro hf
  obtain ⟨δ, hδ, hb⟩ := hf.2 1 (by norm_num)
  obtain ⟨u, v, hclose, hlarge⟩ := square_nonuniform_witness δ hδ
  exact (not_lt_of_ge hlarge) (hb u (mem_univ _) v (mem_univ _) hclose)


theorem identity_nonemptyUniformContinuousOn_univ :
    NonemptyUniformContinuousOn univ (fun x : ℝ ↦ x) := by
  refine ⟨⟨0, mem_univ _⟩, ?_⟩
  intro ε hε
  exact ⟨ε, hε, fun _ _ _ _ hclose ↦ hclose⟩

/-- Bài tập 3.8.5: f(x)=g(x)=x liên tục đều trên ℝ nhưng tích không liên tục đều. -/
theorem uniformlyContinuous_factors_nonuniform_product :
    ∃ D : Set ℝ, ∃ f g : ℝ → ℝ,
      NonemptyUniformContinuousOn D f ∧ NonemptyUniformContinuousOn D g ∧
        ¬ NonemptyUniformContinuousOn D (fun x : ℝ ↦ f x * g x) := by
  refine ⟨univ, (fun x : ℝ ↦ x), (fun x : ℝ ↦ x),
    identity_nonemptyUniformContinuousOn_univ, identity_nonemptyUniformContinuousOn_univ, ?_⟩
  simpa only [pow_two] using square_not_nonemptyUniformContinuousOn_univ

end calculus.Chapter03.Section08NonuniformExamples
