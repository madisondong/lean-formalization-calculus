import calculus.Chapter03.Section08
import calculus.Chapter03.Section08Holder
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §3.8 — hai ví dụ căn bậc hai

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3815–3833, Ví dụ 3.8.9 và 3.8.10.
-/

set_option autoImplicit false
open Set

namespace calculus.Chapter03.Section08SqrtExamples
open calculus.Chapter03.Section08
open calculus.Chapter03.Section08Holder


theorem sqrt_difference_factorization {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |u - v| = (Real.sqrt u + Real.sqrt v) * |Real.sqrt u - Real.sqrt v| := by
  have hfactor : u - v =
      (Real.sqrt u + Real.sqrt v) * (Real.sqrt u - Real.sqrt v) := by
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]
  rw [hfactor, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]


theorem sqrt_difference_division_identity_Ici {a u v : ℝ} (ha : 0 < a)
    (hu : u ∈ Ici a) (hv : v ∈ Ici a) :
    |Real.sqrt u - Real.sqrt v| = |u - v| / (Real.sqrt u + Real.sqrt v) := by
  have hu0 : 0 ≤ u := ha.le.trans hu
  have hv0 : 0 ≤ v := ha.le.trans hv
  have hsum : 0 < Real.sqrt u + Real.sqrt v :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 (ha.trans_le hu)) (Real.sqrt_nonneg _)
  apply (eq_div_iff hsum.ne').mpr
  calc
    |Real.sqrt u - Real.sqrt v| * (Real.sqrt u + Real.sqrt v) =
        (Real.sqrt u + Real.sqrt v) * |Real.sqrt u - Real.sqrt v| := mul_comm _ _
    _ = |u - v| := (sqrt_difference_factorization hu0 hv0).symm


theorem sqrt_difference_lipschitz_bound_Ici {a u v : ℝ} (ha : 0 < a)
    (hu : u ∈ Ici a) (hv : v ∈ Ici a) :
    |Real.sqrt u - Real.sqrt v| ≤ (1 / (2 * Real.sqrt a)) * |u - v| := by
  have hu0 : 0 ≤ u := ha.le.trans hu
  have hv0 : 0 ≤ v := ha.le.trans hv
  have hsum : 2 * Real.sqrt a ≤ Real.sqrt u + Real.sqrt v := by
    linarith [Real.sqrt_le_sqrt hu, Real.sqrt_le_sqrt hv]
  have hb : (2 * Real.sqrt a) * |Real.sqrt u - Real.sqrt v| ≤ |u - v| := by
    rw [sqrt_difference_factorization hu0 hv0]
    exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
  have hd : 0 < 2 * Real.sqrt a := by
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 ha)
  calc
    |Real.sqrt u - Real.sqrt v| ≤ |u - v| / (2 * Real.sqrt a) :=
      (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hb)
    _ = (1 / (2 * Real.sqrt a)) * |u - v| := by ring

/-- Ví dụ 3.8.9: √x thỏa điều kiện Lipschitz trên [a,+∞), với a>0. -/
theorem sqrt_nonemptyLipschitzOn_Ici {a : ℝ} (ha : 0 < a) :
    NonemptyLipschitzOn (Ici a) Real.sqrt := by
  refine ⟨⟨a, self_mem_Ici⟩, 1 / (2 * Real.sqrt a), ?_, ?_⟩
  · exact (one_div_pos.mpr (mul_pos (by norm_num) (Real.sqrt_pos.2 ha))).le
  · exact fun _ hu _ hv ↦ sqrt_difference_lipschitz_bound_Ici ha hu hv

/-- Ví dụ 3.8.9: √x liên tục đều trên [a,+∞), với a>0. -/
theorem sqrt_nonemptyUniformContinuousOn_Ici {a : ℝ} (ha : 0 < a) :
    NonemptyUniformContinuousOn (Ici a) Real.sqrt :=
  nonemptyHolderContinuousOn_uniformContinuous (nonemptyLipschitzOn_holder (sqrt_nonemptyLipschitzOn_Ici ha))


theorem sqrt_difference_holder_bound {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.sqrt u - Real.sqrt v| ≤ |u - v| ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  apply Real.abs_le_sqrt
  rcases le_total v u with hvu | huv
  · have hsu := Real.sqrt_le_sqrt hvu
    have hs : 0 ≤ Real.sqrt u - Real.sqrt v := sub_nonneg.mpr hsu
    have hm := mul_nonneg (Real.sqrt_nonneg v) hs
    rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]
  · have hsv := Real.sqrt_le_sqrt huv
    have hs : 0 ≤ Real.sqrt v - Real.sqrt u := sub_nonneg.mpr hsv
    have hm := mul_nonneg (Real.sqrt_nonneg u) hs
    rw [abs_of_nonpos (sub_nonpos.mpr huv)]
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]


theorem sqrt_nonemptyHolderContinuousOn_Ici_zero : NonemptyHolderContinuousOn (Ici (0 : ℝ)) Real.sqrt := by
  exact ⟨⟨0, self_mem_Ici⟩, 1, by norm_num, 1 / 2, by norm_num,
    fun _ hu _ hv ↦ by simpa only [one_mul] using sqrt_difference_holder_bound hu hv⟩


theorem sqrt_nonemptyUniformContinuousOn_Ici_zero :
    NonemptyUniformContinuousOn (Ici (0 : ℝ)) Real.sqrt :=
  nonemptyHolderContinuousOn_uniformContinuous sqrt_nonemptyHolderContinuousOn_Ici_zero


theorem sqrt_lipschitz_printed_natural_bound {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ u ∈ Ici (0 : ℝ), ∀ v ∈ Ici (0 : ℝ),
      |Real.sqrt u - Real.sqrt v| ≤ L * |u - v|) :
    ∀ n : ℕ, 0 < n → (n : ℝ) ≤ L ^ 2 := by
  intro n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrec : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  have hh := hb (1 / (n : ℝ)) hrec.le 0 self_mem_Ici
  simp only [Real.sqrt_zero, sub_zero,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hrec.le] at hh
  rw [Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ)) (n : ℝ), Real.sqrt_one] at hh
  have hquot : 1 / Real.sqrt (n : ℝ) ≤ L / (n : ℝ) := by
    calc
      1 / Real.sqrt (n : ℝ) ≤ L * (1 / (n : ℝ)) := hh
      _ = L / (n : ℝ) := by ring
  have hmul : (1 / Real.sqrt (n : ℝ)) * (n : ℝ) ≤ L :=
    (le_div_iff₀ hnR).mp hquot
  have hroot : Real.sqrt (n : ℝ) ≤ L := by
    calc
      Real.sqrt (n : ℝ) = (n : ℝ) / Real.sqrt (n : ℝ) := Real.div_sqrt.symm
      _ = (1 / Real.sqrt (n : ℝ)) * (n : ℝ) := by ring
      _ ≤ L := hmul
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (n : ℝ)) hL).mpr hroot
  simpa only [Real.sq_sqrt hnR.le] using hsq


theorem sqrt_not_nonemptyLipschitzOn_Ici_zero : ¬ NonemptyLipschitzOn (Ici (0 : ℝ)) Real.sqrt := by
  rintro ⟨_, L, hL, hb⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (L ^ 2 + 1)
  have hnR : 0 < (n : ℝ) := by nlinarith [sq_nonneg L]
  have hnN : 0 < n := by exact_mod_cast hnR
  have hbound := sqrt_lipschitz_printed_natural_bound hL hb n hnN
  linarith

/-- Ví dụ 3.8.10: √x liên tục Hölder và liên tục đều trên [0,+∞), nhưng không thỏa điều kiện Lipschitz. -/
theorem sqrt_full_nonnegative_example :
    NonemptyHolderContinuousOn (Ici (0 : ℝ)) Real.sqrt ∧
      NonemptyUniformContinuousOn (Ici (0 : ℝ)) Real.sqrt ∧
        ¬ NonemptyLipschitzOn (Ici (0 : ℝ)) Real.sqrt :=
  ⟨sqrt_nonemptyHolderContinuousOn_Ici_zero, sqrt_nonemptyUniformContinuousOn_Ici_zero,
    sqrt_not_nonemptyLipschitzOn_Ici_zero⟩

end calculus.Chapter03.Section08SqrtExamples
