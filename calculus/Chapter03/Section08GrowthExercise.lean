import calculus.Chapter03.Section08
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# §3.8 — Bài tập 3.8.12: chặn tăng trưởng trên [1,+∞)

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3980–3982.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08GrowthExercise
open calculus.Chapter03.Section08

/-- Bài tập 3.8.12: tồn tại M>0 sao cho |f(x)|/x≤M với mọi x≥1. -/
theorem nonemptyUniformContinuousOn_Ici_exists_linear_bound {f : ℝ → ℝ}
    (hf : NonemptyUniformContinuousOn (Ici (1 : ℝ)) f) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → |f x| / x ≤ M := by
  obtain ⟨δ, hδ, hstep⟩ := hf.2 1 (by norm_num)
  let d : ℝ := δ / 2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdδ : d < δ := by dsimp only [d]; linarith
  have hmem (n : ℕ) : 1 + (n : ℝ) * d ∈ Ici (1 : ℝ) := by
    simp only [mem_Ici]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hd.le)
  have hgrid : ∀ n : ℕ, |f (1 + (n : ℝ) * d) - f 1| ≤ (n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hdist : |(1 + ((n + 1 : ℕ) : ℝ) * d) - (1 + (n : ℝ) * d)| = d := by
        have heq : (1 + ((n + 1 : ℕ) : ℝ) * d) - (1 + (n : ℝ) * d) = d := by
          simp only [Nat.cast_add, Nat.cast_one]
          ring
        rw [heq, abs_of_pos hd]
      have hs := hstep (1 + ((n + 1 : ℕ) : ℝ) * d) (hmem (n + 1))
        (1 + (n : ℝ) * d) (hmem n) (by rw [hdist]; exact hdδ)
      have ht := abs_sub_le (f (1 + ((n + 1 : ℕ) : ℝ) * d))
        (f (1 + (n : ℝ) * d)) (f 1)
      simp only [Nat.cast_add, Nat.cast_one] at hs ht ⊢
      linarith
  refine ⟨|f 1| + 1 + 1 / d, by positivity, ?_⟩
  intro x hx
  let n : ℕ := ⌊(x - 1) / d⌋₊
  have hfloor : (n : ℝ) * d ≤ x - 1 :=
    (le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hx) hd.le))
  have hceil : x - 1 < ((n : ℝ) + 1) * d :=
    (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one ((x - 1) / d))
  have hnear : |x - (1 + (n : ℝ) * d)| < δ := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hs := hstep x (by simpa only [mem_Ici] using hx)
    (1 + (n : ℝ) * d) (hmem n) hnear
  have ht := abs_sub_le (f x) (f (1 + (n : ℝ) * d)) (f 1)
  have ha := abs_add_le (f x - f 1) (f 1)
  simp only [sub_add_cancel] at ha
  have hbound : |f x| ≤ |f 1| + (n : ℝ) + 1 := by
    have hn := hgrid n
    linarith
  have hnle : (n : ℝ) ≤ x / d := (le_div_iff₀ hd).mpr (by linarith)
  have hnx : (n : ℝ) ≤ (1 / d) * x := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hnle
  have hbase := mul_le_mul_of_nonneg_left hx (show 0 ≤ |f 1| + 1 by positivity)
  have hlinear : |f 1| + (n : ℝ) + 1 ≤ (|f 1| + 1 + 1 / d) * x := by
    nlinarith
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx)).mpr
    (hbound.trans hlinear)

end calculus.Chapter03.Section08GrowthExercise
