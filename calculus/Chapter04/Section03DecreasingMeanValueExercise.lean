import calculus.Chapter04.Section01Derivatives
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bài 13: dãy giảm ngặt và tổng các giá trị đạo hàm

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1152–1153. Không cần `f′` liên tục.
-/
namespace calculus.Chapter04.Section03DecreasingMeanValueExercise
open Set Filter Finset calculus.Chapter04.Section01Derivatives
open scoped Topology BigOperators


noncomputable def partitionPoint (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)


noncomputable def partitionWeight (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))


theorem partitionPoint_mem (n : ℕ) : partitionPoint n ∈ Ioc (0 : ℝ) 1 := by
  constructor
  · unfold partitionPoint
    positivity
  · unfold partitionPoint
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith


theorem partitionPoint_strictAnti : StrictAnti partitionPoint := by
  apply strictAnti_nat_of_succ_lt
  intro n
  simp only [partitionPoint, Nat.cast_add, Nat.cast_one]
  apply one_div_lt_one_div_of_lt (by positivity)
  linarith


theorem partitionWeight_eq_sub (n : ℕ) :
    partitionWeight n = partitionPoint n - partitionPoint (n + 1) := by
  have h1 : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have h2 : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  simp only [partitionWeight, partitionPoint, Nat.cast_add, Nat.cast_one]
  have hshift : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
  rw [hshift]
  field_simp [h1, h2]
  ring


theorem partitionWeight_mem (n : ℕ) : partitionWeight n ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · unfold partitionWeight
    positivity
  · rw [partitionWeight_eq_sub]
    have hn := partitionPoint_mem n
    have hn1 := partitionPoint_mem (n + 1)
    linarith [hn.2, hn1.1]


theorem partitionWeight_strictAnti : StrictAnti partitionWeight := by
  apply strictAnti_nat_of_succ_lt
  intro n
  simp only [partitionWeight, Nat.cast_add, Nat.cast_one]
  apply one_div_lt_one_div_of_lt (by positivity)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith


theorem partitionPoint_tendsto_zero : Tendsto partitionPoint atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat


theorem decreasing_mean_value_partition {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hfd : DifferentiableOn ℝ f (Ioo (0 : ℝ) 1)) :
    ∃ C : ℕ → ℝ, StrictAnti C ∧ (∀ n, C n ∈ Ioo (0 : ℝ) 1) ∧
      Tendsto (fun n : ℕ ↦ ∑ k ∈ range n, partitionWeight k * deriv f (C k))
        atTop (𝓝 (f 1 - f 0)) := by
  classical
  have hwitness (n : ℕ) : ∃ c ∈ Ioo (partitionPoint (n + 1)) (partitionPoint n),
      partitionWeight n * deriv f c = f (partitionPoint n) - f (partitionPoint (n + 1)) := by
    have hab : partitionPoint (n + 1) < partitionPoint n :=
      partitionPoint_strictAnti (Nat.lt_succ_self n)
    have hsubc : Icc (partitionPoint (n + 1)) (partitionPoint n) ⊆ Icc (0 : ℝ) 1 := by
      intro x hx
      exact ⟨(partitionPoint_mem (n + 1)).1.le.trans hx.1,
        hx.2.trans (partitionPoint_mem n).2⟩
    have hsubd : Ioo (partitionPoint (n + 1)) (partitionPoint n) ⊆ Ioo (0 : ℝ) 1 := by
      intro x hx
      exact ⟨(partitionPoint_mem (n + 1)).1.trans hx.1,
        hx.2.trans_le (partitionPoint_mem n).2⟩
    obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope f hab (hfc.mono hsubc) (hfd.mono hsubd)
    refine ⟨c, hc, ?_⟩
    rw [partitionWeight_eq_sub]
    have hmul := (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he
    simpa only [mul_comm] using hmul
  choose C hc he using hwitness
  have hC : StrictAnti C := by
    apply strictAnti_nat_of_succ_lt
    intro n
    exact (hc (n + 1)).2.trans (hc n).1
  have hCmem (n : ℕ) : C n ∈ Ioo (0 : ℝ) 1 :=
    ⟨(partitionPoint_mem (n + 1)).1.trans (hc n).1,
      (hc n).2.trans_le (partitionPoint_mem n).2⟩
  have hsum (n : ℕ) :
      (∑ k ∈ range n, partitionWeight k * deriv f (C k)) = f 1 - f (partitionPoint n) := by
    induction n with
    | zero => simp [partitionPoint]
    | succ n ih =>
      rw [sum_range_succ, ih, he n]
      ring
  have hA : Tendsto partitionPoint atTop (𝓝[Icc (0 : ℝ) 1] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ partitionPoint_tendsto_zero
      (Eventually.of_forall fun n ↦ ⟨(partitionPoint_mem n).1.le, (partitionPoint_mem n).2⟩)
  have hflim : Tendsto (fun n : ℕ ↦ f (partitionPoint n)) atTop (𝓝 (f 0)) :=
    (hfc 0 (by constructor <;> norm_num)).tendsto.comp hA
  refine ⟨C, hC, hCmem, ?_⟩
  simpa only [hsum] using (tendsto_const_nhds (x := f 1)).sub hflim

/-- Bài 13: tổng từ 1 đến `n`, với hai dãy giảm ngặt trên các chỉ số dương. -/
theorem source_decreasing_weighted_derivative_sums {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hfd : DifferentiableOnDomain f (Ioo (0 : ℝ) 1)) :
    ∃ α c : ℕ → ℝ,
      StrictAntiOn α (Ici 1) ∧ StrictAntiOn c (Ici 1) ∧
      (∀ n, 1 ≤ n → α n ∈ Ioo (0 : ℝ) 1 ∧ c n ∈ Ioo (0 : ℝ) 1) ∧
      Tendsto (fun n : ℕ ↦ ∑ k ∈ range n, α (k + 1) * deriv f (c (k + 1)))
        atTop (𝓝 (f 1 - f 0)) := by
  obtain ⟨C, hC, hCmem, hlim⟩ := decreasing_mean_value_partition hfc
    ((differentiableOnDomain_iff_differentiableOn_of_isOpen f _ isOpen_Ioo).mp hfd)
  let α : ℕ → ℝ := fun n ↦ partitionWeight (n - 1)
  let c : ℕ → ℝ := fun n ↦ C (n - 1)
  refine ⟨α, c, ?_, ?_, ?_, ?_⟩
  · intro i hi j _ hij
    exact partitionWeight_strictAnti (Nat.sub_lt_sub_right hi hij)
  · intro i hi j _ hij
    exact hC (Nat.sub_lt_sub_right hi hij)
  · intro n _
    exact ⟨partitionWeight_mem _, hCmem _⟩
  · simpa only [α, c, Nat.add_sub_cancel] using hlim

end calculus.Chapter04.Section03DecreasingMeanValueExercise
