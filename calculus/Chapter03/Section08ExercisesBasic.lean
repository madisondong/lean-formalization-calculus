import calculus.Chapter03.Section08Holder
import calculus.Chapter02.Section09
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §3.8 — bài tập cơ bản về liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex`, Bài tập 3.8.1(a,b), 3.8.3(b,d,e,g), 3.8.4 và 3.8.6, dòng 3906–3947.
-/

set_option autoImplicit false
open Set
open scoped NNReal
namespace calculus.Chapter03.Section08ExercisesBasic
open calculus.Chapter03.Section08
open calculus.Chapter03.Section08Holder
open calculus.Chapter02.Section09

/-- Bài tập 3.8.1(a): hàm afin liên tục đều trên ℝ, với a thực tùy ý. -/
theorem affine_nonemptyUniformContinuousOn (a b : ℝ) :
    NonemptyUniformContinuousOn univ (fun x : ℝ ↦ a * x + b) := by
  apply nonemptyHolderContinuousOn_uniformContinuous
  apply nonemptyLipschitzOn_holder
  refine ⟨univ_nonempty, |a|, abs_nonneg _, ?_⟩
  intro u _ v _
  rw [show (a * u + b) - (a * v + b) = a * (u - v) by ring, abs_mul]


theorem reciprocal_difference_bound_Ici {a u v : ℝ} (ha : 0 < a)
    (hu : u ∈ Ici a) (hv : v ∈ Ici a) :
    |1 / u - 1 / v| ≤ (1 / a ^ 2) * |u - v| := by
  have hu0 : 0 < u := ha.trans_le hu
  have hv0 : 0 < v := ha.trans_le hv
  have huv : 0 < u * v := mul_pos hu0 hv0
  have haa : 0 < a ^ 2 := sq_pos_of_pos ha
  have hab : a ^ 2 ≤ u * v := by
    simpa only [pow_two] using mul_le_mul hu hv ha.le hu0.le
  have he : 1 / u - 1 / v = (v - u) / (u * v) := by
    field_simp
  rw [he, abs_div, abs_of_pos huv, abs_sub_comm v u]
  calc
    |u - v| / (u * v) ≤ |u - v| / a ^ 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) haa hab
    _ = (1 / a ^ 2) * |u - v| := by ring

/-- Bài tập 3.8.1(b): hàm nghịch đảo liên tục đều trên [a,+∞), với a>0. -/
theorem reciprocal_nonemptyUniformContinuousOn_Ici {a : ℝ} (ha : 0 < a) :
    NonemptyUniformContinuousOn (Ici a) (fun x : ℝ ↦ 1 / x) := by
  apply nonemptyHolderContinuousOn_uniformContinuous
  apply nonemptyLipschitzOn_holder
  exact ⟨⟨a, Set.self_mem_Ici⟩, 1 / a ^ 2, (div_pos (by norm_num) (sq_pos_of_pos ha)).le,
    fun _ hu _ hv ↦ reciprocal_difference_bound_Ici ha hu hv⟩

/-- Bài tập 3.8.3(b): hàm liên tục đều trên [0,+∞). -/
theorem rational_linear_nonemptyUniformContinuousOn_Ici :
    NonemptyUniformContinuousOn (Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + 1)) := by
  apply nonemptyHolderContinuousOn_uniformContinuous
  apply nonemptyLipschitzOn_holder
  refine ⟨⟨0, Set.self_mem_Ici⟩, 1, by norm_num, ?_⟩
  intro u hu v hv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  have hu1 : 0 < u + 1 := by linarith
  have hv1 : 0 < v + 1 := by linarith
  have hp : 0 < (u + 1) * (v + 1) := mul_pos hu1 hv1
  have hge : 1 ≤ (u + 1) * (v + 1) := by
    nlinarith [mul_nonneg hu hv]
  have he : u / (u + 1) - v / (v + 1) =
      (u - v) / ((u + 1) * (v + 1)) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hp, one_mul]
  exact (div_le_iff₀ hp).mpr (le_mul_of_one_le_right (abs_nonneg _) hge)

/-- Bài tập 3.8.3(d): hàm liên tục đều trên (0,1). -/
theorem reciprocal_abs_two_nonemptyUniformContinuousOn_Ioo :
    NonemptyUniformContinuousOn (Ioo (0 : ℝ) 1) (fun x : ℝ ↦ 1 / |x - 2|) := by
  apply nonemptyHolderContinuousOn_uniformContinuous
  apply nonemptyLipschitzOn_holder
  refine ⟨⟨1 / 2, by norm_num⟩, 1, by norm_num, ?_⟩
  intro u hu v hv
  have hu2 : |u - 2| = 2 - u := by rw [abs_of_neg (by linarith [hu.2] : u - 2 < 0)]; ring
  have hv2 : |v - 2| = 2 - v := by rw [abs_of_neg (by linarith [hv.2] : v - 2 < 0)]; ring
  change |(1 / |u - 2|) - (1 / |v - 2|)| ≤ 1 * |u - v|
  rw [hu2, hv2]
  have hb := reciprocal_difference_bound_Ici (a := 1) (u := 2 - u) (v := 2 - v)
    (by norm_num) (by change 1 ≤ 2 - u; linarith [hu.2]) (by change 1 ≤ 2 - v; linarith [hv.2])
  have he : |(2 - u) - (2 - v)| = |u - v| := by
    rw [show (2 - u) - (2 - v) = v - u by ring, abs_sub_comm]
  simpa only [one_pow, div_one, one_mul, he] using hb

/-- Bài tập 3.8.3(e): sin²x liên tục đều trên [0,+∞). -/
theorem sin_square_nonemptyUniformContinuousOn_Ici :
    NonemptyUniformContinuousOn (Ici (0 : ℝ)) (fun x : ℝ ↦ Real.sin x ^ 2) := by
  apply nonemptyHolderContinuousOn_uniformContinuous
  apply nonemptyLipschitzOn_holder
  refine ⟨⟨0, Set.self_mem_Ici⟩, 2, by norm_num, ?_⟩
  intro u _ v _
  have hs : |Real.sin u + Real.sin v| ≤ 2 := by
    linarith [abs_add_le (Real.sin u) (Real.sin v),
      Real.abs_sin_le_one u, Real.abs_sin_le_one v]
  rw [show Real.sin u ^ 2 - Real.sin v ^ 2 =
    (Real.sin u - Real.sin v) * (Real.sin u + Real.sin v) by ring, abs_mul]
  calc
    |Real.sin u - Real.sin v| * |Real.sin u + Real.sin v| ≤ |u - v| * 2 :=
      mul_le_mul (Real.abs_sin_sub_sin_le u v) hs (abs_nonneg _) (abs_nonneg _)
    _ = 2 * |u - v| := by ring

/-- Bài tập 3.8.3(g): arctan liên tục đều trên ℝ. -/
theorem arctan_nonemptyUniformContinuousOn :
    NonemptyUniformContinuousOn univ Real.arctan := by
  have hl : LipschitzWith 1 Real.arctan :=
    lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan (fun x ↦ by
      change ‖deriv Real.arctan x‖ ≤ (1 : ℝ)
      rw [Real.deriv_arctan, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)).mpr (by nlinarith [sq_nonneg x]))
  apply nonemptyHolderContinuousOn_uniformContinuous
  apply nonemptyLipschitzOn_holder
  exact ⟨univ_nonempty, 1, by norm_num,
    fun u _ v _ ↦ by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul u v⟩

/-- Bài tập 3.8.4: tổng hai hàm liên tục đều trên cùng miền là liên tục đều. -/
theorem nonemptyUniformContinuousOn_add {D : Set ℝ} {f g : ℝ → ℝ}
    (hf : NonemptyUniformContinuousOn D f) (hg : NonemptyUniformContinuousOn D g) :
    NonemptyUniformContinuousOn D (fun x ↦ f x + g x) := by
  refine ⟨hf.1, ?_⟩
  intro ε hε
  obtain ⟨δf, hδf, hsmallf⟩ := hf.2 (ε / 2) (by linarith)
  obtain ⟨δg, hδg, hsmallg⟩ := hg.2 (ε / 2) (by linarith)
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro u hu v hv huv
  have hsf := hsmallf u hu v hv (huv.trans_le (min_le_left _ _))
  have hsg := hsmallg u hu v hv (huv.trans_le (min_le_right _ _))
  calc
    |(f u + g u) - (f v + g v)| = |(f u - f v) + (g u - g v)| := by congr 1; ring
    _ ≤ |f u - f v| + |g u - g v| := abs_add_le _ _
    _ < ε := by linarith

/-- Bài tập 3.8.4: nhân hàm liên tục đều với hằng số thực bảo toàn tính liên tục đều. -/
theorem nonemptyUniformContinuousOn_const_mul {D : Set ℝ} {f : ℝ → ℝ}
    (hf : NonemptyUniformContinuousOn D f) (k : ℝ) :
    NonemptyUniformContinuousOn D (fun x ↦ k * f x) := by
  refine ⟨hf.1, ?_⟩
  intro ε hε
  have hk : 0 < |k| + 1 := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := hf.2 (ε / (|k| + 1)) (div_pos hε hk)
  refine ⟨δ, hδ, ?_⟩
  intro u hu v hv huv
  have hs := hsmall u hu v hv huv
  have hprod : (|k| + 1) * |f u - f v| < ε := by
    have ht := (lt_div_iff₀ hk).mp hs
    simpa only [mul_comm] using ht
  rw [← mul_sub, abs_mul]
  have hb : |k| * |f u - f v| ≤ (|k| + 1) * |f u - f v| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  exact hb.trans_lt hprod

/-- Bài tập 3.8.6: hàm liên tục đều biến dãy Cauchy trong D thành dãy Cauchy. -/
theorem nonemptyUniformContinuousOn_sourceCauchy {D : Set ℝ} {f : ℝ → ℝ}
    (hf : NonemptyUniformContinuousOn D f) {u : ℕ → ℝ}
    (huD : ∀ n : ℕ, 1 ≤ n → u n ∈ D) (hu : SequenceCauchy u) :
    SequenceCauchy (fun n ↦ f (u n)) := by
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hf.2 ε hε
  obtain ⟨N, hN, htail⟩ := hu δ hδ
  refine ⟨N, hN, fun m hm n hn ↦ ?_⟩
  exact hsmall (u m) (huD m (hN.trans hm)) (u n) (huD n (hN.trans hn))
    (htail m hm n hn)

end calculus.Chapter03.Section08ExercisesBasic
