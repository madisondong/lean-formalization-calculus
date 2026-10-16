import calculus.Chapter04.Section03
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bài 4.3.20: tổng có trọng số

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1174–1175. Hằng số ở vế phải là `2013·2014/4`.
-/

set_option autoImplicit false
noncomputable section

namespace calculus.Chapter04.Section03WeightedSumReplacement
open Set
open scoped BigOperators

private theorem ordered_preimage_partition (m : ℕ) :
    ∀ {f : ℝ → ℝ} {a b : ℝ}, a < b → ContinuousOn f (Icc a b) →
      ∀ v : ℕ → ℝ, v 0 = f a → v (m + 1) = f b →
        (∀ i j : ℕ, i < j → j ≤ m + 1 → v i < v j) →
      ∃ t : ℕ → ℝ, t 0 = a ∧ t (m + 1) = b ∧
        (∀ k ≤ m + 1, t k ∈ Icc a b ∧ f (t k) = v k) ∧
        (∀ i j : ℕ, i < j → j ≤ m + 1 → t i < t j) := by
  induction m with
  | zero =>
      intro f a b hab hc v hv0 hv1 hv
      refine ⟨fun k ↦ if k = 0 then a else b, by simp, by simp, ?_, ?_⟩
      · intro k hk
        rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
        · simpa [hv0] using (show a ∈ Icc a b ∧ f a = f a from
            ⟨⟨le_rfl, hab.le⟩, rfl⟩)
        · simpa [hv1] using (show b ∈ Icc a b ∧ f b = f b from
            ⟨⟨hab.le, le_rfl⟩, rfl⟩)
      · intro i j hij hj
        have hi : i = 0 := by omega
        have hj' : j = 1 := by omega
        simpa [hi, hj'] using hab
  | succ m ih =>
      intro f a b hab hc v hv0 hvb hv
      have hleft : f a < v (m + 1) := by
        rw [← hv0]
        exact hv 0 (m + 1) (by omega) (by omega)
      have hright : v (m + 1) < f b := by
        rw [← hvb]
        exact hv (m + 1) (m + 1 + 1) (by omega) (by omega)
      obtain ⟨c, hcab, hcv⟩ := intermediate_value_Ioo hab.le hc ⟨hleft, hright⟩
      have hsub : Icc a c ⊆ Icc a b := fun x hx ↦ ⟨hx.1, hx.2.trans hcab.2.le⟩
      obtain ⟨u, hu0, huc, hub, hum⟩ := ih hcab.1 (hc.mono hsub) v hv0
        hcv.symm (fun i j hij hj ↦ hv i j hij (by omega))
      let t : ℕ → ℝ := fun k ↦ if k ≤ m + 1 then u k else b
      refine ⟨t, by simp [t, hu0], by simp [t], ?_, ?_⟩
      · intro k hk
        by_cases hkm : k ≤ m + 1
        · simpa [t, hkm] using ⟨hsub (hub k hkm).1, (hub k hkm).2⟩
        · have hlast : k = m + 1 + 1 := by omega
          subst k
          simpa [t, hvb] using
            (show b ∈ Icc a b ∧ f b = f b from ⟨⟨hab.le, le_rfl⟩, rfl⟩)
      · intro i j hij hj
        by_cases hjm : j ≤ m + 1
        · have him : i ≤ m + 1 := by omega
          simpa [t, him, hjm] using hum i j hij hjm
        · have him : i ≤ m + 1 := by omega
          have hib : u i < b := (hub i him).1.2.trans_lt hcab.2
          simpa [t, him, hjm] using hib

private theorem cauchy_square_witness {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (ha : 0 ≤ a)
    (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b)) (hf : f a < f b) :
    ∃ x ∈ Ioo a b, deriv f x ≠ 0 ∧
      x / deriv f x = (b ^ 2 - a ^ 2) / (2 * (f b - f a)) := by
  obtain ⟨x, hx, he⟩ := Section03.cauchy hab hc hd
    (continuous_pow 2).continuousOn (differentiable_id.pow 2).differentiableOn
  have he' : (f b - f a) * (2 * x) = (b ^ 2 - a ^ 2) * deriv f x := by
    simpa using he
  have hxp : 0 < x := ha.trans_lt hx.1
  have hfp : 0 < f b - f a := sub_pos.mpr hf
  have hdn : deriv f x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he'
    have hp : 0 < (f b - f a) * (2 * x) := mul_pos hfp (by positivity)
    linarith
  refine ⟨x, hx, hdn, ?_⟩
  apply (div_eq_div_iff hdn (mul_ne_zero (by norm_num) hfp.ne')).2
  nlinarith [he']

private theorem telescope_squares (t : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (t (k + 1) ^ 2 - t k ^ 2)) = t n ^ 2 - t 0 ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring


theorem weighted_sum_replacement {f : ℝ → ℝ} (n : ℕ) (hn : 0 < n)
    (hc : ContinuousOn f (Icc 0 1))
    (hd : DifferentiableOn ℝ f (Ioo 0 1)) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    ∃ x : Fin n → ℝ, StrictMono x ∧
      (∀ k, x k ∈ Ioo (0 : ℝ) 1 ∧ deriv f (x k) ≠ 0) ∧
      (∑ k : Fin n, (((k : ℕ) + 1 : ℕ) : ℝ) * x k / deriv f (x k)) =
        (n : ℝ) * ((n : ℝ) + 1) / 4 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  let S : ℝ := ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1) / 2
  have hS : 0 < S := by dsimp [S]; positivity
  let v : ℕ → ℝ := fun k ↦ ((k : ℝ) * ((k : ℝ) + 1) / 2) / S
  have hv0 : v 0 = f 0 := by simp [v, h0]
  have hvn : v (m + 1) = f 1 := by
    change S / S = f 1
    rw [div_self hS.ne', h1]
  have hvm : ∀ i j : ℕ, i < j → j ≤ m + 1 → v i < v j := by
    intro i j hij _
    apply (div_lt_div_iff_of_pos_right hS).2
    have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hp : 0 < ((j : ℝ) - i) * ((j : ℝ) + i + 1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [hp]
  obtain ⟨t, ht0, htn, htb, htm⟩ := ordered_preimage_partition m
    (by norm_num : (0 : ℝ) < 1) hc v hv0 hvn hvm
  have hw (k : Fin (m + 1)) :
      ∃ x ∈ Ioo (t k) (t ((k : ℕ) + 1)), deriv f x ≠ 0 ∧
        x / deriv f x =
          (t ((k : ℕ) + 1) ^ 2 - t k ^ 2) / (2 * (v ((k : ℕ) + 1) - v k)) := by
    have hk : (k : ℕ) < m + 1 := k.isLt
    have hk1 : (k : ℕ) + 1 ≤ m + 1 := by omega
    have hta := (htb k (by omega)).1
    have htb' := (htb ((k : ℕ) + 1) hk1).1
    have hsub : Icc (t k) (t ((k : ℕ) + 1)) ⊆ Icc (0 : ℝ) 1 :=
      fun z hz ↦ ⟨hta.1.trans hz.1, hz.2.trans htb'.2⟩
    have hsub' : Ioo (t k) (t ((k : ℕ) + 1)) ⊆ Ioo (0 : ℝ) 1 :=
      fun z hz ↦ ⟨hta.1.trans_lt hz.1, hz.2.trans_le htb'.2⟩
    have hfm : f (t k) < f (t ((k : ℕ) + 1)) := by
      rw [(htb k (by omega)).2, (htb ((k : ℕ) + 1) hk1).2]
      exact hvm k ((k : ℕ) + 1) (by omega) hk1
    obtain ⟨x, hx, hdn, he⟩ := cauchy_square_witness
      (htm k ((k : ℕ) + 1) (by omega) hk1) hta.1 (hc.mono hsub) (hd.mono hsub') hfm
    refine ⟨x, hx, hdn, ?_⟩
    simpa only [(htb k (by omega)).2, (htb ((k : ℕ) + 1) hk1).2] using he
  choose x hx hdn he using hw
  have hxm : StrictMono x := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have htij : t ((i : ℕ) + 1) ≤ t j := by
      rcases eq_or_lt_of_le (show (i : ℕ) + 1 ≤ j by omega) with h | h
      · simpa only [h] using (le_refl (t (j : ℕ)))
      · exact (htm ((i : ℕ) + 1) j h (by omega)).le
    exact ((hx i).2.trans_le htij).trans (hx j).1
  refine ⟨x, hxm, ?_, ?_⟩
  · intro k
    exact ⟨⟨((htb k (by omega)).1.1).trans_lt (hx k).1,
      ((hx k).2).trans_le (htb ((k : ℕ) + 1) (by omega)).1.2⟩, hdn k⟩
  · have hterm (k : Fin (m + 1)) :
        (((k : ℕ) + 1 : ℕ) : ℝ) * x k / deriv f (x k) =
          (S / 2) * (t ((k : ℕ) + 1) ^ 2 - t k ^ 2) := by
      have hvdiff : v ((k : ℕ) + 1) - v k = (((k : ℕ) + 1 : ℕ) : ℝ) / S := by
        dsimp [v]
        push_cast
        ring
      have hkp : 0 < (((k : ℕ) + 1 : ℕ) : ℝ) := by positivity
      have hden : 2 * (v ((k : ℕ) + 1) - v k) ≠ 0 := by
        rw [hvdiff]
        exact mul_ne_zero (by norm_num) (div_ne_zero hkp.ne' hS.ne')
      have he' := (div_eq_div_iff (hdn k) hden).1 (he k)
      rw [hvdiff] at he'
      have he'' :
          (2 * (((k : ℕ) + 1 : ℕ) : ℝ)) * x k =
            S * (t ((k : ℕ) + 1) ^ 2 - t k ^ 2) * deriv f (x k) := by
        field_simp [hS.ne'] at he'
        nlinarith [he']
      apply (div_eq_iff (hdn k)).2
      nlinarith [he'']
    have htel :
        (∑ k : Fin (m + 1), (t ((k : ℕ) + 1) ^ 2 - t k ^ 2)) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ t (k + 1) ^ 2 - t k ^ 2),
        telescope_squares, ht0, htn]
      norm_num
    calc
      _ = ∑ k : Fin (m + 1), (S / 2) * (t ((k : ℕ) + 1) ^ 2 - t k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hterm k
      _ = (S / 2) * ∑ k : Fin (m + 1), (t ((k : ℕ) + 1) ^ 2 - t k ^ 2) := by
        rw [Finset.mul_sum]
      _ = ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1) / 4 := by
        rw [htel]
        dsimp [S]
        ring

/-- Bài 4.3.20: tổng với 2013 điểm có giá trị `2013·2014/4`. -/
theorem weighted_sum_replacement_2013 {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1))
    (hd : DifferentiableOn ℝ f (Ioo 0 1)) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    ∃ x : Fin 2013 → ℝ, StrictMono x ∧
      (∀ k, x k ∈ Ioo (0 : ℝ) 1 ∧ deriv f (x k) ≠ 0) ∧
      (∑ k : Fin 2013, (((k : ℕ) + 1 : ℕ) : ℝ) * x k / deriv f (x k)) =
        (2013 * 2014 / 4 : ℝ) := by
  convert weighted_sum_replacement 2013 (by norm_num) hc hd h0 h1 using 1
  norm_num

end calculus.Chapter04.Section03WeightedSumReplacement
