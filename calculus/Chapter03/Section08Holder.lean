import calculus.Chapter03.Section08
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# §3.8 — liên tục Hölder và liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3799–3813, Định nghĩa 3.8.7 và Định lí 3.8.8.
-/

set_option autoImplicit false
open Set
open scoped NNReal

namespace calculus.Chapter03.Section08Holder
open calculus.Chapter03.Section08

/-- Định nghĩa 3.8.7: liên tục Hölder trên D≠∅, với L≥0 và α>0. -/
def NonemptyHolderContinuousOn (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  D.Nonempty ∧ ∃ L : ℝ, 0 ≤ L ∧ ∃ α : ℝ, 0 < α ∧
    ∀ u ∈ D, ∀ v ∈ D, |f u - f v| ≤ L * |u - v| ^ α


def NonemptyLipschitzOn (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  D.Nonempty ∧ ∃ L : ℝ, 0 ≤ L ∧
    ∀ u ∈ D, ∀ v ∈ D, |f u - f v| ≤ L * |u - v|


theorem nonemptyLipschitzOn_iff_mathlib {D : Set ℝ} {f : ℝ → ℝ} :
    NonemptyLipschitzOn D f ↔ D.Nonempty ∧ ∃ L : ℝ≥0, LipschitzOnWith L f D := by
  constructor
  · rintro ⟨hD, L, hL, hf⟩
    refine ⟨hD, NNReal.mk L hL, ?_⟩
    rw [lipschitzOnWith_iff_dist_le_mul]
    simpa only [Real.dist_eq, NNReal.coe_mk] using hf
  · rintro ⟨hD, L, hf⟩
    exact ⟨hD, L, L.coe_nonneg, by simpa only [Real.dist_eq] using hf.dist_le_mul⟩


theorem nonemptyLipschitzOn_holder {D : Set ℝ} {f : ℝ → ℝ}
    (hf : NonemptyLipschitzOn D f) : NonemptyHolderContinuousOn D f := by
  obtain ⟨hD, L, hL, hh⟩ := hf
  exact ⟨hD, L, hL, 1, by norm_num, by simpa only [Real.rpow_one] using hh⟩


theorem zero_holder_bound_constant {D : Set ℝ} {f : ℝ → ℝ} {α : ℝ}
    (hD : D.Nonempty)
    (hb : ∀ u ∈ D, ∀ v ∈ D, |f u - f v| ≤ (0 : ℝ) * |u - v| ^ α) :
    ∃ c : ℝ, ∀ u ∈ D, f u = c := by
  obtain ⟨a, ha⟩ := hD
  refine ⟨f a, fun u hu ↦ ?_⟩
  have hz : |f u - f a| ≤ 0 := by
    simpa only [zero_mul] using hb u hu a ha
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))


theorem holder_delta_power_identity {ε L α : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hα : 0 < α) :
    ((ε / L) ^ (1 / α)) ^ α = ε / L := by
  rw [← Real.rpow_mul (div_pos hε hL).le,
    one_div_mul_cancel hα.ne', Real.rpow_one]

/-- Định lí 3.8.8: liên tục Hölder suy ra liên tục đều. -/
theorem nonemptyHolderContinuousOn_uniformContinuous {D : Set ℝ} {f : ℝ → ℝ}
    (hf : NonemptyHolderContinuousOn D f) : NonemptyUniformContinuousOn D f := by
  obtain ⟨hD, L, hL, α, hα, hb⟩ := hf
  by_cases hL0 : L = 0
  · have hb0 : ∀ u ∈ D, ∀ v ∈ D,
        |f u - f v| ≤ (0 : ℝ) * |u - v| ^ α := by
      simpa only [hL0] using hb
    obtain ⟨c, hc⟩ := zero_holder_bound_constant hD hb0
    have hconst := nonemptyUniformContinuousOn_const D hD c
    refine ⟨hD, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hconst.2 ε hε
    refine ⟨δ, hδ, ?_⟩
    intro u hu v hv huv
    simpa only [hc u hu, hc v hv] using hd u hu v hv huv
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    refine ⟨hD, ?_⟩
    intro ε hε
    refine ⟨(ε / L) ^ (1 / α), Real.rpow_pos_of_pos (div_pos hε hLpos) _, ?_⟩
    intro u hu v hv huv
    calc
      |f u - f v| ≤ L * |u - v| ^ α := hb u hu v hv
      _ < L * (((ε / L) ^ (1 / α)) ^ α) :=
        mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (abs_nonneg _) huv hα) hLpos
      _ = L * (ε / L) := by rw [holder_delta_power_identity hε hLpos hα]
      _ = ε := mul_div_cancel₀ ε hLpos.ne'

end calculus.Chapter03.Section08Holder
