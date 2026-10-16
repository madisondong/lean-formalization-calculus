import calculus.Chapter03.Section08
import calculus.Chapter02.Section03
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

/-!
# §3.8 — tiêu chuẩn dãy của tính liên tục đều

Nguồn: `source/Ch3_gioihanhamso.tex`, dòng 3842–3856, Định lí 3.8.12.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08SequenceCriterion
open calculus.Chapter03.Section08
open calculus.Chapter02.Section03


def PositiveIndexUniformContinuitySequenceCriterionOn (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ u v : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → u n ∈ D) →
    (∀ n : ℕ, 1 ≤ n → v n ∈ D) →
      ConvergesTo (fun n ↦ u n - v n) 0 →
        ConvergesTo (fun n ↦ f (u n) - f (v n)) 0


def AllNatUniformContinuitySequenceCriterionOn (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ u v : ℕ → ℝ, (∀ n : ℕ, u n ∈ D) → (∀ n : ℕ, v n ∈ D) →
    ConvergesTo (fun n ↦ u n - v n) 0 →
      ConvergesTo (fun n ↦ f (u n) - f (v n)) 0


theorem nonemptyUniformContinuousOn_sequenceCondition {D : Set ℝ} {f : ℝ → ℝ}
    (hf : NonemptyUniformContinuousOn D f) : PositiveIndexUniformContinuitySequenceCriterionOn D f := by
  intro u v hu hv huv ε hε
  obtain ⟨δ, hδ, hb⟩ := hf.2 ε hε
  obtain ⟨N, hN, hclose⟩ := huv δ hδ
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have hnpos : 1 ≤ n := hN.trans hn
  have hdist : |u n - v n| < δ := by
    simpa only [sub_zero] using hclose n hn
  simpa only [sub_zero] using hb (u n) (hu n hnpos) (v n) (hv n hnpos) hdist


theorem not_uniformContinuityConditionOn_iff (D : Set ℝ) (f : ℝ → ℝ) :
    ¬ UniformContinuityConditionOn D f ↔
      ∃ ε > 0, ∀ δ > 0, ∃ u ∈ D, ∃ v ∈ D,
        |u - v| < δ ∧ ε ≤ |f u - f v| := by
  classical
  unfold UniformContinuityConditionOn
  push Not
  rfl


theorem nonuniform_sequences {D : Set ℝ} {f : ℝ → ℝ}
    (hD : D.Nonempty) (hno : ¬ UniformContinuityConditionOn D f) :
    ∃ ε > 0, ∃ u v : ℕ → ℝ,
      (∀ n : ℕ, u n ∈ D ∧ v n ∈ D) ∧
      (∀ n : ℕ, 1 ≤ n → |u n - v n| < 1 / (n : ℝ) ∧
        ε ≤ |f (u n) - f (v n)|) ∧
      ConvergesTo (fun n ↦ u n - v n) 0 ∧
      ¬ ConvergesTo (fun n ↦ f (u n) - f (v n)) 0 := by
  classical
  obtain ⟨ε, hε, hfail⟩ := (not_uniformContinuityConditionOn_iff D f).mp hno
  obtain ⟨p, hp⟩ := hD
  have hw : ∀ n : ℕ, ∃ u ∈ D, ∃ v ∈ D,
      1 ≤ n → |u - v| < 1 / (n : ℝ) ∧ ε ≤ |f u - f v| := by
    intro n
    by_cases hn : 1 ≤ n
    · have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      obtain ⟨u, hu, v, hv, hb⟩ := hfail (1 / (n : ℝ)) (one_div_pos.mpr hnpos)
      exact ⟨u, hu, v, hv, fun _ ↦ hb⟩
    · exact ⟨p, hp, p, hp, fun h ↦ False.elim (hn h)⟩
  choose u hu v hv hb using hw
  have hinput : ConvergesTo (fun n ↦ u n - v n) 0 := by
    intro η hη
    obtain ⟨N, hN, hsmall⟩ := reciprocal_converges η hη
    refine ⟨N, hN, fun n hn ↦ ?_⟩
    have hn1 : 1 ≤ n := hN.trans hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hrec : 1 / (n : ℝ) < η := by
      simpa only [sub_zero, abs_of_pos (one_div_pos.mpr hnpos)] using hsmall n hn
    simpa only [sub_zero] using (hb n hn1).1.trans hrec
  have houtput : ¬ ConvergesTo (fun n ↦ f (u n) - f (v n)) 0 := by
    intro hlim
    obtain ⟨N, hN, hsmall⟩ := hlim ε hε
    have hlt : |f (u N) - f (v N)| < ε := by
      simpa only [sub_zero] using hsmall N le_rfl
    exact (not_lt_of_ge (hb N hN).2) hlt
  exact ⟨ε, hε, u, v, fun n ↦ ⟨hu n, hv n⟩, hb, hinput, houtput⟩

/-- Định lí 3.8.12: trên D≠∅, liên tục đều tương đương tiêu chuẩn dãy có các số hạng từ chỉ số 1 thuộc D. -/
theorem nonemptyUniformContinuousOn_iff_sequenceCondition {D : Set ℝ} {f : ℝ → ℝ}
    (hD : D.Nonempty) : NonemptyUniformContinuousOn D f ↔ PositiveIndexUniformContinuitySequenceCriterionOn D f := by
  constructor
  · exact nonemptyUniformContinuousOn_sequenceCondition
  · intro hseq
    refine ⟨hD, ?_⟩
    by_contra hno
    obtain ⟨ε, hε, u, v, hmem, _, hinput, houtput⟩ := nonuniform_sequences hD hno
    exact houtput (hseq u v (fun n _ ↦ (hmem n).1) (fun n _ ↦ (hmem n).2) hinput)


theorem positiveIndexUniformContinuitySequenceCriterionOn_iff_allNat {D : Set ℝ} {f : ℝ → ℝ}
    (hD : D.Nonempty) : PositiveIndexUniformContinuitySequenceCriterionOn D f ↔ AllNatUniformContinuitySequenceCriterionOn D f := by
  constructor
  · intro h u v hu hv huv
    exact h u v (fun n _ ↦ hu n) (fun n _ ↦ hv n) huv
  · intro h u v hu hv huv
    obtain ⟨p, hp⟩ := hD
    let u₀ : ℕ → ℝ := fun n ↦ if n = 0 then p else u n
    let v₀ : ℕ → ℝ := fun n ↦ if n = 0 then p else v n
    have hu₀mem : ∀ n : ℕ, u₀ n ∈ D := by
      intro n
      by_cases hn : n = 0
      · simpa only [u₀, if_pos hn] using hp
      · simpa only [u₀, if_neg hn] using hu n (Nat.one_le_iff_ne_zero.mpr hn)
    have hv₀mem : ∀ n : ℕ, v₀ n ∈ D := by
      intro n
      by_cases hn : n = 0
      · simpa only [v₀, if_pos hn] using hp
      · simpa only [v₀, if_neg hn] using hv n (Nat.one_le_iff_ne_zero.mpr hn)
    have hu₀eq : ∀ n : ℕ, 1 ≤ n → u₀ n = u n := by
      intro n hn
      exact if_neg (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
    have hv₀eq : ∀ n : ℕ, 1 ≤ n → v₀ n = v n := by
      intro n hn
      exact if_neg (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
    have hinputEq : ∀ n : ℕ, 1 ≤ n → u₀ n - v₀ n = u n - v n := by
      intro n hn
      rw [hu₀eq n hn, hv₀eq n hn]
    have hinput₀ : ConvergesTo (fun n ↦ u₀ n - v₀ n) 0 :=
      (convergesTo_congr hinputEq).mpr huv
    have houtput₀ : ConvergesTo (fun n ↦ f (u₀ n) - f (v₀ n)) 0 :=
      h u₀ v₀ hu₀mem hv₀mem hinput₀
    have houtputEq : ∀ n : ℕ, 1 ≤ n → f (u₀ n) - f (v₀ n) = f (u n) - f (v n) := by
      intro n hn
      rw [hu₀eq n hn, hv₀eq n hn]
    exact (convergesTo_congr houtputEq).mp houtput₀


theorem nonemptyUniformContinuousOn_iff_allNatSequenceCondition {D : Set ℝ} {f : ℝ → ℝ}
    (hD : D.Nonempty) : NonemptyUniformContinuousOn D f ↔ AllNatUniformContinuitySequenceCriterionOn D f := by
  rw [nonemptyUniformContinuousOn_iff_sequenceCondition hD, positiveIndexUniformContinuitySequenceCriterionOn_iff_allNat hD]

end calculus.Chapter03.Section08SequenceCriterion
