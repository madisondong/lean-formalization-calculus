import calculus.Chapter04.Section04AsymptotesWithin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bài 4.4.13: phân loại đầy đủ tiệm cận

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 2748–2756. Mỗi phía tiếp cận và mỗi đầu vô cùng cần có bộ lọc không suy biến.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04AsymptoteClassificationSupport
open Set Filter
open scoped Topology
open calculus.Chapter04.Section04Asymptotes
open calculus.Chapter04.Section04AsymptotesWithin

theorem full_tail_horizontal_iff {D : Set ℝ} (hT : ∀ᶠ x : ℝ in atTop, x ∈ D)
    (hB : ∀ᶠ x : ℝ in atBot, x ∈ D) (f : ℝ → ℝ) (b : ℝ) :
    HasHorizontalAsymptoteWithin f D b ↔ HasHorizontalAsymptote f b := by
  have htop : atTop ⊓ 𝓟 D = atTop := inf_eq_left.mpr (le_principal_iff.mpr hT)
  have hbot : atBot ⊓ 𝓟 D = atBot := inf_eq_left.mpr (le_principal_iff.mpr hB)
  rw [hasHorizontalAsymptoteWithin_iff, htop, hbot, HasHorizontalAsymptote]
  constructor
  · rintro (h | h)
    · exact Or.inl h.2
    · exact Or.inr h.2
  · rintro (h | h)
    · exact Or.inl ⟨inferInstance, h⟩
    · exact Or.inr ⟨inferInstance, h⟩

theorem full_tail_oblique_iff {D : Set ℝ} (hT : ∀ᶠ x : ℝ in atTop, x ∈ D)
    (hB : ∀ᶠ x : ℝ in atBot, x ∈ D) (f : ℝ → ℝ) (m b : ℝ) :
    HasObliqueAsymptoteWithin f D m b ↔ HasObliqueAsymptote f m b := by
  have htop : atTop ⊓ 𝓟 D = atTop := inf_eq_left.mpr (le_principal_iff.mpr hT)
  have hbot : atBot ⊓ 𝓟 D = atBot := inf_eq_left.mpr (le_principal_iff.mpr hB)
  rw [hasObliqueAsymptoteWithin_filter_iff, htop, hbot, HasObliqueAsymptote]
  constructor
  · rintro ⟨hm, h | h⟩
    · exact ⟨hm, Or.inl h.2⟩
    · exact ⟨hm, Or.inr h.2⟩
  · rintro ⟨hm, h | h⟩
    · exact ⟨hm, Or.inl ⟨inferInstance, h⟩⟩
    · exact ⟨hm, Or.inr ⟨inferInstance, h⟩⟩


theorem no_vertical_of_finite_sides {D : Set ℝ} {f : ℝ → ℝ} {a r l : ℝ}
    (hr : Tendsto f (𝓝[>] a) (𝓝 r)) (hl : Tendsto f (𝓝[<] a) (𝓝 l)) :
    ¬ HasVerticalAsymptoteWithinAt f D a := by
  rw [hasVerticalAsymptoteWithinAt_iff]
  rintro (h | h)
  · let : NeBot (𝓝[D ∩ Ioi a] a) := h.1
    have hf : Tendsto f (𝓝[D ∩ Ioi a] a) (𝓝 r) :=
      hr.mono_left (nhdsWithin_mono a inter_subset_right)
    rcases h.2 with ht | hb
    · exact not_tendsto_atTop_of_tendsto_nhds hf ht
    · exact not_tendsto_atBot_of_tendsto_nhds hf hb
  · let : NeBot (𝓝[D ∩ Iio a] a) := h.1
    have hf : Tendsto f (𝓝[D ∩ Iio a] a) (𝓝 l) :=
      hl.mono_left (nhdsWithin_mono a inter_subset_right)
    rcases h.2 with ht | hb
    · exact not_tendsto_atTop_of_tendsto_nhds hf ht
    · exact not_tendsto_atBot_of_tendsto_nhds hf hb

theorem no_vertical_of_continuousAt {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) : ¬ HasVerticalAsymptoteWithinAt f D a :=
  no_vertical_of_finite_sides (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hf.tendsto.mono_left nhdsWithin_le_nhds)


theorem vertical_of_right_bot {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hD : ∀ᶠ x in 𝓝[>] a, x ∈ D) (hf : Tendsto f (𝓝[>] a) atBot) :
    HasVerticalAsymptoteWithinAt f D a := by
  have heq : 𝓝[D ∩ Ioi a] a = 𝓝[>] a := by
    simpa only [Set.ofPred_mem_eq] using nhdsWithin_inter_of_mem hD
  rw [hasVerticalAsymptoteWithinAt_iff, heq]
  exact Or.inl ⟨inferInstance, Or.inr hf⟩

theorem vertical_of_left_bot {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hD : ∀ᶠ x in 𝓝[<] a, x ∈ D) (hf : Tendsto f (𝓝[<] a) atBot) :
    HasVerticalAsymptoteWithinAt f D a := by
  have heq : 𝓝[D ∩ Iio a] a = 𝓝[<] a := by
    simpa only [Set.ofPred_mem_eq] using nhdsWithin_inter_of_mem hD
  rw [hasVerticalAsymptoteWithinAt_iff, heq]
  exact Or.inr ⟨inferInstance, Or.inr hf⟩

theorem vertical_of_right_top {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hD : ∀ᶠ x in 𝓝[>] a, x ∈ D) (hf : Tendsto f (𝓝[>] a) atTop) :
    HasVerticalAsymptoteWithinAt f D a := by
  have heq : 𝓝[D ∩ Ioi a] a = 𝓝[>] a := by
    simpa only [Set.ofPred_mem_eq] using nhdsWithin_inter_of_mem hD
  rw [hasVerticalAsymptoteWithinAt_iff, heq]
  exact Or.inl ⟨inferInstance, Or.inl hf⟩


theorem affine_parameters_iff {F : Filter ℝ} [NeBot F] {f : ℝ → ℝ}
    (hInv : Tendsto (fun x : ℝ ↦ x⁻¹) F (𝓝 0))
    (hNe : ∀ᶠ x : ℝ in F, x ≠ 0) {m₀ b₀ : ℝ}
    (hknown : Tendsto (fun x ↦ f x - (m₀ * x + b₀)) F (𝓝 0)) (m b : ℝ) :
    Tendsto (fun x ↦ f x - (m * x + b)) F (𝓝 0) ↔ m = m₀ ∧ b = b₀ := by
  have hk := (affine_residual_limit_iff hInv hNe f m₀ b₀).mp hknown
  constructor
  · intro h
    have hnew := (affine_residual_limit_iff hInv hNe f m b).mp h
    have hm : m = m₀ := tendsto_nhds_unique hnew.1 hk.1
    subst m
    exact ⟨rfl, tendsto_nhds_unique hnew.2 hk.2⟩
  · rintro ⟨rfl, rfl⟩
    exact hknown

theorem no_horizontal_at_end_of_nonzero_affine {F : Filter ℝ} [NeBot F]
    {f : ℝ → ℝ} {m b : ℝ} (hm : m ≠ 0)
    (hparams : ∀ u v : ℝ,
      Tendsto (fun x ↦ f x - (u * x + v)) F (𝓝 0) ↔ u = m ∧ v = b) (v : ℝ) :
    ¬ Tendsto f F (𝓝 v) := by
  intro hf
  have hr : Tendsto (fun x ↦ f x - (0 * x + v)) F (𝓝 0) := by
    simpa only [zero_mul, zero_add, sub_self] using hf.sub_const v
  exact hm ((hparams 0 v).mp hr).1.symm

theorem sine_product_tendsto_zero {F : Filter ℝ} {g : ℝ → ℝ}
    (hg : Tendsto g F (𝓝 0)) : Tendsto (fun x ↦ Real.sin x * g x) F (𝓝 0) :=
  bdd_le_mul_tendsto_zero (Eventually.of_forall Real.neg_one_le_sin)
    (Eventually.of_forall Real.sin_le_one) hg


theorem sine_not_tendsto_zero_atBot : ¬ Tendsto Real.sin atBot (𝓝 0) := by
  intro h
  have hπ : 0 < 2 * Real.pi := by positivity
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) * (2 * Real.pi)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).atTop_mul_const hπ
  have hseq : Tendsto (fun n : ℕ ↦ Real.pi / 2 - (n : ℝ) * (2 * Real.pi)) atTop atBot := by
    have hh := tendsto_atBot_add_const_left atTop (Real.pi / 2)
      (tendsto_neg_atTop_atBot.comp hn)
    exact hh.congr (fun n ↦ by dsimp only [Function.comp_def]; ring)
  have hval (n : ℕ) : Real.sin (Real.pi / 2 - (n : ℝ) * (2 * Real.pi)) = 1 := by
    rw [Real.sin_sub_nat_mul_two_pi, Real.sin_pi_div_two]
  have hone : Tendsto (fun n : ℕ ↦ Real.sin (Real.pi / 2 - (n : ℝ) * (2 * Real.pi)))
      atTop (𝓝 1) := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).congr
        (fun n ↦ (hval n).symm)
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique (h.comp hseq) hone
  norm_num at he

end calculus.Chapter04.Section04AsymptoteClassificationSupport
