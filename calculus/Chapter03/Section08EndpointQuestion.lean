import calculus.Chapter03.Section08OpenIntervalExtension
import calculus.Chapter03.Section02OneSided
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Tactic.Linarith

/-!
# §3.8 — Bài tập 3.8.10: hai giới hạn trên (0,+∞)

Nguồn: `source/Ch3_gioihanhamso.tex` dòng 3971–3973.
-/

set_option autoImplicit false
open Set Filter Topology

namespace calculus.Chapter03.Section08EndpointQuestion
open calculus.Chapter03.Section02
open calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section08
open calculus.Chapter03.Section08OpenIntervalExtension


theorem nonemptyUniformContinuousOn_positiveRay_has_right_limit
    (f : ℝ → ℝ) (hf : NonemptyUniformContinuousOn (Ioi (0 : ℝ)) f) :
    ∃ L : ℝ, DomainRightLimit (Ioi (0 : ℝ)) f 0 L := by
  have hsmall : UniformContinuousOn f (Ioo (0 : ℝ) 1) :=
    ((nonemptyUniformContinuousOn_iff (Ioi (0 : ℝ)) f).mp hf).2.mono (fun _ hx ↦ hx.1)
  obtain ⟨F, hF, hEq⟩ := uniformContinuousOn_openInterval_exists_continuous_extension
    (by norm_num : (0 : ℝ) < 1) hsmall
  have hT : Tendsto F (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 (F 0)) :=
    (hF 0 (by norm_num : (0 : ℝ) ∈ Icc 0 1)).tendsto.mono_left
      (nhdsWithin_mono 0 (Ioo_subset_Icc_self : Ioo (0 : ℝ) 1 ⊆ Icc 0 1))
  have hTf : Tendsto f (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 (F 0)) := by
    apply hT.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hEq x hx
  rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0 : ℝ) < 1)] at hTf
  have hacc : RightAccumulationPointOf (Ioi (0 : ℝ)) 0 := by
    intro δ hδ
    exact ⟨δ / 2, by change 0 < δ / 2; linarith, by linarith, by linarith⟩
  refine ⟨F 0, (domainRightLimit_iff_tendsto hacc).mpr ?_⟩
  simpa only [inter_self] using hTf


theorem sine_positiveRay_uniformContinuous_no_atTop_limits :
    NonemptyUniformContinuousOn (Ioi (0 : ℝ)) Real.sin ∧
      (¬ ∃ L : ℝ, DomainAtTopLimit (Ioi (0 : ℝ)) Real.sin L) ∧
      ¬ DomainAtTopTopLimit (Ioi (0 : ℝ)) Real.sin ∧
      ¬ DomainAtTopBotLimit (Ioi (0 : ℝ)) Real.sin := by
  have hphases : ∀ M : ℝ, ∃ x y : ℝ,
      x ∈ Ioi (0 : ℝ) ∧ y ∈ Ioi (0 : ℝ) ∧ M < x ∧ M < y ∧
        Real.sin x = 1 ∧ Real.sin y = -1 := by
    intro M
    obtain ⟨n, hn⟩ := exists_nat_gt ((max M 0 + Real.pi / 2) / (2 * Real.pi))
    have hden : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hprod : max M 0 + Real.pi / 2 < (n : ℝ) * (2 * Real.pi) :=
      (div_lt_iff₀ hden).mp hn
    have hM : M ≤ max M 0 := le_max_left M 0
    have h0 : (0 : ℝ) ≤ max M 0 := le_max_right M 0
    refine ⟨Real.pi / 2 + n * (2 * Real.pi),
      -Real.pi / 2 + n * (2 * Real.pi), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 < Real.pi / 2 + (n : ℝ) * (2 * Real.pi)
      linarith [Real.pi_pos]
    · change 0 < -Real.pi / 2 + (n : ℝ) * (2 * Real.pi)
      linarith
    · linarith [Real.pi_pos]
    · linarith
    · simp only [Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
    · have he : -Real.pi / 2 = -(Real.pi / 2) := by ring
      rw [he]
      simp only [Real.sin_add_nat_mul_two_pi, Real.sin_neg, Real.sin_pi_div_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨1, by norm_num⟩, ?_⟩
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro u _ v _ huv
    exact lt_of_le_of_lt (Real.abs_sin_sub_sin_le u v) huv
  · rintro ⟨L, hL⟩
    obtain ⟨M, hM⟩ := hL.2 1 (by norm_num)
    obtain ⟨x, y, hx, hy, hMx, hMy, hsx, hsy⟩ := hphases M
    have hp := hM x hx hMx
    have hn := hM y hy hMy
    rw [hsx] at hp
    rw [hsy] at hn
    linarith [(abs_lt.mp hp).2, (abs_lt.mp hn).1]
  · intro htop
    obtain ⟨B, _, hB⟩ := (domainAtTopTopLimit_iff.mp htop).2 2 (by norm_num)
    obtain ⟨x, _, hx, _, hBx, _, hsx, _⟩ := hphases B
    have hbad := hB x hx hBx
    rw [hsx] at hbad
    norm_num at hbad
  · intro hbot
    obtain ⟨B, _, hB⟩ := (domainAtTopBotLimit_iff.mp hbot).2 2 (by norm_num)
    obtain ⟨_, y, _, hy, _, hBy, _, hsy⟩ := hphases B
    have hbad := hB y hy hBy
    rw [hsy] at hbad
    norm_num at hbad

/-- Bài tập 3.8.10: hàm liên tục đều trên (0,+∞) có giới hạn hữu hạn tại 0⁺, nhưng có thể không có giới hạn tại +∞. -/
theorem uniformContinuous_positiveRay_endpoint_question_answers :
    (∀ f : ℝ → ℝ, NonemptyUniformContinuousOn (Ioi (0 : ℝ)) f →
      ∃ L : ℝ, DomainRightLimit (Ioi (0 : ℝ)) f 0 L) ∧
    ∃ f : ℝ → ℝ, NonemptyUniformContinuousOn (Ioi (0 : ℝ)) f ∧
      (¬ ∃ L : ℝ, DomainAtTopLimit (Ioi (0 : ℝ)) f L) ∧
      ¬ DomainAtTopTopLimit (Ioi (0 : ℝ)) f ∧
      ¬ DomainAtTopBotLimit (Ioi (0 : ℝ)) f := by
  exact ⟨nonemptyUniformContinuousOn_positiveRay_has_right_limit, Real.sin,
    sine_positiveRay_uniformContinuous_no_atTop_limits⟩

end calculus.Chapter03.Section08EndpointQuestion
