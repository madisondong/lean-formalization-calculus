import calculus.Chapter04.Section03

/-!
# Bài 4.3.42: phần dư nội suy bậc ba

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1414–1416. Chỉ cần khả vi ba lần trong nội khoảng; điểm `m` trong phần dư được chọn sau `x`.
-/
namespace calculus.Chapter04.Section03InterpolationRemainderExercise
open Set calculus.Chapter04.Section03


theorem third_derivative_zero_of_four_ordered_zeros
    {g g₁ g₂ g₃ : ℝ → ℝ} {a u v b : ℝ}
    (hau : a < u) (huv : u < v) (hvb : v < b)
    (hc : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g₁ t) t)
    (hd₁ : ∀ t ∈ Ioo a b, HasDerivAt g₁ (g₂ t) t)
    (hd₂ : ∀ t ∈ Ioo a b, HasDerivAt g₂ (g₃ t) t)
    (ha : g a = 0) (hu : g u = 0) (hv : g v = 0) (hb : g b = 0) :
    ∃ m ∈ Ioo a b, g₃ m = 0 := by
  have h₁ : Icc a u ⊆ Icc a b := Icc_subset_Icc le_rfl (huv.trans hvb).le
  have h₂ : Icc u v ⊆ Icc a b := Icc_subset_Icc hau.le hvb.le
  have h₃ : Icc v b ⊆ Icc a b := Icc_subset_Icc (hau.trans huv).le le_rfl
  obtain ⟨p, hp, hdp⟩ := rolle hau (hc.mono h₁)
    (fun t ht ↦ (hd t ⟨ht.1, ht.2.trans (huv.trans hvb)⟩).differentiableAt.differentiableWithinAt)
    (ha.trans hu.symm)
  obtain ⟨q, hq, hdq⟩ := rolle huv (hc.mono h₂)
    (fun t ht ↦ (hd t ⟨hau.trans ht.1, ht.2.trans hvb⟩).differentiableAt.differentiableWithinAt)
    (hu.trans hv.symm)
  obtain ⟨r, hr, hdr⟩ := rolle hvb (hc.mono h₃)
    (fun t ht ↦ (hd t ⟨(hau.trans huv).trans ht.1, ht.2⟩).differentiableAt.differentiableWithinAt)
    (hv.trans hb.symm)
  have hp' : p ∈ Ioo a b := ⟨hp.1, hp.2.trans (huv.trans hvb)⟩
  have hq' : q ∈ Ioo a b := ⟨hau.trans hq.1, hq.2.trans hvb⟩
  have hr' : r ∈ Ioo a b := ⟨(hau.trans huv).trans hr.1, hr.2⟩
  have hpq : p < q := hp.2.trans hq.1
  have hqr : q < r := hq.2.trans hr.1
  have hsubpq : Icc p q ⊆ Ioo a b := fun t ht ↦
    ⟨hp'.1.trans_le ht.1, ht.2.trans_lt hq'.2⟩
  have hsubqr : Icc q r ⊆ Ioo a b := fun t ht ↦
    ⟨hq'.1.trans_le ht.1, ht.2.trans_lt hr'.2⟩
  have hzp : g₁ p = 0 := (hd p hp').unique hdp
  have hzq : g₁ q = 0 := (hd q hq').unique hdq
  have hzr : g₁ r = 0 := (hd r hr').unique hdr
  obtain ⟨s, hs, hds⟩ := rolle hpq
    (fun t ht ↦ (hd₁ t (hsubpq ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd₁ t (hsubpq (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt)
    (hzp.trans hzq.symm)
  obtain ⟨w, hw, hdw⟩ := rolle hqr
    (fun t ht ↦ (hd₁ t (hsubqr ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd₁ t (hsubqr (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt)
    (hzq.trans hzr.symm)
  have hs' : s ∈ Ioo a b := hsubpq (Ioo_subset_Icc_self hs)
  have hw' : w ∈ Ioo a b := hsubqr (Ioo_subset_Icc_self hw)
  have hsw : s < w := hs.2.trans hw.1
  have hsubsw : Icc s w ⊆ Ioo a b := fun t ht ↦
    ⟨hs'.1.trans_le ht.1, ht.2.trans_lt hw'.2⟩
  have hzs : g₂ s = 0 := (hd₁ s hs').unique hds
  have hzw : g₂ w = 0 := (hd₁ w hw').unique hdw
  obtain ⟨m, hm, hdm⟩ := rolle hsw
    (fun t ht ↦ (hd₂ t (hsubsw ht)).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd₂ t (hsubsw (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt)
    (hzs.trans hzw.symm)
  have hm' := hsubsw (Ioo_subset_Icc_self hm)
  exact ⟨m, hm', (hd₂ m hm').unique hdm⟩


theorem cubic_interpolation_remainder
    {f f₁ f₂ f₃ : ℝ → ℝ} {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f₁ t) t)
    (hd₁ : ∀ t ∈ Ioo a b, HasDerivAt f₁ (f₂ t) t)
    (hd₂ : ∀ t ∈ Ioo a b, HasDerivAt f₂ (f₃ t) t)
    (ha : f a = 0) (hb : f b = 0) (hz : f c = 0)
    (x : ℝ) (hx : x ∈ Ioo a b) :
    ∃ m ∈ Ioo a b, f x = (1 / 6 : ℝ) * (x - a) * (x - b) * (x - c) * f₃ m := by
  by_cases hxc : x = c
  · refine ⟨(a + b) / 2, ⟨by linarith [hc.1, hc.2], by linarith [hc.1, hc.2]⟩, ?_⟩
    simp [hxc, hz]
  · let P : ℝ → ℝ := fun t ↦ (t - a) * (t - b) * (t - c)
    let P₁ : ℝ → ℝ := fun t ↦
      (t - b) * (t - c) + (t - a) * (t - c) + (t - a) * (t - b)
    let P₂ : ℝ → ℝ := fun t ↦ 6 * t - 2 * (a + b + c)
    have hP (t : ℝ) : HasDerivAt P (P₁ t) t := by
      have hA := (hasDerivAt_id t).fun_sub (hasDerivAt_const t a)
      have hB := (hasDerivAt_id t).fun_sub (hasDerivAt_const t b)
      have hC := (hasDerivAt_id t).fun_sub (hasDerivAt_const t c)
      apply ((hA.fun_mul hB).fun_mul hC).congr_deriv
      dsimp [P₁]
      ring
    have hP₁ (t : ℝ) : HasDerivAt P₁ (P₂ t) t := by
      have hA := (hasDerivAt_id t).fun_sub (hasDerivAt_const t a)
      have hB := (hasDerivAt_id t).fun_sub (hasDerivAt_const t b)
      have hC := (hasDerivAt_id t).fun_sub (hasDerivAt_const t c)
      apply (((hB.fun_mul hC).fun_add (hA.fun_mul hC)).fun_add
        (hA.fun_mul hB)).congr_deriv
      dsimp [P₂]
      ring
    have hP₂ (t : ℝ) : HasDerivAt P₂ 6 t := by
      simpa only [P₂, id_eq, mul_one] using ((hasDerivAt_id t).const_mul 6).sub_const
        (2 * (a + b + c))
    let K : ℝ := f x / P x
    let g : ℝ → ℝ := fun t ↦ f t - K * P t
    let g₁ : ℝ → ℝ := fun t ↦ f₁ t - K * P₁ t
    let g₂ : ℝ → ℝ := fun t ↦ f₂ t - K * P₂ t
    let g₃ : ℝ → ℝ := fun t ↦ f₃ t - K * 6
    have hgc : ContinuousOn g (Icc a b) :=
      hf.sub (continuous_const.mul
        (((continuous_id.sub continuous_const).mul
          (continuous_id.sub continuous_const)).mul
          (continuous_id.sub continuous_const))).continuousOn
    have hgd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt g (g₁ t) t :=
      (hd t ht).fun_sub ((hP t).const_mul K)
    have hgd₁ (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt g₁ (g₂ t) t :=
      (hd₁ t ht).fun_sub ((hP₁ t).const_mul K)
    have hgd₂ (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt g₂ (g₃ t) t :=
      (hd₂ t ht).fun_sub ((hP₂ t).const_mul K)
    have hPa : P a = 0 := by simp [P]
    have hPb : P b = 0 := by simp [P]
    have hPc : P c = 0 := by simp [P]
    have hPx : P x ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx.1.ne') (sub_ne_zero.mpr hx.2.ne))
        (sub_ne_zero.mpr hxc)
    have hga : g a = 0 := by simp [g, ha, hPa]
    have hgb : g b = 0 := by simp [g, hb, hPb]
    have hgz : g c = 0 := by simp [g, hz, hPc]
    have hgx : g x = 0 := by
      dsimp [g, K]
      rw [div_mul_cancel₀ _ hPx, sub_self]
    have hex : ∃ m ∈ Ioo a b, g₃ m = 0 := by
      by_cases hcx : c < x
      · exact third_derivative_zero_of_four_ordered_zeros hc.1 hcx hx.2
          hgc hgd hgd₁ hgd₂ hga hgz hgx hgb
      · have hxc' : x < c := lt_of_le_of_ne (le_of_not_gt hcx) hxc
        exact third_derivative_zero_of_four_ordered_zeros hx.1 hxc' hc.2
          hgc hgd hgd₁ hgd₂ hga hgx hgz hgb
    obtain ⟨m, hm, he⟩ := hex
    have he' : f₃ m = K * 6 := by
      dsimp [g₃] at he
      exact sub_eq_zero.mp he
    refine ⟨m, hm, ?_⟩
    rw [he']
    dsimp [K]
    field_simp [hPx]
    dsimp [P]
    ring

/-- Bài 42: phần dư nội suy bậc ba cho hàm liên tục trên đoạn và khả vi ba lần trong nội khoảng. -/
theorem source_cubic_interpolation_remainder {f : ℝ → ℝ} {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hd₁ : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (deriv f) t)
    (hd₂ : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (deriv (deriv f)) t)
    (ha : f a = 0) (hb : f b = 0) (hz : f c = 0)
    (x : ℝ) (hx : x ∈ Ioo a b) :
    ∃ m ∈ Ioo a b,
      f x = (1 / 6 : ℝ) * (x - a) * (x - b) * (x - c) * deriv (deriv (deriv f)) m :=
  cubic_interpolation_remainder hc hf
    (fun t ht ↦ (hd t ht).hasDerivAt)
    (fun t ht ↦ (hd₁ t ht).hasDerivAt)
    (fun t ht ↦ (hd₂ t ht).hasDerivAt) ha hb hz x hx

end calculus.Chapter04.Section03InterpolationRemainderExercise
