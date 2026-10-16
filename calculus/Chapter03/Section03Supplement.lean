import calculus.Chapter03.Section03
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.MetricSpace.Cauchy

/-!
§3.3 — các kết quả bổ sung

Nguồn: dòng 2140–2290.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section03Supplement
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02Infinite calculus.Chapter03.Section03
open calculus.Chapter02.Section03

/-- Ví dụ 3.3.8: thương chứa sin trên miền tự nhiên. -/
theorem sine_div_domainLimit :
    DomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ Real.sin x / x) 0 1 := by
  have hs : DomainLimit (univ \ {(0 : ℝ)}) Real.sinc 0 1 := by
    simpa only [Real.sinc_zero] using domainLimit_of_continuousAt
      (univ_diff_accumulation 0) (show ContinuousAt Real.sinc 0 from Real.continuous_sinc.continuousAt)
  exact (domainLimit_congr_punctured (fun x _ hx ↦ (Real.sinc_of_ne_zero hx).symm)).mpr hs

/-- Dòng 2190: không thể chọn δ=ε<π/2 với mọi ε>0. -/
theorem printed_cosine_delta_restriction_false :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, δ = ε ∧ δ < Real.pi / 2 := by
  intro h
  obtain ⟨δ, hd, hp⟩ := h Real.pi Real.pi_pos
  rw [hd] at hp
  linarith [Real.pi_pos]


theorem cosine_domainLimit (a : ℝ) : DomainLimit univ Real.cos a (Real.cos a) := by
  refine ⟨univ_accumulation a, fun ε hε ↦ ⟨ε, hε, fun x _ _ hx ↦ ?_⟩⟩
  exact (Real.abs_cos_sub_cos_le x a).trans_lt hx

/-- dòng 2205: định lí kẹp từ bên trái, kèm giả thiết điểm tụ trái. -/
theorem domainLeftLimit_squeeze {D : Set ℝ} {f g h : ℝ → ℝ} {a L : ℝ}
    (hf : DomainLeftLimit D f a L) (hh : DomainLeftLimit D h a L)
    (hb : ∃ δ > 0, ∀ x ∈ D, a - δ < x → x < a → f x ≤ g x ∧ g x ≤ h x) :
    DomainLeftLimit D g a L := by
  apply domainLeftLimit_iff_restricted.mpr
  apply domainLimit_squeeze (domainLeftLimit_iff_restricted.mp hf) (domainLeftLimit_iff_restricted.mp hh)
  obtain ⟨δ, hδ, hbound⟩ := hb
  exact ⟨δ, hδ, fun x hx _ hl _ ↦ hbound x hx.1 hl hx.2⟩

/-- dòng 2205: định lí kẹp từ bên phải, kèm giả thiết điểm tụ phải. -/
theorem domainRightLimit_squeeze {D : Set ℝ} {f g h : ℝ → ℝ} {a L : ℝ}
    (hf : DomainRightLimit D f a L) (hh : DomainRightLimit D h a L)
    (hb : ∃ δ > 0, ∀ x ∈ D, a < x → x < a + δ → f x ≤ g x ∧ g x ≤ h x) :
    DomainRightLimit D g a L := by
  apply domainRightLimit_iff_restricted.mpr
  apply domainLimit_squeeze (domainRightLimit_iff_restricted.mp hf) (domainRightLimit_iff_restricted.mp hh)
  obtain ⟨δ, hδ, hbound⟩ := hb
  exact ⟨δ, hδ, fun x hx _ _ hr ↦ hbound x hx.1 hx.2 hr⟩

/-- Định lí 3.3.9: định lí kẹp tại +∞ trên miền chung không bị chặn trên. -/
theorem domainAtTopLimit_squeeze {D : Set ℝ} {f g h : ℝ → ℝ} {L : ℝ}
    (hf : DomainAtTopLimit D f L) (hh : DomainAtTopLimit D h L)
    (hb : ∃ B > 0, ∀ x ∈ D, B < x → f x ≤ g x ∧ g x ≤ h x) :
    DomainAtTopLimit D g L := by
  apply (domainAtTopLimit_iff_tendsto hf.1).mpr
  obtain ⟨B, _, hbound⟩ := hb
  have hB : ∀ᶠ x in (atTop ⊓ 𝓟 D), B < x :=
    (eventually_gt_atTop B).filter_mono inf_le_left
  have hD : ∀ᶠ x in (atTop ⊓ 𝓟 D), x ∈ D :=
    (show ∀ᶠ x in 𝓟 D, x ∈ D from eventually_mem_principal D).filter_mono inf_le_right
  have hbounds : ∀ᶠ x in (atTop ⊓ 𝓟 D), f x ≤ g x ∧ g x ≤ h x := by
    filter_upwards [hB, hD] with x hx hxD
    exact hbound x hxD hx
  exact ((domainAtTopLimit_iff_tendsto hf.1).mp hf).squeeze'
    ((domainAtTopLimit_iff_tendsto hh.1).mp hh)
    (hbounds.mono fun _ hx ↦ hx.1) (hbounds.mono fun _ hx ↦ hx.2)

/-- dòng 2205: định lí kẹp tại −∞, kèm giả thiết miền không bị chặn dưới. -/
theorem domainAtBotLimit_squeeze {D : Set ℝ} {f g h : ℝ → ℝ} {L : ℝ}
    (hf : DomainAtBotLimit D f L) (hh : DomainAtBotLimit D h L)
    (hb : ∃ B < 0, ∀ x ∈ D, x < B → f x ≤ g x ∧ g x ≤ h x) :
    DomainAtBotLimit D g L := by
  apply (domainAtBotLimit_iff_tendsto hf.1).mpr
  obtain ⟨B, _, hbound⟩ := hb
  have hB : ∀ᶠ x in (atBot ⊓ 𝓟 D), x < B :=
    (eventually_lt_atBot B).filter_mono inf_le_left
  have hD : ∀ᶠ x in (atBot ⊓ 𝓟 D), x ∈ D :=
    (show ∀ᶠ x in 𝓟 D, x ∈ D from eventually_mem_principal D).filter_mono inf_le_right
  have hbounds : ∀ᶠ x in (atBot ⊓ 𝓟 D), f x ≤ g x ∧ g x ≤ h x := by
    filter_upwards [hB, hD] with x hx hxD
    exact hbound x hxD hx
  exact ((domainAtBotLimit_iff_tendsto hf.1).mp hf).squeeze'
    ((domainAtBotLimit_iff_tendsto hh.1).mp hh)
    (hbounds.mono fun _ hx ↦ hx.1) (hbounds.mono fun _ hx ↦ hx.2)


def exponentialLimitDomain : Set ℝ := {x : ℝ | x ≠ 0 ∧ 0 < 1 + 1 / x}

/-- Ví dụ 3.3.10: (1+1/x)^x→e khi x→+∞. -/
theorem e_atTop_domainLimit :
    DomainAtTopLimit exponentialLimitDomain (fun x ↦ (1 + 1 / x) ^ x) (Real.exp 1) := by
  have hD : ¬ BddAbove exponentialLimitDomain := by
    rintro ⟨M, hM⟩
    have hx : 0 < max M 0 + 1 := by linarith [le_max_right M (0 : ℝ)]
    have hd : max M 0 + 1 ∈ exponentialLimitDomain :=
      ⟨ne_of_gt hx, by positivity⟩
    have hh := hM hd
    linarith [le_max_left M (0 : ℝ)]
  exact (domainAtTopLimit_iff_tendsto hD).mpr
    ((Real.tendsto_one_add_div_rpow_exp 1).mono_left inf_le_left)


theorem domainLimit_own_value_iff_continuousAt {f : ℝ → ℝ} {a : ℝ} :
    DomainLimit univ f a (f a) ↔ ContinuousAt f a := by
  constructor
  · intro h
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := h.2 ε hε
    refine ⟨δ, hδ, fun x hx ↦ ?_⟩
    by_cases heq : x = a
    · simpa only [heq, dist_self] using hε
    · simpa only [Real.dist_eq] using hh x (mem_univ _)
        (abs_pos.mpr (sub_ne_zero.mpr heq)) (by simpa only [Real.dist_eq] using hx)
  · exact domainLimit_of_continuousAt (univ_accumulation a)


theorem domainLimit_own_value_iff_continuousWithinAt {E : Set ℝ} {f : ℝ → ℝ} {L : ℝ}
    (ha : AccumulationPointOf E L) : DomainLimit E f L (f L) ↔ ContinuousWithinAt f E L := by
  constructor
  · intro hf
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := hf.2 ε hε
    refine ⟨δ, hδ, fun x hxE hx ↦ ?_⟩
    by_cases heq : x = L
    · simpa only [heq, dist_self] using hε
    · simpa only [Real.dist_eq] using hh x hxE
        (abs_pos.mpr (sub_ne_zero.mpr heq)) (by simpa only [Real.dist_eq] using hx)
  · intro hf
    exact (domainLimit_iff_tendsto ha).mpr
      (hf.tendsto.mono_left (nhdsWithin_mono L sdiff_subset))


theorem domainLimit_comp_domains {D E : Set ℝ} {f g : ℝ → ℝ} {a L : ℝ}
    (hg : DomainLimit D g a L) (hf : DomainLimit E f L (f L))
    (hL : L ∈ E) (himage : ∀ x ∈ D, g x ∈ E) :
    DomainLimit D (fun x ↦ f (g x)) a (f L) := by
  have hc : ContinuousWithinAt f (insert L E) L := by
    simpa only [insert_eq_of_mem hL] using
      (domainLimit_own_value_iff_continuousWithinAt hf.1).mp hf
  have hmem : ∀ᶠ x in 𝓝[D \ {a}] a, g x ∈ insert L E := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mem_insert_of_mem L (himage x hx.1)
  exact (domainLimit_iff_tendsto hg.1).mpr
    (hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨puncturedLimitCondition_iff_tendsto.mp hg.2, hmem⟩))

/-- Định lí 3.3.11: giới hạn hàm hợp, cho phép g(x)=L. -/
theorem domainLimit_comp {D : Set ℝ} {f g : ℝ → ℝ} {a L : ℝ}
    (hg : DomainLimit D g a L) (hf : DomainLimit univ f L (f L)) :
    DomainLimit D (fun x ↦ f (g x)) a (f L) :=
  (domainLimit_iff_tendsto hg.1).mpr
    (((domainLimit_own_value_iff_continuousAt.mp hf).tendsto.comp
      (puncturedLimitCondition_iff_tendsto.mp hg.2)))


noncomputable def signedCubeRoot (x : ℝ) : ℝ := if 0 ≤ x then x ^ (1 / 3 : ℝ) else -((-x) ^ (1 / 3 : ℝ))

theorem signedCubeRoot_cube (x : ℝ) : signedCubeRoot x ^ 3 = x := by
  unfold signedCubeRoot
  split_ifs with hx
  · simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hx (by decide : (3 : ℕ) ≠ 0)
  · have hp : 0 ≤ -x := by linarith
    have hh := Real.rpow_inv_natCast_pow hp (by decide : (3 : ℕ) ≠ 0)
    simp only [one_div, Nat.cast_ofNat] at hh ⊢
    rw [neg_pow, hh]
    norm_num

theorem signedCubeRoot_unique {x y : ℝ} (hy : y ^ 3 = x) : signedCubeRoot x = y :=
  (show Odd (3 : ℕ) from by decide).pow_injective ((signedCubeRoot_cube x).trans hy.symm)

theorem signedCubeRoot_at_eight : signedCubeRoot 8 = 2 := signedCubeRoot_unique (by norm_num)

theorem signedCubeRoot_continuousAt_eight : ContinuousAt signedCubeRoot 8 := by
  have h : ContinuousAt (fun x : ℝ ↦ x ^ (1 / 3 : ℝ)) 8 :=
    (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 3 : ℝ))).continuousAt
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 8)] with x hx
  exact if_pos hx.le

/-- Ví dụ 3.3.12: giới hạn căn bậc ba thực của 2x²−10 tại 3. -/
theorem cubic_root_quadratic_limit :
    DomainLimit univ (fun x ↦ signedCubeRoot (2 * x ^ 2 - 10)) 3 2 := by
  have hc : Continuous (fun x : ℝ ↦ 2 * x ^ 2 - 10) :=
    (continuous_const.mul (continuous_id.pow 2)).sub continuous_const
  have hg : DomainLimit univ (fun x ↦ 2 * x ^ 2 - 10) 3 8 := by
    convert domainLimit_of_continuousAt (univ_accumulation 3) hc.continuousAt using 1
    norm_num
  have hf : DomainLimit univ signedCubeRoot 8 (signedCubeRoot 8) :=
    domainLimit_of_continuousAt (univ_accumulation 8) signedCubeRoot_continuousAt_eight
  simpa only [signedCubeRoot_at_eight] using domainLimit_comp hg hf

/-- Định lí 3.3.13: điều kiện Cauchy trên miền bỏ điểm. -/
def PuncturedFunctionCauchyCondition (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ r ∈ D, ∀ s ∈ D,
    0 < |r - a| → |r - a| < δ → 0 < |s - a| → |s - a| < δ → |f r - f s| < ε

/-- Định lí 3.3.13: giới hạn hữu hạn tồn tại khi và chỉ khi điều kiện Cauchy đúng. -/
theorem hasDomainLimit_iff_cauchy {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) : HasDomainLimit D f a ↔ PuncturedFunctionCauchyCondition D f a := by
  constructor
  · rintro ⟨L, hL⟩ ε hε
    obtain ⟨δ, hδ, hh⟩ := hL.2 (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun r hr s hs hrn hrd hsn hsd ↦ ?_⟩
    have hfr := hh r hr hrn hrd
    have hfs := hh s hs hsn hsd
    have ht := abs_sub_le (f r) L (f s)
    rw [abs_sub_comm L (f s)] at ht
    linarith
  · intro hc
    obtain ⟨u, hu, hua⟩ := accumulationPointOf_iff_sequence.mp ha
    have hcu : CauchySeq (fun n ↦ f (u n)) := by
      apply Metric.cauchySeq_iff.mpr
      intro ε hε
      obtain ⟨δ, hδ, hh⟩ := hc ε hε
      obtain ⟨N, hN, hNu⟩ := hua δ hδ
      refine ⟨N, fun m hm n hn ↦ ?_⟩
      have hm1 := hN.trans hm
      have hn1 := hN.trans hn
      simpa only [Real.dist_eq] using hh (u m) (hu m hm1).1 (u n) (hu n hn1).1
        (abs_pos.mpr (sub_ne_zero.mpr (hu m hm1).2)) (hNu m hm)
        (abs_pos.mpr (sub_ne_zero.mpr (hu n hn1).2)) (hNu n hn)
    obtain ⟨L, hfu⟩ := cauchySeq_tendsto_of_complete hcu
    have hfus : ConvergesTo (fun n ↦ f (u n)) L := convergesTo_iff_tendsto.mpr hfu
    refine ⟨L, ha, fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hh⟩ := hc (ε / 2) (half_pos hε)
    obtain ⟨Nu, hNu, hnear⟩ := hua δ hδ
    obtain ⟨Nf, hNf, hval⟩ := hfus (ε / 2) (half_pos hε)
    let N := max Nu Nf
    have hnU : Nu ≤ N := le_max_left _ _
    have hnF : Nf ≤ N := le_max_right _ _
    have hn1 : 1 ≤ N := hNu.trans hnU
    refine ⟨δ, hδ, fun x hx hxn hxd ↦ ?_⟩
    have hfx := hh x hx (u N) (hu N hn1).1 hxn hxd
      (abs_pos.mpr (sub_ne_zero.mpr (hu N hn1).2)) (hnear N hnU)
    have hfN := hval N hnF
    have ht := abs_sub_le (f x) (f (u N)) L
    linarith

end calculus.Chapter03.Section03Supplement
