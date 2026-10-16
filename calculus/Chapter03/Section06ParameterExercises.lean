import calculus.Chapter03.Section03Exercises
import calculus.Chapter03.Section04
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Bài tập 3.6.2(b,c): ghép hàm. -/
namespace calculus.Chapter03.Section06ParameterExercises
open Set Filter Topology
open calculus.Chapter03.Section02 calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section03 calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section04 calculus.Chapter03.Section02Infinite

noncomputable def logarithmicPiece (a b x : ℝ) : ℝ :=
  if 2 < |x| then (x - 2) * Real.log (x ^ 2 - 4) else a * x + b


theorem logarithmic_piece_left_top (a b : ℝ) :
    DomainLeftTopLimit univ (logarithmicPiece a b) (-2) := by
  refine ⟨leftAccumulation_univ _, ?_⟩
  have harg : Tendsto (fun x : ℝ ↦ x ^ 2 - 4) (𝓝[<] (-2 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun x : ℝ ↦ x ^ 2 - 4) (-2) :=
        (continuousAt_id.pow 2).sub continuousAt_const
      convert hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (-2 : ℝ) ≤ 𝓝 (-2)) using 1; norm_num
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x ^ 2 - 4
      change x < -2 at hx
      nlinarith
  have hlog := Real.tendsto_log_nhdsGT_zero.comp harg
  have hlinear : Tendsto (fun x : ℝ ↦ x - 2) (𝓝[<] (-2 : ℝ)) (𝓝 (-4 : ℝ)) := by
    convert! (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun x : ℝ ↦ x - 2) (-2)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (-2 : ℝ) ≤ 𝓝 (-2)) using 1; norm_num
  have ht := hlinear.neg_mul_atBot (by norm_num : (-4 : ℝ) < 0) hlog
  simpa only [univ_inter] using ht.congr' (by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change x < -2 at hx
    have hp : 2 < |x| := by rw [abs_of_neg (by linarith : x < 0)]; linarith
    simp only [logarithmicPiece, if_pos hp, Function.comp_def])

/-- Bài tập 2(b): không có tham số cho hàm liên tục trên miền. -/
theorem exercise02_logarithmic_piece_no_parameters :
    ¬∃ a b : ℝ, DomainContinuousOn univ (logarithmicPiece a b) := by
  rintro ⟨a, b, hc⟩
  have ht := ((domainContinuousAt_univ _ (-2)).mp (hc (-2) (mem_univ _))).tendsto
  have hl := (logarithmic_piece_left_top a b).2
  have hfinite := ht.mono_left
    (nhdsWithin_le_nhds : 𝓝[univ ∩ Iio (-2 : ℝ)] (-2) ≤ 𝓝 (-2))
  have : NeBot (𝓝[univ ∩ Iio (-2 : ℝ)] (-2)) := by
    simpa only [univ_inter] using (inferInstance : NeBot (𝓝[<] (-2 : ℝ)))
  exact not_tendsto_nhds_of_tendsto_atTop hl _ hfinite

noncomputable def trigonometricRawQuotient (x : ℝ) : ℝ :=
  (Real.sin x ^ 2 - 1) / (4 * x ^ 2 - Real.pi ^ 2) ^ 2

noncomputable def trigonometricPiece (a b x : ℝ) : ℝ :=
  if x = Real.pi / 2 then a else
    if x = -Real.pi / 2 then b else trigonometricRawQuotient x

noncomputable def trigonometricPatchValue : ℝ := -1 / (16 * Real.pi ^ 2)

theorem trigonometric_raw_square (x : ℝ) :
    trigonometricRawQuotient x = -(Real.cos x / (4 * x ^ 2 - Real.pi ^ 2)) ^ 2 := by
  have hn : Real.sin x ^ 2 - 1 = -(Real.cos x ^ 2) := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  simp only [trigonometricRawQuotient, hn, neg_div, div_pow]


theorem trigonometric_raw_patch_limits (s : ℝ)
    (hs : s = Real.pi / 2 ∨ s = -Real.pi / 2) :
    Tendsto trigonometricRawQuotient (𝓝[≠] s) (𝓝 trigonometricPatchValue) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  rcases hs with rfl | rfl
  · have hf : HasDerivAt Real.cos (-1) (Real.pi / 2) := by
      simpa only [Real.sin_pi_div_two] using Real.hasDerivAt_cos (Real.pi / 2)
    have hg : HasDerivAt (fun x : ℝ ↦ 4*x^2-Real.pi^2) (4*Real.pi) (Real.pi / 2) := by
      convert! ((((hasDerivAt_id (Real.pi / 2)).pow 2).const_mul 4).sub_const (Real.pi ^ 2))
        using 1; norm_num; ring
    have hr := ratio_of_derivative_slopes (univ_accumulation (Real.pi / 2))
      hf hg Real.cos_pi_div_two (by ring)
      (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hp)
    have ht : Tendsto (fun x : ℝ ↦ Real.cos x/(4*x^2-Real.pi^2))
        (𝓝[≠] (Real.pi / 2)) (𝓝 (-1/(4*Real.pi))) := by
      simpa only [← compl_eq_univ_sdiff] using
        (domainLimit_iff_tendsto (univ_accumulation (Real.pi / 2))).mp hr
    have hq := (ht.pow 2).neg
    have hv : -(-1/(4*Real.pi))^2 = trigonometricPatchValue := by
      unfold trigonometricPatchValue
      field_simp [hp]; ring
    rw [hv] at hq
    exact hq.congr (fun x ↦ (trigonometric_raw_square x).symm)
  · have hf : HasDerivAt Real.cos 1 (-Real.pi / 2) := by
      simpa only [neg_div, Real.sin_neg, Real.sin_pi_div_two, neg_neg] using
        Real.hasDerivAt_cos (-Real.pi / 2)
    have hg : HasDerivAt (fun x : ℝ ↦ 4*x^2-Real.pi^2) (-4*Real.pi) (-Real.pi / 2) := by
      convert! ((((hasDerivAt_id (-Real.pi / 2)).pow 2).const_mul 4).sub_const (Real.pi ^ 2))
        using 1; norm_num; ring
    have hr := ratio_of_derivative_slopes (univ_accumulation (-Real.pi / 2)) hf hg
      (by simpa only [neg_div, Real.cos_neg] using Real.cos_pi_div_two)
      (by ring) (mul_ne_zero (by norm_num : (-4 : ℝ) ≠ 0) hp)
    have ht : Tendsto (fun x : ℝ ↦ Real.cos x/(4*x^2-Real.pi^2))
        (𝓝[≠] (-Real.pi / 2)) (𝓝 (1/(-4*Real.pi))) := by
      simpa only [← compl_eq_univ_sdiff] using
        (domainLimit_iff_tendsto (univ_accumulation (-Real.pi / 2))).mp hr
    have hq := (ht.pow 2).neg
    have hv : -(1/(-4*Real.pi))^2 = trigonometricPatchValue := by
      unfold trigonometricPatchValue
      field_simp [hp]; ring
    rw [hv] at hq
    exact hq.congr (fun x ↦ (trigonometric_raw_square x).symm)

/-- Bài tập 2(c): hàm liên tục trên ℝ khi và chỉ khi a=b=−1/(16π²). -/
theorem exercise02_trigonometric_piece_parameters (a b : ℝ) :
    DomainContinuousOn univ (trigonometricPiece a b) ↔
      a = trigonometricPatchValue ∧ b = trigonometricPatchValue := by
  classical
  have hp : Real.pi / 2 ≠ -Real.pi / 2 := by linarith [Real.pi_pos]
  have hlimits : ∀ s : ℝ, s = Real.pi / 2 ∨ s = -Real.pi / 2 →
      Tendsto (trigonometricPiece a b) (𝓝[≠] s) (𝓝 trigonometricPatchValue) := by
    intro s hs
    apply (trigonometric_raw_patch_limits s hs).congr'
    rcases hs with rfl | rfl
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_ne_nhds hp).filter_mono nhdsWithin_le_nhds] with x hx hother
      simp [trigonometricPiece, show x ≠ Real.pi / 2 from hx, hother]
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_ne_nhds hp.symm).filter_mono nhdsWithin_le_nhds] with x hx hother
      simp [trigonometricPiece, show x ≠ -Real.pi / 2 from hx, hother]
  constructor
  · intro hc
    have h1 := ((domainContinuousAt_univ _ _).mp (hc _ (mem_univ _))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
    have h2 := ((domainContinuousAt_univ _ _).mp (hc _ (mem_univ _))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (-Real.pi / 2) ≤ 𝓝 (-Real.pi / 2))
    exact ⟨by simpa [trigonometricPiece] using (tendsto_nhds_unique h1 (hlimits _ (Or.inl rfl))),
      by simpa [trigonometricPiece, hp.symm] using (tendsto_nhds_unique h2 (hlimits _ (Or.inr rfl)))⟩
  · rintro ⟨ha, hb⟩ x hx
    apply (domainContinuousAt_univ _ x).mpr
    by_cases hx1 : x = Real.pi / 2
    · apply continuousAt_iff_punctured_nhds.mpr
      have hv : trigonometricPiece a b x = trigonometricPatchValue := by
        rw [trigonometricPiece, if_pos hx1, ha]
      rw [hv]
      exact hlimits x (Or.inl hx1)
    by_cases hx2 : x = -Real.pi / 2
    · apply continuousAt_iff_punctured_nhds.mpr
      have hv : trigonometricPiece a b x = trigonometricPatchValue := by
        rw [trigonometricPiece, if_neg hx1, if_pos hx2, hb]
      rw [hv]
      exact hlimits x (Or.inr hx2)
    have hd : 4 * x ^ 2 - Real.pi ^ 2 ≠ 0 := by
      intro hz
      have hfactor : (2*x-Real.pi)*(2*x+Real.pi)=0 := by nlinarith [hz]
      rcases mul_eq_zero.mp hfactor with h | h
      · apply hx1; linarith
      · apply hx2; linarith
    have hc : ContinuousAt trigonometricRawQuotient x :=
      ((Real.continuous_sin.continuousAt.pow 2).sub continuousAt_const).div
        (((continuousAt_const.mul (continuousAt_id.pow 2)).sub continuousAt_const).pow 2)
        (pow_ne_zero 2 hd)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx1, eventually_ne_nhds hx2] with y hy1 hy2
    simp [trigonometricPiece, hy1, hy2]

/-- Với b=a−π/2, hai công thức sin(x+a) và cos(x+b) trùng nhau. -/
theorem repaired_phase_branches_coincide (a x : ℝ) :
    Real.sin (x + a) = Real.cos (x + (a - Real.pi / 2)) := by
  rw [show x + (a - Real.pi / 2) = x + a - Real.pi / 2 by ring,
    Real.cos_sub_pi_div_two]

end calculus.Chapter03.Section06ParameterExercises
