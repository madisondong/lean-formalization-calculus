import calculus.Chapter04.Section03MidpointExercises

/-!
# §4.3, Bài 38: giá trị trung bình của đạo hàm cấp ba

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1400–1402. Hàm chỉ cần khả vi ba lần, không cần C³.
-/
set_option autoImplicit false
open Set Filter Topology
open scoped BigOperators ContDiff
namespace calculus.Chapter04.Section03ThirdMeanExercise
open calculus.Chapter04.Section03MidpointExercises


theorem third_order_unit_taylor_with_derivative_family {f fp fpp fppp : ℝ → ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f (fp x) x)
    (hfp : ∀ x : ℝ, HasDerivAt fp (fpp x) x)
    (hfpp : ∀ x : ℝ, HasDerivAt fpp (fppp x) x) :
    ∃ c ∈ Ioo (0 : ℝ) 1,
      f 1 = f 0 + fp 0 + fpp 0 / 2 + fppp c / 6 := by
  have hdf : Differentiable ℝ f := fun x ↦ (hf x).differentiableAt
  have hdfp : Differentiable ℝ fp := fun x ↦ (hfp x).differentiableAt
  have hdfpp : Differentiable ℝ fpp := fun x ↦ (hfpp x).differentiableAt
  have hef : deriv f = fp := funext fun x ↦ (hf x).deriv
  have hefp : deriv fp = fpp := funext fun x ↦ (hfp x).deriv
  have hfpC : ContDiff ℝ 1 fp := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨hdfp, ?_⟩
    rw [hefp]
    exact hdfpp.continuous
  have hfC : ContDiff ℝ 2 f := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨hdf, by norm_num, ?_⟩
    rw [hef]
    exact hfpC
  have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hefirst : EqOn (derivWithin f (Icc 0 1)) fp (Icc 0 1) :=
    fun x hx ↦ (hf x).hasDerivWithinAt.derivWithin (hu x hx)
  have hesecond : EqOn (iteratedDerivWithin 2 f (Icc 0 1)) fpp (Icc 0 1) := by
    intro x hx
    rw [show 2 = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one,
      derivWithin_congr hefirst (hefirst hx),
      (hfp x).hasDerivWithinAt.derivWithin (hu x hx)]
  have hd2 : DifferentiableOn ℝ (iteratedDerivWithin 2 f (Icc 0 1)) (Ioo 0 1) :=
    (hdfpp.differentiableOn).congr (hesecond.mono Ioo_subset_Icc_self)
  have hdom : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hdomo : uIoo (0 : ℝ) 1 = Ioo 0 1 := uIoo_of_lt zero_lt_one
  obtain ⟨c, hc, ht⟩ := taylor_mean_remainder_lagrange
    (by norm_num : (0 : ℝ) ≠ 1) hfC.contDiffOn
    (by simpa only [hdom, hdomo] using hd2)
  have hc01 : c ∈ Ioo (0 : ℝ) 1 := by simpa only [hdomo] using hc
  rw [hdom] at ht
  have hz : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hP : taylorWithinEval f 2 (Icc 0 1) 0 1 = f 0 + fp 0 + fpp 0 / 2 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, iteratedDerivWithin_one, hefirst hz, hesecond hz]
    ring
  have h3 : iteratedDerivWithin 3 f (Icc 0 1) c = fppp c := by
    rw [show 3 = 2 + 1 from rfl, iteratedDerivWithin_succ,
      derivWithin_of_mem_nhds (Icc_mem_nhds hc01.1 hc01.2)]
    have hevent : iteratedDerivWithin 2 f (Icc 0 1) =ᶠ[𝓝 c] fpp := by
      filter_upwards [Icc_mem_nhds hc01.1 hc01.2] with x hx
      exact hesecond hx
    rw [hevent.deriv_eq, (hfpp c).deriv]
  refine ⟨c, hc01, ?_⟩
  rw [hP, h3] at ht
  norm_num at ht
  linarith

/-- Bài 38: hàm khả vi ba lần trên ℝ, không cần thuộc `C³`. -/
theorem third_derivative_mean_value {f : ℝ → ℝ}
    (hf : Differentiable ℝ f)
    (hfp : Differentiable ℝ (deriv f))
    (hfpp : Differentiable ℝ (deriv (deriv f))) :
    ∃ c ∈ Ioo (-1 : ℝ) 1,
      deriv (deriv (deriv f)) c / 6 = (f 1 - f (-1)) / 2 - deriv f 0 := by
  let fp : ℝ → ℝ := deriv f
  let fpp : ℝ → ℝ := deriv fp
  let fppp : ℝ → ℝ := deriv fpp
  let g : ℝ → ℝ := fun x ↦ f x - f (-x)
  let gp : ℝ → ℝ := fun x ↦ fp x + fp (-x)
  let gpp : ℝ → ℝ := fun x ↦ fpp x - fpp (-x)
  let gppp : ℝ → ℝ := fun x ↦ fppp x + fppp (-x)
  have hd (x : ℝ) : HasDerivAt f (fp x) x := (hf x).hasDerivAt
  have hdp (x : ℝ) : HasDerivAt fp (fpp x) x := (hfp x).hasDerivAt
  have hdpp (x : ℝ) : HasDerivAt fpp (fppp x) x := (hfpp x).hasDerivAt
  have hgd (x : ℝ) : HasDerivAt g (gp x) x := by
    have hr := (hd (-x)).comp x (hasDerivAt_neg x)
    simpa only [g, gp, Function.comp_def, mul_neg_one, sub_neg_eq_add] using (hd x).fun_sub hr
  have hgpd (x : ℝ) : HasDerivAt gp (gpp x) x := by
    have hr := (hdp (-x)).comp x (hasDerivAt_neg x)
    simpa only [gp, gpp, Function.comp_def, mul_neg_one, sub_eq_add_neg] using (hdp x).fun_add hr
  have hgppd (x : ℝ) : HasDerivAt gpp (gppp x) x := by
    have hr := (hdpp (-x)).comp x (hasDerivAt_neg x)
    simpa only [gpp, gppp, Function.comp_def, mul_neg_one, sub_neg_eq_add] using (hdpp x).fun_sub hr
  obtain ⟨u, hu, ht⟩ := third_order_unit_taylor_with_derivative_family hgd hgpd hgppd
  have hul : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2⟩
  have hnegul : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  obtain ⟨c, hc, hmean⟩ := derivative_mean_value_in_open_interval
    (fun x _ ↦ hdpp x) hul hnegul
  refine ⟨c, hc, ?_⟩
  change fppp c / 6 = (f 1 - f (-1)) / 2 - fp 0
  rw [hmean]
  simp only [g, gp, gpp, gppp, neg_zero, sub_self, zero_div, add_zero, zero_add] at ht
  linarith

end calculus.Chapter04.Section03ThirdMeanExercise
