import calculus.Chapter04.Section03Taylor
import Mathlib.Analysis.Calculus.Darboux

/-!
# §4.3, Bài 35–37: trung điểm và đạo hàm ở đầu mút

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1391–1399. Đạo hàm tại đầu mút là đạo hàm một bên; Bài 35 không cần C², Bài 36 giữ giả thiết C².
-/
set_option autoImplicit false
open Set Filter Topology
open scoped BigOperators
namespace calculus.Chapter04.Section03MidpointExercises
open calculus.Chapter04.Section01Higher calculus.Chapter04.Section01HigherClosed
open calculus.Chapter04.Section03Taylor


theorem source_closed_order_mono {k n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (hkn : k ≤ n) (hf : DifferentiableToOrderOnClosedInterval n f a b) :
    DifferentiableToOrderOnClosedInterval k f a b := by
  refine ⟨hf.1, ?_, right_order_mono hkn hf.2.2.1, left_order_mono hkn hf.2.2.2⟩
  intro j hj
  exact hf.2.1 j (lt_of_lt_of_le hj hkn)


theorem source_closed_second_derivative_family {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval 2 f a b) :
    (∀ x ∈ Icc a b, HasDerivWithinAt f (derivWithin f (Icc a b) x) (Icc a b) x) ∧
    ContinuousOn (derivWithin f (Icc a b)) (Icc a b) ∧
    ∀ x ∈ Ioo a b, HasDerivAt (derivWithin f (Icc a b))
      (iteratedDerivWithin 2 f (Icc a b) x) x := by
  have hd := source_closed_to_within hf
  have hd0 : DifferentiableOn ℝ f (Icc a b) := by
    simpa only [iteratedDerivWithin_zero] using hd 0 (by decide)
  have hd1 : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b) := by
    simpa only [iteratedDerivWithin_one] using hd 1 (by decide)
  refine ⟨fun x hx ↦ (hd0 x hx).hasDerivWithinAt, hd1.continuousOn, ?_⟩
  intro x hx
  have hmem : Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  have he : deriv (derivWithin f (Icc a b)) x = iteratedDerivWithin 2 f (Icc a b) x := by
    rw [show 2 = 1 + 1 from rfl, iteratedDerivWithin_succ,
      iteratedDerivWithin_one, derivWithin_of_mem_nhds hmem]
  exact (hd1.differentiableAt hmem).hasDerivAt.congr_deriv he


theorem second_order_taylor_with_derivative_family {f fp fpp : ℝ → ℝ} {x₀ x : ℝ}
    (hne : x₀ ≠ x)
    (hf : ∀ y ∈ uIcc x₀ x, HasDerivWithinAt f (fp y) (uIcc x₀ x) y)
    (hpc : ContinuousOn fp (uIcc x₀ x))
    (hpd : ∀ y ∈ uIoo x₀ x, HasDerivAt fp (fpp y) y) :
    ∃ c ∈ uIoo x₀ x,
      f x = f x₀ + fp x₀ * (x - x₀) + fpp c * (x - x₀) ^ 2 / 2 := by
  have hu := uniqueDiffOn_uIcc hne
  have he : EqOn (derivWithin f (uIcc x₀ x)) fp (uIcc x₀ x) :=
    fun y hy ↦ (hf y hy).derivWithin (hu y hy)
  have hC : ContDiffOn ℝ 1 f (uIcc x₀ x) :=
    (contDiffOn_one_iff_derivWithin hu).mpr
      ⟨fun y hy ↦ (hf y hy).differentiableWithinAt, hpc.congr he⟩
  have hd : DifferentiableOn ℝ (iteratedDerivWithin 1 f (uIcc x₀ x)) (uIoo x₀ x) := by
    have hp : DifferentiableOn ℝ fp (uIoo x₀ x) :=
      fun y hy ↦ (hpd y hy).differentiableAt.differentiableWithinAt
    simpa only [iteratedDerivWithin_one] using hp.congr
      (he.mono uIoo_subset_uIcc_self)
  obtain ⟨c, hc, ht⟩ := taylor_mean_remainder_lagrange hne hC hd
  have hP : taylorWithinEval f 1 (uIcc x₀ x) x₀ x = f x₀ + fp x₀ * (x - x₀) := by
    rw [taylor_within_apply]
    have h0 := he left_mem_uIcc
    norm_num [Finset.sum_range_succ, iteratedDerivWithin_one, h0]
    ring
  have h2 : iteratedDerivWithin 2 f (uIcc x₀ x) c = fpp c := by
    have hcnhds : uIcc x₀ x ∈ 𝓝 c := Icc_mem_nhds hc.1 hc.2
    rw [show 2 = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one,
      derivWithin_of_mem_nhds hcnhds]
    have hevent : derivWithin f (uIcc x₀ x) =ᶠ[𝓝 c] fp := by
      filter_upwards [Icc_mem_nhds hc.1 hc.2] with y hy
      exact he hy
    rw [hevent.deriv_eq, (hpd c hc).deriv]
  refine ⟨c, hc, ?_⟩
  rw [hP] at ht
  norm_num [h2] at ht
  linarith


theorem derivative_mean_value_in_open_interval {fp fpp : ℝ → ℝ} {a b u v : ℝ}
    (hd : ∀ x ∈ Ioo a b, HasDerivAt fp (fpp x) x)
    (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    ∃ c ∈ Ioo a b, fpp c = (fpp u + fpp v) / 2 := by
  have himage : Convex ℝ (fpp '' Ioo a b) :=
    (convex_Ioo a b).image_hasDerivWithinAt
      (fun x hx ↦ (hd x hx).hasDerivWithinAt)
  have hm := (convex_iff_add_mem.mp himage)
    (mem_image_of_mem fpp hu) (mem_image_of_mem fpp hv)
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he : (1 / 2 : ℝ) • fpp u + (1 / 2 : ℝ) • fpp v = (fpp u + fpp v) / 2 := by
    simp only [smul_eq_mul]
    ring
  rw [he] at hm
  exact hm


theorem midpoint_plus_second_derivative_of_equal_endpoint_derivatives
    {f fp fpp : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (fp x) (Icc a b) x)
    (hpc : ContinuousOn fp (Icc a b))
    (hpd : ∀ x ∈ Ioo a b, HasDerivAt fp (fpp x) x) (he : fp a = fp b) :
    ∃ c ∈ Ioo a b,
      f ((a + b) / 2) = (f a + f b) / 2 + (b - a) ^ 2 / 8 * fpp c := by
  let m : ℝ := (a + b) / 2
  let r : ℝ → ℝ := fun x ↦ a + b - x
  let g : ℝ → ℝ := fun x ↦ f x + f (r x)
  let gp : ℝ → ℝ := fun x ↦ fp x - fp (r x)
  let gpp : ℝ → ℝ := fun x ↦ fpp x + fpp (r x)
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hs : Icc a m ⊆ Icc a b := fun x hx ↦ ⟨hx.1, hx.2.trans hmb.le⟩
  have hrmap : MapsTo r (Icc a m) (Icc a b) := by
    intro x hx
    dsimp [r]
    constructor <;> linarith [hx.1, hx.2]
  have hri : ∀ x ∈ Ioo a m, r x ∈ Ioo a b := by
    intro x hx
    dsimp [r]
    constructor <;> linarith [hx.1, hx.2]
  have hr (x : ℝ) : HasDerivAt r (-1) x :=
    (hasDerivAt_id x).const_sub (a + b)
  have hgf : ∀ x ∈ Icc a m, HasDerivWithinAt g (gp x) (Icc a m) x := by
    intro x hx
    have hreflect := (hf (r x) (hrmap hx)).comp x (hr x).hasDerivWithinAt hrmap
    have h := ((hf x (hs hx)).mono hs).fun_add hreflect
    simpa only [g, gp, Function.comp_def, mul_neg_one, sub_eq_add_neg] using h
  have hgpc : ContinuousOn gp (Icc a m) := by
    exact (hpc.mono hs).sub (hpc.comp (continuous_const.sub continuous_id).continuousOn hrmap)
  have hgpd : ∀ x ∈ Ioo a m, HasDerivAt gp (gpp x) x := by
    intro x hx
    have hxi : x ∈ Ioo a b := ⟨hx.1, hx.2.trans hmb⟩
    have hreflect := (hpd (r x) (hri x hx)).comp x (hr x)
    simpa only [gp, gpp, Function.comp_def, mul_neg_one, sub_neg_eq_add] using
      (hpd x hxi).fun_sub hreflect
  have hga : gp a = 0 := by simp [gp, r, he]
  have hdom : uIcc a m = Icc a m := uIcc_of_le ham.le
  have hdomo : uIoo a m = Ioo a m := uIoo_of_lt ham
  obtain ⟨u, hu, ht⟩ := second_order_taylor_with_derivative_family ham.ne
    (by simpa only [hdom] using hgf) (by simpa only [hdom] using hgpc)
    (by simpa only [hdomo] using hgpd)
  have huam : u ∈ Ioo a m := by simpa only [hdomo] using hu
  have huab : u ∈ Ioo a b := ⟨huam.1, huam.2.trans hmb⟩
  obtain ⟨c, hc, hmean⟩ := derivative_mean_value_in_open_interval hpd huab (hri u huam)
  have hrm : r m = m := by dsimp [r, m]; ring
  have hra : r a = b := by dsimp [r]; ring
  rw [hga, zero_mul, add_zero] at ht
  have ht' : 2 * f m = f a + f b +
      (fpp u + fpp (r u)) * (m - a) ^ 2 / 2 := by
    simpa only [g, gpp, hrm, hra, two_mul] using ht
  refine ⟨c, hc, ?_⟩
  rw [hmean]
  dsimp [m] at ht' ⊢
  nlinarith [ht']

/-- Bài 35: công thức tại trung điểm, với đạo hàm một bên ở hai đầu mút. -/
theorem source_midpoint_plus_second_derivative {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval 2 f a b)
    (he : iteratedDerivWithin 1 f (Icc a b) a = iteratedDerivWithin 1 f (Icc a b) b) :
    ∃ c ∈ Ioo a b,
      f ((a + b) / 2) = (f a + f b) / 2 +
        (b - a) ^ 2 / 8 * iteratedDerivWithin 2 f (Icc a b) c := by
  obtain ⟨hd, hc, hdd⟩ := source_closed_second_derivative_family hf
  exact midpoint_plus_second_derivative_of_equal_endpoint_derivatives hf.1 hd hc hdd
    (by simpa only [iteratedDerivWithin_one] using he)


theorem endpoint_average_second_derivative {f fp fpp : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (fp x) (Icc a b) x)
    (hpc : ContinuousOn fp (Icc a b))
    (hpd : ∀ x ∈ Ioo a b, HasDerivAt fp (fpp x) x) :
    ∃ c ∈ Ioo a b,
      (f a + f b) / 2 = f ((a + b) / 2) + (b - a) ^ 2 / 8 * fpp c := by
  let m : ℝ := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hma : m ∈ Icc a b := ⟨ham.le, hmb.le⟩
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hsa : uIcc m a ⊆ Icc a b := uIcc_subset_Icc hma ha
  have hsb : uIcc m b ⊆ Icc a b := uIcc_subset_Icc hma hb
  have hfsub {x : ℝ} (hs : uIcc m x ⊆ Icc a b) :
      ∀ y ∈ uIcc m x, HasDerivWithinAt f (fp y) (uIcc m x) y :=
    fun y hy ↦ (hf y (hs hy)).mono hs
  obtain ⟨u, hu, htu⟩ := second_order_taylor_with_derivative_family ham.ne'
    (hfsub hsa) (hpc.mono hsa)
    (fun y hy ↦ hpd y (uIoo_subset_Ioo hma ha hy))
  obtain ⟨v, hv, htv⟩ := second_order_taylor_with_derivative_family hmb.ne
    (hfsub hsb) (hpc.mono hsb)
    (fun y hy ↦ hpd y (uIoo_subset_Ioo hma hb hy))
  obtain ⟨c, hc, hmean⟩ := derivative_mean_value_in_open_interval hpd
    (uIoo_subset_Ioo hma ha hu) (uIoo_subset_Ioo hma hb hv)
  refine ⟨c, hc, ?_⟩
  rw [hmean]
  dsimp [m] at htu htv ⊢
  nlinarith [htu, htv]

/-- Bài 36: giá trị trung bình của đạo hàm cấp hai, với giả thiết C². -/
theorem source_endpoint_average_second_derivative {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval 2 f a b)
    (_hc : ContinuousOn (iteratedDerivWithin 2 f (Icc a b)) (Icc a b)) :
    ∃ c ∈ Ioo a b,
      (f a + f b) / 2 = f ((a + b) / 2) +
        (b - a) ^ 2 / 8 * iteratedDerivWithin 2 f (Icc a b) c := by
  obtain ⟨hd, hc, hdd⟩ := source_closed_second_derivative_family hf
  exact endpoint_average_second_derivative hf.1 hd hc hdd

/-- Bài 37: tồn tại điểm có `f‴ ≥ 24`, với giả thiết C³. -/
theorem source_third_derivative_ge_twenty_four {f : ℝ → ℝ}
    (hf : DifferentiableToOrderOnClosedInterval 3 f 0 1)
    (_hc : ContinuousOn (iteratedDerivWithin 3 f (Icc 0 1)) (Icc 0 1))
    (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hp0 : iteratedDerivWithin 1 f (Icc 0 1) 0 = 0)
    (hp1 : iteratedDerivWithin 1 f (Icc 0 1) 1 = 0)
    (hpp0 : iteratedDerivWithin 2 f (Icc 0 1) 0 = 0)
    (hpp1 : iteratedDerivWithin 2 f (Icc 0 1) 1 = 0) :
    ∃ c ∈ Ioo (0 : ℝ) 1, 24 ≤ iteratedDerivWithin 3 f (Icc 0 1) c := by
  have hf2 := source_closed_order_mono (by decide : 2 ≤ 3) hf
  have hc2 : ContinuousOn (iteratedDerivWithin 2 f (Icc 0 1)) (Icc 0 1) :=
    ((source_closed_to_within hf) 2 (by decide)).continuousOn
  have hhalf : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  have hz : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have ho : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  obtain ⟨u, hu, htu⟩ := source_taylor_lagrange 2 (by decide) hf2 hc2 hf.2.1 hz hhalf
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  obtain ⟨v, hv, htv⟩ := source_taylor_lagrange 2 (by decide) hf2 hc2 hf.2.1 ho hhalf
    (by norm_num : (1 / 2 : ℝ) ≠ 1)
  norm_num [taylorPolynomialWithin, Finset.sum_range_succ, h0, h1, hp0, hp1, hpp0, hpp1]
    at htu htv
  have hsum : iteratedDerivWithin 3 f (Icc 0 1) u +
      iteratedDerivWithin 3 f (Icc 0 1) v = 48 := by linarith
  by_cases hu24 : 24 ≤ iteratedDerivWithin 3 f (Icc 0 1) u
  · exact ⟨u, uIoo_subset_Ioo hz hhalf hu, hu24⟩
  · exact ⟨v, uIoo_subset_Ioo ho hhalf hv, by linarith⟩

end calculus.Chapter04.Section03MidpointExercises
