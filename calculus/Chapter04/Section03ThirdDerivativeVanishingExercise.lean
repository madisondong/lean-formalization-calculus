import Mathlib.Analysis.Calculus.Deriv.Pow
import calculus.Chapter04.Section03BoundedSecondDerivativeVanishingExercise
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# §4.3, Bài 44: f→C và f‴→0 kéo theo f′,f″→0

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1422–1431. Các đạo hàm chỉ cần tồn tại trên một đuôi; không cần C³.
-/
set_option autoImplicit false
namespace calculus.Chapter04.Section03ThirdDerivativeVanishingExercise
open Set Filter
open scoped Topology
open calculus.Chapter04.Section03BoundedSecondDerivativeVanishingExercise


theorem tail_first_derivative_tendsto_zero {f d d₂ : ℝ → ℝ} {a L M : ℝ}
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (d x) x)
    (hd : ∀ x ∈ Ioi a, HasDerivAt d (d₂ x) x)
    (hbound : ∀ x ∈ Ioi a, |d₂ x| ≤ M)
    (hl : Tendsto f atTop (𝓝 L)) : Tendsto d atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ ↦ x + a) atTop atTop :=
    tendsto_atTop_add_const_right atTop a tendsto_id
  have hF (x : ℝ) (hx : x ∈ Ioi 0) :
      HasDerivAt (fun y : ℝ ↦ f (y + a)) (d (x + a)) x := by
    have ht := (hf (x + a) (by change a < x + a; have hh : (0 : ℝ) < x := hx; linarith)).comp x
      ((hasDerivAt_id x).add_const a)
    simpa only [Function.comp_def, id_eq, mul_one] using! ht
  have hD (x : ℝ) (hx : x ∈ Ioi 0) :
      HasDerivAt (fun y : ℝ ↦ d (y + a)) (d₂ (x + a)) x := by
    have ht := (hd (x + a) (by change a < x + a; have hh : (0 : ℝ) < x := hx; linarith)).comp x
      ((hasDerivAt_id x).add_const a)
    simpa only [Function.comp_def, id_eq, mul_one] using! ht
  have ht := first_derivative_tendsto_zero_of_bounded_second_derivative hF hD
    (fun x hx ↦ hbound (x + a) (by change a < x + a; have hh : (0 : ℝ) < x := hx; linarith)) (hl.comp hshift)
  have hback : Tendsto (fun x : ℝ ↦ x + -a) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-a) tendsto_id
  simpa only [Function.comp_def, add_assoc, neg_add_cancel, add_zero] using ht.comp hback


theorem second_finite_difference_witness {f d d₂ : ℝ → ℝ} {a x h : ℝ}
    (hf : ∀ y ∈ Ioi a, HasDerivAt f (d y) y)
    (hd : ∀ y ∈ Ioi a, HasDerivAt d (d₂ y) y)
    (hx : a < x) (hh : 0 < h) :
    ∃ z ∈ Ioo x (x + 2 * h),
      d₂ z = (f (x + 2 * h) - 2 * f (x + h) + f x) / h ^ 2 := by
  let A : ℝ := (f (x + 2 * h) - 2 * f (x + h) + f x) / (2 * h ^ 2)
  let B : ℝ := (f (x + h) - f x) / h - A * h
  let G : ℝ → ℝ := fun y ↦ f y - A * (y - x) ^ 2 - B * (y - x) - f x
  let D : ℝ → ℝ := fun y ↦ d y - 2 * A * (y - x) - B
  have hG (y : ℝ) (hy : y ∈ Ioi a) : HasDerivAt G (D y) y := by
    have hp := (((hasDerivAt_id y).sub_const x).fun_pow 2).const_mul A
    have hq := ((hasDerivAt_id y).sub_const x).const_mul B
    simp only [id_eq] at hp hq
    have ht := (((hf y hy).fun_sub hp).fun_sub hq).sub_const (f x)
    apply ht.congr_deriv
    dsimp only [D]
    ring
  have hD (y : ℝ) (hy : y ∈ Ioi a) : HasDerivAt D (d₂ y - 2 * A) y := by
    have hp := ((hasDerivAt_id y).sub_const x).const_mul (2 * A)
    have ht := ((hd y hy).fun_sub hp).sub_const B
    simpa only [D, id_eq, mul_one] using! ht
  have hGa : G x = 0 := by simp only [G, sub_self, pow_two, mul_zero, sub_zero]
  have hGb : G (x + h) = 0 := by
    dsimp only [G, A, B]
    field_simp [hh.ne']
    ring
  have hGc : G (x + 2 * h) = 0 := by
    dsimp only [G, A, B]
    field_simp [hh.ne']
    ring
  have hGcont {u v : ℝ} (hu : a < u) : ContinuousOn G (Icc u v) := by
    intro y hy
    exact (hG y (by change a < y; linarith [hy.1])).continuousAt.continuousWithinAt
  obtain ⟨u, hu, huD⟩ := exists_hasDerivAt_eq_zero (by linarith : x < x + h)
    (hGcont hx) (hGa.trans hGb.symm)
    (fun y hy ↦ hG y (by change a < y; linarith [hy.1]))
  obtain ⟨v, hv, hvD⟩ := exists_hasDerivAt_eq_zero (by linarith : x + h < x + 2 * h)
    (hGcont (by linarith : a < x + h)) (hGb.trans hGc.symm)
    (fun y hy ↦ hG y (by change a < y; linarith [hy.1]))
  have huv : u < v := by linarith [hu.2, hv.1]
  have hDcont : ContinuousOn D (Icc u v) := by
    intro y hy
    exact (hD y (by change a < y; linarith [hy.1, hu.1])).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hzD⟩ := exists_hasDerivAt_eq_zero huv hDcont (huD.trans hvD.symm)
    (fun y hy ↦ hD y (by change a < y; linarith [hy.1, hu.1]))
  refine ⟨z, ⟨by linarith [hz.1, hu.1], by linarith [hz.2, hv.2]⟩, ?_⟩
  have hza : d₂ z = 2 * A := by linarith
  rw [hza]
  dsimp only [A]
  field_simp [hh.ne']


theorem second_derivative_forward_estimate {f d d₂ d₃ : ℝ → ℝ} {a M x h : ℝ}
    (hf : ∀ y ∈ Ioi a, HasDerivAt f (d y) y)
    (hd : ∀ y ∈ Ioi a, HasDerivAt d (d₂ y) y)
    (hdd : ∀ y ∈ Ioi a, HasDerivAt d₂ (d₃ y) y)
    (hM : 0 ≤ M) (hbound : ∀ y ∈ Ioi a, |d₃ y| ≤ M)
    (hx : a < x) (hh : 0 < h) :
    |d₂ x| ≤ 2 * M * h + |f (x + 2 * h) - 2 * f (x + h) + f x| / h ^ 2 := by
  obtain ⟨z, hz, hzs⟩ := second_finite_difference_witness hf hd hx hh
  have hzpos : z ∈ Ioi a := by change a < z; linarith [hz.1]
  have hvar : |d₂ z - d₂ x| ≤ M * |z - x| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y hy ↦ (hdd y hy).hasDerivWithinAt)
        (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hbound y hy)
        (convex_Ioi a) hx hzpos
  have hstep : |z - x| ≤ 2 * h := by
    rw [abs_of_pos (sub_pos.mpr hz.1)]
    linarith [hz.2]
  have hdz : |d₂ z| = |f (x + 2 * h) - 2 * f (x + h) + f x| / h ^ 2 := by
    rw [hzs, abs_div, abs_of_pos (sq_pos_of_pos hh)]
  calc
    |d₂ x| = |(d₂ x - d₂ z) + d₂ z| := by congr 1; ring
    _ ≤ |d₂ x - d₂ z| + |d₂ z| := abs_add_le _ _
    _ ≤ M * (2 * h) + |f (x + 2 * h) - 2 * f (x + h) + f x| / h ^ 2 := by
      rw [abs_sub_comm, hdz]
      exact add_le_add (hvar.trans (mul_le_mul_of_nonneg_left hstep hM)) le_rfl
    _ = 2 * M * h + |f (x + 2 * h) - 2 * f (x + h) + f x| / h ^ 2 := by ring


theorem tail_second_derivative_tendsto_zero {f d d₂ d₃ : ℝ → ℝ} {a L M : ℝ}
    (hf : ∀ y ∈ Ioi a, HasDerivAt f (d y) y)
    (hd : ∀ y ∈ Ioi a, HasDerivAt d (d₂ y) y)
    (hdd : ∀ y ∈ Ioi a, HasDerivAt d₂ (d₃ y) y)
    (hbound : ∀ y ∈ Ioi a, |d₃ y| ≤ M)
    (hl : Tendsto f atTop (𝓝 L)) : Tendsto d₂ atTop (𝓝 0) := by
  have hM : 0 ≤ M := (abs_nonneg (d₃ (a + 1))).trans
    (hbound (a + 1) (by change a < a + 1; linarith))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let h : ℝ := ε / (8 * (M + 1))
  have hden : 0 < 8 * (M + 1) := by linarith
  have hh : 0 < h := div_pos hε hden
  have hprod : h * (8 * (M + 1)) = ε := div_mul_cancel₀ ε hden.ne'
  have hMh : 2 * M * h < ε / 2 := by nlinarith
  have hshift₁ : Tendsto (fun x : ℝ ↦ x + h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  have hshift₂ : Tendsto (fun x : ℝ ↦ x + 2 * h) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 * h) tendsto_id
  have hdiff : Tendsto (fun x : ℝ ↦ f (x + 2 * h) - 2 * f (x + h) + f x)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, show L - 2 * L + L = 0 by ring] using
      ((hl.comp hshift₂).sub ((hl.comp hshift₁).const_mul 2)).add hl
  have hsmall := (Metric.tendsto_nhds.mp hdiff) (ε * h ^ 2 / 2) (by positivity)
  filter_upwards [hsmall, eventually_gt_atTop a] with x hfx hx
  have hfx' : |f (x + 2 * h) - 2 * f (x + h) + f x| < ε * h ^ 2 / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hfx
  have hquot : |f (x + 2 * h) - 2 * f (x + h) + f x| / h ^ 2 < ε / 2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hh)).mpr
    nlinarith
  have hest := second_derivative_forward_estimate hf hd hdd hM hbound hx hh
  rw [Real.dist_eq, sub_zero]
  linarith

/-- Bài 44: `f → C` và `f‴ → 0` kéo theo `f′, f″ → 0`; các đạo hàm chỉ cần tồn tại trên một đuôi. -/
theorem source_third_derivative_vanishing {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ᶠ x : ℝ in atTop, DifferentiableAt ℝ f x)
    (hd : ∀ᶠ x : ℝ in atTop, DifferentiableAt ℝ (deriv f) x)
    (hdd : ∀ᶠ x : ℝ in atTop, DifferentiableAt ℝ (deriv (deriv f)) x)
    (hl : Tendsto f atTop (𝓝 C))
    (hthird : Tendsto (deriv (deriv (deriv f))) atTop (𝓝 0)) :
    Tendsto (deriv f) atTop (𝓝 0) ∧ Tendsto (deriv (deriv f)) atTop (𝓝 0) := by
  have hb := (Metric.tendsto_nhds.mp hthird) 1 (by norm_num)
  have he : ∀ᶠ x : ℝ in atTop,
      HasDerivAt f (deriv f x) x ∧
      HasDerivAt (deriv f) (deriv (deriv f) x) x ∧
      HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x ∧
      |deriv (deriv (deriv f)) x| ≤ 1 := by
    filter_upwards [hf, hd, hdd, hb] with x hfx hdx hddx hbx
    refine ⟨hfx.hasDerivAt, hdx.hasDerivAt, hddx.hasDerivAt, ?_⟩
    exact (by simpa only [Real.dist_eq, sub_zero] using hbx :
      |deriv (deriv (deriv f)) x| < 1).le
  obtain ⟨a, ha⟩ := eventually_atTop.mp he
  have hsecond : Tendsto (deriv (deriv f)) atTop (𝓝 0) :=
    tail_second_derivative_tendsto_zero
      (fun x hx ↦ (ha x hx.le).1)
      (fun x hx ↦ (ha x hx.le).2.1)
      (fun x hx ↦ (ha x hx.le).2.2.1)
      (fun x hx ↦ (ha x hx.le).2.2.2) hl
  have hb₂ := (Metric.tendsto_nhds.mp hsecond) 1 (by norm_num)
  have he₂ : ∀ᶠ x : ℝ in atTop,
      HasDerivAt f (deriv f x) x ∧
      HasDerivAt (deriv f) (deriv (deriv f) x) x ∧
      |deriv (deriv f) x| ≤ 1 := by
    filter_upwards [hf, hd, hb₂] with x hfx hdx hbx
    refine ⟨hfx.hasDerivAt, hdx.hasDerivAt, ?_⟩
    exact (by simpa only [Real.dist_eq, sub_zero] using hbx : |deriv (deriv f) x| < 1).le
  obtain ⟨b, hb'⟩ := eventually_atTop.mp he₂
  refine ⟨tail_first_derivative_tendsto_zero
    (fun x hx ↦ (hb' x hx.le).1)
    (fun x hx ↦ (hb' x hx.le).2.1)
    (fun x hx ↦ (hb' x hx.le).2.2) hl, hsecond⟩

end calculus.Chapter04.Section03ThirdDerivativeVanishingExercise
