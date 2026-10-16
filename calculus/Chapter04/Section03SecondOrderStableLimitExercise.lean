import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# §4.3 Bài 12(b): giới hạn khi f+f′+f″→C

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1146–1150. Đạo hàm cấp hai chỉ cần tồn tại trên một đuôi; không cần C² hay hội tụ riêng của `f′`.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace calculus.Chapter04.Section03SecondOrderStableLimitExercise


def secondOrderStableEnergy (u v : ℝ) : ℝ :=
  3 / 4 * u ^ 2 + (v + u / 2) ^ 2


theorem second_order_energy_hasDerivAt {f d e : ℝ → ℝ} {C x : ℝ}
    (hf : HasDerivAt f (d x) x) (hd : HasDerivAt d (e x) x) :
    HasDerivAt (fun y ↦ secondOrderStableEnergy (f y - C) (d y))
      (3 / 2 * (f x - C) * d x +
        2 * (d x + (f x - C) / 2) * (e x + d x / 2)) x := by
  have hu := hf.sub_const C
  have hz := hd.fun_add (hu.div_const 2)
  have h₁ := (hu.fun_pow 2).const_mul (3 / 4 : ℝ)
  have h₂ := hz.fun_pow 2
  dsimp only [secondOrderStableEnergy]
  apply (h₁.fun_add h₂).congr_deriv
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring


theorem second_order_energy_differential_inequality (u v w : ℝ) :
    3 / 2 * u * v + 2 * (v + u / 2) * (w + v / 2) ≤
      -secondOrderStableEnergy u v / 2 + 2 * (u + v + w) ^ 2 := by
  dsimp only [secondOrderStableEnergy]
  nlinarith [sq_nonneg (v + u / 2 - 2 * (u + v + w)), sq_nonneg u]


theorem nonnegative_energy_tendsto_zero {E dE R : ℝ → ℝ} (a : ℝ)
    (hd : ∀ x ∈ Ici a, HasDerivAt E (dE x) x)
    (hE : ∀ x ∈ Ici a, 0 ≤ E x)
    (hbound : ∀ x ∈ Ici a, dE x ≤ -E x / 2 + 2 * (R x) ^ 2)
    (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto E atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hR₂ : Tendsto (fun x ↦ 2 * (R x) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using (hR.pow 2).const_mul 2
  obtain ⟨b, hb⟩ := eventually_atTop.mp
    (hR₂.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 4)))
  let B : ℝ := max a b
  let G : ℝ → ℝ := fun x ↦ Real.exp (x / 2) * (E x - ε / 2)
  have hBa : a ≤ B := le_max_left _ _
  have hBb : b ≤ B := le_max_right _ _
  have hg (x : ℝ) (hx : x ∈ Ici B) :
      HasDerivAt G (Real.exp (x / 2) * (dE x + (E x - ε / 2) / 2)) x := by
    have hx' : x ∈ Ici a := hBa.trans hx
    have hex := ((hasDerivAt_id x).div_const (2 : ℝ)).exp
    simp only [id_eq] at hex
    apply (hex.fun_mul ((hd x hx').sub_const (ε / 2))).congr_deriv
    ring
  have hm : AntitoneOn G (Ici B) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici B)
      (fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt)
    · intro x hx
      have hx' : x ∈ Ici B := by
        have hh : x ∈ Ioi B := by simpa only [interior_Ici] using hx
        exact mem_Ici.mpr (mem_Ioi.mp hh).le
      exact (hg x hx').differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ici B := by
        have hh : x ∈ Ioi B := by simpa only [interior_Ici] using hx
        exact mem_Ici.mpr (mem_Ioi.mp hh).le
      rw [(hg x hx').deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      have hsmall := hb x (hBb.trans hx')
      have hh := hbound x (hBa.trans hx')
      linarith
  have hexlim : Tendsto (fun x : ℝ ↦ Real.exp (-(x / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hdecay : Tendsto (fun x : ℝ ↦ G B * Real.exp (-(x / 2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hexlim.const_mul (G B)
  obtain ⟨c, hc⟩ := eventually_atTop.mp
    (hdecay.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2)))
  refine ⟨max B c, ?_⟩
  intro x hx
  have hxB : x ∈ Ici B := (le_max_left _ _).trans hx
  have hxc : c ≤ x := (le_max_right _ _).trans hx
  have hmono : G x ≤ G B := hm (by simp : B ∈ Ici B) hxB hxB
  have hprod := mul_le_mul_of_nonneg_right hmono (Real.exp_nonneg (-(x / 2)))
  have heq : G x * Real.exp (-(x / 2)) = E x - ε / 2 := by
    calc
      G x * Real.exp (-(x / 2)) =
          (Real.exp (x / 2) * Real.exp (-(x / 2))) * (E x - ε / 2) := by
        dsimp only [G]
        ring
      _ = E x - ε / 2 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [heq] at hprod
  have he_nonneg := hE x (hBa.trans hxB)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg he_nonneg]
  linarith [hc x hxc]


theorem second_order_stable_limit {f d e : ℝ → ℝ} (a C : ℝ)
    (hf : ∀ x ∈ Ici a, HasDerivAt f (d x) x)
    (hd : ∀ x ∈ Ici a, HasDerivAt d (e x) x)
    (hl : Tendsto (fun x ↦ f x + d x + e x) atTop (𝓝 C)) :
    Tendsto f atTop (𝓝 C) := by
  let E : ℝ → ℝ := fun x ↦ secondOrderStableEnergy (f x - C) (d x)
  let dE : ℝ → ℝ := fun x ↦ 3 / 2 * (f x - C) * d x +
    2 * (d x + (f x - C) / 2) * (e x + d x / 2)
  let R : ℝ → ℝ := fun x ↦ f x - C + d x + e x
  have hR : Tendsto R atTop (𝓝 0) := by
    have ht := hl.sub_const C
    simp only [sub_self] at ht
    apply ht.congr
    intro x
    dsimp only [R]
    ring
  have hlimE : Tendsto E atTop (𝓝 0) := by
    apply nonnegative_energy_tendsto_zero a
      (fun x hx ↦ second_order_energy_hasDerivAt (hf x hx) (hd x hx))
    · intro x _
      dsimp only [E, secondOrderStableEnergy]
      positivity
    · intro x _
      exact second_order_energy_differential_inequality (f x - C) (d x) (e x)
    · exact hR
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨b, hb⟩ := eventually_atTop.mp
    (hlimE.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 3 / 4 * ε ^ 2)))
  refine ⟨b, ?_⟩
  intro x hx
  have hh := hb x hx
  dsimp only [E, secondOrderStableEnergy] at hh
  rw [Real.dist_eq]
  nlinarith [sq_nonneg (d x + (f x - C) / 2), sq_abs (f x - C), abs_nonneg (f x - C)]

/-- Bài 12(b): `f + f′ + f″ → C` kéo theo `f → C`; đạo hàm cấp hai chỉ cần tồn tại trên một đuôi. -/
theorem source_second_order_stable_limit {f : ℝ → ℝ} (C : ℝ)
    (hf : DifferentiableOn ℝ f (Ici 0))
    (hff : ∀ᶠ x : ℝ in atTop, DifferentiableAt ℝ (deriv f) x)
    (hl : Tendsto (fun x ↦ f x + deriv f x + deriv (deriv f) x) atTop (𝓝 C)) :
    Tendsto f atTop (𝓝 C) := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp hff
  apply second_order_stable_limit (max a 1) C _ _ hl
  · intro x hx
    have hxpos : (0 : ℝ) < x := by
      have hh : (1 : ℝ) ≤ x := (le_max_right _ _).trans hx
      linarith
    exact ((hf x (mem_Ici.mpr hxpos.le)).differentiableAt (Ici_mem_nhds hxpos)).hasDerivAt
  · intro x hx
    exact (ha x ((le_max_left _ _).trans hx)).hasDerivAt

end calculus.Chapter04.Section03SecondOrderStableLimitExercise
