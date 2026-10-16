import calculus.Chapter04.Section04InfiniteExtensions
import calculus.Chapter03.Section02Infinite
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# §4.4 Bài 8: giới hạn từ tổ hợp vi phân trên (0,+∞)

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1742–1749. `L` là giới hạn hữu hạn của tổ hợp vi phân; hai kết luận có phản ví dụ khi `a < 0`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace calculus.Chapter04.Section04DifferentialAsymptoticExercises
open calculus.Chapter03.Section02Infinite

theorem source_positive_halfline_at_top_iff {f : ℝ → ℝ} {L : ℝ} :
    DomainAtTopLimit (Ioi (0 : ℝ)) f L ↔ Tendsto f atTop (𝓝 L) := by
  have hb : ¬BddAbove (Ioi (0 : ℝ)) := not_bddAbove_Ioi (0 : ℝ)
  have hfilter : atTop ⊓ 𝓟 (Ioi (0 : ℝ)) = atTop := by
    apply inf_eq_left.mpr
    exact le_principal_iff.mpr (eventually_gt_atTop (0 : ℝ))
  rw [domainAtTopLimit_iff_tendsto hb, hfilter]

theorem linear_differential_combination_tendsto {f : ℝ → ℝ} {a L : ℝ}
    (ha : 0 < a) (hf : DifferentiableOn ℝ f (Ioi 0))
    (hs : Tendsto (fun x : ℝ ↦ a * f x + deriv f x) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 (L / a)) := by
  have hdf (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : HasDerivAt f (deriv f x) x :=
    ((hf x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have he (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.exp (a * y))
      (a * Real.exp (a * x)) x := by
    convert! ((hasDerivAt_id x).const_mul a).exp using 1; (simp only [id_eq]; ring)
  have hg (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun y : ℝ ↦ f y * Real.exp (a * y))
        ((a * f x + deriv f x) * Real.exp (a * x)) x := by
    have ht := (hdf x hx).fun_mul (he x)
    apply ht.congr_deriv
    ring
  have hratio : Tendsto (fun x : ℝ ↦
      ((a * f x + deriv f x) * Real.exp (a * x)) / (a * Real.exp (a * x)))
      atTop (𝓝 (L / a)) := by
    apply (hs.div_const a).congr'
    filter_upwards with x
    field_simp [ha.ne', Real.exp_ne_zero (a * x)]
  have heinf : Tendsto (fun x : ℝ ↦ Real.exp (a * x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
  have ht := calculus.Chapter04.Section04InfiniteExtensions.lhopital_infinite_atTop_hasDerivAt
    (a := 0) hg (fun x _ ↦ he x)
    (fun x _ ↦ mul_ne_zero ha.ne' (Real.exp_ne_zero (a * x)))
    (Or.inl heinf) hratio (Or.inl ⟨L / a, rfl⟩)
  apply ht.congr'
  filter_upwards with x
  field_simp [Real.exp_ne_zero (a * x)]

theorem source_linear_differential_combination_limit (f : ℝ → ℝ) (a L : ℝ)
    (ha : 0 < a) (hf : DifferentiableOn ℝ f (Ioi 0))
    (hs : DomainAtTopLimit (Ioi 0) (fun x : ℝ ↦ a * f x + deriv f x) L) :
    DomainAtTopLimit (Ioi 0) f (L / a) := by
  apply source_positive_halfline_at_top_iff.mpr
  exact linear_differential_combination_tendsto ha hf (source_positive_halfline_at_top_iff.mp hs)

theorem sqrt_weighted_differential_combination_tendsto {f : ℝ → ℝ} {a L : ℝ}
    (ha : 0 < a) (hf : DifferentiableOn ℝ f (Ioi 0))
    (hs : Tendsto (fun x : ℝ ↦ a * f x + 2 * Real.sqrt x * deriv f x) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 (L / a)) := by
  let g : ℝ → ℝ := fun t ↦ f (t ^ 2)
  have hgd (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt g (2 * t * deriv f (t ^ 2)) t := by
    have htp : t ^ 2 ∈ Ioi (0 : ℝ) := by exact sq_pos_of_pos (show 0 < t from ht)
    have hdf : HasDerivAt f (deriv f (t ^ 2)) (t ^ 2) :=
      ((hf (t ^ 2) htp).differentiableAt (isOpen_Ioi.mem_nhds htp)).hasDerivAt
    have hpow : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t := by
      simpa using! (hasDerivAt_id t).fun_pow 2
    have hcomp := HasDerivAt.comp (h := fun u : ℝ ↦ u ^ 2) t hdf hpow
    apply hcomp.congr_deriv
    ring
  have hdiff : DifferentiableOn ℝ g (Ioi 0) :=
    fun t ht ↦ (hgd t ht).differentiableAt.differentiableWithinAt
  have htrans := hs.comp (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hgsource : Tendsto (fun t : ℝ ↦ a * g t + deriv g t) atTop (𝓝 L) := by
    apply htrans.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [(hgd t ht).deriv]
    simp only [Function.comp_def, g, Real.sqrt_sq_eq_abs, abs_of_pos ht]
  have hglim := linear_differential_combination_tendsto ha hdiff hgsource
  have ht := hglim.comp Real.tendsto_sqrt_atTop
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, g, Real.sq_sqrt hx.le]

theorem source_sqrt_weighted_differential_combination_limit (f : ℝ → ℝ) (a L : ℝ)
    (ha : 0 < a) (hf : DifferentiableOn ℝ f (Ioi 0))
    (hs : DomainAtTopLimit (Ioi 0) (fun x : ℝ ↦ a * f x + 2 * Real.sqrt x * deriv f x) L) :
    DomainAtTopLimit (Ioi 0) f (L / a) := by
  apply source_positive_halfline_at_top_iff.mpr
  exact sqrt_weighted_differential_combination_tendsto ha hf
    (source_positive_halfline_at_top_iff.mp hs)

def exponentialLinearODECounterexample (a x : ℝ) : ℝ := Real.exp (-a * x)
def exponentialSqrtODECounterexample (a x : ℝ) : ℝ := Real.exp (-a * Real.sqrt x)

theorem exponentialLinearODECounterexample_hasDerivAt (a x : ℝ) :
    HasDerivAt (exponentialLinearODECounterexample a) (-a * exponentialLinearODECounterexample a x) x := by
  convert! ((hasDerivAt_id x).const_mul (-a)).exp using 1;
    (dsimp only [exponentialLinearODECounterexample]; simp only [id_eq]; ring)

theorem source_negative_a_linear_counterexample (a : ℝ) (ha : a < 0) :
    DifferentiableOn ℝ (exponentialLinearODECounterexample a) (Ioi 0) ∧
      DomainAtTopLimit (Ioi 0)
        (fun x : ℝ ↦ a * exponentialLinearODECounterexample a x + deriv (exponentialLinearODECounterexample a) x) 0 ∧
      Tendsto (exponentialLinearODECounterexample a) atTop atTop ∧
      ¬DomainAtTopLimit (Ioi 0) (exponentialLinearODECounterexample a) (0 / a) := by
  have htop : Tendsto (exponentialLinearODECounterexample a) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (neg_pos.mpr ha))
  refine ⟨fun x _ ↦ (exponentialLinearODECounterexample_hasDerivAt a x).differentiableAt.differentiableWithinAt,
    ?_, htop, ?_⟩
  · apply source_positive_halfline_at_top_iff.mpr
    have heq (x : ℝ) : a * exponentialLinearODECounterexample a x + deriv (exponentialLinearODECounterexample a) x = 0 := by
      rw [(exponentialLinearODECounterexample_hasDerivAt a x).deriv]
      ring
    simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atTop (𝓝 0))
  · intro he
    exact (not_tendsto_nhds_of_tendsto_atTop htop (0 / a)) (source_positive_halfline_at_top_iff.mp he)

theorem exponentialSqrtODECounterexample_hasDerivAt {a x : ℝ} (hx : 0 < x) :
    HasDerivAt (exponentialSqrtODECounterexample a)
      (-a / (2 * Real.sqrt x) * exponentialSqrtODECounterexample a x) x := by
  have ht := ((Real.hasDerivAt_sqrt hx.ne').const_mul (-a)).exp
  convert! ht using 1
  dsimp only [exponentialSqrtODECounterexample]
  ring

theorem source_negative_a_sqrt_counterexample (a : ℝ) (ha : a < 0) :
    DifferentiableOn ℝ (exponentialSqrtODECounterexample a) (Ioi 0) ∧
      DomainAtTopLimit (Ioi 0)
        (fun x : ℝ ↦ a * exponentialSqrtODECounterexample a x +
          2 * Real.sqrt x * deriv (exponentialSqrtODECounterexample a) x) 0 ∧
      Tendsto (exponentialSqrtODECounterexample a) atTop atTop ∧
      ¬DomainAtTopLimit (Ioi 0) (exponentialSqrtODECounterexample a) (0 / a) := by
  have htop : Tendsto (exponentialSqrtODECounterexample a) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_sqrt_atTop.const_mul_atTop (neg_pos.mpr ha))
  refine ⟨fun x hx ↦ (exponentialSqrtODECounterexample_hasDerivAt hx).differentiableAt.differentiableWithinAt,
    ?_, htop, ?_⟩
  · apply source_positive_halfline_at_top_iff.mpr
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [(exponentialSqrtODECounterexample_hasDerivAt hx).deriv]
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    field_simp [hs]
    ring
  · intro he
    exact (not_tendsto_nhds_of_tendsto_atTop htop (0 / a)) (source_positive_halfline_at_top_iff.mp he)

end calculus.Chapter04.Section04DifferentialAsymptoticExercises
