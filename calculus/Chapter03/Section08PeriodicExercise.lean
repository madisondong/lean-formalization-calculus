import calculus.Chapter03.Section01Properties
import calculus.Chapter03.Section04
import calculus.Chapter03.Section08HeineCantor
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §3.8 — liên tục và tuần hoàn suy ra liên tục đều

Nguồn: Bài tập 3.8.9, `source/Ch3_gioihanhamso.tex` dòng 3967–3969.
-/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08PeriodicExercise
open calculus.Chapter03.Section01Properties calculus.Chapter03.Section04
open calculus.Chapter03.Section08 calculus.Chapter03.Section08HeineCantor

/-- Bài tập 3.8.9: hàm liên tục tuần hoàn trên ℝ thì liên tục đều. -/
theorem sourceContinuous_hasPositiveForwardPeriod_uniformContinuous {f : ℝ → ℝ}
    (hc : DomainContinuousOn univ f) (hp : HasPositiveForwardPeriod univ f) :
    NonemptyUniformContinuousOn univ f := by
  obtain ⟨T, hT, hper⟩ := hp
  have hf : Function.Periodic f T := fun x ↦ (hper x (mem_univ x)).2
  have hcont : ContinuousOn f (Icc (-T) (2 * T)) :=
    ((domainContinuousOn_iff_continuousOn (univ_nonempty : (univ : Set ℝ).Nonempty)).mp
      hc).mono (subset_univ _)
  have hcompact : NonemptyUniformContinuousOn (Icc (-T) (2 * T)) f :=
    continuousOn_closedInterval_nonemptyUniformContinuousOn
      (nonempty_Icc.mpr (by linarith)) hcont
  refine ⟨univ_nonempty, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hcompact.2 ε hε
  refine ⟨min δ T, lt_min hδ hT, ?_⟩
  intro u _hu v _hv huv
  let n : ℤ := ⌊u / T⌋
  let u₀ : ℝ := u - (n : ℝ) * T
  let v₀ : ℝ := v - (n : ℝ) * T
  have hfloor : (n : ℝ) * T ≤ u :=
    (le_div_iff₀ hT).mp (Int.floor_le (u / T))
  have hceil : u < ((n : ℝ) + 1) * T :=
    (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (u / T))
  have hu0 : 0 ≤ u₀ := by dsimp only [u₀]; linarith
  have huT : u₀ < T := by dsimp only [u₀]; nlinarith
  have hdist : |u₀ - v₀| = |u - v| := by
    dsimp only [u₀, v₀]
    congr 1
    ring
  have huvT : |u₀ - v₀| < T :=
    hdist.trans_lt (huv.trans_le (min_le_right _ _))
  have hbetween := abs_lt.mp huvT
  have huI : u₀ ∈ Icc (-T) (2 * T) := ⟨by linarith, by linarith⟩
  have hvI : v₀ ∈ Icc (-T) (2 * T) := ⟨by linarith [hbetween.2], by linarith [hbetween.1]⟩
  have hsmall := hb u₀ huI v₀ hvI (hdist.trans_lt (huv.trans_le (min_le_left _ _)))
  have hfu : f u₀ = f u := (hf.int_mul n).sub_eq u
  have hfv : f v₀ = f v := (hf.int_mul n).sub_eq v
  simpa only [hfu, hfv] using hsmall

end calculus.Chapter03.Section08PeriodicExercise
