import calculus.Chapter04.Section01Derivatives
import Mathlib.Tactic.NormNum

/-!
# 4.1.2: vận tốc và đường thẳng tiếp tuyến

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 123–132.
-/
namespace calculus.Chapter04.Section01Geometry
open Filter Set Section01Derivatives
open scoped Topology

/-- Vận tốc trung bình theo số gia thời gian `h > 0`. -/
noncomputable def averageVelocity (s : ℝ → ℝ) (t h : ℝ) : ℝ := (s (t + h) - s t) / h

theorem averageVelocity_denominator_ne_zero {h : ℝ} (hh : 0 < h) : h ≠ 0 := ne_of_gt hh


theorem instantaneous_velocity_iff_hasDerivAt (s : ℝ → ℝ) (t v : ℝ) :
    Tendsto (averageVelocity s t) (𝓝[≠] (0 : ℝ)) (𝓝 v) ↔ HasDerivAt s v t :=
  (hasDerivAt_iff_increment_limit s t v).symm


theorem instantaneous_velocity_eq_deriv {s : ℝ → ℝ} {t v : ℝ}
    (h : Tendsto (averageVelocity s t) (𝓝[≠] (0 : ℝ)) (𝓝 v)) : deriv s t = v :=
  ((instantaneous_velocity_iff_hasDerivAt s t v).mp h).deriv

/-- Dòng 123: độ dời có thể âm, còn quãng đường luôn không âm. -/
theorem signed_displacement_counterexample :
    ((fun t : ℝ ↦ -t) 1 - (fun t : ℝ ↦ -t) 0) < 0 ∧
      |(fun t : ℝ ↦ -t) 1 - (fun t : ℝ ↦ -t) 0| = 1 := by norm_num


noncomputable def secantLine (f : ℝ → ℝ) (x z y : ℝ) : ℝ :=
  f x + (f z - f x) / (z - x) * (y - x)


noncomputable def tangentLine (f : ℝ → ℝ) (x L y : ℝ) : ℝ := f x + L * (y - x)

theorem secantLine_at_first (f : ℝ → ℝ) (x z : ℝ) : secantLine f x z x = f x := by
  simp [secantLine]

theorem secantLine_at_second (f : ℝ → ℝ) (x z : ℝ) (hz : z ≠ x) :
    secantLine f x z z = f z := by
  simp [secantLine, sub_ne_zero.mpr hz]


theorem secantLine_tendsto_tangent {f : ℝ → ℝ} {I : Set ℝ} {x L : ℝ}
    (h : HasDerivativeWithinAt f I x L) (y : ℝ) :
    Tendsto (fun z ↦ secantLine f x z y) (𝓝[I \ {x}] x) (𝓝 (tangentLine f x L y)) :=
  tendsto_const_nhds.add (h.mul_const (y - x))


theorem tangentLine_eq_derivative {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x L : ℝ} (hx : x ∈ I) (h : HasDerivativeWithinAt f I x L) (y : ℝ) :
    tangentLine f x L y = f x + deriv f x * (y - x) := by
  rw [deriv_eq_of_hasDerivativeWithinAt hI hx h]
  rfl

end calculus.Chapter04.Section01Geometry
