import calculus.Chapter04.Section03
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bài tập 4.3.32: giá trị trung bình cấp hai cho thương cát tuyến

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1379–1380. Hàm chỉ cần khả vi hai lần; điểm kết luận nằm trong `(a, b)`.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section03SecondMeanExercise
open Set

/-- Thương cát tuyến trên `x > a`. -/
def secantSlope (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (f x - f a) / (x - a)


theorem second_mean_secant_witness {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hff : Differentiable ℝ (deriv f))
    {a b : ℝ} (hab : a < b) :
    ∃ ξ ∈ Ioo a b,
      (secantSlope f a ξ - secantSlope f a b) / (ξ - b) =
        deriv (deriv f) ξ / 2 := by
  let s : ℝ := secantSlope f a b
  let F : ℝ → ℝ := fun x ↦ f x - f a - s * (x - a)
  let F₁ : ℝ → ℝ := fun x ↦ deriv f x - s
  let p : ℝ → ℝ := fun x ↦ (x - a) * (x - b)
  let p₁ : ℝ → ℝ := fun x ↦ (x - b) + (x - a)
  let W : ℝ → ℝ := fun x ↦ F₁ x * p x - F x * p₁ x
  have hF (x : ℝ) : HasDerivAt F (F₁ x) x := by
    simpa only [mul_one, id_eq] using
      ((hf x).hasDerivAt.sub_const (f a)).fun_sub
        (((hasDerivAt_id x).sub_const a).const_mul s)
  have hF₁ (x : ℝ) : HasDerivAt F₁ (deriv (deriv f) x) x :=
    (hff x).hasDerivAt.sub_const s
  have hp (x : ℝ) : HasDerivAt p (p₁ x) x := by
    have ht := ((hasDerivAt_id x).sub_const a).fun_mul
      ((hasDerivAt_id x).sub_const b)
    apply ht.congr_deriv
    simp only [p₁, one_mul, mul_one, id_eq]
  have hp₁ (x : ℝ) : HasDerivAt p₁ 2 x := by
    have ht := ((hasDerivAt_id x).sub_const b).fun_add
      ((hasDerivAt_id x).sub_const a)
    exact ht.congr_deriv (by norm_num)
  have hW (x : ℝ) :
      HasDerivAt W (deriv (deriv f) x * p x - 2 * F x) x := by
    have ht := ((hF₁ x).fun_mul (hp x)).fun_sub ((hF x).fun_mul (hp₁ x))
    apply ht.congr_deriv
    ring
  have hFc : Continuous F :=
    (hf.continuous.sub continuous_const).sub
      (continuous_const.mul (continuous_id.sub continuous_const))
  have hF₁c : Continuous F₁ := hff.continuous.sub continuous_const
  have hpc : Continuous p :=
    (continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const)
  have hp₁c : Continuous p₁ :=
    (continuous_id.sub continuous_const).add (continuous_id.sub continuous_const)
  have hWc : Continuous W := (hF₁c.mul hpc).sub (hFc.mul hp₁c)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hFa : F a = 0 := by simp [F]
  have hFb : F b = 0 := by
    dsimp [F, s, secantSlope]
    rw [div_mul_cancel₀ _ hba]
    ring
  have hWa : W a = 0 := by simp [W, p, hFa]
  have hWb : W b = 0 := by simp [W, p, hFb]
  obtain ⟨ξ, hξ, hcancel⟩ := exists_hasDerivAt_eq_zero hab hWc.continuousOn
    (hWa.trans hWb.symm) (fun x _ ↦ hW x)
  have hξa : ξ - a ≠ 0 := sub_ne_zero.mpr hξ.1.ne'
  have hξb : ξ - b ≠ 0 := sub_ne_zero.mpr hξ.2.ne
  have he : deriv (deriv f) ξ * ((ξ - a) * (ξ - b)) -
      2 * (f ξ - f a - s * (ξ - a)) = 0 := by
    simpa only [p, F] using hcancel
  refine ⟨ξ, hξ, ?_⟩
  change (((f ξ - f a) / (ξ - a) - s) / (ξ - b)) = deriv (deriv f) ξ / 2
  field_simp [hξa, hξb]
  nlinarith [he]


theorem second_mean_exercise {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hff : Differentiable ℝ (deriv f))
    {a b c₀ : ℝ} (hab : a < b) (_hbc : b < c₀) :
    ∃ ξ ∈ Ioo a b,
      (secantSlope f a ξ - secantSlope f a b) / (ξ - b) =
        deriv (deriv f) ξ / 2 :=
  second_mean_secant_witness hf hff hab

end calculus.Chapter04.Section03SecondMeanExercise
