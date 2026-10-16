import calculus.Chapter04.Section01Higher
import calculus.Chapter04.Section01Derivatives
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope

/-!
# Lồi, lõm, dây cung và điểm uốn

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1843–1957. Tính lồi và lõm không ngặt cho phép hàm afin thuộc cả hai lớp.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04ConvexityAndInflection
open Set Filter calculus.Chapter04.Section01Higher
open calculus.Chapter04.Section01Derivatives
open scoped Topology

/-- Định nghĩa 4.4.15: tính lồi trên `(a, b)`, với trọng số `λ ∈ (0, 1)`. -/
def ConvexOnOpenInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x₁ ∈ Ioo a b, ∀ x₂ ∈ Ioo a b, ∀ w ∈ Ioo (0 : ℝ) 1,
    f (w * x₁ + (1 - w) * x₂) ≤ w * f x₁ + (1 - w) * f x₂


def ConcaveOnOpenInterval (f : ℝ → ℝ) (a b : ℝ) : Prop := ConvexOnOpenInterval (fun x ↦ -f x) a b


theorem convexOnOpenInterval_iff_convexOn (f : ℝ → ℝ) (a b : ℝ) :
    ConvexOnOpenInterval f a b ↔ ConvexOn ℝ (Ioo a b) f := by
  rw [convexOn_iff_forall_pos]
  constructor
  · intro h
    refine ⟨convex_Ioo a b, ?_⟩
    intro x hx y hy u v hu hv huv
    have he : v = 1 - u := by linarith
    simpa only [he, smul_eq_mul] using h x hx y hy u ⟨hu, by linarith⟩
  · intro h x hx y hy w «hλ»
    simpa only [smul_eq_mul] using h.2 hx hy «hλ».1 (sub_pos.mpr «hλ».2) (by ring)


theorem concaveOnOpenInterval_iff_concaveOn (f : ℝ → ℝ) (a b : ℝ) :
    ConcaveOnOpenInterval f a b ↔ ConcaveOn ℝ (Ioo a b) f := by
  rw [ConcaveOnOpenInterval, convexOnOpenInterval_iff_convexOn]
  exact neg_convexOn_iff

/-- Nhận xét 4.4.16: tung độ đồ thị không vượt tung độ dây cung. -/
theorem source_chord_ordinate_le {f : ℝ → ℝ} {a b x₁ x₂ w : ℝ}
    (hf : ConvexOnOpenInterval f a b) (hx₁ : x₁ ∈ Ioo a b) (hx₂ : x₂ ∈ Ioo a b)
    (_horder : x₁ < x₂) («hλ» : w ∈ Ioo (0 : ℝ) 1) :
    f (w * x₁ + (1 - w) * x₂) ≤ w * f x₁ + (1 - w) * f x₂ :=
  hf x₁ hx₁ x₂ hx₂ w «hλ»

/-- Mệnh đề 4.4.17: tính lồi tương đương với hai bất đẳng thức hệ số góc cát tuyến. -/
theorem convexOnOpenInterval_iff_secant_chain (f : ℝ → ℝ) (a b : ℝ) :
    ConvexOnOpenInterval f a b ↔ ∀ x₁ ∈ Ioo a b, ∀ x₂ ∈ Ioo a b, ∀ x₃ ∈ Ioo a b,
      x₁ < x₂ → x₂ < x₃ →
      (f x₂ - f x₁) / (x₂ - x₁) ≤ (f x₃ - f x₁) / (x₃ - x₁) ∧
        (f x₃ - f x₁) / (x₃ - x₁) ≤ (f x₃ - f x₂) / (x₃ - x₂) := by
  rw [convexOnOpenInterval_iff_convexOn]
  constructor
  · intro hf x₁ hx₁ x₂ hx₂ x₃ hx₃ h₁₂ h₂₃
    exact ⟨hf.secant_mono_aux2 hx₁ hx₃ h₁₂ h₂₃,
      hf.secant_mono_aux3 hx₁ hx₃ h₁₂ h₂₃⟩
  · intro hf
    apply convexOn_of_slope_mono_adjacent (convex_Ioo a b)
    intro x₁ x₂ x₃ hx₁ hx₃ h₁₂ h₂₃
    have hx₂ : x₂ ∈ Ioo a b := ⟨hx₁.1.trans h₁₂, h₂₃.trans hx₃.2⟩
    exact (hf x₁ hx₁ x₂ hx₂ x₃ hx₃ h₁₂ h₂₃).1.trans
      (hf x₁ hx₁ x₂ hx₂ x₃ hx₃ h₁₂ h₂₃).2

/-- Định lí 4.4.18: với hàm khả vi, tính lồi tương đương với đạo hàm tăng không ngặt. -/
theorem convexOnOpenInterval_iff_monotone_deriv (f : ℝ → ℝ) (a b : ℝ)
    (hf : DifferentiableOn ℝ f (Ioo a b)) :
    ConvexOnOpenInterval f a b ↔ MonotoneOn (deriv f) (Ioo a b) := by
  rw [convexOnOpenInterval_iff_convexOn]
  constructor
  · intro hc
    exact hc.monotoneOn_deriv (fun x hx ↦ (hf x hx).differentiableAt (isOpen_Ioo.mem_nhds hx))
  · intro hm
    exact MonotoneOn.convexOn_of_deriv (convex_Ioo a b) hf.continuousOn
      (by simpa only [isOpen_Ioo.interior_eq] using hf)
      (by simpa only [isOpen_Ioo.interior_eq] using hm)

/-- Hệ quả 4.4.19: với hàm khả vi hai lần, tính lồi tương đương với đạo hàm cấp hai không âm. -/
theorem convexOnOpenInterval_iff_second_deriv_nonneg (f : ℝ → ℝ) (a b : ℝ)
    (hf : DifferentiableToOrderOn 2 f (Ioo a b)) :
    ConvexOnOpenInterval f a b ↔ ∀ x ∈ Ioo a b, 0 ≤ deriv (deriv f) x := by
  have hd := (differentiableToOrderOn_two f isOpen_Ioo).mp hf
  rw [convexOnOpenInterval_iff_monotone_deriv f a b hd.1]
  constructor
  · intro hm x hx
    have hp := hm.derivWithin_nonneg (x := x)
    rwa [derivWithin_of_isOpen isOpen_Ioo hx] at hp
  · intro hp
    apply monotoneOn_of_deriv_nonneg (convex_Ioo a b) hd.2.continuousOn
    · simpa only [isOpen_Ioo.interior_eq] using hd.2
    · simpa only [isOpen_Ioo.interior_eq] using hp


theorem concaveOnOpenInterval_of_second_deriv_nonpos (f : ℝ → ℝ) (a b : ℝ)
    (hf : DifferentiableToOrderOn 2 f (Ioo a b))
    (hp : ∀ x ∈ Ioo a b, deriv (deriv f) x ≤ 0) : ConcaveOnOpenInterval f a b := by
  apply (concaveOnOpenInterval_iff_concaveOn f a b).mpr
  have hd := (differentiableToOrderOn_two f isOpen_Ioo).mp hf
  apply concaveOn_of_deriv2_nonpos' (convex_Ioo a b) hd.1 hd.2
  intro x hx
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hp x hx

/-- Định nghĩa 4.4.20: khả vi trên `(a, b) \ {x₀}`, có đạo hàm hai phía hữu hạn hoặc vô cùng tại `x₀ ∈ (a, b)`, lồi một phía và lõm phía kia. -/
def SourceInflectionOn (f : ℝ → ℝ) (a b x₀ : ℝ) : Prop :=
  x₀ ∈ Ioo a b ∧
  (∀ x ∈ (Ioo a b) \ {x₀}, DifferentiableAt ℝ f x) ∧
  (DifferentiableAt ℝ f x₀ ∨ HasInfiniteDerivativeWithinAt f (Ioo a b) x₀) ∧
  ∃ δ : ℝ, 0 < δ ∧ Ioo (x₀ - δ) (x₀ + δ) ⊆ Ioo a b ∧
    ((ConvexOnOpenInterval f (x₀ - δ) x₀ ∧ ConcaveOnOpenInterval f x₀ (x₀ + δ)) ∨
      (ConcaveOnOpenInterval f (x₀ - δ) x₀ ∧ ConvexOnOpenInterval f x₀ (x₀ + δ)))


theorem sourceInflectionOn_of_second_deriv_neg_pos {f : ℝ → ℝ} {x₀ δ : ℝ}
    (hδ : 0 < δ)
    (hl : DifferentiableToOrderOn 2 f (Ioo (x₀ - δ) x₀))
    (hr : DifferentiableToOrderOn 2 f (Ioo x₀ (x₀ + δ)))
    (hpoint : DifferentiableAt ℝ f x₀ ∨
      HasInfiniteDerivativeWithinAt f (Ioo (x₀ - δ) (x₀ + δ)) x₀)
    (hls : ∀ x ∈ Ioo (x₀ - δ) x₀, deriv (deriv f) x < 0)
    (hrs : ∀ x ∈ Ioo x₀ (x₀ + δ), 0 < deriv (deriv f) x) :
    SourceInflectionOn f (x₀ - δ) (x₀ + δ) x₀ := by
  have hld := (differentiableToOrderOn_two f isOpen_Ioo).mp hl
  have hrd := (differentiableToOrderOn_two f isOpen_Ioo).mp hr
  refine ⟨⟨by linarith, by linarith⟩, ?_, hpoint, δ, hδ, Subset.rfl, Or.inr ⟨?_, ?_⟩⟩
  · intro x hx
    rcases lt_or_gt_of_ne (show x ≠ x₀ from hx.2) with hx₀ | hx₀
    · exact (hld.1 x ⟨hx.1.1, hx₀⟩).differentiableAt (Ioo_mem_nhds hx.1.1 hx₀)
    · exact (hrd.1 x ⟨hx₀, hx.1.2⟩).differentiableAt (Ioo_mem_nhds hx₀ hx.1.2)
  · exact concaveOnOpenInterval_of_second_deriv_nonpos f (x₀ - δ) x₀ hl fun x hx ↦ (hls x hx).le
  · exact (convexOnOpenInterval_iff_second_deriv_nonneg f x₀ (x₀ + δ) hr).mpr fun x hx ↦ (hrs x hx).le


theorem sourceInflectionOn_of_second_deriv_pos_neg {f : ℝ → ℝ} {x₀ δ : ℝ}
    (hδ : 0 < δ)
    (hl : DifferentiableToOrderOn 2 f (Ioo (x₀ - δ) x₀))
    (hr : DifferentiableToOrderOn 2 f (Ioo x₀ (x₀ + δ)))
    (hpoint : DifferentiableAt ℝ f x₀ ∨
      HasInfiniteDerivativeWithinAt f (Ioo (x₀ - δ) (x₀ + δ)) x₀)
    (hls : ∀ x ∈ Ioo (x₀ - δ) x₀, 0 < deriv (deriv f) x)
    (hrs : ∀ x ∈ Ioo x₀ (x₀ + δ), deriv (deriv f) x < 0) :
    SourceInflectionOn f (x₀ - δ) (x₀ + δ) x₀ := by
  have hld := (differentiableToOrderOn_two f isOpen_Ioo).mp hl
  have hrd := (differentiableToOrderOn_two f isOpen_Ioo).mp hr
  refine ⟨⟨by linarith, by linarith⟩, ?_, hpoint, δ, hδ, Subset.rfl, Or.inl ⟨?_, ?_⟩⟩
  · intro x hx
    rcases lt_or_gt_of_ne (show x ≠ x₀ from hx.2) with hx₀ | hx₀
    · exact (hld.1 x ⟨hx.1.1, hx₀⟩).differentiableAt (Ioo_mem_nhds hx.1.1 hx₀)
    · exact (hrd.1 x ⟨hx₀, hx.1.2⟩).differentiableAt (Ioo_mem_nhds hx₀ hx.1.2)
  · exact (convexOnOpenInterval_iff_second_deriv_nonneg f (x₀ - δ) x₀ hl).mpr fun x hx ↦ (hls x hx).le
  · exact concaveOnOpenInterval_of_second_deriv_nonpos f x₀ (x₀ + δ) hr fun x hx ↦ (hrs x hx).le

end calculus.Chapter04.Section04ConvexityAndInflection
