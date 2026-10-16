import calculus.Chapter04.Section01Higher
import calculus.Chapter04.Section01Derivatives

/-!
# 4.1.24: đạo hàm cấp cao trên đoạn

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 402–403. Xét `a < b`; đạo hàm ở đầu mút là đạo hàm một bên, các đạo hàm cấp thấp hơn đều hữu hạn.
-/
namespace calculus.Chapter04.Section01HigherClosed
open Set Filter calculus.Chapter04.Section01Higher
open scoped Topology


def HasRightDerivativesUpToOrder : ℕ → (ℝ → ℝ) → ℝ → ℝ → Prop
  | 0, _, _, _ => True
  | n + 1, f, a, b => HasRightDerivativesUpToOrder n f a b ∧
      ∃ L : ℝ, Tendsto
        (fun x ↦ (iteratedDerivWithin n f (Icc a b) x -
          iteratedDerivWithin n f (Icc a b) a) / (x - a)) (𝓝[Ioo a b] a) (𝓝 L)


def HasLeftDerivativesUpToOrder : ℕ → (ℝ → ℝ) → ℝ → ℝ → Prop
  | 0, _, _, _ => True
  | n + 1, f, a, b => HasLeftDerivativesUpToOrder n f a b ∧
      ∃ L : ℝ, Tendsto
        (fun x ↦ (iteratedDerivWithin n f (Icc a b) x -
          iteratedDerivWithin n f (Icc a b) b) / (x - b)) (𝓝[Ioo a b] b) (𝓝 L)


def DifferentiableToOrderOnClosedInterval (n : ℕ) (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  a < b ∧ DifferentiableToOrderOn n f (Ioo a b) ∧
    HasRightDerivativesUpToOrder n f a b ∧ HasLeftDerivativesUpToOrder n f a b


theorem right_order_one_iff {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    HasRightDerivativesUpToOrder 1 f a b ↔
      ∃ L : ℝ, Section01Derivatives.HasRightDerivativeAt f a L := by
  simp only [HasRightDerivativesUpToOrder, iteratedDerivWithin_zero, true_and,
    nhdsWithin_Ioo_eq_nhdsGT hab, Section01Derivatives.HasRightDerivativeAt]


theorem left_order_one_iff {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    HasLeftDerivativesUpToOrder 1 f a b ↔
      ∃ L : ℝ, Section01Derivatives.HasLeftDerivativeAt f b L := by
  simp only [HasLeftDerivativesUpToOrder, iteratedDerivWithin_zero, true_and,
    nhdsWithin_Ioo_eq_nhdsLT hab, Section01Derivatives.HasLeftDerivativeAt]


theorem source_closed_order_one_iff {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    DifferentiableToOrderOnClosedInterval 1 f a b ↔
      Section01Derivatives.DifferentiableOnClosedInterval f a b := by
  rw [DifferentiableToOrderOnClosedInterval, and_iff_right hab,
    differentiableToOrderOn_one, right_order_one_iff hab, left_order_one_iff hab]
  have hi : (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) ↔ DifferentiableOn ℝ f (Ioo a b) :=
    by
      constructor
      · intro h x hx
        exact (h x hx).differentiableWithinAt
      · intro h x hx
        exact (h x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  simp only [Section01Derivatives.DifferentiableOnClosedInterval, hi]


theorem source_closed_nonempty {n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableToOrderOnClosedInterval n f a b) :
    (Ioo a b).Nonempty ∧ NeBot (𝓝[Ioo a b] a) ∧ NeBot (𝓝[Ioo a b] b) :=
  ⟨nonempty_Ioo.mpr hf.1, left_nhdsWithin_Ioo_neBot hf.1, right_nhdsWithin_Ioo_neBot hf.1⟩

end calculus.Chapter04.Section01HigherClosed
