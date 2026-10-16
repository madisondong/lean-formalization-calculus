import calculus.Chapter04.Section03ReciprocalLogMaclaurin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §4.3: miền đoạn Taylor tại dòng 1287

Nguồn: các công thức dòng 1290–1292. Toàn đoạn từ 0 đến `x` phải nằm trong miền trơn; chỉ kiểm tra mẫu tại điểm cuối là chưa đủ.
-/

set_option autoImplicit false
noncomputable section
open Set Finset
open scoped BigOperators
namespace calculus.Chapter04.Section03MaclaurinTaylorSegmentDomains
open calculus.Chapter04.Section03ReciprocalLogMaclaurin

/-- Đoạn Taylor từ 0 đến `x` tránh cực −1. -/
def PlusTaylorSegmentDomain (x : ℝ) : Prop :=
  ∀ y ∈ uIcc (0 : ℝ) x, 1 + y ≠ 0

/-- Đoạn Taylor từ 0 đến `x` tránh cực 1. -/
def MinusTaylorSegmentDomain (x : ℝ) : Prop :=
  ∀ y ∈ uIcc (0 : ℝ) x, 1 - y ≠ 0

/-- Toàn bộ đoạn Taylor thuộc miền logarit thực dương. -/
def LogTaylorSegmentDomain (x : ℝ) : Prop :=
  ∀ y ∈ uIcc (0 : ℝ) x, 0 < 1 + y

theorem plus_taylor_segment_domain_iff (x : ℝ) :
    PlusTaylorSegmentDomain x ↔ -1 < x := by
  constructor
  · intro h
    by_contra hx
    have hx' : x ≤ -1 := le_of_not_gt hx
    have hx0 : x ≤ 0 := by linarith
    have hpole : (-1 : ℝ) ∈ uIcc 0 x := by
      rw [uIcc_of_ge hx0]
      exact ⟨hx', by norm_num⟩
    have hh := h (-1) hpole
    norm_num at hh
  · intro hx y hy
    exact (one_add_pos_on_segment hx hy).ne'

theorem minus_taylor_segment_domain_iff (x : ℝ) :
    MinusTaylorSegmentDomain x ↔ x < 1 := by
  constructor
  · intro h
    by_contra hx
    have hx' : 1 ≤ x := le_of_not_gt hx
    have hx0 : 0 ≤ x := by linarith
    have hpole : (1 : ℝ) ∈ uIcc 0 x := by
      rw [uIcc_of_le hx0]
      exact ⟨by norm_num, hx'⟩
    have hh := h 1 hpole
    norm_num at hh
  · intro hx y hy
    exact (one_sub_pos_on_segment hx hy).ne'

theorem log_taylor_segment_domain_iff (x : ℝ) :
    LogTaylorSegmentDomain x ↔ 0 < 1 + x := by
  constructor
  · intro h
    exact h x right_mem_uIcc
  · intro hx y hy
    exact one_add_pos_on_segment (by linarith) hy

/-- Công thức, dòng 1290: khai triển của `1/(1+x)` trên miền `x > −1`. -/
theorem plus_reciprocal_maclaurin_on_maximal_taylor_segment (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : PlusTaylorSegmentDomain x) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      1 / (1 + x) = (∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * x ^ k) +
        (-1 : ℝ) ^ (n + 1) * (1 / (1 + θ * x) ^ (n + 2)) * x ^ (n + 1) :=
  plusReciprocal_maclaurin_on_source_component n hn x
    ((plus_taylor_segment_domain_iff x).mp hx)

/-- Công thức, dòng 1291: khai triển của `1/(1−x)` trên miền `x < 1`. -/
theorem minus_reciprocal_maclaurin_on_maximal_taylor_segment (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : MinusTaylorSegmentDomain x) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      1 / (1 - x) = (∑ k ∈ range (n + 1), x ^ k) +
        (1 / (1 - θ * x) ^ (n + 2)) * x ^ (n + 1) :=
  minusReciprocal_maclaurin_on_source_component n hn x
    ((minus_taylor_segment_domain_iff x).mp hx)

/-- Công thức, dòng 1292: khai triển của `ln(1+x)` trên miền `x > −1`. -/
theorem source_log_one_add_maclaurin_on_full_natural_domain (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : 0 < 1 + x) :
    LogTaylorSegmentDomain x ∧
      ∃ θ ∈ Ioo (0 : ℝ) 1,
        Real.log (1 + x) =
          (∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (k + 1) / (k + 1 : ℕ)) +
            (-1 : ℝ) ^ n * x ^ (n + 1) /
              ((1 + θ * x) ^ (n + 1) * (n + 1 : ℕ)) := by
  exact ⟨(log_taylor_segment_domain_iff x).mpr hx,
    logOneAdd_maclaurin_on_source_domain n hn x (by linarith)⟩

/-- Dòng 1290: phản ví dụ `n = 1`, `x = −2`, với đoạn Taylor đi qua cực −1. -/
theorem plus_reciprocal_cross_pole_source_counterexample :
    (-2 : ℝ) ≠ -1 ∧
      ¬∃ θ ∈ Ioo (0 : ℝ) 1,
        1 / (1 + (-2 : ℝ)) = 1 - (-2 : ℝ) +
          (1 / (1 + θ * (-2)) ^ 3) * (-2 : ℝ) ^ 2 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨θ, hθ, he⟩
  apply crossing_pole_first_degree_counterexample
  refine ⟨θ, hθ, ?_⟩
  have hden : 1 + θ * (-2) = 1 - 2 * θ := by ring
  rw [hden] at he
  norm_num at he
  convert he using 1; ring

/-- Dòng 1291: phản ví dụ `n = 1`, `x = 2`, với đoạn Taylor đi qua cực 1. -/
theorem minus_reciprocal_cross_pole_source_counterexample :
    (2 : ℝ) ≠ 1 ∧
      ¬∃ θ ∈ Ioo (0 : ℝ) 1,
        1 / (1 - (2 : ℝ)) = 1 + (2 : ℝ) +
          (1 / (1 - θ * 2) ^ 3) * (2 : ℝ) ^ 2 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨θ, hθ, he⟩
  apply crossing_pole_first_degree_counterexample
  refine ⟨θ, hθ, ?_⟩
  have hden : 1 - θ * 2 = 1 - 2 * θ := by ring
  rw [hden] at he
  norm_num at he
  convert he using 1; ring

end calculus.Chapter04.Section03MaclaurinTaylorSegmentDomains
