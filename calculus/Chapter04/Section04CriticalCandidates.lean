import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-!
# Giá trị lớn nhất, nhỏ nhất và các điểm tới hạn

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1827–1840, Nhận xét 4.4.14. Đoạn xét không rỗng.
-/
set_option autoImplicit false
noncomputable section
namespace calculus.Chapter04.Section04CriticalCandidates
open Set Filter
open scoped Topology


def IsCriticalPointOnOpenInterval (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  x ∈ Ioo a b ∧ (¬ DifferentiableAt ℝ f x ∨ deriv f x = 0)


def candidatePoints (a b : ℝ) (C : Finset ℝ) : Finset ℝ := insert a (insert b C)


def candidateValues (f : ℝ → ℝ) (a b : ℝ) (C : Finset ℝ) : Finset ℝ :=
  (candidatePoints a b C).image f


theorem candidateValues_nonempty (f : ℝ → ℝ) (a b : ℝ) (C : Finset ℝ) :
    (candidateValues f a b C).Nonempty := by
  classical
  exact ⟨f a, Finset.mem_image.mpr ⟨a, by simp [candidatePoints], rfl⟩⟩


theorem interior_global_maximum_is_critical {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hmax : IsMaxOn f (Icc a b) x) :
    IsLocalMax f x ∧ IsCriticalPointOnOpenInterval f a b x := by
  have hlocal := hmax.isLocalMax (Icc_mem_nhds hx.1 hx.2)
  refine ⟨hlocal, hx, ?_⟩
  by_cases hd : DifferentiableAt ℝ f x
  · exact Or.inr hlocal.deriv_eq_zero
  · exact Or.inl hd


theorem interior_global_minimum_is_critical {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hmin : IsMinOn f (Icc a b) x) :
    IsLocalMin f x ∧ IsCriticalPointOnOpenInterval f a b x := by
  have hlocal := hmin.isLocalMin (Icc_mem_nhds hx.1 hx.2)
  refine ⟨hlocal, hx, ?_⟩
  by_cases hd : DifferentiableAt ℝ f x
  · exact Or.inr hlocal.deriv_eq_zero
  · exact Or.inl hd


theorem continuous_closed_interval_attains_extrema {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x) ∧
      (∃ x ∈ Icc a b, IsMinOn f (Icc a b) x) := by
  exact ⟨isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf,
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf⟩


theorem maximum_mem_candidatePoints {f : ℝ → ℝ} {a b x : ℝ} {C : Finset ℝ}
    (hC : ∀ y : ℝ, y ∈ C ↔ IsCriticalPointOnOpenInterval f a b y)
    (hx : x ∈ Icc a b) (hmax : IsMaxOn f (Icc a b) x) :
    x ∈ candidatePoints a b C := by
  classical
  by_cases hxa : x = a
  · simp [candidatePoints, hxa]
  by_cases hxb : x = b
  · simp [candidatePoints, hxb]
  have hxin : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hc : x ∈ C := (hC x).mpr (interior_global_maximum_is_critical hxin hmax).2
  simp [candidatePoints, hc]


theorem minimum_mem_candidatePoints {f : ℝ → ℝ} {a b x : ℝ} {C : Finset ℝ}
    (hC : ∀ y : ℝ, y ∈ C ↔ IsCriticalPointOnOpenInterval f a b y)
    (hx : x ∈ Icc a b) (hmin : IsMinOn f (Icc a b) x) :
    x ∈ candidatePoints a b C := by
  classical
  by_cases hxa : x = a
  · simp [candidatePoints, hxa]
  by_cases hxb : x = b
  · simp [candidatePoints, hxb]
  have hxin : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hc : x ∈ C := (hC x).mpr (interior_global_minimum_is_critical hxin hmin).2
  simp [candidatePoints, hc]


theorem candidatePoints_subset_interval {f : ℝ → ℝ} {a b : ℝ} {C : Finset ℝ}
    (hab : a ≤ b) (hC : ∀ y : ℝ, y ∈ C ↔ IsCriticalPointOnOpenInterval f a b y) :
    ↑(candidatePoints a b C) ⊆ Icc a b := by
  classical
  intro x hx
  simp only [candidatePoints, Finset.mem_coe, Finset.mem_insert] at hx
  rcases hx with rfl | rfl | hx
  · exact ⟨le_rfl, hab⟩
  · exact ⟨hab, le_rfl⟩
  · exact Ioo_subset_Icc_self ((hC x).mp hx).1


theorem finite_critical_candidates_extrema {f : ℝ → ℝ} {a b : ℝ} (C : Finset ℝ)
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hC : ∀ y : ℝ, y ∈ C ↔ IsCriticalPointOnOpenInterval f a b y) :
    IsGreatest (f '' Icc a b) ((candidateValues f a b C).max' (candidateValues_nonempty f a b C)) ∧
    IsLeast (f '' Icc a b) ((candidateValues f a b C).min' (candidateValues_nonempty f a b C)) ∧
    sSup (f '' Icc a b) = (candidateValues f a b C).max' (candidateValues_nonempty f a b C) ∧
    sInf (f '' Icc a b) = (candidateValues f a b C).min' (candidateValues_nonempty f a b C) := by
  classical
  obtain ⟨⟨x, hx, hmax⟩, ⟨y, hy, hmin⟩⟩ := continuous_closed_interval_attains_extrema hab hf
  have hxp := maximum_mem_candidatePoints hC hx hmax
  have hyp := minimum_mem_candidatePoints hC hy hmin
  have hsub := candidatePoints_subset_interval hab hC
  have hxval : f x ∈ candidateValues f a b C := Finset.mem_image.mpr ⟨x, hxp, rfl⟩
  have hyval : f y ∈ candidateValues f a b C := Finset.mem_image.mpr ⟨y, hyp, rfl⟩
  have hmaxeq : (candidateValues f a b C).max' (candidateValues_nonempty f a b C) = f x := by
    apply le_antisymm
    · apply Finset.max'_le
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact hmax (hsub hw)
    · exact Finset.le_max' _ _ hxval
  have hmineq : (candidateValues f a b C).min' (candidateValues_nonempty f a b C) = f y := by
    apply le_antisymm
    · exact Finset.min'_le _ _ hyval
    · apply Finset.le_min'
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact hmin (hsub hw)
  have hgreatest : IsGreatest (f '' Icc a b) (f x) := by
    refine ⟨mem_image_of_mem f hx, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact hmax hw
  have hleast : IsLeast (f '' Icc a b) (f y) := by
    refine ⟨mem_image_of_mem f hy, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact hmin hw
  rw [hmaxeq, hmineq]
  exact ⟨hgreatest, hleast,
    hgreatest.isLUB.csSup_eq ⟨f x, hgreatest.1⟩,
    hleast.isGLB.csInf_eq ⟨f y, hleast.1⟩⟩

end calculus.Chapter04.Section04CriticalCandidates
