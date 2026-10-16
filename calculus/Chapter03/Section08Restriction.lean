import calculus.Chapter03.Section08

/-! §3.8 — hạn chế hàm liên tục đều. Nguồn: dòng 3875, định nghĩa tại dòng 3767; miền hàm và phép hạn chế tại dòng 18–20, 93–97. -/

set_option autoImplicit false
open Set
namespace calculus.Chapter03.Section08Restriction
open calculus.Chapter03.Section08


theorem uniformContinuityConditionOn_mono {A D : Set ℝ} {f : ℝ → ℝ}
    (hAD : A ⊆ D) (hf : UniformContinuityConditionOn D f) :
    UniformContinuityConditionOn A f := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hf ε hε
  exact ⟨δ, hδ, fun u hu v hv huv ↦ hb u (hAD hu) v (hAD hv) huv⟩

/-- Hàm liên tục đều trên D vẫn liên tục đều trên tập con không rỗng A⊆D. -/
theorem nonemptyUniformContinuousOn_mono_of_nonempty {A D : Set ℝ} {f : ℝ → ℝ}
    (hA : A.Nonempty) (hAD : A ⊆ D) (hf : NonemptyUniformContinuousOn D f) :
    NonemptyUniformContinuousOn A f :=
  ⟨hA, uniformContinuityConditionOn_mono hAD hf.2⟩


theorem nonemptyUniformContinuousOn_restriction_iff_nonempty {A D : Set ℝ} {f : ℝ → ℝ}
    (hAD : A ⊆ D) (hf : NonemptyUniformContinuousOn D f) :
    NonemptyUniformContinuousOn A f ↔ A.Nonempty :=
  ⟨fun h ↦ h.1, fun hA ↦ nonemptyUniformContinuousOn_mono_of_nonempty hA hAD hf⟩

end calculus.Chapter03.Section08Restriction
