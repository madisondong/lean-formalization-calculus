import calculus.Chapter04.Section04
import calculus.Chapter04.Section04InfiniteExtensions

/-!
# Nhận xét 4.4.5(ii): L'Hospital lặp hữu hạn lần

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1536. Mỗi cấp cần hai đạo hàm tồn tại, đạo hàm mẫu khác 0 và dạng 0/0 hoặc ∞/∞.
-/

set_option autoImplicit false
namespace calculus.Chapter04.Section04RepeatedLHospital
open Set Filter
open scoped Topology
open calculus.Chapter04.Section04
open calculus.Chapter04.Section04InfiniteExtensions


def IsLHopitalApproachFilter (F : Filter ℝ) : Prop :=
  (∃ a : ℝ, F = 𝓝[>] a) ∨ (∃ a : ℝ, F = 𝓝[<] a) ∨
    (∃ a : ℝ, F = 𝓝[≠] a) ∨ F = atTop ∨ F = atBot


def HasLHopitalIndeterminateForm (f g : ℝ → ℝ) (F : Filter ℝ) : Prop :=
  (Tendsto f F (𝓝 0) ∧ Tendsto g F (𝓝 0)) ∨
    ((Tendsto f F atTop ∨ Tendsto f F atBot) ∧
      (Tendsto g F atTop ∨ Tendsto g F atBot))


def LHopitalStepHypotheses (f f' g g' : ℝ → ℝ) (F : Filter ℝ) : Prop :=
  (∀ᶠ x in F, HasDerivAt f (f' x) x) ∧
    (∀ᶠ x in F, HasDerivAt g (g' x) x) ∧
    (∀ᶠ x in F, g' x ≠ 0) ∧ HasLHopitalIndeterminateForm f g F


theorem source_lhospital_step {f f' g g' : ℝ → ℝ} {F l : Filter ℝ}
    (hF : IsLHopitalApproachFilter F) (hlt : IsRealLimitTargetFilter l)
    (hs : LHopitalStepHypotheses f f' g g' F)
    (hl : Tendsto (fun x ↦ f' x / g' x) F l) :
    Tendsto (fun x ↦ f x / g x) F l := by
  rcases hs with ⟨hf, hg, hne, hform⟩
  rcases hF with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | rfl
  · rcases hform with ⟨hfl, hgl⟩ | ⟨_, hgl⟩
    · exact HasDerivAt.lhopital_zero_nhdsGT hf hg hne hfl hgl hl
    · exact lhopital_infinite_nhdsGT hf hg hne hgl hl hlt
  · rcases hform with ⟨hfl, hgl⟩ | ⟨_, hgl⟩
    · exact HasDerivAt.lhopital_zero_nhdsLT hf hg hne hfl hgl hl
    · exact lhopital_infinite_nhdsLT hf hg hne hgl hl hlt
  · rcases hform with ⟨hfl, hgl⟩ | ⟨hfl, hgl⟩
    · exact lhopital_zero_punctured hf hg hne hfl hgl hl
    · exact source_lhopital_infinite_punctured hf hg hne hfl hgl hl hlt
  · obtain ⟨a, ha⟩ := eventually_atTop.mp (hf.and (hg.and hne))
    have hff : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x := fun x hx ↦ (ha x hx.le).1
    have hgg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x := fun x hx ↦ (ha x hx.le).2.1
    have hnn : ∀ x ∈ Ioi a, g' x ≠ 0 := fun x hx ↦ (ha x hx.le).2.2
    rcases hform with ⟨hfl, hgl⟩ | ⟨hfl, hgl⟩
    · exact HasDerivAt.lhopital_zero_atTop_on_Ioi hff hgg hnn hfl hgl hl
    · exact source_lhopital_infinite_atTop hff hgg hnn hfl hgl hl hlt
  · obtain ⟨a, ha⟩ := eventually_atBot.mp (hf.and (hg.and hne))
    have hff : ∀ x ∈ Iio a, HasDerivAt f (f' x) x := fun x hx ↦ (ha x hx.le).1
    have hgg : ∀ x ∈ Iio a, HasDerivAt g (g' x) x := fun x hx ↦ (ha x hx.le).2.1
    have hnn : ∀ x ∈ Iio a, g' x ≠ 0 := fun x hx ↦ (ha x hx.le).2.2
    rcases hform with ⟨hfl, hgl⟩ | ⟨hfl, hgl⟩
    · exact HasDerivAt.lhopital_zero_atBot_on_Iio hff hgg hnn hfl hgl hl
    · exact source_lhopital_infinite_atBot hff hgg hnn hfl hgl hl hlt


theorem source_repeated_lhospital {n : ℕ} {f g : ℕ → ℝ → ℝ} {F l : Filter ℝ}
    (hF : IsLHopitalApproachFilter F) (hlt : IsRealLimitTargetFilter l)
    (hsteps : ∀ i < n, LHopitalStepHypotheses (f i) (f (i + 1)) (g i) (g (i + 1)) F)
    (hl : Tendsto (fun x ↦ f n x / g n x) F l) :
    Tendsto (fun x ↦ f 0 x / g 0 x) F l := by
  induction n generalizing f g with
  | zero => exact hl
  | succ n ih =>
    have hshift : ∀ i < n,
        LHopitalStepHypotheses (f (i + 1)) (f ((i + 1) + 1))
          (g (i + 1)) (g ((i + 1) + 1)) F := by
      intro i hi
      exact hsteps (i + 1) (Nat.succ_lt_succ hi)
    have hlast : Tendsto (fun x ↦ f (n + 1) x / g (n + 1) x) F l := hl
    have hfirst := ih (f := fun i ↦ f (i + 1)) (g := fun i ↦ g (i + 1)) hshift hlast
    exact source_lhospital_step hF hlt (hsteps 0 (Nat.zero_lt_succ n)) hfirst

end calculus.Chapter04.Section04RepeatedLHospital
