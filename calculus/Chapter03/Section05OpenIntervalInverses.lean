import calculus.Chapter03.Section05
import calculus.Chapter03.Section03Exercises
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue

/-! Mục `C03-S05-remark-002`: hàm ngược của hàm liên tục tăng ngặt trên (a,b), với a<b. -/
namespace calculus.Chapter03.Section05OpenIntervalInverses

set_option autoImplicit false

open Set Filter Topology
open calculus.Chapter03.Section01Properties
open calculus.Chapter03.Section02OneSided
open calculus.Chapter03.Section02Infinite
open calculus.Chapter03.Section03Exercises
open calculus.Chapter03.Section04


def openIntervalDomain (a b : ℝ) : IntervalDomain :=
  ⟨Ioo a b, ordConnected_Ioo⟩


theorem open_strictMono_value_above_inf {a b x : ℝ} {f : ℝ → ℝ}
    (hinc : StrictMonoOn f (Ioo a b)) (hlo : BddBelow (f '' Ioo a b))
    (hx : x ∈ Ioo a b) : sInf (f '' Ioo a b) < f x := by
  obtain ⟨l, hal, hlx⟩ := exists_between hx.1
  have hl : l ∈ Ioo a b := ⟨hal, hlx.trans hx.2⟩
  exact csInf_lt_of_lt hlo ⟨l, hl, rfl⟩ (hinc hl hx hlx)


theorem open_strictMono_value_below_sup {a b x : ℝ} {f : ℝ → ℝ}
    (hinc : StrictMonoOn f (Ioo a b)) (hhi : BddAbove (f '' Ioo a b))
    (hx : x ∈ Ioo a b) : f x < sSup (f '' Ioo a b) := by
  obtain ⟨r, hxr, hrb⟩ := exists_between hx.2
  have hr : r ∈ Ioo a b := ⟨hx.1.trans hxr, hrb⟩
  exact lt_csSup_of_lt hhi ⟨r, hr, rfl⟩ (hinc hx hr hxr)


theorem strictMono_open_bounded_image {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Ioo a b))
    (hinc : StrictMonoOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b)) :
    f '' Ioo a b = Ioo (sInf (f '' Ioo a b)) (sSup (f '' Ioo a b)) := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨open_strictMono_value_above_inf hinc hlo hx,
      open_strictMono_value_below_sup hinc hhi hx⟩
  · exact ((isConnected_Ioo hab).image f hcont).Ioo_csInf_csSup_subset hlo hhi


theorem strictMono_open_upper_unbounded_image {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ioo a b)) (hinc : StrictMonoOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : ¬ BddAbove (f '' Ioo a b)) :
    f '' Ioo a b = Ioi (sInf (f '' Ioo a b)) := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact open_strictMono_value_above_inf hinc hlo hx
  · exact (isPreconnected_Ioo.image f hcont).Ioi_csInf_subset hlo hhi


noncomputable def boundedOpenIntervalHomeomorph {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Ioo a b))
    (hinc : StrictMonoOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b)) :
    Ioo a b ≃ₜ Ioo (sInf (f '' Ioo a b)) (sSup (f '' Ioo a b)) :=
  ((hinc.orderIso f (Ioo a b)).trans
    (OrderIso.setCongr _ _ (strictMono_open_bounded_image hab hcont hinc hlo hhi))).toHomeomorph


theorem boundedOpenIntervalHomeomorph_value {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Ioo a b))
    (hinc : StrictMonoOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b))
    (x : Ioo a b) :
    (boundedOpenIntervalHomeomorph hab hcont hinc hlo hhi x : ℝ) = f x := by
  rfl


noncomputable def upperUnboundedOpenIntervalHomeomorph {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ioo a b)) (hinc : StrictMonoOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : ¬ BddAbove (f '' Ioo a b)) :
    Ioo a b ≃ₜ Ioi (sInf (f '' Ioo a b)) :=
  ((hinc.orderIso f (Ioo a b)).trans
    (OrderIso.setCongr _ _ (strictMono_open_upper_unbounded_image hcont hinc hlo hhi))).toHomeomorph


theorem upperUnboundedOpenIntervalHomeomorph_value {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ioo a b)) (hinc : StrictMonoOn f (Ioo a b))
    (hlo : BddBelow (f '' Ioo a b)) (hhi : ¬ BddAbove (f '' Ioo a b))
    (x : Ioo a b) :
    (upperUnboundedOpenIntervalHomeomorph hcont hinc hlo hhi x : ℝ) = f x := by
  rfl

/-- Nếu hàm bị chặn trên và dưới thì miền giá trị là (c,d), với c,d hữu hạn và c<d; hàm ngược liên tục. -/
theorem corrected_bounded_open_interval_inverse {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Ioo a b) f)
    (hinc : FunctionStrictlyIncreasing (openIntervalDomain a b) f)
    (hlo : BddBelow (f '' Ioo a b)) (hhi : BddAbove (f '' Ioo a b)) :
    ∃ c d : ℝ, c < d ∧ DomainRightLimit (Ioo a b) f a c ∧
      DomainLeftLimit (Ioo a b) f b d ∧ f '' Ioo a b = Ioo c d ∧
      ∃ e : Ioo a b ≃ₜ Ioo c d,
        (∀ x : Ioo a b, (e x : ℝ) = f x) ∧ Continuous e.symm ∧
        (∀ y : Ioo c d, f (e.symm y : ℝ) = (y : ℝ)) := by
  have hm : StrictMonoOn f (Ioo a b) := hinc
  have hc : ContinuousOn f (Ioo a b) :=
    (domainContinuousOn_iff_continuousOn (nonempty_Ioo.mpr hab)).mp hf
  have ha := (monotone_Ioo_lower_endpoint hab hm.monotoneOn).1 hlo
  have hb := (monotone_Ioo_upper_endpoint hab hm.monotoneOn).1 hhi
  obtain ⟨x, hx⟩ := nonempty_Ioo.mpr hab
  have hcd : sInf (f '' Ioo a b) < sSup (f '' Ioo a b) :=
    (open_strictMono_value_above_inf hm hlo hx).trans
      (open_strictMono_value_below_sup hm hhi hx)
  let e := boundedOpenIntervalHomeomorph hab hc hm hlo hhi
  have he : ∀ x : Ioo a b, (e x : ℝ) = f x :=
    boundedOpenIntervalHomeomorph_value hab hc hm hlo hhi
  refine ⟨sInf (f '' Ioo a b), sSup (f '' Ioo a b), hcd, ha, hb,
    strictMono_open_bounded_image hab hc hm hlo hhi, e, he, e.symm.continuous, ?_⟩
  intro y
  calc
    f (e.symm y : ℝ) = (e (e.symm y) : ℝ) := (he (e.symm y)).symm
    _ = (y : ℝ) := congrArg Subtype.val (e.apply_symm_apply y)

/-- Nếu hàm bị chặn dưới nhưng không bị chặn trên thì miền giá trị là (c,+∞), với c hữu hạn, và hàm ngược liên tục. -/
theorem corrected_upper_unbounded_open_interval_inverse {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Ioo a b) f)
    (hinc : FunctionStrictlyIncreasing (openIntervalDomain a b) f)
    (hlo : BddBelow (f '' Ioo a b)) (hhi : ¬ BddAbove (f '' Ioo a b)) :
    ∃ c : ℝ, DomainRightLimit (Ioo a b) f a c ∧
      DomainLeftTopLimit (Ioo a b) f b ∧ f '' Ioo a b = Ioi c ∧
      ∃ e : Ioo a b ≃ₜ Ioi c,
        (∀ x : Ioo a b, (e x : ℝ) = f x) ∧ Continuous e.symm ∧
        (∀ y : Ioi c, f (e.symm y : ℝ) = (y : ℝ)) := by
  have hm : StrictMonoOn f (Ioo a b) := hinc
  have hc : ContinuousOn f (Ioo a b) :=
    (domainContinuousOn_iff_continuousOn (nonempty_Ioo.mpr hab)).mp hf
  have ha := (monotone_Ioo_lower_endpoint hab hm.monotoneOn).1 hlo
  have hb := (monotone_Ioo_upper_endpoint hab hm.monotoneOn).2 hhi
  let e := upperUnboundedOpenIntervalHomeomorph hc hm hlo hhi
  have he : ∀ x : Ioo a b, (e x : ℝ) = f x :=
    upperUnboundedOpenIntervalHomeomorph_value hc hm hlo hhi
  refine ⟨sInf (f '' Ioo a b), ha, hb,
    strictMono_open_upper_unbounded_image hc hm hlo hhi, e, he, e.symm.continuous, ?_⟩
  intro y
  calc
    f (e.symm y : ℝ) = (e (e.symm y) : ℝ) := (he (e.symm y)).symm
    _ = (y : ℝ) := congrArg Subtype.val (e.apply_symm_apply y)

end calculus.Chapter03.Section05OpenIntervalInverses
