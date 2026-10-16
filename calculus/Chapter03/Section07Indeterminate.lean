import calculus.Chapter03.Section07

/-!
§3.7 — các dạng vô định

Nguồn: dòng 3394–3415.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section07Indeterminate
open calculus.Chapter03.Section07


def SignedInfiniteLimitAlong (D : Set ℝ) (p : LimitApproach) (f : ℝ → ℝ) : Prop :=
  NontrivialDomainApproach D p ∧
    (Tendsto f (domainApproachFilter D p) atTop ∨ Tendsto f (domainApproachFilter D p) atBot)

/-- Định nghĩa 3.7.22(a): dạng vô định +∞−(+∞). -/
def PositiveInfinityDifferenceForm (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  NontrivialDomainApproach D p ∧ Tendsto f (domainApproachFilter D p) atTop ∧
    Tendsto g (domainApproachFilter D p) atTop

/-- Định nghĩa 3.7.22(b): dạng vô định 0·∞, với cả hai thứ tự thừa số. -/
def ZeroInfinityProductForm (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  (InfinitesimalAlong D p f ∧ SignedInfiniteLimitAlong D p g) ∨
    (SignedInfiniteLimitAlong D p f ∧ InfinitesimalAlong D p g)

/-- Định nghĩa 3.7.22(c): dạng vô định 0/0. -/
def ZeroOverZeroForm (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  InfinitesimalAlong D p f ∧ InfinitesimalAlong D p g

/-- Định nghĩa 3.7.22(d): dạng vô định ∞/∞, với mọi cặp dấu. -/
def InfinityOverInfinityForm (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  SignedInfiniteLimitAlong D p f ∧ SignedInfiniteLimitAlong D p g

/-- Định nghĩa 3.7.23(a): dạng vô định 0⁰. -/
def ZeroPowerZeroForm (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  InfinitesimalAlong D p f ∧ InfinitesimalAlong D p g

/-- Định nghĩa 3.7.23(b): dạng vô định 1^∞, với mũ tiến đến ±∞. -/
def OnePowerInfinityForm (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  NontrivialDomainApproach D p ∧ Tendsto f (domainApproachFilter D p) (𝓝 1) ∧
    SignedInfiniteLimitAlong D p g

/-- Định nghĩa 3.7.23(c): dạng vô định ∞⁰; giá trị thực còn phụ thuộc miền lũy thừa. -/
def InfinityPowerZeroForm (D : Set ℝ) (p : LimitApproach) (f g : ℝ → ℝ) : Prop :=
  SignedInfiniteLimitAlong D p f ∧ InfinitesimalAlong D p g

end calculus.Chapter03.Section07Indeterminate
