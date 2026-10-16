import calculus.Chapter03.Section04
import calculus.Chapter03.Section02Infinite
import calculus.Chapter03.Section01Properties
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §3.5 — các tính chất của hàm liên tục

Nguồn: dòng 2770–2923; Định nghĩa 2.1.6, Chương 2, dòng 119–133 (120,132).
-/
namespace calculus.Chapter03.Section05

open Set Filter Topology
open calculus.Chapter03.Section04 calculus.Chapter03.Section01Properties
open calculus.Chapter02.Section03

/-- Mục `C03-S05-definition-001` (a): hàm đạt giá trị lớn nhất trên miền. -/
def AttainsMaximumOn (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  a∈D ∧ ∀ x∈D, f x≤f a

/-- Mục `C03-S05-definition-001` (b): hàm đạt giá trị nhỏ nhất trên miền. -/
def AttainsMinimumOn (D : Set ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  a∈D ∧ ∀ x∈D, f a≤f x


theorem domain_continuous_closed_interval_bounded_above {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f) :
    FunctionBoundedAboveOn (Icc a b) f := by
  have hc := (domainContinuousOn_iff_continuousOn hD).mp hf
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨M,fun x hx => hM ⟨x,hx,rfl⟩⟩

/-- Mục `C03-S05-theorem-001`: hàm liên tục trên đoạn không rỗng thì bị chặn. -/
theorem domain_continuous_closed_interval_bounded {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f) :
    FunctionBoundedOn (Icc a b) f := by
  have hc := (domainContinuousOn_iff_continuousOn hD).mp hf
  obtain ⟨m,hm⟩ := isCompact_Icc.bddBelow_image hc
  obtain ⟨M,hM⟩ := domain_continuous_closed_interval_bounded_above hD hf
  exact ⟨m,M,fun x hx => ⟨hm ⟨x,hx,rfl⟩,hM x hx⟩⟩

/-- Mục `C03-S05-theorem-002`: hàm liên tục trên đoạn không rỗng đạt giá trị lớn nhất và nhỏ nhất. -/
theorem domain_closed_interval_extrema {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f) :
    ∃ xM xm : ℝ, AttainsMaximumOn (Icc a b) f xM ∧ AttainsMinimumOn (Icc a b) f xm := by
  have hc := (domainContinuousOn_iff_continuousOn hD).mp hf
  obtain ⟨xM,hxM,hM⟩ := isCompact_Icc.exists_isMaxOn hD hc
  obtain ⟨xm,hxm,hm⟩ := isCompact_Icc.exists_isMinOn hD hc
  exact ⟨xM,xm,⟨hxM,hM⟩,⟨hxm,hm⟩⟩

/-- Mục `C03-S05-lemma-001`: nếu f liên tục tại c trên D và f(c)>0 thì f dương tại các điểm của D đủ gần c. -/
theorem domain_continuous_positive_near_point {D : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hf : DomainContinuousAt D f c) (hp : 0<f c) :
    ∃ δ>0, ∀ x∈D,  |x-c| <δ → 0<f x := by
  obtain ⟨δ,hδ,h⟩ := hf.2 (f c/2) (by positivity)
  refine ⟨δ,hδ,fun x hx hdist => ?_⟩
  have hh := (abs_lt.mp (h x hx hdist)).1
  linarith

/-- Mục `C03-S05-remark-001`: nếu f liên tục tại c trên D và f(c)<0 thì f âm tại các điểm của D đủ gần c. -/
theorem domain_continuous_negative_near_point {D : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hf : DomainContinuousAt D f c) (hp : f c<0) :
    ∃ δ>0, ∀ x∈D,  |x-c| <δ → f x<0 := by
  obtain ⟨δ,hδ,h⟩ := hf.2 (-f c/2) (by linarith)
  refine ⟨δ,hδ,fun x hx hdist => ?_⟩
  have hh := (abs_lt.mp (h x hx hdist)).2
  linarith

/-- Mục `C03-S05-theorem-004`: với a≤b, hàm liên tục trên [a,b] đạt mọi giá trị nằm ngặt giữa f(a) và f(b) tại một điểm của (a,b). -/
theorem domain_intermediate_value {a b γ : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hγ : f a<γ ∧ γ<f b ∨ f b<γ ∧ γ<f a) :
    ∃ c∈Ioo a b, f c=γ := by
  have hab : a≤b := nonempty_Icc.mp hD
  have hc := (domainContinuousOn_iff_continuousOn hD).mp hf
  rcases hγ with h | h
  · exact intermediate_value_Ioo hab hc h
  · exact intermediate_value_Ioo' hab hc h


theorem domain_intermediate_value_increasing_endpoints {a b γ : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hγ : f a<γ ∧ γ<f b) : ∃ c∈Ioo a b, f c=γ :=
  domain_intermediate_value hD hf (Or.inl hγ)

/-- Mục `C03-S05-theorem-003`: với a≤b, hàm liên tục trên [a,b] có giá trị trái dấu tại hai đầu mút thì có nghiệm trong (a,b). -/
theorem domain_zero_between_opposite_signs {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hsgn : f a<0 ∧ 0<f b ∨ f b<0 ∧ 0<f a) :
    ∃ c∈Ioo a b, f c=0 := domain_intermediate_value hD hf hsgn


theorem printed_reversed_extrema_range {D : Set ℝ} {f : ℝ → ℝ} {xm xM m M γ : ℝ}
    (hmax : AttainsMaximumOn D f xm) (hmin : AttainsMinimumOn D f xM)
    (hm : m=f xm) (hM : M=f xM) (hγ : γ∈Icc m M) : ∃ c∈D, f c=γ := by
  refine ⟨xm,hmax.1,?_⟩
  have horder := hmin.2 xm hmax.1
  rw [←hm,←hM] at horder
  have hgm := hγ.1
  have hgM := hγ.2
  linarith

/-- Mục `C03-S05-corollary-001`: kết luận với γ∈[m,M], trong đó m là giá trị lớn nhất, M là giá trị nhỏ nhất theo bản in. -/
theorem source_printed_extrema_range {a b xm xM m M γ : ℝ} {f : ℝ → ℝ}
    (_hD : (Icc a b).Nonempty) (_hf : DomainContinuousOn (Icc a b) f)
    (hmax : AttainsMaximumOn (Icc a b) f xm) (hmin : AttainsMinimumOn (Icc a b) f xM)
    (hm : m=f xm) (hM : M=f xM) (hγ : γ∈Icc m M) : ∃ c∈Icc a b, f c=γ :=
  printed_reversed_extrema_range hmax hmin hm hM hγ


theorem conventional_extrema_image_range {a b : ℝ} {f : ℝ → ℝ} {xm xM γ : ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hmin : AttainsMinimumOn (Icc a b) f xm) (hmax : AttainsMaximumOn (Icc a b) f xM)
    (hγ : γ∈Icc (f xm) (f xM)) : ∃ c∈Icc a b, f c=γ := by
  have hc := (domainContinuousOn_iff_continuousOn hD).mp hf
  have hpre : IsPreconnected (Icc a b) := isPreconnected_Icc
  exact hpre.intermediate_value hmin.1 hmax.1 hc hγ

/-- Mục `C03-S05-example-001`: eˣ=−x có nghiệm trong (−1,0). -/
theorem exponential_negative_identity_root : ∃ c∈Ioo (-1:ℝ) 0, Real.exp c= -c := by
  have hc : Continuous (fun x : ℝ => Real.exp x+x) := Real.continuous_exp.add continuous_id
  have hleft : Real.exp (-1)+(-1)<0 := by
    have he : Real.exp (-1)<1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show (-1:ℝ)<0 by norm_num)
    linarith
  obtain ⟨c,hcD,hc0⟩ := domain_zero_between_opposite_signs
    (f := fun x : ℝ => Real.exp x+x) (by norm_num : (Icc (-1:ℝ) 0).Nonempty)
    (fun a ha => (domainContinuousAt_iff_within ha).mpr (hc.continuousOn a ha))
    (Or.inl ⟨hleft,by norm_num⟩)
  exact ⟨c,hcD,by linarith⟩

/-- Mục `C03-S05-example-002`: với mọi n≥1 và a>0, tồn tại căn bậc n dương của a. -/
theorem positive_nth_root_exists {a : ℝ} {n : ℕ} (ha : 0<a) (hn : 1≤n) :
    ∃ x : ℝ, 0<x ∧ x^n=a := by
  refine ⟨a^((n:ℝ)⁻¹),Real.rpow_pos_of_pos ha _,?_⟩
  exact Real.rpow_inv_natCast_pow ha.le (by omega)


def closedIntervalDomain (a b : ℝ) : IntervalDomain := ⟨Icc a b,ordConnected_Icc⟩

/-- Mục `C03-S05-theorem-005`: hàm liên tục tăng ngặt trên đoạn không rỗng [a,b] đơn ánh và có miền giá trị [f(a),f(b)]. -/
theorem function_strictly_increasing_interval_image {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hinc : FunctionStrictlyIncreasing (closedIntervalDomain a b) f) :
    InjOn f (Icc a b) ∧ f '' Icc a b=Icc (f a) (f b) := by
  have hm : StrictMonoOn f (Icc a b) := fun x hx y hy hxy => hinc x hx y hy hxy
  exact ⟨hm.injOn,((domainContinuousOn_iff_continuousOn hD).mp hf).image_Icc_of_monotoneOn
    (nonempty_Icc.mp hD) hm.monotoneOn⟩


noncomputable def strictlyIncreasingClosedIntervalMap {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hinc : FunctionStrictlyIncreasing (closedIntervalDomain a b) f) :
    Icc a b → Icc (f a) (f b) := fun x =>
  ⟨f x,by rw [←(function_strictly_increasing_interval_image hD hf hinc).2]; exact ⟨x,x.property,rfl⟩⟩

/-- Mục `C03-S05-theorem-005`: hàm liên tục tăng ngặt trên đoạn không rỗng [a,b] có hàm ngược liên tục trên [f(a),f(b)]. -/
noncomputable def strictlyIncreasingClosedIntervalHomeomorph {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hinc : FunctionStrictlyIncreasing (closedIntervalDomain a b) f) :
    Icc a b ≃ₜ Icc (f a) (f b) := by
  let F := strictlyIncreasingClosedIntervalMap hD hf hinc
  have hbij : Function.Bijective F := by
    constructor
    · intro x y he
      apply Subtype.ext
      exact (function_strictly_increasing_interval_image hD hf hinc).1 x.property y.property
        (congrArg Subtype.val he)
    · intro y
      have hy : (y:ℝ)∈f '' Icc a b := by
        rw [(function_strictly_increasing_interval_image hD hf hinc).2]
        exact y.property
      obtain ⟨x,hx,he⟩ := hy
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hF : Continuous F := ((domainContinuousOn_iff_continuousOn hD).mp hf).domRestrict.subtype_mk _
  exact (Equiv.ofBijective F hbij).toHomeomorphOfContinuousClosed hF hF.isClosedMap


theorem function_increasing_homeomorph_value {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hinc : FunctionStrictlyIncreasing (closedIntervalDomain a b) f) (x : Icc a b) :
    (strictlyIncreasingClosedIntervalHomeomorph hD hf hinc x : ℝ)=f x := rfl


theorem function_strictly_decreasing_interval_image {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hdec : FunctionStrictlyDecreasing (closedIntervalDomain a b) f) :
    InjOn f (Icc a b) ∧ f '' Icc a b=Icc (f b) (f a) := by
  have hm : StrictAntiOn f (Icc a b) := fun x hx y hy hxy => hdec x hx y hy hxy
  exact ⟨hm.injOn,((domainContinuousOn_iff_continuousOn hD).mp hf).image_Icc_of_antitoneOn
    (nonempty_Icc.mp hD) hm.antitoneOn⟩


noncomputable def strictlyDecreasingClosedIntervalMap {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hdec : FunctionStrictlyDecreasing (closedIntervalDomain a b) f) :
    Icc a b → Icc (f b) (f a) := fun x =>
  ⟨f x,by rw [←(function_strictly_decreasing_interval_image hD hf hdec).2]; exact ⟨x,x.property,rfl⟩⟩

/-- Dòng 2917: hàm liên tục giảm ngặt trên đoạn không rỗng [a,b] có hàm ngược liên tục trên [f(b),f(a)]. -/
noncomputable def strictlyDecreasingClosedIntervalHomeomorph {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hdec : FunctionStrictlyDecreasing (closedIntervalDomain a b) f) :
    Icc a b ≃ₜ Icc (f b) (f a) := by
  let F := strictlyDecreasingClosedIntervalMap hD hf hdec
  have hbij : Function.Bijective F := by
    constructor
    · intro x y he
      apply Subtype.ext
      exact (function_strictly_decreasing_interval_image hD hf hdec).1 x.property y.property
        (congrArg Subtype.val he)
    · intro y
      have hy : (y:ℝ)∈f '' Icc a b := by
        rw [(function_strictly_decreasing_interval_image hD hf hdec).2]
        exact y.property
      obtain ⟨x,hx,he⟩ := hy
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hF : Continuous F := ((domainContinuousOn_iff_continuousOn hD).mp hf).domRestrict.subtype_mk _
  exact (Equiv.ofBijective F hbij).toHomeomorphOfContinuousClosed hF hF.isClosedMap


theorem function_decreasing_homeomorph_value {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hdec : FunctionStrictlyDecreasing (closedIntervalDomain a b) f) (x : Icc a b) :
    (strictlyDecreasingClosedIntervalHomeomorph hD hf hdec x : ℝ)=f x := rfl


def unitOpenIntervalDomain : IntervalDomain := ⟨Ioo (0 : ℝ) 1,ordConnected_Ioo⟩

/-- Mục `C03-S05-remark-002`: hàm hằng tăng không ngặt nhưng không đơn ánh. -/
theorem printed_open_interval_inverse_counterexample :
    DomainContinuousOn (Ioo (0 : ℝ) 1) (fun _ => (0 : ℝ)) ∧
    FunctionIncreasing unitOpenIntervalDomain (fun _ => (0 : ℝ)) ∧
    FunctionBoundedOn (Ioo (0 : ℝ) 1) (fun _ => (0 : ℝ)) ∧
    ¬ InjOn (fun _ => (0 : ℝ)) (Ioo (0 : ℝ) 1) ∧
    (fun _ => (0 : ℝ)) '' Ioo (0 : ℝ) 1 ≠ Ioo (0 : ℝ) 0 := by
  refine ⟨fun a ha => ⟨ha,fun ε hε => ⟨1,by norm_num,fun x hx hd => by simpa using hε⟩⟩,
    fun x hx y hy hxy => le_rfl,⟨0,0,fun x hx => ⟨le_rfl,le_rfl⟩⟩,?_,?_⟩
  · intro h
    have he := h (by norm_num : (1/3 : ℝ)∈Ioo (0 : ℝ) 1)
      (by norm_num : (2/3 : ℝ)∈Ioo (0 : ℝ) 1) rfl
    norm_num at he
  · intro he
    have hz : (0 : ℝ)∈(fun _ => (0 : ℝ)) '' Ioo (0 : ℝ) 1 :=
      ⟨1/2,by norm_num,rfl⟩
    rw [he] at hz
    norm_num at hz


theorem constant_open_interval_endpoint_limits :
    calculus.Chapter03.Section02OneSided.DomainRightLimit (Ioo (0 : ℝ) 1)
      (fun _ => (0 : ℝ)) 0 0 ∧
    calculus.Chapter03.Section02OneSided.DomainLeftLimit (Ioo (0 : ℝ) 1)
      (fun _ => (0 : ℝ)) 1 0 := by
  constructor
  · constructor
    · intro δ hδ
      let t := min (δ/2) (1/2 : ℝ)
      have ht : 0<t := lt_min (by positivity) (by norm_num)
      have htδ : t<δ := (min_le_left _ _).trans_lt (by linarith)
      have ht1 : t<1 := (min_le_right _ _).trans_lt (by norm_num)
      exact ⟨t,⟨ht,ht1⟩,by simpa using ht,by simpa using htδ⟩
    · intro ε hε
      exact ⟨1,by norm_num,fun x hx hl hr => by simpa using hε⟩
  · constructor
    · intro δ hδ
      let t := min (δ/2) (1/2 : ℝ)
      have ht : 0<t := lt_min (by positivity) (by norm_num)
      have htδ : t<δ := (min_le_left _ _).trans_lt (by linarith)
      have ht1 : t<1 := (min_le_right _ _).trans_lt (by norm_num)
      exact ⟨1-t,⟨by linarith,by linarith⟩,by linarith,by linarith⟩
    · intro ε hε
      exact ⟨1,by norm_num,fun x hx hl hr => by simpa using hε⟩

/-- Mục `C03-S05-remark-002`: hàm tăng không ngặt trên (0,1), có đoạn hằng và không bị chặn trên. -/
noncomputable def unboundedPlateau (x : ℝ) : ℝ := max 0 (1/(1-x)-2)


theorem printed_unbounded_open_inverse_counterexample :
    DomainContinuousOn (Ioo (0 : ℝ) 1) unboundedPlateau ∧
    FunctionIncreasing unitOpenIntervalDomain unboundedPlateau ∧
    FunctionBoundedBelowOn (Ioo (0 : ℝ) 1) unboundedPlateau ∧
    ¬ FunctionBoundedAboveOn (Ioo (0 : ℝ) 1) unboundedPlateau ∧
    ¬ InjOn unboundedPlateau (Ioo (0 : ℝ) 1) ∧
    unboundedPlateau '' Ioo (0 : ℝ) 1 ≠ Ioi (0 : ℝ) := by
  refine ⟨?_,?_,⟨0,fun x hx => le_max_left _ _⟩,?_,?_,?_⟩
  · intro a ha
    apply (domainContinuousAt_iff_within ha).mpr
    have hp : 1-a≠0 := by linarith [ha.2]
    have hc : ContinuousAt (fun x : ℝ => max 0 (1/(1-x)-2)) a :=
      continuousAt_const.max
        ((continuousAt_const.div (continuousAt_const.sub continuousAt_id) hp).sub
          continuousAt_const)
    exact hc.continuousWithinAt
  · intro x hx y hy hxy
    apply max_le_max_left
    have hpx : 0<1-x := by linarith [hx.2]
    have hpy : 0<1-y := by linarith [hy.2]
    have hi : (1-x)⁻¹≤(1-y)⁻¹ := (inv_le_inv₀ hpx hpy).mpr (by linarith)
    simpa only [one_div] using sub_le_sub_right hi 2
  · rintro ⟨M,hM⟩
    let K := max (M+3) (3 : ℝ)
    have hK3 : 3≤K := le_max_right _ _
    have hKM : M+3≤K := le_max_left _ _
    have hK : 0<K := by linarith
    have hinv : 0<1/K := one_div_pos.mpr hK
    have hinv1 : 1/K<1 := (div_lt_one hK).mpr (by linarith)
    have hx : 1-1/K∈Ioo (0 : ℝ) 1 := ⟨by linarith,by linarith⟩
    have he : 1/(1-(1-1/K))=K := by
      field_simp [hK.ne']
      ring
    have hh := hM (1-1/K) hx
    have hvalue : K-2≤unboundedPlateau (1-1/K) := by
      unfold unboundedPlateau
      rw [he]
      exact le_max_right _ _
    linarith
  · intro h
    have he := h (by norm_num : (1/4 : ℝ)∈Ioo (0 : ℝ) 1)
      (by norm_num : (1/3 : ℝ)∈Ioo (0 : ℝ) 1)
      (by norm_num [unboundedPlateau])
    norm_num at he
  · intro he
    have hz : (0 : ℝ)∈unboundedPlateau '' Ioo (0 : ℝ) 1 :=
      ⟨1/4,by norm_num,by norm_num [unboundedPlateau]⟩
    rw [he] at hz
    exact (lt_irrefl (0 : ℝ)) hz


theorem unbounded_plateau_endpoint_limits :
    calculus.Chapter03.Section02OneSided.DomainRightLimit (Ioo (0 : ℝ) 1)
      unboundedPlateau 0 0 ∧
    calculus.Chapter03.Section02Infinite.DomainLeftTopLimit (Ioo (0 : ℝ) 1)
      unboundedPlateau 1 := by
  constructor
  · refine ⟨constant_open_interval_endpoint_limits.1.1,?_⟩
    intro ε hε
    refine ⟨1/4,by norm_num,fun x hx hl hr => ?_⟩
    have hp : 0<1-x := by linarith [hx.2]
    have hv : 1/(1-x)≤2 := (div_le_iff₀ hp).mpr (by linarith)
    have he : unboundedPlateau x=0 := by
      exact max_eq_left (by linarith)
    simpa [he] using hε
  · apply calculus.Chapter03.Section02Infinite.domainLeftTopLimit_iff.mpr
    refine ⟨constant_open_interval_endpoint_limits.2.1,?_⟩
    intro M
    let K := max (M+3) (3 : ℝ)
    have hK3 : 3≤K := le_max_right _ _
    have hKM : M+3≤K := le_max_left _ _
    have hK : 0<K := by linarith
    refine ⟨1/K,one_div_pos.mpr hK,fun x hx hl hr => ?_⟩
    have hp : 0<1-x := by linarith
    have hsmall : 1-x<1/K := by linarith
    have hmul : K*(1-x)<1 := by
      have hh := mul_lt_mul_of_pos_left hsmall hK
      have he : K*(1/K)=1 := by field_simp [hK.ne']
      simpa only [he] using hh
    have hlarge : K<1/(1-x) := (lt_div_iff₀ hp).mpr hmul
    have hbound : 1/(1-x)-2≤unboundedPlateau x := le_max_right _ _
    linarith

/-- Dòng 2907: nếu dãy không hội tụ về x₀ thì có một dãy con luôn cách x₀ ít nhất ε₀>0. -/
theorem nonconvergent_sequence_gap {u : ℕ → ℝ} {x0 : ℝ}
    (hu : ¬ConvergesTo u x0) :
    ∃ ε0>0, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, 1≤n → 1≤φ n ∧ ε0≤ |u (φ n)-x0|  := by
  classical
  unfold ConvergesTo at hu
  push Not at hu
  obtain ⟨ε0,hε0,hbad⟩ := hu
  have hfreq : ∃ᶠ n : ℕ in atTop, 1≤n ∧ ε0≤ |u n-x0|  := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨n,hn,hgap⟩ := hbad (max 1 N) (le_max_left _ _)
    exact ⟨n,(le_max_right _ _).trans hn,(le_max_left _ _).trans hn,hgap⟩
  obtain ⟨φ,hφ,hgap⟩ := extraction_of_frequently_atTop hfreq
  exact ⟨ε0,hε0,φ,hφ,fun n hn => hgap n⟩

/-- Dòng 2912: nếu vₙ→x₁ và |vₙ−x₀|≥ε₀>0 thì |x₁−x₀|≥ε₀, nên x₁≠x₀. -/
theorem convergent_sequence_gap_preserved {v : ℕ → ℝ} {x0 x1 ε0 : ℝ}
    (hv : ConvergesTo v x1) (hε0 : 0<ε0)
    (hgap : ∀ n, 1≤n → ε0≤ |v n-x0| ) : ε0≤ |x1-x0|  ∧ x1≠x0 := by
  have ht : Tendsto (fun n =>  |v n-x0| ) atTop (𝓝  |x1-x0| ) :=
    ((convergesTo_iff_tendsto.mp hv).sub_const x0).abs
  have he : ∀ᶠ n : ℕ in atTop, ε0≤ |v n-x0|  :=
    eventually_atTop.mpr ⟨1,fun n hn => hgap n hn⟩
  have hge := ge_of_tendsto ht he
  refine ⟨hge,?_⟩
  intro hsame
  simpa [hsame] using hε0.trans_le hge





theorem domain_continuous_closed_interval_bounded_above_of_lt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f) :
    FunctionBoundedAboveOn (Icc a b) f :=
  domain_continuous_closed_interval_bounded_above (nonempty_Icc.mpr hab.le) hf

/-- Mục `C03-S05-theorem-001`: trường hợp a<b. -/
theorem domain_continuous_closed_interval_bounded_of_lt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f) :
    FunctionBoundedOn (Icc a b) f :=
  domain_continuous_closed_interval_bounded (nonempty_Icc.mpr hab.le) hf

/-- Mục `C03-S05-theorem-002`: trường hợp a<b. -/
theorem domain_closed_interval_extrema_of_lt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f) :
    ∃ xM xm : ℝ, AttainsMaximumOn (Icc a b) f xM ∧ AttainsMinimumOn (Icc a b) f xm :=
  domain_closed_interval_extrema (nonempty_Icc.mpr hab.le) hf

/-- Mục `C03-S05-theorem-003`: trường hợp a<b. -/
theorem domain_zero_between_opposite_signs_of_lt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hsgn : f a < 0 ∧ 0 < f b ∨ f b < 0 ∧ 0 < f a) :
    ∃ c ∈ Ioo a b, f c = 0 :=
  domain_zero_between_opposite_signs (nonempty_Icc.mpr hab.le) hf hsgn

/-- Mục `C03-S05-theorem-004`: trường hợp a<b và f(a)<γ<f(b). -/
theorem domain_intermediate_value_increasing_endpoints_of_lt {a b γ : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hγ : f a < γ ∧ γ < f b) : ∃ c ∈ Ioo a b, f c = γ :=
  domain_intermediate_value_increasing_endpoints (nonempty_Icc.mpr hab.le) hf hγ

/-- Mục `C03-S05-corollary-001`: trường hợp a<b. -/
theorem source_printed_extrema_range_of_lt {a b xm xM m M γ : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hmax : AttainsMaximumOn (Icc a b) f xm) (hmin : AttainsMinimumOn (Icc a b) f xM)
    (hm : m = f xm) (hM : M = f xM) (hγ : γ ∈ Icc m M) : ∃ c ∈ Icc a b, f c = γ :=
  source_printed_extrema_range (nonempty_Icc.mpr hab.le) hf hmax hmin hm hM hγ

/-- Mục `C03-S05-theorem-005`: trường hợp a<b. -/
theorem function_strictly_increasing_interval_image_of_lt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hinc : FunctionStrictlyIncreasing (closedIntervalDomain a b) f) :
    InjOn f (Icc a b) ∧ f '' Icc a b = Icc (f a) (f b) :=
  function_strictly_increasing_interval_image (nonempty_Icc.mpr hab.le) hf hinc


noncomputable def strictlyIncreasingClosedIntervalHomeomorphOfLt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hinc : FunctionStrictlyIncreasing (closedIntervalDomain a b) f) :
    Icc a b ≃ₜ Icc (f a) (f b) :=
  strictlyIncreasingClosedIntervalHomeomorph (nonempty_Icc.mpr hab.le) hf hinc


theorem function_increasing_homeomorph_value_of_lt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hinc : FunctionStrictlyIncreasing (closedIntervalDomain a b) f) (x : Icc a b) :
    (strictlyIncreasingClosedIntervalHomeomorphOfLt hab hf hinc x : ℝ) = f x :=
  function_increasing_homeomorph_value (nonempty_Icc.mpr hab.le) hf hinc x

/-- Dòng 2917: tính đơn ánh và miền giá trị, trường hợp a<b. -/
theorem function_strictly_decreasing_interval_image_of_lt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hdec : FunctionStrictlyDecreasing (closedIntervalDomain a b) f) :
    InjOn f (Icc a b) ∧ f '' Icc a b = Icc (f b) (f a) :=
  function_strictly_decreasing_interval_image (nonempty_Icc.mpr hab.le) hf hdec


noncomputable def strictlyDecreasingClosedIntervalHomeomorphOfLt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hdec : FunctionStrictlyDecreasing (closedIntervalDomain a b) f) :
    Icc a b ≃ₜ Icc (f b) (f a) :=
  strictlyDecreasingClosedIntervalHomeomorph (nonempty_Icc.mpr hab.le) hf hdec


theorem function_decreasing_homeomorph_value_of_lt {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hdec : FunctionStrictlyDecreasing (closedIntervalDomain a b) f) (x : Icc a b) :
    (strictlyDecreasingClosedIntervalHomeomorphOfLt hab hf hdec x : ℝ) = f x :=
  function_decreasing_homeomorph_value (nonempty_Icc.mpr hab.le) hf hdec x

end calculus.Chapter03.Section05
