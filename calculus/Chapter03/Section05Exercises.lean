import calculus.Chapter03.Section05
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# §3.5 — bài tập về hàm liên tục

Nguồn: dòng 2933–2988; Định nghĩa 2.1.6.
-/
namespace calculus.Chapter03.Section05Exercises
open Set Filter Topology
open calculus.Chapter03.Section04 calculus.Chapter03.Section05
open calculus.Chapter03.Section01Properties

/-- Bài tập 1: f(x)>γ gần c nếu f liên tục tại c và f(c)>γ. -/
theorem exercise01_value_above_near_point {D : Set ℝ} {f : ℝ → ℝ} {c γ : ℝ}
    (hf : DomainContinuousAt D f c) (hγ : γ<f c) :
    ∃ δ>0, ∀ x∈Ioo (c-δ) (c+δ) ∩ D, γ<f x := by
  obtain ⟨δ,hδ,h⟩ := hf.2 ((f c-γ)/2) (by positivity)
  refine ⟨δ,hδ,fun x hx => ?_⟩
  have hd :  |x-c| <δ := abs_lt.mpr ⟨by linarith [hx.1.1],by linarith [hx.1.2]⟩
  have he := (abs_lt.mp (h x hx.2 hd)).1
  linarith


theorem exercise02_intersection {a b : ℝ} {f g : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hg : DomainContinuousOn (Icc a b) g) (ha : f a<g a) (hb : g b<f b) :
    ∃ c∈Ioo a b, f c=g c := by
  have hc := ((domainContinuousOn_iff_continuousOn hD).mp hf).sub
    ((domainContinuousOn_iff_continuousOn hD).mp hg)
  obtain ⟨c,hcD,hc0⟩ := domain_zero_between_opposite_signs hD
    ((domainContinuousOn_iff_continuousOn hD).mpr hc)
    (Or.inl ⟨sub_neg.mpr ha,sub_pos.mpr hb⟩)
  exact ⟨c,hcD,sub_eq_zero.mp hc0⟩

/-- Bài tập 3: cos có điểm bất động trong [−1,1]. -/
theorem exercise03_cosine_fixed_point : ∃ c : ℝ, Real.cos c=c := by
  obtain ⟨c,hc,he⟩ := exists_mem_Icc_isFixedPt_of_mapsTo
    Real.continuous_cos.continuousOn (by norm_num : (-1:ℝ)≤1)
    (fun x hx => ⟨Real.neg_one_le_cos x,Real.cos_le_one x⟩)
  exact ⟨c,he⟩

/-- Bài tập 4: cos(x+1)=x²−2 có hai nghiệm phân biệt. -/
theorem exercise04_two_cosine_quadratic_roots :
    ∃ c₁ c₂ : ℝ, c₁≠c₂ ∧ Real.cos (c₁+1)=c₁^2-2 ∧
      Real.cos (c₂+1)=c₂^2-2 := by
  let F : ℝ → ℝ := fun x => Real.cos (x+1)-(x^2-2)
  have hc : Continuous F := (Real.continuous_cos.comp (continuous_id.add continuous_const)).sub
    ((continuous_id.pow 2).sub continuous_const)
  have hl : F (-2)<0 := by
    have h := Real.cos_le_one ((-2:ℝ)+1)
    dsimp [F]
    nlinarith
  have hm : 0<F 0 := by
    have h := Real.neg_one_le_cos ((0:ℝ)+1)
    dsimp [F]
    nlinarith
  have hr : F 2<0 := by
    have h := Real.cos_le_one ((2:ℝ)+1)
    dsimp [F]
    nlinarith
  obtain ⟨c₁,h₁,he₁⟩ := intermediate_value_Ioo (by norm_num : (-2:ℝ)≤0)
    hc.continuousOn ⟨hl,hm⟩
  obtain ⟨c₂,h₂,he₂⟩ := intermediate_value_Ioo' (by norm_num : (0:ℝ)≤2)
    hc.continuousOn ⟨hr,hm⟩
  exact ⟨c₁,c₂,ne_of_lt (h₁.2.trans h₂.1),sub_eq_zero.mp he₁,sub_eq_zero.mp he₂⟩

/-- Bài tập 5: f(√2)=7 nếu f liên tục và f(q)=q²+5 trên ℚ. -/
theorem exercise05_rational_square_value {f : ℝ → ℝ}
    (hf : DomainContinuousOn univ f) (he : ∀ q : ℚ, f q=(q:ℝ)^2+5) :
    f (Real.sqrt 2)=7 := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr
    (fun a => (domainContinuousAt_univ f a).mp (hf a (mem_univ a)))
  have hg : Continuous (fun x : ℝ => x^2+5) := (continuous_id.pow 2).add continuous_const
  have heq : f=(fun x : ℝ => x^2+5) :=
    Rat.isDenseEmbedding_coe_real.dense.equalizer hc hg (funext he)
  rw [heq]
  change (Real.sqrt 2)^2+5=7
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num


theorem exercise06_fixed_point {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hm : MapsTo f (Icc a b) (Icc a b)) : ∃ c∈Icc a b, f c=c :=
  exists_mem_Icc_isFixedPt_of_mapsTo ((domainContinuousOn_iff_continuousOn hD).mp hf)
    (nonempty_Icc.mp hD) hm


theorem exercise06_unique_fixed_point {a b : ℝ} {f : ℝ → ℝ}
    (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (hm : MapsTo f (Icc a b) (Icc a b))
    (hcontract : ∀ x∈Icc a b, ∀ y∈Icc a b, x≠y →  |f x-f y| < |x-y| ) :
    ∃! c : Icc a b, f c=c := by
  obtain ⟨c,hc,he⟩ := exercise06_fixed_point hD hf hm
  refine ⟨⟨c,hc⟩,he,?_⟩
  intro y hy
  apply Subtype.ext
  by_contra hne
  have hh := hcontract y y.property c hc hne
  rw [hy,he] at hh
  exact (lt_irrefl _) hh


theorem exercise07_finite_average {a b : ℝ} {n : ℕ} {f : ℝ → ℝ}
    (hn : 1≤n) (hD : (Icc a b).Nonempty) (hf : DomainContinuousOn (Icc a b) f)
    (x : Fin n → ℝ) (hx : ∀ i, x i∈Icc a b) :
    ∃ c∈Icc a b, f c=(∑ i : Fin n, f (x i))/(n:ℝ) := by
  obtain ⟨xM,xm,hmax,hmin⟩ := domain_closed_interval_extrema hD hf
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlow : (n:ℝ)*f xm≤∑ i : Fin n, f (x i) := by
    calc
      (n:ℝ)*f xm = ∑ _i : Fin n, f xm := by simp
      _ ≤ ∑ i : Fin n, f (x i) := Finset.sum_le_sum (fun i hi => hmin.2 (x i) (hx i))
  have hhigh : (∑ i : Fin n, f (x i))≤(n:ℝ)*f xM := by
    calc
      (∑ i : Fin n, f (x i)) ≤ ∑ _i : Fin n, f xM :=
        Finset.sum_le_sum (fun i hi => hmax.2 (x i) (hx i))
      _ = (n:ℝ)*f xM := by simp
  exact conventional_extrema_image_range hD hf hmin hmax
    ⟨(le_div_iff₀ hnp).mpr (by simpa [mul_comm] using hlow),
     (div_le_iff₀ hnp).mpr (by simpa [mul_comm] using hhigh)⟩


theorem continuous_zero_of_opposite_endpoints {a b : ℝ} {F : ℝ → ℝ}
    (hab : a≤b) (hc : ContinuousOn F (Icc a b)) (hop : F b= -F a) :
    ∃ c∈Icc a b, F c=0 := by
  rcases le_total (F a) 0 with ha | ha
  · exact intermediate_value_Icc hab hc ⟨ha,by linarith⟩
  · exact intermediate_value_Icc' hab hc ⟨by linarith,ha⟩

/-- Bài tập 9: hàm liên tục tuần hoàn với chu kì T>0 có điểm c thỏa f(c+T/2)=f(c). -/
theorem exercise09_half_period_equal {f : ℝ → ℝ} {T : ℝ}
    (hf : DomainContinuousOn univ f) (hp : HasPositiveForwardPeriodOn univ f T) :
    ∃ c : ℝ, f (c+T/2)=f c := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr
    (fun a => (domainContinuousAt_univ f a).mp (hf a (mem_univ a)))
  let F : ℝ → ℝ := fun x => f (x+T/2)-f x
  have hF : Continuous F := (hc.comp (continuous_id.add continuous_const)).sub hc
  have hop : F (T/2)= -F 0 := by
    have hperiod := (hp.2 0 (mem_univ 0)).2
    dsimp [F]
    convert congrArg (fun v : ℝ => v-f (T/2)) hperiod using 1 <;> ring_nf
  obtain ⟨c,hcD,he⟩ := continuous_zero_of_opposite_endpoints
    (by linarith [hp.1] : (0:ℝ)≤T/2) hF.continuousOn hop
  exact ⟨c,sub_eq_zero.mp he⟩

/-- Bài tập 10: nếu f liên tục trên [0,2] và f(0)=f(2) thì có hai điểm cách nhau 1 có cùng giá trị. -/
theorem exercise10_equal_values_gap_one {f : ℝ → ℝ}
    (hf : DomainContinuousOn (Icc (0:ℝ) 2) f) (he : f 0=f 2) :
    ∃ c₁ c₂ : ℝ, c₁∈Icc (0:ℝ) 2 ∧ c₂∈Icc (0:ℝ) 2 ∧ c₁-c₂=1 ∧ f c₁=f c₂ := by
  have hc := (domainContinuousOn_iff_continuousOn (by norm_num : (Icc (0:ℝ) 2).Nonempty)).mp hf
  let F : ℝ → ℝ := fun x => f (x+1)-f x
  have hF : ContinuousOn F (Icc (0:ℝ) 1) :=
    (hc.comp (continuous_id.add continuous_const).continuousOn
      (fun x hx => by
        change x+1∈Icc (0:ℝ) 2
        exact ⟨by linarith [hx.1],by linarith [hx.2]⟩)).sub
      (hc.mono (by intro x hx; exact ⟨hx.1,by linarith [hx.2]⟩))
  have hop : F 1= -F 0 := by dsimp [F]; norm_num; linarith
  obtain ⟨c,hcD,hec⟩ := continuous_zero_of_opposite_endpoints (by norm_num) hF hop
  refine ⟨c+1,c,⟨by linarith [hcD.1],by linarith [hcD.2]⟩,
    ⟨hcD.1,by linarith [hcD.2]⟩,by ring,sub_eq_zero.mp hec⟩

/-- Bài tập 11: không có hàm liên tục thỏa f∘f=−id. -/
theorem exercise11_composition_negation_not_continuous {f : ℝ → ℝ}
    (he : ∀ x : ℝ, f (f x)= -x) : ¬DomainContinuousOn univ f := by
  intro hf
  have hc : Continuous f := continuous_iff_continuousAt.mpr
    (fun a => (domainContinuousAt_univ f a).mp (hf a (mem_univ a)))
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg f hxy
    rw [he x,he y] at h
    exact neg_injective h
  rcases hc.strictMono_of_inj hinj with hm | hm
  · have h := hm (hm (show (0:ℝ)<1 by norm_num))
    rw [he 0,he 1] at h
    norm_num at h
  · have h := hm (hm (show (0:ℝ)<1 by norm_num))
    rw [he 0,he 1] at h
    norm_num at h

/-- Bài tập 12: hàm liên tục tuần hoàn đạt giá trị lớn nhất và nhỏ nhất. -/
theorem exercise12_periodic_extrema {f : ℝ → ℝ}
    (hf : DomainContinuousOn univ f) (hp : HasPositiveForwardPeriod univ f) :
    ∃ xM xm : ℝ, AttainsMaximumOn univ f xM ∧ AttainsMinimumOn univ f xm := by
  obtain ⟨T,hT,hperiod⟩ := hp
  have hc : Continuous f := continuous_iff_continuousAt.mpr
    (fun a => (domainContinuousAt_univ f a).mp (hf a (mem_univ a)))
  have hp' : Function.Periodic f T := fun x => (hperiod x (mem_univ x)).2
  have hcompact := hp'.compact_of_continuous hT.ne' hc
  obtain ⟨M,hM,hmax⟩ := hcompact.exists_isMaxOn (range_nonempty f) continuousOn_id
  obtain ⟨m,hm,hmin⟩ := hcompact.exists_isMinOn (range_nonempty f) continuousOn_id
  obtain ⟨xM,rfl⟩ := hM
  obtain ⟨xm,rfl⟩ := hm
  exact ⟨xM,xm,⟨mem_univ _,fun x hx => hmax ⟨x,rfl⟩⟩,
    ⟨mem_univ _,fun x hx => hmin ⟨x,rfl⟩⟩⟩




/-- Bài tập 2: với a<b, hai hàm liên tục f,g trên [a,b] thỏa f(a)<g(a), f(b)>g(b) có đồ thị cắt nhau trong (a,b). -/
theorem domain_continuous_intersection {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hg : DomainContinuousOn (Icc a b) g) (ha : f a < g a) (hb : g b < f b) :
    ∃ c ∈ Ioo a b, f c = g c :=
  exercise02_intersection (nonempty_Icc.mpr hab.le) hf hg ha hb

/-- Bài tập 6(a): với a<b, mọi ánh xạ liên tục [a,b]→[a,b] có điểm bất động. -/
theorem domain_continuous_fixed_point {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hm : MapsTo f (Icc a b) (Icc a b)) : ∃ c ∈ Icc a b, f c = c :=
  exercise06_fixed_point (nonempty_Icc.mpr hab.le) hf hm

/-- Bài tập 6(b): với a<b, ánh xạ liên tục [a,b]→[a,b] thỏa |f(x)−f(y)|<|x−y| khi x≠y có duy nhất một điểm bất động. -/
theorem domain_continuous_unique_fixed_point {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (hm : MapsTo f (Icc a b) (Icc a b))
    (hcontract : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≠ y → |f x - f y| < |x - y|) :
    ∃! c : Icc a b, f c = c :=
  exercise06_unique_fixed_point (nonempty_Icc.mpr hab.le) hf hm hcontract

/-- Bài tập 7: với a<b và n≥1, trung bình cộng của n giá trị của hàm liên tục trên [a,b] cũng là một giá trị của hàm trên đoạn. -/
theorem domain_continuous_finite_average {a b : ℝ} {n : ℕ} {f : ℝ → ℝ}
    (hn : 1 ≤ n) (hab : a < b) (hf : DomainContinuousOn (Icc a b) f)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc a b) :
    ∃ c ∈ Icc a b, f c = (∑ i : Fin n, f (x i)) / (n : ℝ) :=
  exercise07_finite_average hn (nonempty_Icc.mpr hab.le) hf x hx

end calculus.Chapter03.Section05Exercises
