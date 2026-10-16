import calculus.Chapter03.Section02
import Mathlib.Topology.Algebra.Polynomial

/-!
§3.3 — phép toán trên giới hạn, thứ tự và định lí kẹp

Nguồn: dòng 2045–2138.
-/
set_option autoImplicit false
open Set Filter Topology
namespace calculus.Chapter03.Section03
open calculus.Chapter03.Section02


theorem punctured_eventually_iff {D : Set ℝ} {a : ℝ} {P : ℝ → Prop} :
    (∀ᶠ x in 𝓝[D \ {a}] a, P x) ↔
      ∃ δ > 0, ∀ x ∈ D, x ≠ a → a - δ < x → x < a + δ → P x := by
  change {x | P x} ∈ 𝓝[D \ {a}] a ↔ _
  rw [Metric.mem_nhdsWithin_iff]
  constructor
  · rintro ⟨δ, hδ, hh⟩
    refine ⟨δ, hδ, fun x hx hn hl hr ↦ hh ?_⟩
    refine ⟨?_, ⟨hx, by simpa only [mem_singleton_iff] using hn⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  · rintro ⟨δ, hδ, hh⟩
    refine ⟨δ, hδ, fun x hx ↦ ?_⟩
    have hdist := hx.1
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hdist
    exact hh x hx.2.1 (by simpa only [mem_singleton_iff] using hx.2.2)
      (by linarith [hdist.1]) (by linarith [hdist.2])


theorem domainLimit_restrict {D E : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (h : DomainLimit D f a L) (haE : AccumulationPointOf E a) (hED : E ⊆ D) :
    DomainLimit E f a L := by
  refine ⟨haE, fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, hh⟩ := h.2 ε hε
  exact ⟨δ, hδ, fun x hx ↦ hh x (hED hx)⟩


theorem domainLimit_eventually_ne_zero {D : Set ℝ} {g : ℝ → ℝ} {a M : ℝ}
    (hg : DomainLimit D g a M) (hM : M ≠ 0) :
    ∃ δ > 0, ∀ x ∈ D, x ≠ a → a - δ < x → x < a + δ → g x ≠ 0 :=
  punctured_eventually_iff.mp
    ((puncturedLimitCondition_iff_tendsto.mp hg.2).eventually (eventually_ne_nhds hM))


theorem quotient_domain_accumulation {D : Set ℝ} {g : ℝ → ℝ} {a M : ℝ}
    (hg : DomainLimit D g a M) (hM : M ≠ 0) :
    AccumulationPointOf {x ∈ D | g x ≠ 0} a := by
  obtain ⟨δ₀, hδ₀, hh⟩ := domainLimit_eventually_ne_zero hg hM
  intro δ hδ
  obtain ⟨x, hx, hn, hl, hr⟩ := hg.1 (min δ δ₀) (lt_min hδ hδ₀)
  have hxl : a - δ₀ < x := by linarith [min_le_right δ δ₀]
  have hxr : x < a + δ₀ := by linarith [min_le_right δ δ₀]
  exact ⟨x, ⟨hx, hh x hx hn hxl hxr⟩, hn,
    by linarith [min_le_left δ δ₀], by linarith [min_le_left δ δ₀]⟩

/-- Định lí 3.3.1(i): giới hạn của tổng. -/
theorem domainLimit_add {D : Set ℝ} {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : DomainLimit D f a L) (hg : DomainLimit D g a M) :
    DomainLimit D (fun x ↦ f x + g x) a (L + M) :=
  (domainLimit_iff_tendsto hf.1).mpr
    ((puncturedLimitCondition_iff_tendsto.mp hf.2).add (puncturedLimitCondition_iff_tendsto.mp hg.2))

/-- Định lí 3.3.1(ii): giới hạn của tích. -/
theorem domainLimit_mul {D : Set ℝ} {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : DomainLimit D f a L) (hg : DomainLimit D g a M) :
    DomainLimit D (fun x ↦ f x * g x) a (L * M) :=
  (domainLimit_iff_tendsto hf.1).mpr
    ((puncturedLimitCondition_iff_tendsto.mp hf.2).mul (puncturedLimitCondition_iff_tendsto.mp hg.2))

/-- Định lí 3.3.1(iii): nhân với một hằng số thực tùy ý. -/
theorem domainLimit_const_mul {D : Set ℝ} {f : ℝ → ℝ} {a L : ℝ}
    (hf : DomainLimit D f a L) (c : ℝ) : DomainLimit D (fun x ↦ c * f x) a (c * L) :=
  (domainLimit_iff_tendsto hf.1).mpr ((puncturedLimitCondition_iff_tendsto.mp hf.2).const_mul c)


theorem domainLimit_div_extension {D : Set ℝ} {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : DomainLimit D f a L) (hg : DomainLimit D g a M) (hM : M ≠ 0) :
    DomainLimit D (fun x ↦ f x / g x) a (L / M) :=
  (domainLimit_iff_tendsto hf.1).mpr
    ((puncturedLimitCondition_iff_tendsto.mp hf.2).div (puncturedLimitCondition_iff_tendsto.mp hg.2) hM)

/-- Định lí 3.3.1(iv): giới hạn thương trên miền mẫu khác 0. -/
theorem domainLimit_div_natural_domain {D : Set ℝ} {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : DomainLimit D f a L) (hg : DomainLimit D g a M) (hM : M ≠ 0) :
    DomainLimit {x ∈ D | g x ≠ 0} (fun x ↦ f x / g x) a (L / M) :=
  domainLimit_restrict (domainLimit_div_extension hf hg hM)
    (quotient_domain_accumulation hg hM) (fun _ hx ↦ hx.1)


theorem domainLimit_of_continuousAt {D : Set ℝ} {f : ℝ → ℝ} {a : ℝ}
    (ha : AccumulationPointOf D a) (hf : ContinuousAt f a) : DomainLimit D f a (f a) :=
  (domainLimit_iff_tendsto ha).mpr (hf.tendsto.mono_left nhdsWithin_le_nhds)


theorem punctured_univ_accumulation (a b : ℝ) : AccumulationPointOf (univ \ {b}) a := by
  intro δ hδ
  by_cases hb : a + δ / 2 = b
  · refine ⟨a - δ / 2, ?_, by linarith, by linarith, by linarith⟩
    simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]
    linarith
  · exact ⟨a + δ / 2, by simpa using hb, by linarith, by linarith, by linarith⟩

/-- Ví dụ 3.3.2: hàm phân thức trên miền tự nhiên. -/
theorem polynomial_ratio_limit_at_two :
    DomainLimit (univ \ {(-7 : ℝ)}) (fun x ↦ (x ^ 2 + 2 * x - 3) / (x + 7)) 2 (5 / 9) := by
  have hf : ContinuousAt (fun x : ℝ ↦ (x ^ 2 + 2 * x - 3) / (x + 7)) 2 :=
    (((continuous_id.pow 2).add (continuous_const.mul continuous_id)).sub continuous_const).continuousAt.div
      (continuous_id.add continuous_const).continuousAt (by norm_num)
  convert domainLimit_of_continuousAt (punctured_univ_accumulation 2 (-7)) hf using 1
  norm_num

/-- Nhận xét 3.3.3(i): giới hạn của đa thức thực. -/
theorem polynomial_domainLimit (P : Polynomial ℝ) (a : ℝ) :
    DomainLimit univ (fun x ↦ P.eval x) a (P.eval a) :=
  domainLimit_of_continuousAt (univ_accumulation a) P.continuousAt

/-- Nhận xét 3.3.3(ii): hàm hữu tỉ trên miền mẫu khác 0. -/
theorem rational_function_domainLimit (P Q : Polynomial ℝ) (a : ℝ) (hQ : Q.eval a ≠ 0) :
    DomainLimit {x : ℝ | Q.eval x ≠ 0} (fun x ↦ P.eval x / Q.eval x) a (P.eval a / Q.eval a) := by
  simpa only [mem_univ, true_and] using
    domainLimit_div_natural_domain (polynomial_domainLimit P a) (polynomial_domainLimit Q a) hQ

/-- Ví dụ 3.3.4: giới hạn của biểu thức sau khi rút gọn trên miền xác định. -/
theorem cancelled_ratio_eq {x : ℝ} (hx : x ≠ -1) :
    (x ^ 2 + 6 * x + 5) / (x + 1) = x + 5 := by
  have hd : x + 1 ≠ 0 := by intro hh; apply hx; linarith
  apply (div_eq_iff hd).mpr
  ring

theorem cancelled_ratio_limit_at_negative_one :
    DomainLimit (univ \ {(-1 : ℝ)}) (fun x ↦ (x ^ 2 + 6 * x + 5) / (x + 1)) (-1) 4 := by
  have hf : ContinuousAt (fun x : ℝ ↦ x + 5) (-1) :=
    (continuous_id.add continuous_const).continuousAt
  have h : DomainLimit (univ \ {(-1 : ℝ)}) (fun x ↦ x + 5) (-1) 4 := by
    convert domainLimit_of_continuousAt (univ_diff_accumulation (-1)) hf using 1
    norm_num
  exact (domainLimit_congr_punctured (fun x _ hx ↦ cancelled_ratio_eq hx)).mpr h

/-- dòng 2087: dạng 0/0 không xác định giới hạn của thương. -/
theorem indeterminate_zero_zero_different_limits :
    DomainLimit (univ \ {(0 : ℝ)}) (fun _ ↦ (0 : ℝ)) 0 0 ∧
    DomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ x) 0 0 ∧
    DomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ (0 : ℝ) / x) 0 0 ∧
    DomainLimit (univ \ {(0 : ℝ)}) (fun x ↦ x / x) 0 1 := by
  have h0 := domainLimit_restrict (constant_domainLimit 0 0) (univ_diff_accumulation 0)
    (show univ \ {(0 : ℝ)} ⊆ univ from fun _ _ ↦ mem_univ _)
  have h1 := domainLimit_restrict (constant_domainLimit 1 0) (univ_diff_accumulation 0)
    (show univ \ {(0 : ℝ)} ⊆ univ from fun _ _ ↦ mem_univ _)
  refine ⟨h0, domainLimit_restrict (identity_domainLimit 0) (univ_diff_accumulation 0)
    (fun _ _ ↦ mem_univ _), ?_, ?_⟩
  · simpa only [zero_div] using h0
  · exact (domainLimit_congr_punctured (fun x _ hx ↦ div_self hx)).mpr h1

/-- Định lí 3.3.5: lấy giới hạn hữu hạn bảo toàn bất đẳng thức không ngặt. -/
theorem domainLimit_le {D : Set ℝ} {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : DomainLimit D f a L) (hg : DomainLimit D g a M)
    (hfg : ∃ δ > 0, ∀ x ∈ D, x ≠ a → a - δ < x → x < a + δ → f x ≤ g x) : L ≤ M := by
  have : (𝓝[D \ {a}] a).NeBot := accumulationPointOf_iff_neBot.mp hf.1
  exact le_of_tendsto_of_tendsto (puncturedLimitCondition_iff_tendsto.mp hf.2)
    (puncturedLimitCondition_iff_tendsto.mp hg.2) (punctured_eventually_iff.mpr hfg)

/-- Định lí 3.3.6: hai giới hạn khác nhau xác định thứ tự gần điểm đang xét. -/
theorem domainLimit_eventually_lt {D : Set ℝ} {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : DomainLimit D f a L) (hg : DomainLimit D g a M) (hLM : L < M) :
    ∃ δ > 0, ∀ x ∈ D, x ≠ a → a - δ < x → x < a + δ → f x < g x :=
  punctured_eventually_iff.mp ((puncturedLimitCondition_iff_tendsto.mp hf.2).eventually_lt
    (puncturedLimitCondition_iff_tendsto.mp hg.2) hLM)

/-- Định lí 3.3.7: định lí kẹp trên miền có điểm tụ. -/
theorem domainLimit_squeeze {D : Set ℝ} {f g h : ℝ → ℝ} {a L : ℝ}
    (hf : DomainLimit D f a L) (hh : DomainLimit D h a L)
    (hbound : ∃ δ > 0, ∀ x ∈ D, x ≠ a → a - δ < x → x < a + δ → f x ≤ g x ∧ g x ≤ h x) :
    DomainLimit D g a L := by
  have hb := punctured_eventually_iff.mpr hbound
  exact (domainLimit_iff_tendsto hf.1).mpr
    ((puncturedLimitCondition_iff_tendsto.mp hf.2).squeeze'
      (puncturedLimitCondition_iff_tendsto.mp hh.2) (hb.mono fun _ hx ↦ hx.1) (hb.mono fun _ hx ↦ hx.2))

end calculus.Chapter03.Section03
