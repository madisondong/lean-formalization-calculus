import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# L'Hospital với mẫu tiến tới vô cùng

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1481–1535. Mẫu tiến tới `+∞` hoặc `−∞`; tử không cần có giới hạn.
-/
namespace calculus.Chapter04.Section04Infinite
open Set Filter
open scoped Topology


theorem constant_div_infinite {g : ℝ → ℝ} {l : Filter ℝ}
    (hg : Tendsto g l atTop ∨ Tendsto g l atBot) (C : ℝ) :
    Tendsto (fun x ↦ C / g x) l (𝓝 0) := by
  rcases hg with hg | hg
  · exact tendsto_const_nhds.div_atTop hg
  · exact tendsto_const_nhds.div_atBot hg


theorem eventually_ne_of_infinite {g : ℝ → ℝ} {l : Filter ℝ}
    (hg : Tendsto g l atTop ∨ Tendsto g l atBot) (C : ℝ) :
    ∀ᶠ x in l, g x ≠ C := by
  rcases hg with hg | hg
  · exact hg.eventually_ne_atTop C
  · exact hg.eventually_ne_atBot C


theorem lhopital_infinite_right_finite {f g : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (hgne : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (hgl : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot)
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[>] a) (𝓝 L)) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hev : ∀ᶠ x in 𝓝[>] a, x ∈ Ioo a b ∧ |deriv f x / deriv g x - L| < δ := by
    filter_upwards [Ioo_mem_nhdsGT hab, (Metric.tendsto_nhds.mp hl) δ hδ] with x hx hq
    exact ⟨hx, by simpa only [Real.dist_eq] using hq⟩
  obtain ⟨d, had, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  change a < d at had
  let α : ℝ := (a + d) / 2
  have hα : α ∈ Ioo a d := by dsimp [α]; constructor <;> linarith
  have hαb : α ∈ Ioo a b := (hd hα).1
  have hconst := constant_div_infinite hgl (f α - L * g α)
  have hbase := constant_div_infinite hgl (g α)
  have hevent : ∀ᶠ x in 𝓝[>] a, |f x / g x - L| < ε := by
    filter_upwards [Ioo_mem_nhdsGT hα.1,
      (Metric.tendsto_nhds.mp hconst) (ε / 2) (by positivity),
      (Metric.tendsto_nhds.mp hbase) 1 (by norm_num),
      eventually_ne_of_infinite hgl 0, eventually_ne_of_infinite hgl (g α)]
      with x hx hsmall hbase hxg hxga
    have hxsrc : x ∈ Ioo a b := ⟨hx.1, hx.2.trans hαb.2⟩
    have hsub : Icc x α ⊆ Ioo a b := fun y hy ↦
      ⟨hxsrc.1.trans_le hy.1, hy.2.trans_lt hαb.2⟩
    obtain ⟨c, hc, he⟩ := exists_ratio_deriv_eq_ratio_slope f hx.2
      (hf.continuousOn.mono hsub) (hf.mono (Ioo_subset_Icc_self.trans hsub))
      g (hg.continuousOn.mono hsub) (hg.mono (Ioo_subset_Icc_self.trans hsub))
    have hcd : c ∈ Ioo a d := ⟨hx.1.trans hc.1, hc.2.trans hα.2⟩
    have hq : |(f x - f α) / (g x - g α) - L| < δ := by
      have heq : (f x - f α) / (g x - g α) = deriv f c / deriv g c := by
        apply (div_eq_div_iff (sub_ne_zero.mpr hxga) (hgne c (hd hcd).1)).mpr
        nlinarith [he]
      rw [heq]
      exact (hd hcd).2
    have hb : |1 - g α / g x| < 2 := by
      have hbase' : |g α / g x| < 1 := by simpa only [Real.dist_eq, sub_zero] using hbase
      have hh : |1 - g α / g x| ≤ 1 + |g α / g x| := by
        simpa only [sub_eq_add_neg, abs_one, abs_neg] using
          abs_add_le (1 : ℝ) (-(g α / g x))
      linarith
    have heq : f x / g x - L =
        ((f x - f α) / (g x - g α) - L) * (1 - g α / g x) +
          (f α - L * g α) / g x := by
      field_simp [hxg, sub_ne_zero.mpr hxga]
      ring
    have hprod : |(f x - f α) / (g x - g α) - L| * |1 - g α / g x| < δ * 2 :=
      (mul_le_mul_of_nonneg_right hq.le (abs_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left hb hδ)
    have hsmall' : |(f α - L * g α) / g x| < ε / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hsmall
    rw [heq]
    calc
      _ ≤ |((f x - f α) / (g x - g α) - L) * (1 - g α / g x)| +
          |(f α - L * g α) / g x| := abs_add_le _ _
      _ = |(f x - f α) / (g x - g α) - L| * |1 - g α / g x| +
          |(f α - L * g α) / g x| := by rw [abs_mul]
      _ < δ * 2 + ε / 2 := add_lt_add hprod hsmall'
      _ = ε := by dsimp [δ]; ring
  simpa only [Real.dist_eq] using hevent


theorem lhopital_infinite_right_atTop {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (hgne : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (hgl : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot)
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[>] a) atTop) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) atTop := by
  apply tendsto_atTop.2
  intro M
  let K : ℝ := 2 * (|M| + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hev : ∀ᶠ x in 𝓝[>] a, x ∈ Ioo a b ∧ K < deriv f x / deriv g x := by
    filter_upwards [Ioo_mem_nhdsGT hab, hl.eventually_gt_atTop K] with x hx hq
    exact ⟨hx, hq⟩
  obtain ⟨d, had, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  change a < d at had
  let α : ℝ := (a + d) / 2
  have hα : α ∈ Ioo a d := by dsimp [α]; constructor <;> linarith
  have hαb : α ∈ Ioo a b := (hd hα).1
  have hconst := constant_div_infinite hgl (f α)
  have hbase := constant_div_infinite hgl (g α)
  filter_upwards [Ioo_mem_nhdsGT hα.1,
    (Metric.tendsto_nhds.mp hconst) 1 (by norm_num),
    (Metric.tendsto_nhds.mp hbase) (1 / 2) (by norm_num),
    eventually_ne_of_infinite hgl 0, eventually_ne_of_infinite hgl (g α)]
    with x hx hsmall hbase hxg hxga
  have hxsrc : x ∈ Ioo a b := ⟨hx.1, hx.2.trans hαb.2⟩
  have hsub : Icc x α ⊆ Ioo a b := fun y hy ↦
    ⟨hxsrc.1.trans_le hy.1, hy.2.trans_lt hαb.2⟩
  obtain ⟨c, hc, he⟩ := exists_ratio_deriv_eq_ratio_slope f hx.2
    (hf.continuousOn.mono hsub) (hf.mono (Ioo_subset_Icc_self.trans hsub))
    g (hg.continuousOn.mono hsub) (hg.mono (Ioo_subset_Icc_self.trans hsub))
  have hcd : c ∈ Ioo a d := ⟨hx.1.trans hc.1, hc.2.trans hα.2⟩
  have heq : (f x - f α) / (g x - g α) = deriv f c / deriv g c := by
    apply (div_eq_div_iff (sub_ne_zero.mpr hxga) (hgne c (hd hcd).1)).mpr
    nlinarith [he]
  have hq : K < (f x - f α) / (g x - g α) := by
    rw [heq]
    exact (hd hcd).2
  have hb : (1 / 2 : ℝ) < 1 - g α / g x := by
    have hh : |g α / g x| < (1 / 2 : ℝ) := by
      simpa only [Real.dist_eq, sub_zero] using hbase
    have hh' := (abs_lt.mp hh).2
    linarith
  have hs : -1 < f α / g x := by
    have hh : |f α / g x| < (1 : ℝ) := by
      simpa only [Real.dist_eq, sub_zero] using hsmall
    exact (abs_lt.mp hh).1
  have hformula : f x / g x =
      ((f x - f α) / (g x - g α)) * (1 - g α / g x) + f α / g x := by
    field_simp [hxg, sub_ne_zero.mpr hxga]
    ring
  have hp : K * (1 / 2) <
      ((f x - f α) / (g x - g α)) * (1 - g α / g x) := by
    exact (mul_lt_mul_of_pos_right hq (by norm_num : (0 : ℝ) < 1 / 2)).trans
      (mul_lt_mul_of_pos_left hb (hK.trans hq))
  rw [hformula]
  dsimp [K] at hp
  linarith [le_abs_self M]


theorem lhopital_infinite_right_atBot {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (hgne : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (hgl : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot)
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[>] a) atBot) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) atBot := by
  have hneg : Tendsto (fun x ↦ deriv (fun y ↦ -f y) x / deriv g x)
      (𝓝[>] a) atTop := by
    apply (tendsto_neg_atBot_atTop.comp hl).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    rw [((hf x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.fun_neg.deriv]
    simp only [Function.comp_apply, neg_div]
  have h := lhopital_infinite_right_atTop hab hf.neg hg hgne hgl hneg
  simpa only [Function.comp_def, Pi.neg_apply, neg_div, neg_neg] using
    tendsto_neg_atTop_atBot.comp h


theorem source_lhopital_infinite_right_finite {f g : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (hgne : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (_hfl : Tendsto f (𝓝[>] a) atTop ∨ Tendsto f (𝓝[>] a) atBot)
    (hgl : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot)
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[>] a) (𝓝 L)) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) (𝓝 L) :=
  lhopital_infinite_right_finite hab hf hg hgne hgl hl


theorem source_lhopital_infinite_right_atTop {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (hgne : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (_hfl : Tendsto f (𝓝[>] a) atTop ∨ Tendsto f (𝓝[>] a) atBot)
    (hgl : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot)
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[>] a) atTop) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) atTop :=
  lhopital_infinite_right_atTop hab hf hg hgne hgl hl


theorem source_lhopital_infinite_right_atBot {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (hgne : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (_hfl : Tendsto f (𝓝[>] a) atTop ∨ Tendsto f (𝓝[>] a) atBot)
    (hgl : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot)
    (hl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[>] a) atBot) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) atBot :=
  lhopital_infinite_right_atBot hab hf hg hgne hgl hl

end calculus.Chapter04.Section04Infinite
