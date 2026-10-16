import calculus.Chapter04.Section04Infinite

/-!
# Các phía và đầu vô cùng của L'Hospital dạng ∞/∞

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 1530–1539, Nhận xét 4.4.5(i).
-/
namespace calculus.Chapter04.Section04InfiniteExtensions
open Set Filter calculus.Chapter04.Section04Infinite
open scoped Topology


def IsRealLimitTargetFilter (l : Filter ℝ) : Prop :=
  (∃ L : ℝ, l = 𝓝 L) ∨ l = atTop ∨ l = atBot


theorem lhopital_infinite_right_hasDerivAt {f f' g g' : ℝ → ℝ}
    {a b : ℝ} {l : Filter ℝ} (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hne : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hgl : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) (𝓝[>] a) l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) l := by
  have hdf : DifferentiableOn ℝ f (Ioo a b) :=
    fun x hx ↦ (hf x hx).differentiableAt.differentiableWithinAt
  have hdg : DifferentiableOn ℝ g (Ioo a b) :=
    fun x hx ↦ (hg x hx).differentiableAt.differentiableWithinAt
  have hdne : ∀ x ∈ Ioo a b, deriv g x ≠ 0 := by
    intro x hx
    rw [(hg x hx).deriv]
    exact hne x hx
  have hdl : Tendsto (fun x ↦ deriv f x / deriv g x) (𝓝[>] a) l := by
    apply hl.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    rw [(hf x hx).deriv, (hg x hx).deriv]
  rcases hlt with ⟨L, rfl⟩ | rfl | rfl
  · exact lhopital_infinite_right_finite hab hdf hdg hdne hgl hdl
  · exact lhopital_infinite_right_atTop hab hdf hdg hdne hgl hdl
  · exact lhopital_infinite_right_atBot hab hdf hdg hdne hgl hdl


theorem lhopital_infinite_left_hasDerivAt {f f' g g' : ℝ → ℝ}
    {a b : ℝ} {l : Filter ℝ} (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hne : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hgl : Tendsto g (𝓝[<] b) atTop ∨ Tendsto g (𝓝[<] b) atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) (𝓝[<] b) l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[<] b) l := by
  have hs (x : ℝ) (hx : x ∈ Ioo (-b) (-a)) : -x ∈ Ioo a b := by
    constructor <;> linarith [hx.1, hx.2]
  have hff : ∀ x ∈ Ioo (-b) (-a), HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x :=
    fun x hx ↦ (hf (-x) (hs x hx)).comp x (hasDerivAt_neg x)
  have hgg : ∀ x ∈ Ioo (-b) (-a), HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x :=
    fun x hx ↦ (hg (-x) (hs x hx)).comp x (hasDerivAt_neg x)
  have hgin : Tendsto (g ∘ Neg.neg) (𝓝[>] (-b)) atTop ∨
      Tendsto (g ∘ Neg.neg) (𝓝[>] (-b)) atBot :=
    hgl.elim (fun h ↦ Or.inl (h.comp tendsto_neg_nhdsGT_neg))
      (fun h ↦ Or.inr (h.comp tendsto_neg_nhdsGT_neg))
  have hq : Tendsto (fun x ↦ (f' (-x) * -1) / (g' (-x) * -1))
      (𝓝[>] (-b)) l := by
    simpa only [Function.comp_def, mul_neg, mul_one, neg_div_neg_eq] using
      hl.comp tendsto_neg_nhdsGT_neg
  have h := lhopital_infinite_right_hasDerivAt (neg_lt_neg hab) hff hgg
    (fun x hx ↦ mul_ne_zero (hne (-x) (hs x hx)) (by norm_num)) hgin hq hlt
  simpa only [Function.comp_def, neg_neg] using h.comp tendsto_neg_nhdsLT


theorem lhopital_infinite_atTop_hasDerivAt {f f' g g' : ℝ → ℝ}
    {a : ℝ} {l : Filter ℝ}
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hne : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hgl : Tendsto g atTop atTop ∨ Tendsto g atTop atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) atTop l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) atTop l := by
  let A : ℝ := 1 + max a 0
  have haA : a < A := (le_max_left a 0).trans_lt (lt_one_add _)
  have hA : 0 < A := (le_max_right a 0).trans_lt (lt_one_add _)
  have hnz (x : ℝ) (hx : x ∈ Ioo 0 A⁻¹) : x ≠ 0 := hx.1.ne'
  have hs (x : ℝ) (hx : x ∈ Ioo 0 A⁻¹) : x⁻¹ ∈ Ioi a :=
    haA.trans ((lt_inv_comm₀ hA hx.1).mpr hx.2)
  have hff : ∀ x ∈ Ioo 0 A⁻¹,
      HasDerivAt (f ∘ Inv.inv) (f' x⁻¹ * -(x ^ 2)⁻¹) x :=
    fun x hx ↦ (hf x⁻¹ (hs x hx)).comp x (hasDerivAt_inv (hnz x hx))
  have hgg : ∀ x ∈ Ioo 0 A⁻¹,
      HasDerivAt (g ∘ Inv.inv) (g' x⁻¹ * -(x ^ 2)⁻¹) x :=
    fun x hx ↦ (hg x⁻¹ (hs x hx)).comp x (hasDerivAt_inv (hnz x hx))
  have hgin : Tendsto (g ∘ Inv.inv) (𝓝[>] 0) atTop ∨
      Tendsto (g ∘ Inv.inv) (𝓝[>] 0) atBot :=
    hgl.elim (fun h ↦ Or.inl (h.comp tendsto_inv_nhdsGT_zero))
      (fun h ↦ Or.inr (h.comp tendsto_inv_nhdsGT_zero))
  have hq : Tendsto (fun x ↦ (f' x⁻¹ * -(x ^ 2)⁻¹) / (g' x⁻¹ * -(x ^ 2)⁻¹))
      (𝓝[>] (0 : ℝ)) l := by
    apply (hl.comp tendsto_inv_nhdsGT_zero).congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    simp only [Function.comp_def]
    rw [mul_div_mul_right _ _ (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hx.ne')))]
  have h := lhopital_infinite_right_hasDerivAt (inv_pos.mpr hA) hff hgg
    (fun x hx ↦ mul_ne_zero (hne x⁻¹ (hs x hx))
      (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (hnz x hx))))) hgin hq hlt
  simpa only [Function.comp_def, inv_inv] using h.comp tendsto_inv_atTop_nhdsGT_zero


theorem lhopital_infinite_atBot_hasDerivAt {f f' g g' : ℝ → ℝ}
    {a : ℝ} {l : Filter ℝ}
    (hf : ∀ x ∈ Iio a, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Iio a, HasDerivAt g (g' x) x)
    (hne : ∀ x ∈ Iio a, g' x ≠ 0)
    (hgl : Tendsto g atBot atTop ∨ Tendsto g atBot atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) atBot l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) atBot l := by
  have hs (x : ℝ) (hx : x ∈ Ioi (-a)) : -x ∈ Iio a := by
    change -a < x at hx
    change -x < a
    linarith
  have hff : ∀ x ∈ Ioi (-a), HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x :=
    fun x hx ↦ (hf (-x) (hs x hx)).comp x (hasDerivAt_neg x)
  have hgg : ∀ x ∈ Ioi (-a), HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x :=
    fun x hx ↦ (hg (-x) (hs x hx)).comp x (hasDerivAt_neg x)
  have hgin : Tendsto (g ∘ Neg.neg) atTop atTop ∨ Tendsto (g ∘ Neg.neg) atTop atBot :=
    hgl.elim (fun h ↦ Or.inl (h.comp tendsto_neg_atTop_atBot))
      (fun h ↦ Or.inr (h.comp tendsto_neg_atTop_atBot))
  have hq : Tendsto (fun x ↦ (f' (-x) * -1) / (g' (-x) * -1)) atTop l := by
    simpa only [Function.comp_def, mul_neg, mul_one, neg_div_neg_eq] using
      hl.comp tendsto_neg_atTop_atBot
  have h := lhopital_infinite_atTop_hasDerivAt hff hgg
    (fun x hx ↦ mul_ne_zero (hne (-x) (hs x hx)) (by norm_num)) hgin hq hlt
  simpa only [Function.comp_def, neg_neg] using h.comp tendsto_neg_atBot_atTop


theorem lhopital_infinite_nhdsGT {f f' g g' : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hf : ∀ᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x)
    (hne : ∀ᶠ x in 𝓝[>] a, g' x ≠ 0)
    (hgl : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) (𝓝[>] a) l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[>] a) l := by
  obtain ⟨b, hab, hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hf.and (hg.and hne))
  exact lhopital_infinite_right_hasDerivAt hab (fun x hx ↦ (hs hx).1)
    (fun x hx ↦ (hs hx).2.1) (fun x hx ↦ (hs hx).2.2) hgl hl hlt


theorem lhopital_infinite_nhdsLT {f f' g g' : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hf : ∀ᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in 𝓝[<] a, HasDerivAt g (g' x) x)
    (hne : ∀ᶠ x in 𝓝[<] a, g' x ≠ 0)
    (hgl : Tendsto g (𝓝[<] a) atTop ∨ Tendsto g (𝓝[<] a) atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) (𝓝[<] a) l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[<] a) l := by
  obtain ⟨b, hba, hs⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (hf.and (hg.and hne))
  exact lhopital_infinite_left_hasDerivAt hba (fun x hx ↦ (hs hx).1)
    (fun x hx ↦ (hs hx).2.1) (fun x hx ↦ (hs hx).2.2) hgl hl hlt


theorem source_lhopital_infinite_punctured {f f' g g' : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hf : ∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x)
    (hne : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (_hfl : Tendsto f (𝓝[≠] a) atTop ∨ Tendsto f (𝓝[≠] a) atBot)
    (hgl : Tendsto g (𝓝[≠] a) atTop ∨ Tendsto g (𝓝[≠] a) atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) (𝓝[≠] a) l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[≠] a) l := by
  have hgL : Tendsto g (𝓝[<] a) atTop ∨ Tendsto g (𝓝[<] a) atBot :=
    hgl.elim (fun h ↦ Or.inl (h.mono_left (nhdsLT_le_nhdsNE a)))
      (fun h ↦ Or.inr (h.mono_left (nhdsLT_le_nhdsNE a)))
  have hgR : Tendsto g (𝓝[>] a) atTop ∨ Tendsto g (𝓝[>] a) atBot :=
    hgl.elim (fun h ↦ Or.inl (h.mono_left (nhdsGT_le_nhdsNE a)))
      (fun h ↦ Or.inr (h.mono_left (nhdsGT_le_nhdsNE a)))
  simp only [← Iio_union_Ioi, nhdsWithin_union, tendsto_sup, eventually_sup] at hf hg hne hl ⊢
  exact ⟨lhopital_infinite_nhdsLT hf.1 hg.1 hne.1 hgL hl.1 hlt,
    lhopital_infinite_nhdsGT hf.2 hg.2 hne.2 hgR hl.2 hlt⟩

/-- Nhận xét 4.4.5(i): L’Hospital dạng ∞/∞ khi tiến từ bên trái. -/
theorem source_lhopital_infinite_left {f f' g g' : ℝ → ℝ}
    {a b : ℝ} {l : Filter ℝ} (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hne : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (_hfl : Tendsto f (𝓝[<] b) atTop ∨ Tendsto f (𝓝[<] b) atBot)
    (hgl : Tendsto g (𝓝[<] b) atTop ∨ Tendsto g (𝓝[<] b) atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) (𝓝[<] b) l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) (𝓝[<] b) l :=
  lhopital_infinite_left_hasDerivAt hab hf hg hne hgl hl hlt

/-- Nhận xét 4.4.5(i): L’Hospital dạng ∞/∞ tại `+∞`. -/
theorem source_lhopital_infinite_atTop {f f' g g' : ℝ → ℝ}
    {a : ℝ} {l : Filter ℝ}
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hne : ∀ x ∈ Ioi a, g' x ≠ 0)
    (_hfl : Tendsto f atTop atTop ∨ Tendsto f atTop atBot)
    (hgl : Tendsto g atTop atTop ∨ Tendsto g atTop atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) atTop l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) atTop l :=
  lhopital_infinite_atTop_hasDerivAt hf hg hne hgl hl hlt

/-- Nhận xét 4.4.5(i): L’Hospital dạng ∞/∞ tại `−∞`. -/
theorem source_lhopital_infinite_atBot {f f' g g' : ℝ → ℝ}
    {a : ℝ} {l : Filter ℝ}
    (hf : ∀ x ∈ Iio a, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Iio a, HasDerivAt g (g' x) x)
    (hne : ∀ x ∈ Iio a, g' x ≠ 0)
    (_hfl : Tendsto f atBot atTop ∨ Tendsto f atBot atBot)
    (hgl : Tendsto g atBot atTop ∨ Tendsto g atBot atBot)
    (hl : Tendsto (fun x ↦ f' x / g' x) atBot l) (hlt : IsRealLimitTargetFilter l) :
    Tendsto (fun x ↦ f x / g x) atBot l :=
  lhopital_infinite_atBot_hasDerivAt hf hg hne hgl hl hlt

end calculus.Chapter04.Section04InfiniteExtensions
