import calculus.Chapter02.Section04
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic.Push

/-!
# 2.8. Định lí Cantor và Bolzano–Weierstrass

Nguồn: `source/Ch2_dayso.tex`, dòng 2523–2668; mã C02-S09.
-/

set_option autoImplicit false

namespace calculus.Chapter02.Section08

open Set Filter
open scoped Topology

/-- Định nghĩa 2.8.1: các đoạn không rỗng, lồng nhau, tại mọi n≥1. -/
def NestedClosedIntervals (a b : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → a n ≤ b n) ∧
    ∀ n : ℕ, 1 ≤ n → Icc (a (n + 1)) (b (n + 1)) ⊆ Icc (a n) (b n)

/-- Giao các đoạn tại n≥1. -/
def closedIntervalIntersection (a b : ℕ → ℝ) : Set ℝ :=
  ⋂ n ∈ Ici 1, Icc (a n) (b n)


theorem mem_closedIntervalIntersection (a b : ℕ → ℝ) (x : ℝ) :
    x ∈ closedIntervalIntersection a b ↔ ∀ n : ℕ, 1 ≤ n → a n ≤ x ∧ x ≤ b n := by
  simp [closedIntervalIntersection]

/-- Các đoạn khác rỗng lồng nhau khi và chỉ khi đầu mút trái tăng, đầu mút phải giảm. -/
theorem nestedClosedIntervals_iff (a b : ℕ → ℝ) :
    NestedClosedIntervals a b ↔
      (∀ n : ℕ, 1 ≤ n → a n ≤ b n) ∧ MonotoneOn a (Ici 1) ∧ AntitoneOn b (Ici 1) := by
  constructor
  · rintro ⟨hab, hnest⟩
    refine ⟨hab, monotoneOn_nat_Ici_of_le_succ ?_, antitoneOn_nat_Ici_of_succ_le ?_⟩
    · intro n hn
      exact (hnest n hn ⟨le_rfl, hab (n + 1) (by omega)⟩).1
    · intro n hn
      exact (hnest n hn ⟨hab (n + 1) (by omega), le_rfl⟩).2
  · rintro ⟨hab, ha, hb⟩
    refine ⟨hab, ?_⟩
    intro n hn x hx
    exact ⟨(ha hn (show n + 1 ∈ Ici 1 from Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_succ n)).trans hx.1,
      hx.2.trans (hb hn (show n + 1 ∈ Ici 1 from Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_succ n))⟩


theorem nested_endpoint_cross_le (a b : ℕ → ℝ) (h : NestedClosedIntervals a b)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : a m ≤ b n := by
  obtain ⟨hab, ha, hb⟩ := (nestedClosedIntervals_iff a b).mp h
  rcases le_total m n with hmn | hnm
  · exact (ha hm hn hmn).trans (hab n hn)
  · exact (hab m hm).trans (hb hn hm hnm)


theorem nested_endpoint_bounds (a b : ℕ → ℝ) (h : NestedClosedIntervals a b) :
    BddAbove (a '' Ici 1) ∧ BddBelow (b '' Ici 1) := by
  constructor
  · exact ⟨b 1, by rintro x ⟨n, hn, rfl⟩; exact nested_endpoint_cross_le a b h n 1 hn le_rfl⟩
  · exact ⟨a 1, by rintro x ⟨n, hn, rfl⟩; exact nested_endpoint_cross_le a b h 1 n le_rfl hn⟩


theorem endpoint_range_nonempty (a : ℕ → ℝ) : (a '' Ici 1).Nonempty :=
  ⟨a 1, ⟨1, by simp, rfl⟩⟩

/-- Dòng 2534: hai dãy đầu mút hội tụ về cận trên bé nhất và cận dưới lớn nhất của các số hạng tại n≥1. -/
theorem nested_endpoints_tendsto (a b : ℕ → ℝ) (h : NestedClosedIntervals a b) :
    Tendsto a atTop (𝓝 (sSup (a '' Ici 1))) ∧ Tendsto b atTop (𝓝 (sInf (b '' Ici 1))) := by
  obtain ⟨_, ha, hb⟩ := (nestedClosedIntervals_iff a b).mp h
  obtain ⟨hba, hbb⟩ := nested_endpoint_bounds a b h
  exact ⟨Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici ha hba,
    Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici hb hbb⟩

/-- Dòng 2536: cận trên bé nhất của các đầu mút trái không vượt cận dưới lớn nhất của các đầu mút phải. -/
theorem nested_sup_le_inf (a b : ℕ → ℝ) (h : NestedClosedIntervals a b) :
    sSup (a '' Ici 1) ≤ sInf (b '' Ici 1) := by
  apply le_csInf (endpoint_range_nonempty b)
  rintro x ⟨n, hn, rfl⟩
  apply csSup_le (endpoint_range_nonempty a)
  rintro y ⟨m, hm, rfl⟩
  exact nested_endpoint_cross_le a b h m n hm hn

/-- Dòng 2537–2539: giao các đoạn là đoạn có đầu mút bằng cận trên bé nhất và cận dưới lớn nhất ấy. -/
theorem cantor_intersection_eq (a b : ℕ → ℝ) (h : NestedClosedIntervals a b) :
    closedIntervalIntersection a b = Icc (sSup (a '' Ici 1)) (sInf (b '' Ici 1)) := by
  obtain ⟨hba, hbb⟩ := nested_endpoint_bounds a b h
  ext x
  rw [mem_closedIntervalIntersection]
  constructor
  · intro hx
    exact ⟨csSup_le (endpoint_range_nonempty a) (by rintro y ⟨n, hn, rfl⟩; exact (hx n hn).1),
      le_csInf (endpoint_range_nonempty b) (by rintro y ⟨n, hn, rfl⟩; exact (hx n hn).2)⟩
  · intro hx n hn
    exact ⟨(le_csSup hba ⟨n, hn, rfl⟩).trans hx.1,
      hx.2.trans (csInf_le hbb ⟨n, hn, rfl⟩)⟩

/-- Định lí 2.8.2: giao các đoạn lồng nhau khác rỗng. -/
theorem cantor_intersection_nonempty (a b : ℕ → ℝ) (h : NestedClosedIntervals a b) :
    (closedIntervalIntersection a b).Nonempty := by
  rw [cantor_intersection_eq a b h]
  exact ⟨sSup (a '' Ici 1), le_rfl, nested_sup_le_inf a b h⟩

/-- Định lí 2.8.2: nếu độ dài tiến về 0 thì giao có đúng một điểm. -/
theorem cantor_intersection_existsUnique (a b : ℕ → ℝ) (h : NestedClosedIntervals a b)
    (hw : Section03.ConvergesTo (fun n ↦ b n - a n) 0) :
    ∃! x : ℝ, x ∈ closedIntervalIntersection a b := by
  obtain ⟨ha, hb⟩ := nested_endpoints_tendsto a b h
  have heq := tendsto_nhds_unique (hb.sub ha) (Section03.convergesTo_iff_tendsto.mp hw)
  have hab : sSup (a '' Ici 1) = sInf (b '' Ici 1) := by linarith
  rw [cantor_intersection_eq a b h, ← hab, Icc_self]
  exact ⟨_, rfl, by intro x hx; exact hx⟩


theorem strictMono_sequenceSubsequence (u : ℕ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Section04.IsSequenceSubsequence u (u ∘ φ) :=
  ⟨φ, fun n hn ↦ hn.trans (hφ.id_le n), hφ.strictMonoOn _, fun _ _ ↦ rfl⟩

/-- Định lí 2.8.4: dãy thực bị chặn có dãy con hội tụ. -/
theorem bounded_has_convergent_subsequence (u : ℕ → ℝ) (hu : Section04.SequenceBounded u) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ ∃ ℓ : ℝ, Section03.ConvergesTo v ℓ := by
  obtain ⟨⟨M, hM⟩, ⟨m, hm⟩⟩ := hu
  obtain ⟨ℓ, _, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n : ℕ ↦ u (n + 1)) (fun n ↦ ⟨hm (n + 1) (by omega), hM (n + 1) (by omega)⟩)
  have hidx : StrictMono (fun n : ℕ ↦ φ n + 1) := fun i j hij ↦ Nat.add_lt_add_right (hφ hij) 1
  exact ⟨fun n ↦ u (φ n + 1), strictMono_sequenceSubsequence u _ hidx,
    ℓ, Section03.convergesTo_iff_tendsto.mpr hlim⟩

/-- Nhận xét 2.8.3(1): các khoảng mở (0,1/n) có giao rỗng. -/
theorem shrinking_open_intervals_empty :
    (⋂ n ∈ Ici (1 : ℕ), Ioo (0 : ℝ) (1 / (n : ℝ))) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxall : ∀ n : ℕ, 1 ≤ n → 0 < x ∧ x < 1 / (n : ℝ) := by
    simpa using hx
  have hxpos := (hxall 1 le_rfl).1
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / x) 1)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) (le_of_lt ((le_max_right _ _).trans_lt hn))
  have hn1 : 1 ≤ n := by exact_mod_cast (le_of_lt ((le_max_right _ _).trans_lt hn))
  have hsmall := (lt_div_iff₀ hnpos).mp (hxall n hn1).2
  have hlarge := (div_lt_iff₀ hxpos).mp ((le_max_left _ _).trans_lt hn)
  nlinarith

/-- Nhận xét 2.8.3(2): các tập đóng không bị chặn [n,+∞) có giao rỗng. -/
theorem closed_unbounded_intervals_empty :
    (⋂ n ∈ Ici (1 : ℕ), Ici (n : ℝ)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxall : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x := by simpa using hx
  obtain ⟨n, hn⟩ := exists_nat_gt (max x 1)
  have hn1 : 1 ≤ n := by exact_mod_cast (le_of_lt ((le_max_right _ _).trans_lt hn))
  exact not_le_of_gt ((le_max_left _ _).trans_lt hn) (hxall n hn1)

/-- Bài 2.8.1: mọi dãy trong (1,10) có dãy con hội tụ. -/
theorem bounded_open_interval_has_convergent_subsequence (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n → 1 < u n ∧ u n < 10) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ ∃ ℓ : ℝ, Section03.ConvergesTo v ℓ :=
  bounded_has_convergent_subsequence u
    ⟨⟨10, fun n hn ↦ (hu n hn).2.le⟩, ⟨1, fun n hn ↦ (hu n hn).1.le⟩⟩

/-- Bài 2.8.2: ví dụ không bị chặn vẫn có dãy con hội tụ về 0. -/
theorem unbounded_with_convergent_subsequence_example :
    ¬ Section04.SequenceBounded Section04.reciprocalEvenSquareOdd ∧
      Section04.IsSequenceSubsequence Section04.reciprocalEvenSquareOdd
        (fun n ↦ Section04.reciprocalEvenSquareOdd (2 * n)) ∧
      Section03.ConvergesTo (fun n ↦ Section04.reciprocalEvenSquareOdd (2 * n)) 0 := by
  refine ⟨Section04.reciprocalEvenSquareOdd_unbounded, (Section04.standard_sequenceSubsequences _).1, ?_⟩
  have hl := Section04.tendsto_sequenceSubsequence _ _ 0
    (Section03.convergesTo_iff_tendsto.mp Section03.reciprocal_converges)
    ((Section04.standard_sequenceSubsequences (fun n : ℕ ↦ 1 / (n : ℝ))).1)
  apply Section03.convergesTo_iff_tendsto.mpr
  convert hl using 1
  ext n
  have he : (2 * n) % 2 = 0 := by omega
  simp [Section04.reciprocalEvenSquareOdd, he]

/-- Bài 2.8.4: e^(sin n) có dãy con hội tụ vì e⁻¹≤e^(sin n)≤e. -/
theorem exp_sine_has_convergent_subsequence :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence (fun n : ℕ ↦ Real.exp (Real.sin n)) v ∧
      ∃ ℓ : ℝ, Section03.ConvergesTo v ℓ := by
  apply bounded_has_convergent_subsequence
  exact ⟨⟨Real.exp 1, fun n _ ↦ Real.exp_le_exp.mpr (Real.sin_le_one _)⟩,
    ⟨Real.exp (-1), fun n _ ↦ Real.exp_le_exp.mpr (Real.neg_one_le_sin _)⟩⟩

/-- Bài 2.8.6: 2cos n−sin n thuộc [−3,3], nên có dãy con hội tụ. -/
theorem trig_linear_combination_has_convergent_subsequence :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence (fun n : ℕ ↦ 2 * Real.cos n - Real.sin n) v ∧
      ∃ ℓ : ℝ, Section03.ConvergesTo v ℓ := by
  apply bounded_has_convergent_subsequence
  constructor
  · exact ⟨3, fun n _ ↦ by linarith [Real.cos_le_one (n : ℝ), Real.neg_one_le_sin (n : ℝ)]⟩
  · exact ⟨-3, fun n _ ↦ by linarith [Real.neg_one_le_cos (n : ℝ), Real.sin_le_one (n : ℝ)]⟩

/-- Bài 2.8.7: f có miền [0,∞). -/
theorem positive_fraction_has_convergent_subsequence
    (f : {x : ℝ // 0 ≤ x} → ℝ) (hf : ∀ x, 0 < f x) :
    ∃ v : ℕ → ℝ,
      Section04.IsSequenceSubsequence (fun n : ℕ ↦ f ⟨n, Nat.cast_nonneg n⟩ / (f ⟨n, Nat.cast_nonneg n⟩ + 1)) v ∧
      ∃ ℓ : ℝ, Section03.ConvergesTo v ℓ := by
  apply bounded_has_convergent_subsequence
  constructor
  · refine ⟨1, fun n _ ↦ ?_⟩
    exact (div_le_one (by linarith [hf ⟨(n : ℝ), Nat.cast_nonneg n⟩])).mpr (by linarith)
  · exact ⟨0, fun n _ ↦ (div_pos (hf _) (by linarith [hf ⟨(n : ℝ), Nat.cast_nonneg n⟩])).le⟩

/-- Bài 2.8.11: dãy có mọi khoảng cách giữa hai số hạng nhỏ hơn M có dãy con hội tụ. -/
theorem bounded_pairwise_difference_has_convergent_subsequence (u : ℕ → ℝ)
    (M : ℝ) (_hM : 0 < M) (hu : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → |u n - u m| < M) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ ∃ ℓ : ℝ, Section03.ConvergesTo v ℓ := by
  apply bounded_has_convergent_subsequence
  exact ⟨⟨u 1 + M, fun n hn ↦ by linarith [(abs_lt.mp (hu 1 n le_rfl hn)).2]⟩,
    ⟨u 1 - M, fun n hn ↦ by linarith [(abs_lt.mp (hu 1 n le_rfl hn)).1]⟩⟩


theorem sequenceSubsequence_trans (u v w : ℕ → ℝ)
    (hv : Section04.IsSequenceSubsequence u v) (hw : Section04.IsSequenceSubsequence v w) :
    Section04.IsSequenceSubsequence u w := by
  obtain ⟨φ, hφpos, hφmono, hφterms⟩ := hv
  obtain ⟨ψ, hψpos, hψmono, hψterms⟩ := hw
  refine ⟨φ ∘ ψ, fun k hk ↦ hφpos _ (hψpos k hk), ?_, ?_⟩
  · intro i hi j hj hij
    exact hφmono (hψpos i hi) (hψpos j hj) (hψmono hi hj hij)
  · intro k hk
    exact (hψterms k hk).trans (hφterms _ (hψpos k hk))

/-- Bài 2.8.9(a): nếu u không hội tụ về ℓ thì có dãy con cách ℓ một khoảng dương cố định. -/
theorem not_converges_has_separated_subsequence (u : ℕ → ℝ) (ℓ : ℝ)
    (hu : ¬ Section03.ConvergesTo u ℓ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧
      ∀ k : ℕ, 1 ≤ k → ε < |v k - ℓ| := by
  unfold Section03.ConvergesTo at hu
  push Not at hu
  obtain ⟨δ, hδ, hbad⟩ := hu
  have hex : ∀ N : ℕ, ∃ n > N, δ / 2 < |u n - ℓ| := by
    intro N
    obtain ⟨n, hn, hdist⟩ := hbad (N + 1) (by omega)
    exact ⟨n, by omega, by linarith⟩
  obtain ⟨φ, hφ, hsep⟩ := Nat.exists_strictMono_subsequence hex
  exact ⟨δ / 2, by linarith, u ∘ φ, strictMono_sequenceSubsequence u φ hφ, fun k _ ↦ hsep k⟩

/-- Bài 2.8.9(b): cận dưới dương chung cho khoảng cách đến ℓ
loại mọi dãy con hội tụ về ℓ. -/
theorem separated_has_no_subsequence_converging (v : ℕ → ℝ) (ℓ ε : ℝ)
    (hε : 0 < ε) (hsep : ∀ k : ℕ, 1 ≤ k → ε < |v k - ℓ|) :
    ∀ w : ℕ → ℝ, Section04.IsSequenceSubsequence v w → ¬ Section03.ConvergesTo w ℓ := by
  intro w hw hlim
  obtain ⟨φ, hφpos, _, hterms⟩ := hw
  obtain ⟨N, hN, hclose⟩ := hlim ε hε
  have hnear := hclose N le_rfl
  rw [hterms N hN] at hnear
  exact not_lt_of_gt (hsep _ (hφpos N hN)) hnear

/-- Bài 2.8.10: mỗi điểm giới hạn của dãy bị chặn phân kì có một điểm giới hạn khác nó. -/
theorem bounded_nonconvergent_has_other_subsequence_limit
    (u v : ℕ → ℝ) (ℓ : ℝ) (hu : Section04.SequenceBounded u)
    (hdiv : Section03.IsDivergent u) (_hv : Section04.IsSequenceSubsequence u v)
    (_hvl : Section03.ConvergesTo v ℓ) :
    ∃ w : ℕ → ℝ, Section04.IsSequenceSubsequence u w ∧
      ∃ ℓ' : ℝ, ℓ' ≠ ℓ ∧ Section03.ConvergesTo w ℓ' := by
  have hnot : ¬ Section03.ConvergesTo u ℓ := fun h ↦ hdiv ⟨ℓ, h⟩
  obtain ⟨ε, hε, z, hz, hsep⟩ := not_converges_has_separated_subsequence u ℓ hnot
  obtain ⟨w, hw, ℓ', hwl⟩ := bounded_has_convergent_subsequence z
    (Section04.sequenceBounded_sequenceSubsequence u z hu hz)
  exact ⟨w, sequenceSubsequence_trans u z w hz hw, ℓ',
    fun heq ↦ separated_has_no_subsequence_converging z ℓ ε hε hsep w hw (heq ▸ hwl), hwl⟩


theorem exists_strictMono_indexed (P : ℕ → ℕ → Prop)
    (h : ∀ n N : ℕ, ∃ m > N, P n m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) := by
  classical
  choose f hf using h
  let φ : ℕ → ℕ := fun n ↦ Nat.rec (f 0 0) (fun k m ↦ f (k + 1) m) n
  refine ⟨φ, strictMono_nat_of_lt_succ (fun n ↦ (hf (n + 1) (φ n)).1), ?_⟩
  intro n
  cases n with
  | zero => exact (hf 0 0).2
  | succ n => exact (hf (n + 1) (φ n)).2


theorem unbounded_above_tail (u : ℕ → ℝ) (hu : ¬ Section04.SequenceBoundedAbove u)
    (N : ℕ) (M : ℝ) : ∃ n : ℕ, N < n ∧ M < u n := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) u (by simp)
  apply hu
  refine ⟨max M (u j), fun n _ ↦ ?_⟩
  by_cases hsmall : n ≤ N
  · exact (hmax n (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _)
  · exact (hn n (by omega)).trans (le_max_left _ _)

/-- Bài 2.8.12(a): dãy không bị chặn trên có dãy con tiến về +∞. -/
theorem unbounded_above_has_subsequence_tendsto_atTop (u : ℕ → ℝ)
    (hu : ¬ Section04.SequenceBoundedAbove u) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ Tendsto v atTop atTop := by
  obtain ⟨φ, hφ, hgrow⟩ := exists_strictMono_indexed
    (fun n m ↦ (n : ℝ) < u m) (fun n N ↦ unbounded_above_tail u hu N n)
  refine ⟨u ∘ φ, strictMono_sequenceSubsequence u φ hφ, ?_⟩
  exact tendsto_atTop_mono (fun n ↦ (hgrow n).le) tendsto_natCast_atTop_atTop

/-- Bài 2.8.12(b): dãy không bị chặn dưới có dãy con tiến về −∞. -/
theorem unbounded_below_has_subsequence_tendsto_atBot (u : ℕ → ℝ)
    (hu : ¬ Section04.SequenceBoundedBelow u) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ Tendsto v atTop atBot := by
  have hneg : ¬ Section04.SequenceBoundedAbove (fun n ↦ -u n) := by
    rintro ⟨M, hM⟩
    exact hu ⟨-M, fun n hn ↦ by linarith [hM n hn]⟩
  obtain ⟨v, hv, hl⟩ := unbounded_above_has_subsequence_tendsto_atTop (fun n ↦ -u n) hneg
  obtain ⟨φ, hpos, hmono, hterms⟩ := hv
  refine ⟨fun n ↦ -v n, ⟨φ, hpos, hmono, ?_⟩, ?_⟩
  · intro n hn
    change -v n = u (φ n)
    rw [hterms n hn]
    simp
  · exact tendsto_neg_atTop_atBot.comp hl

/-- Bài 2.8.5: (−1)ⁿn² không có dãy con hội tụ. -/
theorem alternating_square_has_no_convergent_subsequence :
    ∀ v : ℕ → ℝ, Section04.IsSequenceSubsequence (fun n : ℕ ↦ (-1 : ℝ) ^ n * (n : ℝ) ^ 2) v →
      Section03.IsDivergent v := by
  intro v hv
  apply Section04.unbounded_divergent
  intro hb
  obtain ⟨M, _, hM⟩ := (Section04.sequenceBounded_iff_abs v).mp hb
  obtain ⟨φ, hpos, hmono, hterms⟩ := hv
  obtain ⟨n, hn⟩ := exists_nat_gt (max M 1)
  have hn1 : 1 ≤ n := by exact_mod_cast (le_of_lt ((le_max_right _ _).trans_lt hn))
  have hidx : n ≤ φ n := Section04.subsequence_index_ge φ hpos hmono n hn1
  have hidxR : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hidx
  have hphi1 : (1 : ℝ) ≤ φ n := by exact_mod_cast hpos n hn1
  have hbound := hM n hn1
  rw [hterms n hn1] at hbound
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ (φ n : ℝ) from Nat.cast_nonneg (φ n)), one_mul] at hbound
  have hlarge := (le_max_left _ _).trans_lt hn
  nlinarith


theorem zero_width_intersection_point_unique (a b : ℕ → ℝ)
    (hw : Section03.ConvergesTo (fun n ↦ b n - a n) 0)
    (x y : ℝ) (hx : x ∈ closedIntervalIntersection a b) (hy : y ∈ closedIntervalIntersection a b) : x = y := by
  by_contra hne
  have hε : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN, hclose⟩ := hw |x - y| hε
  have hxn := (mem_closedIntervalIntersection a b x).mp hx N hN
  have hyn := (mem_closedIntervalIntersection a b y).mp hy N hN
  have hwidth : 0 ≤ b N - a N := by linarith
  have habs : |x - y| ≤ b N - a N := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsmall := hclose N le_rfl
  rw [sub_zero, abs_of_nonneg hwidth] at hsmall
  exact not_lt_of_ge habs hsmall

/-- Bài 2.8.14: giao các đoạn lồng nhau khác rỗng. -/
theorem cantor_nonempty_via_bolzanoWeierstrass (a b x : ℕ → ℝ)
    (h : NestedClosedIntervals a b) (hx : ∀ n : ℕ, 1 ≤ n → x n ∈ Icc (a n) (b n)) :
    (closedIntervalIntersection a b).Nonempty := by
  obtain ⟨_, ha, hb⟩ := (nestedClosedIntervals_iff a b).mp h
  have hbound : Section04.SequenceBounded x :=
    ⟨⟨b 1, fun n hn ↦ (hx n hn).2.trans (hb (by simp) hn hn)⟩,
      ⟨a 1, fun n hn ↦ (ha (by simp) hn hn).trans (hx n hn).1⟩⟩
  obtain ⟨v, hv, ℓ, hl⟩ := bounded_has_convergent_subsequence x hbound
  obtain ⟨φ, hpos, hmono, hterms⟩ := hv
  refine ⟨ℓ, (mem_closedIntervalIntersection a b ℓ).mpr ?_⟩
  intro N hN
  apply isClosed_Icc.mem_of_tendsto (Section03.convergesTo_iff_tendsto.mp hl)
  refine eventually_atTop.2 ⟨N, fun k hk ↦ ?_⟩
  have hk1 : 1 ≤ k := hN.trans hk
  have hφk : k ≤ φ k := Section04.subsequence_index_ge φ hpos hmono k hk1
  have hφN : N ≤ φ k := hk.trans hφk
  rw [hterms k hk1]
  exact ⟨(ha hN (hpos k hk1) hφN).trans (hx _ (hpos k hk1)).1,
    (hx _ (hpos k hk1)).2.trans (hb hN (hpos k hk1) hφN)⟩

/-- Bài 2.8.14: độ dài tiến về 0 thì giao các đoạn có duy nhất một điểm. -/
theorem cantor_unique_via_bolzanoWeierstrass (a b x : ℕ → ℝ)
    (h : NestedClosedIntervals a b) (hx : ∀ n : ℕ, 1 ≤ n → x n ∈ Icc (a n) (b n))
    (hw : Section03.ConvergesTo (fun n ↦ b n - a n) 0) :
    ∃! c : ℝ, c ∈ closedIntervalIntersection a b := by
  obtain ⟨c, hc⟩ := cantor_nonempty_via_bolzanoWeierstrass a b x h hx
  exact ⟨c, hc, fun y hy ↦ zero_width_intersection_point_unique a b hw y c hy hc⟩


theorem tail_approaches_unattained_supremum (u : ℕ → ℝ)
    (hu : Section04.SequenceBoundedAbove u) (hs : sSup (Section04.sequenceRangeFromOne u) ∉ Section04.sequenceRangeFromOne u)
    (N : ℕ) (x : ℝ) (hx : x < sSup (Section04.sequenceRangeFromOne u)) :
    ∃ n : ℕ, N < n ∧ x < u n := by
  classical
  have hba := (Section04.sequenceBoundedAbove_iff u).mp hu
  have hne : (Section04.sequenceRangeFromOne u).Nonempty := ⟨u 1, ⟨1, by simp, rfl⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 (max N 1)) u
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, le_max_right _ _⟩⟩
  have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjs : u j < sSup (Section04.sequenceRangeFromOne u) := by
    apply lt_of_le_of_ne (le_csSup hba ⟨j, hjpos, rfl⟩)
    intro heq
    exact hs (heq ▸ (show u j ∈ Section04.sequenceRangeFromOne u from ⟨j, hjpos, rfl⟩))
  obtain ⟨y, hy, hlarge⟩ := exists_lt_of_lt_csSup hne (max_lt hx hjs)
  obtain ⟨n, hn, rfl⟩ := hy
  refine ⟨n, ?_, (le_max_left _ _).trans_lt hlarge⟩
  by_contra hsmall
  have hnN : n ≤ max N 1 := (le_of_not_gt hsmall).trans (le_max_left _ _)
  have hbound := hmax n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
  exact not_lt_of_ge hbound ((le_max_right _ _).trans_lt hlarge)

/-- Bài 2.8.8: cận trên bé nhất không đạt được là giới hạn của một dãy con. -/
theorem unattained_supremum_has_convergent_subsequence (u : ℕ → ℝ)
    (hu : Section04.SequenceBounded u) (hs : sSup (Section04.sequenceRangeFromOne u) ∉ Section04.sequenceRangeFromOne u) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧
      Section03.ConvergesTo v (sSup (Section04.sequenceRangeFromOne u)) := by
  have hba := (Section04.sequenceBoundedAbove_iff u).mp hu.1
  have hex : ∀ k N : ℕ, ∃ n > N,
      sSup (Section04.sequenceRangeFromOne u) - 1 / ((k : ℝ) + 1) < u n := by
    intro k N
    have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact tail_approaches_unattained_supremum u hu.1 hs N _ (by linarith)
  obtain ⟨φ, hφ, hlow⟩ := exists_strictMono_indexed _ hex
  refine ⟨u ∘ φ, strictMono_sequenceSubsequence u φ hφ, ?_⟩
  apply Section03.convergesTo_of_error_le_const_div (C := 1) (by norm_num)
  intro n hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hupp := le_csSup hba (show u (φ n) ∈ Section04.sequenceRangeFromOne u from ⟨φ n, hn.trans (hφ.id_le n), rfl⟩)
  have hdist : |u (φ n) - sSup (Section04.sequenceRangeFromOne u)| ≤ 1 / ((n : ℝ) + 1) :=
    abs_le.mpr ⟨by linarith [hlow n], by
      have hε : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩
  exact hdist.trans (one_div_le_one_div_of_le hpos (by linarith))

/-- Dãy có số hạng khác 0 và giới hạn 0 có dãy con với tỉ số liên tiếp tiến về 0. -/
theorem zero_limit_has_ratio_zero_subsequence (u : ℕ → ℝ)
    (hu : Section03.ConvergesTo u 0) (hneq : ∀ n : ℕ, 1 ≤ n → u n ≠ 0) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧
      Section03.ConvergesTo (fun n ↦ v (n + 1) / v n) 0 := by
  classical
  have hex : ∀ n m : ℕ, ∃ k : ℕ, m < k ∧ 1 ≤ k ∧
      (1 ≤ m → |u k| < |u m| / ((n : ℝ) + 1)) := by
    intro n m
    by_cases hm : 1 ≤ m
    · have hε : 0 < |u m| / ((n : ℝ) + 1) := div_pos (abs_pos.mpr (hneq m hm)) (by positivity)
      obtain ⟨N, hN, hclose⟩ := hu _ hε
      refine ⟨max N (m + 1), ?_, ?_, fun _ ↦ ?_⟩
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _)
      · exact hN.trans (le_max_left _ _)
      · simpa only [sub_zero] using hclose _ (le_max_left _ _)
    · exact ⟨m + 1, Nat.lt_succ_self m, by omega, fun hm' ↦ False.elim (hm hm')⟩
  choose f hf using hex
  let φ : ℕ → ℕ := fun n ↦ Nat.rec 1 (fun k m ↦ f k m) n
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ (fun n ↦ (hf n (φ n)).1)
  have hφpos : ∀ n : ℕ, 1 ≤ φ n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact (hf n (φ n)).2.1
  refine ⟨u ∘ φ, strictMono_sequenceSubsequence u φ hφ, ?_⟩
  apply Section03.convergesTo_of_error_le_const_div (C := 1) (by norm_num)
  intro n hn
  have hden : 0 < |u (φ n)| := abs_pos.mpr (hneq _ (hφpos n))
  have hnext := (hf n (φ n)).2.2 (hφpos n)
  have hr : |u (φ (n + 1)) / u (φ n)| < 1 / ((n : ℝ) + 1) := by
    rw [abs_div]
    apply (div_lt_iff₀ hden).mpr
    change |u (f n (φ n))| < (1 / ((n : ℝ) + 1)) * |u (φ n)|
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hnext
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  simpa only [Function.comp_def, sub_zero] using
    hr.le.trans (one_div_le_one_div_of_le hnpos (by linarith))

/-- Bài 2.8.13: dãy bị chặn, có số hạng khác 0, có dãy con mà tỉ số liên tiếp hội tụ. -/
theorem bounded_nonzero_has_convergent_successive_ratios (u : ℕ → ℝ)
    (hu : Section04.SequenceBounded u) (hneq : ∀ n : ℕ, 1 ≤ n → u n ≠ 0) :
    ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧
      ∃ ℓ : ℝ, Section03.ConvergesTo (fun n ↦ v (n + 1) / v n) ℓ := by
  obtain ⟨v, hv, ℓ, hl⟩ := bounded_has_convergent_subsequence u hu
  by_cases hℓ : ℓ = 0
  · have hl0 : Section03.ConvergesTo v 0 := hℓ ▸ hl
    have hvneq : ∀ n : ℕ, 1 ≤ n → v n ≠ 0 := by
      obtain ⟨φ, hpos, _, hterms⟩ := hv
      intro n hn
      rw [hterms n hn]
      exact hneq _ (hpos n hn)
    obtain ⟨w, hw, hr⟩ := zero_limit_has_ratio_zero_subsequence v hl0 hvneq
    exact ⟨w, sequenceSubsequence_trans u v w hv hw, 0, hr⟩
  · have hlim := Section03.convergesTo_iff_tendsto.mp hl
    have hshift : Tendsto (fun n : ℕ ↦ v (n + 1)) atTop (𝓝 ℓ) :=
      hlim.comp (tendsto_add_atTop_nat 1)
    refine ⟨v, hv, 1, Section03.convergesTo_iff_tendsto.mpr ?_⟩
    have hr := hshift.div hlim hℓ
    have hfun : ((fun n : ℕ ↦ v (n + 1)) / v) = (fun n : ℕ ↦ v (n + 1) / v n) := by
      ext n
      rfl
    rw [hfun, div_self hℓ] at hr
    exact hr


theorem nestedClosedIntervals_subset (a b : ℕ → ℝ) (h : NestedClosedIntervals a b)
    (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) : Icc (a m) (b m) ⊆ Icc (a n) (b n) := by
  obtain ⟨_, ha, hb⟩ := (nestedClosedIntervals_iff a b).mp h
  intro x hx
  exact ⟨(ha hn (hn.trans hnm) hnm).trans hx.1, hx.2.trans (hb hn (hn.trans hnm) hnm)⟩

/-- Bài 2.8.3: dãy chỉ số 1,2,4,8,…, với n₁=1. -/
def dyadicIndex (n : ℕ) : ℕ := 2 ^ (n - 1)

/-- I₁=[−1,1]; với n≥2, Iₙ=[0,2^{−(n−2)}]. -/
noncomputable def dyadicLeft (n : ℕ) : ℝ := if n ≤ 1 then -1 else 0


noncomputable def dyadicRight (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ (n - 2)


theorem dyadicIndex_strictMonoOn : StrictMonoOn dyadicIndex (Ici 1) := by
  intro i hi j hj hij
  change 1 ≤ i at hi
  change 1 ≤ j at hj
  exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : i - 1 < j - 1)

/-- Các đoạn của phép chia đôi không rỗng và lồng nhau. -/
theorem dyadic_intervals_nested : NestedClosedIntervals dyadicLeft dyadicRight := by
  apply (nestedClosedIntervals_iff _ _).mpr
  refine ⟨?_, monotoneOn_nat_Ici_of_le_succ ?_, antitoneOn_nat_Ici_of_succ_le ?_⟩
  · intro n hn
    have hnon : 0 ≤ 1 / (2 : ℝ) ^ (n - 2) := by positivity
    unfold dyadicLeft dyadicRight
    split_ifs <;> linarith
  · intro n hn
    unfold dyadicLeft
    split_ifs <;> norm_num
    omega
  · intro n hn
    apply one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ) ^ (n - 2))
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by omega : n - 2 ≤ n + 1 - 2)

/-- Độ dài Iₙ bằng 4/2ⁿ, tức 2/2ⁿ⁻¹. -/
theorem dyadic_interval_width (n : ℕ) (hn : 1 ≤ n) :
    dyadicRight n - dyadicLeft n = 4 / (2 : ℝ) ^ n := by
  by_cases hn1 : n = 1
  · subst n
    norm_num [dyadicLeft, dyadicRight]
  · have hn2 : 2 ≤ n := by omega
    have hexp : n = (n - 2) + 2 := by omega
    have hpow : (2 : ℝ) ^ n = 4 * (2 : ℝ) ^ (n - 2) := by
      conv_lhs => rw [hexp, pow_add]
      norm_num
      ring
    simp only [dyadicRight, dyadicLeft, show ¬n ≤ 1 from by omega, if_false, sub_zero]
    rw [hpow]
    field_simp

/-- Độ dài các đoạn chia đôi tiến về 0. -/
theorem dyadic_width_converges_zero :
    Section03.ConvergesTo (fun n ↦ dyadicRight n - dyadicLeft n) 0 := by
  have hl := (Section03.convergesTo_iff_tendsto.mp Section03.reciprocal_two_pow_converges).const_mul 4
  have h0 : Section03.ConvergesTo (fun n : ℕ ↦ 4 / (2 : ℝ) ^ n) 0 := by
    apply Section03.convergesTo_iff_tendsto.mpr
    simpa only [mul_zero, mul_one_div] using hl
  exact (Section03.convergesTo_congr (fun n hn ↦ dyadic_interval_width n hn)).mpr h0

/-- Số hạng được chọn x_{nₖ} thuộc Iₖ với mọi chỉ số dương. -/
theorem dyadic_alternating_reciprocal_mem (n : ℕ) (hn : 1 ≤ n) :
    (-1 : ℝ) ^ dyadicIndex n / (dyadicIndex n : ℝ) ∈ Icc (dyadicLeft n) (dyadicRight n) := by
  by_cases hn1 : n = 1
  · subst n
    norm_num [dyadicIndex, dyadicLeft, dyadicRight]
  · have hn2 : 2 ≤ n := by omega
    have hexp : n - 1 = (n - 2) + 1 := by omega
    have he : dyadicIndex n = 2 * 2 ^ (n - 2) := by
      unfold dyadicIndex
      rw [hexp, pow_succ, Nat.mul_comm]
    have hsign : (-1 : ℝ) ^ dyadicIndex n = 1 := by
      rw [he, pow_mul]
      norm_num
    simp only [hsign, dyadicLeft, show ¬n ≤ 1 from by omega, if_false, dyadicRight]
    constructor
    · positivity
    · apply one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ) ^ (n - 2))
      simp only [dyadicIndex, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by omega : n - 2 ≤ n - 1)

/-- Bài 2.8.3: dãy con đã chọn hội tụ về 0, với n₁=1 và các đoạn chia đôi nêu trên. -/
theorem dyadic_alternating_reciprocal_subsequence :
    dyadicIndex 1 = 1 ∧
      Section04.IsSequenceSubsequence (fun n : ℕ ↦ (-1 : ℝ) ^ n / (n : ℝ))
        (fun k ↦ (-1 : ℝ) ^ dyadicIndex k / (dyadicIndex k : ℝ)) ∧
      Section03.ConvergesTo (fun k ↦ (-1 : ℝ) ^ dyadicIndex k / (dyadicIndex k : ℝ)) 0 := by
  have hsub : Section04.IsSequenceSubsequence (fun n : ℕ ↦ (-1 : ℝ) ^ n / (n : ℝ))
      (fun k ↦ (-1 : ℝ) ^ dyadicIndex k / (dyadicIndex k : ℝ)) :=
    ⟨dyadicIndex, fun n _ ↦ Nat.one_le_pow _ _ (by norm_num), dyadicIndex_strictMonoOn, fun _ _ ↦ rfl⟩
  exact ⟨by norm_num [dyadicIndex], hsub, Section03.convergesTo_iff_tendsto.mpr
    (Section04.tendsto_sequenceSubsequence _ _ 0
      (Section03.convergesTo_iff_tendsto.mp Section03.alternating_reciprocal_converges) hsub)⟩

/-- Mỗi đoạn chia đôi chứa các số hạng có chỉ số lớn tùy ý, nên chứa vô hạn chỉ số. -/
theorem dyadic_intervals_contain_arbitrarily_late_terms (n N : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, N < m ∧ (-1 : ℝ) ^ m / (m : ℝ) ∈ Icc (dyadicLeft n) (dyadicRight n) := by
  let k := max n (N + 2)
  have hkn : n ≤ k := le_max_left _ _
  have hk1 : 1 ≤ k := hn.trans hkn
  have hidx := Section04.subsequence_index_ge dyadicIndex
    (fun n _ ↦ Nat.one_le_pow _ _ (by norm_num)) dyadicIndex_strictMonoOn k hk1
  refine ⟨dyadicIndex k, ?_, ?_⟩
  · have hbig : N + 2 ≤ k := le_max_right _ _
    omega
  · exact nestedClosedIntervals_subset _ _ dyadic_intervals_nested n k hn hkn
      (dyadic_alternating_reciprocal_mem k hk1)

/-- Các khoảng mở của phản ví dụ không rỗng và lồng nhau. -/
theorem shrinking_open_intervals_nested_nonempty :
    (∀ n : ℕ, 1 ≤ n → (Ioo (0 : ℝ) (1 / (n : ℝ))).Nonempty) ∧
      ∀ n : ℕ, 1 ≤ n → Ioo (0 : ℝ) (1 / ((n + 1 : ℕ) : ℝ)) ⊆ Ioo (0 : ℝ) (1 / (n : ℝ)) := by
  constructor
  · intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hinv : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
    exact ⟨(1 / (n : ℝ)) / 2, by constructor <;> linarith⟩
  · intro n hn x hx
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact ⟨hx.1, hx.2.trans_le (one_div_le_one_div_of_le hnpos (by push_cast; linarith))⟩

/-- Các khoảng [n,∞) đóng, lồng nhau và khác rỗng nhưng có giao rỗng. -/
theorem closed_unbounded_intervals_nested_nonempty :
    (∀ n : ℕ, 1 ≤ n → (Ici (n : ℝ)).Nonempty ∧ IsClosed (Ici (n : ℝ)) ∧ ¬ BddAbove (Ici (n : ℝ))) ∧
      ∀ n : ℕ, 1 ≤ n → Ici ((n + 1 : ℕ) : ℝ) ⊆ Ici (n : ℝ) := by
  constructor
  · intro n _
    refine ⟨⟨n, by simp⟩, isClosed_Ici, ?_⟩
    rintro ⟨M, hM⟩
    have hbig := hM (show max M (n : ℝ) + 1 ∈ Ici (n : ℝ) from by
      change (n : ℝ) ≤ max M (n : ℝ) + 1
      linarith [le_max_right M (n : ℝ)])
    linarith [le_max_left M (n : ℝ)]
  · intro n _ x hx
    change ((n + 1 : ℕ) : ℝ) ≤ x at hx
    change (n : ℝ) ≤ x
    push_cast at hx
    linarith

end calculus.Chapter02.Section08
