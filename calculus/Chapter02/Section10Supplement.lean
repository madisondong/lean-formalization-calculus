import calculus.Chapter02.Section10
import calculus.Chapter02.Section04
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# 2.10. Giới hạn trên, giới hạn dưới: đặc trưng và điểm giới hạn

Nguồn: `source/Ch2_dayso.tex`, dòng 3000–3401; mã C02-S11.
-/

set_option autoImplicit false

namespace calculus.Chapter02.Section10Supplement

open Set Filter
open scoped Topology
open Section10


theorem tailRange_eq_image (u : ℕ → ℝ) (n : ℕ) :
    tailRange u n = (fun k : ℕ ↦ (u k : EReal)) '' Ici n := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩


theorem tailSup_eq_iSup (u : ℕ → ℝ) (n : ℕ) :
    tailSup u n = ⨆ k : ℕ, ⨆ (_ : n ≤ k), (u k : EReal) := by
  rw [tailSup, tailRange_eq_image, sSup_image]
  rfl


theorem tailInf_eq_iInf (u : ℕ → ℝ) (n : ℕ) :
    tailInf u n = ⨅ k : ℕ, ⨅ (_ : n ≤ k), (u k : EReal) := by
  rw [tailInf, tailRange_eq_image, sInf_image]
  rfl


theorem sequenceLimsup_eq_filter (u : ℕ → ℝ) :
    sequenceLimsup u = limsup (fun n : ℕ ↦ (u n : EReal)) atTop := by
  unfold sequenceLimsup
  rw [(show Antitone (tailSup u) from fun _ _ h ↦ (tail_bounds_mono h).1).iInf_nat_add 1]
  simp_rw [tailSup_eq_iSup]
  exact limsup_eq_iInf_iSup_of_nat.symm


theorem sequenceLiminf_eq_filter (u : ℕ → ℝ) :
    sequenceLiminf u = liminf (fun n : ℕ ↦ (u n : EReal)) atTop := by
  unfold sequenceLiminf
  rw [(show Monotone (tailInf u) from fun _ _ h ↦ (tail_bounds_mono h).2).iSup_nat_add 1]
  simp_rw [tailInf_eq_iInf]
  exact liminf_eq_iSup_iInf_of_nat.symm

/-- Hội tụ trong số thực mở rộng. -/
def ExtendedConvergesTo (u : ℕ → ℝ) (ℓ : EReal) : Prop :=
  Tendsto (fun n : ℕ ↦ (u n : EReal)) atTop (𝓝 ℓ)

/-- Hội tụ mở rộng về ℓ∈ℝ tương đương hội tụ ε–N. -/
theorem extendedConvergesTo_coe_iff (u : ℕ → ℝ) (ℓ : ℝ) :
    ExtendedConvergesTo u ℓ ↔ Section03.ConvergesTo u ℓ :=
  EReal.tendsto_coe.trans Section03.convergesTo_iff_tendsto.symm

/-- Hội tụ về +∞ trong `EReal` tương đương `Tendsto` tới `atTop` trong ℝ. -/
theorem extendedConvergesTo_top_iff (u : ℕ → ℝ) :
    ExtendedConvergesTo u ⊤ ↔ Tendsto u atTop atTop := EReal.tendsto_coe_nhds_top_iff

/-- Hội tụ về −∞ trong `EReal` tương đương `Tendsto` tới `atBot` trong ℝ. -/
theorem extendedConvergesTo_bot_iff (u : ℕ → ℝ) :
    ExtendedConvergesTo u ⊥ ↔ Tendsto u atTop atBot := EReal.tendsto_coe_nhds_bot_iff

/-- Điểm giới hạn là giới hạn của một dãy con. -/
def extendedSequenceClusterSet (u : ℕ → ℝ) : Set EReal :=
  {ℓ | ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ ExtendedConvergesTo v ℓ}

/-- Điểm tụ theo bộ lọc tương đương giới hạn của một dãy con. -/
theorem mem_extendedSequenceClusterSet_iff (u : ℕ → ℝ) (ℓ : EReal) :
    ℓ ∈ extendedSequenceClusterSet u ↔ MapClusterPt ℓ atTop (fun n : ℕ ↦ (u n : EReal)) := by
  constructor
  · rintro ⟨v, ⟨φ, hpos, hmono, hφ⟩, hv⟩
    apply MapClusterPt.of_comp (Section04.subsequence_index_tendsto φ hpos hmono)
    have hconv : Tendsto ((fun n : ℕ ↦ (u n : EReal)) ∘ φ) atTop (𝓝 ℓ) :=
      hv.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ congrArg (fun x : ℝ ↦ (x : EReal)) (hφ n hn))
    exact hconv.mapClusterPt
  · intro h
    obtain ⟨φ, hmono, hconv⟩ := h.tendsto_subseq
    refine ⟨u ∘ φ, ⟨φ, ?_, hmono.strictMonoOn (Ici 1), fun _ _ ↦ rfl⟩, hconv⟩
    intro n hn
    exact hn.trans (hmono.id_le n)

/-- Nhận xét 2.10.13(i): luôn có dãy con đạt limsup, kể cả ±∞. -/
theorem sequenceLimsup_mem_clusterSet (u : ℕ → ℝ) : sequenceLimsup u ∈ extendedSequenceClusterSet u := by
  rw [mem_extendedSequenceClusterSet_iff, sequenceLimsup_eq_filter]
  exact MapClusterPt.limsup

/-- Nhận xét 2.10.13(ii): luôn có dãy con đạt liminf. -/
theorem sequenceLiminf_mem_clusterSet (u : ℕ → ℝ) : sequenceLiminf u ∈ extendedSequenceClusterSet u := by
  rw [mem_extendedSequenceClusterSet_iff, sequenceLiminf_eq_filter]
  exact MapClusterPt.liminf

/-- Mệnh đề 2.10.16: mọi điểm giới hạn nằm giữa liminf và limsup. -/
theorem cluster_point_bounds (u : ℕ → ℝ) (ℓ : EReal) (h : ℓ ∈ extendedSequenceClusterSet u) :
    sequenceLiminf u ≤ ℓ ∧ ℓ ≤ sequenceLimsup u := by
  have hc := (mem_extendedSequenceClusterSet_iff u ℓ).mp h
  rw [sequenceLiminf_eq_filter, sequenceLimsup_eq_filter]
  exact ⟨hc.liminf_le, hc.le_limsup⟩

/-- Nhận xét 2.10.17: limsup là điểm giới hạn lớn nhất, kể cả khi bằng ±∞. -/
theorem sequenceLimsup_isGreatest_clusterSet (u : ℕ → ℝ) :
    IsGreatest (extendedSequenceClusterSet u) (sequenceLimsup u) :=
  ⟨sequenceLimsup_mem_clusterSet u, fun _ h ↦ (cluster_point_bounds u _ h).2⟩

/-- Liminf là điểm giới hạn nhỏ nhất, kể cả khi bằng ±∞. -/
theorem sequenceLiminf_isLeast_clusterSet (u : ℕ → ℝ) :
    IsLeast (extendedSequenceClusterSet u) (sequenceLiminf u) :=
  ⟨sequenceLiminf_mem_clusterSet u, fun _ h ↦ (cluster_point_bounds u _ h).1⟩

/-- Hội tụ mở rộng khi và chỉ khi liminf và limsup cùng bằng giá trị giới hạn. -/
theorem extendedConvergesTo_iff_liminf_limsup (u : ℕ → ℝ) (ℓ : EReal) :
    ExtendedConvergesTo u ℓ ↔ sequenceLiminf u = ℓ ∧ sequenceLimsup u = ℓ := by
  rw [sequenceLiminf_eq_filter, sequenceLimsup_eq_filter]
  exact ⟨fun h ↦ ⟨h.liminf_eq, h.limsup_eq⟩, fun h ↦ tendsto_of_liminf_eq_limsup h.1 h.2⟩

/-- Hệ quả 2.10.14: hội tụ hữu hạn về ℓ khi và chỉ khi liminf=limsup=ℓ. -/
theorem convergesTo_iff_liminf_limsup (u : ℕ → ℝ) (ℓ : ℝ) :
    Section03.ConvergesTo u ℓ ↔ sequenceLiminf u = (ℓ : EReal) ∧ sequenceLimsup u = (ℓ : EReal) := by
  rw [← extendedConvergesTo_coe_iff]
  exact extendedConvergesTo_iff_liminf_limsup u ℓ

/-- Mệnh đề 2.10.8(i): dãy tiến về +∞ khi và chỉ khi liminf=+∞. -/
theorem tendsto_atTop_iff_sequenceLiminf_top (u : ℕ → ℝ) :
    Tendsto u atTop atTop ↔ sequenceLiminf u = ⊤ := by
  rw [← extendedConvergesTo_top_iff, extendedConvergesTo_iff_liminf_limsup]
  exact ⟨And.left, fun h ↦ ⟨h, top_unique (h ▸ sequenceLiminf_le_sequenceLimsup u)⟩⟩

/-- Mệnh đề 2.10.8(ii): dãy tiến về −∞ khi và chỉ khi limsup=−∞. -/
theorem tendsto_atBot_iff_sequenceLimsup_bot (u : ℕ → ℝ) :
    Tendsto u atTop atBot ↔ sequenceLimsup u = ⊥ := by
  rw [← extendedConvergesTo_bot_iff, extendedConvergesTo_iff_liminf_limsup]
  exact ⟨And.right, fun h ↦ ⟨bot_unique (h ▸ sequenceLiminf_le_sequenceLimsup u), h⟩⟩

/-- Định lí 2.10.11: đặc trưng limsup hữu hạn bằng cận ε trên phần đuôi
và một dãy con đạt giới hạn ấy. -/
theorem sequenceLimsup_eq_coe_iff (u : ℕ → ℝ) (ℓ : ℝ) :
    sequenceLimsup u = (ℓ : EReal) ↔
      (∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → u n < ℓ + ε) ∧
      ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ Section03.ConvergesTo v ℓ := by
  constructor
  · intro h
    constructor
    · intro ε hε
      have hh : limsup (fun n : ℕ ↦ (u n : EReal)) atTop < ((ℓ + ε : ℝ) : EReal) := by
        rw [← sequenceLimsup_eq_filter, h]
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hh)
      refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
      exact EReal.coe_lt_coe_iff.mp (hN n ((le_max_left N 1).trans hn))
    · obtain ⟨v, hv, hconv⟩ := sequenceLimsup_mem_clusterSet u
      exact ⟨v, hv, (extendedConvergesTo_coe_iff v ℓ).mp (h ▸ hconv)⟩
  · rintro ⟨hupper, v, hv, hconv⟩
    apply le_antisymm
    · by_contra hnot
      obtain ⟨r, hℓr, hrs⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
      have hpos : 0 < r - ℓ := by linarith [EReal.coe_lt_coe_iff.mp hℓr]
      obtain ⟨N, _, hN⟩ := hupper (r - ℓ) hpos
      have hb : sequenceLimsup u ≤ (r : EReal) := by
        rw [sequenceLimsup_eq_filter]
        apply limsup_le_of_le (by isBoundedDefault)
        exact (eventually_ge_atTop N).mono fun n hn ↦ EReal.coe_le_coe_iff.mpr (by linarith [hN n hn])
      exact (not_le_of_gt hrs) hb
    · exact (cluster_point_bounds u ℓ ⟨v, hv, (extendedConvergesTo_coe_iff v ℓ).mpr hconv⟩).2

/-- Định lí 2.10.12: đặc trưng liminf hữu hạn với uₙ>ℓ−ε trên phần đuôi. -/
theorem sequenceLiminf_eq_coe_iff (u : ℕ → ℝ) (ℓ : ℝ) :
    sequenceLiminf u = (ℓ : EReal) ↔
      (∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ℓ - ε < u n) ∧
      ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ Section03.ConvergesTo v ℓ := by
  constructor
  · intro h
    constructor
    · intro ε hε
      have hh : ((ℓ - ε : ℝ) : EReal) < liminf (fun n : ℕ ↦ (u n : EReal)) atTop := by
        rw [← sequenceLiminf_eq_filter, h]
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hh)
      refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
      exact EReal.coe_lt_coe_iff.mp (hN n ((le_max_left N 1).trans hn))
    · obtain ⟨v, hv, hconv⟩ := sequenceLiminf_mem_clusterSet u
      exact ⟨v, hv, (extendedConvergesTo_coe_iff v ℓ).mp (h ▸ hconv)⟩
  · rintro ⟨hlower, v, hv, hconv⟩
    apply le_antisymm
    · exact (cluster_point_bounds u ℓ ⟨v, hv, (extendedConvergesTo_coe_iff v ℓ).mpr hconv⟩).1
    · by_contra hnot
      obtain ⟨r, hsr, hrℓ⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
      have hpos : 0 < ℓ - r := by linarith [EReal.coe_lt_coe_iff.mp hrℓ]
      obtain ⟨N, _, hN⟩ := hlower (ℓ - r) hpos
      have hb : (r : EReal) ≤ sequenceLiminf u := by
        rw [sequenceLiminf_eq_filter]
        apply le_liminf_of_le (by isBoundedDefault)
        exact (eventually_ge_atTop N).mono fun n hn ↦ EReal.coe_le_coe_iff.mpr (by linarith [hN n hn])
      exact (not_le_of_gt hsr) hb


theorem sequenceBoundedAbove_iff_sequenceLimsup_lt_top (u : ℕ → ℝ) :
    Section04.SequenceBoundedAbove u ↔ sequenceLimsup u < ⊤ := by
  constructor
  · rintro ⟨M, hM⟩
    have hb : sequenceLimsup u ≤ (M : EReal) := by
      rw [sequenceLimsup_eq_filter]
      exact limsup_le_of_le (by isBoundedDefault)
        ((eventually_ge_atTop 1).mono fun n hn ↦ EReal.coe_le_coe_iff.mpr (hM n hn))
    exact hb.trans_lt (EReal.coe_lt_top M)
  · intro h
    obtain ⟨M, hM, _⟩ := EReal.exists_between_coe_real h
    rw [sequenceLimsup_eq_filter] at hM
    have he := (eventually_lt_of_limsup_lt hM).mono fun n hn ↦ (EReal.coe_lt_coe_iff.mp hn).le
    have hb : IsBoundedUnder (· ≤ ·) atTop u := ⟨M, he⟩
    obtain ⟨B, hB⟩ := hb.bddAbove_range
    exact ⟨B, fun n _ ↦ hB ⟨n, rfl⟩⟩


theorem sequenceBoundedBelow_iff_bot_lt_sequenceLiminf (u : ℕ → ℝ) :
    Section04.SequenceBoundedBelow u ↔ ⊥ < sequenceLiminf u := by
  constructor
  · rintro ⟨m, hm⟩
    have hb : (m : EReal) ≤ sequenceLiminf u := by
      rw [sequenceLiminf_eq_filter]
      exact le_liminf_of_le (by isBoundedDefault)
        ((eventually_ge_atTop 1).mono fun n hn ↦ EReal.coe_le_coe_iff.mpr (hm n hn))
    exact (EReal.bot_lt_coe m).trans_le hb
  · intro h
    obtain ⟨m, _, hm⟩ := EReal.exists_between_coe_real h
    rw [sequenceLiminf_eq_filter] at hm
    have he := (eventually_lt_of_lt_liminf hm).mono fun n hn ↦ (EReal.coe_lt_coe_iff.mp hn).le
    have hb : IsBoundedUnder (· ≥ ·) atTop u := ⟨m, he⟩
    obtain ⟨B, hB⟩ := hb.bddBelow_range
    exact ⟨B, fun n _ ↦ hB ⟨n, rfl⟩⟩

/-- Mệnh đề 2.10.6(i),(ii): không bị chặn trên khi và chỉ khi limsup=+∞. -/
theorem not_sequenceBoundedAbove_iff_sequenceLimsup_top (u : ℕ → ℝ) :
    ¬ Section04.SequenceBoundedAbove u ↔ sequenceLimsup u = ⊤ := by
  rw [sequenceBoundedAbove_iff_sequenceLimsup_lt_top, lt_top_iff_ne_top, not_not]

/-- Mệnh đề 2.10.7(i),(ii): không bị chặn dưới khi và chỉ khi liminf=−∞. -/
theorem not_sequenceBoundedBelow_iff_sequenceLiminf_bot (u : ℕ → ℝ) :
    ¬ Section04.SequenceBoundedBelow u ↔ sequenceLiminf u = ⊥ := by
  rw [sequenceBoundedBelow_iff_bot_lt_sequenceLiminf, bot_lt_iff_ne_bot, not_not]

/-- Mệnh đề 2.10.6(ii),(iii), Bài tập 5(a): tồn tại dãy con tiến về +∞ khi và chỉ khi limsup=+∞. -/
theorem sequenceLimsup_top_iff_subsequence_atTop (u : ℕ → ℝ) :
    sequenceLimsup u = ⊤ ↔ ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ Tendsto v atTop atTop := by
  constructor
  · intro h
    obtain ⟨v, hv, hconv⟩ := sequenceLimsup_mem_clusterSet u
    exact ⟨v, hv, (extendedConvergesTo_top_iff v).mp (h ▸ hconv)⟩
  · rintro ⟨v, hv, hconv⟩
    exact top_unique (cluster_point_bounds u ⊤ ⟨v, hv, (extendedConvergesTo_top_iff v).mpr hconv⟩).2

/-- Mệnh đề 2.10.7(ii),(iii), Bài tập 5(b): tồn tại dãy con tiến về −∞ khi và chỉ khi liminf=−∞. -/
theorem sequenceLiminf_bot_iff_subsequence_atBot (u : ℕ → ℝ) :
    sequenceLiminf u = ⊥ ↔ ∃ v : ℕ → ℝ, Section04.IsSequenceSubsequence u v ∧ Tendsto v atTop atBot := by
  constructor
  · intro h
    obtain ⟨v, hv, hconv⟩ := sequenceLiminf_mem_clusterSet u
    exact ⟨v, hv, (extendedConvergesTo_bot_iff v).mp (h ▸ hconv)⟩
  · rintro ⟨v, hv, hconv⟩
    exact bot_unique (cluster_point_bounds u ⊥ ⟨v, hv, (extendedConvergesTo_bot_iff v).mpr hconv⟩).1

/-- Nhận xét 2.10.10(i): trường hợp chỉ bị chặn dưới. -/
theorem bounded_below_unbounded_above_liminf_limsup (u : ℕ → ℝ)
    (hb : Section04.SequenceBoundedBelow u) (hu : ¬ Section04.SequenceBoundedAbove u) :
    sequenceLimsup u = ⊤ ∧ ⊥ < sequenceLiminf u ∧
      (sequenceLiminf u = ⊤ ∨ ∃ r : ℝ, sequenceLiminf u = r) := by
  have ht := (sequenceBoundedBelow_iff_bot_lt_sequenceLiminf u).mp hb
  refine ⟨(not_sequenceBoundedAbove_iff_sequenceLimsup_top u).mp hu, ht, ?_⟩
  by_cases htop : sequenceLiminf u = ⊤
  · exact Or.inl htop
  · exact Or.inr ⟨(sequenceLiminf u).toReal, (EReal.coe_toReal htop ht.ne').symm⟩

/-- Nhận xét 2.10.10(ii): trường hợp chỉ bị chặn trên. -/
theorem bounded_above_unbounded_below_liminf_limsup (u : ℕ → ℝ)
    (hb : Section04.SequenceBoundedAbove u) (hu : ¬ Section04.SequenceBoundedBelow u) :
    sequenceLiminf u = ⊥ ∧ sequenceLimsup u < ⊤ ∧
      (sequenceLimsup u = ⊥ ∨ ∃ r : ℝ, sequenceLimsup u = r) := by
  have ht := (sequenceBoundedAbove_iff_sequenceLimsup_lt_top u).mp hb
  refine ⟨(not_sequenceBoundedBelow_iff_sequenceLiminf_bot u).mp hu, ht, ?_⟩
  by_cases hbot : sequenceLimsup u = ⊥
  · exact Or.inl hbot
  · exact Or.inr ⟨(sequenceLimsup u).toReal, (EReal.coe_toReal ht.ne hbot).symm⟩

/-- Bài tập 3: bất đẳng thức từ một chỉ số nào đó truyền tới cả liminf và limsup. -/
theorem liminf_limsup_mono_of_eventually_le (u v : ℕ → ℝ) (h : u ≤ᶠ[atTop] v) :
    sequenceLimsup u ≤ sequenceLimsup v ∧ sequenceLiminf u ≤ sequenceLiminf v := by
  rw [sequenceLimsup_eq_filter, sequenceLimsup_eq_filter, sequenceLiminf_eq_filter, sequenceLiminf_eq_filter]
  have hc := h.mono fun _ hn ↦ EReal.coe_le_coe_iff.mpr hn
  exact ⟨limsup_le_limsup hc, liminf_le_liminf hc⟩

/-- Bài tập 4: đổi dấu hoán đổi limsup và liminf. -/
theorem liminf_limsup_neg (u : ℕ → ℝ) :
    sequenceLiminf (fun n ↦ -u n) = -sequenceLimsup u ∧
      sequenceLimsup (fun n ↦ -u n) = -sequenceLiminf u := by
  simp_rw [sequenceLimsup_eq_filter, sequenceLiminf_eq_filter, EReal.coe_neg]
  exact ⟨EReal.liminf_neg, EReal.limsup_neg⟩

/-- Bài tập 9: limsup của giá trị tuyệt đối bằng 0 khi và chỉ khi dãy hội tụ 0. -/
theorem convergesTo_zero_iff_abs_sequenceLimsup_zero (u : ℕ → ℝ) :
    Section03.ConvergesTo u 0 ↔ sequenceLimsup (fun n ↦ |u n|) = 0 := by
  constructor
  · intro h
    have ha := (Section03.convergesTo_iff_tendsto.mp h).abs
    have he := EReal.tendsto_coe.mpr ha
    simpa [abs_zero, sequenceLimsup_eq_filter] using he.limsup_eq
  · intro h
    have hc : sequenceLimsup (fun n ↦ |u n|) = ((0 : ℝ) : EReal) := by simpa using h
    have hb := ((sequenceLimsup_eq_coe_iff (fun n ↦ |u n|) 0).mp hc).1
    intro ε hε
    obtain ⟨N, hN, hbound⟩ := hb ε hε
    exact ⟨N, hN, fun n hn ↦ by simpa using hbound n hn⟩

/-- Bài tập 6(a): bất đẳng thức cho liminf của tổng, loại ±∞∓∞. -/
theorem sequenceLiminf_add_ge (u v : ℕ → ℝ)
    (_h : sequenceLiminf u ≠ ⊥ ∨ sequenceLiminf v ≠ ⊤)
    (_h' : sequenceLiminf u ≠ ⊤ ∨ sequenceLiminf v ≠ ⊥) :
    sequenceLiminf u + sequenceLiminf v ≤ sequenceLiminf (fun n ↦ u n + v n) := by
  simp_rw [sequenceLiminf_eq_filter, EReal.coe_add]
  exact EReal.le_liminf_add

/-- Bài tập 6(b): limsup của tổng không vượt tổng limsup khi tổng ấy có nghĩa. -/
theorem sequenceLimsup_add_le (u v : ℕ → ℝ)
    (h : sequenceLimsup u ≠ ⊥ ∨ sequenceLimsup v ≠ ⊤)
    (h' : sequenceLimsup u ≠ ⊤ ∨ sequenceLimsup v ≠ ⊥) :
    sequenceLimsup (fun n ↦ u n + v n) ≤ sequenceLimsup u + sequenceLimsup v := by
  simp_rw [sequenceLimsup_eq_filter] at h h' ⊢
  simp_rw [EReal.coe_add]
  exact EReal.limsup_add_le h h'

/-- Khi dãy thứ nhất hội tụ hữu hạn, cộng nó dịch chính xác liminf và limsup. -/
theorem liminf_limsup_add_of_converges (u v : ℕ → ℝ) (x : ℝ)
    (hu : Section03.ConvergesTo u x) :
    sequenceLiminf (fun n ↦ u n + v n) = (x : EReal) + sequenceLiminf v ∧
      sequenceLimsup (fun n ↦ u n + v n) = (x : EReal) + sequenceLimsup v := by
  have hconv := EReal.tendsto_coe.mpr (Section03.convergesTo_iff_tendsto.mp hu)
  have hadd (a b : ℕ → EReal) : a + b = (fun n ↦ a n + b n) := by
    funext n
    rfl
  have hi := hconv.liminf_eq
  have hs := hconv.limsup_eq
  simp_rw [sequenceLiminf_eq_filter, sequenceLimsup_eq_filter, EReal.coe_add]
  constructor
  · apply le_antisymm
    · have hupper := EReal.liminf_add_le (u := fun n : ℕ ↦ (u n : EReal))
        (v := fun n : ℕ ↦ (v n : EReal)) (f := atTop)
        (Or.inl (hs ▸ EReal.coe_ne_bot x)) (Or.inl (hs ▸ EReal.coe_ne_top x))
      simpa only [hs, hadd] using hupper
    · have hlower := EReal.le_liminf_add (u := fun n : ℕ ↦ (u n : EReal))
        (v := fun n : ℕ ↦ (v n : EReal)) (f := atTop)
      simpa only [hi, hadd] using hlower
  · apply le_antisymm
    · have hupper := EReal.limsup_add_le (u := fun n : ℕ ↦ (u n : EReal))
        (v := fun n : ℕ ↦ (v n : EReal)) (f := atTop)
        (Or.inl (hs ▸ EReal.coe_ne_bot x)) (Or.inl (hs ▸ EReal.coe_ne_top x))
      simpa only [hs, hadd] using hupper
    · have hlower := EReal.le_limsup_add (u := fun n : ℕ ↦ (v n : EReal))
        (v := fun n : ℕ ↦ (u n : EReal)) (f := atTop)
      simpa only [hi, hadd, add_comm] using hlower


theorem tails_tendsto_liminf_limsup (u : ℕ → ℝ) :
    Tendsto (tailInf u) atTop (𝓝 (sequenceLiminf u)) ∧
      Tendsto (tailSup u) atTop (𝓝 (sequenceLimsup u)) := by
  have hi : Monotone (tailInf u) := fun _ _ h ↦ (tail_bounds_mono h).2
  have hs : Antitone (tailSup u) := fun _ _ h ↦ (tail_bounds_mono h).1
  unfold sequenceLiminf sequenceLimsup
  rw [hi.iSup_nat_add 1, hs.iInf_nat_add 1]
  exact ⟨tendsto_atTop_iSup hi, tendsto_atTop_iInf hs⟩

/-- Cận thực m,M cho mọi số hạng tại n≥1. -/
theorem bounded_sequence_range_sup_inf_bounds (u : ℕ → ℝ) (m M : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → m ≤ u n ∧ u n ≤ M) :
    ∀ n : ℕ, 1 ≤ n → m ≤ sInf (Section04.sequenceRangeFromOne u) ∧
      sInf (Section04.sequenceRangeFromOne u) ≤ u n ∧ u n ≤ sSup (Section04.sequenceRangeFromOne u) ∧
      sSup (Section04.sequenceRangeFromOne u) ≤ M := by
  have hne : (Section04.sequenceRangeFromOne u).Nonempty := ⟨u 1, 1, by simp, rfl⟩
  have hbelow : BddBelow (Section04.sequenceRangeFromOne u) := ⟨m, by
    rintro y ⟨n, hn, rfl⟩; exact (h n hn).1⟩
  have habove : BddAbove (Section04.sequenceRangeFromOne u) := ⟨M, by
    rintro y ⟨n, hn, rfl⟩; exact (h n hn).2⟩
  intro n hn
  exact ⟨le_csInf hne (by rintro y ⟨k, hk, rfl⟩; exact (h k hk).1),
    csInf_le hbelow ⟨n, hn, rfl⟩, le_csSup habove ⟨n, hn, rfl⟩,
    csSup_le hne (by rintro y ⟨k, hk, rfl⟩; exact (h k hk).2)⟩

/-- Cận của các đuôi trong `EReal`: m≤tₙ≤uₙ≤sₙ≤M với n dương. -/
theorem bounded_tail_sup_inf_bounds (u : ℕ → ℝ) (m M : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → m ≤ u n ∧ u n ≤ M) (n : ℕ) (hn : 1 ≤ n) :
    (m : EReal) ≤ tailInf u n ∧ tailInf u n ≤ (u n : EReal) ∧
      (u n : EReal) ≤ tailSup u n ∧ tailSup u n ≤ (M : EReal) := by
  refine ⟨?_, (tail_bounds_term u n).1, (tail_bounds_term u n).2, ?_⟩
  · apply le_sInf
    rintro y ⟨k, hk, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (h k (hn.trans hk)).1
  · apply sSup_le
    rintro y ⟨k, hk, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (h k (hn.trans hk)).2

/-- Các cận đuôi của dãy bị chặn là hữu hạn; khi đó dùng `toReal`. -/
theorem bounded_tail_sup_inf_finite (u : ℕ → ℝ) (hu : Section04.SequenceBounded u)
    (n : ℕ) (hn : 1 ≤ n) :
    tailInf u n ≠ ⊥ ∧ tailInf u n ≠ ⊤ ∧ tailSup u n ≠ ⊥ ∧ tailSup u n ≠ ⊤ := by
  obtain ⟨⟨M, hM⟩, ⟨m, hm⟩⟩ := hu
  obtain ⟨hlow, _, _, hhigh⟩ := bounded_tail_sup_inf_bounds u m M (fun n hn ↦ ⟨hm n hn, hM n hn⟩) n hn
  have ht := tail_bounds_term u n
  exact ⟨((EReal.bot_lt_coe m).trans_le hlow).ne',
    (ht.1.trans_lt (EReal.coe_lt_top (u n))).ne,
    ((EReal.bot_lt_coe (u n)).trans_le ht.2).ne',
    (hhigh.trans_lt (EReal.coe_lt_top M)).ne⟩

/-- Dòng 3131–3133: khi dãy bị chặn, cận trên bé nhất và cận dưới lớn nhất thực của các đuôi
hội tụ về limsup và liminf thực. -/
theorem bounded_real_tails_tendsto (u : ℕ → ℝ) (hu : Section04.SequenceBounded u) :
    ∃ s t : ℝ, sequenceLimsup u = s ∧ sequenceLiminf u = t ∧
      Tendsto (fun n ↦ (tailSup u n).toReal) atTop (𝓝 s) ∧
      Tendsto (fun n ↦ (tailInf u n).toReal) atTop (𝓝 t) := by
  have hsTop := ((sequenceBoundedAbove_iff_sequenceLimsup_lt_top u).mp hu.1).ne
  have hiBot := ((sequenceBoundedBelow_iff_bot_lt_sequenceLiminf u).mp hu.2).ne'
  have hsBot := ((sequenceBoundedBelow_iff_bot_lt_sequenceLiminf u).mp hu.2).trans_le
    (sequenceLiminf_le_sequenceLimsup u)
  have hiTop := (sequenceLiminf_le_sequenceLimsup u).trans_lt
    ((sequenceBoundedAbove_iff_sequenceLimsup_lt_top u).mp hu.1)
  refine ⟨(sequenceLimsup u).toReal, (sequenceLiminf u).toReal,
    (EReal.coe_toReal hsTop hsBot.ne').symm, (EReal.coe_toReal hiTop.ne hiBot).symm, ?_, ?_⟩
  · exact (EReal.tendsto_toReal hsTop hsBot.ne').comp (tails_tendsto_liminf_limsup u).2
  · exact (EReal.tendsto_toReal hiTop.ne hiBot).comp (tails_tendsto_liminf_limsup u).1


theorem liminf_limsup_congr (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) :
    sequenceLimsup u = sequenceLimsup v ∧ sequenceLiminf u = sequenceLiminf v := by
  simp_rw [sequenceLimsup_eq_filter, sequenceLiminf_eq_filter]
  have hc := h.mono fun _ hn ↦ congrArg (fun x : ℝ ↦ (x : EReal)) hn
  exact ⟨limsup_congr hc, liminf_congr hc⟩


theorem affine_sequenceSubsequence (u : ℕ → ℝ) (q r : ℕ) (hq : 0 < q) :
    Section04.IsSequenceSubsequence u (fun k ↦ u (q * k + r)) := by
  refine ⟨fun k ↦ q * k + r, ?_, ?_, fun _ _ ↦ rfl⟩
  · intro k hk
    have hqk : q ≤ q * k := by simpa using Nat.mul_le_mul_left q hk
    exact (show 1 ≤ q by omega).trans (hqk.trans (Nat.le_add_right _ _))
  · intro i _ j _ hij
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hij hq) r


theorem liminf_limsup_of_converges (u : ℕ → ℝ) (ℓ : ℝ) (h : Section03.ConvergesTo u ℓ) :
    sequenceLimsup u = (ℓ : EReal) ∧ sequenceLiminf u = (ℓ : EReal) :=
  ((convergesTo_iff_liminf_limsup u ℓ).mp h).symm


theorem liminf_limsup_eq_of_bounds_and_cluster (u : ℕ → ℝ) (m M : ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → m ≤ u n ∧ u n ≤ M)
    (hm : (m : EReal) ∈ extendedSequenceClusterSet u) (hM : (M : EReal) ∈ extendedSequenceClusterSet u) :
    sequenceLimsup u = (M : EReal) ∧ sequenceLiminf u = (m : EReal) := by
  have hlower : (m : EReal) ≤ sequenceLiminf u := by
    rw [sequenceLiminf_eq_filter]
    exact le_liminf_of_le (by isBoundedDefault)
      ((eventually_ge_atTop 1).mono fun n hn ↦ EReal.coe_le_coe_iff.mpr (hbound n hn).1)
  have hupper : sequenceLimsup u ≤ (M : EReal) := by
    rw [sequenceLimsup_eq_filter]
    exact limsup_le_of_le (by isBoundedDefault)
      ((eventually_ge_atTop 1).mono fun n hn ↦ EReal.coe_le_coe_iff.mpr (hbound n hn).2)
  exact ⟨le_antisymm hupper (cluster_point_bounds u M hM).2,
    le_antisymm (cluster_point_bounds u m hm).1 hlower⟩

/-- Ví dụ 2.10.4(a): (−1)ⁿ có limsup=1 và liminf=−1. -/
theorem alternating_one_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ (-1 : ℝ) ^ n) = 1 ∧
      sequenceLiminf (fun n : ℕ ↦ (-1 : ℝ) ^ n) = -1 := by
  have he : Section03.ConvergesTo (fun n : ℕ ↦ (-1 : ℝ) ^ (2 * n)) 1 := by
    apply Section03.convergesTo_iff_tendsto.mpr
    convert tendsto_const_nhds (x := (1 : ℝ)) using 1; simp [pow_mul]
  have ho : Section03.ConvergesTo (fun n : ℕ ↦ (-1 : ℝ) ^ (2 * n + 1)) (-1) := by
    apply Section03.convergesTo_iff_tendsto.mpr
    convert tendsto_const_nhds (x := (-1 : ℝ)) using 1; simp [pow_add, pow_mul]
  apply liminf_limsup_eq_of_bounds_and_cluster _ (-1) 1
  · intro n _
    simpa only [abs_neg_one_pow] using (abs_le.mp (le_of_eq (abs_neg_one_pow (α := ℝ) n)))
  · exact ⟨_, affine_sequenceSubsequence _ 2 1 (by omega), (extendedConvergesTo_coe_iff _ (-1)).mpr ho⟩
  · exact ⟨_, affine_sequenceSubsequence _ 2 0 (by omega), (extendedConvergesTo_coe_iff _ 1).mpr he⟩

/-- Ví dụ 2.10.4(b): 1+1/n có limsup=liminf=1. -/
theorem one_add_reciprocal_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ 1 + 1 / (n : ℝ)) = 1 ∧
      sequenceLiminf (fun n : ℕ ↦ 1 + 1 / (n : ℝ)) = 1 := by
  apply liminf_limsup_of_converges _ 1
  apply Section03.convergesTo_iff_tendsto.mpr
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat

/-- Ví dụ 2.10.5(a): (−1)^n n không bị chặn cả hai phía. -/
theorem alternating_nat_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ (-1 : ℝ) ^ n * n) = ⊤ ∧
      sequenceLiminf (fun n : ℕ ↦ (-1 : ℝ) ^ n * n) = ⊥ :=
  ⟨(not_sequenceBoundedAbove_iff_sequenceLimsup_top _).mp Section04.alternating_nat_sequence_unbounded.1,
    (not_sequenceBoundedBelow_iff_sequenceLiminf_bot _).mp Section04.alternating_nat_sequence_unbounded.2⟩

/-- Ví dụ 2.10.5(b): −n có limsup=liminf=−∞. -/
theorem negative_nat_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ -(n : ℝ)) = ⊥ ∧ sequenceLiminf (fun n : ℕ ↦ -(n : ℝ)) = ⊥ := by
  have hconv : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  exact ((extendedConvergesTo_iff_liminf_limsup _ ⊥).mp
    ((extendedConvergesTo_bot_iff _).mpr hconv)).symm

/-- Dòng 3148: dãy hằng 0 đạt cận trên bé nhất của mọi đuôi. -/
theorem constant_sequence_cannot_be_strictly_below_tail_supremum :
    ¬ ∃ φ : ℕ → ℕ, ∀ k : ℕ, 1 ≤ k →
      (0 : ℝ) < sSup ((fun _ : ℕ ↦ (0 : ℝ)) '' Ici (φ (k - 1) + 1)) := by
  rintro ⟨φ, hφ⟩
  have h := hφ 1 le_rfl
  have himage : ((fun _ : ℕ ↦ (0 : ℝ)) '' Ici (φ (1 - 1) + 1)) = {0} := by
    ext x
    constructor
    · rintro ⟨n, _, rfl⟩; simp
    · intro hx
      exact ⟨φ (1 - 1) + 1, by simp, by simpa using hx.symm⟩
  simp at h

/-
namespace calculus.SourceCorrectionsChapter12

open Set Filter
open scoped Topology BigOperators Pointwise
open calculus.Chapter02.Section03
open calculus.Chapter02.Section06Supplement

/-- C02-S11-theorem-001.proof-strict-tail-supremum: mỗi số hạng không vượt cận trên bé nhất của đuôi. -/
theorem selected_term_le_real_tail_supremum (u : ℕ → ℝ) (N k : ℕ)
    (hb : BddAbove (u '' Ici N)) (hk : N ≤ k) :
    u k ≤ sSup (u '' Ici N) :=
  le_csSup hb ⟨k, hk, rfl⟩

end calculus.SourceCorrectionsChapter12

-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- C02-S11-theorem-001.proof-strict-tail-supremum, dòng 3148: bất đẳng thức ngặt với cận trên bé nhất của đuôi trong lời giải gốc. -/
theorem source_strict_tail_supremum_subsequence (u : ℕ → ℝ) (ℓ : ℝ)
    (hlim : calculus.Chapter02.Section10.sequenceLimsup u = (ℓ : EReal)) :
    ∃ φ : ℕ → ℕ, φ 0 = 0 ∧ StrictMono φ ∧
      ∀ k : ℕ, 1 ≤ k →
        sSup (u '' Ici (φ (k - 1) + 1)) - 1 / (k : ℝ) < u (φ k) ∧
          u (φ k) < sSup (u '' Ici (φ (k - 1) + 1)) := by
  sorry

/-- Bài tập 8: phản ví dụ xₙ=1/n, yₙ=n tại n≥1. -/
theorem nonnegative_product_limsup_counterexample :
    (∀ n : ℕ, 1 ≤ n → 0 ≤ 1 / (n : ℝ) ∧ 0 ≤ (n : ℝ)) ∧
      Section03.ConvergesTo (fun n : ℕ ↦ 1 / (n : ℝ)) 0 ∧
      sequenceLimsup (fun n : ℕ ↦ (n : ℝ)) = ⊤ ∧
      sequenceLimsup (fun n : ℕ ↦ (1 / (n : ℝ)) * n) = 1 ∧
      sequenceLimsup (fun n : ℕ ↦ (1 / (n : ℝ)) * n) ≠ (0 : EReal) * sequenceLimsup (fun n : ℕ ↦ (n : ℝ)) := by
  have hlim : Section03.ConvergesTo (fun n : ℕ ↦ (1 / (n : ℝ)) * n) 1 := by
    apply Section03.convergesTo_iff_tendsto.mpr
    apply tendsto_const_nhds.congr'
    exact (eventually_ge_atTop 1).mono fun n hn ↦ by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      simp [hn0]
  have hprod := (liminf_limsup_of_converges _ 1 hlim).1
  have hnat : sequenceLimsup (fun n : ℕ ↦ (n : ℝ)) = ⊤ :=
    ((extendedConvergesTo_iff_liminf_limsup _ ⊤).mp
      ((extendedConvergesTo_top_iff _).mpr tendsto_natCast_atTop_atTop)).2
  refine ⟨fun n _ ↦ ⟨by positivity, Nat.cast_nonneg _⟩, Section03.reciprocal_converges, hnat, hprod, ?_⟩
  rw [hprod, hnat, zero_mul]
  norm_num

/-- Bài tập 8: limsup của tích hai dãy không âm khi một dãy có giới hạn dương. -/
theorem product_sequenceLimsup_of_positive_limit (u v : ℕ → ℝ) (x : ℝ)
    (hu0 : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n) (hv0 : ∀ n : ℕ, 1 ≤ n → 0 ≤ v n)
    (hu : Section03.ConvergesTo u x) (hx : 0 < x) :
    sequenceLimsup (fun n ↦ u n * v n) = (x : EReal) * sequenceLimsup v := by
  have hmul (a b : ℕ → EReal) : a * b = (fun n ↦ a n * b n) := by
    funext n
    rfl
  have he := EReal.tendsto_coe.mpr (Section03.convergesTo_iff_tendsto.mp hu)
  have hs := he.limsup_eq
  have hi := he.liminf_eq
  have hau : ∀ᶠ n : ℕ in atTop, (0 : EReal) ≤ (u n : EReal) :=
    (eventually_ge_atTop 1).mono fun n hn ↦ EReal.coe_nonneg.mpr (hu0 n hn)
  have hav : ∀ᶠ n : ℕ in atTop, (0 : EReal) ≤ (v n : EReal) :=
    (eventually_ge_atTop 1).mono fun n hn ↦ EReal.coe_nonneg.mpr (hv0 n hn)
  simp_rw [sequenceLimsup_eq_filter, EReal.coe_mul]
  apply le_antisymm
  · have hupper := EReal.limsup_mul_le hau.frequently hav
      (Or.inl (hs ▸ (EReal.coe_pos.mpr hx).ne')) (Or.inl (hs ▸ EReal.coe_ne_top x))
    simpa only [hs, hmul] using hupper
  · have hlower := EReal.le_limsup_mul hav.frequently hau
    simpa only [hi, hmul, mul_comm] using hlower


theorem liminf_limsup_const_mul_nonneg (u : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    sequenceLimsup (fun n ↦ c * u n) = (c : EReal) * sequenceLimsup u ∧
      sequenceLiminf (fun n ↦ c * u n) = (c : EReal) * sequenceLiminf u := by
  simp_rw [sequenceLimsup_eq_filter, sequenceLiminf_eq_filter, EReal.coe_mul]
  exact ⟨EReal.limsup_const_mul_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c),
    EReal.liminf_const_mul_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c)⟩

/-- Bài tập 1(a): giới hạn trên và dưới của tổng hai lũy thừa của −1. -/
theorem alternating_power_sum_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ (-1 : ℝ) ^ n + (-1 : ℝ) ^ (n + 2)) = 2 ∧
      sequenceLiminf (fun n : ℕ ↦ (-1 : ℝ) ^ n + (-1 : ℝ) ^ (n + 2)) = -2 := by
  have heq : (fun n : ℕ ↦ (-1 : ℝ) ^ n + (-1 : ℝ) ^ (n + 2)) =
      (fun n : ℕ ↦ 2 * (-1 : ℝ) ^ n) := by
    funext n
    simp [pow_add]
    ring
  rw [heq]
  have hh := liminf_limsup_const_mul_nonneg (fun n : ℕ ↦ (-1 : ℝ) ^ n) 2 (by norm_num)
  norm_num [alternating_one_liminf_limsup.1, alternating_one_liminf_limsup.2] at hh
  exact hh

/-- Bài tập 2(a): 3−(−1)^n có hai điểm giới hạn 2 và 4. -/
theorem three_sub_alternating_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ 3 - (-1 : ℝ) ^ n) = 4 ∧
      sequenceLiminf (fun n : ℕ ↦ 3 - (-1 : ℝ) ^ n) = 2 := by
  have hconst : Section03.ConvergesTo (fun _ : ℕ ↦ (3 : ℝ)) 3 :=
    Section03.convergesTo_iff_tendsto.mpr tendsto_const_nhds
  have hneg := liminf_limsup_neg (fun n : ℕ ↦ (-1 : ℝ) ^ n)
  have hsum := liminf_limsup_add_of_converges (fun _ : ℕ ↦ (3 : ℝ)) (fun n ↦ -(-1 : ℝ) ^ n) 3 hconst
  have heq : (fun n : ℕ ↦ 3 - (-1 : ℝ) ^ n) = (fun n : ℕ ↦ 3 + -(-1 : ℝ) ^ n) := by
    funext n
    ring
  rw [heq]
  norm_num [hneg.1, hneg.2, alternating_one_liminf_limsup.1, alternating_one_liminf_limsup.2] at hsum
  refine ⟨hsum.2.trans ?_, hsum.1.trans ?_⟩
  · change ((3 : ℝ) : EReal) + ((1 : ℝ) : EReal) = ((4 : ℝ) : EReal)
    rw [← EReal.coe_add]
    norm_num
  · change ((3 : ℝ) : EReal) + ((-1 : ℝ) : EReal) = ((2 : ℝ) : EReal)
    rw [← EReal.coe_add]
    norm_num

/-- Bài tập 6: hai ví dụ bất đẳng thức ngặt với u=(−1)^n,v=−u. -/
theorem alternating_sum_strict_endpoint_inequalities :
    sequenceLiminf (fun n : ℕ ↦ (-1 : ℝ) ^ n) + sequenceLiminf (fun n : ℕ ↦ -(-1 : ℝ) ^ n) <
      sequenceLiminf (fun n : ℕ ↦ (-1 : ℝ) ^ n + -(-1 : ℝ) ^ n) ∧
    sequenceLimsup (fun n : ℕ ↦ (-1 : ℝ) ^ n + -(-1 : ℝ) ^ n) <
      sequenceLimsup (fun n : ℕ ↦ (-1 : ℝ) ^ n) + sequenceLimsup (fun n : ℕ ↦ -(-1 : ℝ) ^ n) := by
  have hzero := liminf_limsup_of_converges (fun n : ℕ ↦ (-1 : ℝ) ^ n + -(-1 : ℝ) ^ n) 0
    (Section03.convergesTo_iff_tendsto.mpr (by simp))
  have hneg := liminf_limsup_neg (fun n : ℕ ↦ (-1 : ℝ) ^ n)
  rw [hneg.1, hneg.2, hzero.1, hzero.2, alternating_one_liminf_limsup.1, alternating_one_liminf_limsup.2]
  norm_num

/-- Dòng 3127: các cận thực m,M tồn tại theo định nghĩa `SequenceBounded`. -/
theorem sequenceBounded_exists_bounds (u : ℕ → ℝ) (hu : Section04.SequenceBounded u) :
    ∃ m M : ℝ, ∀ n : ℕ, 1 ≤ n → m ≤ u n ∧ u n ≤ M := by
  obtain ⟨⟨M, hM⟩, ⟨m, hm⟩⟩ := hu
  exact ⟨m, M, fun n hn ↦ ⟨hm n hn, hM n hn⟩⟩

/-- Dòng 3131: các cận thực của đuôi đơn điệu và bị chặn trên miền chỉ số dương. -/
theorem bounded_real_tails_properties (u : ℕ → ℝ) (hu : Section04.SequenceBounded u) :
    MonotoneOn (fun n ↦ (tailInf u n).toReal) (Ici 1) ∧
      AntitoneOn (fun n ↦ (tailSup u n).toReal) (Ici 1) ∧
      Section04.SequenceBounded (fun n ↦ (tailInf u n).toReal) ∧
      Section04.SequenceBounded (fun n ↦ (tailSup u n).toReal) := by
  obtain ⟨m, M, hbound⟩ := sequenceBounded_exists_bounds u hu
  have hb (n : ℕ) (hn : 1 ≤ n) :
      m ≤ (tailInf u n).toReal ∧ (tailSup u n).toReal ≤ M := by
    obtain ⟨hlo, _, _, hhi⟩ := bounded_tail_sup_inf_bounds u m M hbound n hn
    have hf := bounded_tail_sup_inf_finite u hu n hn
    exact ⟨by simpa using EReal.toReal_le_toReal hlo (EReal.coe_ne_bot m) hf.2.1,
      by simpa using EReal.toReal_le_toReal hhi hf.2.2.1 (EReal.coe_ne_top M)⟩
  have hmiddle (n : ℕ) (hn : 1 ≤ n) : (tailInf u n).toReal ≤ (tailSup u n).toReal :=
    EReal.toReal_le_toReal ((tail_bounds_term u n).1.trans (tail_bounds_term u n).2)
      (bounded_tail_sup_inf_finite u hu n hn).1 (bounded_tail_sup_inf_finite u hu n hn).2.2.2
  refine ⟨?_, ?_, ⟨⟨M, ?_⟩, ⟨m, ?_⟩⟩, ⟨⟨M, ?_⟩, ⟨m, ?_⟩⟩⟩
  · intro i hi j hj hij
    exact EReal.toReal_le_toReal (tail_bounds_mono hij).2
      (bounded_tail_sup_inf_finite u hu i hi).1 (bounded_tail_sup_inf_finite u hu j hj).2.1
  · intro i hi j hj hij
    exact EReal.toReal_le_toReal (tail_bounds_mono hij).1
      (bounded_tail_sup_inf_finite u hu j hj).2.2.1 (bounded_tail_sup_inf_finite u hu i hi).2.2.2
  · intro n hn; exact (hmiddle n hn).trans (hb n hn).2
  · intro n hn; exact (hb n hn).1
  · intro n hn; exact (hb n hn).2
  · intro n hn; exact (hb n hn).1.trans (hmiddle n hn)

/-- Ví dụ 2.10.18(a), Bài tập 1(e): (1+(−1)^n)/n hội tụ 0. -/
theorem alternating_plus_one_div_nat_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ (1 + (-1 : ℝ) ^ n) / n) = 0 ∧
      sequenceLiminf (fun n : ℕ ↦ (1 + (-1 : ℝ) ^ n) / n) = 0 := by
  have hb : Section04.SequenceBounded (fun n : ℕ ↦ 1 + (-1 : ℝ) ^ n) := by
    refine ⟨⟨2, ?_⟩, ⟨0, ?_⟩⟩
    · intro n _; have h := (abs_le.mp (le_of_eq (abs_neg_one_pow (α := ℝ) n))).2; linarith
    · intro n _; have h := (abs_le.mp (le_of_eq (abs_neg_one_pow (α := ℝ) n))).1; linarith
  have hlim := Section04.sequenceBounded_div_nat_pow_tendsto_zero _ hb 1 (by omega)
  simpa only [EReal.coe_zero] using liminf_limsup_of_converges _ 0
    (Section03.convergesTo_iff_tendsto.mpr (by simpa using hlim))

/-- Bài tập 2(e): yₙ/n có limsup=liminf=0 khi y bị chặn. -/
theorem bounded_div_nat_liminf_limsup (u : ℕ → ℝ) (hu : Section04.SequenceBounded u) :
    sequenceLimsup (fun n : ℕ ↦ u n / n) = 0 ∧ sequenceLiminf (fun n : ℕ ↦ u n / n) = 0 := by
  simpa only [EReal.coe_zero] using liminf_limsup_of_converges _ 0
    (Section03.convergesTo_iff_tendsto.mpr (by
      simpa using Section04.sequenceBounded_div_nat_pow_tendsto_zero u hu 1 (by omega)))

/-- Ví dụ 2.10.18(b): −(1+(−1)^n)n có limsup 0 và liminf −∞. -/
theorem negative_even_nat_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ -(1 + (-1 : ℝ) ^ n) * n) = 0 ∧
      sequenceLiminf (fun n : ℕ ↦ -(1 + (-1 : ℝ) ^ n) * n) = ⊥ := by
  have hupper : sequenceLimsup (fun n : ℕ ↦ -(1 + (-1 : ℝ) ^ n) * n) ≤ 0 := by
    rw [sequenceLimsup_eq_filter]
    apply limsup_le_of_le (by isBoundedDefault)
    exact Eventually.of_forall fun n ↦ EReal.coe_nonpos.mpr (mul_nonpos_of_nonpos_of_nonneg
      (by have h := (abs_le.mp (le_of_eq (abs_neg_one_pow (α := ℝ) n))).1; linarith)
      (Nat.cast_nonneg n))
  have hzero : (0 : EReal) ∈ extendedSequenceClusterSet (fun n : ℕ ↦ -(1 + (-1 : ℝ) ^ n) * n) := by
    refine ⟨_, affine_sequenceSubsequence _ 2 1 (by omega), ?_⟩
    apply (extendedConvergesTo_coe_iff _ (0 : ℝ)).mpr
    apply Section03.convergesTo_iff_tendsto.mpr
    convert tendsto_const_nhds (x := (0 : ℝ)) using 1; simp [pow_add, pow_mul]
  have hbelow : ¬ Section04.SequenceBoundedBelow (fun n : ℕ ↦ -(1 + (-1 : ℝ) ^ n) * n) := by
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (|m| + 1)
    have hk1 : 1 ≤ k := by
      have hkpos : (0 : ℝ) < k := lt_trans (by positivity) hk
      exact_mod_cast hkpos
    have hh := hm (2 * k) (by omega)
    norm_num [pow_mul, Nat.cast_mul] at hh
    linarith [neg_abs_le m]
  exact ⟨le_antisymm hupper (cluster_point_bounds _ 0 hzero).2,
    (not_sequenceBoundedBelow_iff_sequenceLiminf_bot _).mp hbelow⟩


theorem nat_div_successor_converges :
    Section03.ConvergesTo (fun n : ℕ ↦ (n : ℝ) / (n + 1)) 1 := by
  have hr : Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp
      ((show StrictMono (fun n : ℕ ↦ n + 1) from fun _ _ h ↦ by dsimp; omega).tendsto_atTop)
  apply Section03.convergesTo_iff_tendsto.mpr
  apply (show Tendsto (fun n : ℕ ↦ 1 - 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) from
    by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hr).congr'
  exact Eventually.of_forall fun n ↦ by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- Bài tập 1(b): 2(−1)^n+n/(n+1) có limsup 3 và liminf −1. -/
theorem twice_alternating_add_ratio_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ 2 * (-1 : ℝ) ^ n + (n : ℝ) / (n + 1)) = 3 ∧
      sequenceLiminf (fun n : ℕ ↦ 2 * (-1 : ℝ) ^ n + (n : ℝ) / (n + 1)) = -1 := by
  have hbase := liminf_limsup_const_mul_nonneg (fun n : ℕ ↦ (-1 : ℝ) ^ n) 2 (by norm_num)
  norm_num [alternating_one_liminf_limsup.1, alternating_one_liminf_limsup.2] at hbase
  have hsum := liminf_limsup_add_of_converges (fun n : ℕ ↦ (n : ℝ) / (n + 1))
    (fun n : ℕ ↦ 2 * (-1 : ℝ) ^ n) 1 nat_div_successor_converges
  simp only [hbase.1, hbase.2, EReal.coe_one] at hsum
  have heq : (fun n : ℕ ↦ 2 * (-1 : ℝ) ^ n + (n : ℝ) / (n + 1)) =
      (fun n : ℕ ↦ (n : ℝ) / (n + 1) + 2 * (-1 : ℝ) ^ n) := by
    funext n
    ring
  rw [heq]
  refine ⟨hsum.2.trans ?_, hsum.1.trans ?_⟩
  · change ((1 : ℝ) : EReal) + ((2 : ℝ) : EReal) = ((3 : ℝ) : EReal)
    rw [← EReal.coe_add]
    norm_num
  · change ((1 : ℝ) : EReal) + ((-2 : ℝ) : EReal) = ((-1 : ℝ) : EReal)
    rw [← EReal.coe_add]
    norm_num

/-- Bài tập 2(b): giới hạn trên và dưới của dãy luân phiên chứa nghịch đảo. -/
theorem shifted_alternating_add_reciprocal_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1) + (-1 : ℝ) ^ n / n) = 1 ∧
      sequenceLiminf (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1) + (-1 : ℝ) ^ n / n) = -1 := by
  have hsum := liminf_limsup_add_of_converges (fun n : ℕ ↦ (-1 : ℝ) ^ n / n)
    (fun n : ℕ ↦ -(-1 : ℝ) ^ n) 0 Section03.alternating_reciprocal_converges
  have hneg := liminf_limsup_neg (fun n : ℕ ↦ (-1 : ℝ) ^ n)
  have heq : (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1) + (-1 : ℝ) ^ n / n) =
      (fun n : ℕ ↦ (-1 : ℝ) ^ n / n + -(-1 : ℝ) ^ n) := by
    funext n
    simp [pow_add]
    ring
  rw [heq]
  simpa [hneg.1, hneg.2, alternating_one_liminf_limsup.1, alternating_one_liminf_limsup.2] using hsum.symm

/-- Mẫu 2n−5 khác 0 với mọi n nguyên dương. -/
theorem quadratic_ratio_denominator_ne_zero (n : ℕ) (_hn : 1 ≤ n) :
    2 * (n : ℝ) - 5 ≠ 0 := by
  intro h
  have hcast : ((2 * n : ℕ) : ℝ) = 5 := by push_cast; linarith
  have hnat : 2 * n = 5 := by exact_mod_cast hcast
  omega

/-- Bài tập 2(c): thương đa thức bậc 2/bậc 1 tiến về +∞. -/
theorem quadratic_ratio_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ (1 + (n : ℝ) ^ 2) / (2 * n - 5)) = ⊤ ∧
      sequenceLiminf (fun n : ℕ ↦ (1 + (n : ℝ) ^ 2) / (2 * n - 5)) = ⊤ := by
  have hconv : Tendsto (fun n : ℕ ↦ (1 + (n : ℝ) ^ 2) / (2 * n - 5)) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    obtain ⟨N, hN⟩ := exists_nat_gt (max 3 (2 * M))
    refine eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    have hreal : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hn3 : (3 : ℝ) ≤ n := by linarith [le_max_left (3 : ℝ) (2 * M)]
    have hden : 0 < 2 * (n : ℝ) - 5 := by linarith
    have hlow : (n : ℝ) / 2 ≤ (1 + (n : ℝ) ^ 2) / (2 * n - 5) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith
    linarith [le_max_right (3 : ℝ) (2 * M)]
  exact ((extendedConvergesTo_iff_liminf_limsup _ ⊤).mp
    ((extendedConvergesTo_top_iff _).mpr hconv)).symm

/-- Bài tập 2(d): thương đa thức bậc 3/bậc 2 tiến về +∞, với mẫu luôn dương. -/
theorem cubic_ratio_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ ((n : ℝ) ^ 3 + n ^ 2 - n + 1) / (n ^ 2 + 2 * n + 5)) = ⊤ ∧
      sequenceLiminf (fun n : ℕ ↦ ((n : ℝ) ^ 3 + n ^ 2 - n + 1) / (n ^ 2 + 2 * n + 5)) = ⊤ := by
  have hconv : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ 3 + n ^ 2 - n + 1) / (n ^ 2 + 2 * n + 5)) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    obtain ⟨N, hN⟩ := exists_nat_gt (max 3 (2 * M))
    refine eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    have hreal : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hn3 : (3 : ℝ) ≤ n := by linarith [le_max_left (3 : ℝ) (2 * M)]
    have hden : 0 < (n : ℝ) ^ 2 + 2 * n + 5 := by positivity
    have hsq : (9 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hcube := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hlow : (n : ℝ) / 2 ≤ ((n : ℝ) ^ 3 + n ^ 2 - n + 1) / (n ^ 2 + 2 * n + 5) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith
    linarith [le_max_right (3 : ℝ) (2 * M)]
  exact ((extendedConvergesTo_iff_liminf_limsup _ ⊤).mp
    ((extendedConvergesTo_top_iff _).mpr hconv)).symm


theorem periodic_extendedSequenceClusterSet (u : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (f : Fin q → ℝ)
    (hterm : ∀ n : ℕ, 1 ≤ n → u n = f ⟨n % q, Nat.mod_lt n hq⟩) :
    extendedSequenceClusterSet u = range (fun r : Fin q ↦ (f r : EReal)) := by
  ext ℓ
  constructor
  · intro h
    apply (Set.finite_range (fun r : Fin q ↦ (f r : EReal))).isClosed.mem_of_mapClusterPt
      ((mem_extendedSequenceClusterSet_iff u ℓ).mp h)
    exact (eventually_ge_atTop 1).mono fun n hn ↦ ⟨⟨n % q, Nat.mod_lt n hq⟩,
      congrArg (fun x : ℝ ↦ (x : EReal)) (hterm n hn).symm⟩
  · rintro ⟨r, rfl⟩
    refine ⟨_, affine_sequenceSubsequence u q r hq, ?_⟩
    apply EReal.tendsto_coe.mpr
    apply tendsto_const_nhds.congr'
    exact (eventually_ge_atTop 1).mono fun k hk ↦ by
      have hqk : q ≤ q * k := by simpa using Nat.mul_le_mul_left q hk
      have hpos : 1 ≤ q * k + r := (show 1 ≤ q by omega).trans (hqk.trans (Nat.le_add_right _ _))
      have hr : (⟨(q * k + r) % q, Nat.mod_lt _ hq⟩ : Fin q) = r := by
        apply Fin.ext
        simp [Nat.add_mod, Nat.mod_eq_of_lt r.isLt]
      simp only [hterm _ hpos, hr]


theorem cosine_half_pi_residue_formula (n : ℕ) :
    Real.cos ((n : ℝ) * Real.pi / 2) =
      (![1, 0, -1, 0] : Fin 4 → ℝ) ⟨n % 4, Nat.mod_lt n (by omega)⟩ := by
  have hcast : (n : ℝ) = (n % 4 : ℕ) + 4 * ((n / 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n 4).symm
  have hangle : (n : ℝ) * Real.pi / 2 =
      ((n % 4 : ℕ) : ℝ) * Real.pi / 2 + ((n / 4 : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hcast]
    ring
  rw [hangle, Real.cos_add_nat_mul_two_pi]
  have hres (r : Fin 4) : Real.cos ((r : ℝ) * Real.pi / 2) =
      (![1, 0, -1, 0] : Fin 4 → ℝ) r := by
    fin_cases r
    · norm_num
    · simp
    · simp
    · have heq : (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
      simp [heq, Real.cos_add_pi]
  exact hres ⟨n % 4, Nat.mod_lt n (by omega)⟩

/-- Bài tập 1(d): cos(nπ/2) có limsup=1 và liminf=−1. -/
theorem cosine_half_pi_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ Real.cos ((n : ℝ) * Real.pi / 2)) = 1 ∧
      sequenceLiminf (fun n : ℕ ↦ Real.cos ((n : ℝ) * Real.pi / 2)) = -1 := by
  have hs := periodic_extendedSequenceClusterSet (fun n : ℕ ↦ Real.cos ((n : ℝ) * Real.pi / 2))
    4 (by omega) (![1, 0, -1, 0] : Fin 4 → ℝ) (fun n _ ↦ cosine_half_pi_residue_formula n)
  have hmax := sequenceLimsup_isGreatest_clusterSet (fun n : ℕ ↦ Real.cos ((n : ℝ) * Real.pi / 2))
  have hmin := sequenceLiminf_isLeast_clusterSet (fun n : ℕ ↦ Real.cos ((n : ℝ) * Real.pi / 2))
  rw [hs] at hmax hmin
  have hg : IsGreatest (range (fun r : Fin 4 ↦ ((![1, 0, -1, 0] : Fin 4 → ℝ) r : EReal))) 1 := by
    refine ⟨⟨0, by simp⟩, ?_⟩
    rintro _ ⟨r, rfl⟩
    fin_cases r <;> norm_num
    all_goals exact EReal.coe_le_coe_iff.mpr (by norm_num : (-1 : ℝ) ≤ 1)
  have hl : IsLeast (range (fun r : Fin 4 ↦ ((![1, 0, -1, 0] : Fin 4 → ℝ) r : EReal))) (-1) := by
    refine ⟨⟨2, by simp⟩, ?_⟩
    rintro _ ⟨r, rfl⟩
    fin_cases r <;> norm_num
    all_goals exact EReal.coe_le_coe_iff.mpr (by norm_num : (-1 : ℝ) ≤ 1)
  exact ⟨hmax.unique hg, hmin.unique hl⟩


theorem extendedSequenceClusterSet_add_vanishing (u v : ℕ → ℝ)
    (hv : Section03.ConvergesTo v 0) :
    extendedSequenceClusterSet (fun n ↦ u n + v n) = extendedSequenceClusterSet u := by
  have hsubset (a b : ℕ → ℝ) (hb : Section03.ConvergesTo b 0) :
      extendedSequenceClusterSet a ⊆ extendedSequenceClusterSet (fun n ↦ a n + b n) := by
    rintro ℓ ⟨w, ⟨φ, hpos, hmono, hterm⟩, hw⟩
    have hφ := Section04.subsequence_index_tendsto φ hpos hmono
    have ha : Tendsto (fun k ↦ (a (φ k) : EReal)) atTop (𝓝 ℓ) :=
      hw.congr' ((eventually_ge_atTop 1).mono fun k hk ↦
        congrArg (fun x : ℝ ↦ (x : EReal)) (hterm k hk))
    have hbt : Tendsto (fun k ↦ (b (φ k) : EReal)) atTop (𝓝 (0 : EReal)) := by
      exact ((EReal.tendsto_coe.mpr (Section03.convergesTo_iff_tendsto.mp hb)).comp hφ).congr
        (fun _ ↦ rfl)
    refine ⟨(fun n ↦ a n + b n) ∘ φ, ⟨φ, hpos, hmono, fun _ _ ↦ rfl⟩, ?_⟩
    have hcont : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (ℓ, 0) :=
      EReal.continuousAt_add (Or.inr (by norm_num)) (Or.inr (by norm_num))
    have hadd : Tendsto (fun n ↦ (a (φ n) : EReal) + (b (φ n) : EReal)) atTop (𝓝 (ℓ + 0)) :=
      (hcont.tendsto.comp (ha.prodMk_nhds hbt)).congr (fun _ ↦ rfl)
    have hadd0 : Tendsto (fun n ↦ (a (φ n) : EReal) + (b (φ n) : EReal)) atTop (𝓝 ℓ) := by
      simpa only [add_zero] using hadd
    exact hadd0.congr (fun n ↦ (EReal.coe_add (a (φ n)) (b (φ n))).symm)
  apply Subset.antisymm
  · have hneg : Section03.ConvergesTo (fun n ↦ -v n) 0 :=
      Section03.convergesTo_iff_tendsto.mpr (by
        simpa using (Section03.convergesTo_iff_tendsto.mp hv).neg)
    simpa only [add_neg_cancel_right] using hsubset (fun n ↦ u n + v n) (fun n ↦ -v n) hneg
  · exact hsubset u v hv


theorem sine_half_pi_residue_formula (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi / 2) =
      (![0, 1, 0, -1] : Fin 4 → ℝ) ⟨n % 4, Nat.mod_lt n (by omega)⟩ := by
  have hcast : (n : ℝ) = (n % 4 : ℕ) + 4 * ((n / 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n 4).symm
  have hangle : (n : ℝ) * Real.pi / 2 =
      ((n % 4 : ℕ) : ℝ) * Real.pi / 2 + ((n / 4 : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hcast]
    ring
  rw [hangle, Real.sin_add_nat_mul_two_pi]
  have hres (r : Fin 4) : Real.sin ((r : ℝ) * Real.pi / 2) =
      (![0, 1, 0, -1] : Fin 4 → ℝ) r := by
    fin_cases r
    · norm_num
    · simp
    · simp
    · have heq : (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
      simp [heq, Real.sin_add_pi]
  exact hres ⟨n % 4, Nat.mod_lt n (by omega)⟩

/-- Bài tập 1(c): sin(nπ/3) nhận các giá trị theo chu kì sáu số hạng. -/
theorem sine_third_pi_residue_formula (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi / 3) =
      (![0, Real.sqrt 3 / 2, Real.sqrt 3 / 2, 0, -(Real.sqrt 3 / 2), -(Real.sqrt 3 / 2)] :
        Fin 6 → ℝ) ⟨n % 6, Nat.mod_lt n (by omega)⟩ := by
  have hcast : (n : ℝ) = (n % 6 : ℕ) + 6 * ((n / 6 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n 6).symm
  have hangle : (n : ℝ) * Real.pi / 3 =
      ((n % 6 : ℕ) : ℝ) * Real.pi / 3 + ((n / 6 : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hcast]
    ring
  rw [hangle, Real.sin_add_nat_mul_two_pi]
  have hres (r : Fin 6) : Real.sin ((r : ℝ) * Real.pi / 3) =
      (![0, Real.sqrt 3 / 2, Real.sqrt 3 / 2, 0, -(Real.sqrt 3 / 2), -(Real.sqrt 3 / 2)] :
        Fin 6 → ℝ) r := by
    fin_cases r
    · norm_num
    · simp [Real.sin_pi_div_three]
    · have heq : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      simp [heq, Real.sin_pi_sub, Real.sin_pi_div_three]
    · simp
    · have heq : (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
      simp [heq, Real.sin_add_pi, Real.sin_pi_div_three]
    · have heq : (5 : ℝ) * Real.pi / 3 = (Real.pi - Real.pi / 3) + Real.pi := by ring
      simp [heq, Real.sin_add_pi, Real.sin_pi_sub, Real.sin_pi_div_three]
  exact hres ⟨n % 6, Nat.mod_lt n (by omega)⟩

/-- Bài tập 1(c): giới hạn trên và dưới của sin(nπ/3). -/
theorem sine_third_pi_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ Real.sin ((n : ℝ) * Real.pi / 3)) = ((Real.sqrt 3 / 2 : ℝ) : EReal) ∧
      sequenceLiminf (fun n : ℕ ↦ Real.sin ((n : ℝ) * Real.pi / 3)) = ((-(Real.sqrt 3 / 2) : ℝ) : EReal) := by
  let f : Fin 6 → ℝ := ![0, Real.sqrt 3 / 2, Real.sqrt 3 / 2, 0, -(Real.sqrt 3 / 2), -(Real.sqrt 3 / 2)]
  have hs := periodic_extendedSequenceClusterSet (fun n : ℕ ↦ Real.sin ((n : ℝ) * Real.pi / 3))
    6 (by omega) f (fun n _ ↦ sine_third_pi_residue_formula n)
  have hmax := sequenceLimsup_isGreatest_clusterSet (fun n : ℕ ↦ Real.sin ((n : ℝ) * Real.pi / 3))
  have hmin := sequenceLiminf_isLeast_clusterSet (fun n : ℕ ↦ Real.sin ((n : ℝ) * Real.pi / 3))
  rw [hs] at hmax hmin
  have hp : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
  have hg : IsGreatest (range (fun r : Fin 6 ↦ (f r : EReal))) ((Real.sqrt 3 / 2 : ℝ) : EReal) := by
    refine ⟨⟨1, by simp [f]⟩, ?_⟩
    rintro _ ⟨r, rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    fin_cases r <;> (dsimp [f]; linarith)
  have hl : IsLeast (range (fun r : Fin 6 ↦ (f r : EReal))) ((-(Real.sqrt 3 / 2) : ℝ) : EReal) := by
    refine ⟨⟨4, by simp [f]⟩, ?_⟩
    rintro _ ⟨r, rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    fin_cases r <;> (dsimp [f]; linarith)
  exact ⟨hmax.unique hg, hmin.unique hl⟩

/-- Bài tập 1(f): các dãy con n=4k+1 và n=4k+3 tiến về hai hướng vô cùng đối nhau. -/
theorem nat_mul_sine_half_pi_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2)) = ⊤ ∧
      sequenceLiminf (fun n : ℕ ↦ (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2)) = ⊥ := by
  have hsin (k r : ℕ) : Real.sin (((4 * k + r : ℕ) : ℝ) * Real.pi / 2) =
      Real.sin ((r : ℝ) * Real.pi / 2) := by
    have heq : (((4 * k + r : ℕ) : ℝ) * Real.pi / 2) =
        (r : ℝ) * Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [heq, Real.sin_add_nat_mul_two_pi]
  have he : Tendsto (fun k : ℕ ↦ (4 * k + 1 : ℕ) * Real.sin (((4 * k + 1 : ℕ) : ℝ) * Real.pi / 2))
      atTop atTop := by
    have hc : Tendsto (fun k : ℕ ↦ ((4 * k + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp ((show StrictMono (fun k : ℕ ↦ 4 * k + 1) from
        fun _ _ h ↦ by dsimp; omega).tendsto_atTop)).congr (fun _ ↦ rfl)
    simpa only [hsin, Nat.cast_one, one_mul, Real.sin_pi_div_two, mul_one] using hc
  have ho : Tendsto (fun k : ℕ ↦ (4 * k + 3 : ℕ) * Real.sin (((4 * k + 3 : ℕ) : ℝ) * Real.pi / 2))
      atTop atBot := by
    have hs : Real.sin ((3 : ℝ) * Real.pi / 2) = -1 := by
      have heq : (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
      simp [heq, Real.sin_add_pi]
    have hc : Tendsto (fun k : ℕ ↦ -((4 * k + 3 : ℕ) : ℝ)) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.comp
        ((show StrictMono (fun k : ℕ ↦ 4 * k + 3) from fun _ _ h ↦ by dsimp; omega).tendsto_atTop))).congr (fun _ ↦ rfl)
    simpa only [hsin, Nat.cast_ofNat, hs, mul_neg_one] using hc
  exact ⟨(sequenceLimsup_top_iff_subsequence_atTop _).mpr
      ⟨_, affine_sequenceSubsequence _ 4 1 (by omega), he⟩,
    (sequenceLiminf_bot_iff_subsequence_atBot _).mpr
      ⟨_, affine_sequenceSubsequence _ 4 3 (by omega), ho⟩⟩

/-- Tổng x₁+…+xₙ. -/
noncomputable def partialSumFromOne (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, u (k + 1)

/-- Tổng từ x₁ đến xₙ thỏa truy hồi thêm số hạng xₙ₊₁. -/
theorem partialSumFromOne_succ (u : ℕ → ℝ) (n : ℕ) :
    partialSumFromOne u (n + 1) = partialSumFromOne u n + u (n + 1) := by
  exact Finset.sum_range_succ _ n

/-- Các trung bình cộng trong Bài tập 12. -/
noncomputable def cesaroMean (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * partialSumFromOne u n


theorem cesaroMean_converges (u : ℕ → ℝ) (a : ℝ) (h : Section03.ConvergesTo u a) :
    Section03.ConvergesTo (cesaroMean u) a := by
  apply Section03.convergesTo_iff_tendsto.mpr
  have hshift := (Section03.convergesTo_iff_tendsto.mp h).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n : ℕ ↦ (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, u (k + 1)) atTop (𝓝 a)
  simpa only [one_div, Function.comp_apply] using hshift.cesaro


theorem cesaroMean_mono (u v : ℕ → ℝ) (h : ∀ n : ℕ, 1 ≤ n → u n ≤ v n) :
    ∀ n : ℕ, cesaroMean u n ≤ cesaroMean v n := by
  intro n
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro k _
  exact h (k + 1) (by omega)

/-- Bài tập 12: chuỗi bất đẳng thức giữa bốn giới hạn trên, giới hạn dưới,
kể cả khi có giá trị vô cùng. -/
theorem cesaroMean_liminf_limsup_chain (u : ℕ → ℝ) :
    sequenceLiminf u ≤ sequenceLiminf (cesaroMean u) ∧
      sequenceLiminf (cesaroMean u) ≤ sequenceLimsup (cesaroMean u) ∧
      sequenceLimsup (cesaroMean u) ≤ sequenceLimsup u := by
  refine ⟨?_, sequenceLiminf_le_sequenceLimsup _, ?_⟩
  · by_contra hnot
    obtain ⟨a, hma, hau⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
    have he : ∀ᶠ n : ℕ in atTop, (a : EReal) < (u n : EReal) := by
      rw [sequenceLiminf_eq_filter] at hau
      exact eventually_lt_of_lt_liminf hau
    have hm : Section03.ConvergesTo (fun n ↦ min (u n) a) a := by
      apply Section03.convergesTo_iff_tendsto.mpr
      apply tendsto_const_nhds.congr'
      exact he.mono fun n hn ↦ (min_eq_right (EReal.coe_lt_coe_iff.mp hn).le).symm
    have hmean := (liminf_limsup_of_converges _ a (cesaroMean_converges _ a hm)).2
    have hmono := (liminf_limsup_mono_of_eventually_le _ _ (Eventually.of_forall
      (cesaroMean_mono (fun n ↦ min (u n) a) u (fun n _ ↦ min_le_left _ _)))).2
    rw [hmean] at hmono
    exact (not_le_of_gt hma) hmono
  · by_contra hnot
    obtain ⟨a, hua, ham⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
    have he : ∀ᶠ n : ℕ in atTop, (u n : EReal) < (a : EReal) := by
      rw [sequenceLimsup_eq_filter] at hua
      exact eventually_lt_of_limsup_lt hua
    have hm : Section03.ConvergesTo (fun n ↦ max (u n) a) a := by
      apply Section03.convergesTo_iff_tendsto.mpr
      apply tendsto_const_nhds.congr'
      exact he.mono fun n hn ↦ (max_eq_right (EReal.coe_lt_coe_iff.mp hn).le).symm
    have hmean := (liminf_limsup_of_converges _ a (cesaroMean_converges _ a hm)).1
    have hmono := (liminf_limsup_mono_of_eventually_le _ _ (Eventually.of_forall
      (cesaroMean_mono u (fun n ↦ max (u n) a) (fun n _ ↦ le_max_left _ _)))).1
    rw [hmean] at hmono
    exact (not_le_of_gt ham) hmono


theorem extendedSequenceClusterSet_congr (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) :
    extendedSequenceClusterSet u = extendedSequenceClusterSet v := by
  ext ℓ
  simp only [mem_extendedSequenceClusterSet_iff]
  have hc : (fun n ↦ (u n : EReal)) =ᶠ[atTop] (fun n ↦ (v n : EReal)) :=
    h.mono fun _ hn ↦ congrArg (fun x : ℝ ↦ (x : EReal)) hn
  exact Filter.EventuallyEq.mapClusterPt_iff hc


theorem one_add_twice_alternating_residue_formula (n : ℕ) :
    1 + 2 * (-1 : ℝ) ^ n =
      (![3, -1] : Fin 2 → ℝ) ⟨n % 2, Nat.mod_lt n (by omega)⟩ := by
  have halt : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n % 2) := by
    rw [← Nat.mod_add_div n 2]
    simp [pow_add, pow_mul]
  rw [halt]
  have hres (r : Fin 2) : 1 + 2 * (-1 : ℝ) ^ (r : ℕ) = (![3, -1] : Fin 2 → ℝ) r := by
    fin_cases r <;> norm_num
  exact hres ⟨n % 2, Nat.mod_lt n (by omega)⟩

/-- Ví dụ 2.10.18(c): dãy có hai điểm giới hạn −1 và 3. -/
theorem alternating_double_ratio_clusterSet :
    extendedSequenceClusterSet (fun n : ℕ ↦ 1 + (-1 : ℝ) ^ n * (2 * n / (n + 1))) =
      {(-1 : EReal), 3} := by
  let u : ℕ → ℝ := fun n ↦ 1 + 2 * (-1 : ℝ) ^ n
  let v : ℕ → ℝ := fun n ↦ -2 * (-1 : ℝ) ^ n / (n + 1)
  have hv : Section03.ConvergesTo v 0 := by
    apply Section03.convergesTo_of_error_le_const_div (C := 2) (by norm_num)
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    norm_num [v, abs_div, abs_mul, abs_neg_one_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)]
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hnpos (by linarith)
  have heq : (fun n : ℕ ↦ 1 + (-1 : ℝ) ^ n * (2 * n / (n + 1))) =
      (fun n ↦ u n + v n) := by
    funext n
    dsimp [u, v]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [heq, extendedSequenceClusterSet_add_vanishing u v hv]
  have hp := periodic_extendedSequenceClusterSet u 2 (by omega) (![3, -1] : Fin 2 → ℝ)
    (fun n _ ↦ one_add_twice_alternating_residue_formula n)
  rw [hp]
  ext ℓ
  constructor
  · rintro ⟨r, rfl⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    fin_cases r
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

/-- Ví dụ 2.10.18(c): giá trị limsup và liminf. -/
theorem alternating_double_ratio_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ 1 + (-1 : ℝ) ^ n * (2 * n / (n + 1))) = 3 ∧
      sequenceLiminf (fun n : ℕ ↦ 1 + (-1 : ℝ) ^ n * (2 * n / (n + 1))) = -1 := by
  have hmax := sequenceLimsup_isGreatest_clusterSet (fun n : ℕ ↦ 1 + (-1 : ℝ) ^ n * (2 * n / (n + 1)))
  have hmin := sequenceLiminf_isLeast_clusterSet (fun n : ℕ ↦ 1 + (-1 : ℝ) ^ n * (2 * n / (n + 1)))
  rw [alternating_double_ratio_clusterSet] at hmax hmin
  have hle : (-1 : EReal) ≤ 3 := EReal.coe_le_coe_iff.mpr (by norm_num : (-1 : ℝ) ≤ 3)
  exact ⟨hmax.unique ⟨by simp, by rintro x (rfl | rfl) <;> simp [hle]⟩,
    hmin.unique ⟨by simp, by rintro x (rfl | rfl) <;> simp [hle]⟩⟩


theorem sine_half_pi_affine (k r : ℕ) :
    Real.sin (((4 * k + r : ℕ) : ℝ) * Real.pi / 2) = Real.sin ((r : ℝ) * Real.pi / 2) := by
  have heq : (((4 * k + r : ℕ) : ℝ) * Real.pi / 2) =
      (r : ℝ) * Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by push_cast; ring
  rw [heq, Real.sin_add_nat_mul_two_pi]

/-- Ví dụ 2.10.18(d): giới hạn trên và dưới của n^{sin(nπ/2)}. -/
theorem nat_rpow_sine_half_pi_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ (n : ℝ) ^ Real.sin ((n : ℝ) * Real.pi / 2)) = ⊤ ∧
      sequenceLiminf (fun n : ℕ ↦ (n : ℝ) ^ Real.sin ((n : ℝ) * Real.pi / 2)) = 0 := by
  have htop : sequenceLimsup (fun n : ℕ ↦ (n : ℝ) ^ Real.sin ((n : ℝ) * Real.pi / 2)) = ⊤ := by
    apply (sequenceLimsup_top_iff_subsequence_atTop _).mpr
    refine ⟨_, affine_sequenceSubsequence _ 4 1 (by omega), ?_⟩
    have hc : Tendsto (fun k : ℕ ↦ ((4 * k + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp ((show StrictMono (fun k : ℕ ↦ 4 * k + 1) from
        fun _ _ h ↦ by dsimp; omega).tendsto_atTop)).congr (fun _ ↦ rfl)
    simpa only [sine_half_pi_affine, Nat.cast_one, one_mul, Real.sin_pi_div_two, Real.rpow_one] using hc
  have hzero : (0 : EReal) ∈ extendedSequenceClusterSet
      (fun n : ℕ ↦ (n : ℝ) ^ Real.sin ((n : ℝ) * Real.pi / 2)) := by
    refine ⟨_, affine_sequenceSubsequence _ 4 3 (by omega), ?_⟩
    apply (extendedConvergesTo_coe_iff _ (0 : ℝ)).mpr
    apply Section03.convergesTo_iff_tendsto.mpr
    have hs : Real.sin ((3 : ℝ) * Real.pi / 2) = -1 := by
      have heq : (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
      simp [heq, Real.sin_add_pi]
    have hc : Tendsto (fun k : ℕ ↦ (((4 * k + 3 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
      (tendsto_one_div_atTop_nhds_zero_nat.comp ((show StrictMono (fun k : ℕ ↦ 4 * k + 3) from
        fun _ _ h ↦ by dsimp; omega).tendsto_atTop)).congr (fun _ ↦ by simp only [Function.comp_apply, one_div])
    simpa only [sine_half_pi_affine, Nat.cast_ofNat, hs, Real.rpow_neg_one] using hc
  have hnonneg : (0 : EReal) ≤ sequenceLiminf
      (fun n : ℕ ↦ (n : ℝ) ^ Real.sin ((n : ℝ) * Real.pi / 2)) := by
    rw [sequenceLiminf_eq_filter]
    exact le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦
      EReal.coe_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  exact ⟨htop, le_antisymm (cluster_point_bounds _ 0 hzero).1 hnonneg⟩

/-- Bảng bốn lớp chỉ số của dãy trước khi thêm nhiễu trong Ví dụ 2.10.18(e). -/
theorem alternating_sine_residue_formula (n : ℕ) :
    3 * (-1 : ℝ) ^ n + 2 * Real.sin ((n : ℝ) * Real.pi / 2) =
      (![3, -1, 3, -5] : Fin 4 → ℝ) ⟨n % 4, Nat.mod_lt n (by omega)⟩ := by
  have halt : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n % 4) := by
    rw [← Nat.mod_add_div n 4]
    norm_num [pow_add, pow_mul]
  rw [halt, sine_half_pi_residue_formula]
  have hres (r : Fin 4) :
      3 * (-1 : ℝ) ^ (r : ℕ) + 2 * (![0, 1, 0, -1] : Fin 4 → ℝ) r =
        (![3, -1, 3, -5] : Fin 4 → ℝ) r := by
    fin_cases r <;> norm_num
  exact hres ⟨n % 4, Nat.mod_lt n (by omega)⟩

/-- Ví dụ 2.10.18(e): tập các điểm giới hạn mở rộng. -/
theorem alternating_sine_reciprocal_clusterSet :
    extendedSequenceClusterSet (fun n : ℕ ↦ 3 * (-1 : ℝ) ^ n + 1 / n + 2 * Real.sin ((n : ℝ) * Real.pi / 2)) =
      {(-5 : EReal), -1, 3} := by
  let u : ℕ → ℝ := fun n ↦ 3 * (-1 : ℝ) ^ n + 2 * Real.sin ((n : ℝ) * Real.pi / 2)
  have heq : (fun n : ℕ ↦ 3 * (-1 : ℝ) ^ n + 1 / n + 2 * Real.sin ((n : ℝ) * Real.pi / 2)) =
      (fun n ↦ u n + 1 / n) := by funext n; dsimp [u]; ring
  rw [heq, extendedSequenceClusterSet_add_vanishing u _ Section03.reciprocal_converges]
  have hp := periodic_extendedSequenceClusterSet u 4 (by omega) (![3, -1, 3, -5] : Fin 4 → ℝ)
    (fun n _ ↦ alternating_sine_residue_formula n)
  rw [hp]
  ext ℓ
  constructor
  · rintro ⟨r, rfl⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    fin_cases r
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
  · intro h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨3, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

/-- Ví dụ 2.10.18(e): giá trị limsup và liminf. -/
theorem alternating_sine_reciprocal_liminf_limsup :
    sequenceLimsup (fun n : ℕ ↦ 3 * (-1 : ℝ) ^ n + 1 / n + 2 * Real.sin ((n : ℝ) * Real.pi / 2)) = 3 ∧
      sequenceLiminf (fun n : ℕ ↦ 3 * (-1 : ℝ) ^ n + 1 / n + 2 * Real.sin ((n : ℝ) * Real.pi / 2)) = -5 := by
  have hmax := sequenceLimsup_isGreatest_clusterSet
    (fun n : ℕ ↦ 3 * (-1 : ℝ) ^ n + 1 / n + 2 * Real.sin ((n : ℝ) * Real.pi / 2))
  have hmin := sequenceLiminf_isLeast_clusterSet
    (fun n : ℕ ↦ 3 * (-1 : ℝ) ^ n + 1 / n + 2 * Real.sin ((n : ℝ) * Real.pi / 2))
  rw [alternating_sine_reciprocal_clusterSet] at hmax hmin
  have hm1 : (-5 : EReal) ≤ -1 := EReal.coe_le_coe_iff.mpr (by norm_num : (-5 : ℝ) ≤ -1)
  have hm3 : (-5 : EReal) ≤ 3 := EReal.coe_le_coe_iff.mpr (by norm_num : (-5 : ℝ) ≤ 3)
  have h13 : (-1 : EReal) ≤ 3 := EReal.coe_le_coe_iff.mpr (by norm_num : (-1 : ℝ) ≤ 3)
  exact ⟨hmax.unique ⟨by simp, by rintro x (rfl | rfl | rfl) <;> simp [hm3, h13]⟩,
    hmin.unique ⟨by simp, by rintro x (rfl | rfl | rfl) <;> simp [hm1, hm3]⟩⟩


theorem nonnegative_product_one_finite (a b : EReal) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hprod : a * b = 1) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ a = s ∧ b = t ∧ s * t = 1 := by
  have ha0 : a ≠ 0 := by intro h; rw [h, zero_mul] at hprod; norm_num at hprod
  have hb0 : b ≠ 0 := by intro h; rw [h, mul_zero] at hprod; norm_num at hprod
  have hap : 0 < a := lt_of_le_of_ne ha ha0.symm
  have hbp : 0 < b := lt_of_le_of_ne hb hb0.symm
  have haTop : a ≠ ⊤ := by
    intro h
    rw [h, EReal.top_mul_of_pos hbp] at hprod
    exact (EReal.coe_ne_top 1) hprod.symm
  have hbTop : b ≠ ⊤ := by
    intro h
    rw [h, EReal.mul_top_of_pos hap] at hprod
    exact (EReal.coe_ne_top 1) hprod.symm
  have haBot : a ≠ ⊥ := ((show (⊥ : EReal) < 0 by exact EReal.bot_lt_coe 0).trans hap).ne'
  have hbBot : b ≠ ⊥ := ((show (⊥ : EReal) < 0 by exact EReal.bot_lt_coe 0).trans hbp).ne'
  have hsa : a = (a.toReal : EReal) := (EReal.coe_toReal haTop haBot).symm
  have htb : b = (b.toReal : EReal) := (EReal.coe_toReal hbTop hbBot).symm
  refine ⟨a.toReal, b.toReal, ?_, ?_, hsa, htb, ?_⟩
  · exact EReal.coe_pos.mp (hsa ▸ hap)
  · exact EReal.coe_pos.mp (htb ▸ hbp)
  · apply EReal.coe_injective
    simpa only [EReal.coe_mul] using hsa ▸ htb ▸ hprod

/-- Bài tập 10: giả thiết về tích các giới hạn mở rộng suy ra giới hạn hữu hạn dương. -/
theorem positive_sequence_converges_of_limsup_mul_limsup_reciprocal_eq_one (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n → 0 < u n)
    (hprod : sequenceLimsup u * sequenceLimsup (fun n ↦ 1 / u n) = 1) :
    ∃ a : ℝ, 0 < a ∧ Section03.ConvergesTo u a := by
  have hnonneg (v : ℕ → ℝ) (hv : ∀ n : ℕ, 1 ≤ n → 0 ≤ v n) :
      (0 : EReal) ≤ sequenceLimsup v := by
    apply le_trans _ (sequenceLiminf_le_sequenceLimsup v)
    rw [sequenceLiminf_eq_filter]
    exact le_liminf_of_le (by isBoundedDefault) ((eventually_ge_atTop 1).mono fun n hn ↦
      EReal.coe_nonneg.mpr (hv n hn))
  obtain ⟨s, t, hspos, htpos, hs, ht, hst⟩ := nonnegative_product_one_finite
    (sequenceLimsup u) (sequenceLimsup (fun n ↦ 1 / u n))
    (hnonneg u (fun n hn ↦ (hu n hn).le))
    (hnonneg _ (fun n hn ↦ one_div_nonneg.mpr (hu n hn).le)) hprod
  obtain ⟨N, hN, htail⟩ := ((sequenceLimsup_eq_coe_iff _ t).mp ht).1 1 (by norm_num)
  have hlower : ((1 / (t + 1) : ℝ) : EReal) ≤ sequenceLiminf u := by
    rw [sequenceLiminf_eq_filter]
    apply le_liminf_of_le (by isBoundedDefault)
    exact (eventually_ge_atTop N).mono fun n hn ↦ EReal.coe_le_coe_iff.mpr (by
      have hupos := hu n (hN.trans hn)
      have hrec : 1 < (t + 1) * u n := (div_lt_iff₀ hupos).mp (htail n hn)
      apply (div_le_iff₀ (by linarith : 0 < t + 1)).mpr
      nlinarith)
  have hiTop : sequenceLiminf u ≠ ⊤ :=
    ((sequenceLiminf_le_sequenceLimsup u).trans_lt (hs ▸ EReal.coe_lt_top s)).ne
  have hiPos : (0 : EReal) < sequenceLiminf u :=
    (EReal.coe_pos.mpr (by positivity : 0 < 1 / (t + 1))).trans_le hlower
  have hiBot : sequenceLiminf u ≠ ⊥ := ((EReal.bot_lt_coe 0).trans hiPos).ne'
  let a := (sequenceLiminf u).toReal
  have hi : sequenceLiminf u = (a : EReal) := (EReal.coe_toReal hiTop hiBot).symm
  have hapos : 0 < a := EReal.coe_pos.mp (hi ▸ hiPos)
  obtain ⟨v, ⟨φ, hpos, hmono, hterm⟩, hconv⟩ := sequenceLiminf_mem_clusterSet u
  have hua : Section03.ConvergesTo (u ∘ φ) a := by
    apply (extendedConvergesTo_coe_iff _ a).mp
    exact (hi ▸ hconv).congr' ((eventually_ge_atTop 1).mono fun n hn ↦
      congrArg (fun x : ℝ ↦ (x : EReal)) (hterm n hn))
  have hinv : Section03.ConvergesTo (fun n ↦ 1 / u (φ n)) (1 / a) :=
    Section03.convergesTo_iff_tendsto.mpr
      (tendsto_const_nhds.div (Section03.convergesTo_iff_tendsto.mp hua) hapos.ne')
  have hcluster : ((1 / a : ℝ) : EReal) ∈ extendedSequenceClusterSet (fun n ↦ 1 / u n) :=
    ⟨_, ⟨φ, hpos, hmono, fun _ _ ↦ rfl⟩, (extendedConvergesTo_coe_iff _ _).mpr hinv⟩
  have hrecbound : 1 / a ≤ t := EReal.coe_le_coe_iff.mp (by
    simpa only [ht] using (cluster_point_bounds _ _ hcluster).2)
  have has : a ≤ s := EReal.coe_le_coe_iff.mp (by
    simpa only [hi, hs] using sequenceLiminf_le_sequenceLimsup u)
  have hsa : s ≤ a := by
    have hh : 1 ≤ t * a := (div_le_iff₀ hapos).mp hrecbound
    nlinarith
  have heq : s = a := le_antisymm hsa has
  exact ⟨a, hapos, (convergesTo_iff_liminf_limsup u a).mpr ⟨hi, by simpa only [heq] using hs⟩⟩


theorem eventual_ratio_upper_geometric (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n → 0 < u n) (b : ℝ) (hb : 0 < b)
    (h : ∀ᶠ n : ℕ in atTop, u (n + 1) / u n ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, u n ≤ C * b ^ n := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  let N := max N₀ 1
  have hN : 1 ≤ N := le_max_right _ _
  let C := u N / b ^ N
  have hC : 0 < C := div_pos (hu N hN) (pow_pos hb N)
  refine ⟨C, hC, eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact (div_mul_cancel₀ (u N) (pow_pos hb N).ne').symm.le
  | succ n hn ih =>
    have hstep : u (n + 1) ≤ b * u n :=
      (div_le_iff₀ (hu n (hN.trans hn))).mp (hN₀ n ((le_max_left _ _).trans hn))
    calc
      u (n + 1) ≤ b * (C * b ^ n) := hstep.trans (mul_le_mul_of_nonneg_left ih hb.le)
      _ = C * b ^ (n + 1) := by rw [pow_succ]; ring


theorem eventual_ratio_lower_geometric (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n → 0 < u n) (b : ℝ) (hb : 0 < b)
    (h : ∀ᶠ n : ℕ in atTop, b ≤ u (n + 1) / u n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, C * b ^ n ≤ u n := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  let N := max N₀ 1
  have hN : 1 ≤ N := le_max_right _ _
  let C := u N / b ^ N
  have hC : 0 < C := div_pos (hu N hN) (pow_pos hb N)
  refine ⟨C, hC, eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact (div_mul_cancel₀ (u N) (pow_pos hb N).ne').le
  | succ n hn ih =>
    have hstep : b * u n ≤ u (n + 1) :=
      (le_div_iff₀ (hu n (hN.trans hn))).mp (hN₀ n ((le_max_left _ _).trans hn))
    calc
      C * b ^ (n + 1) = b * (C * b ^ n) := by rw [pow_succ]; ring
      _ ≤ b * u n := mul_le_mul_of_nonneg_left ih hb.le
      _ ≤ u (n + 1) := hstep


theorem geometric_nth_root_converges (C b : ℝ) (hC : 0 < C) :
    Section03.ConvergesTo (fun n : ℕ ↦ C ^ (1 / (n : ℝ)) * b) b := by
  apply Section03.convergesTo_iff_tendsto.mpr
  simpa using ((tendsto_const_nhds (x := C)).rpow tendsto_one_div_atTop_nhds_zero_nat
    (Or.inl hC.ne')).mul_const b


theorem nth_root_sequenceLimsup_le_of_eventual_ratio_le (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n → 0 < u n) (b : ℝ) (hb : 0 < b)
    (h : ∀ᶠ n : ℕ in atTop, u (n + 1) / u n ≤ b) :
    sequenceLimsup (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) ≤ (b : EReal) := by
  obtain ⟨C, hC, hgeom⟩ := eventual_ratio_upper_geometric u hu b hb h
  have hroot : (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) ≤ᶠ[atTop]
      (fun n : ℕ ↦ C ^ (1 / (n : ℝ)) * b) := by
    filter_upwards [hgeom, eventually_ge_atTop 1] with n hn hn1
    calc
      (u n) ^ (1 / (n : ℝ)) ≤ (C * b ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (hu n hn1).le hn (by positivity)
      _ = C ^ (1 / (n : ℝ)) * b := by
        rw [Real.mul_rpow hC.le (pow_nonneg hb.le n), one_div,
          Real.pow_rpow_inv_natCast hb.le (by omega)]
  have he := (liminf_limsup_of_converges _ b (geometric_nth_root_converges C b hC)).1
  simpa only [he] using (liminf_limsup_mono_of_eventually_le _ _ hroot).1


theorem le_nth_root_sequenceLiminf_of_eventual_le_ratio (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n → 0 < u n) (b : ℝ) (hb : 0 < b)
    (h : ∀ᶠ n : ℕ in atTop, b ≤ u (n + 1) / u n) :
    (b : EReal) ≤ sequenceLiminf (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) := by
  obtain ⟨C, hC, hgeom⟩ := eventual_ratio_lower_geometric u hu b hb h
  have hroot : (fun n : ℕ ↦ C ^ (1 / (n : ℝ)) * b) ≤ᶠ[atTop]
      (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) := by
    filter_upwards [hgeom, eventually_ge_atTop 1] with n hn hn1
    calc
      C ^ (1 / (n : ℝ)) * b = (C * b ^ n) ^ (1 / (n : ℝ)) := by
        rw [Real.mul_rpow hC.le (pow_nonneg hb.le n), one_div,
          Real.pow_rpow_inv_natCast hb.le (by omega)]
      _ ≤ (u n) ^ (1 / (n : ℝ)) := Real.rpow_le_rpow (by positivity) hn (by positivity)
  have he := (liminf_limsup_of_converges _ b (geometric_nth_root_converges C b hC)).2
  simpa only [he] using (liminf_limsup_mono_of_eventually_le _ _ hroot).2

/-- Bài tập 11: tính dương, tính bị chặn của các căn và bất đẳng thức giữa bốn giới hạn mở rộng. -/
theorem positive_nth_root_bounded_and_liminf_limsup_chain (u : ℕ → ℝ)
    (hu : ∀ n : ℕ, 1 ≤ n → 0 < u n)
    (hratio : Section04.SequenceBounded (fun n ↦ u (n + 1) / u n)) :
    Section04.SequenceBounded (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) ∧
      sequenceLiminf (fun n ↦ u (n + 1) / u n) ≤ sequenceLiminf (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) ∧
      sequenceLiminf (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) ≤ sequenceLimsup (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) ∧
      sequenceLimsup (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) ≤ sequenceLimsup (fun n ↦ u (n + 1) / u n) := by
  have hroot0 : (0 : EReal) ≤ sequenceLiminf (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) := by
    rw [sequenceLiminf_eq_filter]
    exact le_liminf_of_le (by isBoundedDefault) ((eventually_ge_atTop 1).mono fun n hn ↦
      EReal.coe_nonneg.mpr (Real.rpow_nonneg (hu n hn).le _))
  have hratio0 : (0 : EReal) ≤ sequenceLimsup (fun n ↦ u (n + 1) / u n) := by
    apply le_trans _ (sequenceLiminf_le_sequenceLimsup _)
    rw [sequenceLiminf_eq_filter]
    exact le_liminf_of_le (by isBoundedDefault) ((eventually_ge_atTop 1).mono fun n hn ↦
      EReal.coe_nonneg.mpr (div_nonneg (hu (n + 1) (by omega)).le (hu n hn).le))
  have hupper : sequenceLimsup (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) ≤
      sequenceLimsup (fun n ↦ u (n + 1) / u n) := by
    by_contra hnot
    obtain ⟨b, hrb, hbr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
    have hb : 0 < b := EReal.coe_pos.mp (hratio0.trans_lt hrb)
    rw [sequenceLimsup_eq_filter] at hrb
    have htail := (eventually_lt_of_limsup_lt hrb).mono fun n hn ↦
      (EReal.coe_lt_coe_iff.mp hn).le
    exact (not_le_of_gt hbr) (nth_root_sequenceLimsup_le_of_eventual_ratio_le u hu b hb htail)
  have hlower : sequenceLiminf (fun n ↦ u (n + 1) / u n) ≤
      sequenceLiminf (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) := by
    by_contra hnot
    obtain ⟨b, hrb, hbr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
    have hb : 0 < b := EReal.coe_pos.mp (hroot0.trans_lt hrb)
    rw [sequenceLiminf_eq_filter] at hbr
    have htail := (eventually_lt_of_lt_liminf hbr).mono fun n hn ↦
      (EReal.coe_lt_coe_iff.mp hn).le
    exact (not_le_of_gt hrb) (le_nth_root_sequenceLiminf_of_eventual_le_ratio u hu b hb htail)
  have hboundedAbove : Section04.SequenceBoundedAbove (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) :=
    (sequenceBoundedAbove_iff_sequenceLimsup_lt_top _).mpr
      (hupper.trans_lt ((sequenceBoundedAbove_iff_sequenceLimsup_lt_top _).mp hratio.1))
  have hboundedBelow : Section04.SequenceBoundedBelow (fun n : ℕ ↦ (u n) ^ (1 / (n : ℝ))) :=
    ⟨0, fun n hn ↦ Real.rpow_nonneg (hu n hn).le _⟩
  exact ⟨⟨hboundedAbove, hboundedBelow⟩, hlower, sequenceLiminf_le_sequenceLimsup _, hupper⟩

/-- Các giới hạn thực của cận đuôi bằng cận trên bé nhất và cận dưới lớn nhất thực
lấy trên các đuôi có chỉ số dương. -/
theorem bounded_real_tail_limits_eq_inf_sup (u : ℕ → ℝ) (hu : Section04.SequenceBounded u) :
    ∃ s t : ℝ, sequenceLimsup u = s ∧ sequenceLiminf u = t ∧
      sInf (Section04.sequenceRangeFromOne (fun n ↦ (tailSup u n).toReal)) = s ∧
      sSup (Section04.sequenceRangeFromOne (fun n ↦ (tailInf u n).toReal)) = t ∧
      Tendsto (fun n ↦ (tailSup u n).toReal) atTop (𝓝 s) ∧
      Tendsto (fun n ↦ (tailInf u n).toReal) atTop (𝓝 t) := by
  obtain ⟨s, t, hs, ht, hst, htt⟩ := bounded_real_tails_tendsto u hu
  have hprop := bounded_real_tails_properties u hu
  have hrange (f : ℕ → ℝ) : range (fun n ↦ f (n + 1)) = Section04.sequenceRangeFromOne f := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n + 1, by simp, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      have hn1 : 1 ≤ n := hn
      refine ⟨n - 1, ?_⟩
      change f (n - 1 + 1) = f n
      rw [Nat.sub_add_cancel hn1]
  have hsanti : Antitone (fun n : ℕ ↦ (tailSup u (n + 1)).toReal) :=
    fun i j hij ↦ hprop.2.1 (by simp) (by simp) (Nat.add_le_add_right hij 1)
  have htmono : Monotone (fun n : ℕ ↦ (tailInf u (n + 1)).toReal) :=
    fun i j hij ↦ hprop.1 (by simp) (by simp) (Nat.add_le_add_right hij 1)
  have hsL := isGLB_of_tendsto_atTop hsanti (hst.comp (tendsto_add_atTop_nat 1))
  have htL := isLUB_of_tendsto_atTop htmono (htt.comp (tendsto_add_atTop_nat 1))
  have hsEq := hsL.csInf_eq (range_nonempty (fun n : ℕ ↦ (tailSup u (n + 1)).toReal))
  have htEq := htL.csSup_eq (range_nonempty (fun n : ℕ ↦ (tailInf u (n + 1)).toReal))
  rw [hrange (fun n : ℕ ↦ (tailSup u n).toReal)] at hsEq
  rw [hrange (fun n : ℕ ↦ (tailInf u n).toReal)] at htEq
  exact ⟨s, t, hs, ht, hsEq, htEq, hst, htt⟩

end calculus.Chapter02.Section10Supplement
