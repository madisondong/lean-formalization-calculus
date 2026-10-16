import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Function
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Equiv.Nat
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# 1.5. Ánh xạ

Nguồn: `source/Ch1_taphop.tex`, dòng 1514–2031.
Bài tập về giao họ phân biệt họ khác rỗng ở §1.4 dòng 677 với họ «bất kỳ» ở §1.5 dòng 1682.
-/

namespace calculus.Chapter01.Section05

open Set Function

variable {X Y Z I : Type*}

/-- Quan hệ ánh xạ: mỗi đối số có duy nhất một giá trị. -/
def IsMapping (R : X → Y → Prop) : Prop := ∀ x, ∃! y, R x y


theorem graph_isMapping (f : X → Y) : IsMapping (fun x y ↦ f x = y) := by
  intro x
  exact ⟨f x, rfl, fun y hy ↦ hy.symm⟩

/-- Mỗi quan hệ ánh xạ là đồ thị của một hàm. -/
theorem isMapping_iff_exists_function (R : X → Y → Prop) :
    IsMapping R ↔ ∃ f : X → Y, ∀ x y, R x y ↔ f x = y := by
  classical
  constructor
  · intro h
    choose f hf huniq using h
    exact ⟨f, fun x y ↦ ⟨fun hy ↦ (huniq x y hy).symm, fun hy ↦ hy ▸ hf x⟩⟩
  · rintro ⟨f, hf⟩ x
    exact ⟨f x, (hf x (f x)).mpr rfl, fun y hy ↦ ((hf x y).mp hy).symm⟩

/-- Hai ánh xạ cùng nguồn và đích bằng nhau khi mọi giá trị tương ứng bằng nhau. -/
theorem function_eq_iff (f g : X → Y) : f = g ↔ ∀ x, f x = g x := funext_iff

/-- Đồ thị hợp thành chính là hợp thành hai quan hệ đồ thị. -/
theorem composition_graph (f : X → Y) (g : Y → Z) (x : X) (z : Z) :
    (∃ y, f x = y ∧ g y = z) ↔ (g ∘ f) x = z := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact hy
  · intro h
    exact ⟨f x, rfl, h⟩

/-- Định lí hợp thành: hợp thành hai quan hệ ánh xạ là quan hệ ánh xạ. -/
theorem composition_isMapping (f : X → Y) (g : Y → Z) :
    IsMapping (fun x z ↦ ∃ y, f x = y ∧ g y = z) := by
  intro x
  refine ⟨g (f x), ⟨f x, rfl, rfl⟩, ?_⟩
  intro z hz
  exact (composition_graph f g x z).mp hz |>.symm


theorem composition_apply (f : X → Y) (g : Y → Z) (x : X) :
    (g ∘ f) x = g (f x) := rfl

/-- Ví dụ 2: hai hợp thành đa thức f∘g và g∘f trên ℤ. -/
theorem integer_composition_formulas (x : ℤ) :
    ((2 * x - 1) ^ 2 + 2 = 4 * x ^ 2 - 4 * x + 3) ∧
      (2 * (x ^ 2 + 2) - 1 = 2 * x ^ 2 + 3) := by
  constructor <;> ring

/-- Hai ánh xạ trong ví dụ 2 không giao hoán: giá trị tại 1 khác nhau. -/
theorem integer_compositions_ne :
    (fun x : ℤ ↦ (2 * x - 1) ^ 2 + 2) ≠ (fun x : ℤ ↦ 2 * (x ^ 2 + 2) - 1) := by
  intro h
  have := congrFun h 1
  norm_num at this

/-- Định nghĩa ảnh: y thuộc ảnh của A khi tồn tại x∈A sao cho f(x)=y. -/
theorem mem_image_iff (f : X → Y) (A : Set X) (y : Y) :
    y ∈ f '' A ↔ ∃ x ∈ A, f x = y := Iff.rfl


theorem image_univ_eq_range (f : X → Y) : f '' univ = range f := image_univ

/-- Định lí ảnh (i). -/
theorem image_mono (f : X → Y) {A B : Set X} (h : A ⊆ B) :
    f '' A ⊆ f '' B := Set.image_mono h

/-- Định lí ảnh (ii): ảnh bảo toàn hợp. -/
theorem image_union (f : X → Y) (A B : Set X) :
    f '' (A ∪ B) = f '' A ∪ f '' B := Set.image_union f A B

/-- Định lí ảnh (iii): ảnh của giao chứa trong giao của hai ảnh. -/
theorem image_inter_subset (f : X → Y) (A B : Set X) :
    f '' (A ∩ B) ⊆ f '' A ∩ f '' B := Set.image_inter_subset f A B

/-- Định lí ảnh (iv): hiệu hai ảnh chứa trong ảnh của hiệu. -/
theorem image_diff_superset (f : X → Y) (A B : Set X) :
    f '' A \ f '' B ⊆ f '' (A \ B) := by
  rintro y ⟨⟨x, hx, rfl⟩, hy⟩
  exact ⟨x, ⟨hx, fun hb ↦ hy ⟨x, hb, rfl⟩⟩, rfl⟩

/-- Định nghĩa ảnh ngược một phần tử là ảnh ngược tập đơn, không phải hàm ngược. -/
theorem mem_fiber_iff (f : X → Y) (x : X) (y : Y) :
    x ∈ f ⁻¹' {y} ↔ f x = y := mem_singleton_iff


theorem mem_preimage_iff (f : X → Y) (B : Set Y) (x : X) :
    x ∈ f ⁻¹' B ↔ f x ∈ B := Iff.rfl

/-- Định lí ảnh ngược (i). -/
theorem preimage_union (f : X → Y) (A B : Set Y) :
    f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B := Set.preimage_union

/-- Định lí ảnh ngược (ii). -/
theorem preimage_inter (f : X → Y) (A B : Set Y) :
    f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := Set.preimage_inter

/-- Định lí ảnh ngược (iii): ảnh ngược bảo toàn bao hàm. -/
theorem preimage_mono (f : X → Y) {A B : Set Y} (h : A ⊆ B) :
    f ⁻¹' A ⊆ f ⁻¹' B := fun _ hx ↦ h hx

/-- Định lí ảnh ngược (iv). -/
theorem preimage_diff (f : X → Y) (A B : Set Y) :
    f ⁻¹' (A \ B) = f ⁻¹' A \ f ⁻¹' B := Set.preimage_sdiff f A B

/-- Định lí ảnh ngược (v): ảnh ngược của phần bù là phần bù của ảnh ngược. -/
theorem preimage_complement (f : X → Y) (B : Set Y) :
    f ⁻¹' (univ \ B) = univ \ f ⁻¹' B := by
  simp

/-- Định lí họ tập (i), tập chỉ số có thể rỗng. -/
theorem image_iUnion (f : X → Y) (A : I → Set X) :
    (f '' ⋃ i, A i) = ⋃ i, f '' A i := Set.image_iUnion

/-- Định lí họ tập (ii), tập chỉ số có thể rỗng. -/
theorem image_iInter_subset (f : X → Y) (A : I → Set X) :
    (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := Set.image_iInter_subset A f

/-- Định lí họ tập (iii). -/
theorem preimage_iUnion (f : X → Y) (B : I → Set Y) :
    (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := Set.preimage_iUnion

/-- Định lí họ tập (iv). -/
theorem preimage_iInter (f : X → Y) (B : I → Set Y) :
    (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := Set.preimage_iInter

/-- Đơn ánh: hai đối số có cùng ảnh thì bằng nhau. -/
theorem injective_iff (f : X → Y) :
    Injective f ↔ ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂ := Iff.rfl

/-- Dạng phản đảo của định nghĩa đơn ánh. -/
theorem injective_iff_ne (f : X → Y) :
    Injective f ↔ ∀ x₁ x₂, x₁ ≠ x₂ → f x₁ ≠ f x₂ := by
  constructor
  · intro hf x₁ x₂ hne heq
    exact hne (hf heq)
  · intro h x₁ x₂ heq
    by_contra hne
    exact h x₁ x₂ hne heq

/-- Toàn ánh: mỗi phần tử đích có một tiền ảnh. -/
theorem surjective_iff (f : X → Y) :
    Surjective f ↔ ∀ y, ∃ x, f x = y := Iff.rfl

/-- Toàn ánh tương đương mọi thớ ảnh ngược khác rỗng. -/
theorem surjective_iff_fibers_nonempty (f : X → Y) :
    Surjective f ↔ ∀ y, (f ⁻¹' {y}).Nonempty := by
  simp only [Surjective, Set.Nonempty, mem_preimage, mem_singleton_iff]

/-- Toàn ánh tương đương tập ảnh bằng tập đích. -/
theorem surjective_iff_range_univ (f : X → Y) :
    Surjective f ↔ range f = univ := Set.range_eq_univ.symm


theorem bijective_iff (f : X → Y) :
    Bijective f ↔ Injective f ∧ Surjective f := Iff.rfl

/-- Ánh xạ đồng nhất là song ánh. -/
theorem identity_bijective (X : Type*) [Nonempty X] : Bijective (id : X → X) :=
  Function.bijective_id

/-- Ánh xạ ngược: hai hợp thành đều là ánh xạ đồng nhất. -/
theorem inverse_iff (f : X → Y) (g : Y → X) :
    (g ∘ f = id ∧ f ∘ g = id) ↔ LeftInverse g f ∧ RightInverse g f := by
  simp only [funext_iff, LeftInverse, RightInverse, comp_apply, id_eq]

/-- Nghịch đảo trái và nghịch đảo phải của cùng một hàm bằng nhau. -/
theorem left_right_inverse_eq (f : X → Y) (g h : Y → X)
    (hgf : LeftInverse g f) (hfh : RightInverse h f) : g = h := by
  funext y
  calc
    g y = g (f (h y)) := congrArg g (hfh y).symm
    _ = h y := hgf (h y)

/-- Khi nghịch đảo trái và phải bằng nhau, hàm chung là nghịch đảo hai phía. -/
theorem left_right_inverse_exists (f : X → Y) (g h : Y → X)
    (hgf : LeftInverse g f) (hfh : RightInverse h f) :
    g = h ∧ LeftInverse g f ∧ RightInverse g f := by
  have heq := left_right_inverse_eq f g h hgf hfh
  exact ⟨heq, hgf, heq ▸ hfh⟩


theorem inverse_unique (f : X → Y) (g h : Y → X)
    (hg : LeftInverse g f ∧ RightInverse g f)
    (hh : LeftInverse h f ∧ RightInverse h f) : g = h :=
  left_right_inverse_eq f g h hg.1 hh.2

/-- Định lí khả nghịch khi và chỉ khi song ánh. -/
theorem exists_inverse_iff_bijective (f : X → Y) :
    (∃ g : Y → X, LeftInverse g f ∧ RightInverse g f) ↔ Bijective f :=
  Function.bijective_iff_has_inverse.symm

/-- Bài tập 4: nghịch đảo của một song ánh là song ánh. -/
theorem inverse_bijective (f : X → Y) (g : Y → X)
    (hgf : LeftInverse g f) (hfg : RightInverse g f) : Bijective g :=
  ⟨hfg.injective, hgf.surjective⟩

/-- Bài tập 5: A⊆f⁻¹(f(A)); đẳng thức khi f đơn ánh. -/
theorem subset_preimage_image (f : X → Y) (A : Set X) :
    A ⊆ f ⁻¹' (f '' A) ∧ (Injective f → A = f ⁻¹' (f '' A)) := by
  exact ⟨fun x hx ↦ ⟨x, hx, rfl⟩, fun hf ↦ (Set.preimage_image_eq A hf).symm⟩

/-- Bài tập 6: f(f⁻¹(B))⊆B; đẳng thức khi f toàn ánh. -/
theorem image_preimage_subset (f : X → Y) (B : Set Y) :
    f '' (f ⁻¹' B) ⊆ B ∧ (Surjective f → f '' (f ⁻¹' B) = B) :=
  ⟨Set.image_preimage_subset f B, fun hf ↦ Set.image_preimage_eq B hf⟩

/-- Bài tập 7: đặc trưng đơn ánh bằng bảo toàn bao hàm thực sự. -/
theorem injective_iff_image_strictMono (f : X → Y) :
    Injective f ↔ ∀ A B : Set X, A ⊂ B → f '' A ⊂ f '' B := by
  classical
  constructor
  · intro hf A B hAB
    exact hf.image_strictMono hAB
  · intro h x y heq
    by_contra hxy
    have hsub : ({x} : Set X) ⊂ {x, y} := by
      rw [Set.ssubset_iff_subset_ne]
      refine ⟨by simp, ?_⟩
      intro hset
      have : y ∈ ({x} : Set X) := hset ▸ (by simp : y ∈ ({x, y} : Set X))
      exact hxy (mem_singleton_iff.mp this).symm
    have hout := h {x} {x, y} hsub
    have himage : f '' ({x} : Set X) = f '' {x, y} := by simp [Set.image_singleton, Set.image_pair, heq]
    exact hout.ne himage

/-- Bài tập 8: đặc trưng toàn ánh bằng ảnh ngược bảo toàn bao hàm thực sự. -/
theorem surjective_iff_preimage_strictMono (f : X → Y) :
    Surjective f ↔ ∀ A B : Set Y, A ⊂ B → f ⁻¹' A ⊂ f ⁻¹' B := by
  classical
  constructor
  · intro hf A B hAB
    rw [Set.ssubset_iff_subset_ne] at hAB ⊢
    refine ⟨Set.preimage_mono hAB.1, ?_⟩
    intro heq
    exact hAB.2 (hf.preimage_injective heq)
  · intro h y
    by_contra hnot
    have hsub : (∅ : Set Y) ⊂ {y} := by simp
    have hout := h ∅ {y} hsub
    have hempty : f ⁻¹' ({y} : Set Y) = ∅ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun hx ↦ hnot ⟨x, hx⟩
    rw [Set.preimage_empty, hempty] at hout
    exact hout.ne rfl

/-- Bài tập 9 dưới quy ước họ khác rỗng (§1.4 dòng 677): đơn ánh bảo toàn giao. -/
theorem injective_image_iInter [Nonempty I] (f : X → Y) (hf : Injective f)
    (A : I → Set X) : (f '' ⋂ i, A i) = ⋂ i, f '' A i :=
  hf.injOn.image_iInter_eq

/-- Bài tập 9: bảo toàn giao hai tập kéo theo đơn ánh. -/
theorem injective_iff_image_inter (f : X → Y) :
    Injective f ↔ ∀ A B : Set X, f '' (A ∩ B) = f '' A ∩ f '' B := by
  classical
  constructor
  · intro hf A B
    exact Set.image_inter hf
  · intro h x y heq
    have hx : f x ∈ f '' ({x} ∩ {y}) := by rw [h]; simp [heq]
    obtain ⟨z, ⟨hzx, hzy⟩, _⟩ := hx
    exact (mem_singleton_iff.mp hzx).symm.trans (mem_singleton_iff.mp hzy)

/-- Bài tập 9 nếu cho phép họ rỗng: kế tiếp đơn ánh nhưng không bảo toàn giao. -/
theorem empty_family_counterexample :
    Injective Nat.succ ∧
      (Nat.succ '' ⋂ i : Empty, (fun _ : Empty ↦ (univ : Set ℕ)) i) ≠
        (⋂ i : Empty, Nat.succ '' (fun _ : Empty ↦ (univ : Set ℕ)) i) := by
  refine ⟨Nat.succ_injective, ?_⟩
  simp only [iInter_of_empty]
  intro heq
  have : 0 ∈ Nat.succ '' (univ : Set ℕ) := by rw [heq]; exact mem_univ 0
  obtain ⟨n, _, hn⟩ := this
  exact Nat.succ_ne_zero n hn

/-- Bài tập 10(a): hợp thành đơn ánh. -/
theorem composition_injective (f : X → Y) (g : Y → Z)
    (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := hg.comp hf

/-- Bài tập 10(b): hợp thành toàn ánh. -/
theorem composition_surjective (f : X → Y) (g : Y → Z)
    (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := hg.comp hf

/-- Bài tập 10(c), phần song ánh. -/
theorem composition_bijective (f : X → Y) (g : Y → Z)
    (hf : Bijective f) (hg : Bijective g) : Bijective (g ∘ f) := hg.comp hf

/-- Bài tập 10(c), thứ tự nghịch đảo là f⁻¹∘g⁻¹. -/
theorem composition_inverse (f : X → Y) (g : Y → Z) (fi : Y → X) (gi : Z → Y)
    (hf : LeftInverse fi f ∧ RightInverse fi f)
    (hg : LeftInverse gi g ∧ RightInverse gi g) :
    LeftInverse (fi ∘ gi) (g ∘ f) ∧ RightInverse (fi ∘ gi) (g ∘ f) := by
  constructor
  · intro x
    change fi (gi (g (f x))) = x
    rw [hg.1, hf.1]
  · intro z
    change g (f (fi (gi z))) = z
    rw [hf.2, hg.2]

/-- Bài tập 11(a): quan hệ cùng lực lượng có tính đối xứng. -/
theorem equinumerous_symm (h : Nonempty (X ≃ Y)) : Nonempty (Y ≃ X) :=
  h.map Equiv.symm

/-- Bài tập 11(b): cùng lực lượng bắc cầu. -/
theorem equinumerous_trans (hXY : Nonempty (X ≃ Y)) (hYZ : Nonempty (Y ≃ Z)) :
    Nonempty (X ≃ Z) := by
  obtain ⟨e⟩ := hXY
  obtain ⟨g⟩ := hYZ
  exact ⟨e.trans g⟩

/-- Bài tập 11(c): hai tập hữu hạn cùng lực lượng khi và chỉ khi số phần tử bằng nhau. -/
theorem equinumerous_finite_iff [Fintype X] [Fintype Y] :
    Nonempty (X ≃ Y) ↔ Fintype.card X = Fintype.card Y := Fintype.card_eq.symm

/-- Ví dụ 1(a): quan hệ ba cặp xác định một ánh xạ giữa hai tập hữu hạn. -/
theorem finite_relation_functional :
    ∀ x ∈ ({1, 2, 3} : Set ℤ), ∃! y : ℤ,
      y ∈ ({4, 5, 6} : Set ℤ) ∧
        (x, y) ∈ ({(1, 4), (2, 4), (3, 5)} : Set (ℤ × ℤ)) := by
  intro x hx
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · refine ⟨4, by simp, ?_⟩
    intro y hy
    simpa using hy.2
  · refine ⟨4, by simp, ?_⟩
    intro y hy
    simpa using hy.2
  · refine ⟨5, by simp, ?_⟩
    intro y hy
    simpa using hy.2

/-- Ví dụ 1(a), quan hệ g không duy nhất: 1 có hai ảnh 4 và 5. -/
theorem finite_relation_not_functional :
    ¬ (∀ x ∈ ({1, 2, 3} : Set ℤ), ∃! y : ℤ,
      y ∈ ({4, 5, 6} : Set ℤ) ∧
        (x, y) ∈ ({(1, 4), (1, 5), (2, 6), (3, 6)} : Set (ℤ × ℤ))) := by
  intro h
  obtain ⟨y, _, huniq⟩ := h 1 (by simp)
  have h4 := huniq 4 (by simp)
  have h5 := huniq 5 (by simp)
  omega

/-- Ví dụ 1(b): quan hệ bình phương trên ℤ là đồ thị một hàm. -/
theorem integer_square_isMapping : IsMapping (fun x y : ℤ ↦ y = x ^ 2) := by
  intro x
  exact ⟨x ^ 2, rfl, fun _ hy ↦ hy⟩

/-- Ví dụ 1(b): đường tròn nguyên không là ánh xạ, vì 0 có ảnh −5 và 5. -/
theorem integer_circle_not_isMapping : ¬ IsMapping (fun x y : ℤ ↦ x ^ 2 + y ^ 2 = 25) := by
  intro h
  obtain ⟨y, _, huniq⟩ := h 0
  have hm := huniq (-5) (by norm_num)
  have hp := huniq 5 (by norm_num)
  omega

/-- Ví dụ 3: ảnh của đoạn nguyên [0,2] qua phép bình phương có ba phần tử. -/
theorem image_square_zero_two :
    (fun x : ℤ ↦ x ^ 2) '' {x | 0 ≤ x ∧ x ≤ 2} = {0, 1, 4} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx0, hx2⟩, rfl⟩
    interval_cases x <;> norm_num
  · intro hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩

/-- Ví dụ 3: ảnh của phép bình phương trên ℤ là tập các số chính phương, kể cả 0. -/
theorem range_integer_square :
    range (fun x : ℤ ↦ x ^ 2) = {y | ∃ x : ℤ, x ^ 2 = y} := rfl

/-- Ví dụ 4, ảnh ngược của 9 gồm −3 và 3. -/
theorem preimage_square_nine : (fun x : ℤ ↦ x ^ 2) ⁻¹' {9} = {-3, 3} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
  constructor
  · intro hx
    have hfactor : (x - 3) * (x + 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · right; omega
    · left; omega
  · rintro (rfl | rfl) <;> norm_num

/-- Ví dụ 4: ảnh ngược của các số nguyên ≤10 gồm bảy số nguyên từ −3 đến 3. -/
theorem preimage_square_le_ten :
    (fun x : ℤ ↦ x ^ 2) ⁻¹' {y | y ≤ 10} = {-3, -2, -1, 0, 1, 2, 3} := by
  ext x
  constructor
  · intro hx
    change x ^ 2 ≤ 10 at hx
    have hlo : -3 ≤ x := by nlinarith
    have hhi : x ≤ 3 := by nlinarith
    interval_cases x <;> norm_num
  · intro hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Bình phương trên các số tự nhiên dương. -/
def positiveSquare (n : ℕ+) : ℕ+ := ⟨n.val ^ 2, pow_pos n.property 2⟩

/-- Ví dụ 5(b) và bài tập 1(a): bình phương trên ℕ+ là đơn ánh. -/
theorem positiveSquare_injective : Injective positiveSquare := by
  intro m n h
  apply Subtype.ext
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (congrArg Subtype.val h)

/-- Bài tập 1(a): 2 không nằm trong ảnh bình phương nên hàm không toàn ánh. -/
theorem positiveSquare_not_surjective : ¬ Surjective positiveSquare := by
  intro h
  obtain ⟨n, hn⟩ := h ⟨2, by norm_num⟩
  have hs : n.val ^ 2 = 2 := congrArg Subtype.val hn
  have hnpos : 0 < (n : ℕ) := n.property
  have hn1 : (n : ℕ) = 1 ∨ 2 ≤ (n : ℕ) := by omega
  rcases hn1 with hn1 | hn2
  · rw [hn1] at hs
    norm_num at hs
  · nlinarith

/-- Ví dụ 5(b) và bài tập 1(b): 1 và −1 có cùng ảnh trên ℤ. -/
theorem integer_square_not_injective : ¬ Injective (fun x : ℤ ↦ x ^ 2) := by
  intro h
  have := h (a₁ := 1) (a₂ := -1) (by norm_num)
  norm_num at this

/-- Bài tập 1(b): số nguyên −1 không là bình phương. -/
theorem integer_square_not_surjective : ¬ Surjective (fun x : ℤ ↦ x ^ 2) := by
  intro h
  obtain ⟨x, hx⟩ := h (-1)
  have := sq_nonneg x
  linarith

/-- Bài tập 1(c): bình phương trên ℝ không đơn ánh. -/
theorem real_square_not_injective : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  intro h
  have := h (a₁ := 1) (a₂ := -1) (by norm_num)
  norm_num at this

/-- Bài tập 1(c): bình phương trên ℝ không toàn ánh vì −1 không có ảnh ngược. -/
theorem real_square_not_surjective : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  intro h
  obtain ⟨x, hx⟩ := h (-1)
  have := sq_nonneg x
  linarith

/-- Ví dụ 6(b): n↦n+2 trên ℤ là toàn ánh. -/
theorem integer_translation_surjective : Surjective (fun n : ℤ ↦ n + 2) := by
  intro y
  exact ⟨y - 2, by ring⟩

/-- Bài tập 1(d): 10x+7 là song ánh trên ℝ, với nghịch đảo (y−7)/10. -/
theorem affine_ten_bijective_and_inverse :
    Bijective (fun x : ℝ ↦ 10 * x + 7) ∧
      LeftInverse (fun y : ℝ ↦ (y - 7) / 10) (fun x ↦ 10 * x + 7) ∧
      RightInverse (fun y : ℝ ↦ (y - 7) / 10) (fun x ↦ 10 * x + 7) := by
  have hl : LeftInverse (fun y : ℝ ↦ (y - 7) / 10) (fun x ↦ 10 * x + 7) := by
    intro x; ring
  have hr : RightInverse (fun y : ℝ ↦ (y - 7) / 10) (fun x ↦ 10 * x + 7) := by
    intro y; ring
  exact ⟨⟨hl.injective, hr.surjective⟩, hl, hr⟩

/-- Bài tập 1(g): |x| trên ℝ không đơn ánh. -/
theorem real_abs_not_injective : ¬ Injective (abs : ℝ → ℝ) := by
  intro h
  have := h (a₁ := 1) (a₂ := -1) (by norm_num)
  norm_num at this

/-- Bài tập 1(g): |x| trên ℝ không toàn ánh vì giá trị luôn không âm. -/
theorem real_abs_not_surjective : ¬ Surjective (abs : ℝ → ℝ) := by
  intro h
  obtain ⟨x, hx⟩ := h (-1)
  have := abs_nonneg x
  linarith

/-- Bài tập 2(a): ba hợp thành trên ℝ. -/
theorem square_translation_compositions (x : ℝ) :
    ((fun t : ℝ ↦ t ^ 2) ∘ (fun t : ℝ ↦ t - 1)) x = x ^ 2 - 2 * x + 1 ∧
      ((fun t : ℝ ↦ t - 1) ∘ (fun t : ℝ ↦ t ^ 2)) x = x ^ 2 - 1 ∧
      ((fun t : ℝ ↦ t ^ 2) ∘ (fun t : ℝ ↦ t ^ 2)) x = x ^ 4 := by
  dsimp only [comp_apply]
  constructor
  · ring
  · constructor
    · rfl
    · ring

/-- Bài tập 2(b): ba hợp thành trên ℝ, thứ tự f∘g,g∘f,f∘f. -/
theorem affine_compositions (x : ℝ) :
    ((fun t : ℝ ↦ 3 * t + 5) ∘ (fun t : ℝ ↦ 5 - t)) x = 20 - 3 * x ∧
      ((fun t : ℝ ↦ 5 - t) ∘ (fun t : ℝ ↦ 3 * t + 5)) x = -3 * x ∧
      ((fun t : ℝ ↦ 3 * t + 5) ∘ (fun t : ℝ ↦ 3 * t + 5)) x = 9 * x + 20 := by
  dsimp only [comp_apply]
  constructor
  · ring
  · constructor <;> ring

/-- Bài tập 3(a): hợp thành hàm afin 5x+1 với hàm lũy thừa bậc 2021. -/
theorem power_affine_decomposition :
    (fun x : ℝ ↦ (5 * x + 1) ^ 2021) =
      (fun y : ℝ ↦ y ^ 2021) ∘ (fun x : ℝ ↦ 5 * x + 1) := rfl

/-- Ví dụ 5(a): miền có đúng ba số nguyên 1,2,3. -/
def finiteInjection : ({1, 2, 3} : Set ℤ) → ({4, 5, 6, 7} : Set ℤ) := fun x ↦
  ⟨x.val + 4, by
    have hx := x.property
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx | hx <;> simp [hx]⟩

/-- Ví dụ 5(a): ánh xạ (1,5),(2,6),(3,7) đơn ánh. -/
theorem finiteInjection_injective : Injective finiteInjection := by
  intro x y h
  apply Subtype.ext
  have heq := congrArg Subtype.val h
  change x.val + 4 = y.val + 4 at heq
  omega

/-- Ví dụ 5(a): ánh xạ g có đúng các ảnh (1,5),(2,6),(3,5). -/
def finiteNoninjection : ({1, 2, 3} : Set ℤ) → ({4, 5, 6, 7} : Set ℤ) := fun x ↦
  ⟨if x.val = 2 then 6 else 5, by split <;> norm_num⟩

/-- Ví dụ 5(a): g(1)=g(3), nên g không đơn ánh. -/
theorem finiteNoninjection_not_injective : ¬ Injective finiteNoninjection := by
  intro h
  have heq := h (a₁ := ⟨1, by simp⟩) (a₂ := ⟨3, by simp⟩) (by
    apply Subtype.ext
    norm_num [finiteNoninjection])
  have := congrArg Subtype.val heq
  norm_num at this

/-- Ví dụ 6(a): hàm có đúng các ảnh (1,5),(2,6),(3,7),(4,6). -/
def finiteSurjection : ({1, 2, 3, 4} : Set ℤ) → ({5, 6, 7} : Set ℤ) := fun x ↦
  ⟨if x.val = 1 then 5 else if x.val = 3 then 7 else 6, by
    split
    · norm_num
    · split <;> norm_num⟩

/-- Ví dụ 6(a): mỗi phần tử 5, 6, 7 có tiền ảnh trong tập nguồn. -/
theorem finiteSurjection_surjective : Surjective finiteSurjection := by
  intro y
  have hy := y.property
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with hy | hy | hy
  · refine ⟨⟨1, by simp⟩, ?_⟩
    apply Subtype.ext
    simp [finiteSurjection, hy]
  · refine ⟨⟨2, by simp⟩, ?_⟩
    apply Subtype.ext
    simp [finiteSurjection, hy]
  · refine ⟨⟨3, by simp⟩, ?_⟩
    apply Subtype.ext
    simp [finiteSurjection, hy]

/-- Ví dụ 6(a): g có đúng các ảnh (1,5),(2,6),(3,5),(4,6). -/
def finiteNonsurjection : ({1, 2, 3, 4} : Set ℤ) → ({5, 6, 7} : Set ℤ) := fun x ↦
  ⟨if x.val = 2 ∨ x.val = 4 then 6 else 5, by split <;> norm_num⟩

/-- Ví dụ 6(a): 7 không thuộc ảnh của g. -/
theorem finiteNonsurjection_not_surjective : ¬ Surjective finiteNonsurjection := by
  intro h
  obtain ⟨x, hx⟩ := h ⟨7, by simp⟩
  have heq := congrArg Subtype.val hx
  change (if x.val = 2 ∨ x.val = 4 then 6 else 5) = (7 : ℤ) at heq
  split at heq <;> norm_num at heq

/-- Ví dụ 7(a): ánh xạ có đồ thị {(1,4),(2,5),(3,6)} giữa hai tập hữu hạn. -/
def finiteBijection : ({1, 2, 3} : Set ℤ) → ({4, 5, 6} : Set ℤ) := fun x ↦
  ⟨x.val + 3, by
    have hx := x.property
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx | hx <;> simp [hx]⟩

/-- Ví dụ 7(a): hàm vừa đơn ánh vừa toàn ánh. -/
theorem finiteBijection_bijective : Bijective finiteBijection := by
  constructor
  · intro x y h
    apply Subtype.ext
    have heq := congrArg Subtype.val h
    change x.val + 3 = y.val + 3 at heq
    omega
  · intro y
    refine ⟨⟨y.val - 3, ?_⟩, ?_⟩
    · have hy := y.property
      simp only [mem_insert_iff, mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> simp [hy]
    · apply Subtype.ext
      change y.val - 3 + 3 = y.val
      ring

/-- Bài tập 1(e): nghịch đảo của phân thức là 2(1+y)/(1−y), với y≠1. -/
theorem fractional_minus_two_bijective_and_inverse :
    BijOn (fun x : ℝ ↦ (x - 2) / (x + 2)) {x | x ≠ -2} {y | y ≠ 1} ∧
      InvOn (fun y : ℝ ↦ 2 * (1 + y) / (1 - y))
        (fun x : ℝ ↦ (x - 2) / (x + 2)) {x | x ≠ -2} {y | y ≠ 1} := by
  have hm : MapsTo (fun x : ℝ ↦ (x - 2) / (x + 2)) {x | x ≠ -2} {y | y ≠ 1} := by
    intro x hx
    change x ≠ -2 at hx
    change (x - 2) / (x + 2) ≠ 1
    have hd : x + 2 ≠ 0 := by intro hz; apply hx; linarith
    intro h
    have h' := (div_eq_iff hd).mp h
    linarith
  have hi : MapsTo (fun y : ℝ ↦ 2 * (1 + y) / (1 - y)) {y | y ≠ 1} {x | x ≠ -2} := by
    intro y hy
    change y ≠ 1 at hy
    change 2 * (1 + y) / (1 - y) ≠ -2
    have hd : 1 - y ≠ 0 := by intro hz; apply hy; linarith
    intro h
    have h' := (div_eq_iff hd).mp h
    linarith
  have hinv : InvOn (fun y : ℝ ↦ 2 * (1 + y) / (1 - y))
      (fun x : ℝ ↦ (x - 2) / (x + 2)) {x | x ≠ -2} {y | y ≠ 1} := by
    constructor
    · intro x hx
      have hd : x + 2 ≠ 0 := by change x ≠ -2 at hx; intro hz; apply hx; linarith
      have he : 1 - (x - 2) / (x + 2) ≠ 0 := by
        have := hm hx
        change (x - 2) / (x + 2) ≠ 1 at this
        intro h; apply this; linarith
      change 2 * (1 + (x - 2) / (x + 2)) / (1 - (x - 2) / (x + 2)) = x
      field_simp
      ring
    · intro y hy
      have hd : 1 - y ≠ 0 := by change y ≠ 1 at hy; intro hz; apply hy; linarith
      have he : 2 * (1 + y) / (1 - y) + 2 ≠ 0 := by
        have := hi hy
        change 2 * (1 + y) / (1 - y) ≠ -2 at this
        intro h; apply this; linarith
      change (2 * (1 + y) / (1 - y) - 2) / (2 * (1 + y) / (1 - y) + 2) = y
      field_simp
      ring
  exact ⟨hinv.bijOn hm hi, hinv⟩

/-- Bài tập 1(f): nguồn ℝ\{3}, đích ℝ\{1}; nghịch đảo (3y−2)/(y−1). -/
theorem fractional_three_bijective_and_inverse :
    BijOn (fun x : ℝ ↦ (x - 2) / (x - 3)) {x | x ≠ 3} {y | y ≠ 1} ∧
      InvOn (fun y : ℝ ↦ (3 * y - 2) / (y - 1))
        (fun x : ℝ ↦ (x - 2) / (x - 3)) {x | x ≠ 3} {y | y ≠ 1} := by
  have hm : MapsTo (fun x : ℝ ↦ (x - 2) / (x - 3)) {x | x ≠ 3} {y | y ≠ 1} := by
    intro x hx
    change x ≠ 3 at hx
    change (x - 2) / (x - 3) ≠ 1
    have hd : x - 3 ≠ 0 := by intro hz; apply hx; linarith
    intro h
    have h' := (div_eq_iff hd).mp h
    linarith
  have hi : MapsTo (fun y : ℝ ↦ (3 * y - 2) / (y - 1)) {y | y ≠ 1} {x | x ≠ 3} := by
    intro y hy
    change y ≠ 1 at hy
    change (3 * y - 2) / (y - 1) ≠ 3
    have hd : y - 1 ≠ 0 := by intro hz; apply hy; linarith
    intro h
    have h' := (div_eq_iff hd).mp h
    linarith
  have hinv : InvOn (fun y : ℝ ↦ (3 * y - 2) / (y - 1))
      (fun x : ℝ ↦ (x - 2) / (x - 3)) {x | x ≠ 3} {y | y ≠ 1} := by
    constructor
    · intro x hx
      have hd : x - 3 ≠ 0 := by change x ≠ 3 at hx; intro hz; apply hx; linarith
      have he : (x - 2) / (x - 3) - 1 ≠ 0 := by
        have := hm hx
        change (x - 2) / (x - 3) ≠ 1 at this
        intro h; apply this; linarith
      change (3 * ((x - 2) / (x - 3)) - 2) / ((x - 2) / (x - 3) - 1) = x
      field_simp
      ring
    · intro y hy
      have hd : y - 1 ≠ 0 := by change y ≠ 1 at hy; intro hz; apply hy; linarith
      have he : (3 * y - 2) / (y - 1) - 3 ≠ 0 := by
        have := hi hy
        change (3 * y - 2) / (y - 1) ≠ 3 at this
        intro h; apply this; linarith
      change ((3 * y - 2) / (y - 1) - 2) / ((3 * y - 2) / (y - 1) - 3) = y
      field_simp
      ring
  exact ⟨hinv.bijOn hm hi, hinv⟩

/-- Bài tập 1(k): song ánh afin từ (0,1) đến (a,b), với a<b. -/
theorem affine_interval_bijective_and_inverse (a b : ℝ) (hab : a < b) :
    BijOn (fun x : ℝ ↦ a + (b - a) * x) (Ioo 0 1) (Ioo a b) ∧
      InvOn (fun y : ℝ ↦ (y - a) / (b - a))
        (fun x : ℝ ↦ a + (b - a) * x) (Ioo 0 1) (Ioo a b) := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hm : MapsTo (fun x : ℝ ↦ a + (b - a) * x) (Ioo 0 1) (Ioo a b) := by
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    constructor <;> nlinarith
  have hi : MapsTo (fun y : ℝ ↦ (y - a) / (b - a)) (Ioo a b) (Ioo 0 1) := by
    intro y hy
    rcases hy with ⟨hy0, hy1⟩
    constructor
    · exact div_pos (sub_pos.mpr hy0) hd
    · apply (div_lt_one hd).mpr
      linarith
  have hinv : InvOn (fun y : ℝ ↦ (y - a) / (b - a))
      (fun x : ℝ ↦ a + (b - a) * x) (Ioo 0 1) (Ioo a b) := by
    constructor
    · intro x _
      change (a + (b - a) * x - a) / (b - a) = x
      field_simp
      ring
    · intro y _
      change a + (b - a) * ((y - a) / (b - a)) = y
      field_simp
      ring
  exact ⟨hinv.bijOn hm hi, hinv⟩

/-- Bài tập 1(l): tan(πx/2) trên (−1,1), nghịch đảo 2 arctan(y)/π. -/
theorem tangent_interval_bijective_and_inverse :
    BijOn (fun x : ℝ ↦ Real.tan (Real.pi * x / 2)) (Ioo (-1) 1) univ ∧
      InvOn (fun y : ℝ ↦ 2 * Real.arctan y / Real.pi)
        (fun x : ℝ ↦ Real.tan (Real.pi * x / 2)) (Ioo (-1) 1) univ := by
  have hp := Real.pi_pos
  have hi : MapsTo (fun y : ℝ ↦ 2 * Real.arctan y / Real.pi) univ (Ioo (-1) 1) := by
    intro y _
    have hlo := Real.neg_pi_div_two_lt_arctan y
    have hhi := Real.arctan_lt_pi_div_two y
    constructor
    · apply (lt_div_iff₀ hp).mpr
      linarith
    · apply (div_lt_iff₀ hp).mpr
      linarith
  have hinv : InvOn (fun y : ℝ ↦ 2 * Real.arctan y / Real.pi)
      (fun x : ℝ ↦ Real.tan (Real.pi * x / 2)) (Ioo (-1) 1) univ := by
    constructor
    · intro x hx
      have hlo : -(Real.pi / 2) < Real.pi * x / 2 := by nlinarith [hx.1]
      have hhi : Real.pi * x / 2 < Real.pi / 2 := by nlinarith [hx.2]
      change 2 * Real.arctan (Real.tan (Real.pi * x / 2)) / Real.pi = x
      rw [Real.arctan_tan hlo hhi]
      field_simp
    · intro y _
      change Real.tan (Real.pi * (2 * Real.arctan y / Real.pi) / 2) = y
      have he : Real.pi * (2 * Real.arctan y / Real.pi) / 2 = Real.arctan y := by
        field_simp
      rw [he, Real.tan_arctan]
  exact ⟨hinv.bijOn (fun _ _ ↦ mem_univ _) hi, hinv⟩

/-- Bài tập 3(b): hàm sin rồi exp trên toàn ℝ. -/
theorem exponential_sine_decomposition :
    (fun x : ℝ ↦ Real.exp (Real.sin x)) = Real.exp ∘ Real.sin := rfl

/-- Bài tập 11(d): song ánh (0,1)→ℝ bằng tan(π(2x−1)/2). -/
noncomputable def openUnitIntervalEquivReal : Ioo (0 : ℝ) 1 ≃ ℝ :=
  ((Set.BijOn.equiv _ (affine_interval_bijective_and_inverse (-1) 1 (by norm_num)).1).trans
    (Set.BijOn.equiv _ tangent_interval_bijective_and_inverse.1)).trans
      (Equiv.Set.univ ℝ)

/-- Bài tập 11(d): công thức song ánh (0,1)→ℝ. -/
theorem openUnitIntervalEquivReal_apply (x : Ioo (0 : ℝ) 1) :
    openUnitIntervalEquivReal x = Real.tan (Real.pi * (-1 + (1 - -1) * x.val) / 2) := rfl

/-- Bài tập 11(d): song ánh (0,1)→(a,b) với a<b, công thức a+(b−a)x. -/
noncomputable def openUnitIntervalEquivOpenInterval (a b : ℝ) (hab : a < b) :
    Ioo (0 : ℝ) 1 ≃ Ioo a b :=
  Set.BijOn.equiv _ (affine_interval_bijective_and_inverse a b hab).1

/-- Bài tập 11(d): giá trị song ánh từ (0,1) đến (a,b). -/
theorem openUnitIntervalEquivOpenInterval_apply (a b : ℝ) (hab : a < b) (x : Ioo (0 : ℝ) 1) :
    (openUnitIntervalEquivOpenInterval a b hab x).val = a + (b - a) * x.val := rfl

/-- Bài tập 12(a): công thức chia nguyên ở hai nhánh chẵn và lẻ. -/
def integerEnumerationFromOne (n : ℕ+) : ℤ :=
  if (n : ℕ) % 2 = 0 then -((n : ℕ) / 2 : ℕ) else (((n : ℕ) - 1) / 2 : ℕ)

/-- Bài tập 12(a): hai nhánh chẵn và lẻ xác định hàm đơn ánh, với 1↦0. -/
theorem integerEnumerationFromOne_injective : Injective integerEnumerationFromOne := by
  intro m n h
  apply Subtype.ext
  change (m : ℕ) = (n : ℕ)
  have hmpos : 0 < (m : ℕ) := m.property
  have hnpos : 0 < (n : ℕ) := n.property
  unfold integerEnumerationFromOne at h
  split_ifs at h <;> omega

/-- Bài tập 12(a): số nguyên âm có chỉ số −2y, không âm có chỉ số 2y+1. -/
theorem integerEnumerationFromOne_surjective : Surjective integerEnumerationFromOne := by
  intro y
  by_cases hy : y < 0
  · have hpos : 0 < (-2 * y).toNat := by omega
    refine ⟨⟨(-2 * y).toNat, hpos⟩, ?_⟩
    unfold integerEnumerationFromOne
    simp only [PNat.mk_coe]
    split_ifs <;> omega
  · have hpos : 0 < (2 * y + 1).toNat := by omega
    refine ⟨⟨(2 * y + 1).toNat, hpos⟩, ?_⟩
    unfold integerEnumerationFromOne
    simp only [PNat.mk_coe]
    split_ifs <;> omega

/-- Bài tập 12(a): hàm đã cho là song ánh ℕ+→ℤ. -/
theorem integerEnumerationFromOne_bijective : Bijective integerEnumerationFromOne :=
  ⟨integerEnumerationFromOne_injective, integerEnumerationFromOne_surjective⟩

/-- Bài tập 12(c): tích hai tập vô hạn đếm được là vô hạn đếm được. -/
theorem product_countably_infinite (hX : Nonempty (X ≃ ℕ+))
    (hY : Nonempty (Y ≃ ℕ+)) : Nonempty ((X × Y) ≃ ℕ+) := by
  obtain ⟨eX⟩ := hX
  obtain ⟨eY⟩ := hY
  exact ⟨(Equiv.prodCongr eX eY).trans (Equiv.prodEquivOfEquivNat Equiv.pnatEquivNat)⟩

/-- Bài tập 12(d): các số hữu tỉ trong [0,1) tạo thành tập vô hạn đếm được. -/
theorem rational_halfOpenUnitInterval_countably_infinite :
    Nonempty ((Ico (0 : ℚ) 1) ≃ ℕ+) := by
  classical
  let : Infinite (Ico (0 : ℚ) 1) := Set.Ico.infinite (by norm_num)
  let : Denumerable (Ico (0 : ℚ) 1) := Denumerable.ofEncodableOfInfinite _
  exact ⟨(Denumerable.eqv _).trans Equiv.pnatEquivNat.symm⟩

/-- Bài tập 12(e): ℚ là tập vô hạn đếm được. -/
theorem rationals_countably_infinite : Nonempty (ℚ ≃ ℕ+) :=
  ⟨(Denumerable.eqv ℚ).trans Equiv.pnatEquivNat.symm⟩

/-- Bài tập 12(f): [0,1] không đếm được. -/
theorem closedUnitInterval_uncountable : ¬ (Icc (0 : ℝ) 1).Countable := by
  simp

/-- Căn bậc hai có dấu dùng trong Bài tập 1(h). -/
noncomputable def signedSquareRoot (y : ℝ) : ℝ :=
  if 0 ≤ y then Real.sqrt y else -Real.sqrt (-y)


theorem mul_abs_injective : Injective (fun x : ℝ ↦ x * |x|) := by
  intro x y heq
  change x * |x| = y * |y| at heq
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hx, abs_of_nonneg hy] at heq
    have hz : (x - y) * (x + y) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h <;> linarith
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [abs_of_nonneg hx, abs_of_nonpos hy'] at heq
    nlinarith [sq_nonneg x, sq_nonneg y]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', abs_of_nonneg hy] at heq
    nlinarith [sq_nonneg x, sq_nonneg y]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hy' : y ≤ 0 := le_of_not_ge hy
    rw [abs_of_nonpos hx', abs_of_nonpos hy'] at heq
    have hz : (x - y) * (x + y) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h <;> linarith

/-- Tính chất căn có dấu: r|r|=y với mọi y, bao gồm số âm và 0. -/
theorem signedSquareRoot_mul_abs (y : ℝ) :
    signedSquareRoot y * |signedSquareRoot y| = y := by
  unfold signedSquareRoot
  split_ifs with hy
  · rw [abs_of_nonneg (Real.sqrt_nonneg y)]
    nlinarith [Real.sq_sqrt hy]
  · have hy' : 0 ≤ -y := by linarith
    rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg (-y))]
    nlinarith [Real.sq_sqrt hy']

/-- Bài tập 1(h): x|x|+1 song ánh trên ℝ và công thức nghịch đảo căn có dấu. -/
theorem mul_abs_add_one_bijective_and_inverse :
    Bijective (fun x : ℝ ↦ x * |x| + 1) ∧
      LeftInverse (fun y : ℝ ↦ signedSquareRoot (y - 1)) (fun x ↦ x * |x| + 1) ∧
      RightInverse (fun y : ℝ ↦ signedSquareRoot (y - 1)) (fun x ↦ x * |x| + 1) := by
  have hinj : Injective (fun x : ℝ ↦ x * |x| + 1) := by
    intro x y h
    apply mul_abs_injective
    linarith
  have hr : RightInverse (fun y : ℝ ↦ signedSquareRoot (y - 1)) (fun x ↦ x * |x| + 1) := by
    intro y
    have := signedSquareRoot_mul_abs (y - 1)
    dsimp
    linarith
  have hl : LeftInverse (fun y : ℝ ↦ signedSquareRoot (y - 1)) (fun x ↦ x * |x| + 1) := by
    intro x
    apply hinj
    exact hr (x * |x| + 1)
  exact ⟨⟨hinj, hr.surjective⟩, hl, hr⟩

/-- Bài tập 1(i): x/(1+|x|) vào (−1,1), nghịch đảo y/(1−|y|). -/
theorem bounded_abs_fraction_bijective_and_inverse :
    BijOn (fun x : ℝ ↦ x / (1 + |x|)) univ (Ioo (-1) 1) ∧
      InvOn (fun y : ℝ ↦ y / (1 - |y|))
        (fun x : ℝ ↦ x / (1 + |x|)) univ (Ioo (-1) 1) := by
  have hm : MapsTo (fun x : ℝ ↦ x / (1 + |x|)) univ (Ioo (-1) 1) := by
    intro x _
    have hd : 0 < 1 + |x| := by linarith [abs_nonneg x]
    constructor
    · apply (lt_div_iff₀ hd).mpr
      linarith [neg_abs_le x]
    · apply (div_lt_iff₀ hd).mpr
      linarith [le_abs_self x]
  have hinv : InvOn (fun y : ℝ ↦ y / (1 - |y|))
      (fun x : ℝ ↦ x / (1 + |x|)) univ (Ioo (-1) 1) := by
    constructor
    · intro x _
      have hd : 0 < 1 + |x| := by linarith [abs_nonneg x]
      have habs : |x / (1 + |x|)| = |x| / (1 + |x|) := by
        rw [abs_div, abs_of_pos hd]
      have he : 1 - |x / (1 + |x|)| ≠ 0 := by
        have hx := hm (mem_univ x)
        have hlt : |x / (1 + |x|)| < 1 := abs_lt.mpr hx
        linarith
      change (x / (1 + |x|)) / (1 - |x / (1 + |x|)|) = x
      rw [habs]
      field_simp
      ring
    · intro y hy
      have hd : 0 < 1 - |y| := by
        have hlt : |y| < 1 := abs_lt.mpr hy
        linarith
      have habs : |y / (1 - |y|)| = |y| / (1 - |y|) := by
        rw [abs_div, abs_of_pos hd]
      change (y / (1 - |y|)) / (1 + |y / (1 - |y|)|) = y
      rw [habs]
      field_simp
      ring
  exact ⟨hinv.bijOn hm (fun _ _ ↦ mem_univ _) , hinv⟩

/-- Bài tập 1(m): đa thức 9x²+6x−5 trên [0,∞), nghịch đảo (√(y+6)−1)/3. -/
theorem quadratic_halfline_bijective_and_inverse :
    BijOn (fun x : ℝ ↦ 9 * x ^ 2 + 6 * x - 5) (Ici 0) (Ici (-5)) ∧
      InvOn (fun y : ℝ ↦ (Real.sqrt (y + 6) - 1) / 3)
        (fun x : ℝ ↦ 9 * x ^ 2 + 6 * x - 5) (Ici 0) (Ici (-5)) := by
  have hm : MapsTo (fun x : ℝ ↦ 9 * x ^ 2 + 6 * x - 5) (Ici 0) (Ici (-5)) := by
    intro x hx
    change 0 ≤ x at hx
    change -5 ≤ 9 * x ^ 2 + 6 * x - 5
    nlinarith [sq_nonneg x]
  have hi : MapsTo (fun y : ℝ ↦ (Real.sqrt (y + 6) - 1) / 3) (Ici (-5)) (Ici 0) := by
    intro y hy
    change -5 ≤ y at hy
    have hs : 1 ≤ Real.sqrt (y + 6) := by
      have hnonneg := Real.sqrt_nonneg (y + 6)
      have hs := Real.sq_sqrt (show 0 ≤ y + 6 by linarith)
      nlinarith
    change 0 ≤ (Real.sqrt (y + 6) - 1) / 3
    linarith
  have hinv : InvOn (fun y : ℝ ↦ (Real.sqrt (y + 6) - 1) / 3)
      (fun x : ℝ ↦ 9 * x ^ 2 + 6 * x - 5) (Ici 0) (Ici (-5)) := by
    constructor
    · intro x hx
      change (Real.sqrt (9 * x ^ 2 + 6 * x - 5 + 6) - 1) / 3 = x
      have hs : 9 * x ^ 2 + 6 * x - 5 + 6 = (3 * x + 1) ^ 2 := by ring
      rw [hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (show 0 ≤ 3 * x + 1 by
        change 0 ≤ x at hx; linarith)]
      ring
    · intro y hy
      change -5 ≤ y at hy
      have hs := Real.sq_sqrt (show 0 ≤ y + 6 by linarith)
      change 9 * ((Real.sqrt (y + 6) - 1) / 3) ^ 2 +
        6 * ((Real.sqrt (y + 6) - 1) / 3) - 5 = y
      nlinarith
  exact ⟨hinv.bijOn hm hi, hinv⟩

/-- Căn bậc ba thực, kể cả với đối số âm. -/
noncomputable def realCubeRoot (y : ℝ) : ℝ :=
  if hy : 0 ≤ y then
    ((NNReal.powOrderIso 3 (by norm_num)).symm ⟨y, hy⟩ : NNReal)
  else
    -((NNReal.powOrderIso 3 (by norm_num)).symm ⟨-y, by linarith⟩ : NNReal)

/-- Căn bậc ba thực thỏa r³=y với mọi y∈ℝ. -/
theorem realCubeRoot_cube (y : ℝ) : realCubeRoot y ^ 3 = y := by
  unfold realCubeRoot
  split_ifs with hy
  · have h := (NNReal.powOrderIso 3 (by norm_num)).apply_symm_apply ⟨y, hy⟩
    have he := congrArg (fun z : NNReal ↦ (z : ℝ)) h
    exact he
  · have h := (NNReal.powOrderIso 3 (by norm_num)).apply_symm_apply
      ⟨-y, by linarith⟩
    have he := congrArg (fun z : NNReal ↦ (z : ℝ)) h
    change (-(((NNReal.powOrderIso 3 (by norm_num)).symm
      ⟨-y, by linarith⟩ : NNReal) : ℝ)) ^ 3 = y
    rw [neg_pow]
    norm_num
    exact neg_eq_iff_eq_neg.mpr he


theorem real_cube_injective : Injective (fun x : ℝ ↦ x ^ 3) :=
  (Odd.strictMono_pow (show Odd (3 : ℕ) by decide)).injective


theorem realCubeRoot_of_cube (x : ℝ) : realCubeRoot (x ^ 3) = x := by
  apply real_cube_injective
  exact realCubeRoot_cube (x ^ 3)

/-- Bài tập 2(c): căn bậc ba thực trên toàn ℝ, với ba hợp thành. -/
theorem cube_root_compositions (x : ℝ) :
    ((fun t : ℝ ↦ realCubeRoot (t - 1)) ∘ (fun t : ℝ ↦ t ^ 3 + 1)) x = x ∧
      ((fun t : ℝ ↦ t ^ 3 + 1) ∘ (fun t : ℝ ↦ realCubeRoot (t - 1))) x = x ∧
      ((fun t : ℝ ↦ realCubeRoot (t - 1)) ∘ (fun t : ℝ ↦ realCubeRoot (t - 1))) x =
        realCubeRoot (realCubeRoot (x - 1) - 1) := by
  dsimp only [comp_apply]
  constructor
  · simpa using realCubeRoot_of_cube x
  · constructor
    · rw [realCubeRoot_cube]
      ring
    · rfl

/-- Bài tập 3(c): bình phương rồi cộng 1, tiếp theo căn bậc ba thực. -/
theorem cube_root_square_decomposition :
    (fun x : ℝ ↦ realCubeRoot (x ^ 2 + 1)) =
      realCubeRoot ∘ (fun x : ℝ ↦ x ^ 2 + 1) := rfl

/-- Bài tập 1(j): (1+exp x)/(1−exp x) trên ℝ\{0},
đích ℝ\[−1,1], nghịch đảo log((y−1)/(y+1)). -/
theorem exponential_fraction_bijective_and_inverse :
    BijOn (fun x : ℝ ↦ (1 + Real.exp x) / (1 - Real.exp x)) {x | x ≠ 0}
      (univ \ Icc (-1) 1) ∧
      InvOn (fun y : ℝ ↦ Real.log ((y - 1) / (y + 1)))
        (fun x : ℝ ↦ (1 + Real.exp x) / (1 - Real.exp x)) {x | x ≠ 0}
          (univ \ Icc (-1) 1) := by
  have hm : MapsTo (fun x : ℝ ↦ (1 + Real.exp x) / (1 - Real.exp x))
      {x | x ≠ 0} (univ \ Icc (-1) 1) := by
    intro x hx
    change x ≠ 0 at hx
    have hexp := Real.exp_pos x
    have hd : 1 - Real.exp x ≠ 0 := by
      intro hz
      apply hx
      exact (Real.exp_eq_one_iff x).mp (by linarith)
    refine ⟨mem_univ _, ?_⟩
    intro hf
    by_cases hp : 0 < 1 - Real.exp x
    · have hgt : 1 < (1 + Real.exp x) / (1 - Real.exp x) := by
        apply (one_lt_div hp).mpr
        linarith
      exact (not_lt_of_ge hf.2) hgt
    · have hn : 1 - Real.exp x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hd
      have hlt : (1 + Real.exp x) / (1 - Real.exp x) < -1 := by
        apply (div_lt_iff_of_neg hn).mpr
        linarith
      exact (not_lt_of_ge hf.1) hlt
  have hrat : ∀ y ∈ (univ \ Icc (-1 : ℝ) 1),
      0 < (y - 1) / (y + 1) ∧ y + 1 ≠ 0 ∧ (y - 1) / (y + 1) ≠ 1 := by
    intro y hy
    have hcases : y < -1 ∨ 1 < y := by
      by_cases hlo : y < -1
      · exact Or.inl hlo
      · right
        have : ¬ y ≤ 1 := fun h ↦ hy.2 ⟨le_of_not_gt hlo, h⟩
        exact lt_of_not_ge this
    have hden : y + 1 ≠ 0 := by
      intro hz
      rcases hcases with h | h <;> linarith
    refine ⟨?_, hden, ?_⟩
    · rcases hcases with h | h
      · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
      · exact div_pos (by linarith) (by linarith)
    · intro h
      have h' := (div_eq_iff hden).mp h
      linarith
  have hi : MapsTo (fun y : ℝ ↦ Real.log ((y - 1) / (y + 1)))
      (univ \ Icc (-1) 1) {x | x ≠ 0} := by
    intro y hy
    change Real.log ((y - 1) / (y + 1)) ≠ 0
    intro hzero
    have h := Real.exp_log (hrat y hy).1
    rw [hzero] at h
    exact (hrat y hy).2.2 (by simpa using h.symm)
  have hinv : InvOn (fun y : ℝ ↦ Real.log ((y - 1) / (y + 1)))
      (fun x : ℝ ↦ (1 + Real.exp x) / (1 - Real.exp x)) {x | x ≠ 0}
        (univ \ Icc (-1) 1) := by
    constructor
    · intro x hx
      have hd : 1 - Real.exp x ≠ 0 := by
        intro hz
        apply hx
        exact (Real.exp_eq_one_iff x).mp (by linarith)
      have he : (1 + Real.exp x) / (1 - Real.exp x) + 1 ≠ 0 := (hrat _ (hm hx)).2.1
      have hformula : (((1 + Real.exp x) / (1 - Real.exp x)) - 1) /
          (((1 + Real.exp x) / (1 - Real.exp x)) + 1) = Real.exp x := by
        field_simp
        ring
      change Real.log ((((1 + Real.exp x) / (1 - Real.exp x)) - 1) /
          (((1 + Real.exp x) / (1 - Real.exp x)) + 1)) = x
      rw [hformula, Real.log_exp]
    · intro y hy
      have hp := (hrat y hy).1
      have hd := (hrat y hy).2.1
      have he : 1 - (y - 1) / (y + 1) ≠ 0 := by
        intro h
        exact (hrat y hy).2.2 (by linarith)
      change (1 + Real.exp (Real.log ((y - 1) / (y + 1)))) /
        (1 - Real.exp (Real.log ((y - 1) / (y + 1)))) = y
      rw [Real.exp_log hp]
      field_simp
      ring
  exact ⟨hinv.bijOn hm hi, hinv⟩

/-- Bài tập 9, dòng 677: đơn ánh khi và chỉ khi ảnh bảo toàn giao của mọi họ không rỗng. -/
theorem injective_iff_nonempty_family_image_inter (f : X → Y) :
    Injective f ↔ ∀ (J : Type) (_ : Nonempty J) (A : J → Set X),
      (f '' ⋂ j, A j) = ⋂ j, f '' A j := by
  constructor
  · intro hf J hJ A
    let : Nonempty J := hJ
    exact injective_image_iInter f hf A
  · intro h
    apply (injective_iff_image_inter f).mpr
    intro A B
    have hsource : (⋂ i : Bool, if i then A else B) = A ∩ B := by
      ext x
      simp [and_comm]
    have htarget : (⋂ i : Bool, f '' (if i then A else B)) = f '' A ∩ f '' B := by
      ext y
      simp [and_comm]
    have heq := h Bool ⟨true⟩ (fun i : Bool ↦ if i then A else B)
    rwa [hsource, htarget] at heq

/-- Nhận xét: ảnh của {−2,−1,0} qua bình phương là {0,1,4}. -/
theorem square_negative_set_image :
    (fun x : ℤ ↦ x ^ 2) '' {-2, -1, 0} = {0, 1, 4} := by
  ext y
  simp [Set.image_insert_eq, Set.insert_comm, or_comm, or_left_comm]

/-- Nhận xét: ảnh bảo toàn hợp; ảnh của giao có thể nhỏ hơn giao của các ảnh. -/
theorem square_image_intersection_counterexample :
    ((fun x : ℤ ↦ x ^ 2) '' {-2, -1, 0} = {0, 1, 4}) ∧
      ((fun x : ℤ ↦ x ^ 2) '' {0, 1, 2} = {0, 1, 4}) ∧
      (({-2, -1, 0} : Set ℤ) ∩ {0, 1, 2} = {0}) ∧
      ((fun x : ℤ ↦ x ^ 2) '' (({-2, -1, 0} : Set ℤ) ∩ {0, 1, 2}) = {0}) ∧
      ((fun x : ℤ ↦ x ^ 2) '' (({-2, -1, 0} : Set ℤ) ∩ {0, 1, 2}) ≠
        (fun x : ℤ ↦ x ^ 2) '' {-2, -1, 0} ∩ (fun x : ℤ ↦ x ^ 2) '' {0, 1, 2}) := by
  have hneg := square_negative_set_image
  have hpos : (fun x : ℤ ↦ x ^ 2) '' {0, 1, 2} = {0, 1, 4} := by
    ext y
    simp [Set.image_insert_eq]
  have hinter : ({-2, -1, 0} : Set ℤ) ∩ {0, 1, 2} = {0} := by
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    omega
  have himage : (fun x : ℤ ↦ x ^ 2) '' (({-2, -1, 0} : Set ℤ) ∩ {0, 1, 2}) = {0} := by
    rw [hinter, Set.image_singleton]
    norm_num
  refine ⟨hneg, hpos, hinter, himage, ?_⟩
  rw [himage, hneg, hpos, Set.inter_self]
  intro heq
  have : (1 : ℤ) ∈ ({0} : Set ℤ) := by rw [heq]; simp
  norm_num at this

/-- Nhận xét: hiệu ảnh rỗng nhưng ảnh hiệu bằng {1,4}, nên bao hàm là thực sự. -/
theorem square_image_difference_counterexample :
    (({-2, -1, 0} : Set ℤ) \ {0, 1, 2} = {-2, -1}) ∧
      ((fun x : ℤ ↦ x ^ 2) '' (({-2, -1, 0} : Set ℤ) \ {0, 1, 2}) = {1, 4}) ∧
      ((fun x : ℤ ↦ x ^ 2) '' {-2, -1, 0} \ (fun x : ℤ ↦ x ^ 2) '' {0, 1, 2} = ∅) ∧
      ((fun x : ℤ ↦ x ^ 2) '' (({-2, -1, 0} : Set ℤ) \ {0, 1, 2}) ≠
        (fun x : ℤ ↦ x ^ 2) '' {-2, -1, 0} \ (fun x : ℤ ↦ x ^ 2) '' {0, 1, 2}) := by
  have hdiff : ({-2, -1, 0} : Set ℤ) \ {0, 1, 2} = {-2, -1} := by
    ext x
    simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff]
    omega
  have himage : (fun x : ℤ ↦ x ^ 2) '' (({-2, -1, 0} : Set ℤ) \ {0, 1, 2}) = {1, 4} := by
    rw [hdiff, Set.image_pair]
    ext y
    norm_num [or_comm]
  have hpos : (fun x : ℤ ↦ x ^ 2) '' {0, 1, 2} = {0, 1, 4} := by
    ext y
    simp [Set.image_insert_eq]
  have hdimage : (fun x : ℤ ↦ x ^ 2) '' {-2, -1, 0} \ (fun x : ℤ ↦ x ^ 2) '' {0, 1, 2} = ∅ := by
    rw [square_negative_set_image, hpos, Set.sdiff_self]
  refine ⟨hdiff, himage, hdimage, ?_⟩
  rw [himage, hdimage]
  intro heq
  have : (1 : ℤ) ∈ (∅ : Set ℤ) := by rw [← heq]; simp
  exact this


/-- Số tam giác t_d=1+…+d. -/
def triangular (d : ℕ) : ℕ := (d + 1).choose 2


lemma triangular_zero : triangular 0 = 0 := by norm_num [triangular]


lemma triangular_succ (d : ℕ) : triangular (d + 1) = triangular d + d + 1 := by
  unfold triangular
  rw [Nat.choose_succ_succ' (d + 1) 1, Nat.choose_one_right]
  change (d + 1) + (d + 1).choose 2 = (d + 1).choose 2 + d + 1
  omega


lemma triangular_strictMono : StrictMono triangular := by
  apply strictMono_nat_of_lt_succ
  intro d
  rw [triangular_succ]
  omega


lemma triangular_gap {d e : ℕ} (h : d < e) : triangular d + d < triangular e := by
  have hmono := triangular_strictMono.monotone (show d + 1 ≤ e by omega)
  rw [triangular_succ] at hmono
  omega

/-- Hàm ghép cặp đường chéo với hai chỉ số bắt đầu từ 0. -/
def diagonalPair (p : ℕ × ℕ) : ℕ := triangular (p.1 + p.2) + p.1


lemma diagonalPair_injective : Function.Injective diagonalPair := by
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  change triangular (a + b) + a = triangular (c + d) + c at heq
  have hsum : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hlt | he | hgt
    · have hg := triangular_gap hlt
      omega
    · exact he
    · have hg := triangular_gap hgt
      omega
  have hac : a = c := by rw [hsum] at heq; omega
  have hbd : b = d := by omega
  exact Prod.ext hac hbd


lemma diagonalPair_surjective : Function.Surjective diagonalPair := by
  intro n
  induction n with
  | zero => exact ⟨(0, 0), triangular_zero⟩
  | succ n ih =>
    obtain ⟨⟨a, b⟩, hp⟩ := ih
    change triangular (a + b) + a = n at hp
    by_cases hb : b = 0
    · refine ⟨(0, a + 1), ?_⟩
      change triangular (0 + (a + 1)) + 0 = n + 1
      simp only [zero_add, add_zero]
      rw [triangular_succ]
      simp only [hb, add_zero] at hp
      omega
    · refine ⟨(a + 1, b - 1), ?_⟩
      change triangular (a + 1 + (b - 1)) + (a + 1) = n + 1
      have hsum : a + 1 + (b - 1) = a + b := by omega
      rw [hsum]
      omega


lemma triangular_formula (d : ℕ) :
    (triangular d : ℚ) = (d : ℚ) * ((d : ℚ) + 1) / 2 := by
  unfold triangular
  rw [Nat.cast_choose_two]
  simp only [Nat.cast_add, Nat.cast_one]
  ring


/-- Song ánh trung gian từ cặp chỉ số dương đến một chỉ số dương. -/
noncomputable def positiveDiagonalEquiv : (ℕ+ × ℕ+) ≃ ℕ+ :=
  ((Equiv.prodCongr Equiv.pnatEquivNat Equiv.pnatEquivNat).trans
    (Equiv.ofBijective diagonalPair ⟨diagonalPair_injective, diagonalPair_surjective⟩)).trans
      Equiv.pnatEquivNat.symm

/-- Bài tập 12(b): hàm ghép cặp với i,j≥1. -/
def positiveDiagonalPair (p : ℕ+ × ℕ+) : ℕ+ :=
  ⟨triangular ((p.1 : ℕ) + (p.2 : ℕ) - 2) + (p.1 : ℕ), by
    have hi : 0 < (p.1 : ℕ) := p.1.property
    omega⟩

/-- Đổi chỉ số dương i,j thành i−1,j−1 trong ghép cặp đường chéo. -/
theorem positiveDiagonalPair_eq_equiv (p : ℕ+ × ℕ+) :
    positiveDiagonalPair p = positiveDiagonalEquiv p := by
  apply Subtype.ext
  change triangular ((p.1 : ℕ) + (p.2 : ℕ) - 2) + (p.1 : ℕ) =
    triangular (((p.1 : ℕ) - 1) + ((p.2 : ℕ) - 1)) + ((p.1 : ℕ) - 1) + 1
  have hi : 0 < (p.1 : ℕ) := p.1.property
  have hj : 0 < (p.2 : ℕ) := p.2.property
  have hs : (p.1 : ℕ) + (p.2 : ℕ) - 2 = ((p.1 : ℕ) - 1) + ((p.2 : ℕ) - 1) := by omega
  rw [hs]
  omega

/-- Bài tập 12(b): công thức chính xác ½(i+j−2)(i+j−1)+i là số nguyên dương. -/
theorem positiveDiagonalPair_formula (p : ℕ+ × ℕ+) :
    (((positiveDiagonalPair p : ℕ+) : ℕ) : ℚ) =
      (1 / 2 : ℚ) * (((p.1 : ℕ) : ℚ) + ((p.2 : ℕ) : ℚ) - 2) *
        (((p.1 : ℕ) : ℚ) + ((p.2 : ℕ) : ℚ) - 1) + ((p.1 : ℕ) : ℚ) := by
  change ((triangular ((p.1 : ℕ) + (p.2 : ℕ) - 2) + (p.1 : ℕ) : ℕ) : ℚ) = _
  have hi : 0 < (p.1 : ℕ) := p.1.property
  have hj : 0 < (p.2 : ℕ) := p.2.property
  have hs : 2 ≤ (p.1 : ℕ) + (p.2 : ℕ) := by omega
  rw [Nat.cast_add, triangular_formula, Nat.cast_sub hs]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Bài tập 12(b): hàm ghép cặp theo đường chéo là song ánh. -/
theorem positiveDiagonalPair_bijective : Bijective positiveDiagonalPair := by
  have heq : positiveDiagonalPair = positiveDiagonalEquiv :=
    funext positiveDiagonalPair_eq_equiv
  rw [heq]
  exact positiveDiagonalEquiv.bijective

/-- Bài tập 12(a): công thức chia nguyên của hai nhánh chẵn và lẻ. -/
theorem integerEnumerationFromOne_formula (n : ℕ+) :
    integerEnumerationFromOne n =
      if (n : ℕ) % 2 = 0 then -((n : ℕ) : ℤ) / 2 else (((n : ℕ) : ℤ) - 1) / 2 := by
  have hn : 0 < (n : ℕ) := n.property
  unfold integerEnumerationFromOne
  split_ifs <;> omega

/-- Ví dụ 6(b): 2 không là bình phương số nguyên. -/
theorem integer_square_ne_two (x : ℤ) : x ^ 2 ≠ 2 := by
  intro h
  have hlo : -1 ≤ x := by nlinarith
  have hhi : x ≤ 1 := by nlinarith
  interval_cases x <;> norm_num at h

/-- Ví dụ 1(a): đồ thị f nằm trong tích của tập nguồn và tập đích. -/
theorem finite_relation_domain_codomain (x y : ℤ)
    (h : (x, y) ∈ ({(1, 4), (2, 4), (3, 5)} : Set (ℤ × ℤ))) :
    x ∈ ({1, 2, 3} : Set ℤ) ∧ y ∈ ({4, 5, 6} : Set ℤ) := by
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Ví dụ 1(a): đồ thị g nằm trong tích của tập nguồn và tập đích. -/
theorem finite_nonfunctional_relation_domain_codomain (x y : ℤ)
    (h : (x, y) ∈ ({(1, 4), (1, 5), (2, 6), (3, 6)} : Set (ℤ × ℤ))) :
    x ∈ ({1, 2, 3} : Set ℤ) ∧ y ∈ ({4, 5, 6} : Set ℤ) := by
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Bài tập 12(f): không tồn tại song ánh ℕ+→[0,1]. -/
theorem closedUnitInterval_not_countably_infinite :
    ¬ Nonempty (ℕ+ ≃ Icc (0 : ℝ) 1) := by
  rintro ⟨e⟩
  have hcount : Countable (Icc (0 : ℝ) 1) := Countable.of_equiv ℕ+ e
  exact closedUnitInterval_uncountable (Set.countable_coe_iff.mp hcount)

/-- Đơn ánh f là song ánh từ tập nguồn đến tập ảnh. -/
theorem injective_iff_bijective_rangeFactorization (f : X → Y) :
    Injective f ↔ Bijective (Set.rangeFactorization f) := by
  constructor
  · intro hf
    constructor
    · intro x y h
      exact hf (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx⟩ := y.property
      exact ⟨x, Subtype.ext hx⟩
  · intro hf x y h
    apply hf.1
    exact Subtype.ext h

/-- Bài tập 12: «đếm được» nghĩa là vô hạn đếm được. -/
def CountablyInfinite (A : Type*) : Prop := Nonempty (ℕ+ ≃ A)

/-- Vô hạn đếm được khi và chỉ khi có song ánh ℕ+→A. -/
theorem countablyInfinite_iff_exists_bijective (A : Type*) :
    CountablyInfinite A ↔ ∃ f : ℕ+ → A, Bijective f := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e, e.bijective⟩
  · rintro ⟨f, hf⟩
    exact ⟨Equiv.ofBijective f hf⟩

end calculus.Chapter01.Section05
