import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# 4.1.5: đạo hàm cấp cao và các lớp Cⁿ

Nguồn: `source/Ch4_hamsokhavi.tex`, dòng 316–404. Lớp Cⁿ yêu cầu đạo hàm cấp `n` liên tục; khả vi `n` lần không yêu cầu điều này.
-/
namespace calculus.Chapter04.Section01Higher
open Set
open scoped ContDiff


noncomputable def restrictedIteratedDerivativeWithin (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) : I → ℝ :=
  fun x ↦ iteratedDerivWithin n f I x


def DifferentiableToOrderOn (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ k : ℕ, k < n → DifferentiableOn ℝ (iteratedDerivWithin k f I) I


def DifferentiableOnAndDerivDifferentiableAt (f : ℝ → ℝ) (I : Set ℝ) (x : I) : Prop :=
  DifferentiableOn ℝ f I ∧ DifferentiableAt ℝ (deriv f) x


theorem restrictedIteratedDerivativeWithin_eq_iteratedDeriv (n : ℕ) (f : ℝ → ℝ)
    {I : Set ℝ} (hI : IsOpen I) (x : I) :
    restrictedIteratedDerivativeWithin n f I x = iteratedDeriv n f x :=
  iteratedDerivWithin_of_isOpen hI x.property


theorem restrictedIteratedDerivativeWithin_zero (f : ℝ → ℝ) (I : Set ℝ) (x : I) :
    restrictedIteratedDerivativeWithin 0 f I x = f x := by simp [restrictedIteratedDerivativeWithin]


theorem restrictedIteratedDerivativeWithin_succ (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) (x : I) :
    restrictedIteratedDerivativeWithin (n + 1) f I x = derivWithin (iteratedDerivWithin n f I) I x := by
  exact congrFun (iteratedDerivWithin_succ (n := n) (f := f) (s := I)) x


theorem differentiableToOrderOn_one (f : ℝ → ℝ) (I : Set ℝ) :
    DifferentiableToOrderOn 1 f I ↔ DifferentiableOn ℝ f I := by
  simp [DifferentiableToOrderOn]


theorem differentiableToOrderOn_two (f : ℝ → ℝ) {I : Set ℝ} (hI : IsOpen I) :
    DifferentiableToOrderOn 2 f I ↔
      DifferentiableOn ℝ f I ∧ DifferentiableOn ℝ (deriv f) I := by
  have hd : EqOn (derivWithin f I) (deriv f) I := fun x hx ↦ derivWithin_of_isOpen hI hx
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [iteratedDerivWithin_zero] using h 0 (by decide)
    · have hh : DifferentiableOn ℝ (derivWithin f I) I := by
        simpa only [iteratedDerivWithin_one] using h 1 (by decide)
      exact hh.congr hd.symm
  · rintro ⟨hf, hg⟩ k hk
    have he : k = 0 ∨ k = 1 := by omega
    rcases he with rfl | rfl
    · simpa only [iteratedDerivWithin_zero] using hf
    · simpa only [iteratedDerivWithin_one] using hg.congr hd


def DomainC (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  DifferentiableToOrderOn n f I ∧ ContinuousOn (iteratedDerivWithin n f I) I


theorem domainC_iff_contDiffOn (n : ℕ) (f : ℝ → ℝ) {I : Set ℝ} (hI : IsOpen I) :
    DomainC n f I ↔ ContDiffOn ℝ n f I := by
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hI.uniqueDiffOn]
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨?_, hd⟩
    intro k hk
    by_cases hkn : k < n
    · exact (hd k hkn).continuousOn
    · have he : k = n := by omega
      simpa only [he] using hc
  · rintro ⟨hc, hd⟩
    exact ⟨hd, hc n le_rfl⟩


def DomainSmooth (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ n : ℕ, DifferentiableToOrderOn n f I


theorem domainSmooth_iff_contDiffOn (f : ℝ → ℝ) {I : Set ℝ} (hI : IsOpen I) :
    DomainSmooth f I ↔ ContDiffOn ℝ ∞ f I := by
  constructor
  · intro h
    apply contDiffOn_of_differentiableOn_deriv (n := ⊤)
    intro k _
    exact h (k + 1) k (Nat.lt_succ_self k)
  · intro h n k hk
    exact h.differentiableOn_iteratedDerivWithin (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)) hI.uniqueDiffOn

/-- Nhận xét 4.1.23(ii): trên miền mở, nếu `m ≤ n` thì `Cⁿ ⊆ Cᵐ`. -/
theorem domainC_mono {m n : ℕ} {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hmn : m ≤ n) (hf : DomainC n f I) : DomainC m f I := by
  apply (domainC_iff_contDiffOn m f hI).mpr
  exact ((domainC_iff_contDiffOn n f hI).mp hf).of_le (by exact_mod_cast hmn)

/-- Nhận xét 4.1.23(iii): trên miền mở, `C∞ ⊆ Cⁿ` với mọi `n ∈ ℕ`. -/
theorem domainSmooth_domainC {n : ℕ} {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hf : DomainSmooth f I) : DomainC n f I := by
  apply (domainC_iff_contDiffOn n f hI).mpr
  exact ((domainSmooth_iff_contDiffOn f hI).mp hf).of_le (WithTop.coe_le_coe.mpr le_top)


theorem source_add_higher (n : ℕ) {f g : ℝ → ℝ} {I : Set ℝ} (_hI : IsOpen I)
    (hf : DifferentiableToOrderOn n f I) (hg : DifferentiableToOrderOn n g I) :
    DifferentiableToOrderOn n (fun x ↦ f x + g x) I ∧
      ∀ k : ℕ, k ≤ n → EqOn (iteratedDerivWithin k (fun x ↦ f x + g x) I)
        (fun x ↦ iteratedDerivWithin k f I x + iteratedDerivWithin k g I x) I := by
  induction n with
  | zero =>
    refine ⟨fun k hk ↦ (Nat.not_lt_zero k hk).elim, ?_⟩
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    simp [hk0, EqOn]
  | succ n ih =>
    have hf0 : DifferentiableToOrderOn n f I := fun k hk ↦ hf k (hk.trans_le n.le_succ)
    have hg0 : DifferentiableToOrderOn n g I := fun k hk ↦ hg k (hk.trans_le n.le_succ)
    have hi := ih hf0 hg0
    have hdiff : DifferentiableToOrderOn (n + 1) (fun x ↦ f x + g x) I := by
      intro k hk
      exact ((hf k hk).add (hg k hk)).congr (hi.2 k (Nat.lt_succ_iff.mp hk))
    refine ⟨hdiff, ?_⟩
    intro k hk
    by_cases hkn : k ≤ n
    · exact hi.2 k hkn
    · have hk1 : k = n + 1 := by omega
      subst k
      intro x hx
      rw [iteratedDerivWithin_succ, derivWithin_congr (hi.2 n le_rfl) (hi.2 n le_rfl hx)]
      rw [derivWithin_fun_add (hf n n.lt_succ_self x hx) (hg n n.lt_succ_self x hx)]
      simp only [iteratedDerivWithin_succ]


theorem source_const_mul_higher (n : ℕ) {f : ℝ → ℝ} {I : Set ℝ}
    (hf : DifferentiableToOrderOn n f I) (c : ℝ) :
    DifferentiableToOrderOn n (fun x ↦ c * f x) I ∧
      EqOn (iteratedDerivWithin n (fun x ↦ c * f x) I)
        (fun x ↦ c * iteratedDerivWithin n f I x) I := by
  refine ⟨?_, ?_⟩
  · intro k hk
    exact ((hf k hk).const_mul c).congr fun x _ ↦ iteratedDerivWithin_const_mul_field c f
  · intro x _
    exact iteratedDerivWithin_const_mul_field c f


theorem pow_domainSmooth (n : ℕ) {I : Set ℝ} (hI : IsOpen I) :
    DomainSmooth (fun x : ℝ ↦ x ^ n) I := by
  apply (domainSmooth_iff_contDiffOn _ hI).mpr
  exact (contDiff_id.pow n).contDiffOn


theorem exponential_affine_domainSmooth (a b : ℝ) {I : Set ℝ} (hI : IsOpen I) :
    DomainSmooth (fun x : ℝ ↦ Real.exp (a * x + b)) I := by
  apply (domainSmooth_iff_contDiffOn _ hI).mpr
  exact (((contDiff_const.mul contDiff_id).add contDiff_const).exp).contDiffOn


theorem reciprocal_affine_domainSmooth (a b : ℝ) (ha : a ≠ 0) :
    DomainSmooth (fun x : ℝ ↦ 1 / (a * x + b)) {x | x ≠ -b / a} := by
  have hI : IsOpen ({x : ℝ | x ≠ -b / a}) := isClosed_singleton.isOpen_compl
  apply (domainSmooth_iff_contDiffOn _ hI).mpr
  apply contDiffOn_const.div ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn
  intro x hx he
  apply hx
  apply (eq_div_iff ha).mpr
  linarith


theorem sine_cosine_domainSmooth {I : Set ℝ} (hI : IsOpen I) :
    DomainSmooth Real.sin I ∧ DomainSmooth Real.cos I :=
  ⟨(domainSmooth_iff_contDiffOn _ hI).mpr Real.contDiff_sin.contDiffOn,
    (domainSmooth_iff_contDiffOn _ hI).mpr Real.contDiff_cos.contDiffOn⟩

/-- Ví dụ 4.1.18(b): đạo hàm cấp `n` của `exp(ax+b)`, với `a ≠ 0`. -/
theorem exponential_affine_iteratedDeriv (n : ℕ) (a b x : ℝ) (_ha : a ≠ 0) :
    iteratedDeriv n (fun y : ℝ ↦ Real.exp (a * y + b)) x = a ^ n * Real.exp (a * x + b) := by
  have he : (fun y : ℝ ↦ Real.exp (a * y + b)) =
      (fun y : ℝ ↦ Real.exp b * Real.exp (a * y)) := by
    funext y
    rw [Real.exp_add]
    ring
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  rw [Real.exp_add]
  ring

/-- Ví dụ 4.1.19(a): đạo hàm cấp lẻ của sin. -/
theorem sine_odd_iteratedDeriv (k : ℕ) (x : ℝ) :
    iteratedDeriv (2 * k + 1) Real.sin x = (-1 : ℝ) ^ k * Real.cos x := by
  exact congrFun (Real.iteratedDeriv_odd_sin k) x

theorem sine_odd_iteratedDeriv_zero (k : ℕ) :
    iteratedDeriv (2 * k + 1) Real.sin 0 = (-1 : ℝ) ^ k := by
  simp [sine_odd_iteratedDeriv]

/-- Ví dụ 4.1.19(b): đạo hàm cấp chẵn của cos. -/
theorem cosine_even_iteratedDeriv (k : ℕ) (x : ℝ) :
    iteratedDeriv (2 * k) Real.cos x = (-1 : ℝ) ^ k * Real.cos x := by
  exact congrFun (Real.iteratedDeriv_even_cos k) x

theorem cosine_even_iteratedDeriv_zero (k : ℕ) :
    iteratedDeriv (2 * k) Real.cos 0 = (-1 : ℝ) ^ k := by
  simp [cosine_even_iteratedDeriv]


theorem reciprocal_iteratedDeriv (n : ℕ) (z : ℝ) (hz : z ≠ 0) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / y) z = (-1 : ℝ) ^ n * (n.factorial : ℝ) / z ^ (n + 1) := by
  have hs : IsOpen ({(0 : ℝ)}ᶜ : Set ℝ) := isClosed_singleton.isOpen_compl
  have hmem : z ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := by simpa using hz
  have h := iteratedDerivWithin_one_div n hs hmem
  rw [iteratedDerivWithin_of_isOpen hs hmem] at h
  have he : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
  simpa only [he, zpow_neg, zpow_natCast, div_eq_mul_inv] using h


theorem reciprocal_affine_iteratedDeriv (n : ℕ) (a b x : ℝ) (ha : a ≠ 0)
    (hx : x ≠ -b / a) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / (a * y + b)) x =
      (-1 : ℝ) ^ n * (a ^ n * (n.factorial : ℝ)) / (a * x + b) ^ (n + 1) := by
  have hlin (y : ℝ) : a * y + b = a * (y + b / a) := by field_simp
  have hz : x + b / a ≠ 0 := by
    intro he
    apply hx
    have : x = -(b / a) := eq_neg_of_add_eq_zero_left he
    simpa only [neg_div] using this
  have heq : (fun y : ℝ ↦ 1 / (a * y + b)) =
      (fun y : ℝ ↦ a⁻¹ * (1 / (y + b / a))) := by
    funext y
    rw [hlin y]
    simp [mul_comm]
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]
  change a⁻¹ * iteratedDeriv n (fun y : ℝ ↦ 1 / y) (x + b / a) = _
  rw [reciprocal_iteratedDeriv n _ hz, hlin x, mul_pow, pow_succ]
  field_simp
  ring


theorem pow_iteratedDeriv_at_degree (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ y ^ n) x = (n.factorial : ℝ) := by
  simp [Nat.descFactorial_self]


theorem pow_iteratedDeriv_factorial (n k : ℕ) (x : ℝ) (hk : k ≤ n) :
    iteratedDeriv k (fun y : ℝ ↦ y ^ n) x =
      (n.factorial : ℝ) / ((n - k).factorial : ℝ) * x ^ (n - k) := by
  rw [iteratedDeriv_pow]
  have hf : (((n - k).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hc : (((n - k).factorial : ℕ) : ℝ) * (n.descFactorial k : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hk
  congr 1
  apply (eq_div_iff hf).mpr
  simpa only [mul_comm] using hc

theorem pow_iteratedDeriv_above_degree (n k : ℕ) (x : ℝ) (hk : n < k) :
    iteratedDeriv k (fun y : ℝ ↦ y ^ n) x = 0 := by
  simp [Nat.descFactorial_of_lt hk]

/-- Ví dụ 4.1.21(a): công thức đạo hàm của sinh. -/
theorem hyperbolic_sine_iteratedDeriv (n : ℕ) (x : ℝ) :
    iteratedDeriv n Real.sinh x = (1 / 2 : ℝ) *
      (Real.exp x - (-1 : ℝ) ^ n * Real.exp (-x)) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show k + k = 2 * k by omega, Real.iteratedDeriv_even_sinh]
    rw [(show Even (2 * k) from ⟨k, by omega⟩).neg_one_pow]
    simp [Real.sinh_eq, div_eq_mul_inv, mul_comm]
  · rw [Real.iteratedDeriv_odd_sinh, (show Odd (2 * k + 1) from ⟨k, rfl⟩).neg_one_pow]
    simp [Real.cosh_eq, div_eq_mul_inv, mul_comm]

/-- Ví dụ 4.1.21(b): công thức đạo hàm của cosh. -/
theorem hyperbolic_cosine_iteratedDeriv (n : ℕ) (x : ℝ) :
    iteratedDeriv n Real.cosh x = (1 / 2 : ℝ) *
      (Real.exp x + (-1 : ℝ) ^ n * Real.exp (-x)) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show k + k = 2 * k by omega, Real.iteratedDeriv_even_cosh]
    rw [(show Even (2 * k) from ⟨k, by omega⟩).neg_one_pow]
    simp [Real.cosh_eq, div_eq_mul_inv, mul_comm]
  · rw [Real.iteratedDeriv_odd_cosh, (show Odd (2 * k + 1) from ⟨k, rfl⟩).neg_one_pow]
    simp [Real.sinh_eq, div_eq_mul_inv, mul_comm, sub_eq_add_neg]


theorem hyperbolic_domainSmooth {I : Set ℝ} (hI : IsOpen I) :
    DomainSmooth Real.sinh I ∧ DomainSmooth Real.cosh I :=
  ⟨(domainSmooth_iff_contDiffOn _ hI).mpr Real.contDiff_sinh.contDiffOn,
    (domainSmooth_iff_contDiffOn _ hI).mpr Real.contDiff_cosh.contDiffOn⟩


def quadraticExponentialCoefficient (n : ℕ) (x : ℝ) : ℝ :=
  4 * x ^ 2 + 4 * ((n : ℝ) - 3) * x + (n : ℝ) ^ 2 - 7 * n - 4


theorem quadratic_exponential_iteratedDeriv (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ (y ^ 2 - 3 * y - 1) * Real.exp (2 * y)) x =
      (2 : ℝ) ^ ((n : ℤ) - 2) * Real.exp (2 * x) * quadraticExponentialCoefficient n x := by
  induction n generalizing x with
  | zero =>
    simp only [iteratedDeriv_zero, quadraticExponentialCoefficient, Nat.cast_zero]
    norm_num
    ring
  | succ n ih =>
    have hp : HasDerivAt (𝕜 := ℝ) (F := ℝ) (quadraticExponentialCoefficient n)
        (8 * x + 4 * ((n : ℝ) - 3)) x := by
      convert! ((((hasDerivAt_id x).pow 2).const_mul 4).add
        ((hasDerivAt_id x).const_mul (4 * ((n : ℝ) - 3)))).add_const
        ((n : ℝ) ^ 2 - 7 * n - 4) using 1
      · funext y
        dsimp [quadraticExponentialCoefficient]
        ring
      · dsimp
        ring
    have he : HasDerivAt (𝕜 := ℝ) (F := ℝ) (fun y : ℝ ↦ Real.exp (2 * y))
        (Real.exp (2 * x) * 2) x :=
      by convert! (Real.hasDerivAt_exp (2 * x)).comp x ((hasDerivAt_id x).const_mul 2) using 1
         simp
    have hd := (he.const_mul ((2 : ℝ) ^ ((n : ℤ) - 2))).mul hp
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n
        (fun y : ℝ ↦ (y ^ 2 - 3 * y - 1) * Real.exp (2 * y)) =
      (fun y : ℝ ↦ (2 : ℝ) ^ ((n : ℤ) - 2) * Real.exp (2 * y) *
        quadraticExponentialCoefficient n y) := funext ih
    rw [hfun]
    change deriv ((fun y : ℝ ↦ (2 : ℝ) ^ ((n : ℤ) - 2) * Real.exp (2 * y)) *
      quadraticExponentialCoefficient n) x = _
    rw [hd.deriv]
    have hn : ((n + 1 : ℕ) : ℤ) - 2 = ((n : ℤ) - 2) + 1 := by omega
    rw [hn, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_one, quadraticExponentialCoefficient, Nat.cast_add, Nat.cast_one]
    ring


theorem quadratic_exponential_domainSmooth {I : Set ℝ} (hI : IsOpen I) :
    DomainSmooth (fun y : ℝ ↦ (y ^ 2 - 3 * y - 1) * Real.exp (2 * y)) I := by
  apply (domainSmooth_iff_contDiffOn _ hI).mpr
  exact (((contDiff_id.pow 2).sub (contDiff_const.mul contDiff_id)).sub contDiff_const |>.mul
    ((contDiff_const.mul contDiff_id).exp)).contDiffOn


theorem differentiableToOrderOn_succ_terminal (n : ℕ) (f : ℝ → ℝ) (I : Set ℝ) :
    DifferentiableToOrderOn (n + 1) f I ↔ DifferentiableToOrderOn n f I ∧
      DifferentiableOn ℝ (iteratedDerivWithin n f I) I := by
  constructor
  · intro h
    exact ⟨fun k hk ↦ h k (hk.trans_le n.le_succ), h n n.lt_succ_self⟩
  · rintro ⟨h, hn⟩ k hk
    by_cases hkn : k < n
    · exact h k hkn
    · have he : k = n := by omega
      simpa only [he] using hn


theorem restrictedIteratedDerivativeWithin_one (f : ℝ → ℝ) {I : Set ℝ} (hI : IsOpen I) (x : I) :
    restrictedIteratedDerivativeWithin 1 f I x = deriv f x := by
  simpa only [iteratedDeriv_one] using restrictedIteratedDerivativeWithin_eq_iteratedDeriv 1 f hI x


theorem quadratic_exponential_leibniz_expansion (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ (y ^ 2 - 3 * y - 1) * Real.exp (2 * y)) x =
      (n.choose 0 : ℝ) * (x ^ 2 - 3 * x - 1) * (2 : ℝ) ^ (n : ℤ) * Real.exp (2 * x) +
      (n.choose 1 : ℝ) * (2 * x - 3) * (2 : ℝ) ^ ((n : ℤ) - 1) * Real.exp (2 * x) +
      (n.choose 2 : ℝ) * 2 * (2 : ℝ) ^ ((n : ℤ) - 2) * Real.exp (2 * x) := by
  have hp0 : (2 : ℝ) ^ (n : ℤ) = (2 : ℝ) ^ ((n : ℤ) - 2) * 4 := by
    rw [show (n : ℤ) = ((n : ℤ) - 2) + 2 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hp1 : (2 : ℝ) ^ ((n : ℤ) - 1) = (2 : ℝ) ^ ((n : ℤ) - 2) * 2 := by
    rw [show (n : ℤ) - 1 = ((n : ℤ) - 2) + 1 by omega, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [quadratic_exponential_iteratedDeriv, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, Nat.cast_choose_two, hp0, hp1]
  dsimp [quadraticExponentialCoefficient]
  ring


theorem domainSmooth_iff_positive_orders (f : ℝ → ℝ) (I : Set ℝ) :
    DomainSmooth f I ↔ ∀ n : ℕ, 1 ≤ n → DifferentiableToOrderOn n f I := by
  constructor
  · intro h n _
    exact h n
  · intro h n
    cases n with
    | zero => exact fun k hk ↦ (Nat.not_lt_zero k hk).elim
    | succ n => exact h (n + 1) (Nat.succ_le_succ (Nat.zero_le n))


theorem exponential_affine_positive_order (n : ℕ) (_hn : 1 ≤ n) (a b x : ℝ)
    (ha : a ≠ 0) : iteratedDeriv n (fun y : ℝ ↦ Real.exp (a * y + b)) x =
      a ^ n * Real.exp (a * x + b) := exponential_affine_iteratedDeriv n a b x ha

theorem reciprocal_affine_positive_order (n : ℕ) (_hn : 1 ≤ n) (a b x : ℝ)
    (ha : a ≠ 0) (hx : x ≠ -b / a) :
    iteratedDeriv n (fun y : ℝ ↦ 1 / (a * y + b)) x =
      (-1 : ℝ) ^ n * (a ^ n * (n.factorial : ℝ)) / (a * x + b) ^ (n + 1) :=
  reciprocal_affine_iteratedDeriv n a b x ha hx


theorem sine_positive_index (k : ℕ) (_hk : 1 ≤ k) (x : ℝ) :
    iteratedDeriv 1 Real.sin x = Real.cos x ∧
      iteratedDeriv 3 Real.sin x = -Real.cos x ∧
      iteratedDeriv (2 * k + 1) Real.sin x = (-1 : ℝ) ^ k * Real.cos x ∧
      iteratedDeriv (2 * k + 1) Real.sin 0 = (-1 : ℝ) ^ k := by
  exact ⟨by simp,
    by simp,
    sine_odd_iteratedDeriv k x, sine_odd_iteratedDeriv_zero k⟩

theorem cosine_positive_index (k : ℕ) (_hk : 1 ≤ k) (x : ℝ) :
    iteratedDeriv (2 * k) Real.cos x = (-1 : ℝ) ^ k * Real.cos x ∧
      iteratedDeriv (2 * k) Real.cos 0 = (-1 : ℝ) ^ k :=
  ⟨cosine_even_iteratedDeriv k x, cosine_even_iteratedDeriv_zero k⟩

theorem source_add_positive_order (n : ℕ) (_hn : 1 ≤ n) {f g : ℝ → ℝ}
    {I : Set ℝ} (hI : IsOpen I) (hf : DifferentiableToOrderOn n f I)
    (hg : DifferentiableToOrderOn n g I) :
    DifferentiableToOrderOn n (fun x ↦ f x + g x) I ∧
      EqOn (iteratedDerivWithin n (fun x ↦ f x + g x) I)
        (fun x ↦ iteratedDerivWithin n f I x + iteratedDerivWithin n g I x) I :=
  ⟨(source_add_higher n hI hf hg).1, (source_add_higher n hI hf hg).2 n le_rfl⟩

theorem source_const_mul_positive_order (n : ℕ) (_hn : 1 ≤ n) {f : ℝ → ℝ}
    {I : Set ℝ} (hf : DifferentiableToOrderOn n f I) (c : ℝ) :
    DifferentiableToOrderOn n (fun x ↦ c * f x) I ∧
      EqOn (iteratedDerivWithin n (fun x ↦ c * f x) I)
        (fun x ↦ c * iteratedDerivWithin n f I x) I := source_const_mul_higher n hf c

theorem domainC_mono_positive_orders {m n : ℕ} (_hm : 1 ≤ m) (_hn : 1 ≤ n)
    {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hmn : m ≤ n) (hf : DomainC n f I) :
    DomainC m f I := domainC_mono hI hmn hf

theorem domainSmooth_domainC_positive_order {n : ℕ} (_hn : 1 ≤ n) {f : ℝ → ℝ}
    {I : Set ℝ} (hI : IsOpen I) (hf : DomainSmooth f I) : DomainC n f I :=
  domainSmooth_domainC hI hf

theorem hyperbolic_positive_order (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) :
    iteratedDeriv n Real.sinh x = (1 / 2 : ℝ) *
      (Real.exp x - (-1 : ℝ) ^ n * Real.exp (-x)) ∧
    iteratedDeriv n Real.cosh x = (1 / 2 : ℝ) *
      (Real.exp x + (-1 : ℝ) ^ n * Real.exp (-x)) :=
  ⟨hyperbolic_sine_iteratedDeriv n x, hyperbolic_cosine_iteratedDeriv n x⟩


theorem quadratic_exponential_positive_order (n : ℕ) (_hn : 1 ≤ n) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ (y ^ 2 - 3 * y - 1) * Real.exp (2 * y)) x =
      (2 : ℝ) ^ ((n : ℤ) - 2) * Real.exp (2 * x) * quadraticExponentialCoefficient n x :=
  quadratic_exponential_iteratedDeriv n x

end calculus.Chapter04.Section01Higher
