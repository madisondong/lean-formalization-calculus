import calculus.Chapter03.Section04
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Bài tập 3.6.2(a). -/
namespace calculus.Chapter03.Section06FixedCellExercises
open Set Filter Topology
open calculus.Chapter03.Section04

def fixedCellDomain (n : ℝ) : Set ℝ := Ioc (n*Real.pi) ((n+1)*Real.pi)

noncomputable def fixedCellFunction (n a b x : ℝ) : ℝ :=
  if x ≤ (n+1/2)*Real.pi then Real.sin (x+a) else Real.cos (x+b)

theorem fixed_cell_branch_values (n a b x : ℝ) (hx : x ∈ fixedCellDomain n) :
    ((x ≤ (n+1/2)*Real.pi → fixedCellFunction n a b x = Real.sin (x+a)) ∧
      ((n+1/2)*Real.pi < x → fixedCellFunction n a b x = Real.cos (x+b))) := by
  have _ := hx
  exact ⟨fun h ↦ if_pos h, fun h ↦ if_neg (not_le.mpr h)⟩

/-- Bài tập 3.6.2(a): điều kiện tham số cho hàm liên tục trên một ô với n cố định. -/
theorem exercise02_fixed_cell_parameters (n a b : ℝ) :
    DomainContinuousOn (fixedCellDomain n) (fixedCellFunction n a b) ↔
      Real.sin ((n+1/2)*Real.pi+a) = Real.cos ((n+1/2)*Real.pi+b) := by
  classical
  let m := (n+1/2)*Real.pi
  have hlo : n*Real.pi < m := by dsimp [m]; nlinarith [Real.pi_pos]
  have hhi : m < (n+1)*Real.pi := by dsimp [m]; nlinarith [Real.pi_pos]
  have hm : m ∈ fixedCellDomain n := ⟨hlo, hhi.le⟩
  constructor
  · intro hc
    have hwithin := (domainContinuousAt_iff_within hm).mp (hc m hm)
    have hat : ContinuousAt (fixedCellFunction n a b) m :=
      hwithin.continuousAt (Ioc_mem_nhds hlo hhi)
    have hr : Tendsto (fixedCellFunction n a b) (𝓝[>] m) (𝓝 (Real.cos (m+b))) := by
      have hcos : Tendsto (fun x : ℝ ↦ Real.cos (x+b)) (𝓝[>] m) (𝓝 (Real.cos (m+b))) :=
        ((Real.continuous_cos.comp (continuous_id.add continuous_const)).tendsto m).mono_left
          nhdsWithin_le_nhds
      apply hcos.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : ¬x ≤ (n+1/2)*Real.pi := not_le.mpr (show (n+1/2)*Real.pi < x from hx)
      simp only [fixedCellFunction, if_neg hx']
    have he := tendsto_nhds_unique
      (hat.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] m ≤ 𝓝 m)) hr
    have hvalue : fixedCellFunction n a b m = Real.sin (m+a) :=
      if_pos (show m ≤ (n+1/2)*Real.pi from le_refl m)
    rw [hvalue] at he
    exact he
  · intro hmatch
    have hc : Continuous (fixedCellFunction n a b) := by
      apply Continuous.if (p := fun x : ℝ ↦ x ≤ (n+1/2)*Real.pi)
      · intro x hx
        have hx' : x=(n+1/2)*Real.pi := by
          simpa only [show {x : ℝ | x ≤ (n+1/2)*Real.pi} = Iic ((n+1/2)*Real.pi) from rfl,
            frontier_Iic, mem_singleton_iff] using hx
        simpa only [hx'] using hmatch
      · exact Real.continuous_sin.comp (continuous_id.add continuous_const)
      · exact Real.continuous_cos.comp (continuous_id.add continuous_const)
    exact fun x hx ↦ (domainContinuousAt_iff_within hx).mpr hc.continuousAt.continuousWithinAt

/-- Bài tập 3.6.2(a): điều kiện pha khi n nguyên. -/
theorem fixed_cell_integer_phase_condition (n : ℤ) (a b : ℝ) :
    Real.sin (((n : ℝ)+1/2)*Real.pi+a) =
      Real.cos (((n : ℝ)+1/2)*Real.pi+b) ↔ Real.cos a = -Real.sin b := by
  have hleft : ((n : ℝ)+1/2)*Real.pi+a = (a+Real.pi/2)+(n : ℝ)*Real.pi := by ring
  have hright : ((n : ℝ)+1/2)*Real.pi+b = (b+Real.pi/2)+(n : ℝ)*Real.pi := by ring
  rw [hleft, hright, Real.sin_add_int_mul_pi, Real.cos_add_int_mul_pi,
    Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
  exact ⟨mul_left_cancel₀ (zpow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)),
    fun h ↦ congrArg (fun t : ℝ ↦ (-1 : ℝ)^n*t) h⟩

end calculus.Chapter03.Section06FixedCellExercises
