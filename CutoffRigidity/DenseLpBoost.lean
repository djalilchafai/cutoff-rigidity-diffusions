module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Actual L²-to-Lᵖ improvement from a genuine dense core

Strong L² convergence gives convergence in measure. Its actual Fatou bound
extends a proved core estimate to the genuine L² operator without postulating
an extension or choosing unrelated pointwise representatives.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 600000 in
/-- A bound on an actual dense subspace controls the actual operator's full
Lᵖ seminorm. Density, continuity and convergence in measure do all extension
and representative identification work. -/
theorem eLpNorm_apply_le_of_dense_core
    (T : (α →₂[μ] ℝ) →L[ℝ] (α →₂[μ] ℝ))
    (S : Submodule ℝ (α →₂[μ] ℝ)) (hS : Dense (S : Set (α →₂[μ] ℝ)))
    (q : ENNReal) (C : ℝ)
    (hCore : ∀ u : S, eLpNorm (T u) q μ ≤ ENNReal.ofReal (C*‖(u : α →₂[μ] ℝ)‖))
    (u : α →₂[μ] ℝ) : eLpNorm (T u) q μ ≤ ENNReal.ofReal (C*‖u‖) := by
  obtain ⟨un,hun,hlim⟩ := mem_closure_iff_seq_limit.mp (hS u)
  have hTlim : Tendsto (fun n => T (un n)) atTop (𝓝 (T u)) := T.continuous.tendsto u |>.comp hlim
  have hMeasure := tendstoInMeasure_of_tendsto_Lp hTlim
  have hBudget : Tendsto (fun n => ENNReal.ofReal (C*‖un n‖)) atTop
      (𝓝 (ENNReal.ofReal (C*‖u‖))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim.norm.const_mul C)
  apply le_of_forall_gt_imp_ge_of_dense
  intro B hB
  apply eLpNorm_le_of_tendstoInMeasure _ hMeasure (fun n => Lp.aestronglyMeasurable _)
  filter_upwards [(tendsto_order.mp hBudget).2 B hB] with n hn
  exact (hCore ⟨un n,hun n⟩).trans hn.le

/-- Full actual Lᵖ membership and norm improvement follow from the dense
core bound; no target-space extension or law identity is a premise. -/
theorem memLp_apply_of_dense_core
    (T : (α →₂[μ] ℝ) →L[ℝ] (α →₂[μ] ℝ))
    (S : Submodule ℝ (α →₂[μ] ℝ)) (hS : Dense (S : Set (α →₂[μ] ℝ)))
    (q : ENNReal) (C : ℝ) (hC : 0 ≤ C)
    (hCore : ∀ u : S, eLpNorm (T u) q μ ≤ ENNReal.ofReal (C*‖(u : α →₂[μ] ℝ)‖))
    (u : α →₂[μ] ℝ) :
    ∃ hLp : MemLp (T u) q μ, ‖hLp.toLp (T u)‖ ≤ C*‖u‖ := by
  have hh := eLpNorm_apply_le_of_dense_core T S hS q C hCore u
  have hLp : MemLp (T u) q μ := hh.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hLp,?_⟩
  rw [Lp.norm_toLp]
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg u))] using he

end CutoffRigidity
