module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Actual positive quadratic-distance weights under probability laws

The power-Harnack evaluation argument uses their true positive integrals.
Dominated convergence gives continuity and genuine compact lower bounds.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def quadraticDistanceWeightIntegral
    (μ : Measure E) (a : ℝ) (x : E) : ℝ := ∫ y, Real.exp (-a * ‖x-y‖ ^ 2) ∂μ

theorem quadraticDistanceWeight_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 ≤ a) (x : E) : Integrable (fun y => Real.exp (-a * ‖x-y‖ ^ 2)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  apply Eventually.of_forall
  intro y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _))

theorem quadraticDistanceWeightIntegral_pos (μ : Measure E) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 ≤ a) (x : E) : 0 < quadraticDistanceWeightIntegral μ a x :=
  integral_exp_pos (quadraticDistanceWeight_integrable μ ha x)

theorem continuous_quadraticDistanceWeightIntegral (μ : Measure E) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 ≤ a) : Continuous (quadraticDistanceWeightIntegral μ a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : E => (1 : ℝ))
  · exact Eventually.of_forall fun z => (quadraticDistanceWeight_integrable μ ha z).aestronglyMeasurable
  · exact Eventually.of_forall fun z => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _))
  · exact integrable_const 1
  · exact Eventually.of_forall fun y => (show Continuous (fun z : E => Real.exp (-a * ‖z-y‖ ^ 2)) by fun_prop).tendsto x

theorem exists_pos_le_quadraticDistanceWeightIntegral_on_compact
    (μ : Measure E) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a)
    (K : Set E) (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ quadraticDistanceWeightIntegral μ a x := by
  by_cases hn : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hn (continuous_quadraticDistanceWeightIntegral μ ha).continuousOn
    exact ⟨_,quadraticDistanceWeightIntegral_pos μ ha x,fun y hy => hmin hy⟩
  · exact ⟨1,by norm_num,fun x hx => False.elim (hn ⟨x,hx⟩)⟩

end CutoffRigidity
