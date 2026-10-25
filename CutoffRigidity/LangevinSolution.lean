module

public import CutoffRigidity.LangevinGlobalExistence

/-!
# A canonical selected forward Langevin solution

The actual deterministic existence and uniqueness theorems select a single
solution map depending only on the potential, initial point, and continuous
driving path. The map is defined for all inputs by classical selection; its
specification below is proved under precisely the potential and noise
hypotheses used for existence. It does not depend on a choice of curvature
certificate or differentiability proof.

Measurable dependence on the driving path is not inferred merely from this
classical selection. Initial-point Lipschitz dependence is proved explicitly.
-/

public section

open Set
open scoped Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A canonical selected path. Its actual integral-equation specification is
proved below; no specification is asserted for inputs without a solution. -/
@[expose] noncomputable def langevinSolution (V : E → ℝ) (w : ℝ → E) (x₀ : E) : ℝ → E :=
  Classical.epsilon (fun X : ℝ → E => ∀ T ≥ (0 : ℝ), IsLangevinPathOn V w x₀ X T)

/-- The selected path solves the original Langevin integral equation on every
finite forward interval. -/
theorem langevinSolution_isLangevinPathOn [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    IsLangevinPathOn V w x₀ (langevinSolution V w x₀) T := by
  exact (Classical.epsilon_spec (exists_global_langevin_path hV rate hrate hHess hw x₀)) T hT

/-- Initial condition of the actual selected solution. -/
theorem langevinSolution_initial [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x₀ : E) :
    langevinSolution V w x₀ 0 = x₀ :=
  (langevinSolution_isLangevinPathOn hV rate hrate hHess hw x₀ (le_refl 0)).initial (le_refl 0)

/-- Every actual forward solution agrees with the selected path. -/
theorem langevinSolution_eqOn_of_global_solution [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) {x₀ : E} {X : ℝ → E}
    (hX : ∀ T ≥ (0 : ℝ), IsLangevinPathOn V w x₀ X T) :
    EqOn (langevinSolution V w x₀) X (Ici 0) := by
  intro t ht
  exact langevin_path_unique hV rate hHess
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hw x₀ ht)
    (hX t ht) ⟨ht, le_rfl⟩

/-- The selected solution is continuous on the full forward half-line. -/
theorem langevinSolution_continuousOn [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x₀ : E) :
    ContinuousOn (langevinSolution V w x₀) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hT : (0 : ℝ) ≤ t + 1 := by linarith
  have hc := (langevinSolution_isLangevinPathOn hV rate hrate hHess hw x₀ hT).1 t
    (show t ∈ Icc 0 (t + 1) by exact ⟨ht, le_add_of_nonneg_right zero_le_one⟩)
  apply hc.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_one t))] with s hs hs'
  exact ⟨hs, hs'.le⟩

/-- Curvature contraction for the actual selected solution as a function of
its initial point, with the same continuous driving path. -/
theorem langevinSolution_initial_point_contraction [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x₀ y₀ : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖langevinSolution V w x₀ t - langevinSolution V w y₀ t‖ ≤
      Real.exp (-rate * t) * ‖x₀ - y₀‖ :=
  langevin_same_noise_contraction hV rate hHess
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hw x₀ ht)
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hw y₀ ht) ht

/-- In particular, initial-point dependence is Lipschitz, hence continuous
and measurable, once a continuous driving path is fixed. -/
theorem langevinSolution_initial_point_lipschitz [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith ⟨Real.exp (-rate * t), Real.exp_nonneg _⟩
      (fun x₀ => langevinSolution V w x₀ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x₀ y₀
  rw [dist_eq_norm, dist_eq_norm]
  exact langevinSolution_initial_point_contraction hV rate hrate hHess hw x₀ y₀ ht

end CutoffRigidity
