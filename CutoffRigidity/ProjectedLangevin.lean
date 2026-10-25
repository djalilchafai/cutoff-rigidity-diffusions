module

public import CutoffRigidity.GeneratorIntertwining
public import CutoffRigidity.BrownianProjection
public import CutoffRigidity.LinearLangevinLaw

/-! # Actual affine projection of Langevin trajectories

The pointwise affine eigenfunction equations determine the projected drift.
Continuous linear maps commute with the Bochner integral, so projecting the
actual additive-noise integral equation gives a genuine linear Langevin
solution. Uniqueness identifies its canonical path, before any assertion
about its distribution.
-/

public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CutoffRigidity

variable {d k : ℕ}

/-- An actual affine projection solves the linear quadratic-potential
integral equation, with the genuinely projected additive noise. -/
theorem IsLangevinPathOn.affine_projection
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin k)) (ρ : ℝ)
    (heigen : ∀ x i, langevinDifferentialOperator V (fun y => (A y + b) i) x =
      -ρ * (A x + b) i)
    {w X : ℝ → EuclideanSpace ℝ (Fin d)} {x₀ : EuclideanSpace ℝ (Fin d)} {T : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) :
    IsLangevinPathOn (quadraticLangevinPotential ρ) (fun t => A (w t)) (A x₀ + b)
      (fun t => A (X t) + b) T := by
  refine ⟨(A.continuous.comp_continuousOn hX.1).add continuousOn_const, ?_⟩
  intro t ht
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  have hi : IntervalIntegrable (fun s => gradient V (X s)) volume 0 t :=
    ((hg.comp_continuousOn hX.1).mono
      (show Icc 0 t ⊆ Icc 0 T from fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)).intervalIntegrable_of_Icc ht.1
  have hgrad (x : EuclideanSpace ℝ (Fin d)) :
      A (gradient V x) = gradient (quadraticLangevinPotential ρ) (A x + b) := by
    rw [gradient_quadraticLangevinPotential]
    exact affine_projected_drift_of_coordinate_equations V A b ρ x (heigen x)
  have hI : (∫ s in 0..t, gradient (quadraticLangevinPotential ρ) (A (X s) + b)) =
      A (∫ s in 0..t, gradient V (X s)) := by
    simp_rw [← hgrad]
    exact A.intervalIntegral_comp_comm hi
  dsimp only
  rw [hI, hX.2 t ht, map_sub, map_add, map_sub]
  abel

/-- Uniqueness identifies the affine projection with the actual canonical
quadratic Langevin solution, with no projected-process assumption. -/
theorem langevinSolution_affine_projection
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin k)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (heigen : ∀ x i, langevinDifferentialOperator V (fun y => (A y + b) i) x =
      -ρ * (A x + b) i)
    {w : ℝ → EuclideanSpace ℝ (Fin d)} (hw : Continuous w)
    (x₀ : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    A (langevinSolution V w x₀ t) + b =
      langevinSolution (quadraticLangevinPotential ρ) (fun s => A (w s)) (A x₀ + b) t := by
  symm
  exact langevinSolution_eqOn_of_global_solution
    (contDiff_quadraticLangevinPotential ρ) ρ hρ
    (fun x z => (hessian_quadraticLangevinPotential ρ x z).ge)
    (A.continuous.comp hw)
    (fun T hT => (langevinSolution_isLangevinPathOn hV κ hκ hHess hw x₀ hT).affine_projection
      hV A b ρ heigen) ht

/-- The eigenmap sends the actual Brownian noise to `sqrt ρ` times the
standard orthogonal Brownian projection. This identity is pathwise. -/
theorem eigenmapCLM_brownianDrivingPath {Ω : Type*}
    (v : Fin k → EuclideanSpace ℝ (Fin d)) (ρ : ℝ)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) (s : ℝ) :
    eigenmapCLM v ρ (brownianDrivingPath B ω s) =
      Real.sqrt ρ • brownianDrivingPath (orthogonalBrownianProjection v B) ω s := by
  ext i
  simp only [eigenmapCLM_apply, eigenmapLinear, brownianDrivingPath,
    orthogonalBrownianProjection]
  change Real.sqrt ρ * inner ℝ (v i) (Real.sqrt 2 • B s.toNNReal ω) =
    Real.sqrt ρ * (Real.sqrt 2 * inner ℝ (v i) (B s.toNNReal ω))
  rw [inner_smul_right]

/-- The actual affine projected diffusion is the canonical linear solution
with the projected Brownian noise. Orthonormality additionally certifies
that this noise, before multiplication by `sqrt ρ`, is standard Brownian. -/
theorem langevinProcess_eigenmap_projection_ae
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (v : Fin k → EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin k)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (heigen : ∀ x i, langevinDifferentialOperator V
      (fun y => (eigenmapCLM v ρ y + b) i) x = -ρ * (eigenmapCLM v ρ x + b) i)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      eigenmapCLM v ρ (langevinProcess V B x₀ t ω) + b =
        langevinSolution (quadraticLangevinPotential ρ)
          (fun s => Real.sqrt ρ • brownianDrivingPath (orthogonalBrownianProjection v B) ω s)
          (eigenmapCLM v ρ x₀ + b) t := by
  filter_upwards [brownianDrivingPath_continuous_ae hB] with ω hω
  intro t
  have hnoise : (fun s => eigenmapCLM v ρ (brownianDrivingPath B ω s)) =
      fun s => Real.sqrt ρ • brownianDrivingPath (orthogonalBrownianProjection v B) ω s := by
    funext s
    exact eigenmapCLM_brownianDrivingPath v ρ B ω s
  change eigenmapCLM v ρ (langevinSolution V (brownianDrivingPath B ω) x₀ t) + b = _
  rw [← hnoise]
  exact langevinSolution_affine_projection hV κ hκ hHess (eigenmapCLM v ρ) b ρ hρ
    heigen hω x₀ t.coe_nonneg

end CutoffRigidity
