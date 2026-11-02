module

public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Paper.EigenmapOU

/-! # Identification of the kernel with the SDE law, and pathwise Lemma 3.3

(a) For `IsEuclideanLangevinInf V Pt` and convex `V`, every solution `X` of the Langevin SDE
(`IsLangevinSolution`, on any carrier with a standard Brownian motion `B`) has law `Pt t x₀`.
Pathwise uniqueness (deterministic, via `langevin_path_unique`) and kernel uniqueness
(`isEuclideanDiffusion_unique`) are the ingredients.

(b) Pathwise Lemma 3.3: `Y = T(X)` solves `dY = -ρ Y dt + √(2ρ) dβ` with a standard Brownian `β`
on the same space (the eigenfunctions are affine, so no Itô formula is needed).
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ContDiff

/-- **(a)** Every solution of the Langevin SDE has the law prescribed by the kernel `Pt`. -/
theorem isLangevinSolution_map_eq_kernel {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : CutCur.Rd d → ℝ} {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.IsEuclideanLangevinInf V Pt)
    (hHess : ∀ x z : CutCur.Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} (hB : CutCur.IsStdBrownian B P)
    {x₀ : CutCur.Rd d} {X : ℝ≥0 → Ω → CutCur.Rd d}
    (hX : CutCur.IsLangevinSolution V B P x₀ X) (t : ℝ≥0) :
    P.map (X t) = Pt t x₀ := by
  have hB' : IsEuclideanBrownian B P := isStdBrownian_iff.1 hB
  have hV2 : ContDiff ℝ 2 V := hL.1.of_le (by norm_cast)
  have hH : ∀ x z : CutCur.Rd d, (0 : ℝ) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z; simpa using hHess x z
  rw [IsLangevinSolution.map_eq_langevinKernel hB' hV2 0 le_rfl hH hX t]
  exact (CutCur.isEuclideanDiffusion_eq_langevinKernel hB' hL.1 hL.2.1 0 le_rfl hH hL.2.2 t x₀).symm

/-- **(a)**, rigid-curvature form (convexity is implied by `RigidCurvature`). -/
theorem isLangevinSolution_map_eq_kernel_of_rigid {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : CutCur.Rd d → ℝ} {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.IsEuclideanLangevinInf V Pt) (hR : CutCur.RigidCurvature V)
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} (hB : CutCur.IsStdBrownian B P)
    {x₀ : CutCur.Rd d} {X : ℝ≥0 → Ω → CutCur.Rd d}
    (hX : CutCur.IsLangevinSolution V B P x₀ X) (t : ℝ≥0) :
    P.map (X t) = Pt t x₀ :=
  isLangevinSolution_map_eq_kernel hL hR.hess_nonneg hB hX t

/-- **(b)** Pathwise Lemma 3.3 for any Langevin solution family (`IsLangevin`): `Tv(X_t) = Tv x₀ - ρ ∫₀ᵗ Tv(X_s) ds + √(2ρ) β_t` almost surely for all `t`,
for a standard Brownian motion `β` on the same space. -/
theorem eigenmap_is_ou_pathwise {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : CutCur.Rd d → ℝ} (hV : CutCur.RigidCurvature V)
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hX : CutCur.IsLangevin V B P X)
    (T : Fin (CutCur.firstEigenDim V) → CutCur.Rd d → ℝ) (hT : CutCur.IsEigenbasis V T) :
    let ρ := CutCur.spectralGap V
    let Tv := fun x => (WithLp.toLp 2 fun i => T i x : CutCur.Rd (CutCur.firstEigenDim V))
    ∃ β : ℝ≥0 → Ω → CutCur.Rd (CutCur.firstEigenDim V), CutCur.IsStdBrownian β P ∧
      ∀ x₀, ∀ᵐ w ∂P, ∀ t : ℝ≥0,
        Tv (X x₀ t w) = Tv x₀ - ρ • (∫ s in (0 : ℝ)..(t : ℝ), Tv (X x₀ s.toNNReal w)) +
          Real.sqrt (2 * ρ) • β t w :=
  eigenmap_is_ou_carrier hX hV T hT

end CutoffRigidity.Paper
