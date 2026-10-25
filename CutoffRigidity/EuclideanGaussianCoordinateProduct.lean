module
public import CutoffRigidity.EuclideanGaussianSplitting

/-! # Full Gaussian independence in ordinary finite Euclidean coordinates

The orthogonal subspace factors are transported by actual linear isometries
to Fin k and Fin (d-k) coordinate spaces (with the dimension equality supplied
by the Euclidean splitting theorem). The full first coordinate law is the
standard Gaussian scaled by 1/sqrt rho.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def affineGaussianCoordinates (V : E → ℝ) (ρ : ℝ) :=
  (affineEigenRowsBasis V ρ).repr

@[expose] noncomputable def affineComplementCoordinates (V : E → ℝ) (ρ : ℝ) :=
  (stdOrthonormalBasis ℝ (affineEigenRows V ρ)ᗮ).repr

@[expose] noncomputable def affineEuclideanSplittingCoordinates (V : E → ℝ) (ρ : ℝ) (x : E) :=
  Prod.map (affineGaussianCoordinates V ρ) (affineComplementCoordinates V ρ)
    (affineSplittingCoordinates V ρ x)

/-- The full coordinate Gaussian, with no independence or law hypothesis. -/
theorem affineRowGaussian_map_coordinates (V : E → ℝ) (ρ : ℝ) :
    (affineRowGaussian V ρ).map (affineGaussianCoordinates V ρ) =
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ (affineEigenRows V ρ))))).map
        (fun z => (Real.sqrt ρ)⁻¹ • z) := by
  let A := affineGaussianCoordinates V ρ
  have hA : Measurable A := A.continuous.measurable
  unfold affineRowGaussian
  rw [Measure.map_map hA (by fun_prop)]
  have heq : (fun z : affineEigenRows V ρ => A ((Real.sqrt ρ)⁻¹ • z)) =
      (fun z => (Real.sqrt ρ)⁻¹ • z) ∘ A := by
    funext z
    exact A.map_smul _ _
  change (stdGaussian (affineEigenRows V ρ)).map
    (fun z => A ((Real.sqrt ρ)⁻¹ • z)) = _
  rw [heq,← Measure.map_map (by fun_prop) hA,stdGaussian_map A]

set_option maxHeartbeats 650000 in
/-- A genuine product of the full k-dimensional Gaussian and complementary
probability in finite Euclidean coordinates, derived from the actual Gibbs law. -/
theorem normalized_gibbs_euclidean_coordinate_product
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (gibbsMeasure volume V).map (affineEuclideanSplittingCoordinates V ρ) =
      ((stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ (affineEigenRows V ρ))))).map
        (fun z => (Real.sqrt ρ)⁻¹ • z)).prod
      ((affineComplementLaw V ρ).map (affineComplementCoordinates V ρ)) := by
  obtain ⟨hprob,hprod⟩ := normalized_gibbs_affineSubspace_gaussian_product hV ρ hρ hHess hp
  let := hprob
  have hA : Measurable (affineGaussianCoordinates V ρ) :=
    (affineGaussianCoordinates V ρ).continuous.measurable
  have hB : Measurable (affineComplementCoordinates V ρ) :=
    (affineComplementCoordinates V ρ).continuous.measurable
  change (gibbsMeasure volume V).map
    (Prod.map (affineGaussianCoordinates V ρ) (affineComplementCoordinates V ρ) ∘
      affineSplittingCoordinates V ρ) = _
  rw [← Measure.map_map (hA.prodMap hB) (measurable_affineSplittingCoordinates V ρ),hprod,
    ← Measure.map_prod_map _ _ hA hB,affineRowGaussian_map_coordinates]

end CutoffRigidity
