module

public import CutoffRigidity.OperatorWassersteinTheorem
public import CutoffRigidity.AffineProjectedCutoffs
public import CutoffRigidity.ConvexInteractionSpectralGap

/-! # Actual first-eigenspace entropy and total-variation lower cutoffs

The actual attained spectral gap and weak Bochner rigidity construct the
entire normalized affine eigenspace internally. Its actual Gaussian
projection gives the paper's information lower cutoffs. Neither equilibrium
invariance, centering, Poincaré, an affine family nor a projected law is a
premise. No upper information estimate is asserted here.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

/-- Source assumptions needed for the lower projection argument alone.
The spectral assertion is required in the positive dimensions of the source
sequence; the zero-dimensional entry is a harmless natural-index padding. -/
structure SpectralInformationLowerData (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  potential : EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ContDiff ℝ 2 potential
  rate : ℝ
  rate_pos : 0 < rate
  hessian : ∀ x z, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ potential) x z z
  probability : IsProbabilityMeasure (gibbsMeasure volume potential)
  spectral : 0 < d → gibbsSpectralGap smooth probability = rate
  driver : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)
  noiseLaw : Measure Ω
  brownian : IsEuclideanBrownian driver noiseLaw

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem spectralInformation_rows_finrank_pos (D : SpectralInformationLowerData Ω d) (hd : 0 < d) :
    0 < Module.finrank ℝ (affineEigenRows D.potential D.rate) := by
  have h := firstEigenspace_finrank_pos D.smooth D.probability hd D.rate D.rate_pos D.hessian (D.spectral hd)
  rwa [firstEigenspace_finrank_eq_operator D.smooth D.probability D.rate (D.spectral hd),
    operatorEigenspace_finrank_eq_classical D.smooth D.probability D.rate D.rate_pos D.hessian,
    classicalL2Eigenspace_finrank_eq_rows D.smooth D.rate D.rate_pos D.hessian D.probability] at h

/-- The dimension of the internally constructed affine projection is the
dimension of the actual first self-adjoint operator eigenspace. -/
theorem spectralInformation_rows_finrank_eq_first (D : SpectralInformationLowerData Ω d) (hd : 0 < d) :
    Module.finrank ℝ (affineEigenRows D.potential D.rate) =
      Module.finrank ℝ (gibbsFirstEigenspace D.smooth D.probability) := by
  rw [firstEigenspace_finrank_eq_operator D.smooth D.probability D.rate (D.spectral hd),
    operatorEigenspace_finrank_eq_classical D.smooth D.probability D.rate D.rate_pos D.hessian,
    classicalL2Eigenspace_finrank_eq_rows D.smooth D.rate D.rate_pos D.hessian D.probability]

/-- A genuine orthonormal basis of the actual first eigenspace, transported
from the canonical normalized affine rows through the proved isometries. -/
@[expose] noncomputable def spectralInformationFirstBasis
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d) :
    OrthonormalBasis (Fin (Module.finrank ℝ (affineEigenRows D.potential D.rate))) ℝ
      (gibbsFirstEigenspace D.smooth D.probability) :=
  (classicalEigenOrthonormalBasis D.smooth D.rate D.rate_pos D.hessian D.probability).map
    (((firstEigenCurvatureIsometry D.smooth D.probability D.rate (D.spectral hd)).trans
      (operatorEigenClassicalIsometry D.smooth D.probability D.rate D.rate_pos D.hessian)).symm)

/-- All affine-family fields used by the actual projected-Gaussian proof
are constructed from the canonical first eigenspace. -/
@[expose] noncomputable def spectralInformationToAffine (D : SpectralInformationLowerData Ω d) :
    AffineProjectedCutoffData Ω d where
  potential := D.potential
  smooth := D.smooth
  curvature := D.rate
  curvature_nonneg := D.rate_pos.le
  hessian := D.hessian
  probability := D.probability
  rate := D.rate
  rate_pos := D.rate_pos
  driver := D.driver
  noiseLaw := D.noiseLaw
  brownian := D.brownian
  coordinateCount := Module.finrank ℝ (affineEigenRows D.potential D.rate)
  row := fun hd => ⟨0, spectralInformation_rows_finrank_pos D hd⟩
  coefficient := fun i => (affineEigenBasisCoefficient D.potential D.rate i : EuclideanSpace ℝ (Fin d))
  constant := fun i => affineEigenConstant D.potential D.rate (affineEigenBasisCoefficient D.potential D.rate i)
  eigenfunction := affineEigenBasisFunction_eigenfunction D.potential D.rate_pos
  orthonormal := affineEigenBasisFunction_integral_mul D.potential
    (D.smooth.differentiable (by norm_num)) D.rate_pos D.probability

@[expose] noncomputable def spectralBallKL (D : SpectralInformationLowerData Ω d) (c t : ℝ) : ℝ≥0∞ :=
  ⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
    klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)

@[expose] noncomputable def spectralBallTV (D : SpectralInformationLowerData Ω d) (c t : ℝ) : ℝ :=
  sSup ((fun x => totalVariationDistance
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential)) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d))

/-- The genuine entropy lower estimate obtained by data processing of the
actual first-eigenspace Gaussian projection. -/
theorem spectralBallKL_lower (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    ENNReal.ofReal (D.rate * c ^ 2 / 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤
      spectralBallKL D c t :=
  affineBallKL_lower (spectralInformationToAffine D) hd hc ht

theorem spectralBallTV_le_one (D : SpectralInformationLowerData Ω d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    spectralBallTV D c t ≤ 1 :=
  affineBallTV_le_one (spectralInformationToAffine D) hc t

/-- The genuine TV lower estimate obtained by an actual separating
halfspace in the internally constructed Gaussian projection. -/
theorem spectralBallTV_lower (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    1 - 8 / (D.rate * c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤
      spectralBallTV D c t :=
  affineBallTV_lower (spectralInformationToAffine D) hd hc ht

theorem spectral_entropy_before_cutoff_of_eventual_rate_lower
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hpositive : ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ (D n).rate) :
    Tendsto (fun n : ℕ => spectralBallKL (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) :=
  affine_entropy_before_cutoff_of_eventual_rate_lower
    (fun n => spectralInformationToAffine (D n)) hc hε hε1 hpositive

theorem spectral_totalVariation_before_cutoff_of_eventual_rate_lower
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hpositive : ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ (D n).rate) :
    Tendsto (fun n : ℕ => spectralBallTV (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) :=
  affine_totalVariation_before_cutoff_of_eventual_rate_lower
    (fun n => spectralInformationToAffine (D n)) hc hε hε1 hpositive

/-- The extended positive lower limit includes rates tending to infinity. -/
theorem spectralInformation_rates_eventually_positive_lower
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ (D n).rate := by
  obtain ⟨s, hs0, hs⟩ := exists_between hliminf
  have hsfin : s ≠ ⊤ := ne_of_lt (hs.trans_le le_top)
  have hr : 0 < s.toReal := ENNReal.toReal_pos hs0.ne' hsfin
  have hevent : ∀ᶠ n in atTop, s < ENNReal.ofReal (D n).rate := eventually_lt_of_lt_liminf hs
  refine ⟨s.toReal, hr, ?_⟩
  filter_upwards [hevent] with n hn
  rw [← ENNReal.ofReal_toReal hsfin] at hn
  exact ((ENNReal.ofReal_lt_ofReal_iff (D n).rate_pos).mp hn).le

/-- Actual entropy diverges on the source starting balls before the
critical time; the actual spectral equality supplies the projection. -/
theorem spectral_entropy_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => spectralBallKL (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) :=
  spectral_entropy_before_cutoff_of_eventual_rate_lower D hc hε hε1
    (spectralInformation_rates_eventually_positive_lower D hliminf)

/-- Actual total variation tends to one before the critical time,
without an equilibrium-invariance or upper-information premise. -/
theorem spectral_totalVariation_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => spectralBallTV (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) :=
  spectral_totalVariation_before_cutoff_of_eventual_rate_lower D hc hε hε1
    (spectralInformation_rates_eventually_positive_lower D hliminf)

/-- The canonical affine family used in the Gaussian projection consists
exactly of the continuous representatives of an actual first-eigenspace ONB. -/
theorem spectralInformationFirstBasis_representative
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    (i : Fin (Module.finrank ℝ (affineEigenRows D.potential D.rate)))
    (x : EuclideanSpace ℝ (Fin d)) :
    firstEigenRepresentative D.smooth D.probability D.rate D.rate_pos D.hessian (D.spectral hd)
      (spectralInformationFirstBasis D hd i) x = affineEigenBasisFunction D.potential D.rate i x := by
  let e := (firstEigenCurvatureIsometry D.smooth D.probability D.rate (D.spectral hd)).trans
    (operatorEigenClassicalIsometry D.smooth D.probability D.rate D.rate_pos D.hessian)
  let b := classicalEigenOrthonormalBasis D.smooth D.rate D.rate_pos D.hessian D.probability
  have he : e (spectralInformationFirstBasis D hd i) = b i := by
    change e (e.symm (b i)) = b i
    exact e.apply_symm_apply (b i)
  change classicalEigenRepresentative D.potential D.rate (e (spectralInformationFirstBasis D hd i)) x = _
  rw [he]
  exact classicalEigenOrthonormalBasis_representative D.smooth D.rate D.rate_pos D.hessian D.probability i x

/-- The actual canonical first-eigenspace affine projection. -/
@[expose] noncomputable def spectralInformationEigenmap (D : SpectralInformationLowerData Ω d) :
    EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (affineEigenRows D.potential D.rate))) :=
  affineEigenfunctionMap (spectralInformationToAffine D).coefficient (spectralInformationToAffine D).constant

/-- Actual equilibrium projection is standard Gaussian, as a theorem
about the genuine pushforward measure rather than a data field. -/
theorem spectralInformationEigenmap_gibbs_law (D : SpectralInformationLowerData Ω d) :
    (gibbsMeasure volume D.potential).map (spectralInformationEigenmap D) =
      stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ (affineEigenRows D.potential D.rate)))) := by
  exact gibbsMeasure_map_affineEigenfunctionMap D.smooth
    (spectralInformationToAffine D).coefficient (spectralInformationToAffine D).constant D.rate D.rate_pos
    (spectralInformationToAffine D).eigenfunction D.probability (spectralInformationToAffine D).orthonormal

/-- The actual nonlinear Langevin kernel has the derived OU law under
the canonical first-eigenspace projection. No invariance premise is used. -/
theorem spectralInformationEigenmap_kernel_law (D : SpectralInformationLowerData Ω d)
    (x : EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) :
    (langevinKernel D.potential D.driver D.noiseLaw t x).map (spectralInformationEigenmap D) =
      ouLaw D.rate t (spectralInformationEigenmap D x) := by
  exact langevinKernel_map_affineEigenfunctionMap D.brownian D.smooth D.rate D.rate_pos.le D.hessian
    (spectralInformationToAffine D).coefficient (spectralInformationToAffine D).constant D.rate D.rate_pos
    (spectralInformationToAffine D).eigenfunction D.probability (spectralInformationToAffine D).orthonormal x t

/-- The normalized convex, diagonally invariant interaction supplies all
spectral lower-cutoff data internally, including the exact actual first
gap and the probability normalization of its genuine Gibbs measure. -/
@[expose] noncomputable def normalizedConvexInteractionInformationLowerData
    {W : EuclideanSpace ℝ (Fin d) → ℝ} (hW : ContDiff ℝ 2 W)
    (hconv : ConvexOn ℝ Set.univ W) (ρ : ℝ) (hρ : 0 < ρ)
    (hinv : ∀ x : EuclideanSpace ℝ (Fin d), ∀ t : ℝ,
      W (x + t • diagonalDirection d) = W x)
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) : SpectralInformationLowerData Ω d := by
  let Z := ∫ x : EuclideanSpace ℝ (Fin d), Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))
  let Wn (x : EuclideanSpace ℝ (Fin d)) := W x + Real.log Z
  let Vn (x : EuclideanSpace ℝ (Fin d)) := ρ / 2 * ‖x‖ ^ 2 + Wn x
  have hWn : ContDiff ℝ 2 Wn := hW.add contDiff_const
  have hconvn : ConvexOn ℝ Set.univ Wn := hconv.add_const _
  have hinvn : ∀ x : EuclideanSpace ℝ (Fin d), ∀ t : ℝ,
      Wn (x + t • diagonalDirection d) = Wn x := by
    intro x t
    dsimp only [Wn]
    rw [hinv]
  have hVn : ContDiff ℝ 2 Vn := (contDiff_const.mul (contDiff_norm_sq ℝ)).add hWn
  have hp : IsProbabilityMeasure (gibbsMeasure volume Vn) := by
    simpa only [Vn, Wn, Z, add_assoc] using
      (convexInteraction_normalized_probability_memLp_two hW hconv ρ hρ).1
  exact {
    potential := Vn
    smooth := hVn
    rate := ρ
    rate_pos := hρ
    hessian := hessian_quadratic_add_convex_lower hWn hconvn ρ
    probability := hp
    spectral := fun hd => convexInteraction_spectralGap_eq hd hWn hconvn hρ hinvn hp hVn
    driver := B
    noiseLaw := P
    brownian := hB }

/-- The real-liminf formulation used when the rate lower limit is finite. -/
theorem spectral_entropy_before_cutoff_of_real_liminf
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => (D n).rate) atTop) :
    Tendsto (fun n : ℕ => spectralBallKL (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) :=
  affine_entropy_before_cutoff (fun n => spectralInformationToAffine (D n)) hc hε hε1 hliminf

theorem spectral_totalVariation_before_cutoff_of_real_liminf
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => (D n).rate) atTop) :
    Tendsto (fun n : ℕ => spectralBallTV (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) :=
  affine_totalVariation_before_cutoff (fun n => spectralInformationToAffine (D n)) hc hε hε1 hliminf

end CutoffRigidity
