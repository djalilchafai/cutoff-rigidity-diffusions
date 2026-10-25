module

public import CutoffRigidity.Riemann.WitnessEigen
public import CutoffRigidity.Riemann.SplitGaussian
public import CutoffRigidity.Riemann.AssembleMain

/-! # Witness: joint satisfiability of the standing hypotheses of the Riemannian theorems

On `M = F = ℝ^k = EuclideanSpace ℝ (Fin k)` (`k ≥ 1`) with its standard manifold structure and
Mathlib's standard Riemannian metric, for `ρ > 0`, the potential
`V x = ρ‖x‖²/2 + (k/2) log (2π/ρ)` and the Gaussian `μ = e^{-V} dx = N(0, ρ⁻¹ I)` satisfy all the
standing hypotheses of `riemannian_wasserstein_estimate` and `riemannian_gaussian_splitting`
(except the diffusion-semigroup hypothesis of the former, which is not constructed here):
`V` smooth, `μ` a probability measure, `IsWeightedVolume`, `CD ρ V`, `mSpectralGap μ = ρ`,
and moreover `mFirstEigenDim μ V = k`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Witness

open CutCur CutoffRigidity

variable {k : ℕ}

/-- `e^{-V} dx` is the Gaussian `N(0, ρ⁻¹ I)`. -/
theorem gibbs_gaussPot_eq (ρ : ℝ) (hρ : 0 < ρ) :
    gibbs (gaussPot k ρ) = multivariateGaussian (0 : Rd k) (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  rw [multivariateGaussian_eq_withDensity k hρ, gibbs]
  congr 1
  funext x
  rw [exp_neg_gaussPot ρ hρ]
  congr 1
  rw [show ρ / (2 * Real.pi) = (2 * Real.pi / ρ)⁻¹ by rw [inv_div],
    Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  congr 2
  ring

theorem msmooth_gaussPot (ρ : ℝ) :
    ContMDiff 𝓘(ℝ, Rd k) 𝓘(ℝ, ℝ) ∞ (gaussPot k ρ) :=
  contMDiff_iff_contDiff.2 (contDiff_gaussPot ρ)

/-- **Non-vacuity witness.** The standing hypotheses of the two Riemannian theorems of the
Challenge are jointly satisfiable, on `ℝ^k` for every `k ≥ 1` and `ρ > 0`. -/
theorem exists_riemannian_instance (k : ℕ) (hk : 0 < k) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (V : Rd k → ℝ) (μ : Measure (Rd k)),
      ContMDiff 𝓘(ℝ, Rd k) 𝓘(ℝ, ℝ) ∞ V ∧ IsProbabilityMeasure μ ∧
        IsWeightedVolume (Rd k) μ V ∧ CD (Rd k) ρ V ∧ mSpectralGap (Rd k) μ = ρ ∧
        mFirstEigenDim (Rd k) μ V = k ∧ 0 < mFirstEigenDim (Rd k) μ V ∧
        μ = multivariateGaussian (0 : Rd k) (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  refine ⟨gaussPot k ρ, gibbs (gaussPot k ρ), msmooth_gaussPot ρ,
    isProbabilityMeasure_gibbs_gaussPot ρ hρ, isWeightedVolume_gibbs _, cd_gaussPot ρ,
    ?_, mFirstEigenDim_gaussPot ρ hρ hk, ?_, gibbs_gaussPot_eq ρ hρ⟩
  · rw [mSpectralGap_rd, spectralGap_gaussPot ρ hρ hk]
  · rw [mFirstEigenDim_gaussPot ρ hρ hk]; exact hk

/-- Sanity check: the project's proof of the Gaussian splitting applies to the witness (all
typeclass hypotheses of the theorem are met by `ℝ^k`), and returns the trivial splitting data. -/
theorem splitting_applies (k : ℕ) (hk : 0 < k) (ρ : ℝ) (hρ : 0 < ρ) :
    let k' := mFirstEigenDim (Rd k) (gibbs (gaussPot k ρ)) (gaussPot k ρ)
    ∃ (F' : Type) (_ : NormedAddCommGroup F') (_ : InnerProductSpace ℝ F')
      (_ : FiniteDimensional ℝ F') (N : Type) (_ : EMetricSpace N) (_ : ChartedSpace F' N)
      (_ : IsManifold 𝓘(ℝ, F') ∞ N) (_ : RiemannianBundle (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, F') ∞ F' (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsRiemannianManifold 𝓘(ℝ, F') N) (_ : MeasurableSpace F') (_ : BorelSpace F')
      (_ : MeasurableSpace N) (_ : BorelSpace N)
      (V' : N → ℝ) (μ' : Measure N)
      (Φ : Rd k ≃ₘ^∞⟮𝓘(ℝ, Rd k), 𝓘(ℝ, Rd k').prod 𝓘(ℝ, F')⟯ Rd k' × N),
      (ContMDiff 𝓘(ℝ, F') 𝓘(ℝ, ℝ) ∞ V' ∧ IsProbabilityMeasure μ' ∧ IsWeightedVolume F' μ' V' ∧
        CD F' ρ V') ∧
      (∀ x y, edist x y ^ 2 = edist (Φ x).1 (Φ y).1 ^ 2 + edist (Φ x).2 (Φ y).2 ^ 2) ∧
      (gibbs (gaussPot k ρ)).map Φ =
        (multivariateGaussian 0 (ρ⁻¹ • (1 : Matrix (Fin k') (Fin k') ℝ))).prod μ' := by
  have := isProbabilityMeasure_gibbs_gaussPot (k := k) ρ hρ
  have hgap : mSpectralGap (Rd k) (gibbs (gaussPot k ρ)) = ρ := by
    rw [mSpectralGap_rd, spectralGap_gaussPot ρ hρ hk]
  have h := Paper.riemannian_gaussian_splitting_base (Rd k) (msmooth_gaussPot ρ)
    (isWeightedVolume_gibbs _) hρ (cd_gaussPot ρ) hgap
  obtain ⟨F', i1, i2, i3, N, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, V', μ', Φ, h1, h2, h3, -⟩ := h
  exact ⟨F', i1, i2, i3, N, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, V', μ', Φ, h1, h2, h3⟩

end CutoffRigidity.Riemann.Witness
