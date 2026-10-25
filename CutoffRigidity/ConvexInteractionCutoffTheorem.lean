module
public import CutoffRigidity.BarycenterInformationUpperCutoffs

/-! # Full source cutoff corollary for fixed-curvature convex interactions

The actual normalized potential, probability law, spectral gap, Gaussian
projection and invariant diffusion are constructed from the convex
interaction. Constant-rate asymptotic assumptions are proved internally.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω]

@[expose] noncomputable def normalizedConvexInteractionCutoffFamily
    (W : ∀ n : ℕ, EuclideanSpace ℝ (Fin n) → ℝ)
    (hW : ∀ n, ContDiff ℝ 2 (W n)) (hConv : ∀ n, ConvexOn ℝ univ (W n))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hInv : ∀ n x (t : ℝ), W n (x + t • diagonalDirection n) = W n x)
    (B : ∀ n : ℕ, NNReal → Ω → EuclideanSpace ℝ (Fin n)) (P : ℕ → Measure Ω)
    (hB : ∀ n, IsEuclideanBrownian (B n) (P n)) : ∀ n, ConvexInteractionCubeData Ω n :=
  fun n => {
    interaction := W n
    smooth := hW n
    convex := hConv n
    rate := ρ
    rate_pos := hρ
    diagonalInvariant := hInv n
    driver := B n
    noiseLaw := P n
    brownian := hB n }

/-- A positive fixed source rate has the literal positive lower limit. -/
theorem fixed_rate_positive_liminf {ρ : ℝ} (hρ : 0 < ρ) :
    0 < liminf (fun _ : ℕ => ENNReal.ofReal ρ) atTop := by
  simpa only [liminf_const] using ENNReal.ofReal_pos.mpr hρ

/-- The fixed source rate is genuinely sublogarithmic in dimension. -/
theorem fixed_rate_isLittleO_log (ρ : ℝ) :
    (fun _ : ℕ => ρ) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) :=
  Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop

set_option maxHeartbeats 650000 in
/-- Full Corollary 1.6 on both written initial sets: actual mean-centered
balls and actual mean-centered cubes. All four distances have their
before/after limits, with no probability, spectral gap, invariance,
projection, estimate, or rate-limit premise beyond the raw source data. -/
theorem normalized_convexInteraction_four_distance_cutoff
    (W : ∀ n : ℕ, EuclideanSpace ℝ (Fin n) → ℝ)
    (hW : ∀ n, ContDiff ℝ 2 (W n)) (hConv : ∀ n, ConvexOn ℝ univ (W n))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hInv : ∀ n x (t : ℝ), W n (x + t • diagonalDirection n) = W n x)
    (B : ∀ n : ℕ, NNReal → Ω → EuclideanSpace ℝ (Fin n)) (P : ℕ → Measure Ω)
    (hB : ∀ n, IsEuclideanBrownian (B n) (P n))
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    let D := normalizedConvexInteractionCutoffFamily W hW hConv ρ hρ hInv B P hB
    (Tendsto (fun n => barycenterBallWasserstein (cubeSpectralData (D n)) c
      ((1 - ε) * criticalTime n ρ)) atTop atTop ∧
     Tendsto (fun n => barycenterBallWasserstein (cubeSpectralData (D n)) c
      ((1 + ε) * criticalTime n ρ)) atTop (𝓝 0)) ∧
    (Tendsto (fun n => cubeWasserstein (D n) c ((1 - ε) * criticalTime n ρ)) atTop atTop ∧
     Tendsto (fun n => cubeWasserstein (D n) c ((1 + ε) * criticalTime n ρ)) atTop (𝓝 0)) ∧
    (Tendsto (fun n => meanBallKL (cubeSpectralData (D n)) c ((1 - ε) * criticalTime n ρ)) atTop (𝓝 ⊤) ∧
     Tendsto (fun n => meanBallKL (cubeSpectralData (D n)) c ((1 + ε) * criticalTime n ρ)) atTop (𝓝 0) ∧
     Tendsto (fun n => meanBallTV (cubeSpectralData (D n)) c ((1 - ε) * criticalTime n ρ)) atTop (𝓝 1) ∧
     Tendsto (fun n => meanBallTV (cubeSpectralData (D n)) c ((1 + ε) * criticalTime n ρ)) atTop (𝓝 0) ∧
     Tendsto (fun n => meanBallFisher (cubeSpectralData (D n)) c ((1 - ε) * criticalTime n ρ)) atTop (𝓝 ⊤) ∧
     Tendsto (fun n => meanBallFisher (cubeSpectralData (D n)) c ((1 + ε) * criticalTime n ρ)) atTop (𝓝 0)) ∧
    (Tendsto (fun n => convexCubeKL (D n) c ((1 - ε) * criticalTime n ρ)) atTop (𝓝 ⊤) ∧
     Tendsto (fun n => convexCubeKL (D n) c ((1 + ε) * criticalTime n ρ)) atTop (𝓝 0) ∧
     Tendsto (fun n => convexCubeTV (D n) c ((1 - ε) * criticalTime n ρ)) atTop (𝓝 1) ∧
     Tendsto (fun n => convexCubeTV (D n) c ((1 + ε) * criticalTime n ρ)) atTop (𝓝 0) ∧
     Tendsto (fun n => convexCubeFisher (D n) c ((1 - ε) * criticalTime n ρ)) atTop (𝓝 ⊤) ∧
     Tendsto (fun n => convexCubeFisher (D n) c ((1 + ε) * criticalTime n ρ)) atTop (𝓝 0)) := by
  let D := normalizedConvexInteractionCutoffFamily W hW hConv ρ hρ hInv B P hB
  have hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop := fixed_rate_positive_liminf hρ
  have hliminfS : 0 < liminf (fun n => ENNReal.ofReal (cubeSpectralData (D n)).rate) atTop := hliminf
  have hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) := fixed_rate_isLittleO_log ρ
  have hsubS : (fun n => (cubeSpectralData (D n)).rate) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) := hsub
  exact ⟨⟨barycenter_wasserstein_before_cutoff (fun n => cubeSpectralData (D n)) hc hε hε1,
    barycenter_wasserstein_after_cutoff (fun n => cubeSpectralData (D n)) hc.le hε hliminfS⟩,
    ⟨cube_wasserstein_before_cutoff D hc hε hε1, cube_wasserstein_after_cutoff D hc.le hε hliminf⟩,
    meanBall_information_cutoff (fun n => cubeSpectralData (D n)) hc hε hε1 hliminfS hsubS,
    convexCube_information_cutoff D hc hε hε1 hliminf hsub⟩

end CutoffRigidity
