# R2 worker report (Sigma)

File: CutoffRigidity/Extra/Sigma.lean (builds; no sorry; axioms propext, Classical.choice, Quot.sound).
Proved (namespace CutCur):
- kolmogorov_timeScale, markov_semigroup_timeScale (generic time change u -> a u)
- isSigmaDiffusion_iff (hσ : 0<σ) (hV : Differentiable ℝ V):
  IsSigmaDiffusion V σ Pt ↔ IsEuclideanDiffusion (fun x => V x/σ^2) (fun u => Pt (((σ^2)⁻¹).toNNReal * u))
- isSigmaLangevin_iff (hσ): same for IsSigmaLangevin / IsEuclideanLangevin
- exists_sigmaLangevin (hσ) (hV : ContDiff ℝ ∞ V) (hp : IsProbabilityMeasure (gibbs fun x => V x/σ^2)) : ∃ Pt, IsSigmaLangevin V σ Pt   (NO convexity)
- sigmaLangevin_eq_timeChange: Pt t x = Q ((σ^2).toNNReal * t) x for any IsEuclideanLangevin (V/σ²) Q
- isSigmaLangevin_unique, isEuclideanLangevin_invariant, isSigmaLangevin_invariant
  ((gibbs fun x => V x/σ^2).bind (Pt t) = gibbs fun x => V x/σ^2)
- temperature_kernel: compact bundle (existence ∧ invariance ∧ time change).
