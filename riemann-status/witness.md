# witness: joint satisfiability of the Riemannian standing hypotheses (flat R^k)

Status: DONE, fully checked (`lake build` of each module; no sorry/axiom/native_decide; axioms of
`exists_riemannian_instance`, `splitting_applies`, `mFirstEigenDim_gaussPot`, `cd_gaussPot`,
`gibbs_gaussPot_eq`: propext, Classical.choice, Quot.sound only). No definition bug found: CD is satisfiable.
No existing file edited; `CutoffRigidity.lean` not touched (lead must add the imports below).

Files (namespace `CutoffRigidity.Riemann.Witness`, chain of imports, top module = WitnessMain):
* WitnessGeometry: `instIsContMDiffRiemannianBundleRd` (Prop instance, all smoothness orders n, from Mathlib's
  `riemannianMetricVectorSpace`; Mathlib's own TC search times out for `Rd k` at orders 1/inf, hence this instance),
  `mgrad_rd` (mgrad = gradient), `chartAt_rd`, `chartVolumeDensity_rd` (= 1), `isWeightedVolume_gibbs`
  (IsWeightedVolume (Rd k) (gibbs V) V for ANY V), `inner_cov_rd` (Koszul on flat space), `mlaplacian_rd`
  (mlaplacian = Euclidean laplacian for C^2 f).
* WitnessBochner: `gamma2_euclid` (Gamma_2(f) = ||D^2 f||^2 + D^2V(grad f, grad f), f, V smooth, coordinate computation),
  `carre_rd`, `mgenerator_rd`, `carre2_rd`.
* WitnessGauss: `gaussPot k rho` (V x = rho/2 ||x||^2 + (k/2) log(2 pi/rho)), `contDiff_gaussPot`, `gradient_gaussPot`,
  `hessian_gaussPot`, `cd_gaussPot : CD (Rd k) rho (gaussPot k rho)` (for every rho, any k),
  `isProbabilityMeasure_gibbs_gaussPot` (rho > 0).
* WitnessGap: `spectralGap_gaussPot` (CutCur.spectralGap = rho, k>0; upper bound via affine eigenfunction, lower bound via
  library Bakry-Emery gap), `mSpectralGap_rd : mSpectralGap (Rd k) (gibbs V) = CutCur.spectralGap V`.
* WitnessEigen: `isMEigenfunction_iff_gaussPot`, `firstEigenDim_gaussPot`, `mFirstEigenDim_gaussPot : = k`.
* WitnessMain: `gibbs_gaussPot_eq : gibbs (gaussPot k rho) = multivariateGaussian 0 (rho^-1 • 1)`, `msmooth_gaussPot`,
  `exists_riemannian_instance (k) (hk : 0 < k) (rho) (hrho : 0 < rho) : exists V mu, ContMDiff V /\ IsProbabilityMeasure mu /\
  IsWeightedVolume (Rd k) mu V /\ CD (Rd k) rho V /\ mSpectralGap (Rd k) mu = rho /\ mFirstEigenDim (Rd k) mu V = k /\
  0 < mFirstEigenDim .. /\ mu = multivariateGaussian 0 (rho^-1 • 1)`, and `splitting_applies`: the project's
  `Paper.riemannian_gaussian_splitting` (AssembleMain) is applied to the witness (so all typeclass hypotheses
  IsRiemannianManifold/ConnectedSpace/CompleteSpace/Measurable/Borel hold for Rd k and the conclusion is inhabited).

Not done: the diffusion-semigroup hypothesis `IsDiffusionSemigroup F V Pt` of `riemannian_wasserstein_estimate` is NOT
instantiated (would need the explicit OU/Mehler kernels on the Challenge Kolmogorov-equation formulation). Only the
non-vacuity of the measure/geometry hypotheses is established.
