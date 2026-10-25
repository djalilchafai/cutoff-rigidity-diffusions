# Riemannian branch: work plan for agents

Goal: replace the two remaining `sorry`s of `Challenge.lean` by proofs
`CutoffRigidity.Paper.riemannian_wasserstein_estimate` and
`CutoffRigidity.Paper.riemannian_gaussian_splitting` of exactly the Challenge types
(section `Riemannian`, lines ~320-455 of `Challenge.lean`; it is mirrored verbatim in
`CutoffRigidity/Statements.lean`). Source proofs: `cutcur-lean.tex`, "Proof of Theorem
main_thm_riem" (line ~1322, Cheng-Zhou splitting + Lemma lem_rig) and the Euclidean proof of
Theorem th:maineucl (line ~943), which is reused through the splitting.

## Rules (all agents)
* Lean 4 / Mathlib pinned by the project (`lake env lean FILE` to check one file, `lake build
  MODULE` to build a module; the whole project is already built under `.lake`). Never run
  `lake clean`, never touch `lake-manifest.json`/`lakefile.toml`.
* No `sorry`, no `axiom`, no `native_decide`, nothing but `propext`, `Classical.choice`,
  `Quot.sound`. Do not weaken or change `Challenge.lean`/`Statements.lean`. If a Challenge
  definition or hypothesis makes a statement false or unprovable, STOP on that point and
  describe the exact obstruction (with a proof sketch of why) in your status file; do not
  paper over it with extra hypotheses.
* The files use the `module` system: `module`, `public import ...`, `public section` /
  `@[expose]` for defs you want to unfold elsewhere. Copy the header style of existing files
  such as `CutoffRigidity/RiemannianParallelFlow.lean`.
* Put new files in `CutoffRigidity/Riemann/` (module names `CutoffRigidity.Riemann.<Name>`).
  Do not edit files owned by another agent or existing files outside `Riemann/` except to add a
  lemma needed upstream (then say so in your status file). Do not edit `CutoffRigidity.lean`
  (the lead wires imports).
* Many tools exist already: see the `Riemannian*.lean`, `Parallel*.lean`, `Manifold*.lean`,
  `SmoothRegularLevelManifold.lean`, `CompleteFlowLevelProduct.lean`, `ProductRiemannianMetric.lean`
  files (actual Riemannian gradient/Hessian/Laplacian, chart volume density, parallel
  gradient flows being isometries, level manifold of a parallel gradient, product homeomorphism
  and C¹ diffeomorphism) and the whole Euclidean development (`Paper/*.lean`, `Gibbs*.lean`,
  `OperatorWassersteinTheorem.lean`, ...) whose proofs you should imitate. Euclidean results
  about `EuclideanSpace` can often be reused on the Euclidean factor.
* Do not duplicate: before proving something, grep the project (`grep -rn "theorem name"`)
  and Mathlib (under `/chome/djay/S/Maths/Logiciels/Lean/mathlib-v4.35.0-rc2/packages/mathlib`).
* Work in small compiled steps; keep each file < 1500 lines. Heavy `maxHeartbeats` only
  when necessary and always with `set_option ... in`.
* Report in `riemann-status/<your-name>.md` (create the directory if needed): what is proved
  (exact declaration names and statements), what is open, precise blockers. At the end
  return a short summary. Honest status is required; a partial but fully checked result is
  far better than an unchecked claim.

## Workstreams and interfaces

### A. `weighted` : weighted-manifold foundations and Hessian rigidity of first eigenfunctions
Files `CutoffRigidity/Riemann/Weighted*.lean`. From `IsWeightedVolume F μ V` build:
integration by parts `∫ Γ(f,g) dμ = -∫ f 𝓛g dμ` for smooth `f,g` with `f` or `g` compactly
supported (chart/partition-of-unity computation with the chart volume density; completeness and
`MemLp` growth control as needed), `∫ 𝓛 f dμ = 0` for compactly supported smooth `f`, the
pointwise Bochner identity `Γ₂(f) = ‖Hess f‖² + Ric_V(∇f,∇f)` in the form needed (and the
passage from the Challenge's `CD ρ V` (`ρ Γ(f) ≤ Γ₂(f)` for all smooth `f`) to
`Γ₂(f) ≥ ‖Hess f‖² + ρ Γ(f)`, e.g. by testing against functions with prescribed 2-jet), the
cutoff argument that makes the integrated Bochner formula valid for `L²` eigenfunctions, and
finally

`theorem manifold_eigenfunction_parallel_gradient` : under the hypotheses of
`riemannian_gaussian_splitting` (hV, hμ, hρ, hCD, hgap), every `f` with
`IsMEigenfunction F μ V ρ f` has parallel gradient (vanishing Levi-Civita derivative of `mgrad F f`).
Also: positivity/attainment facts about `mSpectralGap` needed to identify `mFirstEigenDim`.

### B. `splitting` : global geometric splitting and the statement of `riemannian_gaussian_splitting`
Files `CutoffRigidity/Riemann/Split*.lean`. Assume (as a hypothesis of an internal lemma, to be
discharged by workstream A) parallel gradients of eigenfunctions. Using the existing parallel-flow
and level-manifold development, build the isometry `M ≃ ℝ × f⁻¹(0)` (smooth diffeo + distance
identity `edist² = ...`), iterate over an orthonormal basis of the eigenspace to get
`M ≃ ℝ^k × N`, put the induced manifold structure/metric/measurability on `N`, factor the weighted
measure `μ.map Φ = γ ⊗ μ'` (Gaussian factor from `CD`+`∫Γ(f)=ρ‖f‖²`, see Euclidean
`Paper/GaussianFactorization.lean` and `AffineEigenfunctionSplitting.lean`), show `CD(ρ)` for
`(N, μ')`, and the statements about `a`, `‖a‖² = ρ‖f‖²`, orthogonality of the `a`'s (lem_rig).
Final deliverable: `riemannian_gaussian_splitting_of_parallel` : the full Challenge conclusion
assuming only the parallel-gradient hypothesis (a `∀ f, IsMEigenfunction ... → parallel`
premise), stated so that workstream A's theorem plugs in.

### C. `transport` : diffusion semigroup, Gibbs invariance, and the Wasserstein estimate
Files `CutoffRigidity/Riemann/Transport*.lean`. Assume the conclusion of the splitting as an
internal hypothesis (a structure packaging `Φ`, `a`, Gaussian marginal etc.). Prove the two-sided
W₂ estimate of `riemannian_wasserstein_estimate` by following Section 3 of the paper through the
isometry: Lipschitz eigenmap lower bound and exact OU/Mehler law of the projection under the
abstract `Pt`, equilibrium Gaussian transport, the ball refinement, the upper bound through
invariance of `μ`/contraction. FIRST decide whether the Challenge's `IsDiffusionSemigroup`
(Markov, semigroup law, Kolmogorov equation on smooth compactly supported test functions) is
strong enough for each step (invariance of `μ`, law of the affine eigenmap under `Pt`,
contraction/upper bound). If a step is genuinely false or needs uniqueness/conservativity
that the hypothesis does not give, document the counterexample/obstruction precisely in your
status file and state the minimal additional property that is true for the actual minimal
diffusion; continue with everything else.
