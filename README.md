# Cutoff via rigidity: Lean development

This project is a Lean 4 formalization of the manuscript [cutcur-lean.tex](cutcur-lean.tex)
by Chafaï–Fathi, based on [arXiv:2412.15969v4](https://arxiv.org/abs/2412.15969v4).

**Status (1 November 2026, round 2).** `Challenge.lean` states 67 theorems and 67 definitions (850 lines, 87 KB): the 12 numbered results (Theorems 1.1, 1.5, 1.7, 1.9,
3.1, 3.6, Lemma 3.3, Remark 1.2, Corollaries 1.3, 1.4, 1.6, display (1.25)) and further claims of the
manuscript (Remarks 3.4 and 3.5, the Lichnerowicz bound (Euclidean and Riemannian), (R2) => (R1), examples, proof ingredients such as W2
contraction, entropy decay, Pinsker and Talagrand, the optimal constants, and the Section 4 items; see
[PALOMAR.md](PALOMAR.md)). `Solution.lean` proves all of them (no `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound` only). A `lake comparator` run inside the bwrap sandbox accepts the full 67-theorem pair
(con-ron 92444 declarations, nanoda and the Lean kernel; `comparator.json` lists the 67 theorems and 66 definitions, the structure `CutCur.Form` being checked as a dependency). The splitting theorem now also states the
potential identity of Theorem 3.6 and the connectedness and completeness of the factor.
A further block of 11 statements (Bochner identity and `CD ⇔ Ric + Hess V ≥ ρ`, Riemannian `k₁` bounds and Poincaré/log-Sobolev, Fisher
decay for all laws and its Dini form, Brownian scaling at the SDE level, the temperature SDE and cutoffs, W2 and entropy mixing times) is
stated and proved too (see PALOMAR.md, section "Cheap block integration"; flags are in the docstrings).
Two further theorems, `exists_stdBrownian` and `exists_langevin`, show that a standard Brownian motion exists and that the standing hypothesis
`IsLangevin` of all Langevin statements is satisfiable (for `C²` `V` with `Hess V ≥ 0`, the paper's convexity assumption, and probability Gibbs
measure); they rely on the vendored Brownian motion library of Degenne et al. (see Credits below).
Nine further statements (Armstrong-method round, 1 November 2026): kernel = SDE law for rigid curvature, pathwise Lemma 3.3, the integrated entropy-dissipation
inequality (general and Dirac initial laws), the static Dyson–OU statement on the Weyl chamber, the operator/polarization/chain-rule forms of the carré du champ, and the vector
form of the Bochner identity.
Round 2 (1 November 2026, second integration; every item went through a worker and an adversary AI pass, `extra-status/*-adversary.md`; the AI audit of the new and changed statements is pending): (a) the smoothness clause of `IsEuclideanLangevin`,
`IsSigmaLangevin` and of `W n` in `convex_interaction_cutoff` is now `C²` instead of `C^∞` (uniqueness of the diffusion semigroup for convex `C²` potentials is proved, `Extra/C2Uniq*`; 23 statements become stronger);
(b) the integrated de Bruijn identity is now an equality (`langevin_dissipation_eq_K'`, `langevin_dissipation_eq_dirac_K` replace the two inequality statements);
(c) `dyson_spectralGap`: `λ₁ = ρ` for the Dyson–OU law; (d) Gaussian isoperimetry, **quadratic potential `ρ|x|²/2 + c` only** (not general `Hess V ≥ ρ`): `gaussian_isoperimetric_functional` (Bobkov) and `gaussian_isoperimetric_sets`;
(e) the Rothaus alternative for an **abstract Dirichlet-type form** under a compactness hypothesis (`rothaus_alternative_ne`, `Form.Compact`) and **unconditionally for finite spaces** (`finite_rothaus`); the compact-manifold theorem is **not** proved;
(f) the round sphere in model form: `sphere_curvature` (`Ric = (d-1) g`, `CD(d-1)`, optimal) and `sphere_gap` (`λ₁ = d ≠ d-1`) for any manifold isometrically immersed in `S^d`: the sphere is **not** a witness of the hypothesis `hgap` of Theorem 1.9;
(g) `temperature_kernel`: the `σ`-diffusion kernel exists, is Gibbs-invariant and is the time change of the Euclidean Langevin kernel (convex `C²`).
Not formalized: see the section "What is not formalized" below. Theorem 1.9 is proved for every
`IsDiffusionSemigroup` `Pt`, with no extra hypothesis: uniqueness of the minimal diffusion, Bakry–Émery,
log-Sobolev, gap attainment and the Kuwada contraction are formalized (see [PALOMAR.md](PALOMAR.md)).
No human semantic review has taken place; the statements were checked only by an AI audit
(`verification/semantic-audit.md`).

**Corrections to the printed paper**, both reflected in the local manuscript and in the Lean statements
(details in [PAPER_AUDIT.md](PAPER_AUDIT.md)):
- *Theorem 1.7.* The arXiv v4 statement is false as printed. For the Ornstein–Uhlenbeck potential
  `V_d(x)=d|x|²/2+C_d` and singleton initial set `{sqrt(d)e₁}`, curvature is `d`, equilibrium is
  `N(0,I_d/d)`, and the TV mixing time is asymptotic to `log(d)/d`. The printed hypotheses hold, yet for
  `epsilon=1/4`, Wasserstein distance at `3t0/4` tends to zero and Fisher information at `5t0/4` tends to
  infinity. The Lean statement (`product_condition_cutoff`) adds the hypotheses `liminf κ > 0` and
  `t₀ → ∞` for the Fisher and Wasserstein conclusions. The counterexample is a written derivation, not
  checked in Lean.
- *Riemannian theorems.* The setup assumes completeness, connectedness and no boundary; a punctured plane
  is a counterexample otherwise. This is formalized in the Lean statements.

The sections below under "Checked scope" describe the supporting development, written in stages.

## Checked scope

- `CutoffRigidity/Asymptotics.lean`: exact exponential/logarithmic cancellation,
  real-power limits, and conditional scalar cutoff transfer lemmas.
- `CutoffRigidity/Scaling.lean`: a kernel-checked counterexample to the numerical
  inference `liminf curvature > 0` and `curvature*time → infinity` implies
  `time → infinity`. The counterexample uses `curvature=n`, `time=log(n)/n`.
  An eventual upper bound on curvature repairs this numerical inference.
- `CutoffRigidity/OUProfiles.lean`: inequalities and asymptotics for scalar
  Gaussian profiles. Genuine Gaussian distances are established separately in
  the transport, entropy and total variation modules.
- `CutoffRigidity/Transport.lean` and `SecondMoment.lean`: actual coupling
  infimum, Lipschitz pushforward inequality, and Dirac second-moment formula.
- `CutoffRigidity/Eigenmap.lean` and `Evaluation.lean`: eigenmap Lipschitz
  bound, exact ball maximum, and the Riesz/Parseval basis-independence argument.
- `CutoffRigidity/GaussianMoments.lean`: second moments of genuine Gaussian
  measures, including singular positive semidefinite covariances.
- `CutoffRigidity/TransportMoments.lean` and `GaussianTransport.lean`: matching
  coupling lower and upper bounds, giving the exact isotropic Gaussian W₂
  formula and its Mehler marginal specialization.
- `CutoffRigidity/OUKernel.lean`: measurable Mehler kernels, their semigroup
  law, Gaussian invariance, and exact equilibrium transport profile.
- `CutoffRigidity/ConvexInteraction.lean`: actual differential-operator
  calculation for the coordinate-sum eigenfunction.
- `CutoffRigidity/Gibbs.lean` and `AffineRigidity.lean`: full-support and
  zero-Hessian-to-affine steps.
- `verification/Audit.lean`: checks every imported project declaration for
  forbidden axiom dependencies.

Further checked components now include:

- `LangevinKernel.lean` and `LangevinSemigroup.lean`: construction of the actual
  nonlinear Brownian Langevin kernel, measurable solution map, pathwise
  contraction, and semigroup law.
- `EigenfunctionC2Rigidity.lean`: a C² pointwise eigenfunction in actual Gibbs
  L² is affine under the matching Hessian curvature bound. Compact difference
  quotients and cutoffs discharge global derivative integrability assumptions.
- `VectorMehlerLaw.lean`: the actual nonlinear process projected by normalized
  affine eigenfunctions has the Gaussian Mehler marginal, derived from the
  integral equation and Brownian covariance.
- `AffineWassersteinEstimate.lean`: actual nonlinear kernel lower bounds and
  set/ball supremum estimates. Upper bounds use proved contraction and an
  explicit Gibbs invariance hypothesis.
- Gaussian entropy, canonical density Fisher integrals, genuine total
  variation, Pinsker, and the unit-rate OU cutoff special cases are checked.

The actual classical L² eigenspace, unique representatives, evaluation norm Λ,
and its Wasserstein theorem are assembled in `ClassicalEigenspace.lean` and
`ClassicalWassersteinTheorem.lean`. `AffineWassersteinCutoff.lean` proves actual
squared Wasserstein cutoffs with explicit Poincaré and invariance hypotheses;
`AffineProjectedCutoffs.lean` proves actual early entropy and TV cutoffs.
`GibbsStationarity.lean` establishes weak stationarity for compact C² tests,
with integrability derived. `GaussianAverageGenerator.lean` proves the actual
small-time Brownian generator formula on compact C² tests. `FiniteDoobL2.lean`
and `L2FatouBounds.lean` supply the maximal-moment and limiting arguments
needed for stochastic generator development.

`CompactGibbsGenerator.lean`, `GibbsSobolev.lean` and
`GibbsSelfAdjoint.lean` construct the dense compact-test operator, its closed
gradient and energy form, and an actual nonnegative self-adjoint form
operator. `GibbsSobolevClassical.lean` uses cutoff approximation to connect
classical eigenfunctions to this form. `GibbsSelfAdjointEigenfunctions.lean`
places them in the actual operator domain and eigenspace. The reverse implication at the curvature equality rate is now proved by
weak Bochner cutoff rigidity; stochastic/form identification remains open.

The actual weighted Sobolev inclusion and resolvent are now proved compact in
`GibbsCompactEmbedding.lean`, by confinement, localization, quantitative
mollification and Arzelà–Ascoli. Actual operator eigenspaces are connected
to the compact resolvent in `GibbsSpectralEigenspaces.lean`.

`GibbsSpectralGap.lean` proves actual positive first-gap attainment and the
sharp Poincaré inequality; the zero eigenspace is proved to consist exactly
of constants. The weak Bochner cutoff proof now gives the curvature lower
bound for every positive operator eigenvalue and the actual first gap.
For convex diagonally invariant interactions, the actual first gap is proved
to equal the confinement rate, including after the source normalization.

The canonical L² heat semigroup is constructed from implicit Euler resolvents,
with strong continuity, symmetry, positivity, preservation of constants and
Gibbs integrals, and its actual operator-domain generator and weak forward
equation. Actual relative Fisher information is defined through the closed
Sobolev gradient. Smooth-domain entropy/Fisher dissipation and the Salez
reverse Pinsker and entropy-window components are checked. The full
log-Sobolev inequality is proved for arbitrary probability laws using actual
closed Sobolev roots and Fatou approximation.

The actual first eigenspace has genuine representatives, evaluation,
orthonormal bases and basis-independent Lambda. The Euclidean set/ball
Wasserstein theorem now derives every analytic bridge, including Gibbs
invariance for the constructed Brownian kernel. The stochastic L² semigroup
equals canonical form heat on all Gibbs L², with the exact strong generator
domain characterized by the actual self-adjoint graph.

Wasserstein cutoff is proved on balls and convex-interaction cubes around
the actual Gibbs barycenter, deriving
Poincare and the normalized eigenfamily internally. Actual spectral entropy/TV
lower cutoffs require no supplied Gaussian-law premise. Positive C¹ density
Fisher formulae, exponential Fisher decay, genuine density evolution and
bounded-positive compact-perturbation de Bruijn evolution are checked. Fisher
decay now holds for every probability law via actual closed-gradient energy
semicontinuity and genuine L¹ density approximation. The optimized BGL path
proves full entropy-cost regularization for every initial probability law,
including singular laws, through the proved compact C² entropy variational
formula. Positive-time Dirac transitions consequently have genuine RN densities
and finite relative entropy.

The Euclidean information cutoffs now use full entropy/Fisher evolution,
regularization and the literal sublogarithmic rate condition. The normalized
convex-interaction corollary packages all sixteen before/after limits for
Wasserstein, entropy, TV and Fisher on the source balls and cubes.

The product-condition theorem now packages all eight actual TV, entropy,
Fisher and Wasserstein cutoff limits. Its varentropy, Salez window, and
Talagrand inputs are derived. Full Gaussian splitting identifies the actual
first eigenspace dimension and the normalized product law in finite coordinates.
The cited Lᵖ extension and the Riemannian theorem remain unfinished. Complete
bounded vector fields have genuine global C¹ flows and parallel-flow metric
isometries; the zero level has a constructed C² manifold, induced metric and
actual product diffeomorphism. The complete paper is not yet formalized. Project proofs use only
`propext`, `Classical.choice` and `Quot.sound`, and contain no proof placeholders.

## Brownian-free Euclidean statements (25 October 2026)

Twenty-one Euclidean statements of `Challenge.lean` (Thm 1.1, Cor 1.3, 1.4, 1.6, Remarks 3.4/3.5, the W2 contraction, display (1.25), Thm 1.7, Lemma 3.3, the three mixing-time statements, the OU examples and Fisher
information, entropy/Fisher decay and Dini form, normalization and temperature cutoffs) no longer mention Brownian motion: they are stated for transition kernels `Pt`
(`IsEuclideanLangevin`, `IsRigidSequenceK`, `worstK`, `mixingTimeK`, ...). Amendment: Lemma 3.3 is stated in law form (the first version also assumed `V ∈ C^∞`; round 2 reinstated `C²`). The Brownian versions remain as `*_carrier` theorems used inside the proofs. The only statements still mentioning Brownian motion are the SDE-level
`normalization_sde`, `temperature_sde`, `exists_stdBrownian`, `exists_langevin`. See `PALOMAR.md`. The sandboxed Comparator accepts the solution (`verification/comparator-sandboxed.log`); no human review.

**Convexity and `C²` in the Brownian-free statements.** The Euclidean process statements are stated for `C²` potentials (kernel formulation `IsEuclideanLangevin`), as in the manuscript. Uniqueness of the diffusion kernel is proved for convex `C²` potentials
(`euclideanDiffusion_unique_convex`), and every such statement carries a convexity hypothesis (`Hess V ≥ ρ`, `RigidCurvature`, convex `W n`, or the explicitly smooth OU potential). Nonconvex potentials are not covered (the manuscript's setting is convex). The `C^∞` kernel results of the earlier version survive as
proof-side lemmas (`IsEuclideanLangevinInf` in `Extra/SmoothLangevin.lean`).

## What is not formalized

The 67 theorems are not the whole paper. Details: `PALOMAR.md`, `HUMAN_REVIEW.md` section 3, `scope-status/SUMMARY.md`, `extra-status/` (worker and adversary reports of the 1 November 2026 rounds, and `extra-status/integration-round2.md`).

- **Open or conjectural in the paper:** Question 1.10; `eq:loggradbound`.
- **Attempted, blocked, partial or without a precise statement:**
  - sphere: the Challenge has only the model-form statements `sphere_curvature` and `sphere_gap` (any `M^d` isometrically immersed in `S^d`: `Ric = (d-1) g`, `CD(d-1)` and its optimality, `λ₁ = d`). The concrete round sphere (`Extra/Sphere*`: the type `Sph d`, a probability weighted volume, `λ₁ = d ≠ d-1`, and `¬(1 ≤ k₁ ≤ d)`, so `hgap` cannot be dropped in `riemannian_k1_bounds`) is proved but is not a Challenge statement (about 100 lines of definitions). The sphere is not a witness of `hgap` in Theorem 1.9;
  - Gaussian isoperimetry: only the quadratic potential `ρ|x|²/2 + c` (`μ = 𝒩(0, ρ⁻¹ I)`); the general `CD(ρ,∞)` case (Bakry–Ledoux) is not formalized (the manuscript only says Bakry–Émery "implies" it);
  - Theorem 1.7 on manifolds (one sentence in the manuscript, no statement);
  - the Rothaus remark: only an abstract Dirichlet-type form `(Q, E)` under the hypothesis `Form.Compact`, and the unconditional finite-space case; the compact weighted Riemannian manifold (Sobolev embedding `H¹ ⊂ L^{2+δ}`, Rellich, density of smooth functions) is not formalized; the (VW) extremality claims are covered by `optimal_constants_extremal`;
  - Dyson: the static statement (`dyson_ou_static`) and `λ₁ = ρ` (`dyson_spectralGap`) are formalized; the Dyson–OU process and the Neumann realization of the generator are not.
- **Formalized only in a weakened or changed form:** `IsEuclideanLangevin`/`IsSigmaLangevin` are `C²` but the statements all assume convexity (uniqueness of the diffusion kernel is proved for convex `V` only); Theorem 1.9 with the diffusion encoded as `IsDiffusionSemigroup`; `normalization_sde` and `temperature_sde` take the SDE solutions as hypotheses, and `temperature_sde` and `temperature_kernel` add `Hess V ≥ ρ > 0`; Theorem 1.7 amended (the printed statement is false; the counterexample is a written derivation, not checked in Lean); (1.25) for finite `p` only; extra hypotheses `0 < d`, `0 < finrank`, and `hgap` for the `k₁` bounds; the Dyson Poincaré statement is for bounded smooth Lipschitz test functions with `h` extremal in the closure sense; Gaussian isoperimetry and the Rothaus alternative as described above.
- **Now formalized (previously listed here):** that `Pt t x` is the law of any SDE solution (`isLangevinSolution_map_eq_kernel_of_rigid`); the pathwise form of Lemma 3.3 (`eigenmap_is_ou_pathwise`); the Leibniz/chain rule and operator form of `carre`; the vector form of Bochner; `C²` instead of `C^∞` for the kernel statements; the equality `H(μ_s) - H(μ_t) = ∫_s^t I` for general laws (finite entropy at an earlier time) and Dirac laws; `λ₁ = ρ` for Dyson–OU; existence and uniqueness of the `σ`-diffusion kernel (`temperature_kernel`).
- **Not checked in Lean:** a curved Riemannian witness for the theorems of Section 1.4 (only the flat Gaussian on ℝᵏ and, in model form, the sphere); that `Form.Compact` holds for `H¹` of a compact manifold (only for finite spaces, `Rothaus.finite_compact`, not a Challenge statement); non-vacuity of the Gaussian isoperimetric statements for a non-constant test function (`gibbs_quadratic_isProb` only shows the measure hypothesis is satisfiable).

## How to rebuild and verify

Prerequisites: `elan` (the toolchain `v4.35.0-rc2` is read from `lean-toolchain`), `python3`, and,
for the Comparator step, `bwrap` (bubblewrap). Network access is needed on a fresh checkout.

1. **Build everything** (about 9650 jobs; this is long on a cold cache):
   ```sh
   lake exe cache get
   lake build
   ```
2. **Source and metadata checks** (no `sorry`/`axiom`/`native_decide` in the Solution side,
   `comparator.json` and `formalization.yaml` consistent with `Challenge.lean`):
   ```sh
   python3 scripts/check-palomar.py --ready
   ```
3. **Axioms.** `verification/Audit.lean` checks supporting results only. For the 48 endpoint theorems
   (`CutoffRigidity.Paper.*`), run a `#print axioms` on each from a scratch file importing `Solution`; each
   should depend only on `propext`, `Classical.choice`, `Quot.sound`. The Comparator in step 4 enforces the
   same permitted axioms.
   ```sh
   lake env lean verification/Audit.lean
   ```
4. **Official Comparator** (Lean kernel, nanoda and con-ron replay of `Solution.lean` against
   `Challenge.lean`):
   ```sh
   scripts/verify-comparator.sh
   ```
   Expect "Your solution is okay!". Logs from our runs: `verification/comparator-final.log`
   (no sandbox) and `verification/comparator-sandboxed.log` (bwrap sandbox).
   - If `bwrap` fails with `Can't mount on symlink destination /home` (when `/home` is a symlink),
     install the wrapper and put it first in `PATH`:
     ```sh
     mkdir -p /tmp/bwrapfix && cp scripts/bwrap-home-symlink-wrapper.sh /tmp/bwrapfix/bwrap
     chmod +x /tmp/bwrapfix/bwrap
     PATH=/tmp/bwrapfix:$PATH scripts/verify-comparator.sh
     ```
     It re-exposes the local `.lake/packages` read-only and otherwise leaves the sandbox unchanged.
5. **After editing `Challenge.lean`**, regenerate the derived files and repeat steps 1–4:
   ```sh
   python3 scripts/sync-statements.py   # CutoffRigidity/Statements.lean
   python3 scripts/gen-solution.py      # Solution.lean
   ```

These checks establish that the Lean proofs are kernel-valid and match the Challenge statements. They do
not replace human review that the statements faithfully formalize the paper; none has taken place
(`review.status: unchecked` in `formalization.yaml`; the AI audit is in `verification/semantic-audit.md`).

## Reproduction

The project pins Lean `v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; the manifest pins transitive dependencies.
On a fresh checkout with network access, run:

```sh
lake exe cache get
lake build
lake env lean verification/Audit.lean
python3 scripts/check-palomar.py
```

This workspace links `.lake/packages` to the shared package cache at
`~/S/Maths/Logiciels/Lean/mathlib-v4.35.0-rc2/packages`. Its Mathlib revision matches the
pinned commit; project build outputs remain local. This machine-specific link
is not part of the project sources.

## Human review

[HUMAN_REVIEW.md](HUMAN_REVIEW.md) is a draft checklist for the human semantic review, which has not taken place.

## Palomar status

[PALOMAR.md](PALOMAR.md) records the official requirements and the detailed status.

- **Challenge/Solution pair:** `Challenge.lean` states 67 theorems; `Solution.lean` proves all of
  them. `comparator.json` lists the 67 theorems and 67 definitions. The Comparator runs below were made for the
  earlier 12-theorem pair and must be repeated for the extended one.
- **Comparator (12-theorem pair, before the extension):** `lake comparator` accepted the solution (con-ron, nanda and the Lean kernel; 88114
  declarations), both without a sandbox (`verification/comparator-final.log`) and inside the bwrap
  sandbox (`verification/comparator-sandboxed.log`). Only `propext`, `Classical.choice` and
  `Quot.sound` are used.
- **Statement audit:** an AI audit of the 12 statements found no defect
  (`verification/semantic-audit.md`). A Gaussian witness (`Riemann/WitnessMain.lean`) shows the
  Riemannian hypotheses are jointly satisfiable.
- **Amendments:** Theorem 1.7 is stated with the amendment described in [PAPER_AUDIT.md](PAPER_AUDIT.md),
  since the printed version has a counterexample. The Riemannian setting assumes completeness and
  connectedness. Theorem 1.9 has no extra hypothesis on `Pt` beyond `IsDiffusionSemigroup`.
- **Not done:** no human semantic review (`review.status: unchecked` in `formalization.yaml`), no
  registry submission, and no responsible-human attestation. `formalization.yaml` is therefore not yet a submission.
- **Earlier replay reports** (62 results across ten exports; superseded by the full run above):
  [development](verification/development-replay.json), [core](verification/core-replay.json),
  [operator](verification/operator-replay.json), [spectral](verification/spectral-replay.json),
  [curvature](verification/curvature-replay.json), [rigidity](verification/rigidity-replay.json).

## Credits and licensing

New project code is Apache-2.0. The existence of Brownian motion (`exists_stdBrownian`, `exists_langevin`) uses the library
*Formalization of Brownian motion in Lean* by Rémy Degenne, Sebastian Ledvinka, Etienne Marion and Peter Pfaffelhuber
([arXiv:2511.20118](https://arxiv.org/abs/2511.20118); [brownian-motion](https://github.com/RemyDegenne/brownian-motion) and
[kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4)), Apache-2.0. The needed 29 modules are vendored under
[`vendor/`](vendor/README.md) with minimal porting patches (3 library files lightly patched, plus one added Mathlib backport module), with
their licence texts and origin commits; the Challenge does not depend on them. Only the new module `CutoffRigidity/Paper/ExistsBrownian.lean`
imports them (privately). The archived paper in `paper/` retains its The archived paper in `paper/` retains its
separate CC BY 4.0 licence and attribution; see `paper/SOURCE.txt`.
