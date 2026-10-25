# Cutoff via rigidity: Lean development

**Manuscript correction on 23 October 2026:** the local Riemannian setup and
theorems now explicitly assume completeness, connectedness, and no boundary.
The rigidity proof explains where completeness supplies a global flow and
product splitting. This addresses the punctured-plane counterexample found
by two agents; see [PAPER_AUDIT.md](PAPER_AUDIT.md). The correction has not
yet been formalized in Lean.

This project targets the local manuscript [cutcur-lean.tex](cutcur-lean.tex)
by Chafaï–Fathi, based on [arXiv:2412.15969v4](https://arxiv.org/abs/2412.15969v4).
**The full paper has not been formalized.** The existing source audit concerns
the archived arXiv version, where it found a counterexample to the Wasserstein
and Fisher conclusions of Theorem 1.7 as printed. The local target adds a
time-divergence hypothesis to that theorem and the Riemannian assumptions
described above. Full source alignment with the Lean development remains
incomplete.

**Status (25 October 2026).** `Challenge.lean` states 12 theorems; `Solution.lean` proves all
of them (no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only), and a local
`lake comparator` run (without the bwrap sandbox) accepts it. Theorem 1.9 is proved for every
`IsDiffusionSemigroup` `Pt`, with no extra hypothesis: uniqueness of the minimal diffusion, Bakry–Émery,
log-Sobolev, gap attainment and the Kuwada contraction are formalized (see PALOMAR.md). The older
paragraphs below describe intermediate stages.
For the Ornstein–Uhlenbeck potential `V_d(x)=d|x|²/2+C_d` and singleton initial
set `{sqrt(d)e₁}`, curvature is `d`, equilibrium is `N(0,I_d/d)`, and the TV
mixing time is asymptotic to `log(d)/d`. The printed hypotheses hold, yet for
`epsilon=1/4`, Wasserstein distance at `3t0/4` tends to zero and Fisher
information at `5t0/4` tends to infinity. See [PAPER_AUDIT.md](PAPER_AUDIT.md)
for explicit estimates using the actual TV threshold mixing time and the
complete theorem inventory. This probabilistic counterexample is a written
mathematical derivation; it has not been fully checked in Lean.

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

## Palomar status

[PALOMAR.md](PALOMAR.md) records the official requirements and remaining checks.
The metadata and Comparator configuration are explicitly incomplete drafts;
there is no paper-level Challenge/Solution pair. Sixty-two results across ten exports passed
proof replay by Lean, NanoDa and con-ron; see
[the first report](verification/development-replay.json) and
[the core report](verification/core-replay.json) and
[the operator report](verification/operator-replay.json), and
[the spectral report](verification/spectral-replay.json), and
[the curvature report](verification/curvature-replay.json), and
[the rigidity report](verification/rigidity-replay.json).
No full-paper Comparator run, registry registration, or human semantic review
is claimed.
A corrected Theorem 1.7 must be labeled as amended; `t0_d → infinity` is one
possible added hypothesis for the specific Wasserstein/Fisher transfer steps.

New project code is Apache-2.0. The archived paper in `paper/` retains its
separate CC BY 4.0 licence and attribution; see `paper/SOURCE.txt`.
