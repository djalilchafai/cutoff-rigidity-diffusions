# Palomar preparation status

This is an incomplete formalization project, not a Palomar submission. An empty
Comparator theorem list is intentional: it prevents supporting lemmas from being
advertised as a completed formalization of arXiv:2412.15969v4. The draft metadata
does not assign human authorship or maintenance responsibility. The new project
code uses Apache-2.0; the downloaded paper sources retain CC-BY-4.0.

Requirements were checked against the [official submission guide](https://palomar-registry.org/how-to-submit),
[binding submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and [official template](https://github.com/PalomarRegistry/PalomarTemplate) on
23 October 2026. Recheck those sources before an actual submission, since they
are live documents. The template describes newer bundled verifier tooling than
some older policy paragraphs; use the tooling selected by the supported pinned
toolchain and preserve its actual report.

## Local preparation checklist

- Pin Lean and every dependency. Mathlib's resolved toolchain must match Lean.
- Use `module` throughout; expose the interface with public declarations and imports.
- Keep regular Lean sources within 10,000 lines; keep Challenge within 1,000 lines and 100 KiB.
- State the actual paper claims in Challenge, including ordinary definitions and every hypothesis.
- Keep Challenge imports within the allowed library closure; project proof modules belong in Solution.
- Give Solution the same declaration names and types, with complete kernel-checked proofs.
- Permit only `propext`, `Classical.choice` and `Quot.sound`; audit every advertised endpoint.
- Record all omissions, stronger assumptions and AI work, and identify the responsible humans.
- Provide matching SPDX metadata and one root licence; preserve sources' separate licences.
- Run source checks, builds, metadata validation, Comparator and independent kernel checks.
- Preserve the exact checked commit and reports. A successful build alone proves no source alignment.

`scripts/check-palomar.py` performs conservative local source checks and reports
whether the minimum submission scaffolding is populated. It is a convenience
check, not the official verifier or a semantic audit. `--ready` fails until
required submission fields exist. A missing endpoint is a development gap, not
an invitation to insert `sorry` in the proof.

`scripts/verify-comparator.sh` mirrors the current template's use of bundled
NanoDa and con-ron tools. It runs only after the readiness check. It does not
submit or register anything. A submitted config must not contain
`external_kernels`; the local wrapper puts that setting in a temporary config.

## Paper fidelity gates

Use PAPER_AUDIT.md as the theorem/dependency inventory. Each paper theorem needs
an explicit mapping to its Lean declaration before it enters `theorem_names`.
Conditional consequences of contraction estimates, numerical identities for
Gaussian profiles, and finite-dimensional algebra may be useful intermediate
results; none alone proves the diffusion theorems. In particular, assuming
spectral rigidity, Wasserstein contraction or entropy regularization as a field
of a structure leaves those bridges unproved. Such assumptions must remain
visible in any interim theorem and be discharged for the original claims.

Six intermediate results passed exported-proof replay by Lean's kernel,
NanoDa, and con-ron in verified mode. The precise declaration list, export
hash, checker configuration and logs are recorded in
`verification/development-replay.json`. This checks that proof stream, not
source alignment through Comparator. The export is stored outside the project
at its recorded local path; no immutable Git source snapshot is available in
this workspace.

Human semantic review and full-paper Comparator/independent verification
remain outstanding. No registry endorsement, registration or completed
full-paper verification is claimed here.

Five newer core results (C² rigidity, actual kernel semigroup, projected Mehler
law, actual affine transport lower bound and Pinsker) also pass Lean, NanoDa
and con-ron exported-proof replay. See `verification/core-replay.json`; its
export and logs are distinct from the earlier six-result replay. This does
not add a full-paper Comparator or semantic-alignment claim.

Five actual operator/generator results also pass all three exported-proof
replays, including self-adjointness and actual nonlinear-kernel small-time
generator consistency. `verification/operator-replay.json` records the third
export, its hash, configuration and separate logs. These remain intermediate
results; no full-paper Comparator or source semantic verification is claimed.

Six further compactness, attained-gap/Poincare, Dynkin-martingale and information
results passed all three independent exported-proof replays. The fourth report,
`verification/spectral-replay.json`, records the exact six declarations and proof
stream hash. Across four streams, 22 intermediate results have been replayed.
This remains distinct from paper-level Comparator alignment.

The fifth stream, `verification/curvature-replay.json`, passed Lean, NanoDa
and con-ron for four further intermediate weak-Bochner curvature/gap and heat
results. The total is now 26 results across five streams. Paper-level Comparator
alignment and external human review remain outstanding.

The sixth stream, `verification/rigidity-replay.json`, passed all three
independent replay kernels for seven additional intermediate rigidity, spectral
cutoff, gradient, stopping, evolution uniqueness and occupation results.
Across six streams, 33 distinct results have been replayed. This does not
constitute a full-paper Comparator check.

The seventh stream, `verification/endpoints-replay.json`, passed Lean, NanoDa
and con-ron (70,058 declarations accepted). Its eight selected results include
genuine stochastic Gibbs invariance, full semigroup and generator-domain
identification, the actual Euclidean Wasserstein theorem, barycenter/cube
Wasserstein cutoffs, the full log-Sobolev inequality and complete parallel
gradient trajectory existence. There are now 41 distinct selected results
across seven streams. This remains separate from full-paper Comparator and
human semantic review; the entropy upper and manifold endpoints remain open.

The eighth stream, `verification/information-replay.json`, passed all three
checkers (con-ron accepted 70,147 declarations). It adds six actual full Fisher
decay, arbitrary-law entropy regularization, RN existence, variational entropy,
C¹ flow and Fisher lower-cutoff results. The selected replay total is 47 across
eight streams. Full-paper Comparator and external semantic review remain open.

The ninth stream, `verification/cutoffs-replay.json`, passed Lean, NanoDa and
con-ron (71,670 declarations accepted). Eight selected results include both-set
all-distance convex cutoff, actual mean-ball/cube information cutoffs, full
entropy/Fisher evolution, full C¹ transition Poincare and actual parallel-flow
isometry. The replay selection totals 55 across nine streams. Full-paper
Comparator, finite-p/product-condition/manifold completion and human semantic
review remain outstanding.

The tenth proof stream, `verification/product-replay.json`, checks seven new
actual product-condition, Sobolev-domain and level-manifold declarations. All
three independent checkers accept it; con-ron verifies 69,387 declarations.
The stream has 601,577,523 bytes and SHA-256
`5e653faed2ff37f3904eb153c4ddc6db84b91a0d176f79113dfc5b315662d639`.
This brings the distinct checked selection to 62 results across ten exports;
it does not certify the unfinished full-paper endpoints.

## Statement-surface bridges (24 October 2026)

All ten Euclidean statements of `Challenge.lean` (`main_wasserstein_estimate`,
`eigenspace_dim_and_lambda`, `wasserstein_cutoff`, `information_cutoff`, `lp_cutoff`,
`convex_interaction`, `convex_interaction_cutoff`, `product_condition_cutoff`,
`euclidean_gaussian_factorization`, `eigenmap_is_ou`) now have proofs
`CutoffRigidity.Paper.<name>` of exactly the Challenge type, depending only on `propext`,
`Classical.choice` and `Quot.sound`. They were checked by compiling the Euclidean part of
`Solution.lean` (the Riemannian section removed) against the built library; this is not a
Comparator run. The two Riemannian statements (`riemannian_wasserstein_estimate`,
`riemannian_gaussian_splitting`) still have no proof, so `Solution.lean` as generated does
not build and `comparator.json` remains empty. Sequences with varying probability spaces
`Ω n` are handled through the infinite product space (`Paper/SeqData.lean`).

## Riemannian branch (24 October 2026)

`CutoffRigidity.Paper.riemannian_gaussian_splitting` (Theorem 3.6 / Lemma 3.7) is proved with the
exact Challenge type (`CutoffRigidity/Riemann/AssembleMain.lean`), using only `propext`,
`Classical.choice`, `Quot.sound`. Together with the ten Euclidean theorems, every statement of
`Challenge.lean` except `riemannian_wasserstein_estimate` is now proved (checked on a copy of
`Solution.lean` without that theorem; no Comparator run). Reports: `riemann-status/`.

`riemannian_wasserstein_estimate` (Theorem 1.9) was initially unproved, see below.

## Theorem 1.9 without extra hypotheses; final Challenge/Solution status (25 October 2026)

An intermediate version of `riemannian_wasserstein_estimate` carried four extra hypotheses on the
diffusion (`hpos`, invariance, `W₂` contraction, Mehler law). They have been removed: the Challenge
statement is again the original one, with `IsDiffusionSemigroup F V Pt` (Markov kernels, semigroup
law, Kolmogorov's equation on `C_c^∞` test functions) as the only hypothesis on `Pt`, and it is proved
as `CutoffRigidity.Paper.riemannian_wasserstein_estimate` (`Riemann/DiffFinal.lean`). The old amended
proof is kept as `riemannian_wasserstein_estimate_amended`. Reports: `riemann-status/DIFFUSION_PLAN.md`,
`CO_PLAN.md`, `diff-*.md`.

Proof architecture (about 150 files `Riemann/Diff*.lean`):
1. Friedrichs resolvent, `cfc` semigroup with Euler limit on an abstract Hilbert space (`DiffFr*`,
   `DiffFriedrichs`, `DiffCfcSemigroup`); form theory on the manifold, Beurling–Deny, `T_t 1 = 1`,
   chart transfer of the weak equation (`DiffForm*`, `DiffMarkov*`, `DiffChart*`, `DiffInstance*`).
2. Interior elliptic regularity in R^n with variable coefficients and Sobolev embedding (`DiffSobolevRn*`,
   `DiffEllipticRn*`), manifold regularity, smoothing of `T_t`, the canonical kernel `Kk` (Markov, every
   point, `Kk_comp`, Dynkin, eigenfunction identity) (`DiffReg*`, `DiffKer*`, `DiffEig*`, `DiffLap*`).
3. Uniqueness: `Pt = Kk` for every `IsDiffusionSemigroup` (`bridge_final`), by penalized Perron
   subsolutions, resolvent comparison, the mass trick and Laplace uniqueness (`DiffPenal*`,
   `DiffPerron*`, `DiffBridge*`); no Laplacian comparison is used.
4. Pointwise Bakry–Émery bound and log-Sobolev inequality under `CD(ρ,∞)` (`DiffBE*`, `DiffLSI*`);
   attainment of the gap `0 < mFirstEigenDim` (tightness, local Rellich, `DiffGapAttained*`).
5. Kuwada/Hopf–Lax contraction `W₂(Kk t x, μ)² ≤ e^{-2ρt}∫d²(x,y)dμ(y)` and Kantorovich budget
   duality on the manifold (`DiffHopfLax*`, `DiffKuw*`, `DiffKantorovichProper*`); the lower bound
   uses two moments of the eigenmap, not the Mehler law (`DiffLowerMoments`, `DiffMoments`).

All twelve Challenge theorems have proofs of exactly the Challenge type; `Solution.lean` builds with
no `sorry`, and each depends only on `propext`, `Classical.choice`, `Quot.sound`. `comparator.json`
lists 46 theorems and 51 definitions after the cheap block integration (35 and 43 before it; 12 original theorems and 39 definitions at the time of the first Comparator run). `lake comparator` accepted the solution
(`verification/comparator-final.log`: con-ron, nanoda and the Lean kernel all accept, 88114 declarations).
The run was repeated inside the official bwrap sandbox (`verification/comparator-sandboxed.log`,
same result: con-ron, nanoda and the Lean kernel accept). On this machine `/home` is a symlink to
`chome/`, so `lake comparator`'s `bwrap --tmpfs /home` fails; `scripts/bwrap-home-symlink-wrapper.sh`
(placed first in `PATH` as `bwrap`) hides the resolved home tree instead and re-binds read-only the
local mathlib packages that `.lake/packages` points to. Human semantic review and the registry steps
remain to be done.

## Statement audit and non-vacuity witness (25 October 2026)

`verification/semantic-audit.md` is an independent AI audit (not a human review) of the 12 Challenge
statements against the paper: no defect found; remarks on the classical definition of the first
eigenspace, Brownian-motion existence, and the `p < ∞` amendment of display (1.25) are recorded there
and in `Challenge.lean` docstrings. `Riemann/WitnessMain.lean` (`exists_riemannian_instance`) proves
that the hypotheses of the Riemannian theorems hold together for the Gaussian on `ℝ^k`
(`IsWeightedVolume`, `CD ρ`, `mSpectralGap = ρ`, `mFirstEigenDim = k`), so they are not vacuous through a
definition error. No `IsDiffusionSemigroup` instance is constructed for Theorem 1.9 beyond the canonical
kernel `Kk` of `exists_kernel` on any manifold satisfying the standing hypotheses. The sandboxed
Comparator was rerun after these changes with the same result. Human semantic review, registry
steps and attestation of responsible humans remain to be done by people; none is claimed here.

## Hypothesis cleanup (25 October 2026)

`hS` of Theorem 1.7 (`product_condition_cutoff`) was weakened from `∀ n, (S n).Nonempty` to
`∀ n, 0 < n → (S n).Nonempty`. The full build, `scripts/check-palomar.py --ready`, and the sandboxed
`lake comparator` (con-ron 88115 declarations, nanoda, Lean kernel) pass after the change. Human review is still absent.

## Further manuscript claims (25 October 2026)

`Challenge.lean` was extended from 12 to 34 theorems and from 39 to 43 definitions; the new items are
`CutCur.entropyOf`, `IsTestFunction`, `optimalPI`, `optimalLSI`. Each new statement has a proof
`CutoffRigidity.Paper.<name>` of exactly the Challenge type in `CutoffRigidity/Extra/*.lean`, wired in
`Solution.lean`; each depends only on `propext`, `Classical.choice`, `Quot.sound`. The full `lake build`,
`scripts/check-palomar.py --ready` and the axiom check of all 34 theorems pass. The Comparator has NOT been
rerun on the extended pair, and the new statements have had no AI statement audit comparable to
`verification/semantic-audit.md` and no human review. The old Paper-side theorem
`riemannian_gaussian_splitting` was renamed `riemannian_gaussian_splitting_base`; the Paper theorem of the
original name now has the strengthened statement and is proved from
`riemannian_gaussian_splitting_potential` (`Extra/SplitPotential.lean`).

New theorems (manuscript item, module):
- Theorem 3.6, strengthened `riemannian_gaussian_splitting` (replaces the old statement): adds
  `V x = ρ|Φ(x).1|²/2 + V'(Φ x).2 + (k₁/2) log(2π/ρ)` and `ConnectedSpace N`, `CompleteSpace N` (`SplitPotential`).
- Remark 3.4 `wasserstein_cutoff_weak`; Remark 3.5 `information_cutoff_weak` (`WassersteinCutoffWeak`, `InformationCutoffWeak`).
- Display (1.7) `spectral_gap_ge_curvature` and (R2) => (R1) `rigidity_of_gaussian_factor` (`Lichnerowicz`).
- Examples and introduction: `pairwise_interaction`, `ou_first_eigenspace`, `ou_mean_start_cutoff`,
  `ou_lp_infty_fails`, `mixing_time_rigid` (`PairwiseInteraction`, `OUEigen`, `OUMeanStart`, `OUInfty`, `MixingTime`).
- Proof ingredients: `langevin_moment_bounds`, `sup_eigenLambda_ball` (`Moments`); `langevin_w2_contraction`,
  `langevin_entropy_decay`, `pinsker_tvDist`, `talagrand_logSobolev` (`Dynamics`).
- Optimal constants: `optimal_lsi_twice_pi`, `optimal_constants_extremal` (`OptimalConstants`).
- Section 4: `ou_fisher_information` (`OUFisher`), `heat_kernel_score` (`HeatKernelScore`), `normalization_cutoff`
  (`Normalization`), `temperature_bakry_emery`, `temperature_cd` (`Temperature`).

Amendments and flags (all recorded in the docstrings in `Challenge.lean`):
- `0 < d` is assumed in `spectral_gap_ge_curvature`, `ou_first_eigenspace`, `optimal_constants_extremal`,
  `langevin_entropy_decay`, `talagrand_logSobolev`: for `d = 0` the Rayleigh set is empty and `spectralGap = sInf ∅ = 0`.
- `optimal_lsi_twice_pi`, `optimal_constants_extremal` and `talagrand_logSobolev` have NO Brownian carrier hypothesis
  (removed on 25 October 2026; Brownian-free proofs via the Riemannian machinery on `ℝ^d` plus mollification of `C²` potentials,
  `Extra/NoBm*.lean`). `langevin_entropy_decay` and `langevin_w2_contraction` keep `IsLangevin V B P X`: their conclusions are
  statements about the law of the process `X`, so it is part of the claim.
- `temperature_cd` takes the smoothness of Mathlib's standard Riemannian metric on `ℝ^d` as an instance argument
  (a Prop), because the global instance proving it lives in `Riemann/WitnessGeometry`, outside the Challenge.
- `langevin_entropy_decay` states the printed (non-sharp) constants of the regularization inequality.
- `ou_lp_infty_fails`: the `L^∞` distance from a single point can be finite; the manuscript claim is true for the balls
  `B(m, c√n)`, `c > 0`, which is how it is stated. `ou_mean_start_cutoff` adds the non-cutoff at `log n/(2λ₁)`
  and treats only the Wasserstein distance. `mixing_time_rigid` treats only the total variation mixing time.
- Test class of `optimalPI`, `optimalLSI`: smooth, bounded, Lipschitz functions; the manuscript does not fix one.
- `normalization_cutoff` concerns the time-changed laws `X_{αt}` only.

Not formalized (updated after the cheap block integration below): Question 1.10 (open problem); eq. (loggradbound) and its consequences
(conjectural); the derivative identity `dH/dt = -I` for general laws; Theorem 1.7 on manifolds; the sphere, Dyson and KLS discussions; Gaussian
isoperimetry; (existence of Brownian motion is now formalized, see "Vendored Brownian motion library"); the Leibniz identity for the carré du champ; the vector form of the Bochner identity; the Rothaus
alternative (literature); `m` as the centre of mass for coordinates `i ≥ k₁`. (Formerly listed here and now covered: the SDE-level
Brownian scaling, eq. (expdecI) for general laws and its Dini form, W2 and entropy mixing times, the Riemannian Bochner/CD equivalence.)

`scripts/gen-solution.py` now passes `(Ω := Ω)` to `apply` for the three theorems where `Ω` occurs only in
hypotheses (`EXPLICIT` table in the script).

## Extended Challenge (25 October 2026)

Challenge.lean now has 34 theorems and 43 definitions: the original 12 plus 22 further manuscript claims
(see `extra-status/integration.md`). The sandboxed `lake comparator` accepted the extended pair
(con-ron 88377 declarations, nanoda, Lean kernel; `verification/comparator-sandboxed.log`), the full build passes,
and all 34 theorems use only `propext`, `Classical.choice`, `Quot.sound`. The added statements are unaudited by humans
and by the earlier AI audit. Human review is still absent.

## AI audit of the added statements (25 October 2026)

Four independent AI auditors reviewed the 22 added statements and the strengthened splitting
(`verification/audit-extra-{A,B,C,D}.md`, summarized in `verification/semantic-audit.md`): no defect found; one statement
strengthened (`heat_kernel_score` asserts differentiability), two docstrings corrected. Build, readiness check and sandboxed
Comparator were rerun and pass. This is not a human review; `review.status` remains `unchecked`.

## Riemannian Lichnerowicz (25 October 2026)

`mSpectralGap_ge_of_CD` (`CD ρ` with `ρ > 0` implies `ρ ≤ mSpectralGap`, amended by `0 < finrank ℝ F`) was added as the
35th Challenge theorem (`CutoffRigidity/Extra/RiemannLichnerowicz.lean`). It does not use the old `hgap` hypothesis:
ergodicity of the canonical kernel is derived from the Bakry–Émery gradient bound. Build, readiness check, axiom check and the sandboxed
Comparator (35 theorems, 43 definitions) pass. The statement has had no audit beyond the author agent's own report
(`extra-status/rlich.md`); no human review.

`lsi_of_CD` (`Riemann/DiffLSI.lean`) no longer takes the spectral-gap hypothesis: its Poincaré step now uses `poincare_of_CD`
(`Extra/RiemannLichnerowicz.lean`; `DiffLSI` imports it). Gap attainment in `DiffFinal.lean` still uses `hgap`, as in Theorem 1.9.
Build, readiness check, axiom check of all 35 theorems and the sandboxed Comparator pass again.

`mSpectralGap_ge_of_CD` was audited by one independent AI agent (`verification/audit-extra-E.md`): no defect found. Not a human review.

## Brownian carrier hypotheses removed (25 October 2026)

`optimal_lsi_twice_pi`, `optimal_constants_extremal` and `talagrand_logSobolev` no longer assume a Brownian motion
(`hB : IsStdBrownian B P` / `hL : IsLangevin V B P X`), and have the full `C²` hypothesis on `V`. The proofs go through the Riemannian
`lsi_of_CD` on `ℝ^d` (no gap hypothesis, no Brownian motion) and a mollification of `C²` potentials (`CutoffRigidity/Extra/NoBm*.lean`).
The older carrier versions are kept as `*_carrier` in `Extra/OptimalConstants.lean` and `Extra/Dynamics.lean`. These three statements changed
after the AI audits of group B and D, and have not been re-audited. Build, readiness check, axiom check and the sandboxed Comparator were rerun.

The three Brownian-free statements were re-audited by one independent AI agent (`verification/audit-extra-F.md`): no defect. Not a human review.

Second independent AI audits (`verification/audit-extra-G.md`, `audit-second-1.md`, `audit-second-2.md`) covered the statements edited after
their first audit and the original theorems 1-7 and 9-12: no defect; one docstring corrected (`IsDiffusionSemigroup`). Not a human review.

## Cheap block integration (25 October 2026)

Eleven further statements were added to `Challenge.lean` (35 to 46 theorems, 43 to 51 definitions); each has a proof
`CutoffRigidity.Paper.<name>` of exactly the Challenge type, wired in `Solution.lean`, depending only on `propext`,
`Classical.choice`, `Quot.sound`. The full `lake build`, `lake build Challenge Solution` and `scripts/check-palomar.py --ready` pass.
The Comparator has NOT been rerun, and the new statements have had no AI statement audit and no human review
(`review.status` stays `unchecked`). Reports: `extra-status/cb1.md` to `cb4.md`, `extra-status/integration2.md`.

New definitions (all in `Challenge.lean`, namespace `CutCur`): `mixingTimeW2`, `mixingTimeKL`, `IsSDESolution`, `mCurv`, `mExt`, `mRic`,
`mHess`, `mHessSq`. `entropyOf` is now stated on an arbitrary measurable space (same body; on `Rd d` it is the former definition, so
`optimalLSI` and the earlier statements keep their meaning).

New theorems (manuscript item, module):
- `bochner_identity`, `CD_iff_ricci` (Section 1.4, lines 641-663; `RicciBochner`). The Ricci tensor is choice-free
  (`Ric(v,w) = ∑ᵢ ⟨R(eᵢ,v)w, eᵢ⟩`, `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z`, extensions by constant coordinates in the canonical
  trivialization). Scalar form only.
- `riemannian_k1_bounds` (`RiemannK1`): `1 ≤ k₁ ≤ dim M`; flag: needs `hgap : λ₁ = ρ` (false claim without it on spheres).
- `riemannian_poincare_lsi` (`RiemannPoincareLSI`): Poincaré and log-Sobolev (constant `2/ρ`) under `CD(ρ,∞)`, `ρ > 0`, for smooth compactly
  supported `f`, no gap hypothesis.
- `langevin_fisher_decay`, `langevin_fisher_dini` (`FisherDecayGeneral`): eq. (expdecI) for every initial law (`I = +∞` allowed) and the upper
  Dini form; flag: the Dini form is on `toReal` at times with `I(μ_t) ≠ ⊤`, no derivative is claimed.
- `normalization_sde` (`BrownianScaling`): Brownian scaling and the scaled SDE (`IsSDESolution`); solutions are given by hypothesis (`IsLangevin`).
- `temperature_sde`, `temperature_cutoff` (`TemperatureSDE`). Flags: `temperature_sde` adds `C²` and `Hess V ≥ ρ > 0` (convexity is not in the
  manuscript; needed by the library's Langevin kernel); `temperature_cutoff` takes `ρₙ = σ² λ₁(Vₙ/σ²)` as a hypothesis (`hgap`) as the reading
  of "rigid case"; Brownian motions and solutions are given by hypothesis.
- `mixing_time_w2_rigid`, `mixing_time_kl_rigid` (`MixingTimeW2KL`): W2 and entropy mixing times, every `η > 0`; flag: in the W2 statement the
  last conjunct is an implication (`t₀ → ∞` only under `λ₁ = o(log n)`; it fails otherwise).
- The docstring of `normalization_cutoff` now points to `normalization_sde`.

Procedure: definitions moved from the `Extra` modules to `Challenge.lean` (so `Statements.lean` provides them to the Extra files, which now
import `CutoffRigidity.Statements`); `mEntropy` was dropped in favour of the general `entropyOf`; `scripts/sync-statements.py` and
`scripts/gen-solution.py` were rerun unchanged; seven `Extra` modules were appended to `CutoffRigidity.lean`; `comparator.json` regenerated.

## Final suite after the cheap block (25 October 2026)

Challenge.lean: 46 theorems, 51 definitions (998 lines, 68 KB; limits 1000 lines / 100 KiB). Full `lake build` (9683 jobs), `check-palomar.py --ready` (767 Lean files),
axiom check (all 46 theorems use only `propext`, `Classical.choice`, `Quot.sound`, none uses `sorryAx`) and the sandboxed Comparator (con-ron, nanoda, Lean kernel) all pass.
The 11 added statements were audited by two independent AI agents (`verification/audit-extra-H.md`, `audit-extra-I.md`): no defect. Not a human review.

## Vendored Brownian motion library (25 October 2026)

`Challenge.lean` now states 48 theorems (51 definitions unchanged): `exists_stdBrownian` and `exists_langevin`, proved in `Solution.lean` by
`CutoffRigidity.Paper.exists_stdBrownian` and `CutoffRigidity.Paper.exists_langevin` (`CutoffRigidity/Paper/ExistsBrownian.lean`), with only
`propext`, `Classical.choice`, `Quot.sound`. The Challenge closure is still Lean core + Mathlib: the statements use only Challenge definitions.

Vendoring (see `vendor/README.md`, `scope-status/bmx.md`, `extra-status/integration3.md`). The proof of `exists_stdBrownian` uses `isBrownianReal_brownian`
from the Brownian motion library of Degenne, Ledvinka, Marion and Pfaffelhuber (arXiv:2511.20118), whose upstream needs a newer Mathlib than
this project. Rather than bump Mathlib (17+ broken modules) or fork, the 29 needed modules (26 of `BrownianMotion`, 3 of `KolmogorovExtension4`)
are copied under `vendor/`, plus one added module. Origins: brownian-motion `546d77295fdf8ae7f44cec14ec5df7959c4e3617`, kolmogorov_extension4
`c20f168ed693537c78111ffeabc2ab5f384e35d6`. Patches: `IsKolmogorovProcess.lean` (three added `have hqd_nonneg` lines), `KolmogorovChentsov.lean`
(one `.aemeasurable` dropped), `KolmogorovExtension4/CompactSystem.lean` (one added import), new `Compat/CompactSystemExtra.lean` (backport of Mathlib
PRs 36089, 36225, 36160; delete when Mathlib is bumped). Each patched file carries a `-- MODIFIED` comment. They are declared as `[[lean_lib]]`
entries with `srcDir` and `globs` in `lakefile.toml` (`roots` would not build sibling modules); `lake-manifest.json`, the packages directory and the
sandbox wrapper are unchanged. Every vendored file uses `module` and is below 10000 lines; no `sorry`, `axiom`, `native_decide`;
`scripts/check-palomar.py` needed no change. Licences: upstream Apache-2.0 texts live in `vendor/*/LICENSE` (the root keeps exactly one licence file).
Only `CutoffRigidity/Paper/ExistsBrownian.lean` imports the vendored library, with a private `import`, so vendored root-namespace lemmas are
invisible to the rest of the project; the full build shows no declaration clash.

Comparator: NOT rerun after this integration (the earlier spike accepted a mini pair with the same libraries in the sandbox, with all three
kernels; the full pair must be rerun; con-ron will count the vendored declarations too). The new statements have had no AI audit and no human review
(`review.status` stays `unchecked`).
