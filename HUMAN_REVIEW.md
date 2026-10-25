# Human review checklist (draft)

Status (updated 25 October 2026): **no human review has taken place.** This file is a checklist for the people who will do it. It records nothing
as reviewed, and the sign-off block at the end is intentionally blank. Everything below that is marked "AI" was done by
language-model agents and is not a substitute for a person.

What Lean already guarantees (machine-checked, rerunnable, see README "How to rebuild and verify"): the 35 theorems of
`Challenge.lean` are proved by `Solution.lean` with the same statements, using only `propext`, `Classical.choice`,
`Quot.sound`; the Comparator (Lean kernel, nanoda, con-ron) accepts. What it does NOT guarantee: that the *statements and
definitions* mean what the manuscript says. That is what a reviewer must establish.

## AI audits done so far (to reuse, not to trust)
Every one of the 35 statements has had at least one AI audit (statements and definitions read against the manuscript; proofs not read):
- original 12: `verification/semantic-audit.md` (first audit) and independent second audits `audit-second-1.md` (theorems 1-7),
  `audit-second-2.md` (theorems 9-12 and the Riemannian definitions);
- 22 added statements: `audit-extra-A.md` (sequence cutoffs), `-B.md` (spectral gap, constants), `-C.md` (OU, time change, temperature),
  `-D.md` (dynamics, strengthened splitting);
  `-H.md` (Ricci/Bochner/CD, `k₁` bounds, Riemannian Poincaré/LSI, `entropyOf`), `-I.md` (Fisher decay/Dini, `normalization_sde`, temperature, W₂/entropy mixing times);
- later changes: `-E.md` (`mSpectralGap_ge_of_CD`), `-F.md` (the three statements without Brownian carrier), `-G.md` (Thm 1.7 `hS`
  weakening, `heat_kernel_score`).
No audit found a defect; remarks and agreements are in those files. Limits: each statement was read by one or two agents, mostly by hand (few
Lean scratch checks), the agents share blind spots with the author's tooling, and none of this replaces a person. Reviewers may skim the
reports to see what was already examined, but should form their own verdict first (the second audits did so, which is why they are useful).

## 0. Setup (15 min)
- [ ] Clone `https://github.com/djalilchafai/cutoff-rigidity-diffusions`, record the commit hash reviewed.
- [ ] Run steps 1-4 of README "How to rebuild and verify"; note any failure.
- [ ] Confirm that `Solution.lean` imports `CutoffRigidity.Statements` (generated verbatim from `Challenge.lean`'s
      definitions; `python3 scripts/sync-statements.py --check`) and contains no definitions of its own.
- [ ] Confirm that `comparator.json` lists exactly the 46 theorems and 51 definitions of `Challenge.lean`.

## 1. Definitions (highest priority: an error here silently changes every theorem)
Read `Challenge.lean` lines 1-150 (Euclidean) and the Riemannian section (from `mgrad`, about line 712).
- [ ] `gibbs V` is `e^{-V} dx` as a measure (not normalized); `IsProbabilityMeasure (gibbs V)` is assumed where needed.
- [ ] `spectralGap V`: Rayleigh infimum over which test functions, which junk value (`sInf ∅ = 0`), compare with
      "λ₁ = optimal Poincaré constant⁻¹" in the paper.
- [ ] `IsEigenfunction`, `firstEigenspace`, `firstEigenDim` (finrank, smooth vs L² eigenfunctions), `eigenLambda` (Λ(x₀)),
      `IsEigenbasis`. Compare with Remark 1.2 and Definition 1.8.
- [ ] `RigidCurvature` (Hess V ≥ λ₁ I with λ₁ > 0).
- [ ] `IsStdBrownian`, `IsLangevinSolution`, `IsLangevin`: do they describe the SDE `dX = -∇V dt + √2 dB`?
      Check that the Brownian motion is a hypothesis, not constructed (Lean/Mathlib cannot construct one at this revision).
- [ ] `wasserstein2` (couplings; value in `[0,∞]`), `tvDist` (sup over sets), `fisherInfo` (convention and junk values),
      `relLp` (L^p norm of density ratio minus 1; p = ⊤ is an essential sup), `klDiv` (Mathlib's).
- [ ] `worst`, `HasCutoff`, `meanBall`, `meanCube`, `criticalTime`, `mixingTime`, `mixingTimeW2`, `mixingTimeKL` (`⨅ ∅ = ⊤`), `IsRigidSequence`, `IsSDESolution`.
- [ ] Riemannian: `mgrad`, `mlaplacian`, `carre` (Γ), `carre2` (Γ₂), `CD` (Γ₂ ≥ ρΓ), `chartVolumeDensity`,
      `IsWeightedVolume` (μ = e^{-V} vol_g, no stray constant), `mSpectralGap`, `IsMEigenfunction`, `mFirstEigenDim`, `mLambda`;
      `mCurv`, `mExt`, `mRic` (sign and extension conventions), `mHess`, `mHessSq`.
- [ ] `IsDiffusionSemigroup`: Markov kernels, semigroup law, Dynkin identity on `C_c^∞`; the file's docstring says exactly one (`isDiffusionSemigroup_Kk` and uniqueness `bridge_final`; neither `CD` nor `ρ > 0` is needed for uniqueness)
      such semigroup exists under the standing hypotheses (proved, `isDiffusionSemigroup_Kk`). Is that a faithful encoding of
      "the diffusion" of Theorem 1.9?
- [ ] Optimal constants: `entropyOf`, `IsTestFunction` (smooth bounded Lipschitz), `optimalPI`, `optimalLSI` and the factor-2
      convention (`Var f ≤ C∫|∇f|²`, `Ent(f²) ≤ C∫|∇f|²`).

## 2. The 46 statements against the manuscript
For each: read the statement and its docstring, find the manuscript item, tick when statement = claim. "Flag" = known
deviation to judge. AI audits: see the list above.

| # | Theorem (`CutCur.`) | Manuscript item | Flag to judge |
|---|---|---|---|
| 1 | `main_wasserstein_estimate` | Thm 1.1 | |
| 2 | `eigenspace_dim_and_lambda` | Remark 1.2 | |
| 3 | `wasserstein_cutoff` | Cor 1.3 | |
| 4 | `information_cutoff` | Cor 1.4 | |
| 5 | `lp_cutoff` | (1.25) | finite p only (p = ∞ false for OU) |
| 6 | `convex_interaction` | Thm 1.5 | W ∈ C² assumed |
| 7 | `convex_interaction_cutoff` | Cor 1.6 | |
| 8 | `product_condition_cutoff` | Thm 1.7 | amended: `liminf κ > 0`, `t₀ → ∞` for Fisher/W₂ (printed statement is false); `hS` only for `n > 0` |
| 9 | `euclidean_gaussian_factorization` | Thm 3.1, Rem 3.2 | |
| 10 | `eigenmap_is_ou` | Lemma 3.3 | SDE form of the OU generator |
| 11 | `wasserstein_cutoff_weak` | Rem 3.4 | reading of "slow growth" as `(λ₁)⁻¹ ≤ (log n)^α` |
| 12 | `information_cutoff_weak` | Rem 3.5 | reading of `d^{o(1)}` |
| 13 | `spectral_gap_ge_curvature` | (1.7), L519-548 | `0 < d` |
| 14 | `rigidity_of_gaussian_factor` | (R2)⇒(R1) | Gaussian factor stated on the potential; no "all eigenfunctions affine" part |
| 15 | `optimal_lsi_twice_pi` | "Optimal constants" | test class |
| 16 | `optimal_constants_extremal` | "Optimal constants" | `0 < d`; equality with constants optimal on the bounded class |
| 17 | `ou_fisher_information` | Sect. 4.1 | |
| 18 | `normalization_cutoff` | Sect. 4 Normalization | `κ → ακ` is arithmetic; the SDE claim is `normalization_sde` (no. 42) |
| 19 | `temperature_bakry_emery` | Sect. 4 Temperature | invariance only in the weak form `∫L f dμ = 0`; the process level is `temperature_sde` (no. 43) |
| 20 | `heat_kernel_score` | Sect. 4.1 | |
| 21 | `pairwise_interaction` | after (1.5) | evenness of `h` not needed |
| 22 | `ou_first_eigenspace` | after (1.4) | `0 < d` |
| 23 | `mixing_time_rigid` | after Cor 1.6 | TV mixing time only (W2 and entropy: nos. 45, 46) |
| 24 | `ou_mean_start_cutoff` | after Cor 1.3 | extra conjunct "no cutoff at `criticalTime`" |
| 25 | `ou_lp_infty_fails` | after (1.25) | stronger form (tends to ⊤ along every time sequence) on balls with `c > 0` |
| 26 | `langevin_moment_bounds` | proofs of 1.1, 1.3, 1.4 | |
| 27 | `sup_eigenLambda_ball` | proof of 1.1 | |
| 28 | `langevin_w2_contraction` | proof of 1.1 | `ρ ≥ 0` |
| 29 | `langevin_entropy_decay` | proof of Cor 1.4 | `0 < d`; `IsLangevin` for the process `X`; printed (non-sharp) constants |
| 30 | `pinsker_tvDist` | (CKP) | |
| 31 | `talagrand_logSobolev` | (Talagrand, LSI) | `0 < d` |
| 32 | `temperature_cd` | Sect. 4 Temperature | redundant instance argument for the metric on `Rd d` |
| 33 | `mSpectralGap_ge_of_CD` | L619-663 | `0 < finrank ℝ F` |
| 34 | `riemannian_wasserstein_estimate` | Thm 1.9 | semigroup encoded by `IsDiffusionSemigroup`; SDE replaced; not verified that the canonical kernel `Kk` is the law of the SDE (1.26) |
| 35 | `riemannian_gaussian_splitting` | Thm 3.6, Lemma 3.7 | potential identity and connected/complete `N` added |
| 36 | `bochner_identity` | Sect. 1.4, L641-654 | Ricci tensor defined from Mathlib's connection (sign convention: positive on spheres); scalar form only |
| 37 | `CD_iff_ricci` | Sect. 1.4, L655-663 | same `mRic`; `mHess`, `mHessSq` conventions |
| 38 | `riemannian_k1_bounds` | Sect. 1.4, L633-636 | needs `hgap : λ₁ = ρ` (false claim without it on spheres) |
| 39 | `riemannian_poincare_lsi` | Sect. 1.4, L618-632 | `entropyOf` now on any measurable space; compactly supported smooth `f`; constant `2/ρ` |
| 40 | `langevin_fisher_decay` | eq. expdecI | `X` given by `IsLangevin`; `I(ν) = ⊤` allowed |
| 41 | `langevin_fisher_dini` | before eq. expdecI | Dini form on `toReal` at times with `I(μ_t) ≠ ⊤`; no derivative claimed |
| 42 | `normalization_sde` | Sect. 4.2 | solutions by hypothesis; `IsSDESolution` (a.s. continuous paths and integral equation) |
| 43 | `temperature_sde` | Sect. 4.4 | adds `C²`, `Hess V ≥ ρ > 0` (not in manuscript); `e^{-V/σ²}` normalizable; solutions by hypothesis |
| 44 | `temperature_cutoff` | Sect. 4.4 | hypothesis `ρₙ = σ² λ₁(Vₙ/σ²)`; `liminf ρₙ > 0`; information cutoffs under `ρ = o(log n)` |
| 45 | `mixing_time_w2_rigid` | summary after Cor 1.6 | last conjunct an implication (`t₀ → ∞` only if `λ₁ = o(log n)`); any `η > 0` |
| 46 | `mixing_time_kl_rigid` | summary after Cor 1.6 | needs `λ₁ = o(log n)`; any `η > 0` |

## 3. Cross-cutting questions
- [ ] **Vacuity.** Only the Riemannian hypotheses have a Lean witness in the repository (`Riemann/WitnessMain.lean`, Gaussian on ℝᵏ, flat
      only). The second audit of Thm 1.9 reports having proved in scratch files (not committed) that the witness also admits the semigroup `Pt`
      via `isDiffusionSemigroup_Kk`; consider committing that check. For the Langevin-based statements, joint satisfiability rests on classical existence of Brownian motion and strong solutions, which
      Lean cannot instantiate. Decide whether that is acceptable, and whether a curved Riemannian witness is wanted.
- [ ] **Each amendment** (`0 < d`, `0 < finrank`, Thm 1.7, `hS`) necessary and harmless?
- [ ] **Manuscript vs printed paper.** The local `cutcur-lean.tex` differs from arXiv:2412.15969v4 (Thm 1.7 hypotheses, completeness and
      connectedness in the Riemannian setting, finite `p`, Thm 3.6). Judge whether the corrections are mathematically right
      (`PAPER_AUDIT.md`: the Ornstein–Uhlenbeck counterexample to Thm 1.7 is a written derivation, not checked in Lean) and agree with the authors' intent.
- [ ] **Global instance.** `Riemann/WitnessGeometry.lean` adds `instIsContMDiffRiemannianBundleRd`; confirm it cannot change the meaning of
      any Challenge statement (Comparator accepts; `temperature_cd` is the only statement touching it).
- [ ] **Not formalized** (honestly listed in `PALOMAR.md`): Question 1.10 (open); `eq:loggradbound` (conjecture); `dH/dt = -I` for general laws;
      Theorem 1.7 on manifolds; sphere, Dyson, Gaussian isoperimetry; existence of Brownian motion; Leibniz identity for the carré du champ;
      vector-form Bochner; the Rothaus remark. Decide whether any is required for the intended submission.
- [ ] **Cosmetic/lint:** deprecation warnings (`if_pos`, `if_neg`, `haveI`, `Set.mem_setOf_eq`) are harmless.

## 4. Process items (outside Lean)
- [ ] Fill `formalization.yaml` review fields only after a real review (`review.status`, reviewers); do not edit them before.
- [ ] Verify the `formalization.yaml` alignment entries (`lean: CutCur.<name>`) against the official schema; the format was not validated.
- [ ] Authors/responsible humans decide on registry submission and sign the attestation. Nothing was submitted or attested by the AI agents.
- [ ] Decide on the license/attribution statement for the archived paper (CC BY 4.0, `paper/SOURCE.txt`) and the project's Apache-2.0.

## Sign-off (to be completed by humans; left blank on purpose)
Reviewer(s): ____________  Date: ____________  Commit reviewed: ____________
Scope reviewed (definitions / statements 1-46 / other): ____________
Findings and decision: ____________
