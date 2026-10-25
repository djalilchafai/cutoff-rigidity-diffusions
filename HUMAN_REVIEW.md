# Human review checklist (draft)

Status (updated 25 October 2026, after the Brownian-free integration): **no human review has taken place.** The 21 statements converted to kernel form were re-audited by two AI agents after the conversion (`audit-extra-K.md`, `audit-extra-L.md`; earlier audits of the same statements concerned the Brownian-carrier text). This file is a checklist for the people who will do it. It records nothing
as reviewed, and the sign-off block at the end is intentionally blank. Everything below that is marked "AI" was done by
language-model agents and is not a substitute for a person.

What Lean already guarantees (machine-checked, rerunnable, see README "How to rebuild and verify"): the 48 theorems of
`Challenge.lean` are proved by `Solution.lean` with the same statements, using only `propext`, `Classical.choice`,
`Quot.sound`; the Comparator (Lean kernel, nanoda, con-ron) accepts. What it does NOT guarantee: that the *statements and
definitions* mean what the manuscript says. That is what a reviewer must establish.

## AI audits done so far (to reuse, not to trust)
Every one of the 48 statements has had at least one AI audit (statements and definitions read against the manuscript; proofs not read):
- original 12: `verification/semantic-audit.md` (first audit) and independent second audits `audit-second-1.md` (theorems 1-7),
  `audit-second-2.md` (theorems 9-12 and the Riemannian definitions);
- 22 added statements: `audit-extra-A.md` (sequence cutoffs), `-B.md` (spectral gap, constants), `-C.md` (OU, time change, temperature),
  `-D.md` (dynamics, strengthened splitting);
  `-H.md` (Ricci/Bochner/CD, `k₁` bounds, Riemannian Poincaré/LSI, `entropyOf`), `-I.md` (Fisher decay/Dini, `normalization_sde`, temperature, W₂/entropy mixing times), `-J.md` (`exists_stdBrownian`, `exists_langevin`), `-K.md` (kernel definitions `IsEuclideanDiffusion`/`IsEuclideanLangevin`/`IsSigma*`/`worstK`/`mixingTime*K`/`IsRigidSequenceK`, and the kernel versions of Thm 1.1, Cor 1.3, 1.4, 1.6, (1.25), Thm 1.7, Remarks 3.4/3.5; C^∞ trade-off), `-L.md` (`eigenmap_is_ou` law form, mixing times, OU statements, Langevin decay statements, `normalization_cutoff`, `temperature_cutoff`);
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
- [ ] Confirm that `comparator.json` lists exactly the 48 theorems and the definitions of `Challenge.lean` (55 after the Brownian-free integrations: 9 added, 5 removed (`worst`, `IsRigidSequence` too); the old `mixingTime*` live in `Paper/CarrierDefs.lean`).

## 1. Definitions (highest priority: an error here silently changes every theorem)
Read `Challenge.lean` lines 1-150 (Euclidean) and the Riemannian section (from `mgrad`, about line 712).
- [ ] `gibbs V` is `e^{-V} dx` as a measure (not normalized); `IsProbabilityMeasure (gibbs V)` is assumed where needed.
- [ ] `spectralGap V`: Rayleigh infimum over which test functions, which junk value (`sInf ∅ = 0`), compare with
      "λ₁ = optimal Poincaré constant⁻¹" in the paper.
- [ ] `IsEigenfunction`, `firstEigenspace`, `firstEigenDim` (finrank, smooth vs L² eigenfunctions), `eigenLambda` (Λ(x₀)),
      `IsEigenbasis`. Compare with Remark 1.2 and Definition 1.8.
- [ ] `RigidCurvature` (Hess V ≥ λ₁ I with λ₁ > 0).
- [ ] `IsStdBrownian`, `IsLangevinSolution`, `IsLangevin`: do they describe the SDE `dX = -∇V dt + √2 dB`?
      Remaining users: nos. 42, 43, 47, 48 only (all other Euclidean process statements are now Brownian-free; `IsRigidSequence` and `worst` are no longer Challenge definitions). The Brownian motion is a hypothesis in those theorems; its existence is the separate theorems nos. 47-48 (vendored library, see section 5).
- [ ] Confirm that Mathlib's `IsBrownianReal` (a.s. continuous paths and the Gaussian finite-dimensional laws of `IsPreBrownianReal`) is the intended
      definition of real Brownian motion, and that `IsStdBrownian` (independent real coordinates) is a standard Brownian motion on `ℝ^d`.
- [ ] `wasserstein2` (couplings; value in `[0,∞]`), `tvDist` (sup over sets), `fisherInfo` (convention and junk values),
      `relLp` (L^p norm of density ratio minus 1; p = ⊤ is an essential sup), `klDiv` (Mathlib's).
- [ ] `worst`, `HasCutoff`, `meanBall`, `meanCube`, `criticalTime`, `IsSDESolution` (`worst`, `IsRigidSequence` moved to `Paper/CarrierDefs.lean`; the Challenge uses `worstK`, `IsRigidSequenceK`).
- [ ] **Brownian-free kernel definitions (new, 21 statements depend on them):** `IsEuclideanDiffusion` (Markov kernels, semigroup law `Pt (s+t) = Pt t ∘ₖ Pt s`,
      Dynkin/Kolmogorov identity on `C_c^∞` with the generator `Δ - ∇V·∇`), `IsEuclideanLangevin` (adds `V ∈ C^∞` and `IsProbabilityMeasure (gibbs V)`),
      `IsSigmaDiffusion` / `IsSigmaLangevin` (generator `σ²Δ - ∇V·∇`, `V ∈ C^∞`, `e^{-V/σ²}` a probability density), `worstK`, `mixingTimeK`, `mixingTimeW2K`,
      `mixingTimeKLK` (`⨅ ∅ = ⊤`), `IsRigidSequenceK`. Confirm in particular that **`IsEuclideanDiffusion` is a faithful encoding of the law of the solution of the SDE (1.1)**
      (`Pt t x = Law(X_t^x)`): uniqueness of such `Pt` for smooth `V` with probability Gibbs measure is *proved* (`isEuclideanDiffusion_unique`, via the Riemannian
      `bridge_final`), and the Brownian `langevinKernel` is shown to satisfy it, but the identification with the SDE solution is not a Challenge statement.
- [ ] Riemannian: `mgrad`, `mlaplacian`, `carre` (Γ), `carre2` (Γ₂), `CD` (Γ₂ ≥ ρΓ), `chartVolumeDensity`,
      `IsWeightedVolume` (μ = e^{-V} vol_g, no stray constant), `mSpectralGap`, `IsMEigenfunction`, `mFirstEigenDim`, `mLambda`;
      `mCurv`, `mExt`, `mRic` (sign and extension conventions), `mHess`, `mHessSq`.
- [ ] `IsDiffusionSemigroup`: Markov kernels, semigroup law, Dynkin identity on `C_c^∞`; the file's docstring says exactly one (`isDiffusionSemigroup_Kk` and uniqueness `bridge_final`; neither `CD` nor `ρ > 0` is needed for uniqueness)
      such semigroup exists under the standing hypotheses (proved, `isDiffusionSemigroup_Kk`). Is that a faithful encoding of
      "the diffusion" of Theorem 1.9?
- [ ] Optimal constants: `entropyOf`, `IsTestFunction` (smooth bounded Lipschitz), `optimalPI`, `optimalLSI` and the factor-2
      convention (`Var f ≤ C∫|∇f|²`, `Ent(f²) ≤ C∫|∇f|²`).

## 2. The 48 statements against the manuscript
For each: read the statement and its docstring, find the manuscript item, tick when statement = claim. "Flag" = known
deviation to judge. AI audits: see the list above.

| # | Theorem (`CutCur.`) | Manuscript item | Flag to judge |
|---|---|---|---|
| 1 | `main_wasserstein_estimate` | Thm 1.1 | kernel form (`IsEuclideanLangevin`); `V ∈ C^∞` |
| 2 | `eigenspace_dim_and_lambda` | Remark 1.2 | |
| 3 | `wasserstein_cutoff` | Cor 1.3 | kernel form (`IsRigidSequenceK`, `worstK`); `V n ∈ C^∞` |
| 4 | `information_cutoff` | Cor 1.4 | kernel form; `V n ∈ C^∞` |
| 5 | `lp_cutoff` | (1.25) | finite p only (p = ∞ false for OU); kernel form; `V n ∈ C^∞` |
| 6 | `convex_interaction` | Thm 1.5 | W ∈ C² assumed |
| 7 | `convex_interaction_cutoff` | Cor 1.6 | kernel form; `W n ∈ C^∞` (was `C²`) and smooth potential |
| 8 | `product_condition_cutoff` | Thm 1.7 | amended: `liminf κ > 0`, `t₀ → ∞` for Fisher/W₂ (printed statement is false); `hS` only for `n > 0`; kernel form (`mixingTimeK`, `worstK`); `V n ∈ C^∞` |
| 9 | `euclidean_gaussian_factorization` | Thm 3.1, Rem 3.2 | |
| 10 | `eigenmap_is_ou` | Lemma 3.3 | **law form** `(Pt t x₀).map Tv = 𝒩(…)` instead of the pathwise Brownian `β`; `V ∈ C^∞` |
| 11 | `wasserstein_cutoff_weak` | Rem 3.4 | reading of "slow growth" as `(λ₁)⁻¹ ≤ (log n)^α`; **kernel form** (`IsEuclideanLangevin`, `worstK`), `V ∈ C^∞` |
| 12 | `information_cutoff_weak` | Rem 3.5 | reading of `d^{o(1)}`; **kernel form** (`IsRigidSequenceK`, `worstK`), `V ∈ C^∞` |
| 13 | `spectral_gap_ge_curvature` | (1.7), L519-548 | `0 < d` |
| 14 | `rigidity_of_gaussian_factor` | (R2)⇒(R1) | Gaussian factor stated on the potential; no "all eigenfunctions affine" part |
| 15 | `optimal_lsi_twice_pi` | "Optimal constants" | test class |
| 16 | `optimal_constants_extremal` | "Optimal constants" | `0 < d`; equality with constants optimal on the bounded class |
| 17 | `ou_fisher_information` | Sect. 4.1 | kernel form (`Pt t x₀` replaces `Law(X_t)`); `V` automatically `C^∞` |
| 18 | `normalization_cutoff` | Sect. 4 Normalization | `κ → ακ` is arithmetic; the SDE claim is `normalization_sde` (no. 42); kernel form, generic in `Pt n` (no Brownian motion) |
| 19 | `temperature_bakry_emery` | Sect. 4 Temperature | invariance only in the weak form `∫L f dμ = 0`; the process level is `temperature_sde` (no. 43) |
| 20 | `heat_kernel_score` | Sect. 4.1 | |
| 21 | `pairwise_interaction` | after (1.5) | evenness of `h` not needed |
| 22 | `ou_first_eigenspace` | after (1.4) | `0 < d` |
| 23 | `mixing_time_rigid` | after Cor 1.6 | TV mixing time only (W2 and entropy: nos. 45, 46); kernel form (`mixingTimeK`); `V n ∈ C^∞` |
| 24 | `ou_mean_start_cutoff` | after Cor 1.3 | extra conjunct "no cutoff at `criticalTime`"; kernel form |
| 25 | `ou_lp_infty_fails` | after (1.25) | stronger form (tends to ⊤ along every time sequence) on balls with `c > 0`; kernel form |
| 26 | `langevin_moment_bounds` | proofs of 1.1, 1.3, 1.4 | |
| 27 | `sup_eigenLambda_ball` | proof of 1.1 | |
| 28 | `langevin_w2_contraction` | proof of 1.1 | `ρ ≥ 0`; **kernel form** (`IsEuclideanLangevin`, laws `ν.bind (Pt t)`), `V ∈ C^∞` |
| 29 | `langevin_entropy_decay` | proof of Cor 1.4 | `0 < d`; kernel form (`μ_t = ν.bind (Pt t)`); `V ∈ C^∞`; printed (non-sharp) constants |
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
| 40 | `langevin_fisher_decay` | eq. expdecI | kernel form; `V ∈ C^∞`; `I(ν) = ⊤` allowed |
| 41 | `langevin_fisher_dini` | before eq. expdecI | Dini form on `toReal` at times with `I(μ_t) ≠ ⊤`; no derivative claimed; kernel form; `V ∈ C^∞` |
| 42 | `normalization_sde` | Sect. 4.2 | solutions by hypothesis; `IsSDESolution` (a.s. continuous paths and integral equation) |
| 43 | `temperature_sde` | Sect. 4.4 | adds `C²`, `Hess V ≥ ρ > 0` (not in manuscript); `e^{-V/σ²}` normalizable; solutions by hypothesis |
| 44 | `temperature_cutoff` | Sect. 4.4 | hypothesis `ρₙ = σ² λ₁(Vₙ/σ²)`; `liminf ρₙ > 0`; information cutoffs under `ρ = o(log n)`; kernel form (`IsSigmaLangevin`); `Vₙ ∈ C^∞` (was `C²`), normalizability inside `IsSigmaLangevin` |
| 45 | `mixing_time_w2_rigid` | summary after Cor 1.6 | last conjunct an implication (`t₀ → ∞` only if `λ₁ = o(log n)`); any `η > 0`; kernel form |
| 46 | `mixing_time_kl_rigid` | summary after Cor 1.6 | needs `λ₁ = o(log n)`; any `η > 0`; kernel form |
| 47 | `exists_stdBrownian` | existence of Brownian motion (classical) | proved from the vendored library; space `Ω : Type`; no AI audit yet |
| 48 | `exists_langevin` | non-vacuity of `IsLangevin` | assumes `Hess V ≥ 0` (convexity, the paper's standing assumption; for non-convex `V` no global solution is claimed) and `IsProbabilityMeasure (gibbs V)`; `X x₀` is the project's selected pathwise solution; no AI audit yet |

## 3. Cross-cutting questions
- [ ] **Vacuity.** Only the Riemannian hypotheses have a Lean witness in the repository (`Riemann/WitnessMain.lean`, Gaussian on ℝᵏ, flat
      only). The second audit of Thm 1.9 reports having proved in scratch files (not committed) that the witness also admits the semigroup `Pt`
      via `isDiffusionSemigroup_Kk`; consider committing that check. For the Langevin-based statements, `exists_langevin` (no. 48) now shows that `IsLangevin V B P X` is satisfiable
      for every `C²` `V` with `Hess V ≥ 0` and probability Gibbs measure. Check that its hypotheses are no stronger than needed to be non-vacuous
      (all Langevin theorems also assume a curvature condition) and that the conclusion is the full `IsLangevin`, not a weakening. Decide whether a curved
      Riemannian witness is wanted.
- [ ] **Each amendment** (`0 < d`, `0 < finrank`, Thm 1.7, `hS`) necessary and harmless?
- [ ] **`C^∞` instead of `C²` (new amendment, 21 statements).** The Brownian-free statements assume `V ∈ C^∞` (inside `IsEuclideanLangevin`/`IsSigmaLangevin`; for no. 7 also `W n ∈ C^∞`),
      because uniqueness of the diffusion semigroup (Riemannian `bridge_final`, elliptic regularity) is proved for smooth potentials only. Confirm that this is an acceptable
      amendment relative to the manuscript's `C²`/convex setting (it is a restriction of the class of potentials, so these 21 statements are weaker than the printed ones in this respect).
- [ ] **Law form of Lemma 3.3 (no. 10).** The pathwise statement (a Brownian `β` on the same space with `dY = -ρY dt + √(2ρ) dβ`) is replaced by the law form
      `(Pt t x₀).map Tv = 𝒩(e^{-ρt} Tv x₀, (1-e^{-2ρt}) I)`. Confirm that this is an acceptable reading (the pathwise `β` cannot be stated without a Brownian motion; the generator and the Markov property of `T(X)` are not stated).
- [ ] **Convexity for kernels.** Statements 29, 40, 41 use `Hess V ≥ ρ > 0`; sequence statements use `RigidCurvature`; no extra convexity hypothesis was added to any kernel statement.
- [ ] **Manuscript vs printed paper.** The local `cutcur-lean.tex` differs from arXiv:2412.15969v4 (Thm 1.7 hypotheses, completeness and
      connectedness in the Riemannian setting, finite `p`, Thm 3.6). Judge whether the corrections are mathematically right
      (`PAPER_AUDIT.md`: the Ornstein–Uhlenbeck counterexample to Thm 1.7 is a written derivation, not checked in Lean) and agree with the authors' intent.
- [ ] **Global instance.** `Riemann/WitnessGeometry.lean` adds `instIsContMDiffRiemannianBundleRd`; confirm it cannot change the meaning of
      any Challenge statement (Comparator accepts; `temperature_cd` is the only statement touching it).
- [ ] **Not formalized** (honestly listed in `PALOMAR.md`): Question 1.10 (open); `eq:loggradbound` (conjecture); `dH/dt = -I` for general laws;
      Theorem 1.7 on manifolds; sphere, Dyson, Gaussian isoperimetry; Leibniz identity for the carré du champ;
      vector-form Bochner; the Rothaus remark. Decide whether any is required for the intended submission.
- [ ] **Cosmetic/lint:** deprecation warnings (`if_pos`, `if_neg`, `haveI`, `Set.mem_setOf_eq`) are harmless.

## 4. Process items (outside Lean)
- [ ] Fill `formalization.yaml` review fields only after a real review (`review.status`, reviewers); do not edit them before.
- [ ] Verify the `formalization.yaml` alignment entries (`lean: CutCur.<name>`) against the official schema; the format was not validated.
- [ ] Authors/responsible humans decide on registry submission and sign the attestation. Nothing was submitted or attested by the AI agents.
- [ ] Decide on the license/attribution statement for the archived paper (CC BY 4.0, `paper/SOURCE.txt`) and the project's Apache-2.0.

## 5. Vendored third-party code (Brownian existence)
The item "existence of Brownian motion" moved from not formalized to formalized, by vendoring (`vendor/`, `vendor/README.md`).
- [ ] Review the provenance in `vendor/README.md`: upstream repositories, commits `546d77295fdf8ae7f44cec14ec5df7959c4e3617` (brownian-motion) and
      `c20f168ed693537c78111ffeabc2ab5f384e35d6` (kolmogorov_extension4); diff the 26 + 3 vendored files against those commits and check that the only
      differences are the listed patches (3 added `have hqd_nonneg` lines, 1 dropped `.aemeasurable`, 1 added import line, and the `-- MODIFIED` comment lines).
- [ ] Review the added module `vendor/kolmogorov_extension4/Compat/CompactSystemExtra.lean` (backport of Mathlib material, not upstream).
- [ ] Licence: upstream Apache-2.0 texts are in `vendor/*/LICENSE`, headers kept; the project root keeps exactly one licence file.
- [ ] The Challenge closure stays Mathlib-only (the Brownian existence statements use only Challenge definitions); the vendored code is imported only
      (privately) by `CutoffRigidity/Paper/ExistsBrownian.lean`. Check that it adds no axiom (`#print axioms CutCur.exists_stdBrownian`).

## Sign-off (to be completed by humans; left blank on purpose)
Reviewer(s): ____________  Date: ____________  Commit reviewed: ____________
Scope reviewed (definitions / statements 1-48 / vendored code / other): ____________
Findings and decision: ____________
