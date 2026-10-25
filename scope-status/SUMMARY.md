# Scoping summary (25 October 2026): remaining Riemannian and Brownian items

Five scoping agents (reports `geoA.md`, `geoB.md`, `bmA.md`, `bmB.md`, `bmC.md`). Spot-checks by the lead: the scratch proofs
`GeoA1`, `k1`, `lsi`, `expdec`, `dini`, `sde_full`, `mixfinal`, `bmB/E1`, `bmB/E4` (scratchpad directory, not in the repository) were recompiled with
`lake env lean`: no errors, no `sorry`; `IsBrownianReal.smul` exists in Mathlib; `relativeFisherInformation_langevinKernel_le` exists in `FisherDecay.lean`.
Nothing here is added to the Challenge yet. All numbers are agents' estimates.

## Recommended, cheap, no new hard mathematics
| Item | Source | Cost | Note |
| --- | --- | --- | --- |
| `CD ρ V ↔ ∀ x v, ρ g(v,v) ≤ Ric_V(v,v)` and Bochner identity, with a named `Ric` | geoA | ~35 lines Challenge + ~150 proof, 0.5-1 agent-day | adds hypothesis `MSmooth V` (also the manuscript's); the `Ric` definition uses `Classical.choose` extensions (a choice-free formulation exists) |
| Riemannian `1 ≤ k₁ ≤ dim` | geoB | ~40 lines | under `CD`, `ρ > 0`, `λ₁ = ρ` (the manuscript does not claim it without; false on spheres) |
| Riemannian Poincaré and LSI (`ρ Var f ≤ ∫|∇f|²`, `Ent(f²) ≤ (2/ρ)∫|∇f|²`) | geoB | ~6 lines + general-space entropy definition | |
| Fisher decay `I(μ_t) ≤ e^{-2ρ(t-s)} I(μ_s)` for all initial laws | bmC | < 1 h | theorem already in the project |
| Dini form of `dI/dt ≤ -2ρI` | bmC | small | pointwise derivative has no rigorous meaning for general laws |
| Brownian scaling, SDE-level normalization (`IsSDESolution`) | bmC | ~120 lines | uses `IsBrownianReal.smul`; **corrects** the earlier "not available" claim |
| Temperature: SDE-level invariance, `Y(σ⁻²·)` Langevin for `V/σ²`, σ-free critical time (W₂; Fisher/entropy/TV by the same pattern) | bmC | ~150-250 lines | convex setting |
| W₂ and entropy mixing times `mixingTimeW2`, `mixingTimeKL` ≈ `log n/(2λ₁)` | bmC | ~250 lines | new definitions (like `mixingTime`) |
| Dyson on the chamber, static version (measure, `∑xᵢ` eigenfunction, Poincaré `1/ρ`) | geoB | 1.5-4k lines, 1-3 agent-weeks, medium risk | process-level statement infeasible |

## Large, decision needed
* **Existence of Brownian motion (Wiener measure).** bmA estimates 2000-2800 lines (Lévy midpoint construction, 8-lemma breakdown), bmB 3000-6000 lines
  (Lévy–Ciesielski via `Measure.infinitePi`); Kolmogorov extension + Kolmogorov–Chentsov would be ~4000-5000 lines (absent from Mathlib). Not reconciled: budget
  3-6 agent-weeks, high risk. Effect: **no Challenge hypothesis can be dropped** (the statements already quantify over all carriers); it would show the Langevin hypotheses are
  satisfiable (non-vacuity) and let the docstring "existence not proved here" become a theorem. `exists_langevin` for convex C² `V` needs ~100-200 further lines.
* **Brownian-free Euclidean statements** (bmB): `IsEuclideanDiffusion V Pt` is equivalent to `IsDiffusionSemigroup` on `ℝ^d`, `langevinKernel` satisfies it, and uniqueness holds for **C^∞**
  `V` (C² is out of reach: the Riemannian uniqueness theory needs elliptic regularity). Wrappers for four statements are proved given a placeholder `BMExists d`; the W₂-only
  statements (`main_wasserstein_estimate`, `wasserstein_cutoff`, `langevin_w2_contraction`) could go through Theorem 1.9 on `ℝ^d` without a Wiener lemma (400-800 lines of
  identification of `mFirstEigenDim`/`mLambda` with `firstEigenDim`/`eigenLambda`); entropy, Fisher, TV and Lp statements need the Wiener lemma. Trade-off to decide: C^∞ instead of C²,
  new `IsEuclideanLangevin` hypothesis, versus the current Brownian-carrier hypothesis. `eigenmap_is_ou` needs new mathematics (generator form ~250 lines; law form 600-1200).

## Skip (infeasible or no precise manuscript statement)
* Theorem 1.7 on manifolds (no precise statement; 10-20k lines, high risk).
* Sphere claims (`ρ = d-1`, `λ₁ = d`; Mathlib lacks Riemannian bundle instance, Ricci, spherical harmonics; 5-10k lines; cutoff needs heat-kernel asymptotics).
* Gaussian isoperimetry (3k+ lines for a "such as" mention); `dH/dt = -I` for general laws (1500-3000 lines, medium-high risk; the integrated inequality is what is used).
* Process-level Dyson statement.

## Suggested order
1. Cheap block (table above), starting with Ric/Bochner/CD, Fisher decay and Dini, Brownian scaling, k₁ bounds, Riemannian Poincaré/LSI, then temperature and the W₂/entropy mixing times.
   Each addition needs the usual integration (Challenge, Statements, Solution, comparator.json, formalization.yaml, rebuild, Comparator) and an AI audit; expect about 10 new theorems and the
   Challenge size limit (1000 lines / 100 KiB; now ~863 lines) to be approached.
2. Decide on Brownian existence and the C^∞ Brownian-free reformulation (the two large items above).
3. Optional: Dyson static version.

## Decisions needed from the user
* Is it worth doing the Wiener construction (3-6 agent-weeks) for non-vacuity only?
* Is replacing the Brownian-carrier hypothesis by `IsEuclideanLangevin` with `V ∈ C^∞` an acceptable trade for the Euclidean statements?
* Should the cheap block be integrated now (it brings the Challenge near its size limit)?
