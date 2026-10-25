# bmA: existence of a standard Brownian motion in Lean (scoping)

Scratch check: `scratchpad/bm.lean` (both draft statements elaborate with `sorry`; nothing proved).

## 1. Claim and what must be proved
`IsStdBrownian B P` (Challenge L83) := `(∀ i, IsBrownianReal (fun t w => B t w i) P) ∧ iIndepFun (fun i w (t:ℝ≥0) => B t w i) P`.
Mathlib `IsBrownianReal X P` = `IsPreBrownianReal X P` (for all finite `I`, `HasLaw (I.restrict ∘ X) (projectiveFamily I) P`, i.e. centered
Gaussian with covariance `min s t`) + `∀ᵐ ω, Continuous (X · ω)` (only a.s. continuity, not everywhere). `P` need not be a probability
measure in the def (but follows from `HasLaw`).

## 2. Draft Lean statements (elaborate)
```lean
theorem exists_stdBrownian (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → Rd d),
      IsProbabilityMeasure P ∧ IsStdBrownian B P
theorem exists_langevin {d} {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbs V))
    (hc : ConvexOn ℝ Set.univ V) :   -- or: Hess V ≥ 0 / RigidCurvature V
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → Rd d) (X : Rd d → ℝ≥0 → Ω → Rd d),
      IsProbabilityMeasure P ∧ IsLangevin V B P X
```
(d ≥ 1 not needed; d = 0 is trivial.) Both are faithful Challenge-style statements (no hypothesis beyond the manuscript's standing ones;
the second needs convexity because global strong solutions are only constructed for `Hess V ≥ rate ≥ 0`).

## 3. Mathlib inventory (revision v4.35.0-rc2, Sep 2026)
Present:
- `MeasureTheory.Measure.infinitePi` (ProductMeasure.lean) with `infinitePi_map_piCurry`, `infinitePi_map_eval`, `isProjectiveLimit_infinitePi`;
  `ProbabilityTheory.exists_iid ι μ` (HasLawExists.lean): countable/any family of i.i.d. variables on a probability space.
- Ionescu-Tulcea `Kernel.traj` (IonescuTulcea/Traj.lean), `IsProjectiveMeasureFamily`, `IsProjectiveLimit`, `projectiveFamilyContent`,
  `closedCompactCylinders` (scaffolding "for Kolmogorov extension"); `Process/FiniteDimensionalLaws.lean`.
- `BrownianReal.projectiveFamily` + `isProjectiveMeasureFamily_projectiveFamily`; `IsPreBrownianReal`, `IsBrownianReal` and their
  closure properties (`neg`, `smul`, `shift`, `inv`, weak Markov `indepFun_shift`); `IsGaussianProcess.isPreBrownianReal_of_covariance`;
  `HasIndepIncrements.isPreBrownianReal_of_hasLaw` (law `gaussianReal 0 t` of each `X t` + independent increments suffices);
  `IsPreBrownianReal.hasIndepIncrements`. Gaussian toolbox: `gaussianReal`, `IsGaussian`, `HasGaussianLaw`, uncorrelated Gaussian => independent,
  `charFun`, `Measure.ext_of_charFun`, `indepFun_iff_charFun_prod`, `HasSubgaussianMGF.measure_ge_le`, `mgf_id_gaussianReal`.
- Borel-Cantelli (`measure_limsup_atTop_eq_zero`), `IsKolmogorovProcess` (Probability/Process/Kolmogorov.lean: only the DEFINITION of the
  Kolmogorov condition), `HolderWith`, `Topology/EMetricSpace/PairReduction.lean` (a chaining lemma, by Degenne-Ledvinka, preparatory).
Absent (confirmed by grep and by the docstrings "not yet in Mathlib"):
- Kolmogorov extension theorem for uncountable index sets (only the content + compact-cylinder scaffolding).
- Kolmogorov-Chentsov theorem (only the hypothesis structure `IsKolmogorovProcess`); no Hölder modification statement.
- Any existence theorem for Brownian motion, Wiener measure, Haar/Schauder system, isonormal process, Donsker.
No other Mathlib version in the packages dir (only one checkout).

## 4. Routes
**R1 (Kolmogorov extension + Kolmogorov-Chentsov).** Needs (a) Kolmogorov extension for `ℝ≥0 → ℝ` (inner regularity / tightness of the Gaussian
finite-dim laws, `piContent` sigma-additivity as in `piContent_tendsto_zero` but with compactness replacing Ionescu; scaffolding exists but the
core is missing): ~1500-2500 lines; (b) Kolmogorov-Chentsov with p = 4, q = 2 (dyadic chaining, Hölder on dyadics, uniform extension, modification
is indistinguishable-continuous version, measurability of the modification): ~1500-2500 lines; (c) moment bound `E|B_t-B_s|^4 = 3|t-s|^2`
(~150 lines) plus `IsKolmogorovProcess` packaging. Total ~4000-5000 lines. Both (a) and (b) are reusable general theorems (Mathlib
upstream interest; Degenne's BrownianMotion project is working on them, so a later Mathlib bump could supply them). Risky: two big general theorems.

**R2 (Lévy midpoint / Schauder construction) -- recommended.** Everything is countable; `exists_iid` / `infinitePi` give the i.i.d. N(0,1) family.
Plan (lemma-level):
1. L1 (~150): midpoint lemma: if `D ~ N(0,σ²)` and `Z ~ N(0,1)` independent, then `D/2 + σZ/2`, `D/2 - σZ/2` are independent `N(0,σ²/4)·`
   (uncorrelated jointly Gaussian => independent; Mathlib has the pieces).
2. L2 (~300): define the dyadic interpolants `F_n(t,ω)` (piecewise linear on level-n dyadic grid of [0,1], `F_{n+1} = F_n + Σ_k 2^{-(n+2)/2} Z_{n,k} Λ_{n,k}`)
   by recursion; they are continuous, `F_n(t)` measurable.
3. L3 (~300): induction: the level-n increments `F_n((k+1)/2^n) - F_n(k/2^n)` are i.i.d. `N(0,2^{-n})` (L1 + independence bookkeeping
   with `iIndepFun` over blocks of an infinite family: the heaviest "plumbing" lemma).
4. L4 (~250): `sup|F_{n+1}-F_n| ≤ 2^{-(n+2)/2} max_k |Z_{n,k}|`; Gaussian tail `P(|Z|>c√n) ≤ 2e^{-c²n/2}`, union bound over `2^n` points, `c` large enough, Borel-Cantelli
   => a.s. uniformly Cauchy (`Metric.cauchySeq_of_le_tsum`/Weierstrass M-test).
5. L5 (~250): define `B(t) = limsup/lim F_n(t)`, a.e.-measurability (`aemeasurable_of_tendsto_metrizable_ae`), a.s. continuity (uniform limit of continuous).
6. L6 (~400): finite-dim laws: for any `0 ≤ t_0 ≤ … ≤ t_k`, dyadic approximation; joint charFun of the increments of `F_n(t_j)` converges (dominated convergence,
   the Gaussian charFun is explicit) to the Gaussian charFun with covariance `min`; conclude `HasLaw ... projectiveFamily` via
   `isPreBrownianReal_of_covariance` (need Gaussianity of limit: `ext_of_charFun`, or get law `N(0,t)` for each t by charFun and independent increments via
   `indepFun_iff_charFun_prod`, then `HasIndepIncrements.isPreBrownianReal_of_hasLaw`). Cleanest: law `gaussianReal 0 t` of each `B t` (charFun limit, ~100 lines) plus
   `HasIndepIncrements` (limit of independent increments through charFun factorization, ~250 lines).
7. L7 (~300): extend `[0,1]` to `ℝ≥0`: glue countably many independent copies, `B(t) = B^{(m)}(t-m) + Σ_{j<m} B^{(j)}(1)`; index set `ℕ × ℕ × ℕ` for `exists_iid`;
   continuity at integers; increments/law again via independence (or build level-n grids on `[0,N]` directly with scaled Schauder, avoiding gluing).
8. L8 (~250): dimension d: take `Ω = Π (i : Fin d) (…)` with `infinitePi` (`infinitePi_map_piCurry` gives independence of blocks), `B t ω i := B^{(i)} t (ω i)`, prove each coordinate
   is `IsBrownianReal` (`MeasurePreserving` pullback, same as in project `isEuclideanBrownian_comp_measurePreserving`) and `iIndepFun` over `i` (curry lemma); probability measure.
Total ~2000-2800 lines; no deep missing theory, but long plumbing around infinite independence and a.s. convergence. Estimate: 2-4 weeks of one agent
with iteration (comparable to a medium Extra/Riemann module), 1-2 agents in parallel (L1-L5 vs L6-L8). Main risks: (i) independence plumbing for infinite families/blocks
(`iIndepFun` over sigma-algebras generated by sub-families; Mathlib has `iIndepFun.indepFun_finset` but infinite blocks need `infinitePi_map_piCurry`);
(ii) Haar-free proof of the covariance `min(s,t)` -- avoided by working with charFun on dyadic increments, but the passage from dyadic to arbitrary t needs care;
(iii) measurability / universe (use `Ω : Type`, as in `exists_iid` with u = 0) and the `ℝ≥0` vs `[0,1]` bookkeeping.
**R3 (Donsker)**: needs tightness in `C[0,1]`, Prokhorov on C, CLT in functional form; Mathlib has only a scalar CLT (`CentralLimitTheorem.lean`). 8000+ lines; not recommended.

## 5. Consequences for Challenge (what can be dropped)
- With `exists_stdBrownian` alone, no theorem hypothesis can be removed: statements like `main_wasserstein_estimate (hL : IsLangevin V B P X)` quantify over ALL `Ω,B,P,X`,
  which is stronger and more faithful than "for the canonical Brownian motion". Existence only certifies NON-VACUITY (the standing hypothesis is satisfiable). It would
  let us replace the docstring remark (Challenge L95-97, "existence ... not proved here") by an actual theorem, and add `exists_stdBrownian` (and `exists_langevin`) as
  Challenge statements to be proved in Solution.
- Existence of `X` DOES follow from `B` for convex `V`: the project already has deterministic global existence/uniqueness: `exists_langevin_path_on`,
  `exists_global_langevin_path` (LangevinGlobalExistence.lean), `langevinSolution V w x₀ t` (function of the driving path `w`), `brownianDrivingPath`,
  `brownian_global_langevin_path_exists_ae` (LangevinBrownian.lean; docstring says "joint measurability and adaptedness remain" but those are irrelevant for `IsLangevinSolution`,
  which only asks a.s. continuity + the integral equation, no adaptedness or measurability of `X`). Take `X x₀ t ω := langevinSolution V (brownianDrivingPath B ω) x₀ t`;
  then `IsLangevinSolution V B P x₀ (X x₀)` follows from the a.s. continuity of `B` and path-wise existence (~100-200 lines of glue, using `IsEuclideanBrownian` <-> `IsStdBrownian`,
  `isStdBrownian_iff`). It needs a `rate ≥ 0` Hessian lower bound (`hHess`), i.e. convexity; for general C² `V` with non-explosion failing no solution is claimed, so
  `exists_langevin` must assume `ConvexOn`/`Hess V ≥ 0` (all Challenge theorems using `IsLangevin` also have `RigidCurvature V` or `ρ/2|x|²+W`, `W` convex, so this covers them).
  Potential catch: for `IsLangevin` the existence of `X` as a SINGLE family `X : Rd d → ...` over all `x₀` is fine (the formula is uniform in `x₀`).
- Sequences `(V n, B n, P n, X n)`: separate probability spaces are allowed in Challenge (`B n`, `P n`), so `exists_seqBrownian`-type gluing is not needed for non-vacuity.
- The 5 Brownian-free statements already removed need nothing. The `eigenmap_is_ou` conclusion `∃ β, IsStdBrownian β P` is proved from `hB` by an orthogonal-rotation argument (does not use existence).

## 6. Recommendation
Do R2 (a faithful, fully proved existence theorem), then `exists_langevin` (small glue). Priority: LOW-MEDIUM relative to other scoping items, because it gives no stronger
theorem, only non-vacuity of hypotheses (which a human reviewer will care about: "are the Challenge hypotheses satisfiable?"). It is the only genuinely heavy missing classical
ingredient (~2500 lines), and is feasible in this Mathlib. Alternative cheap mitigation if skipped: keep the docstring disclaimer. Do not attempt R1 unless a later Mathlib supplies
Kolmogorov extension + Kolmogorov-Chentsov (check on next bump: `IsKolmogorovProcess` file is the stub for the latter).
