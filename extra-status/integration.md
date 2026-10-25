# Integration report (extra theorems into Challenge/Solution)

State: `lake build` (whole project, 9668 jobs) succeeds; `lake build Challenge Solution` succeeds;
`python3 scripts/check-palomar.py --ready` passes; `#print axioms` of all 34 `CutCur.*` theorems from `import Solution`:
only propext, Classical.choice, Quot.sound. Comparator NOT run. Nothing committed.

## Final Challenge theorem list (34; comparator.json lists them, plus 43 definitions)
Original 12: main_wasserstein_estimate, eigenspace_dim_and_lambda, wasserstein_cutoff, information_cutoff, lp_cutoff,
convex_interaction, convex_interaction_cutoff, product_condition_cutoff, euclidean_gaussian_factorization, eigenmap_is_ou,
riemannian_wasserstein_estimate, riemannian_gaussian_splitting (statement now the strengthened one).
New 22 (in Challenge.lean after eigenmap_is_ou, before the Riemannian section, except temperature_cd):
wasserstein_cutoff_weak, information_cutoff_weak, spectral_gap_ge_curvature, rigidity_of_gaussian_factor, pairwise_interaction,
ou_first_eigenspace, ou_mean_start_cutoff, ou_lp_infty_fails, mixing_time_rigid, langevin_moment_bounds, sup_eigenLambda_ball,
langevin_w2_contraction, langevin_entropy_decay, pinsker_tvDist, talagrand_logSobolev, optimal_lsi_twice_pi,
optimal_constants_extremal, ou_fisher_information, heat_kernel_score, normalization_cutoff, temperature_bakry_emery,
temperature_cd (placed in the Riemannian section right after `def CD`, since it uses `CD`).
New definitions in CutCur (Challenge, before optimal_lsi_twice_pi): entropyOf, IsTestFunction, optimalPI, optimalLSI.

## Changes relative to the proposed texts
1. `temperature_cd`: `CD (Rd d) ...` needs the instance `IsContMDiffRiemannianBundle 𝓘(ℝ, Rd d) ∞ (Rd d) ...`, which is a
   global instance in Riemann/WitnessGeometry and not available to Challenge (imports Mathlib only). The Challenge and Paper
   statements now take it as an instance argument `[IsContMDiffRiemannianBundle ...]` (a Prop; no loss since the
   metric is Mathlib's). Paper side (Extra/Temperature.lean) edited accordingly (`open Bundle`, `Manifold`).
2. Binders `{d : ℕ}` / `{Ω : Type*} [MeasurableSpace Ω]` made explicit where the Extra files used `variable`; `Type u` -> `Type*`;
   `klDiv` -> `InformationTheory.klDiv`. Statements otherwise exactly the Paper ones (Solution builds by `apply ... <;> assumption`).
3. Docstrings extended to flag amendments (0 < d; IsStdBrownian / IsLangevin carrier hypotheses; test class; HWsmallt constants).
4. Splitting: Challenge statement is the Extra statement (potential identity + ConnectedSpace N ∧ CompleteSpace N).
   Paper side: old `Paper.riemannian_gaussian_splitting` (Riemann/AssembleMain.lean) renamed `riemannian_gaussian_splitting_base`
   (users updated: DiffAssembleCanonical, WassAssemble, WitnessMain). New `Paper.riemannian_gaussian_splitting` at the end of
   Extra/SplitPotential.lean, proved by `riemannian_gaussian_splitting_potential`.
5. OptimalConstants: defs moved to CutCur (Challenge/Statements); Extra file imports `CutoffRigidity.Statements`, uses
   `open CutCur (entropyOf IsTestFunction optimalPI optimalLSI)`, and the `IsTestFunction.*` lemmas are now `_root_.CutCur.IsTestFunction.*`.

## Script changes
scripts/gen-solution.py: table `EXPLICIT` giving `(Ω := Ω)` to `apply` for optimal_lsi_twice_pi, optimal_constants_extremal,
talagrand_logSobolev (Ω occurs only in hypotheses, so `apply <;> assumption` could not synthesize `MeasurableSpace ?Ω`).
sync-statements.py unchanged (works; `theorem` at line start, ends with `  sorry`; defs kept).

## Other files
CutoffRigidity.lean: 16 `Extra.*` imports appended. comparator.json regenerated from Challenge order. formalization.yaml: 22 new
alignment entries (manuscript item as YAML comment), scope/fidelity text, review.status still `unchecked`. README.md, PALOMAR.md
(new section), PAPER_AUDIT.md (Remarks 3.4/3.5, Thm 3.6, new table) updated; not-formalized items listed honestly.
Not touched (stale): verification/semantic-audit.md still says the V∘Φ⁻¹ identity is not in Lean; verification/alignment.json
and the Comparator logs concern the 12-theorem pair. Challenge.lean is now 858 lines (limit 1000).
