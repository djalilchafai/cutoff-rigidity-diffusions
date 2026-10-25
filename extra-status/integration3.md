# Integration report 3 (Brownian existence, vendoring)

State: `lake build Challenge Solution BrownianMotion KolmogorovExtension4 Compat CutoffRigidity` succeeds (9721 jobs); `python3 scripts/check-palomar.py --ready`
passes (798 Lean files; script unchanged: it accepted the vendored files as is); `sync-statements.py --check` passes. `#print axioms` of both new
theorems from `import Solution`: propext, Classical.choice, Quot.sound. Comparator NOT run. Nothing committed.

## Theorems (48 now in comparator.json, 51 definitions)
- `CutCur.exists_stdBrownian (d)`: exactly the bmx spike statement. Paper proof `CutoffRigidity.Paper.exists_stdBrownian` (spike proof, `Measure.pi` of `gaussianLimit`).
- `CutCur.exists_langevin (d) (V) (hV : ContDiff ℝ 2 V) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) (hgibbs : IsProbabilityMeasure (gibbs V))`:
  `∃ Ω _ B P X, IsProbabilityMeasure P ∧ IsLangevin V B P X`. Proof 25 lines of glue: `X x₀ = langevinProcess V B x₀`, using
  `langevinProcess_continuous_paths_ae` and `langevinProcess_integral_equation_ae` with rate 0. Hypothesis is the Hessian form (the project's
  constructions take `rate * ‖z‖² ≤ Hess`, rate = 0), equivalent to convexity for C² (the direction Hess => convex is `Extra/NoBmConvex`; I did not prove convex => Hess,
  so ConvexOn was not used as hypothesis). Placed first in comparator.json's theorem list and at the start of the "Main Euclidean results" section of Challenge.
- File: `CutoffRigidity/Paper/ExistsBrownian.lean` (67 lines): `public import CutoffRigidity.Statements`, `CutoffRigidity.LangevinBrownian`, and a PRIVATE
  `import BrownianMotion.Gaussian.BrownianMotion` (so the vendored library is not re-exported). Wired by `public import` in CutoffRigidity.lean (last line).

## Vendored files (lines)
- total: 6620
- vendor/brownian-motion/BrownianMotion/Auxiliary/Algebra.lean: 33
- vendor/brownian-motion/BrownianMotion/Auxiliary/ContinuousBilinForm.lean: 353
- vendor/brownian-motion/BrownianMotion/Auxiliary/DenseCountable.lean: 28
- vendor/brownian-motion/BrownianMotion/Auxiliary/ENNReal.lean: 53
- vendor/brownian-motion/BrownianMotion/Auxiliary/FiniteInf.lean: 61
- vendor/brownian-motion/BrownianMotion/Auxiliary/HasLaw.lean: 29
- vendor/brownian-motion/BrownianMotion/Auxiliary/LinearAlgebra.lean: 81
- vendor/brownian-motion/BrownianMotion/Auxiliary/MeanInequalities.lean: 54
- vendor/brownian-motion/BrownianMotion/Auxiliary/MeasureTheory.lean: 312
- vendor/brownian-motion/BrownianMotion/Auxiliary/Metric.lean: 51
- vendor/brownian-motion/BrownianMotion/Auxiliary/NNReal.lean: 17
- vendor/brownian-motion/BrownianMotion/Auxiliary/Topology.lean: 120
- vendor/brownian-motion/BrownianMotion/Continuity/Chaining.lean: 284
- vendor/brownian-motion/BrownianMotion/Continuity/CoveringNumber.lean: 358
- vendor/brownian-motion/BrownianMotion/Continuity/HasBoundedInternalCoveringNumber.lean: 123
- vendor/brownian-motion/BrownianMotion/Continuity/IsKolmogorovProcess.lean: 1045
- vendor/brownian-motion/BrownianMotion/Continuity/KolmogorovChentsovInequality.lean: 400
- vendor/brownian-motion/BrownianMotion/Continuity/KolmogorovChentsov.lean: 1211
- vendor/brownian-motion/BrownianMotion/Continuity/LimitModification.lean: 382
- vendor/brownian-motion/BrownianMotion/Gaussian/BrownianMotion.lean: 497
- vendor/brownian-motion/BrownianMotion/Gaussian/CovMatrix.lean: 106
- vendor/brownian-motion/BrownianMotion/Gaussian/Gaussian.lean: 27
- vendor/brownian-motion/BrownianMotion/Gaussian/GaussianProcess.lean: 45
- vendor/brownian-motion/BrownianMotion/Gaussian/Moment.lean: 147
- vendor/brownian-motion/BrownianMotion/Gaussian/ProjectiveLimit.lean: 216
- vendor/brownian-motion/BrownianMotion/Gaussian/StochasticProcesses.lean: 52
- vendor/kolmogorov_extension4/Compat/CompactSystemExtra.lean: 171
- vendor/kolmogorov_extension4/KolmogorovExtension4/CompactSystem.lean: 126
- vendor/kolmogorov_extension4/KolmogorovExtension4/KolmogorovExtension.lean: 154
- vendor/kolmogorov_extension4/KolmogorovExtension4/RegularContent.lean: 84

30 Lean files, 6620 lines (6609 upstream-closure + 11 added: 3 `-- MODIFIED` comment lines, 8 header lines in the Compat file). Max 1211 lines.
Plus `vendor/brownian-motion/LICENSE`, `vendor/kolmogorov_extension4/LICENSE` (upstream texts), `vendor/README.md` (origins, SHAs, patches, notice).
The vendored files were taken from the spike's `proj/` copies (diffed against the upstream clones: only the patches differ).

## Patches
As in bmx.md: (1) 3 `have hqd_nonneg` lines in IsKolmogorovProcess.lean; (2) one `.aemeasurable` dropped in KolmogorovChentsov.lean; (3) one added import line in
CompactSystem.lean; (4) new `Compat/CompactSystemExtra.lean` (copyright header added by me, listing the Mathlib PRs). Each modified file got a
`-- MODIFIED ...` comment between header and `module`. lakefile.toml: three `[[lean_lib]]` (Compat, KolmogorovExtension4, BrownianMotion) with `srcDir`,
`globs`, and `leanOptions = {autoImplicit = false, relaxedAutoImplicit = false}` (the upstream options, as in the spike). Not touched: lake-manifest.json, packages, wrapper script.
Build of the three vendored libs from scratch: ~30 s.

## Collisions
None: the full build (CutoffRigidity, Challenge, Solution plus the vendored libs) has no declaration clash. The vendored library is imported only privately
by ExistsBrownian.lean (the one place where project and vendored names meet; it compiles). `Solution`'s environment contains none of the vendored declarations.

## Challenge.lean
953 lines, 68974 bytes (was 998 / 68085; limits 1000 / 100 KiB). To make room, 58 lines were saved by re-wrapping multi-line `/-- -/` docstrings to 150 columns
(script-verified: the whitespace-stripped non-docstring text is identical and the docstring texts are identical up to whitespace). `IsLangevin`'s docstring now says
the satisfiability is proved in `exists_langevin`. The `normalization_sde` docstring still says "no existence is claimed" (about solutions; left). Solution.lean and Statements.lean regenerated.

## Docs updated
formalization.yaml (alignment entries, two related_formalizations entries with the arXiv reference, scope update, acknowledgements; review unchanged `unchecked`; YAML parses),
README.md (counts 48, credits and licensing section), PALOMAR.md (new section "Vendored Brownian motion library"), PAPER_AUDIT.md (new table), HUMAN_REVIEW.md (rows 47-48,
IsBrownianReal check, non-vacuity item, new section 5 on vendored provenance/patches/licence/Challenge closure; counts).

## What remains
- Comparator rerun on the 48-theorem pair (sandboxed; con-ron declaration count will rise by the vendored declarations). The bwrap wrapper should work unchanged (vendor is inside the project).
- No AI audit of the two new statements; stale counts (35/46) remain in verification/*.md and in a few historical sentences of PALOMAR.md/README.md.
- `exists_langevin` assumes Hess V >= 0 (not ConvexOn); a convex => Hess lemma would allow the ConvexOn form. Non-convex V: nothing claimed.
- The Palomar rule "external pinned deps exempt from the 10000-line cap" is irrelevant (vendored files all < 1300 lines).
