# bmx: existence of a standard Brownian motion via Degenne's `brownian-motion` library (spike)

Date 2026-10-25. Nothing in the main project was modified (this file is the only write). All work in
`/tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/bmx/`
(`proj/` = patched sources built against OUR Mathlib; `bump/` = upstream library against ITS Mathlib; `mainbump/` = copy of our
project against ITS Mathlib; `patches/` = diffs and mini Challenge/Solution; `shim/bwrap` = sandbox wrapper variant).

## 0. Result in one paragraph
`exists_stdBrownian (d : ℕ)` (exactly the bmA statement, Challenge definitions of `Rd`/`IsStdBrownian`) is PROVED, in ~25 lines, from
`isBrownianReal_brownian` + `gaussianLimit` + `Measure.pi` + `iIndepFun_pi`, with axioms `propext, Classical.choice, Quot.sound` only.
It compiles BOTH against the library's own Mathlib (e91b128082) and against OUR Mathlib (065356127b), the latter after a tiny port
(6 changed lines in 3 library files + a 163-line backport of 3 Mathlib PRs). A mini Challenge/Solution pair built on it was accepted by
`lake comparator` in the bwrap sandbox, with Lean kernel, nanoda and con-ron (59,887 declarations). Recommendation: (ii) vendoring
(30 files, 6.6k lines, Solution side only). Existence of Brownian motion, estimated 2000-2800 lines in bmA, becomes a half-day integration job.

## 1. The library
- `brownian-motion` HEAD 546d772 (2026-10-23), toolchain v4.35.0, Mathlib e91b128082 (2026-10-22); `kolmogorov_extension4` c20f168 (2026-10-15).
- `theorem isBrownianReal_brownian : IsBrownianReal brownian gaussianLimit` (Gaussian/BrownianMotion.lean L444), `brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ`,
  `gaussianLimit : Measure (ℝ≥0 → ℝ)` with `IsProbabilityMeasure` instance. Proof route: Kolmogorov extension (ke4) + Kolmogorov-Chentsov.
- `IsBrownianReal`/`IsPreBrownianReal` are MATHLIB definitions (Mathlib/Probability/BrownianMotion/Basic.lean), not library ones. I diffed that file and
  `GaussianProjectiveFamily.lean` between the two Mathlib revisions: identical definitions (`structure IsBrownianReal ... extends IsPreBrownianReal` + `cont : ∀ᵐ ω ∂P, Continuous (X · ω)`);
  the only diff is a bullet indentation in one proof. So the library's theorem is literally about the same predicate as Challenge's.
- Transitive closure of `BrownianMotion.Gaussian.BrownianMotion` (the part needed): 26 modules of `BrownianMotion/{Auxiliary,Continuity,Gaussian}` = 6,080 lines, plus ke4 (3 files, 362 lines).
  No `sorry` in this closure (the `sorry`s of the library are in StochasticIntegral/ and Gaussian/IteratedLogarithm.lean, outside the closure);
  `#print axioms isBrownianReal_brownian` = `[propext, Classical.choice, Quot.sound]` (checked in both environments). All files already use `module`, max file 1210 lines, no forbidden tokens
  (I ran check-palomar's `code_only`/token regex on the 30 files: 0 hits).

## 2. Mathlib revisions
Our rev is an ancestor of the library's: the library rev is 652 commits ahead (compare API: `ahead_by 652, behind_by 0`; 6,690 files changed, 875 in Probability/MeasureTheory/Topology;
includes big refactors such as "make `Set` a one-field structure" and many renames). The object e91b128082 is already inside the shared mathlib `.git`, so no network is needed to inspect it.
Mathlib's own cache for e91b128082 exists (`lake exe cache get`: 9038 files, ~2 min).

## 3. Build against OUR Mathlib (scratch Lake project, real `.lake/packages` of symlinks to the shared packages; Mathlib NOT rebuilt)
Setup: `proj/lakefile.toml` requires mathlib at our rev (same manifest as the main project), libs `KolmogorovExtension4`, `BrownianMotion` (globs = the 26 closure modules), `Compat`.
Errors found (exhaustive, since the build now succeeds; 3 library files, then everything compiles):
1. `KolmogorovExtension4/CompactSystem.lean`: needs `compactClosedSquareCylinders`, `isCompactSystem_compactClosedSquareCylinders`, `IsCompactSystem.{supClosure,countableInfClosure,prod,pi}`,
   which entered Mathlib (PRs #36089, #36225, #36160) after our rev, plus `Set.iInter_prod_iInter`, `Set.iInter_pi`, `Set.iInter_univ_pi_eq_empty_iff`, `Set.biInter_univ_pi_eq_empty_iff`.
   Fix: new module `Compat/CompactSystemExtra.lean` (163 lines, copied from Mathlib at the new rev, 3 small lemmas re-proved by `ext; simp`/explicit proof) and 1 added import line.
   Cost: ~1 hour. This file is Apache-2.0 (Degenne, Pfaffelhuber; Mathlib), keep its header.
2. `Continuity/IsKolmogorovProcess.lean` (2 errors): `gcongr` no longer discharges the side goal `0 ≤ q - d` automatically; fix: `have hqd_nonneg : (0:ℝ) ≤ q - d := sub_nonneg.2 hdq_lt.le` before the three `gcongr` calls (3 added lines).
3. `Continuity/KolmogorovChentsov.lean` (1 error): `tendstoInMeasure_of_tendsto_ae_of_measurable_edist` takes `Measurable` in our rev, `AEMeasurable` in the new one; fix: drop a `.aemeasurable` (1 line).
Total: 3 error kinds, 3 library files + 1 new compat file. All other 23 modules compile unchanged. Patches: `patches/bm-IsKolmogorovProcess.diff`, `patches/bm-KolmogorovChentsov.diff`,
`patches/ke4-CompactSystem.diff`, `patches/Compat-CompactSystemExtra.lean`. Full build of the closure in the scratch project takes ~25 s.

## 4. Alternative: bump the main project to the library's Mathlib (NOT recommended)
I built a scratch copy of the main project (`mainbump/`, sources only, Challenge+Solution targets, Mathlib e91b128082 from cache, toolchain v4.35.0; main project untouched) :
- the build stops with 81 error messages in 17 directly broken modules out of 762 (HopfLaxDerivatives 16, Riemann/DiffFrComplex 21, RiemannianGradientCalculus 9, Riemann/WeightedBochnerTrace 7, WeightedBochnerTest 6,
  WeightedIBPLocal 4, LangevinFlow 3, and 10 others with 1-2): failed instance synthesis (29), unsolved goals, `Invalid projection` (the `Set` structure change), renamed lemmas
  (`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`, `tendsto_integral_of_dominated_convergence`, `HasFDerivAtFilter.inv`, `Euclidean.nhds_basis_closedBall`), 2 heartbeat timeouts,
  `fun_prop` failures. ~180 dependent jobs were not built, so the true count is higher (each fix can expose dependents).
- Estimated port: 1-3 agent-days, plus re-audit that the Challenge definitions (`Set`, `Measure.prod` junk value change, `sfinite` renames etc.) mean the same, re-run of all audits that quote Mathlib behaviour, full Comparator rerun (~hours),
  toolchain change rc2 -> v4.35.0, a second shared packages directory (new revs of batteries/aesop/...). Breakage risk: moderate, cost far out of proportion to gaining one theorem. Revisit only if a future bump is needed anyway.

## 5. The theorem (scratch files, both compile and pass `#print axioms`)
`patches/ExistsBM-newMathlib.lean` (library's Mathlib) and `proj/Scratch/ExistsBM.lean` (our Mathlib). Content:
```lean
lemma isBrownianReal_comp (hf : MeasurePreserving f P Q) (hX : IsBrownianReal X Q) :
    IsBrownianReal (fun t w => X t (f w)) P where
  hasLaw I := (hX.hasLaw I).comp hf.hasLaw
  cont := hf.quasiMeasurePreserving.ae hX.cont
theorem exists_stdBrownian (d : ℕ) : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → Rd d),
    IsProbabilityMeasure P ∧ IsStdBrownian B P := by
  refine ⟨Fin d → (ℝ≥0 → ℝ), inferInstance, Measure.pi fun _ => gaussianLimit,
    fun t w => WithLp.toLp 2 (fun i => brownian t (w i)), inferInstance, ?_, ?_⟩
  · intro i; exact isBrownianReal_comp (f := fun w => w i) (measurePreserving_eval _ i) isBrownianReal_brownian
  · exact iIndepFun_pi (μ := fun _ : Fin d => gaussianLimit) (X := fun _ => fun ω t => brownian t ω)
      (fun _ => (Measurable.of_eval fun t => measurable_brownian t).aemeasurable)
```
Finite `Measure.pi` suffices (no `infinitePi`). With `exists_stdBrownian` the project can add `exists_langevin` (bmA section 5: ~100-200 lines of glue via `langevinSolution`, assuming convexity); not done here.

## 6. Integration into a Palomar submission
Constraints found (PalomarPolicy CONTRIBUTING.md sections 2.1, 2.4, fetched 2026-10-25; scripts/check-palomar.py; PALOMAR.md):
- Challenge transitive import closure must be Lean core + Mathlib (+Tau Ceti/CSLib) only. `exists_stdBrownian` is stated with Mathlib's `IsBrownianReal`: OK, Challenge unchanged in spirit.
- Solution-only dependencies may be ANY public GitHub repo pinned by 40-char SHA in `lake-manifest.json` (credential-free `https://github.com/owner/repo`), no submodules, no LFS.
- Every regular `.lean` file in the submission needs `module` and <= 10,000 lines (external pinned Git deps exempt from the cap). Mathlib toolchain must equal project toolchain (rc2 now matches).
- Comparator replays the Solution closure (all three kernels, as tested). check-palomar requires exactly one root licence file.

Three options:
(i) Git dependency. Upstream commits need Mathlib e91b128082 + toolchain v4.35.0 (section 4, expensive). With our Mathlib one needs PUBLIC patched forks of both `brownian-motion` and `kolmogorov_extension4`
(+ the compat file), pinned by SHA, and the fork's lakefile should drop `checkdecls`/`subverso` (docs-only). Manifest: add entries for the 2 packages (generate with `lake update brownian_motion kolmogorov_extension4` in a COPY, then merge only those entries into the main manifest; do not
let Lake touch mathlib), `.lake/packages` becomes a real dir of symlinks to the shared packages plus the two real clones. Wrapper `scripts/bwrap-home-symlink-wrapper.sh` must be changed: it currently ro-binds only `readlink -f .lake/packages`;
with per-package symlinks it must ro-bind each symlink target (my `shim/bwrap` does exactly this and the sandboxed Comparator accepted: loop `for e in .lake/packages/*; [ -L $e ] && --ro-bind $(readlink -f $e)`; `$HOME` may be unset inside lake's
child, use `getent passwd` instead). Costs: 2 public forks to maintain, manifest surgery, wrapper change, rc2 vs v4.35.0 irrelevant. Risk: forks must stay public; Palomar's verifier builds third-party packages itself (fine).
(ii) Vendoring (RECOMMENDED). Copy the 30 files (26 library modules + 3 ke4 modules + `Compat/CompactSystemExtra.lean`, 6,609 lines in total) to e.g. `vendor/BrownianMotion/...` and declare them in `lakefile.toml` as additional `[[lean_lib]]`
with `srcDir = "vendor"` (or `roots`/`globs` as in `proj/lakefile.toml`; note: with `roots`, imported sibling modules of the same package are NOT built, one must use `globs` listing all modules). No change to `lake-manifest.json`, no change to the
packages directory, no change to the sandbox wrapper (verified: my mini project is this exact situation: libs inside the project, Mathlib via symlinked packages; `lake comparator --config` with nanoda + con-ron + Lean kernel passed in 2m25s/3m03s).
Add `CutoffRigidity/Paper/ExistsBrownian.lean` (the ~25 lines above, imports `BrownianMotion.Gaussian.BrownianMotion`), wire it in Solution.lean, and add `exists_stdBrownian` to Challenge.lean (+ `comparator.json`, sync-statements.py/gen-solution.py if they enumerate names).
Import only that one module from Solution so the vendored root-namespace lemmas (they extend `ProbabilityTheory`, `MeasureTheory`, `Set`, `ENNReal`, ... namespaces) never meet a clash with project names (project declarations live in `CutoffRigidity.*`/`CutCur.*`; I found no collisions by namespace inspection; not built with the full 767-file project). When the project later bumps Mathlib, delete `Compat/` (upstream now has it) and re-test.
Licence (Apache-2.0, same as the project): keep each file's copyright header (already present), put the upstream `LICENSE` text in `vendor/…/LICENSE` (NOT at repo root: check-palomar demands exactly one root licence file), add a `NOTICE`-style README stating origin repos + commits
(546d772.., c20f168..), and mark the 3 modified library files and the backported file as modified (Apache-2.0 4(b)); list both repos as reused formalisations in `formalization.yaml` (sources/dependencies) and `PALOMAR.md`.
Cost: ~0.5-1 agent-day, ~6.6k extra lines (the project is 118k lines; 762 files + 30), con-ron declaration count rises (mini project alone: 59,887 vs 88,115 for the main solution; union maybe ~100-110k).
(iii) Prove from scratch (bmA R2): ~2000-2800 lines, 2-4 agent-weeks, risk in independence plumbing. Dominated by (ii) now. Only reason to prefer it: avoiding vendored third-party code in the Solution (trust/size), which Palomar explicitly allows.

## 7. Recommendation
Do (ii) vendoring now: it needs no Mathlib bump, no manifest/wrapper changes, is already validated through the sandboxed Comparator (all three kernels), and turns the non-vacuity gap of the Challenge (docstring of `IsLangevin`)
into a proved theorem `exists_stdBrownian` (then `exists_langevin` from bmA section 5 as a follow-up). Choose (i) only if you prefer an auditable pinned upstream and are willing to publish two patched forks; avoid the Mathlib bump (17+ files broken, 1-3 days, re-audit) unless forced.
Caveats: (a) the vendored sources are patched at 3 places and a backport file is added, so the claim is "uses Degenne's library, lightly ported", not "uses upstream commit X"; (b) the exact integration into the 767-file project was not built (only the mini project was; the project's own `.lake/build` was untouched);
(c) the theorem relies on 6.6k lines of third-party Lean (checked by the kernels, no extra axioms) but it is not part of the Challenge statement, so the statement-audit burden is unchanged.
