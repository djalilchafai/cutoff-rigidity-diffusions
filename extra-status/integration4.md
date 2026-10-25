# Integration report 4 (Brownian-free Euclidean statements)

State: `lake build` (9723 jobs, incl. Challenge, Solution) succeeds; `scripts/check-palomar.py --ready` passes (804 Lean files); `sync-statements.py --check` ok;
`#print axioms` of five sampled replaced theorems from `import Solution`: propext, Classical.choice, Quot.sound. Comparator NOT run, nothing committed.

## Replaced in Challenge.lean (same names/positions; text = the `_K` statements of euc2-5, only docstrings rewritten/shortened)
main_wasserstein_estimate, wasserstein_cutoff, information_cutoff, lp_cutoff, convex_interaction_cutoff, product_condition_cutoff, eigenmap_is_ou, mixing_time_rigid,
mixing_time_w2_rigid, mixing_time_kl_rigid, ou_fisher_information, ou_mean_start_cutoff, ou_lp_infty_fails, langevin_entropy_decay, langevin_fisher_decay, langevin_fisher_dini,
normalization_cutoff, temperature_cutoff. Statements were extracted programmatically from the compiled Extra files (unqualified), so they equal what is proved.
`langevin_w2_contraction_K` not added.

## Definitions
Added to Challenge (9): IsEuclideanDiffusion, IsEuclideanLangevin (after IsLangevin), worstK (after worst), IsRigidSequenceK (after IsRigidSequence), mixingTimeK/W2K/KLK (where the old ones were),
IsSigmaDiffusion, IsSigmaLangevin (after IsSDESolution). Deleted from Challenge and comparator.json: mixingTime, mixingTimeW2, mixingTimeKL (no remaining Challenge user).
Kept: worst, IsRigidSequence (used by wasserstein_cutoff_weak, information_cutoff_weak), IsLangevin, IsStdBrownian, IsLangevinSolution, IsSDESolution.
The three old mixing-time defs are moved to the new proof-side module `CutoffRigidity/Paper/CarrierDefs.lean` (namespace CutCur), since the `_carrier` proofs use them.
comparator.json now: 48 theorems (Challenge order), 57 definitions. The defs were removed from the euc Extra files, which now import `CutoffRigidity.Statements`; the `import all` in EuclideanKernelStatements is gone.

## Paper side
Renamed with suffix `_carrier` (proofs kept, all users updated by word-boundary rename, 19 files): Paper.main_wasserstein_estimate, wasserstein_cutoff, information_cutoff, lp_cutoff,
convex_interaction_cutoff, product_condition_cutoff, eigenmap_is_ou; Extra mixing_time_rigid, mixing_time_w2_rigid, mixing_time_kl_rigid, ou_fisher_information, ou_mean_start_cutoff,
ou_lp_infty_fails, langevin_entropy_decay, langevin_fisher_decay, langevin_fisher_dini, normalization_cutoff, temperature_cutoff. (Note: Extra/Dynamics.lean langevin_entropy_decay etc. included.)
`CutoffRigidity.Paper.<name>` is now `alias <name> := <name>_K` at the end of EuclideanWasserstein / EuclideanCutoffs / EigenmapOUK / EuclideanKernelStatements.
No change to gen-solution.py was needed (`apply ... <;> assumption` works). CutoffRigidity.lean: imports of CarrierDefs and the 5 Extra modules added.

## Challenge size
993 lines, 70404 bytes (limits 1000 / 100 KiB). Tight on lines (7 spare); all docstrings rewritten more compactly, no statement shortened.

## Changes relative to the proposed text
Only docstrings (merged old doc with the kernel/C^infty flags). IsEuclideanDiffusion/IsEuclideanLangevin docstrings mention uniqueness is proved, not assumed. Non-converted statements
still using Brownian objects: wasserstein_cutoff_weak, information_cutoff_weak, langevin_w2_contraction, normalization_sde, temperature_sde, exists_*.

## Docs
formalization.yaml (status.scope and fidelity.divergences extended; review stays unchecked; YAML parses), README.md, PALOMAR.md (section "Brownian-free Euclidean statements"), PAPER_AUDIT.md,
HUMAN_REVIEW.md (18 rows flagged, new definitions to review, C^infty and law-form checklist items, counts updated). Old AI audit files not updated (they refer to the previous texts).
