# Integration report 5 (last three Brownian-based Euclidean statements converted)

State: whole-project `lake build` (9721 jobs) succeeds; `scripts/check-palomar.py --ready` passes (805 files); sync-statements/gen-solution rerun.
`#print axioms` (from `import Solution`, scratch file outside repo) of `wasserstein_cutoff_weak`, `information_cutoff_weak`, `langevin_w2_contraction`: propext, Classical.choice, Quot.sound.
Comparator not run, nothing committed.

## Challenge.lean
`wasserstein_cutoff_weak` (Rem 3.4), `information_cutoff_weak` (Rem 3.5), `langevin_w2_contraction` replaced in place by the kernel statements (text of the compiled `_K` theorems;
in the `_K` files `CutCur.criticalTime` is qualified because of a name clash with `Paper.criticalTime`, same constant). Deleted: `worst`, `IsRigidSequence` (also from comparator.json definition_names).
Challenge: 981 lines, 69194 bytes. comparator.json: 48 theorems (unchanged order), 55 definitions.

## Proof side
- New `CutoffRigidity/Extra/EuclideanWeakK.lean`: `wasserstein_cutoff_weak_K`, `information_cutoff_weak_K`, plus aliases `Paper.wasserstein_cutoff_weak`, `Paper.information_cutoff_weak`, `Paper.langevin_w2_contraction`
  (the last := `langevin_w2_contraction_K` from EuclideanWasserstein.lean). Imported in CutoffRigidity.lean.
- Renamed `_carrier`: `Paper.wasserstein_cutoff_weak`, `Paper.information_cutoff_weak`, `Paper.langevin_w2_contraction` (Dynamics.lean; users in MixingTimeW2KL, EuclideanWasserstein updated).
- `worst` and `IsRigidSequence` moved to `Paper/CarrierDefs.lean` (namespace CutCur); `public import CutoffRigidity.Paper.CarrierDefs` added to 15 Extra/Paper files that use them.
- 3.4 uses `exists_langevinSeq_of_K` + `RigidCurvature.hess_nonneg`; 3.5 follows `information_cutoff_K` via `exists_isRigidSequence_of_K`.

## Docs
formalization.yaml (divergences: 21 statements, remaining SDE list), README, PALOMAR.md, PAPER_AUDIT.md, HUMAN_REVIEW.md (rows 11, 12, 28, definitions list, counts 21/55) updated.
Only `normalization_sde`, `temperature_sde`, `exists_stdBrownian`, `exists_langevin` still mention Brownian motion in Challenge. formalization.yaml still lists `CutCur.wasserstein_cutoff_weak` etc. (names unchanged).
