# Integration report 2 (cheap block: cb1-cb4 into Challenge/Solution)

State: `lake build` (whole project, 9683 jobs) succeeds; `lake build Challenge Solution` succeeds; `python3 scripts/check-palomar.py --ready`
passes; `scripts/sync-statements.py --check` passes; `#print axioms` of the 11 new `CutCur.*` theorems from `import Solution`: only propext,
Classical.choice, Quot.sound. Comparator NOT run. Nothing committed.

## Final theorem list (46 in comparator.json, Challenge order; 51 definitions)
The previous 35, plus 11 new:
- after mixing_time_rigid: mixing_time_w2_rigid, mixing_time_kl_rigid
- after langevin_entropy_decay: langevin_fisher_decay, langevin_fisher_dini
- after normalization_cutoff: normalization_sde
- after temperature_bakry_emery: temperature_sde, temperature_cutoff
- Riemannian section, after temperature_cd: bochner_identity, CD_iff_ricci
- Riemannian section, after mSpectralGap_ge_of_CD: riemannian_k1_bounds, riemannian_poincare_lsi

## Definitions moved to Challenge.lean (deleted from the Extra files, which now `public import CutoffRigidity.Statements`)
mixingTimeW2, mixingTimeKL (after mixingTime); IsSDESolution (before normalization_cutoff); mCurv, mExt, mRic, mHess, mHessSq (Riemannian
section after temperature_cd). `entropyOf` generalized to `{α : Type*} [MeasurableSpace α]` (same body); `mEntropy` and `mEntropy_eq_entropyOf`
deleted; `riemannian_poincare_lsi` now uses `CutCur.entropyOf`. NoBm*/OptimalConstants needed no change (the implicit `α` is inferred).

## Changes relative to the proposed texts
- Statements are exactly the proposed ones; Solution closes each by `apply CutoffRigidity.Paper.<name> <;> assumption` (no script change; `EXPLICIT` unchanged).
- Only cosmetic: in `langevin_fisher_dini` Challenge writes `≠ ⊤` where the Paper file has `≠ ∞` (same term; `∞` is ambiguous with the `ContDiff` scope);
  docstrings shortened and flags kept; binder lines of many signatures (old and new) were joined onto longer lines to meet the 1000-line limit
  (whitespace only, no statement changed); the module docstring was reflowed; the `normalization_cutoff` docstring now points to `normalization_sde`;
  in `temperature_bakry_emery` the three `let` definitions were put on one line each.
- Paper side: docstrings of Extra files mention that the definitions live in Challenge; `mixing_time_*` keep `Type u` (unifies with `Type*`).

## Other files
CutoffRigidity.lean: 7 `public import CutoffRigidity.Extra.*` lines appended. comparator.json regenerated (46 theorems, 51 definitions, same format).
formalization.yaml: 11 alignment entries, new scope update, divergences; review.status still `unchecked`. README.md, PALOMAR.md (section
"Cheap block integration"; Not-formalized list updated), PAPER_AUDIT.md (new table), HUMAN_REVIEW.md (rows 36-46 with flags, counts 46/51, definitions list,
not-formalized list) updated.

## Challenge size
998 lines, 68063 bytes (limits 1000 lines, 100 KiB). Little margin in lines: any further statement needs more reflowing.
Not touched (stale): verification/semantic-audit.md, verification/alignment.json and Comparator logs (they concern the earlier pair); other mentions of "35"
in verification/*.md.
