# Integration 6: adversary-accepted statements added to Challenge

## Final counts
- Challenge.lean: 995 lines, 77867 bytes (limit 1000 / 102400); 57 theorems (was 48), 60 definitions (was 55).
- comparator.json: 57 theorem_names, 60 definition_names (mirrors Challenge order; format unchanged).
- formalization.yaml: 57 alignment statements, review.status unchanged (`unchecked`).

## Added statements (all proved in Solution by `apply CutoffRigidity.Paper.<name> <;> assumption`)
Theorems (9): isLangevinSolution_map_eq_kernel_of_rigid, eigenmap_is_ou_pathwise, langevin_dissipation_ge_K',
langevin_dissipation_dirac_K, dyson_ou_static, carre_eq_operator, carre_polarization, generator_comp, bochner_vector.
Definitions (5): chamber, dysonProb (merged measure and normalisation, adversary's minimal form), mSecondDeriv,
mRoughLaplacian, mVecGenerator.
Dropped: nothing (item 5 `eigenmap_is_ou_pathwise` and `generator_comp` both fit). Not added, as instructed: C2Langevin,
Dissip core (B), Item6a.
Docstring fixes applied: Dyson ("optimal Poincare constant over bounded smooth Lipschitz test functions is 1/rho, with h extremal";
"V - rho|x|^2/2 is convex on the chamber"; no lambda_1 claim; Dyson process not claimed), frame independence of the rough Laplacian
softened to "mathematically ... not asserted here". Dissipation keeps hrho, hHess; Dirac statement has 0<s<t.

## How the Paper side is organised
- SdeId1.lean (Paper.isLangevinSolution_map_eq_kernel_of_rigid, Paper.eigenmap_is_ou_pathwise): used as is (already same statement).
- New CutoffRigidity/Paper/ChallengeExtras.lean: thin wrappers Paper.langevin_dissipation_ge_K', Paper.langevin_dissipation_dirac_K
  (from Dissip.*) and Paper.dyson_ou_static (from Dyson.dyson_ou_static; Dyson.dysonProb = CutCur.dysonProb and chamber are `rfl`;
  the ConvexOn conjunct is transferred by funext + simp [dysonV]; last conjunct by optimalPIDyson_eq).
- Item2a.lean: removed the unused `[MeasurableSpace M] [BorelSpace M]` variables; `generator_comp` and `carre_comp_left'` need them
  internally (library lemmas), so they now build `borel M` locally with `letI`/`haveI`. The [MeasurableSpace F] [BorelSpace F]
  variables are kept (the Challenge's Riemannian `variable` block has them).
- Item2b.lean: its own copies of mSecondDeriv/mRoughLaplacian/mVecGenerator removed; it now uses the CutCur ones from Statements.
- Dyson.lean, Dyson1D, Dyson2..Dyson7 were not `module` files (plain `import`), which makes `public import` from a module impossible
  and violates check-palomar's module-header rule: converted to `module` / `public import` / `@[expose] public section`
  (no proof changes). Dyson7 docstring wording fixed.
- CutoffRigidity.lean imports SdeId1, Dissip4, Dyson7, Item2a, Item2b, Paper.ChallengeExtras.
- scripts/gen-solution.py: EXPLICIT = {"langevin_dissipation_dirac_K": "(rho := rho)"}. Without it `apply ... <;> assumption` closed
  `0 < ?rho` with `hs : 0 < s` (rho := s) and then failed on hHess. This is the only change to the script.

## Statement-diff script
Script: /tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/stmtdiff.py
(strip all /- -/ comments, split into top-level declarations, normalise whitespace; HEAD Challenge.lean from `git show HEAD:Challenge.lean`).
Result: "old decls 115 new decls 129 identical subsequence: True": every pre-existing declaration is unchanged modulo comments and
whitespace; the 14 added declarations are exactly those listed above. Compression done: docstrings reflowed to <=250 columns,
module docstring paragraphs reflowed, and the signature lines of `let`-free theorems joined up to 130 columns.
(Docstring wording of existing declarations was only reflowed, not edited.)

## Commands and results
- python3 scripts/sync-statements.py, python3 scripts/gen-solution.py: OK; `sync-statements.py --check`: OK.
- lake build (default target CutoffRigidity, 9737-9741 jobs): Build completed successfully; then `lake build Solution Challenge CutoffRigidity`:
  success. First attempts failed and were fixed as described (Item2a MeasurableSpace M; non-module Dyson files; dirac `apply` capture).
- python3 scripts/check-palomar.py --ready: "Local source checks passed for 823 Lean files".
- Axioms: `#print axioms` of all 57 comparator theorems from a scratch file importing Solution: all 57 depend only on
  propext, Classical.choice, Quot.sound; no sorryAx (scratch/ax.lean and ax.out in the scratchpad).
- Not run: sandboxed Comparator (left to the lead), verification/Audit.lean.

## Open points for the lead
- README.md, PALOMAR.md, HUMAN_REVIEW*.md still say 48 theorems / 51 definitions (outdated before this change too: comparator.json had 55 defs);
  I did not edit them.
- No human or AI audit of the compressed Challenge text beyond the statement-diff script; the comparator has not been re-run.
