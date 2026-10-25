# Brief for scoping agents (no formalization of the final result, only feasibility study)

Project: Lean 4 formalization of `cutcur-lean.tex` (Chafaï–Fathi). 35 theorems are proved (`Challenge.lean`/`Solution.lean`). Read
`PALOMAR.md` and `extra-status/scan.md` (list of uncovered manuscript claims; its difficulty classification is by module names only and
unverified) for context. This task is SCOPING: decide what it would take to formalize the assigned items, faithfully to the manuscript.
Rules: edit no existing file; write only `scope-status/<your-name>.md` and scratch Lean files under the scratchpad directory (use them to test
that Mathlib/project definitions exist, that a statement elaborates, that an easy lemma goes through). Mathlib is at
`/chome/djay/S/Maths/Logiciels/Lean/mathlib-v4.35.0-rc2/packages/mathlib` (grep it; do not guess names).
For each assigned item report:
1. the manuscript lines and the precise mathematical claim;
2. a DRAFT Lean statement (elaborating, checked with `lake env lean` in a scratch file importing `CutoffRigidity.Statements` or `Solution`),
   stating clearly any hypotheses you had to add and why; whether it would be a faithful Challenge statement;
3. what the project and Mathlib already provide (exact names), and what is missing;
4. an effort estimate (lines of Lean, number of agents/days), the main risks, and whether it is feasible at all in this Mathlib revision;
5. a recommendation: do it / do a weaker faithful version / skip, with reasons, and an ordering relative to the other items.
Be concrete and honest: "infeasible" and "needs X months" are acceptable answers. Do not claim anything is proved unless a scratch file proves it.
