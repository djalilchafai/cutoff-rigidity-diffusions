# Extra formalization: manuscript statements not yet in Challenge.lean

Context: `Challenge.lean` has 12 theorems, all proved (`Solution.lean`). The manuscript `cutcur-lean.tex`
has further mathematical claims. Each agent below formalizes one group, FOLLOWING THE MANUSCRIPT
(statement and proof), as a theorem whose statement uses only `CutCur.*` definitions from
`Challenge.lean` (plus Mathlib), so that the lead can paste it into `Challenge.lean` as a
`theorem ... := by sorry` and wire the proof.

## Rules (all agents)
* Lean 4 / Mathlib pinned by the project: check a file with `lake env lean FILE`, a module with
  `lake build MODULE`. Never `lake clean`; never touch `lake-manifest.json`/`lakefile.toml`.
* No `sorry`, no `axiom`, no `native_decide`; only axioms `propext`, `Classical.choice`, `Quot.sound`
  (check with `#print axioms`).
* Do NOT edit `Challenge.lean`, `CutoffRigidity/Statements.lean`, `Solution.lean`, `CutoffRigidity.lean`,
  `comparator.json`, `formalization.yaml`, or any existing file (except adding a lemma upstream, then say so).
  Put new files in `CutoffRigidity/Extra/` (module `CutoffRigidity.Extra.<Name>`), `module` system, `public import`,
  `public section`, header style of `CutoffRigidity/Paper/ProductCondition.lean`. Files < 1500 lines.
* Final deliverable: in namespace `CutoffRigidity.Paper`, a theorem `<name>` whose statement is EXACTLY the
  text you propose for Challenge (same binders, only `CutCur.`-qualified names allowed in the Paper
  version). Put the proposed Challenge text (unqualified names, with docstring citing the manuscript item)
  in `extra-status/<agent>.md`. The statement must be faithful to the manuscript: no added hypotheses beyond
  those in the text; if the manuscript claim is false or vague, STOP on it and document precisely
  (counterexample/obstruction); only if unavoidable, state the minimal amendment and flag it as an amendment.
* Do not duplicate: grep the project and Mathlib first
  (`/chome/djay/S/Maths/Logiciels/Lean/mathlib-v4.35.0-rc2/packages/mathlib`). Existing Euclidean and Riemannian
  developments (`Paper/*.lean`, `Riemann/*.lean`) contain most tools.
* Report honestly in `extra-status/<agent>.md`: what is proved (exact names), what is open, blockers.
* Do not claim human review. Hand-backs are not verified until the lead checks them.
