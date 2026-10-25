# Brief for independent statement-fidelity auditors (new statements)

Project: Lean 4 formalization of `cutcur-lean.tex` (Chafaï–Fathi). `Challenge.lean` states theorems with `sorry`;
`Solution.lean` proves them. A statement is *faithful* if it says what the manuscript item says: no
dropped or added hypotheses, correct quantifiers/ranges/constants, definitions that mean what their names say,
no junk values (division by zero, `sInf ∅`, `⊤`/`ofReal` truncation, `toReal` of `⊤`, integrals of
non-integrable functions, `Measure.map` of non-measurable maps), and not vacuous (hypotheses jointly satisfiable,
no hypothesis contradictory or making the conclusion trivial).

You audit the statements assigned to you in `Challenge.lean` against `cutcur-lean.tex`, reading both yourself,
plus the definitions they use (all in `Challenge.lean`, namespace `CutCur`). The earlier audit of the original 12
theorems is `verification/semantic-audit.md` (use as format template and for the shared definitions it already
analyzed; do not re-audit those). Amendments are already flagged in docstrings (`0 < d`, carrier hypotheses
`IsStdBrownian`/`IsLangevin`, test-function class); judge whether each flagged amendment is necessary and harmless, and
look for UNFLAGGED deviations.
Do NOT read the proofs to decide fidelity (proofs are kernel-checked); read statements and definitions. You may write
scratch Lean files under the scratchpad directory importing `Solution` or `CutoffRigidity.Statements` to test concrete
instances (non-vacuity, e.g. instantiate the hypotheses for an explicit V; check a definition on an example).
Rules: edit no existing file; write only your report file. Report per statement: verdict (faithful / faithful with remarks /
defect), the manuscript lines, a precise list of deviations with severity, and for each suspected defect a concrete
counterexample or failure scenario. Be adversarial but honest: if nothing is wrong, say so. Do not claim human review.
