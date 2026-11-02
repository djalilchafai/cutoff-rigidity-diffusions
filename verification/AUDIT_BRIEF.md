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

## Pending AI audit (added 1 November 2026, round 2)

No AI audit has been run on the following statements and definitions yet (the worker/adversary reports in `extra-status/` are not audits of the integrated text). Suggested report name: `audit-extra-N.md`.
- Changed statements: the `C²` clause of `IsEuclideanLangevin`, `IsSigmaLangevin` and of `W n` in `convex_interaction_cutoff` (23 statements; check that each carries a convexity hypothesis and that none silently loses strength);
  the equality statements `langevin_dissipation_eq_K'`, `langevin_dissipation_eq_dirac_K` (replacing the `≥` versions).
- New statements: `dyson_spectralGap` (`dysonGap`); `gaussian_isoperimetric_functional`, `gaussian_isoperimetric_sets`, `gibbs_quadratic_isProb` (`gaussianIsoProfile`; QUADRATIC potential only);
  `rothaus_alternative_ne`, `two_optPI_le_optLSI`, `finite_rothaus` (`Form`, `Form.optPI`, `Form.optLSI`, `Form.Compact`; abstract/finite only); `temperature_kernel`; `sphere_curvature`, `sphere_gap` (`IsSphereModel`; model form).
- Points to examine: junk values of `sInf` in `Form.optPI/optLSI`, `dysonGap`, `gaussianIsoProfile`; that `Form.Compact` is not contradictory (satisfied by finite forms in `Extra/Rothaus15`);
  that `finite_rothaus` quantifying over any `Form` with `Q = univ` and the Dirichlet energy is equivalent to the statement for the canonical form; that `IsSphereModel` pulls back exactly the Riemannian inner product (compare `Extra/Item6a`, `Sphere5/6`).
