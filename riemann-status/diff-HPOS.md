# diff-HPOS: gap attainment from LSI (workstream HPOS) -- DONE

Namespace `CutoffRigidity.Riemann.Diff`. LSI is the only external input. Final module: `CutoffRigidity.Riemann.DiffGapAttained2`
(imports all others). `#print axioms gap_attained_of_LSI` = [propext, Classical.choice, Quot.sound]. No sorry/axiom/native_decide.

**Main theorem** (DiffGapAttained2): `gap_attained_of_LSI F hV hμ hρ hCD hgap (hLSI : LSI F V μ ρ) : 0 < mFirstEigenDim F μ V`
(hCD is included: needed by `mFirstEigenDim_pos_iff` for finite dimensionality of the eigenspace).

| file | lines | content |
|---|---|---|
| DiffTight | 265 | `entL`, `LSI F V μ ρ` (test functions), `gibbs_var` (entropy ineq.), `LSI.entropy_form`, `tail_of_LSI` |
| DiffRellichRn | 279 | `c1_translation_F`, `rellich_criterion_F` (Kolmogorov-Riesz in F) |
| DiffRellichChart, 1, 2 | 182+109+201 | `chart_local_totallyBounded` (local Rellich in a chart) |
| DiffRellich | 323 | gluing, `mulBall_totallyBounded`, `ball_totallyBounded_of_tail`, `Qball_totallyBounded_of_tail` |
| DiffGapHilbert, DiffGapManifold, DiffGapAttained | 256+130+227 | Poincare on Q, lsc, Euler-Lagrange, eigenfunction identification, `gap_attained_of_compact` |
| DiffGapAttained2 | 47 | `gap_attained_of_LSI` |

Notes: LSI imposed only on test functions; no extension to Q is needed (tightness for the D-ball, Q-ball by density through `E_lim`).
Lead: add `DiffGapAttained2` to CutoffRigidity.lean.
