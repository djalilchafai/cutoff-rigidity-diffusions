# diff-BE-E2: Poincare from gap, LSI from strong Bakry-Emery

Files: `CutoffRigidity/Riemann/DiffLSIFisher.lean` (helpers), `DiffLSIMain.lean` (main). No sorry/axiom in either.
Both build (`lake build CutoffRigidity.Riemann.DiffLSIMain`). `#print axioms` of `lsi_of_strong_BE` shows
sorryAx only through upstream stubs (`inS_semi`, `integral_semi`, `semi_nonneg`-free path, `entFun_hasDerivAt`,
`entFun_continuousOn`, `poincare_of_InS`); `poincare_of_gap` is clean.

Proved: `poincare_of_gap`, `lsi_of_strong_BE` (+ `entFun_zero_le`, `lsi_delta_time_bound`, `fisher_pt`,
`fisher_int`, `grad_decay_pt`, `grad_decay_int`, `cs_int`, `entropy_le_var`, `ent_delta_limit`, `sqf`, ...).
