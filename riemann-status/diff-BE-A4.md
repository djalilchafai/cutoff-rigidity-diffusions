# diff-BE-A4: integrated Bochner on S (hess_integrable_of_InS)

Status: PROVED in CutoffRigidity/Riemann/DiffBEHess.lean (278 lines, no sorry/axiom).
`#print axioms` shows only propext, Classical.choice, Quot.sound (at time of check, DiffBEClass
had A1 `integrable_carre_of_InS` available; the only upstream black box used is A1).
Statement unchanged. Helpers (same file): carre_comm', young4, hess_real, hess_step.
Method: cutoff chi_n, IBP with chi^2 against Gamma w and chi^2 Lw against w, Young with alpha,
Fatou on K = H + rho*Gamma (single Fatou for each alpha in (0,1]), then alpha -> 0.
