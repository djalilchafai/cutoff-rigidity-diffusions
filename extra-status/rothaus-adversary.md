# R6 Rothaus remark: adversary report

Verdict: ACCEPT (as abstract Dirichlet-form statement plus finite spaces only, with an honest scope docstring).

## Checks
1. `lake build CutoffRigidity.Extra.Rothaus` succeeds. `#print axioms` for rothaus_alternative, two_optPI_le_optLSI,
   rothaus_alternative_ne, rothaus_alternative_sobolev(_ne), finite_rothaus, twoPoint_rothaus: only propext, Classical.choice,
   Quot.sound. No sorry/axiom/native_decide/#print in Rothaus*.lean.
2. Faithfulness. optPI/optLSI use the same normalization as CutCur.optimalPI/optimalLSI (Var <= C*E, Ent(f^2) <= C*E, E = int |grad f|^2),
   so the OU values are 1 and 2 and the threshold "optLSI = 2 optPI" is correct. Junk values: sInf of empty set = 0 is neutralized
   (hgt: 2 optPI < optLSI forces optLSI > 0 and the LSI set non-empty; the _ne versions assume hLSI explicitly). Q empty / {0} / constants gives
   optPI = optLSI = 0, so hgt fails (no vacuous truth from degenerate Q). Conclusion is a genuine extremal: f in Q, 0 < E f, Ent(f^2) = optLSI * E f
   with optLSI > 0 (so entropy > 0, f nonconstant). Integrability is part of Form (memLp 2, integrable Theta = f^2 log(1+f^2)); entropyOf is well
   defined on Q (integrable_flog). Form needs scaling and constant-shift invariance of E only.
3. Satisfiability. Compact needs Q to be the full (complete) form domain (a Q of smooth functions would make Compact false); on a
   compact manifold H^1 satisfies Rellich, Sobolev (L^{2+delta}) and L^2 log L integrability. Witnesses: finite_compact proves Compact for
   every irreducible finite form with full support (no assumption of the conclusion; hgt is the Rothaus premise). Two-point: mu{true}=p=e^{-3},
   E=p(1-p)(f t - f f)^2 = Var, so optPI <= 1 (indeed =1); f=1_true gives Ent(f^2) = -p log p = 3p, E = p(1-p), ratio 3/(1-p) >= 3; the proof of
   3 <= optLSI is by the test function and is correct. So 2 optPI <= 2 < 3 <= optLSI. Recomputed independently.
4. Scope. NOT the compact-manifold statement. The manuscript says "compact setting ... extremal function exists" (cites Rothaus 1981 and
   Saloff-Coste Th. 2.2.3 for the discrete one). Formalised: (a) abstract form under hypothesis Form.Compact (or Rellich + Sobolev), (b) the discrete
   version, (c) a concrete non-vacuous instance. Missing: instantiation for a compact weighted Riemannian manifold (Sobolev embedding H^1 in L^{2+delta},
   Rellich, density of smooth functions so that optima over H^1 equal optima over test functions, and automatic PI/LSI). Extra hypotheses vs manuscript:
   hPI (and hLSI in the _ne versions) which are automatic on compact manifolds.

## Required docstring for the Challenge
State: abstract form (Q,E) on a probability space, Compact/Rellich+Sobolev as hypotheses; discrete case unconditional; the manifold case is NOT proved.

## Suggested Challenge text (sketch)
-- Docstring: "Rothaus alternative, abstract form. (Q,E) is a Dirichlet-type form on a probability space (Q closed under scaling/constants, E >= 0
-- quadratic, Q in L^2 with f^2 log(1+f^2) integrable); `Compact`: energy balls of mean-zero functions are sequentially compact in L^2 and in the
-- Orlicz weight, with lsc energy. NOT the compact-manifold theorem (the instantiation H^1 of a compact manifold is not formalised)."
theorem rothaus_alternative (F : Form mu) (hPI : exists P, 0 <= P /\ forall f in F.Q, variance f mu <= P * F.E f) (hcomp : F.Compact)
  (hgt : 2 * F.optPI < F.optLSI) : exists f in F.Q, 0 < F.E f /\ entropyOf mu (fun x => f x ^ 2) = F.optLSI * F.E f
theorem two_optPI_le_optLSI (F) (hLSI : exists c, 0 <= c /\ forall f in F.Q, Ent(f^2) <= c * F.E f) : 2 * F.optPI <= F.optLSI
theorem finite_rothaus (finite space, weights w >= 0, full support, connected, hgt) : exists f, 0 < E f /\ Ent(f^2) = optLSI * E f
-- (optionally twoPoint_rothaus as non-vacuity witness.) Compressing: the Form structure (9 fields), Compact, optPI, optLSI definitions needed (~25 lines).

Recommendation: Challenge should carry rothaus_alternative_ne (manuscript form) or rothaus_alternative, finite_rothaus, and the scope docstring above.
