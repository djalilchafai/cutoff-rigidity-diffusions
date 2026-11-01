# Item 2 adversary report (Item2a.lean, Item2b.lean)

Recompiled: `lake build CutoffRigidity.Extra.Item2a CutoffRigidity.Extra.Item2b` succeeds (warnings only come from
existing files). No `sorry`/`axiom`/`native_decide`/`#print` in either file. `#print axioms` (scratch file outside the repo)
on all 9 Item2a theorems and on mExt_eventually_frm, mSecondDeriv_mExt_eq, curv_swap, bochner_vector: only
propext, Classical.choice, Quot.sound.

## Item2a: ACCEPT (one cosmetic repair before Challenge insertion)
- `mgenerator F V f = mlaplacian f - <grad V, grad f>` (Statements.lean): correct sign, matches L = Delta - grad V . grad.
- carre_eq_operator: Gamma(f,g)=(L(fg)-fLg-gLf)/2 exactly the manuscript (L633-636), no hypothesis on V (correct: the drift
  term is first order), only smoothness of f,g (manuscript: smooth). Not vacuous: the standing instances are satisfiable
  (R^k with the Euclidean metric; the project already instantiates them in temperature_cd).
- generator_mul, carre_mul_left'/right, carre_symm, carre_comp_left', carre_polarization (matches the polarization used at
  L1417), generator_comp (chain rule L(theta o f) = theta'(f)Lf + theta''(f)Gamma(f)): all correct statements; hypotheses are
  the natural ones (theta ContDiff infinity, f smooth).
- carre2Bil / carre2Bil_self: definition matches Gamma_2(f,g) (L633-637); the diagonal lemma is trivial but correct. NOT
  proved: the polarized Bochner formula for Gamma_2(f,g) (only the diagonal bochner_identity exists). Do not claim it.
- Cosmetic: `[MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]` are included in every theorem signature
  (variable-inclusion) although unused. Harmless (satisfiable, and Statements.lean carries the F ones too), but drop the
  M ones (and ideally F ones) when moving to Challenge, since the Challenge Riemannian section has no MeasurableSpace M.

## Item2b: ACCEPT
Independent derivation of the statement: Bochner gives d(Delta f) = <Delta_rough grad f, .> - Ric(grad f, .)
(from 1/2 Delta|grad f|^2 = |Hess f|^2 + <grad f, Delta_rough grad f> and the scalar Bochner formula). Further,
-d<grad V, grad f>(v) = -Hess V(v, grad f) - Hess f(v, grad V), and Hess f(v, grad V) = <nabla_{grad V} grad f, v> by symmetry
of Hess. Hence d(Lf)(v) = <L_vec grad f, v> - Hess V(grad f, v) - Ric(v, grad f), with L_vec = Delta_rough - nabla_{grad V}.
This is exactly `bochner_vector` (signs and slot orders right). Flat check R^k, V = rho|x|^2/2: Hess V = rho I, Ric = 0,
giving d(Lf)(v) = <L grad f, v> - rho <grad f, v>, which is the right commutation [grad, L] = -rho grad for OU.
- The manuscript's printed "Ric(nabla,nabla)" is a typographical shorthand; the worker's Ric(v, grad f) is the correct
  reading. mRic is symmetric mathematically (curvature symmetries) so the slot order is immaterial, and the theorem fixes it
  anyway, so nothing is weakened.
- mRoughLaplacian with chart-constant frame mExt: nabla^2_{X,Y}u = nabla_X nabla_Y u - nabla_{nabla_X Y}u is tensorial in X,Y,
  so with X=Y=E the value depends only on E(x)=e_i and the sum over an orthonormal basis is the trace; the covariant-derivative
  correction term in mSecondDeriv accounts for nabla_E E(x) != 0. The caveat therefore does not make the statement
  meaningless. The docstring remark "the value is frame independent" is NOT proved in the file (mSecondDeriv_mExt_eq only
  equates it with the frm-frame value); it is a true mathematical fact but should be worded "is" -> "(mathematically) is" or
  proved if the definition goes into Challenge. mVecGenerator = rough Laplacian - nabla_{grad V}: faithful Langevin
  operator on vector fields. Hypotheses: V, f smooth only (as manuscript).
- Non-vacuity: instances as for Item2a; the conclusion has a nontrivial left-hand side (mvfderiv of Lf).

## Placement / size
- Item2b imports Extra.RicciBochner (already part of CutoffRigidity.lean); nothing imports Item2a/b, so no cycle. Challenge.lean
  imports only Mathlib, so Challenge entries must be statement-only with their definitions in Challenge; Statements.lean is
  generated from it by scripts/sync-statements.py and the proofs live in Solution.
- Estimated Challenge growth (981 lines now): definitions mSecondDeriv, mRoughLaplacian, mVecGenerator about 22 lines with
  docstrings; bochner_vector about 8; carre_eq_operator about 6, carre_polarization about 6, generator_comp about 6.
  Total about 50 lines for the recommended set, about 90 if all helpers are included.

## Which theorem deserves a Challenge entry
- Challenge (faithful manuscript claims): carre_eq_operator (Gamma definition = |grad f|^2), bochner_vector (L633-654
  vector Bochner), carre_polarization (L1417 use), generator_comp (chain rule, optional; manuscript uses it implicitly in
  the log/power computations).
- Helpers only: generator_mul, carre_mul_left', carre_mul_right, carre_symm, carre_comp_left', carre2Bil (def) and
  carre2Bil_self, mExt_eventually_frm, mSecondDeriv_mExt_eq, curv_swap.
