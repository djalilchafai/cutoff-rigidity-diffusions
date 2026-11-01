# Audit M (adversarial, statements only) of the nine new Challenge.lean statements

Method: read the Lean statements and definitions in Challenge.lean (lines ~159-165, 328-336, 705-759, 794-877) against cutcur-lean.tex (Lemma 3.3 at L910; eq. expdecI/HI at L1159-1170; Dyson at L285-325; Gamma/Gamma_2/Bochner at L633-663; polarization at L1417). Proofs and worker summaries not read. Nothing compiled. No repo file edited.

## Verdicts

1. isLangevinSolution_map_eq_kernel_of_rigid: NO DEFECT (one REMARK, docstring).
   - Mathematically true. Pathwise uniqueness (Y = X - sqrt2 B solves an ODE with continuous forcing, grad V monotone because Hess V >= rho > 0) makes X_t a.e. equal to a Borel functional of the continuous path of B. Hence X t is AEMeasurable, so P.map (X t) is not the junk value 0. IsStdBrownian forces P to be a probability measure. t = 0 gives a Dirac mass on both sides (Kolmogorov formula at t = 0).
   - Hypotheses are stronger than needed (hR could be reduced to convexity) but consistent. Witness: V = |x|^2/2, rho = 1.
   - REMARK: needs IsEuclideanLangevin, so V is C^infinity, whereas the manuscript uses C^2 (IsLangevin). Unlike the sibling theorems, this docstring does not say "Amendment: V is C^infinity". The flag only appears inside the IsEuclideanLangevin docstring. Suggest adding it. It is a real amendment: the theorem says nothing for C^2 V that is not C^infinity.

2. eigenmap_is_ou_pathwise: NO DEFECT.
   - Uses IsLangevin (V is C^2, no C^infinity needed), so there is no amendment. Matches Lemma 3.3 and its proof (T = Ax+b, rows orthogonal of norm sqrt(rho), A grad V = rho(T-b), beta = A B/sqrt(rho)).
   - Quantifier order is the strong one: one beta for all x0, then "a.s. for all t". It is true for beta = A B / sqrt(rho). Adaptedness of beta is not claimed, but the integral equation determines T(X) pathwise from beta, so the law is the OU law anyway; nothing is lost.
   - No junk: interval integrals are of a.s. continuous paths, and X s.toNNReal is used for s in [0, t]. d = 0 is excluded since RigidCurvature forces gap > 0, which is false for d = 0.
   - Non-vacuous: IsLangevin is satisfiable (exists_langevin), and V = |x|^2/2 gives an eigenbasis.

3. langevin_dissipation_ge_K': NO DEFECT (REMARKS).
   - Ioc (s,t) with r.toNNReal: r > s >= 0, so there is no toNNReal truncation junk.
   - ENNReal: the inequality has the sum on the left, so there is no subtraction or infinity-minus-infinity. The hypothesis klDiv(nu_a) != top with a < s gives klDiv(nu_s) <= klDiv(nu_a) < top.
   - It is the inequality half of expdecI/HI, which is exactly what the manuscript uses (H(t0)-H(t1) >= int I >= (t1-t0) I(t1)).
   - rho is an implicit argument fixed by hrho and hHess. It does not appear in the conclusion, so the statement says "for every rho > 0 with Hess V >= rho". That is equivalent to the existence form, and it is weaker than what de Bruijn needs. Harmless.
   - The lintegral is the lower Lebesgue integral if r -> I is not measurable, but I is monotone under these hypotheses (langevin_fisher_decay), so it is measurable.
   - No 0 < d hypothesis. d = 0 is trivial (everything is 0), so the statement is true there.
   - Satisfiable: nu = mu, V Gaussian.
   - fisherInfo (pre-existing, outside the scope but checked): the integrals in its integration-by-parts line are against Lebesgue measure, so G is the genuine weak gradient of sqrt(h). No problem.

4. langevin_dissipation_dirac_K: NO DEFECT.
   - rho is an implicit argument determined by hrho and hHess, consistent with ge_K'. It is not inferred from the conclusion. Fine.
   - 0 < s < t, and Ioc as above, so there is no junk. If klDiv(P_s x0) = top, the statement is trivial.
   - Faithful to "(recall mu_0 is a Dirac mass)" and eq. HI with t0 > 0.
   - REMARK: the Dirac case is not a corollary of ge_K', because klDiv(delta) = top, which is why it is a separate statement. This is correct.

5. dyson_ou_static (with chamber and dysonProb): NO DEFECT in the statement; REMARKS on the docstring wording about optimality.
   - chamber is {x_1 > ... > x_d}, open and convex. dysonProb restricts to the chamber, so Real.log is only evaluated where x_i - x_j > 0 for i < j; there is no junk (only measure-zero walls). The exponent -(rho/2|x|^2 + sum -beta log(x_i - x_j)) is the right sign (V = rho|x|^2/2 + W, W = sum -beta log). It matches the manuscript's V = rho/2|x|^2 + W.
   - Normalization (m univ)^-1 • m: if Z = 0 or Z = infinity this would be junk, but conjunct 1 asserts IsProbabilityMeasure, which forces 0 < Z < infinity. This is true (Gaussian times polynomial weight with beta >= 0; chamber open and nonempty). So the junk cannot hide.
   - The hypotheses (0 < d, rho > 0, beta >= 0) are all needed. d = 0 makes Var h = 0 and conjunct 8 false. There are no other hypotheses, so no vacuity issue (d = 1, beta = 0 is a standard Gaussian).
   - Each conjunct is true:
     * convexity of -beta log(x_i - x_j) for beta >= 0.
     * L h = -rho h on the chamber (the interaction forces cancel antisymmetrically; generator is local, and V is smooth on the open chamber).
     * Neumann form for ALL bounded smooth Lipschitz phi on R^d: the boundary term vanishes. For beta > 0 the density vanishes on the walls. For beta = 0 it does not, but <(1,...,1), n> = 0 on every wall x_i = x_{i+1}, so it still vanishes. Integrands are integrable (bounded times L^2), so no 0-junk.
     * Poincare with 1/rho: restriction of a rho-log-concave measure to a convex set (Bakry-Emery/Brascamp-Lieb).
     * Var h = d/rho = rho^-1 int |grad h|^2 d(mu), since int |grad h|^2 d(mu) = d.
   - (i) Does "Poincare with 1/rho + Var h = rho^-1 int|grad h|^2" express optimality? Mathematically yes, but not literally as a formal conjunct. h is unbounded, so it is NOT an IsTestFunction. The conclusion "no C < 1/rho works over test functions" needs a one-line truncation argument (psi_n(h) with psi_n smooth, bounded, Lipschitz, equal to the identity on [-n, n]; dominated convergence since h is in L^2 and |grad h| is bounded). The docstring says "so the optimal Poincare constant over bounded smooth Lipschitz test functions is 1/rho, with h extremal". This is accurate as a mathematical consequence, but "extremal" is only in the closure sense (h is not itself a test function), and the step is not part of the Lean statement. REMARK, not a defect. Optional tightening: add a sInf-free conjunct such as `forall C < rho^-1, exists f, IsTestFunction f /\ not (variance f mu <= C * int |grad f|^2 dmu)`.
   - No "lambda_1 = rho" over-claim: the docstring explicitly says the identification with the spectral gap and the Dyson-OU process are not claimed. spectralGap/gibbs cannot be used here because V = +infinity off the chamber. So the statement is strictly weaker than the manuscript's "lambda_1 = rho and x_1+...+x_d in E_1" (honestly flagged). In particular, lambda_1 <= rho (from the extremal h) is not stated either, and lambda_1 >= rho would need Neumann spectral theory.

6. carre_eq_operator: NO DEFECT.
   - Gamma(f,g) = <grad f, grad g> equals (L(fg) - fLg - gLf)/2 for any V, because the V-terms cancel via the product rule for mgrad (needs only differentiability of f, g at x). Matches the manuscript's definition of Gamma (L633). The mlaplacian product rule is true for the genuine Levi-Civita connection on smooth fields (f, g smooth, metric smooth by the instance).
   - "No hypothesis on V" is correct and harmless. This is the link that makes carre (inner product) coincide with the manuscript's operator Gamma.

7. carre_polarization: NO DEFECT (a REMARK on scope).
   - Trivial (bilinearity of inner and linearity of mgrad at x). Hypotheses are needed only for differentiability. The manuscript's polarization concerns the operator-defined Gamma (L1417); combined with carre_eq_operator the two readings agree. Taken alone, this theorem is about the inner-product carre, a weaker content than the manuscript's, but together with carre_eq_operator it is faithful.

8. generator_comp: NO DEFECT.
   - L(theta o f) = theta'(f) Lf + theta''(f) Gamma(f), with deriv (deriv theta) at f x. True with the Lean definitions for smooth f and arbitrary V (the V term is linear in grad(theta o f) = theta'(f) grad f). Scalar chain rule only. The manuscript's Lemma 3.3 proof uses the multivariate "diffusion property" L(g o T), which is NOT covered. Remark only, since the statement is the scalar one and is labelled so.

9. bochner_vector (with mSecondDeriv, mRoughLaplacian, mVecGenerator): NO DEFECT in sign/slot conventions; REMARK on the frame definition.
   - Verified by hand. d(Lf)(v) = <L_vec grad f, v> - Hess V(grad f, v) - Ric(grad f, v), with L_vec u = tr nabla^2 u - nabla_{grad V} u. The two Hess f(grad V, v) terms cancel by symmetry of Hess f, and the Weitzenboeck identity gives the -Ric term. This is the correct vector-form Bochner formula. The manuscript's printed form "Hess(V) nabla - Ric(nabla, nabla)" is only schematic, and the Lean version is the precise one.
   - Slot: Lean has mRic x v (grad f); the docstring says Ric(v, grad f); the sibling bochner_identity uses the symmetric form. mRic (v,w) = sum <R(e_i, v)w, e_i> with R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z - nabla_[X,Y] Z is positive on spheres and symmetric in the genuine geometry (the Lean definition does not have symmetry built in, so v/w slot order is a matter of the theorem, not of the definition; since Ric is symmetric, either order is true).
   - mSecondDeriv u X Y = nabla_X nabla_Y u - nabla_{nabla_X Y} u: argument order verified (X outer, Y inner).
   - mRoughLaplacian frame issue: it is computed with chart-constant extensions mExt of the orthonormal frame at x. The value is frame- and extension-independent mathematically (nabla^2 is tensorial; the sum over e_i of nabla^2_{E_i,E_i} depends only on E_i(x) = e_i), and the docstring states honestly that this independence is not asserted. Since the theorem is a statement about this particular expression, its truth depends on tensoriality of nabla^2 and locality of Mathlib's leviCivitaConnection (true mathematically). mRic and mHessSq already use the same device. REMARK only. No junk from mExt outside the chart source (derivatives are local at x).
   - Hypotheses hV, hf: smooth, as in the manuscript, and needed for differentiability of Lf.
   - Non-vacuity of the Riemannian block: flat R^d (instance taken as argument in temperature_cd) is a witness; Ricci is 0 there, so the Ric term is only exercised in the sphere-type case, which no witness here exercises.

## Summary
No defect in any of the nine. Remarks: (1) add "Amendment: V is C^infinity" to the docstring of isLangevinSolution_map_eq_kernel_of_rigid; (2) dyson_ou_static: the optimality statement in the docstring is a mathematical consequence needing a truncation argument, h is not a test function, and the strict statement could be tightened with an sInf-free conjunct; the lambda_1 = rho identification is correctly not claimed; (3) bochner_vector: frame independence of mRoughLaplacian is by tensoriality, not asserted (honestly documented); (4) the dissipation theorems carry unused-but-harmless rho hypotheses.
