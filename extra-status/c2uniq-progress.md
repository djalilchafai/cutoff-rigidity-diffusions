# R4: C2Uniqueness for convex C^2 potentials -- plan and progress

(Worker for round 2, item R4. Files: CutoffRigidity/Extra/C2Uniq*.lean. No human review.)

## Mathematical route chosen (resolvent / ODE-in-tau, no Fubini, no Schauder)

Setting: V in C^2 with <y, grad V(y) - grad V(0)> >= 0 (convexity), P an `IsEuclideanDiffusion V` semigroup, lam > 0, x fixed.
`U g := int_0^infty e^{-lam s} (P_s g)(x) ds` (resolvent of P at x).

* P-side (flat space, V in C^1 enough): s -> P_s f(x) Lipschitz for f in C_c^infty (Dynkin + semigroup + Markov);
  hence for every continuous compactly supported h, s -> P_s h(x) continuous (uniform approximation by C_c^infty);
  resolvent form of Dynkin: U((lam - L)f) = f(x) for f in C_c^infty.  (No MSmooth V needed; `Lf` is only C^1.)
* Smooth approximants W_n = molc_n V + (1/(n+1)) |x|^2/2 + const: smooth, Hess >= 1/(n+1) > 0, probability Gibbs measure,
  grad W_n -> grad V locally uniformly.  Library kernel `Diff.Kk (Rd d) hW hmu` gives for g in C_c^infty, g >= 0:
  w^n_tau = Kk^n_tau g smooth in y, 0 <= w <= sup g, |grad w_tau| <= sup |grad g| (beStrong_of_CD), d/dtau w_tau(y) = L_{W_n} w_tau (y), w_0 = g.
* Core inequality (ODE in tau): for f_tau = chi_R * w_tau in C_c^infty, Phi(tau) = U(chi_R w_tau); resolvent identity gives
  Phi' = lam Phi - chi_R(x) w_tau(x) - U(E_tau) with E_tau >= -Err (one-sided cutoff control thanks to convexity, w >= 0),
  hence  chi_R(x) r_n(x) <= U(chi_R g) + Err_{n,R}/lam^2, r_n(x) = int_0^infty e^{-lam tau} w^n_tau(x) dtau.
  Applying it to g and to c - g (mass trick via Markov: U(chi_R) <= 1/lam) gives |r_n(x) - U g(x)| <= Err_{n,R}/lam^2, so U g(x) = lim_n r_n(x),
  which does not depend on P.  Then Laplace uniqueness (`laplace_unique`, existing) gives P_t g(x) = P'_t g(x), and the kernels agree
  (`measure_eq_of_integral_smooth`, existing).
* Hypotheses actually needed: V in C^2 (C^1 for the P-side, C^2 for the Hessian of mollifications), convexity Hess V >= 0. The Gibbs measure of V
  need NOT be finite for uniqueness.

## Stages (statements recorded below as they get proved)
S1  C2Uniq1.lean  P-side: Lipschitz/continuity, C_c extension, resolvent Dynkin identity (flat space, V in C^1).
S2  C2Uniq2.lean  mollified convex potentials W_n (smooth, strongly convex, prob. Gibbs, grad -> grad V locally uniformly).
S3  C2Uniq3.lean  smooth-side package: w^n_tau from `Kk`, properties (smooth, bounds, gradient bound, tau-derivative).
S4  C2Uniq4.lean  cutoffs chi_R and core inequality.
S5  C2Uniq5.lean  limits, `C2Uniqueness V` for convex C^2 V, existence, substitution results.

## State (updated after stage 6)

S1-S6 DONE, all compiled (`lake build CutoffRigidity.Extra.C2Uniq7`), no sorry, axioms propext/Classical.choice/Quot.sound only
(checked with `#print axioms` for `c2Unique_of_convex`, `euclideanDiffusion_unique_convex`, `core_upper`, `exists_backward`).

Files (all `namespace CutCur.C2U`, `@[expose] public section`):
* C2Uniq1.lean  P-side: `resU`, `continuous_semi_smooth`, `continuous_semi_cs` (C_c continuous test functions), `hasDerivAt_semi`,
  `resU_dynkin : resU P lam (fun y => lam * f y - generator V f y) x = f x` (V in C^1).
* C2Uniq2.lean  `Wm V n x = (1/(n+1))/2 ‖x‖² + molc n V x`; `Wm_contDiff`, `Wm_hess` (Hess >= 1/(n+1)), `isFiniteMeasure_gibbs_Wm`,
  `fderiv_molc`, `Wm_grad_close : ∃ N, ∀ n ≥ N, ∀ x, ‖x‖ ≤ R → ‖gradient (Wm V n) x - gradient V x‖ ≤ δ`.
* C2Uniq3.lean  `IsBackward W g w K G C` (structure), `exists_backward` (library `Diff.Kk` of `Wm V n`: smooth, 0<=w<=K, ‖∇w‖<=G uniform in n by
  Bakry-Emery `beStrong_of_CD`, d/dtau w = L_W w), `IsBackward.const_sub`.
* C2Uniq4.lean  radial cutoffs `exists_cutoff` (support radius 2R, ‖∇χ‖<=A/R, |Δχ|<=A/R², ⟨∇V,∇χ⟩<=A/R from ⟨∇V(y),y⟩>=-a‖y‖), `laplacian_cutc`.
* C2Uniq5.lean  `generator_mul`, `resU_add/smul/ge/le`, `hasDerivAt_resU_w`, `continuous_resU_w`, `core_upper` (ODE-in-tau inequality).
* C2Uniq6.lean  `resU_close` (two-sided), `inner_gradient_monotone`, `resU_eq_of_nonneg`, `resU_eq`.
* C2Uniq7.lean  `euclideanDiffusion_unique_convex`, `C2Unique`, `c2Unique_of_convex`.

Key final statements (exact Lean):
```lean
theorem euclideanDiffusion_unique_convex {P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V)
    (h₁ : IsEuclideanDiffusion V P₁) (h₂ : IsEuclideanDiffusion V P₂) (t : ℝ≥0) (x : Rd d) : P₁ t x = P₂ t x
def C2Unique (V) : Prop := ∀ P₁ P₂, IsEuclideanDiffusion V P₁ → IsEuclideanDiffusion V P₂ → ∀ t x, P₁ t x = P₂ t x
theorem c2Unique_of_convex (hV : ContDiff ℝ 2 V) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) : C2Unique V
```
No hypothesis on the Gibbs measure is needed for uniqueness.
Note: `C2Uniqueness`/`IsEuclideanLangevinC2` of C2Langevin.lean are not `@[expose]`d (module system) so their bodies cannot be unfolded by importers;
`C2Unique` is the same statement, restated.

## S5 DONE: C^2 transfer lemmas and C^2 kernel statements (all compile, axioms propext/Classical.choice/Quot.sound)

C2Uniq8.lean (namespace CutCur.C2U): own predicates (the `C2Langevin.lean` ones are not exposed, so restated)
```lean
def IsEucLangevin2 (V) (Pt) : Prop := ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs V) ∧ IsEuclideanDiffusion V Pt
def IsRigidSeqK2 (V) (Pt) : Prop := (∀ n, 0 < n → IsEucLangevin2 (V n) (Pt n) ∧ RigidCurvature (V n)) ∧ 0 < liminf (fun n => ENNReal.ofReal (spectralGap (V n))) atTop
theorem exists_isLangevin_of_C2 (hL : IsEucLangevin2 V Pt) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
  ∃ Ω _ B P X, IsProbabilityMeasure P ∧ IsLangevin V B P X ∧ ∀ t x₀, P.map (X x₀ t) = Pt t x₀      -- UNCONDITIONAL
theorem exists_isLangevin_of_rigid_C2, exists_isRigidSequence_of_K2, exists_langevinSeq_of_K2   -- same, sequences / rigid
theorem exists_euclideanLangevin_C2 (hV : ContDiff ℝ 2 V) (hHess) (hp : IsProbabilityMeasure (gibbs V)) : ∃ Pt, IsEucLangevin2 V Pt
```
C2Uniq9.lean (namespace CutoffRigidity.Paper, proofs = those of the `_K` versions with the transfer lemmas replaced):
main_wasserstein_estimate_C2, wasserstein_cutoff_C2, langevin_w2_contraction_C2, langevin_entropy_decay_C2, langevin_fisher_decay_C2,
langevin_fisher_dini_C2, information_cutoff_C2, lp_cutoff_C2, convex_interaction_cutoff_C2 (here also `W n` only C^2),
product_condition_cutoff_C2, mixing_time_rigid_C2, mixing_time_w2_rigid_C2, mixing_time_kl_rigid_C2, wasserstein_cutoff_weak_C2,
information_cutoff_weak_C2.
C2Uniq10.lean (CutoffRigidity.Dissip): langevin_dissipation_ge_C2, langevin_dissipation_core_C2, langevin_dissipation_ge_C2', langevin_dissipation_dirac_C2.
C2Uniq11.lean (CutoffRigidity.Paper): eigenmap_is_ou_C2, isLangevinSolution_map_eq_kernel_C2, isLangevinSolution_map_eq_kernel_of_rigid_C2.
C2Uniq12.lean (CutoffRigidity.DissipEq; imports the still untracked DissipEq5): langevin_dissipation_eq_C2, langevin_dissipation_eq_C2', langevin_dissipation_eq_dirac_C2.

OU statements (`ou_*`): nothing to do, the C^infty clause is automatic for rho/2|x|^2+c.
Not ported (not needed or out of scope): `normalization_cutoff_K`, `temperature_cutoff_K` and `Sigma.lean` use `IsSigmaLangevin` (its own `ContDiff ℝ ∞ V` clause);
the same transfer works after the time change `isEuclideanLangevin_of_sigma` (not done).

## Integration recipe for the lead
Preferred: change the smoothness clause of `IsEuclideanLangevin` (Challenge/Statements) from `ContDiff ℝ ∞ V` to `ContDiff ℝ 2 V` (and of `IsRigidSequenceK` through it);
then every `_K` statement keeps its text and its proof only needs: `isEuclideanDiffusion_unique`/`isEuclideanDiffusion_eq_langevinKernel`/`exists_isLangevin_of_isEuclideanLangevin`/
`exists_isLangevin_of_rigid`/`exists_isRigidSequence_of_K`/`exists_langevinSeq_of_K`/`exists_euclideanLangevin` replaced by the `C2Uniq8` versions (they take the same
arguments with `IsEucLangevin2`); remaining `hL.1.of_le` uses are fine, `hL.1` used as `C^∞` (SdeId1, FisherDecayGeneral, MixingTimeW2KL) only feed lemmas that need `C²`.
Convexity is the only extra hypothesis of the C^2 uniqueness (Hess V >= 0, already present in every statement through `hHess`/`RigidCurvature`).
