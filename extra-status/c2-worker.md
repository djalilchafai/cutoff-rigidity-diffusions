# c2-worker: removing the C^infty restriction from the kernel statements

Verdict: PARTIAL. Genuine obstruction for general C^2 `V`; only the OU statements (where it is vacuous) and a
conditional reduction are delivered. No human review. File: `CutoffRigidity/Extra/C2Langevin.lean`
(`lake build CutoffRigidity.Extra.C2Langevin` OK; axioms of all theorems below: propext, Classical.choice, Quot.sound).

## Delivered (Lean)
```lean
def IsEuclideanLangevinC2 (V) (Pt) : Prop := ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs V) ∧ IsEuclideanDiffusion V Pt
def C2Uniqueness (V) : Prop := ∀ P₁ P₂, IsEuclideanDiffusion V P₁ → IsEuclideanDiffusion V P₂ → ∀ t x, P₁ t x = P₂ t x
theorem IsEuclideanLangevin.toC2 ; IsEuclideanLangevinC2.toSmooth (hV : ContDiff ℝ ∞ V)
theorem c2Uniqueness_of_smooth (hV : ContDiff ℝ ∞ V) (hp) : C2Uniqueness V
theorem isEuclideanLangevinC2_quadratic_iff : IsEuclideanLangevinC2 (fun x => ρ/2*‖x‖^2 + c) Pt ↔ IsEuclideanLangevin (same) Pt
theorem exists_isLangevin_of_C2 (hL : IsEuclideanLangevinC2 V Pt) (hU : C2Uniqueness V) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
  ∃ Ω _ B P X, IsProbabilityMeasure P ∧ IsLangevin V B P X ∧ ∀ t x₀, P.map (X x₀ t) = Pt t x₀      -- conditional on hU
-- unconditional (namespace CutoffRigidity.Paper): ou_fisher_information_C2, ou_mean_start_cutoff_C2, ou_lp_infty_fails_C2
-- conditional on C2Uniqueness: langevin_fisher_decay_C2_of_unique (template; the other general statements follow identically)
```
The 3 OU statements: the `C^infty` clause of `IsEuclideanLangevin` is automatic for `ρ/2|x|²+c`, so nothing was ever
restricted there (the Challenge statements can simply take `IsEuclideanLangevinC2`, or even drop the ContDiff clause).
Likewise `convex_interaction_cutoff` already assumes `W n` is C^infty separately in `hW`; its restriction is in `hW`, not in
`IsEuclideanLangevin`.

## Not recovered (the 18 statements with general V): the exact obstruction
All need `Pt = law of the Langevin solution`, i.e. uniqueness of Markov semigroups solving the forward Kolmogorov equation
`P_t f = f + ∫ P_s L f` for f ∈ C_c^∞, with drift ∇V only C^1 (V ∈ C^2). Why each route fails inside the current library:
* Smooth proof (`bridge_final`/`bridge_of_minimal`, Perron + `MinimalResolvent`, `DiffEllipticRn*`, `DiffKer*`): needs the resolvent
  solution u of λu - Lu = g to be C^2 (to build compactly supported smooth sub-solutions f with λf - Lf ≤ g). With C^1 drift the
  library's Sobolev regularity (`weak_solution_smooth`, `global_regularity`: H^{m+2} needs coefficients C^{m+1}) gives only H^3_loc, and
  H^3 ⊂ C^2 only for d = 1. Schauder / W^{2,p} theory (C^{2,α} regularity for C^{0,1} drift) is not in Mathlib or the project.
* Approximation by smooth convex `V_ε` (mollification exists: `NoBmMollify`): does not by itself identify an arbitrary `Pt` for `V`; it
  needs a comparison `U^P_λ g = lim U^{Q^ε}_λ g`. Sketch that would work: f_ε = U^{Q^ε}_λ g (smooth), λ f_ε - L_V f_ε = g + (∇V_ε-∇V)·∇f_ε,
  with |∇f_ε| ≤ ‖∇g‖/λ-type bounds from Bakry-Emery (Hess V_ε ≥ 0); then Dynkin for P applied to a radial cutoff χ_R f_ε
  (one-sided control of L χ_R by convexity, x·(∇V(x)-∇V(0)) ≥ 0) and the mass trick of `bridge_of_minimal`. Missing pieces, none in the library:
  uniform-in-ε gradient bound for the canonical kernel `Kk`; local-uniform convergence + tightness of P_s (Lyapunov |x|²) ; signed/cutoff
  bookkeeping ; a C^2-V version of `bridge_of_minimal` (it uses `MSmooth` only for `msmooth_mgenerator`, probably continuity of L f suffices).
  Size estimate: 3000-6000 lines of Lean, medium-high risk, several agent-weeks.
* Probabilistic route (superposition principle -> martingale problem -> weak solution -> pathwise uniqueness for monotone drift,
  then `exists_langevin`): superposition principle, martingale-representation/Ito for the canonical process are absent from Mathlib: larger.
* Duality with mollified Q_t g (commutator [∇V·∇, ρ_ε*] = O(ε) since ∇V is locally Lipschitz): needs the weak backward equation for
  `Q_t g` and symmetry/invariance of the project's `langevinKernel` for C^2 V, not available outside the smooth Riemannian identification.

## What could still be recovered cheaply
* The OU statements (done). Everything under the explicit hypothesis `C2Uniqueness V` (conditional; each of the 18 reduces to the
  carrier theorem exactly as `langevin_fisher_decay_C2_of_unique`, via `exists_isLangevin_of_C2`; sequence statements via the pattern of
  `exists_carriers_of_K`). I did not write the other 17 conditional copies because a conditional statement does not discharge the item.
* Note that the C_c^∞ test class could be replaced by C_c^2 in `IsEuclideanDiffusion` (equivalent by mollification and dominated convergence)
  but this does not help uniqueness.

## Adversary verdict (see c2-adversary.md)
No repair needed. The three `_C2` OU theorems are restatements of the Challenge OU statements (the C^infty clause is automatic for
the quadratic potential), not recoveries; they are not added to Challenge.lean. The 18 general-V statements stay blocked on C^2
uniqueness of the diffusion semigroup (estimated 2500-6000 lines, medium-high risk; no cheaper route found).
