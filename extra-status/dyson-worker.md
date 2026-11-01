# dyson-worker: static Dyson--OU statement on the Weyl chamber (manuscript L315-335)

Verdict: DONE for the static statement (about 1400 lines, no sorry; axioms of the headline theorem: propext, Classical.choice, Quot.sound).
No human review is claimed. Process-level statement NOT attempted (out of scope).
Files (all new, imported by nothing existing): `CutoffRigidity/Extra/Dyson.lean`, `Dyson1D.lean`, `Dyson2.lean` ... `Dyson7.lean`.
Build: `lake build CutoffRigidity.Extra.Dyson7` (OK, no errors).

## Normalization (as in the manuscript, nothing silently changed)
`V(x) = (rho/2)|x|^2 + sum_{i<j} h(x_i-x_j)`, `h = -beta log` on `(0,inf)`, `+inf` otherwise, `beta >= 0`, `rho > 0`; no 1/d scaling.
`chamber d = {x | forall i j, i<j -> x j < x i}`; `dysonV d rho beta x = rho/2*|x|^2 + sum_i sum_{j>i} (-beta*log(x i - x j))`
(values off the chamber are junk and never used); `dysonMeasure d rho beta = (volume.restrict (chamber d)).withDensity (ofReal (exp (-dysonV x)))`
(this is how "V = +inf outside" is encoded); `dysonProb = (mu univ)^{-1} • mu`.

## Headline theorem (Dyson7.lean), exact Lean text
```lean
noncomputable def optimalPIDyson (d : ℕ) (ρ β : ℝ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ f : CutCur.Rd d → ℝ, CutCur.IsTestFunction f →
    variance f (dysonProb d ρ β) ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β}

theorem dyson_ou_static (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    let μ := dysonMeasure d ρ β
    let μ' := dysonProb d ρ β
    let h := fun x : CutCur.Rd d => ∑ i, x i
    (IsFiniteMeasure μ ∧ 0 < μ Set.univ ∧ IsProbabilityMeasure μ') ∧
    (IsOpen (chamber d) ∧ Convex ℝ (chamber d) ∧
      ConvexOn ℝ (chamber d) fun x => dysonV d ρ β x - ρ / 2 * ‖x‖ ^ 2) ∧
    (∀ x ∈ chamber d, CutCur.generator (dysonV d ρ β) h x = -ρ * h x) ∧
    (∀ φ : CutCur.Rd d → ℝ, CutCur.IsTestFunction φ →
      ∫ x, inner ℝ (gradient h x) (gradient φ x) ∂μ' = ρ * ∫ x, h x * φ x ∂μ') ∧
    (∀ f : CutCur.Rd d → ℝ, CutCur.IsTestFunction f →
      variance f μ' ≤ ρ⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂μ') ∧
    (optimalPIDyson d ρ β = ρ⁻¹ ∧ MemLp h 2 μ' ∧ 0 < variance h μ' ∧
      variance h μ' = optimalPIDyson d ρ β * ∫ x, ‖gradient h x‖ ^ 2 ∂μ')
```
In words: finite nonzero Gibbs measure on the chamber; chamber open and convex; V is rho-convex on the chamber (V - rho|x|^2/2 convex there);
L h = -rho h pointwise on the chamber (L = Delta - grad V . grad, project's `CutCur.generator`; the 1/(x_i-x_j) terms cancel, via translation invariance);
weak Neumann identity for all test functions (no boundary term); Poincare with constant 1/rho for all test functions (IsTestFunction = smooth, bounded, Lipschitz,
so it includes C_c^infty); optimal Poincare constant = 1/rho and h = sum x_i is an extremal (Var h = d/rho = (1/rho) int |grad h|^2), i.e. lambda_1 = rho with h in E_1.
Also: `dysonMeasure_eq` (it is `volume.withDensity (ofReal Dlim)` with `Dlim = indicator chamber (exp(-rho|x|^2/2) prod (x_i-x_j)^beta)`), `exp_neg_dysonV`.

## Method (why it was cheap: no singular integration by parts, no Riemannian structure)
The chamber measure is the limit of whole-space measures with smooth rho-convex potentials: `V_eps = rho|x|^2/2 + sum_{i<j} G_eps(x_i-x_j)`,
`exp(-G_eps(t)) = (eps*log(1+e^{t/eps}))^beta / (1+e^{-t/eps})` (softplus; `G_eps` smooth and convex because softplus is log-concave: `Dyson1D.lean`,
and the logistic factor forces the wall also for beta = 0). Then, for each eps, the project's Theorem 1.5 pipeline (`convex_interaction`, `pi_valid`) gives the exact
Poincare inequality and `integral_mul_fderiv_gibbs_eq_neg` gives the exact identity `int D_eps d_{(1..1)}phi = rho int D_eps h phi` (since sum_i d_i V_eps = rho h exactly,
by translation invariance). Dominated convergence (uniform bound `(1+|x|)^2 D_eps <= K exp(-rho|x|^2/4)`, a.e. convergence off the null set of ties) passes to eps -> 0.
Extremality: test the Neumann identity on `S_n(h)` (arctan truncations), giving `rho int h^2 = d`, `int h = 0` (phi = 1), then `Var(S_n h) -> d/rho`.

## What is NOT proved / honest limits
* The Hessian form `Hess V >= rho I` on the chamber is stated as convexity of `V - rho|x|^2/2` on the chamber (the manuscript only says "rho-convex"); the pointwise Hessian inequality is not stated.
* `spectralGap` (inf of Rayleigh quotients over C_c^infty non-constant) for the chamber measure is NOT defined/proved equal to rho; only the test-function optimal constant (`optimalPIDyson`, same shape as `CutCur.optimalPI`).
  The remaining step is a cutoff argument (approximating S_n(h) by compactly supported functions), est. 300-600 lines; the lower bound (>= rho) is immediate from `dyson_poincare`.
* Process level (Dyson-OU SDE with reflection for beta < 1 / collisions, Markov semigroup whose generator is the Neumann/Friedrichs realisation, spectral theory of that operator, E_1 as an eigenspace of a self-adjoint operator): not attempted; 
  new SDE theory (Rogers-Shi, Anderson-Guionnet-Zeitouni for beta >= 1; Skorokhod reflection for beta = 0), estimated months. The eigenfunction statement is at the level of the quadratic form (weak Neumann) plus the pointwise identity on the open chamber.
* `d = 0` excluded (`0 < d`), as in Theorem 1.5.
* Not claimed: cutoff or Wasserstein statements for DOU (the manuscript only cites BCL23 for them).

## Possible weak points for the adversary
`dysonV` has junk values off the chamber but is only used on the chamber and through the indicator in `dysonMeasure`; `generator` uses `fderiv` at points of the open chamber, which is local.
Hypotheses are exactly rho > 0, beta >= 0, d > 0; satisfiable (e.g. rho = 1, beta = 0, d = 1, where the chamber is all of R and mu is the Gaussian).
