# dysongap-worker (R1, round 2): spectral gap of the Dyson-OU Gibbs measure equals rho

Verdict: DONE, no sorry, axioms of the headline: propext, Classical.choice, Quot.sound. ~510 lines, 4 new files, none imported by anything existing.
Build: `lake build CutoffRigidity.Extra.DysonGap4` (OK; only linter warnings). No human review claimed.
Files: CutoffRigidity/Extra/DysonGap.lean (cutoff chi_R, gradient bound M/R, pointwise bound on |grad(chi_R h)|^2),
DysonGap2.lean (dominated convergence: int f_R -> 0, int f_R^2 -> d/rho, Var f_R -> d/rho, energy bound), DysonGap3.lean (definition, lower bound,
Rayleigh quotients of chi_R h -> rho, `dysonSpectralGap_eq`), DysonGap4.lean (L2 and H1 convergence f_R -> h, final theorem).

## Definition (same shape as CutCur.spectralGap: same test class, same junk value sInf empty = 0)
```lean
noncomputable def dysonSpectralGap (d : ℕ) (ρ β : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    0 < variance f (dysonProb d ρ β) ∧
    r = (∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) / variance f (dysonProb d ρ β)}
```
Only difference with `spectralGap`: the measure is the normalised `dysonProb d ρ β` (a probability, so `variance` is the usual one) instead of the unnormalised
`gibbs V`; test functions are C_c^infty(R^d) restricted to the chamber (need not vanish at the walls: Neumann/Friedrichs realisation).

## Exact statements
```lean
theorem dysonSpectralGap_eq (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) : dysonSpectralGap d ρ β = ρ

theorem dyson_spectralGap_eigenfunction (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    dysonSpectralGap d ρ β = ρ ∧
    (MemLp (fun x : CutCur.Rd d => ∑ i, x i) 2 (dysonProb d ρ β) ∧
      0 < variance (fun x => ∑ i, x i) (dysonProb d ρ β) ∧
      (∫ x, ‖gradient (fun y => ∑ i, y i) x‖ ^ 2 ∂dysonProb d ρ β) / variance (fun x => ∑ i, x i) (dysonProb d ρ β) = ρ) ∧
    (∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, inner ℝ (gradient (fun y => ∑ i, y i) x) (gradient φ x) ∂dysonProb d ρ β = ρ * ∫ x, (∑ i, x i) * φ x ∂dysonProb d ρ β) ∧
    ∃ f : ℕ → CutCur.Rd d → ℝ, (∀ n, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n) ∧ 0 < variance (f n) (dysonProb d ρ β)) ∧
      Tendsto (fun n => ∫ x, (f n x - ∑ i, x i) ^ 2 ∂dysonProb d ρ β) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ‖gradient (f n) x - gradient (fun y => ∑ i, y i) x‖ ^ 2 ∂dysonProb d ρ β) atTop (𝓝 0)
```
In words: gap = rho; h = sum x_i is in L2, non-constant, Rayleigh quotient exactly rho (so the infimum is attained in the closure); weak Neumann eigen-equation
against every C_c^infty test function (statement over C_c^infty, as the project's Rayleigh class); and h is an H^1(mu)-limit of C_c^infty functions chi_R h.
Hypotheses: d > 0, rho > 0, beta >= 0 only (satisfiable, e.g. d=1, rho=1, beta=0 gives the Gaussian).

## Method
Lower bound: Poincare (`dyson_poincare`) since C_c^infty functions are IsTestFunction (`isTestFunction_of_compact`). Upper bound: f_R = chi_R h, chi_R = bump(x/R)
(bump equal to 1 on the unit ball, supported in ball 2), ||fderiv chi_R|| <= M/R; |grad f_R|^2 <= (1+1/R) d + (1+R)(M/R)^2 h^2 pointwise, hence energy <= d + o(1);
Var f_R -> d/rho by dominated convergence (|f_R| <= |h|, h in L2, mean 0, second moment d/rho from Dyson6); Rayleigh(f_R) squeezed between rho and an upper bound -> rho.

## Not covered / honest limits
* The gap is the Rayleigh infimum (the project's convention), not the bottom of the spectrum of an operator; identification with the Friedrichs/Neumann self-adjoint
  operator and the process level remain out of scope (as in Dyson7).
* "Eigenfunction" is at the level of the weak equation + H^1-closure; no claim about E_1 being exactly span{h} (the dimension of the eigenspace is not computed).
* dysonSpectralGap uses the normalised measure; for the probability dysonProb this agrees with the project's spectralGap convention up to the normalisation of mu (the Rayleigh quotient with the
  unnormalised measure would be rescaled by Z in the numerator only if Var were not normalised; not an issue here since a probability is used).
* Lean `IsEigenfunction` (C^2 pointwise on all of R^d) is not applicable to the chamber (V = +infinity off it); the pointwise identity on the open chamber is in `dyson_ou_static`.
