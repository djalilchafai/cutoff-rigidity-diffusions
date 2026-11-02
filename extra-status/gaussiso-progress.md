# R5 Gaussian isoperimetric inequality: plan and progress

## Target (decided)
Bobkov functional form for the Gaussian measure `N(0, rho^{-1} I_d)` (NOT general `Hess V >= rho`: that needs the
Riemannian Gamma_2 calculus on `P_t f` and is far too large; see "Not done"):
`I(int f dmu) <= int sqrt(I(f)^2 + rho^{-1} |grad f|^2) dmu` for `f : R^d -> [0,1]` C^1 with bounded gradient,
`I = phi ∘ Phi^{-1}`. (Convention check: CD(rho,inf) <-> Gaussian N(0,1/rho), LSI constant 2/rho: same scaling.)
Set form (`mu(A_r) >= Phi(Phi^{-1}(mu A) + sqrt(rho) r)`) afterwards if feasible.

## Route (cheapest found; all single-variable calculus)
Mathlib has a CLT but we do not need it. 1D semigroup proof (Bakry-Ledoux specialised) + Minkowski tensorisation.
* OU/Mehler `P_s f(x) = int f(e^{-s}x + sqrt(1-e^{-2s}) y) dgamma(y)`, `g = P_s f`, `F = sqrt(I(g)^2 + g'^2)`.
* Key identity (uses `I I'' = -1`, `I' = -Phi^{-1}`): `d/ds F = L F - (I(g) g'' - I'(g) g'^2)^2 / F^3`, `L = d^2 - x d`.
  So `Psi(s) = int F_s dgamma` has `Psi' = -int (...)^2/F^3 <= 0`; `Psi(0) = int sqrt(I(f)^2+f'^2)`, `Psi(inf) = I(int f)`.
* Stages:
  1. GaussIso1: profile `I`, `Q = Phi^{-1}`, derivatives; Stein lemma `int y k = int k'` for gamma.
  2. GaussIso2: Mehler derivatives in x (`g' = r P f'`), time derivative / heat equation.
  3. GaussIso3: Psi monotone, limits s->0, s->inf; 1D theorem for smooth f with bounded derivatives valued in [eps,1-eps].
  4. GaussIso4: remove eps (continuity of I at 0,1) and smoothness (mollification) : 1D for C^1 bounded-derivative f:R->[0,1].
  5. GaussIso5: tensorisation to `Fin n -> R` product Gaussian (Minkowski for finite families).
  6. GaussIso6: transfer to `EuclideanSpace`, scaling by rho, final statement.
  7. GaussIso7 (optional): set form / Gaussian concentration.

## State
(see below, updated after each stage)

### Update (stage 3 done)
GaussIso1..5 compile (no sorry): profile I, Stein, Mehler derivatives, heat equation, Psi monotone, and
`Good.bobkov : gI (∫ f dγ) ≤ ∫ sqrt (gI (f x)^2 + f1 x^2) dγ` for `Good ε f f1 f2 f3` (C^3 bounded derivs, values in [ε,1-ε]).
Key identity proved: `Prof.SF_eq`: ∂ₛF = F'' - xF' - M, M = (I g'' - I' g'^2)^2/F^3 >= 0.
Next (route Y): smoothing `P_{s0} f` of C^1 data (Hh-trick kernel derivative, Stein with growth, Mehler invariance) -> 1D theorem for
f C^1 with bounded continuous derivative, [0,1]-valued; then tensorisation (C^1 class closed under marginals), then R^d, rho scaling.

### Update (stage 4 done)
GaussIso6-8 compile (no sorry). `CutoffRigidity.GaussIso.bobkov_C1` (GaussIso8.lean):
```
theorem bobkov_C1 {f f1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f1 x) x) (b0 : BC f) (b1 : BC f1)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gI (∫ y, f y ∂γ1) ≤ ∫ x, Real.sqrt (gI (f x) ^ 2 + f1 x ^ 2) ∂γ1
```
(γ1 = gaussianReal 0 1, gI = φ∘Φ⁻¹ with gI=0 outside (0,1), BC = bounded continuous.) Proof: P_s smoothing via Stein/primitive trick, Good.bobkov, eps-removal.
Next: tensorisation on Fin n → ℝ (Minkowski), transfer to EuclideanSpace, rho scaling, set form.

### Update (stage 5 done)
GaussIso9-10 compile (no sorry): `bobkov_pc` for `γn n = Measure.pi (fun _ => γ1)` on `Fin n → ℝ`, coordinate-wise C^1 class `PC n f d`
(partial derivatives `d i`), via Minkowski + marginal closure. Next: GaussIso11 transfer to EuclideanSpace + rho, identification of
`gibbs (ρ/2|x|²+c)` (probability) with `(stdGaussian E).map ((√ρ)⁻¹ • ·)` via charFun (Mathlib Gaussian Fourier integral), then set form.

### Update (functional form DONE, stage 6)
GaussIso11-13 compile, no sorry, axioms = propext, Classical.choice, Quot.sound.
Final statement (GaussIso13.lean, namespace CutCur; `gaussianIsoProfile` = φ∘Φ⁻¹ with Φ⁻¹(u)=sInf{x | u ≤ cdf x}, 0 outside (0,1)):
```
theorem gaussian_isoperimetric_functional {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {V : Rd d → ℝ}
    (hV : ∃ c : ℝ, ∀ x, V x = ρ / 2 * ‖x‖ ^ 2 + c) (hp : IsProbabilityMeasure (gibbs V))
    {f : Rd d → ℝ} (hf : IsTestFunction f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gaussianIsoProfile (∫ x, f x ∂gibbs V) ≤
      ∫ x, Real.sqrt (gaussianIsoProfile (f x) ^ 2 + ρ⁻¹ * ‖gradient f x‖ ^ 2) ∂gibbs V
```
plus `gibbs_quadratic_isProb` (non-vacuity of hp). Chain: gibbs = gaussρ (charFun), gaussρ_bobkov (EuclideanSpace, ContDiff 1 + Lipschitz),
bobkov_pc (Fin n → ℝ), bobkov_C1 (1D). Not done: general V with Hess V ≥ ρ (non-quadratic), set form.

### Update (set form DONE, stage 7) -- ALL STAGES COMPLETE
GaussIso14-19 + GaussIso.lean (entry point) compile, no sorry, axioms = propext, Classical.choice, Quot.sound.
`lake build CutoffRigidity.Extra.GaussIso` succeeds (8951 jobs). ~3300 lines in total (not 4-8k: the 1D semigroup computation
`∂ₛF = F'' - xF' - (I g'' - I' g'^2)^2/F^3` and Minkowski tensorisation avoid any Riemannian Gamma_2 machinery).
Set form route: smooth 1-Lipschitz mollification of dist(.,A) (GaussIso14), almost-linear smooth ramp psi (15), Bobkov for psi∘e (16),
comparison principle by real induction (17), finite-increment inequality (FS) from Bobkov (18), final theorems (19).
Statements: see extra-status/gaussiso-worker.md.
