# sec4b: manuscript subsection "Optimal constants" (cutcur-lean.tex ~l.808-825)

Status: DONE, no sorry. File `CutoffRigidity/Extra/OptimalConstants.lean` (637 lines, module
`CutoffRigidity.Extra.OptimalConstants`), `lake build` OK, `#print axioms` of both final theorems:
`propext, Classical.choice, Quot.sound`. Not human reviewed; lead must check.

## Conventions (explicit)
* PI with constant C: `Var_mu f <= C * int |grad f|^2 dmu`.  LSI with constant C: `Ent_mu(f^2) <= C * int |grad f|^2 dmu`,
  `Ent_mu(g) = int g log g - (int g) log (int g)`.  Gaussian N(0,1/rho): PI constant 1/rho, LSI constant 2/rho
  (this is the manuscript's "LSI constant 2/rho, PI constant 1/rho", so "LSI = 2 x PI" under rigidity).
* Optimal constants = infimum of valid constants C >= 0 over test functions = smooth (C^infty), bounded, Lipschitz
  functions (contains smooth compactly supported ones and constants; chosen so that `1 + eps g` is admissible in the
  linearization).  Equality with the compactly supported class follows here under rigidity (both = 1/lambda_1).

## Proved (namespace `CutoffRigidity.Paper`)
* defs `entropyOf`, `IsTestFunction`, `optimalPI`, `optimalLSI`.
* `pi_valid` (PI with 1/lambda_1 on test fns), `lsi_valid` (LSI with 2/lambda_1, via `logSobolev_normalized_bounded_lipschitz`
  and scaling), `pi_of_lsi` (linearization: LSI constant C implies PI constant C/2, Taylor bound `phi_lower`),
  `inv_spectralGap_le_of_pi`, `optimalPI_eq`, `optimalLSI_eq`.
* `optimal_lsi_twice_pi` (final, general rigid case).
* `optimal_constants_extremal` (final, convex interaction: PI extremal h = x_1+...+x_d, LSI extremal e^{alpha h}).

## Proposed Challenge text (unqualified names; defs go in `namespace CutCur`)
```lean
/-- Entropy `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)`. -/
noncomputable def entropyOf {d : ℕ} (μ : Measure (Rd d)) (g : Rd d → ℝ) : ℝ :=
  (∫ x, g x * Real.log (g x) ∂μ) - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- Test functions for the optimal constants: smooth, bounded, Lipschitz. -/
def IsTestFunction {d : ℕ} (f : Rd d → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∃ M : ℝ, ∀ x, |f x| ≤ M) ∧ ∃ L : ℝ≥0, LipschitzWith L f

/-- Optimal Poincaré constant: least `C ≥ 0` with `Var_μ f ≤ C ∫|∇f|² dμ` on test functions. -/
noncomputable def optimalPI {d : ℕ} (V : Rd d → ℝ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ f : Rd d → ℝ, IsTestFunction f →
    variance f (gibbs V) ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂gibbs V}

/-- Optimal LSI constant: least `C ≥ 0` with `Ent_μ(f²) ≤ C ∫|∇f|² dμ` on test functions. -/
noncomputable def optimalLSI {d : ℕ} (V : Rd d → ℝ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ f : Rd d → ℝ, IsTestFunction f →
    entropyOf (gibbs V) (fun x => f x ^ 2) ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂gibbs V}

/-- **Optimal constants** (subsection "Optimal constants"): under rigidity `Hess V ≥ λ₁ I`, the optimal
Poincaré constant is `1/λ₁` and the optimal LSI constant is twice the optimal Poincaré constant. -/
theorem optimal_lsi_twice_pi {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {B : ℝ≥0 → Ω → Rd d}
    {P : Measure Ω} (hB : IsStdBrownian B P) {V : Rd d → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbs V)) (hR : RigidCurvature V) :
    optimalPI V = (spectralGap V)⁻¹ ∧ optimalLSI V = 2 * optimalPI V := by
  sorry

/-- **Extremal functions** (same subsection): in the setting of Theorem 1.5, `x ↦ ∑ xᵢ` is extremal for PI
and `x ↦ e^{α ∑ xᵢ}` is extremal for LSI (every real α); both are outside the bounded test class, so the
statement asserts finiteness of all integrals involved and equality with the optimal constants. -/
theorem optimal_constants_extremal {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {B : ℝ≥0 → Ω → Rd d}
    {P : Measure Ω} (hB : IsStdBrownian B P) (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Rd d → ℝ} (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W)
    (hinv : ∀ x (s : ℝ), W (x + s • diagonal d) = W x)
    (hp : IsProbabilityMeasure (gibbs fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) :
    let V := fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + W x
    let h := fun x : Rd d => ∑ i, x i
    optimalPI V = ρ⁻¹ ∧ optimalLSI V = 2 * optimalPI V ∧
    (MemLp h 2 (gibbs V) ∧ 0 < variance h (gibbs V) ∧
      variance h (gibbs V) = optimalPI V * ∫ x, ‖gradient h x‖ ^ 2 ∂gibbs V) ∧
    ∀ α : ℝ,
      Integrable (fun x => Real.exp (α * h x) ^ 2) (gibbs V) ∧
      Integrable (fun x => Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2)) (gibbs V) ∧
      Integrable (fun x => ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2) (gibbs V) ∧
      (α ≠ 0 → 0 < ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂gibbs V) ∧
      entropyOf (gibbs V) (fun x => Real.exp (α * h x) ^ 2) =
        optimalLSI V * ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂gibbs V := by
  sorry
```
The Paper versions (identical statements with `CutCur.` qualification; the defs live in `CutoffRigidity.Paper`
and must be moved to `CutCur` with the Challenge paste, then `Paper.optimal_lsi_twice_pi` etc. rewritten to
`CutCur.optimalPI` ...) are `CutoffRigidity.Paper.optimal_lsi_twice_pi` and `CutoffRigidity.Paper.optimal_constants_extremal`.

## Amendments / flags
1. AMENDMENT (extra hypothesis): `hB : IsStdBrownian B P` (a Brownian motion on some probability space) appears in both
   theorems although the manuscript text does not mention one.  It is needed only because the project's Bakry-Emery LSI
   (`logSobolev_normalized_bounded_lipschitz`) is proved by the Langevin semigroup and the existence of Brownian motion
   is not available in Mathlib (same situation as `IsLangevin` in Challenge).  It is not used in `optimalPI` statements.
   Mathematically harmless (Brownian motions exist); lead may prefer `IsLangevin`-style packaging or `∃`-free variant.
2. The manuscript claim "optimal PI constant is 1/lambda_1" is proved only under rigidity (that is the case used).
3. Extremality claim is TRUE as stated, for every real alpha (also negative or zero; alpha = 0 gives f = 1, trivial
   equality 0 = 0, hence the positivity clause only for alpha != 0).  Precise content: under mu = N(0,1/rho)(dt) x nu in
   the coordinates (t = <u,x>, pi x), h = sqrt(d) t, so Ent(e^{2 alpha h}) = (2/rho) alpha^2 d E[e^{2 alpha h}] =
   (2/rho) int |grad e^{alpha h}|^2 dmu.  The function is NOT in the bounded test class (unbounded, not Lipschitz
   with bounded sup); it lies in the natural LSI domain (H^1(mu), all integrals finite), which is why the theorem
   states integrability of f^2, f^2 log f^2, |grad f|^2 explicitly: without it the Bochner integrals could be junk.
   Likewise h is only extremal in the L^2 sense (`MemLp h 2`, Var h > 0).
4. Test class chosen = smooth bounded Lipschitz (not only compactly supported); equal constants proved under rigidity.
5. Rothaus alternative: not formalized (literature remark), as instructed.
6. Imports added: `LipschitzExponentialLogSobolev` (for `gradient_exp_mul_at`), `Paper.GapBridge`,
   `Paper.ConvexInteraction`.  No existing file modified.
