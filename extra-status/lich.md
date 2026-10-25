# lich: Euclidean Lichnerowicz and (R2) => (R1)

File: CutoffRigidity/Extra/Lichnerowicz.lean (module CutoffRigidity.Extra.Lichnerowicz, 364 lines).
`lake build CutoffRigidity.Extra.Lichnerowicz` succeeds; no sorry/axiom/native_decide; `#print axioms` of both
theorems: propext, Classical.choice, Quot.sound. No existing file edited. Helper lemmas (all in
CutoffRigidity.Paper): gradient_cutoff_mul_inner_add, spectralGap_le_of_affine_eigenfunction_aux_shift (copy of
GapUpper's aux with an additive constant b), hessian_quad, hessian_inv, rayleigh_nonempty.

## 1. PROVED: CutoffRigidity.Paper.spectral_gap_ge_curvature (eq:Lichne, lines ~519-548)
Amendment (flagged): hypothesis `0 < d` is necessary. For d = 0 the Rayleigh set is empty, `sInf ∅ = 0`, while
all other hypotheses hold vacuously (gibbs = Dirac, Hessian condition trivial), so the claim `ρ ≤ spectralGap` is
false. Nothing else is added (ContDiff 2 and probability are the project's standing setting).
Proof: nonempty Rayleigh set via a ContDiffBump (positive density => variance > 0), then Poincare from
`gibbsSpectralGap_mul_variance_le` and `gibbsSpectralGap_ge_curvature`.

Proposed Challenge text:
```lean
/-- **Lichnerowicz / Bakry–Émery bound** (eq. (1.7), `λ₁ ≥ ρ`): if `V` is `C²`, `e^{-V}` is a probability
density and `Hess V ≥ ρ I` with `ρ > 0`, then `λ₁ ≥ ρ`. (`0 < d` is needed: for `d = 0` the gap is `sInf ∅ = 0`.) -/
theorem spectral_gap_ge_curvature {d : ℕ} (hd : 0 < d) {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbs V)) {ρ : ℝ} (hρ : 0 < ρ)
    (hconv : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ρ ≤ spectralGap V := by
  sorry
```
Paper version is identical with `CutCur.` prefixes (`CutCur.Rd d`, `CutCur.gibbs`, `CutCur.spectralGap`).

## 2. PROVED: CutoffRigidity.Paper.rigidity_of_gaussian_factor ((R2) => (R1), lines ~553-565)
Faithful reading: (R2) says that up to rotation+translation mu splits as N(0,1/rho) x (rho-convex-potential factor).
At potential level this is: unit vector u, shift m, V(x) = rho/2 (<u,x>-m)^2 + U(x), U invariant along u (so
U depends only on the orthogonal coordinates), and U rho-convex in directions orthogonal to u (the same form as
the output of Theorem 3.1 with k_1 = 1). Conclusion: R1 = curvature >= rho and lambda_1 = rho; I also add the
manuscript's "in which case" part that the affine function <u,x>-m is a lambda_1-eigenfunction (free from the
proof). No hypothesis beyond the text, except that `ContDiff 2 V` and the probability of gibbs V are the project's
standing setting. Note RigidCurvature V follows (gap = rho > 0, Hessian bound), so it is not repeated.
Not formalized: "all eigenfunctions for lambda_1 are affine" (that is the converse direction, already
`euclidean_gaussian_factorization`, which applies since hypotheses of R1 hold) and the k-dimensional iteration.
The Gaussian factor is expressed on the potential, not as a pushforward product measure (equivalent for the
density e^{-V}; the measure-level statement is already derived in `convex_interaction` for the diagonal case).

Proposed Challenge text:
```lean
/-- **(R2) ⇒ (R1)** (rigidity, §1.3): if, up to translation and rotation, `V = ρ/2 (⟨u,x⟩ - m)² + U(x)` with `U`
invariant along the unit vector `u` and `ρ`-convex in the orthogonal directions (i.e. `μ` splits as `𝒩(m, 1/ρ)`
times a log-concave factor with `ρ`-convex potential), then `Hess V ≥ ρ I`, `λ₁ = ρ`, and `⟨u,x⟩ - m` is an
eigenfunction for `λ₁`. -/
theorem rigidity_of_gaussian_factor {d : ℕ} {V : Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbs V)) {ρ : ℝ} (hρ : 0 < ρ)
    (u : Rd d) (hu : ‖u‖ = 1) (m : ℝ) (U : Rd d → ℝ)
    (hsplit : ∀ x, V x = ρ / 2 * (inner ℝ u x - m) ^ 2 + U x)
    (hinv : ∀ x (t : ℝ), U (x + t • u) = U x)
    (hU : ∀ x z, inner ℝ u z = 0 → ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x z z) :
    (∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) ∧
      spectralGap V = ρ ∧ IsEigenfunction V ρ (fun x => inner ℝ u x - m) := by
  sorry
```
Paper version identical with `CutCur.` prefixes.

## 3. NOT DONE: Riemannian Lichnerowicz (CD rho => mSpectralGap >= rho, line ~627)
Statement would be clear (`ρ ≤ mSpectralGap F μ` under hV, hμ, hρ, hCD, `[IsProbabilityMeasure μ]`, connected,
complete). Blocker: every Riemannian tool in the project (`lsi_of_CD`, `poincare_of_gap`, DiffLSI*, DiffGapAttained*,
`gap_attained_of_LSI`) takes `hgap : mSpectralGap F μ = ρ` as a hypothesis and uses it to supply the Poincare
inequality needed for ergodicity, so nothing yields the lower bound on the gap. The available ingredient without
hgap is `beStrong_of_CD`/`gradBound_of_CD` (DiffBEMain: |grad K_t f| <= e^{-rho t} K_t|grad f|). A proof would need
new development: invariance of mu under K_t, d/dt int (K_t f)^2 dmu = -2 int Gamma(K_t f) dmu, and K_t f -> int f dmu
(ergodicity, needs a first-moment/truncation argument without a Gaussian-concentration input), i.e. a substantial
new file; not attempted.
