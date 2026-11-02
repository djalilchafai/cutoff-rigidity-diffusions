# R5 worker report: Gaussian isoperimetric inequality

Status: PROVED (functional form and set form) for the Gaussian case `V = rho |x|^2/2 + c`; NOT proved for general `Hess V >= rho`.
Not reviewed by a human. Files: `CutoffRigidity/Extra/GaussIso.lean` (entry point) and `GaussIso1..19.lean` (3320 lines). Nothing existing
edited. `lake build CutoffRigidity.Extra.GaussIso` OK; no sorry/axiom/native_decide; `#print axioms` of all four public theorems =
propext, Classical.choice, Quot.sound. Imports: Mathlib, `CutoffRigidity.Statements` (for `CutCur.gibbs`, `Rd`, `IsTestFunction`,
`gradient`), no Brownian motion, no Riemannian layer.

## Precise statements (namespace `CutCur`, file GaussIso13/GaussIso19)
```lean
/-- I = φ ∘ Φ⁻¹, Φ⁻¹(u) = sInf {x | u ≤ cdf (gaussianReal 0 1) x}, I = 0 off (0,1). -/
noncomputable def gaussianIsoProfile (u : ℝ) : ℝ :=
  if 0 < u ∧ u < 1 then gaussianPDFReal 0 1 (sInf {x : ℝ | u ≤ cdf (gaussianReal 0 1) x}) else 0

theorem gaussian_isoperimetric_functional {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {V : Rd d → ℝ}
    (hV : ∃ c : ℝ, ∀ x, V x = ρ / 2 * ‖x‖ ^ 2 + c) (hp : IsProbabilityMeasure (gibbs V))
    {f : Rd d → ℝ} (hf : IsTestFunction f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gaussianIsoProfile (∫ x, f x ∂gibbs V) ≤
      ∫ x, Real.sqrt (gaussianIsoProfile (f x) ^ 2 + ρ⁻¹ * ‖gradient f x‖ ^ 2) ∂gibbs V

theorem gaussian_isoperimetric_sets {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {V : Rd d → ℝ}
    (hV : ∃ c : ℝ, ∀ x, V x = ρ / 2 * ‖x‖ ^ 2 + c) (hp : IsProbabilityMeasure (gibbs V))
    {A : Set (Rd d)} {a : ℝ} (hA : cdf (gaussianReal 0 1) a ≤ (gibbs V).real A) {r : ℝ} (hr : 0 ≤ r) :
    cdf (gaussianReal 0 1) (a + Real.sqrt ρ * r) ≤ (gibbs V).real (Metric.cthickening r A)
-- and gaussian_isoperimetric_sets_thickening: same with `Metric.thickening r A`, `0 < r`.
theorem gibbs_quadratic_isProb {d ρ} (hρ : 0 < ρ) :   -- non-vacuity of hp
    IsProbabilityMeasure (gibbs fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + (d : ℝ) / 2 * Real.log (2 * Real.pi / ρ))
```
`A` need not be measurable (outer measure). Convention check: `V = ρ|x|²/2 + c` is `CD(ρ,∞)` with equality, `μ = N(0, ρ⁻¹ I)`,
matching "LSI constant 2/ρ": the functional form has `ρ⁻¹ ‖∇f‖²` (ρ = 1: Bobkov's inequality; sets: `μ(A_r) ≥ Φ(Φ⁻¹(μ A) + √ρ r)`).
Sharpness (mathematical remark, not formalized): half-spaces give equality.

## Proof architecture
* 1D semigroup (Bakry-Ledoux specialised): `P_s f` Mehler average, `F = √(I(g)² + g'²)`; identity `∂ₛF = F'' - xF' - M`,
  `M = (I g'' - I' g'²)²/F³ ≥ 0` (uses `I I'' = -1`, `I' = -Φ⁻¹`), Stein lemma `∫ x F' dγ = ∫ F'' dγ`, so `Ψ(s) = ∫F_s dγ` is nonincreasing
  from `∫√(I(f)²+f'²)` to `I(∫f)` (GaussIso1-5). Smoothing of merely `C¹` data via the primitive trick (GaussIso6-7), `ε`-removal (GaussIso8):
  `bobkov_C1`.
* Tensorisation by Minkowski's inequality on `Fin n → ℝ` with coordinate-wise `C¹` class (GaussIso9-10): `bobkov_pc`.
* Transfer to `EuclideanSpace`, scaling, identification `gibbs(ρ|x|²/2+c) = (stdGaussian).map ((√ρ)⁻¹ • ·)` via characteristic functions
  (Mathlib's Gaussian Fourier integral) (GaussIso11-13).
* Sets: Bobkov for `ψ ∘ dist(·,A)` through smooth 1-Lipschitz mollification, an almost-linear smooth ramp (slope ≤ (1+η)/s),
  finite-increment inequality for `n_A(t) = μ{dist ≤ t}` (right-continuous, monotone), comparison principle by real induction (GaussIso14-19).

## NOT proved (honest list)
* General `V` with `Hess V ≥ ρ I` (non-quadratic, the manuscript's `CD(ρ,∞)`, Riemannian manifolds): needs Bakry-Ledoux on the `Gamma_2` calculus
  of `P_t f` for a general diffusion semigroup (pointwise smoothness, third derivatives, integrability), or Caffarelli's contraction theorem;
  neither is in Mathlib or in the project in usable form. The statement for `V = ρ|x|²/2 + c` is the equality case `Hess V = ρ I`.
* The manuscript (L626-636) states no precise isoperimetric statement; the above is the chosen precise reading.
* No claim of human review.

## Integration hints for the lead
Challenge-compatible (uses `gibbs`, `Rd`, `IsTestFunction`, `gradient` of Statements/Challenge): add the definition `gaussianIsoProfile`
(or `sInf`-free version) and the three theorems; the proofs only need `public import CutoffRigidity.Extra.GaussIso`.
