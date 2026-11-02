# GaussIso adversary report (R5)

Verdict: ACCEPT, as the Gaussian (quadratic V) case only. It is not the CD(rho,infty) result.

## 1. Build and axioms
- `lake build CutoffRigidity.Extra.GaussIso` succeeds (8951 jobs, replayed from cache). Only deprecation and unused-variable warnings.
- `#print axioms` of gaussian_isoperimetric_functional, gaussian_isoperimetric_sets, gaussian_isoperimetric_sets_thickening, gibbs_quadratic_isProb and gaussianIsoProfile gives only [propext, Classical.choice, Quot.sound].
- grep over GaussIso*.lean finds no sorry, axiom, native_decide or admit.

## 2. Faithfulness
- gaussianIsoProfile u = if 0<u<1 then gaussianPDFReal 0 1 (sInf {x | u <= cdf (gaussianReal 0 1) x}) else 0.
  - For u in (0,1) the set is Ici (Phi^{-1} u), nonempty and bounded below (Phi is strictly increasing, continuous and onto (0,1)). So sInf is the true Phi^{-1}(u), with no junk value of sInf.
  - Proved equal to the gI = gphi o gQ used in the proofs (gaussianIsoProfile_eq).
  - gphi := gaussianPDFReal 0 1 and gPhi := cdf (gaussianReal 0 1). Both are the standard N(0,1) density and cdf, and gphi_eq gives (2 pi)^{-1/2} exp(-x^2/2).
  - Endpoints and off [0,1] give 0, which is correct at 0 and 1. The off-[0,1] junk is harmless: the hypotheses force f in [0,1] and the mean lies in [0,1].
- Functional form: I(int f dmu) <= int sqrt(I(f)^2 + rho^{-1}|grad f|^2) dmu, with mu = N(0, rho^{-1} I_d).
  - Scaling check: f(x) = g(sqrt(rho) x) gives |grad g|^2 = rho^{-1}|grad f|^2. So the factor rho^{-1} is correct.
  - For rho = 1 it is exactly Bobkov (1997).
  - hV forces V = rho|x|^2/2 + c, and the hypothesis IsProbabilityMeasure (gibbs V) forces c = (d/2) log(2 pi/rho). The proof goes through gibbs_quadratic_eq_gaussrho (characteristic function), so mu = N(0, rho^{-1} I).
  - IsTestFunction (smooth, bounded, Lipschitz) is the manuscript's own class. Gradient norm is bounded, so the integral is a genuine Bochner integral with no integrability junk. The map u -> sqrt(...) is continuous and bounded.
- Set form: Phi(a) <= mu.real A implies Phi(a + sqrt(rho) r) <= mu.real (cthickening r A), for r >= 0. The open version thickening needs r > 0.
  - a is a real number, so a = +-infinity is not covered. This is only a presentational limitation: the sets Phi(a) are exactly the values in (0,1), and a < -infinity is trivial.
  - A is arbitrary, possibly non-measurable. `.real` of a measure is the outer measure, which is the right convention. The cthickening is closed hence measurable, so the conclusion is meaningful.
  - r = 0 is allowed for cthickening. It gives Phi(a) <= mu(closure A), which is true. Negative r is excluded (cthickening r with r<0 would be empty or junk).
  - A = empty is excluded automatically (Phi(a) > 0). The proof derives A nonempty from this.
  - Scaling: sqrt(rho) r is correct, since the distance in y = sqrt(rho) x coordinates is sqrt(rho) r.
  - This is the sharp Borell, Sudakov-Tsirelson form, which is equivalent to mu^+(A) >= I(mu(A)).

## 3. Vacuity
- gibbs_quadratic_isProb: for every d and rho>0, c = (d/2) log(2 pi/rho) gives IsProbabilityMeasure. So hp is satisfiable for all d, rho, including d=0 (Dirac measure, c=0).
- IsTestFunction: constants in [0,1] are test functions (trivial case I(c) <= I(c)). A genuinely non-trivial witness is a smooth sigmoid of one coordinate. None of this is constructed in Lean. The hypotheses are clearly satisfiable and not contradictory (smooth, bounded, Lipschitz, in [0,1]).
- d = 0: mu is Dirac, f is constant, and the statement reduces to I(c) <= sqrt(I(c)^2). OK.
- Phi^{-1} conventions: checked above, the generalized inverse equals the true inverse on (0,1).
- Proof is not by a degenerate case: it goes through a genuine comparison argument (GaussIso1..19, about 3300 lines: Bobkov via Bakry-Ledoux style semigroup / tensorization or 1D induction, then sets via comparison with approximations).

## 4. Scope and risk of misleading
- Manuscript (cutcur-lean.tex around L626-636) says only that Bakry-Emery CD(rho,infty) "implies stronger functional inequalities, such as a logarithmic Sobolev inequality, and a Gaussian isoperimetric inequality". This is background commentary and is not a theorem of the paper.
- Lean proves it only for V = rho|x|^2/2 + c, i.e. mu exactly Gaussian N(0, rho^{-1} I). The general result for Hess V >= rho (Bakry-Ledoux, via Bakry-Emery semigroup/Gamma_2) is NOT formalized. The Gaussian case is the equality case of CD(rho,infty).
- Labelled "Gaussian isoperimetry" with the hypothesis written as hV : exists c, V = rho/2|x|^2 + c, a reader could think it covers CD(rho,infty) measures. The docstring must say "Gaussian case only; general CD(rho,infty) not formalized".
- Important: the theorem is not a consequence of the paper's results. It is a standalone classical fact, a substantial formalization of the Gaussian special case.

## 5. Suggested Challenge text (compact)
```
/-- The Gaussian isoperimetric profile I = phi ∘ Phi⁻¹ on (0,1), 0 elsewhere (Phi⁻¹ u = inf{x | u ≤ Phi x}). -/
noncomputable def gaussianIsoProfile (u : ℝ) : ℝ :=
  if 0 < u ∧ u < 1 then gaussianPDFReal 0 1 (sInf {x : ℝ | u ≤ cdf (gaussianReal 0 1) x}) else 0

/-- Non-vacuity: e^{-V}dx is a probability measure for V = rho|x|^2/2 + (d/2) log(2 pi/rho). -/
theorem gibbs_quadratic_isProb {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) : IsProbabilityMeasure (gibbs fun x : Rd d =>
    ρ / 2 * ‖x‖ ^ 2 + (d : ℝ) / 2 * Real.log (2 * Real.pi / ρ))

/-- Bobkov's functional Gaussian isoperimetric inequality for mu = N(0, rho^{-1} I), the quadratic
case V = rho|x|^2/2 + c only (NOT general Hess V >= rho). -/
theorem gaussian_isoperimetric_functional {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {V : Rd d → ℝ}
    (hV : ∃ c : ℝ, ∀ x, V x = ρ / 2 * ‖x‖ ^ 2 + c) (hp : IsProbabilityMeasure (gibbs V))
    {f : Rd d → ℝ} (hf : IsTestFunction f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gaussianIsoProfile (∫ x, f x ∂gibbs V) ≤
      ∫ x, Real.sqrt (gaussianIsoProfile (f x) ^ 2 + ρ⁻¹ * ‖gradient f x‖ ^ 2) ∂gibbs V

/-- Gaussian isoperimetric inequality (Borell, Sudakov-Tsirelson), same quadratic case; A arbitrary. -/
theorem gaussian_isoperimetric_sets {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {V : Rd d → ℝ}
    (hV : ∃ c : ℝ, ∀ x, V x = ρ / 2 * ‖x‖ ^ 2 + c) (hp : IsProbabilityMeasure (gibbs V))
    {A : Set (Rd d)} {a : ℝ} (hA : cdf (gaussianReal 0 1) a ≤ (gibbs V).real A) {r : ℝ} (hr : 0 ≤ r) :
    cdf (gaussianReal 0 1) (a + Real.sqrt ρ * r) ≤ (gibbs V).real (Metric.cthickening r A)
```
(sets_thickening, the open version with 0 < r, can be omitted or kept if line budget allows.)
The docstrings above must keep the explicit "quadratic case only" wording. Do not label the items "CD(rho,infty)".

## Remaining caveats (minor)
- a is real only, so mu(A)=1 with no a is fine. Conclusions are in terms of Phi, not I; the profile form (mu^+) is only via Bobkov functional form.
- gaussianIsoProfile is only ever used in the functional statement. The set statement does not use it.
- Not constructed in Lean: a non-constant test function witness.
