# Item 4 worker report: de Bruijn / entropy dissipation (Armstrong method)

Status: PARTIAL. Two true theorems proved (no sorry, axioms propext/Classical.choice/Quot.sound only). The full identity
`H(mu_s|mu) - H(mu_t|mu) = int_s^t I(mu_r|mu) dr` for a general initial law is NOT proved (exact obstruction below).

Files: CutoffRigidity/Extra/Dissip1.lean (calculus), Dissip2.lean (carrier level), Dissip3.lean (kernel form `IsEuclideanLangevin`).
All build (`lake build CutoffRigidity.Extra.Dissip3`).

## Proved statements (kernel form, Dissip3, namespace CutoffRigidity.Dissip)

(A) general initial law, finite entropy, half "ge" of the integrated identity (lintegral, extended reals):
```
theorem langevin_dissipation_ge_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν]
    (hfin : klDiv ν (CutCur.gibbs V) ≠ ⊤) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal))) +
        klDiv (ν.bind (Pt t)) (CutCur.gibbs V) ≤ klDiv (ν.bind (Pt s)) (CutCur.gibbs V)
```
i.e. H(mu_s)-H(mu_t) >= int_s^t I(mu_r) dr. Proof: existing drop inequality `langevinKernel_entropy_fisher_drop` started at mu_s,
I antitone (`relativeFisherInformation_langevinKernel_antitone`), finiteness of H and I(r) for r>0, then a Riemann-sum lemma
`integral_le_sub_of_drop` (Dissip1, pure real analysis: drop + antitone => int_s^t I <= H s - H t). It uses hρ>0 and Hess V >= rho I only
because the project's drop/antitone theorems do (IsEuclideanLangevin alone gives no such monotonicity).

(B) full identity, for initial density c+g (g C^2 with compact support, c+g >= m > 0, integral 1), all 0 <= s < t:
```
theorem langevin_dissipation_core_K ... (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x) (hNorm : ∫ x, c + g x ∂CutCur.gibbs V = 1) {s t : ℝ≥0} (hst : s < t) :
    klDiv (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt s)) (CutCur.gibbs V) =
      klDiv (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt t)) (CutCur.gibbs V) +
      ∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt r.toNNReal))
```
Proof: existing pointwise derivative `hasDerivAt_klDiv_langevinKernel` (d/dt H = -I for t>0) + continuity at all times
(`continuous_klDiv_langevinKernel`) + FTC with I antitone (interval integrable). Carrier versions: `langevin_dissipation_ge`,
`langevin_dissipation_core` (Dissip2), with `lawAt V ν r := langevinKernel V B P r.toNNReal ∘ₘ ν`.
Also the pointwise derivative `HasDerivAt (t ↦ H(mu_t).toReal) (-I(mu_t).toReal) t` for t>0 for these core initial laws already
exists as `hasDerivAt_klDiv_langevinKernel` (LangevinDeBruijn.lean, carrier form); not re-exported in kernel form here.

## What is NOT proved
The reverse inequality H(mu_s)-H(mu_t) <= int_s^t I for a general initial law with H(nu|mu)<infty (hence the equality), and a pointwise derivative
at t>0 for general nu (the derivative may exist for every t>0 in truth, but proving it needs the same ingredient).

## Exact obstruction
The project only has the derivative formula for the dense class nu=(c+g)mu (compact support perturbation). Passing to general nu by approximation
nu_n -> nu (the project has L1/KL approximation `exists_finite_entropy_probability_core_L1_KL_approx`) gives, for the identity
h_n(s)-h_n(t)=int_s^t I_n, only LOWER semicontinuity of H and I along nu_n P_r. That yields exactly (A) again (Fatou direction).
The missing direction needs: (i) limsup H(nu_n P_t) <= H(nu P_t) (continuity, not lsc, of entropy at fixed t>0; via Jensen
Phi(P_t f_n) <= P_t Phi(f_n) and uniform integrability, roughly 500-800 lines in this kernel/density set-up), and (ii) UPPER semicontinuity
(or a.e. convergence plus domination) of r -> I(nu_n P_r) on [s,t] (needs gradient bounds / Bakry-Emery gradient estimate for the transition
density of an L1 initial datum; the existing `LangevinBoundedGradientEstimate` covers bounded data only) roughly 1000-2000 lines. Alternative: redo the
de Bruijn derivative for the smooth positive density of mu_s itself (needs integration by parts on the whole space with only L1/entropy integrability,
dominated differentiation under the integral): comparable, 1500-3000 lines, medium-high risk. Estimate of the full general identity: 1500-2500 lines
beyond the present 450. Not attempted.

## Remarks for the adversary / lead
* Statement (A) is strictly weaker than the manuscript's equality in eq:HI (an inequality `>=` but it is the direction the manuscript later uses:
  H(mu_t0)-H(mu_t1) >= (t1-t0) I(mu_t1) already follows from the drop theorem; (A) is the sharper integrated form).
* Both hypotheses: (A) needs rho>0 and Hess V >= rho I (as `langevin_entropy_decay`); (B) too, plus the stated regularity of g. Non-vacuity: V=|x|^2/2,
  Pt the OU semigroup (exists), nu = mu (g=0,c=1) is a degenerate witness; nondegenerate: g a normalized smooth bump with c chosen s.t. integral = 1 and c+g>=m>0.
  No witness was formally constructed in Lean (not done).
* The manuscript's derivative claim for every t and every law is not covered; also the name `∂_t I <= -2 rho I` is already the Dini form of `langevin_fisher_dini`.
* hfin (finite entropy) is genuinely needed: for H(nu)=infty both sides are infinite/undefined.
* Nothing integrated into Challenge/Statements; Extra files imported by nothing else.
