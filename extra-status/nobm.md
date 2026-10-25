# nobm: Brownian-free optimal constants, extremal functions, Talagrand + LSI

Status: PROVED for the full C^2 hypothesis (no smoothness amendment). Not reviewed by a human.
All new files are in `CutoffRigidity/Extra/`, `lake build CutoffRigidity.Extra.NoBmStatements` succeeds,
no `sorry`/`axiom`/`native_decide`; `#print axioms` of the three theorems = propext, Classical.choice, Quot.sound.
No existing file edited (not even upstream). The lead only has to add `public import CutoffRigidity.Extra.NoBmStatements`.

## Theorems (namespace `CutoffRigidity.Paper`, file `Extra/NoBmStatements.lean`)
`optimal_lsi_twice_pi_nobm`, `optimal_constants_extremal_nobm`, `talagrand_logSobolev_nobm`.
Statements = the Challenge statements minus the carrier. Note on `talagrand_logSobolev`: its `hL : IsLangevin V B P X`
bundled `ContDiff ℝ 2 V` and `IsProbabilityMeasure (gibbs V)` (standing assumptions of the manuscript) besides the
Brownian/SDE parts; those two are kept as explicit hypotheses `hV`, `hp`. Nothing else was added or dropped
(`0 < d` kept in the last two).

## Where the Brownian motion was really used
Tracing every use of `hB : IsEuclideanBrownian B P` in the Euclidean chain (Talagrand.lean, LogSobolev.lean,
HopfLax*.lean, Lipschitz*LogSobolev.lean, LogSobolevClosedRoot.lean) shows ONE Brownian-dependent leaf:
`logSobolev_regularized_compact_square` (LogSobolevSquareCore.lean: entropy bound for `(f²+ε)/(a+ε)`, f in C²_c, via
the Langevin kernel). Everything else (closed H¹ domain extension, bounded-Lipschitz LSI, Hopf-Lax/Hamilton-Jacobi
exponential inequality, Kantorovich duality, Talagrand, relative Fisher form) only forwards `hB` to it.
`pi_valid` (Poincare) was already Brownian-free; only `lsi_valid` needed the carrier.

## Route taken: option (a), including C^2 via mollification (no C^∞ amendment needed)
1. `NoBm.lsi_smooth_compact` (Extra/NoBmLSI.lean): flat `ℝ^d`, `V` C^∞, `Hess V ≥ ρ`: LSI for C^∞_c tests, from
   `Riemann.Diff.lsi_of_CD` (analytic Bakry-Emery, no Brownian motion, no spectral-gap hypothesis) with
   `cd_euclid_iff`, `isWeightedVolume_gibbs`, `carre_rd`. About 20 lines.
2. `NoBm.convexOn_univ_of_hessian_nonneg` (NoBmConvex.lean) and the mollification of the potential (NoBmMollify.lean):
   `U = V - ρ|x|²/2` is convex; `V_n = ρ|x|²/2 + (ψ_n ⋆ U)` is C^∞ with `Hess V_n ≥ ρ` (convexity is preserved by
   convolution, so no derivative under the integral is needed); uniform Gaussian domination
   `e^{-V_n} ≤ C e^{-ρ|x|²/8}` (from `potential_gaussian_lower_bound`); normalised `W_n = V_n + log Z_n`,
   `Z_n → 1`, `∫ G d gibbs(W_n) → ∫ G d gibbs(V)` for bounded continuous `G`. Result
   `NoBm.lsi_C2_smooth_compact`: LSI for C² potentials and C^∞_c tests.
3. NoBmLSI2.lean: mollify the test function (`fderiv` of a convolution): `NoBm.lsi_C2_compact` for C²_c tests.
4. NoBmLSI3.lean: abstract limit lemma `lsi_of_approx`, cutoff `χ(x/R)`: `NoBm.lsi_C2_bounded` (bounded C² with
   bounded gradient), then `NoBm.logSobolev_regularized_compact_square_nobm` = exactly the statement of the
   Brownian leaf without `hB` (with `h = sqrt(f²+ε)`, `|∇h| ≤ |∇f|`, `∫ klFun(w/D) = Ent(w)/D`).
5. NoBmChain.lean: mechanical copies (script: remove binders `B`, `P`, `hB`, suffix `_nobm`) of the 11 hB-theorems
   of the chain, with the leaf replaced; compiled unchanged (only an unused-`hd` linter warning).
6. NoBmStatements.lean: `lsi_valid_nobm`, `optimalLSI_eq_nobm` (copies of Extra/OptimalConstants proofs), the three theorems.

Option (b) (langevinKernel depends on B,P only through the law of BM) was not needed. Note the dependence of the
project's `langevinKernel` on `B,P` is real (it is defined through the SDE solution), so (b) would require an existence theory.

## Not changed
`langevin_entropy_decay`, `langevin_w2_contraction` and all other theorems whose conclusion mentions the process keep
`IsLangevin`; the Hopf-Lax/Talagrand chain is no longer conditional on a Brownian motion.

## Proposed Challenge text (unqualified names; replace the three existing statements, drop the carrier amendments)
```lean
/-- **Optimal constants** (manuscript subsection "Optimal constants"): under rigidity
(`Hess V ≥ λ₁ I`, `λ₁ > 0`), the optimal Poincaré constant is `1/λ₁` and the optimal
logarithmic Sobolev constant is twice the optimal Poincaré constant. -/
theorem optimal_lsi_twice_pi {d : ℕ} {V : Rd d → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbs V))
    (hR : RigidCurvature V) :
    optimalPI V = (spectralGap V)⁻¹ ∧ optimalLSI V = 2 * optimalPI V := by
  sorry

/-- **Extremal functions** (manuscript subsection "Optimal constants"): in the convex-interaction
setting `V = ρ|x|²/2 + W`, the function `x ↦ x₁+⋯+x_d` is extremal for the Poincaré inequality
(equality with the optimal constant), and `x ↦ e^{α(x₁+⋯+x_d)}` is extremal for the logarithmic
Sobolev inequality (equality with the optimal constant), for every real `α`. Both functions lie outside
the bounded test class, so the statement asserts finiteness of all the integrals involved.
Amendment: `0 < d`. -/
theorem optimal_constants_extremal {d : ℕ} (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Rd d → ℝ} (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W)
    (hinv : ∀ x (s : ℝ), W (x + s • diagonal d) = W x)
    (hp : IsProbabilityMeasure (gibbs fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) :
    let V := fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + W x
    let h := fun x : Rd d => ∑ i, x i
    optimalPI V = ρ⁻¹ ∧ optimalLSI V = 2 * optimalPI V ∧
    (MemLp h 2 (gibbs V) ∧ 0 < variance h (gibbs V) ∧
      variance h (gibbs V) =
        optimalPI V * ∫ x, ‖gradient h x‖ ^ 2 ∂gibbs V) ∧
    ∀ α : ℝ,
      Integrable (fun x => Real.exp (α * h x) ^ 2) (gibbs V) ∧
      Integrable (fun x => Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2))
        (gibbs V) ∧
      Integrable (fun x => ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2) (gibbs V) ∧
      (α ≠ 0 → 0 < ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂gibbs V) ∧
      entropyOf (gibbs V) (fun x => Real.exp (α * h x) ^ 2) =
        optimalLSI V * ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂gibbs V := by
  sorry

/-- **Talagrand** `ρ W₂(ν,μ)² ≤ 2 H(ν | μ)` and **logarithmic Sobolev** `H(ν | μ) ≤ I(ν | μ)/(2ρ)`
(eq. LSI) under `Hess V ≥ ρ I`, for every probability law `ν`. Amendment: `0 < d`. -/
theorem talagrand_logSobolev {d : ℕ} {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbs V)) (hd : 0 < d)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] :
    ENNReal.ofReal ρ * wasserstein2 ν (gibbs V) ^ 2 ≤
        2 * InformationTheory.klDiv ν (gibbs V) ∧
      InformationTheory.klDiv ν (gibbs V) ≤ fisherInfo V ν / ENNReal.ofReal (2 * ρ) := by
  sorry
```
Wiring for `Solution.lean`: `exact CutoffRigidity.Paper.optimal_lsi_twice_pi_nobm hV hp hR` etc. (same argument order
as the Challenge statements above). Downstream users inside the project of the old carrier versions
(`Extra/OptimalConstants.lean`, `Extra/Dynamics.lean::talagrand_logSobolev`) can stay as they are; if no Challenge
theorem uses them they can be dropped from the build, keeping the `_nobm` ones.

## Files (all new, all < 1500 lines)
NoBmLSI.lean (40), NoBmConvex.lean (55), NoBmMollify.lean (360), NoBmLSI2.lean (127), NoBmLSI3.lean (316),
NoBmChain.lean (722, mechanical copies), NoBmStatements.lean (265).
`git status` also shows `D cutcur-lean.bbl` (a LaTeX artifact deleted by someone else, not by this work).
