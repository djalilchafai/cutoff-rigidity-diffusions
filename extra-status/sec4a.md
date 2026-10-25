# sec4a: Section "Further comments" (Fisher/heat kernel, Normalization, Temperature)

All files compile with `lake build` (modules below), no `sorry`, axioms `propext, Classical.choice, Quot.sound` only
(checked with `#print axioms`). Not reviewed by a human; not verified by the lead yet.
No existing file was edited. New files (all in `CutoffRigidity/Extra/`, namespace `CutoffRigidity.Paper`):

* `OUFisher.lean` (363 lines): `ou_fisher_information` (+ helpers `ou_law_of_isLangevin`, `fisherInfo_gaussian_quadratic`,
  `multivariateGaussian_smul_one_eq_withDensity`, `pi_eq_withDensity_of_coordinates'`, ...)
* `Normalization.lean` (116): `normalization_cutoff` (+ `hasCutoff_timeChange`, `worst_timeChange`, `mixingTime_timeChange`)
* `Temperature.lean` (242): `temperature_bakry_emery`, `temperature_cd` (+ `cd_euclid_iff`, ...)
* `HeatKernelScore.lean` (64): `heat_kernel_score`

## What is proved

1. `ou_fisher_information`: exactly the displayed claims. For `V = ρ|x|²/2 + c` (c is forced by IsProbabilityMeasure in
   `IsLangevin`, no extra hypothesis), `t>0`: law = `N(e^{-ρt}x₀, ((1-e^{-2ρt})/ρ) I_d)`; there is a smooth `u` with
   `law = (gibbs V).withDensity e^u`, `u = log dμ_t/dμ` a.e., `∇u = a_t x + b_t x₀` with
   `a_t = ρ - ρ/(1-e^{-2ρt})`, `b_t = ρ e^{-ρt}/(1-e^{-2ρt})` (explicitly free of d and x₀);
   `fisherInfo V law = ofReal (ρ d e^{-4ρt}/(1-e^{-2ρt}) + ρ² e^{-2ρt}|x₀|²)`.
   Uses the project bridges (`IsLangevinSolution.ae_eq_langevinProcess`, Mehler law
   `quadratic_langevinSolution_vector_hasLaw`, `fisherInfo_eq_relativeFisherInformation`,
   `relativeFisherInformation_exponential`); the Lebesgue density of the isotropic Gaussian was not in Mathlib, proved here.
2. `normalization_cutoff`: generic cutoff equivalence for every worst-case profile (any divergence δ_n, any S_n), mixing time
   scaling `t₀^{(α)} = t₀/α` (in ℝ≥0∞), and invariance of the product condition (κ -> ακ, in the exact form of Theorem 1.7).
   Time change is `X^{(α)} x₀ u = X x₀ (α.toNNReal * u)`; `worst_timeChange` shows `worst(X^α)(s) = worst(X)(α s)`.
3. `temperature_bakry_emery`: with `L_σ f = σ²Δf - ∇V·∇f`, `Γ(f,g)=σ²⟨∇f,∇g⟩`, `Γ₂(f)=½L_σΓ(f,f)-Γ(f,L_σ f)` (defined inline in
   the statement): (i) `Γ(f)=σ²|∇f|²` and `Γ₂(f)=σ⁴Σ_{ij}(∂ᵢ∂ⱼf)²+σ² Hess V(∇f,∇f)` for smooth f; (ii) infinitesimal invariance of
   `e^{-V/σ²}dx`: `∫ L_σ f d gibbs(V/σ²) = 0` for C² compactly supported f; (iii) for every ρ, `ρΓ ≤ Γ₂` for all smooth f iff
   `Hess V ≥ ρ I` (free of σ).
   `temperature_cd`: the manuscript's remark (α=σ², V/σ²): `CutCur.CD (Rd d) (ρ/σ²) (V/σ²) ↔ Hess V ≥ ρ`
   (uses the project's flat-space Bochner identity `Riemann.Witness.gamma2_euclid`; elaborates without extra options).
4. `heat_kernel_score` (the "trivial calculus remark"): for `ν = p dx`, `p>0` continuous differentiable, `ν ≪ gibbs V`,
   `u = log p + V` is a.e. `log dν/dμ` and `∇u = ∇log p + ∇V`.

## What is NOT formalized (honest list)

* `eq:loggradbound` (conjectural; skipped as instructed) and the consequent bound on I(μ_t|μ).
* Normalization: the claim "X^{(α)} solves dX = -α∇V dt + √(2α) dB, generator αL" is NOT formalized (needs Brownian scaling
  `α^{-1/2}B_{αt}` is a standard Brownian motion for the project's `IsStdBrownian`; not in the project nor in Mathlib).
  The cutoff/mixing-time/product-condition statements are purely in terms of the time-changed laws and do not need it.
  Also, "κ becomes ακ" is taken as the definition of the curvature constant of αL (algebraic invariance proved).
* Temperature: invariance of the law along the SDE flow for `dY=-∇Vdt+√2σ dB` is stated only infinitesimally
  (`∫L_σ f dμ_σ = 0`); the SDE with temperature is not among the Challenge definitions (IsLangevin has σ=1), and proving
  invariance for general (non-convex) V needs non-explosion/uniqueness, not available. Normalization `Z_σ` is not
  mentioned (invariance of `gibbs(V/σ²)` is homogeneous in the constant).
  "In particular the cutoff critical time is free of σ" is a consequence of Section normalization applied with α=σ², V/σ², not
  separately formalized (needs the SDE time-change claim above).

## Proposed Challenge text (unqualified names; paste in `namespace CutCur`, `theorem ... := by sorry`)

```lean
/-- **Fisher information and the heat kernel (Section 4.1, OU case).** For `V(x) = ρ|x|²/2 + c`
(the constant is forced by `μ = e^{-V}` being a probability measure) and `t > 0`: the law `μ_t` of `X_t` from `x₀` is
`𝒩(e^{-ρt}x₀, ((1-e^{-2ρt})/ρ) I_d)`; `μ_t` has a smooth log-density `u = log dμ_t/dμ` with
`∇u(x) = a_t x + b_t x₀`, where `a_t`, `b_t` depend neither on `d` nor on `x₀`; and
`I(μ_t | μ) = ρ d e^{-4ρt}/(1-e^{-2ρt}) + ρ² e^{-2ρt}|x₀|²`. -/
theorem ou_fisher_information {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {ρ c : ℝ} (hρ : 0 < ρ)
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) B P X)
    (x₀ : Rd d) {t : ℝ} (ht : 0 < t) :
    let V := fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c
    let μt := P.map (X x₀ t.toNNReal)
    μt = multivariateGaussian (Real.exp (-ρ * t) • x₀)
        (((1 - Real.exp (-2 * ρ * t)) / ρ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
      (∃ u : Rd d → ℝ, ContDiff ℝ ∞ u ∧
        μt = (gibbs V).withDensity (fun x => ENNReal.ofReal (Real.exp (u x))) ∧
        (∀ᵐ x ∂gibbs V, u x = Real.log (μt.rnDeriv (gibbs V) x).toReal) ∧
        ∀ x, gradient u x = (ρ - ρ / (1 - Real.exp (-2 * ρ * t))) • x +
          (ρ * Real.exp (-ρ * t) / (1 - Real.exp (-2 * ρ * t))) • x₀) ∧
      fisherInfo V μt = ENNReal.ofReal
        (ρ * d * Real.exp (-4 * ρ * t) / (1 - Real.exp (-2 * ρ * t)) +
          ρ ^ 2 * Real.exp (-2 * ρ * t) * ‖x₀‖ ^ 2) := by
  sorry

/-- **Normalization (Section 4.2).** ... (docstring as in `Extra/Normalization.lean`) -/
theorem normalization_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n} {S : ∀ n, Set (Rd n)}
    {α : ℕ → ℝ} (hα : ∀ n, 0 < α n) :
    let Xα := fun n (x₀ : Rd n) (u : ℝ≥0) => X n x₀ ((α n).toNNReal * u)
    (∀ (δ : ∀ n, Measure (Rd n) → ℝ≥0∞) (t : ℕ → ℝ) (b a : ℝ≥0∞),
      HasCutoff (fun n => worst (P n) (X n) (S n) (δ n)) t b a ↔
        HasCutoff (fun n => worst (P n) (Xα n) (S n) (δ n)) (fun n => t n / α n) b a) ∧
    (∀ (μ : ∀ n, Measure (Rd n)) (η : ℝ) (n : ℕ),
      mixingTime (P n) (Xα n) (μ n) (S n) η =
        mixingTime (P n) (X n) (μ n) (S n) η / ENNReal.ofReal (α n)) ∧
    (∀ (μ : ∀ n, Measure (Rd n)) (η : ℝ) (κ : ℕ → ℝ),
      Tendsto (fun n => α n * κ n * (mixingTime (P n) (Xα n) (μ n) (S n) η).toReal) atTop atTop ↔
        Tendsto (fun n => κ n * (mixingTime (P n) (X n) (μ n) (S n) η).toReal) atTop atTop) := by
  sorry
```

For `temperature_bakry_emery`, `temperature_cd`, `heat_kernel_score` the statements are in
`Extra/Temperature.lean` / `Extra/HeatKernelScore.lean`: drop the `CutCur.` prefixes (`CutCur.Rd` -> `Rd`,
`CutCur.laplacian` -> `laplacian`, `CutCur.gibbs` -> `gibbs`, `CutCur.CD` -> `CD`) and put `sorry` as proof.
(Note: in the `Paper` versions `CutCur.Rd d` is written explicitly; `temperature_cd` needs `CD (Rd d) ...` with the explicit
`F := Rd d` argument, as in the file.)
