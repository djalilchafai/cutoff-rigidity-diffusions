# Independent second audit of theorems 9-12 and the Riemannian definitions (AI, 25 October 2026)

Scope: `euclidean_gaussian_factorization` (Thm 3.1, Rem 3.2), `eigenmap_is_ou` (Lemma 3.3),
`riemannian_wasserstein_estimate` (Thm 1.9 with `IsDiffusionSemigroup`), `riemannian_gaussian_splitting`
(Thm 3.6, Lemma 3.7, strengthened form), and the definitions `IsWeightedVolume`, `CD`, `mSpectralGap`,
`IsMEigenfunction`, `mFirstEigenDim`, `mLambda`, `IsDiffusionSemigroup`.
Method: statements and definitions read against `cutcur-lean.tex` (T:589-735, 864-945, 1322-1400), plus scratch Lean
checks (below). Proofs were not read to decide fidelity, except that I read the *statements* of `bridge_final`,
`isDiffusionSemigroup_Kk`, `WitnessMain`. This is an AI audit, not a human review.

Disclosure on independence: before writing verdicts I ran a grep of `verification/*.md` for the words "Brownian/OU/exist".
It displayed a few lines of `audit-extra-B/C/D/G.md` (about the Brownian-carrier caveat). They concerned only that caveat,
which I had already identified from the definitions; I did not read `semantic-audit.md` or `audit-extra-D.md` until after
the verdicts below were formed.

Result: **no defect in any of the four statements or in the Riemannian definitions**. Verdicts: 9 faithful with remarks,
10 faithful with remarks, 11 faithful with remarks, 12 faithful.

## Lean checks run (scratch files in the scratchpad dir, nothing in the project modified)

1. `#print axioms` of the four theorems in `Solution`: only `propext, Classical.choice, Quot.sound`.
2. Joint satisfiability of Thm 1.9 *including* the diffusion hypothesis, in Lean: for every `k>0, ρ>0` there are `V, μ, Pt` on `Rd k`
   with `ContMDiff V ∧ IsProbabilityMeasure μ ∧ IsWeightedVolume μ V ∧ CD ρ V ∧ mSpectralGap μ = ρ ∧ IsDiffusionSemigroup V Pt`.
   Proof: `Witness.exists_riemannian_instance` plus `Diff.isDiffusionSemigroup_Kk`. (`WitnessMain` itself excludes the
   semigroup, as its docstring says; this closes that gap at statement level.) Also `mFirstEigenDim = k` there.
3. Euclidean joint satisfiability for Thm 3.1: for `V = gaussPot k ρ` (`k>0`): `ContDiff ℝ 2 V`, `gibbs V` probability,
   `ρ‖z‖² ≤ Hess V (z,z)`, `spectralGap V = ρ`, `firstEigenDim V = k`. All compile.
4. `pp.coercions` on the printed statements: `↑(mFirstEigenDim F μ V) * (1 - √(1-q))^2 / ρ` and `↑k / 2 * Real.log (2*π/ρ)`:
   the ℕ casts are at the leaves, no natural-number division.
5. `#synth NormedAddCommGroup (TangentSpace 𝓘(ℝ,F) x)` returns `instNormedAddCommGroupOfRiemannianBundle...`: the norm/inner product
   used in `mgrad`, `carre`, `mlaplacian`, `chartVolumeDensity`, `mSpectralGap` is the Riemannian metric, not the model-space one
   (no diamond).
6. Mathlib `leviCivitaConnection` is a genuine Levi-Civita connection (`isLeviCivitaConnection_leviCivitaConnection`), arbitrary only
   on non-differentiable fields; `mlaplacian` only ever applies it to `mgrad` of smooth `f`.
7. Mathlib `IsBrownianReal` = pre-Brownian finite-dimensional laws plus a.s. continuous paths.

## 9. `euclidean_gaussian_factorization` (C:300-311; T:871-895, Rem. 3.2). Faithful with remarks

Hypotheses: `V` is `C²`, `gibbs V` probability, `ρ>0`, `Hess V ≥ ρ`, `spectralGap V = ρ`: exactly the manuscript's, and jointly
satisfiable (check 3).
Conclusion: `∃ e m U` with `V = ρ/2 Σ_{i<k₁}(⟨eᵢ,x⟩-mᵢ)² + U`, `U` invariant under the first `k₁` coordinates, `Hess U ≥ ρ` on the
span of the last `d-k₁` vectors (`U = V - quadratic` is `C²`, so the `fderiv` is not junk), and every eigenfunction is
`Σ aᵢ(⟨eᵢ,x⟩-mᵢ)`, `a` supported on `i<k₁`, `|a|²=ρ∫f²`.
Remarks:
* Deviation (sharpening, true): the manuscript's `f = ⟨a,p⟩ + b` is stated with `b = -Σ aᵢmᵢ`. True because `f ⊥ 1` (eigenvalue
  `ρ>0`) and the Gaussian factor is centered at `m`. Not flagged in the docstring but the docstring prints the form.
* `m` for `i ≥ k₁` is unconstrained (irrelevant). The paper's "m is the barycenter" is not asserted (not part of the theorem).
* `k₁ = firstEigenDim V` is the Lean (classical `C²`-eigenfunction) `E₁`; if it were smaller than the spectral `E₁` the splitting
  claim would be false, not weaker, so the kernel-checked proof is the real evidence that the two agree. Fidelity of the definition
  itself: harmless (module docstring remark).
* `d = 0`: `spectralGap = sInf ∅ = 0 ≠ ρ`, so excluded by `hgap`. No vacuity elsewhere.
* Existential is not trivializable: `e, m` determine `U = V - quadratic`, and the quadratic part has the right rank `k₁`.
No junk values found.

## 10. `eigenmap_is_ou` (C:317-326; T:910-937). Faithful with remarks

Hypotheses: `IsLangevin` (V `C²`, `gibbs` probability, `B` standard BM, `X x₀` solves the SDE for every `x₀`), `RigidCurvature`
(`λ₁>0`, `Hess ≥ λ₁`), `T` an orthonormal basis of `E₁` by `C²` representatives. That is the setting of Thm 3.1 + Def 1.8.
Conclusion: `∃ β` standard BM on `ℝ^{k₁}` (same `Ω,P`), and for every `x₀`, a.s., for all `t`:
`T(X_t) = T(x₀) - ρ∫₀ᵗ T(X_s)ds + √(2ρ) β_t`. This is `dY = -ρY dt + √(2ρ)dβ`, i.e. generator `ρΔ - ρ y·∇`
(`½·2ρ = ρ`): matches the paper's "generator `ρΔ - ρx·∇`". Hand check of the mathematics: `T = A(x-m)`, `AAᵀ = ρI`,
`A∇U = 0`, so `dT(X) = -ρT dt + √2 A dB`, and `β = ABt/√ρ` is a standard BM, independent of `x₀`: the single `β` for all `x₀`
is correct, and `β` is determined by `X`, so the existential is not a free choice.
Remarks:
* Deviation (stronger, pathwise representation instead of a law/generator statement); no filtration/adaptedness is stated, which is not
  needed to identify the law. Fine.
* The integral of an a.s. continuous integrand: no junk.
* Conditional on the carrier `hL`: needs a Brownian motion, not instantiable inside Lean at this Mathlib revision (residual risk, flagged
  in the docstring of `IsLangevin`). Mathematically non-vacuous (Wiener process + strong solutions for `C²` monotone drift).

## 11. `riemannian_wasserstein_estimate` (C:813-826; T:685-706). Faithful with remarks

Hypotheses: `V` smooth, `μ` probability with `IsWeightedVolume`, `ρ>0`, `CD ρ V`, `mSpectralGap = ρ`, `IsDiffusionSemigroup`, plus the
section instances (smooth manifold without boundary, Riemannian bundle, `IsRiemannianManifold`, `ConnectedSpace`, `CompleteSpace`):
the manuscript's. Complete for `edist` = Cauchy complete = geodesically complete (Hopf-Rinow).
Conclusion: for all nonempty `S`, `lower(sup Λ) ≤ sup W ≤ e^{-2ρt} sup ∫d²dμ`, with `lower(Λ) = (q/ρ)Λ + k₁(1-√(1-q))²/ρ`,
`q = e^{-2ρt}`; and for `Λ(m)=0`, `lower(ρR²) ≤ sup_{d(m,x₀)≤R} W`. Checked: operator precedence (`A ≤ B ∧ C ≤ D` inside the
paren), `1-q ≥ 0` so `√` is genuine, `ofReal` truncation harmless (arguments positive), `Λ = ⊤` gives `⊤` (correct since `q/ρ>0`),
`W = wasserstein2^2` with `(x^{1/2})^2 = x` in `ℝ≥0∞`, coupling set nonempty (product measure) so no `⨅ ∅ = ⊤` junk, `Pt t x₀` is a
probability measure so `W₂` is not junk. `W₂ = ⊤` would only occur without second moments, which fails under the hypotheses.
Definitions:
* `CD`: `Γ(f)=|∇f|²`, `Γ₂ = ½𝓛Γ - Γ(f,𝓛f)` matches the paper (`Γ₂(f,f)`); quantified over all smooth `f`, pointwise: equivalent to
  `Ric + Hess V ≥ ρg` (any tangent vector is the gradient of some smooth global `f` at `x`). Fine.
* `IsWeightedVolume`: in each chart, push-forward of `μ|source` = `e^{-V∘ψ}√det(g_ij) dz` on `target`, `g_ij` the Gram matrix of
  `dψ(e_i)` for an orthonormal basis of `F` in the Riemannian metric (check 5). Charts cover `M`, so `μ` is uniquely determined; the map
  is `AEMeasurable` (continuous on a measurable source), no `map = 0` junk. Volume on `F` is the Haar measure normalised to the
  orthonormal basis. Correct; flat case reduces to `e^{-V}dx` (witness).
* `mSpectralGap`: `inf ∫|∇f|²/Var f` over smooth compactly supported non-constant `f`. Correct (core of the Dirichlet form on a complete
  weighted manifold). `sInf ∅ = 0` junk is excluded by `hgap` and `ρ>0` (point manifold and `dim F=0` die this way; so `0<finrank F` is
  not needed here, unlike in `mSpectralGap_ge_of_CD`, where the gap is the conclusion). Bounded below by 0: no `sInf` junk for unbounded sets.
* `IsMEigenfunction`/`mFirstEigenDim`/`mLambda`: smooth `L²` pointwise eigenfunctions; `finrank` of their span in `L²(μ)`. With complete `M`
  (essential self-adjointness) this is the paper's `E₁`; finiteness holds (discrete spectrum), so `finrank` is not the `0`-junk for infinite
  dimension. `mLambda` quantifies `T : Fin k₁ → M → ℝ` with orthonormal `L²` coordinates: exactly `S_{F₁}`; two continuous representatives
  agree everywhere since `μ` has full support.
* `lower` formula with `mFirstEigenDim*(1-√(1-q))²/ρ`: identical to the paper's `k₁(1-√(1-e^{-2ρt}))²/ρ`; cast of `k₁` verified.
`IsDiffusionSemigroup` (the main adversarial point): conditions are Markov kernel for each `t`, `Pt(s+t) = Pt t ∘ₖ Pt s`, and the integrated
Dynkin/Kolmogorov identity for smooth compactly supported `f`.
* No hidden junk exploit. `𝓛f` is smooth compactly supported, hence bounded. If `s ↦ Pt s(𝓛f)(x)` were non-measurable the interval integral
  would be `0` and force `Pt t f(x) = f(x)`; the frozen semigroup `Pt = Kernel.id` fails (`t𝓛f(x) ≠ 0`), and in any case:
* The project theorem `bridge_final` (`DiffPerron6.lean:39`) states: for complete connected `M`, smooth `V`, finite `μ`, `IsWeightedVolume`,
  every `Pt` with `IsDiffusionSemigroup F V Pt` satisfies `∀ t x, Pt t x = Kk F hV hμ t x`, and `isDiffusionSemigroup_Kk` (`DiffKer9.lean:92`)
  says `Kk` itself satisfies it. So the class is exactly one semigroup and no pathological instance can exist, including via junk
  integrals (the uniqueness quantifies over every `Pt` satisfying the definition literally). `Kk` is the transition semigroup of the
  conservative minimal diffusion (the `Kk` kernel is `p_t(x,·)μ` for `t>0`, `δ_x` for `t=0`, Markov), which is `Law(X_t^x)` of (1.26).
  I verified by Lean that the hypotheses of `bridge_final` are those of the theorem (it needs strictly fewer: neither `ρ>0` nor `CD`).
* Docstring remark: it says uniqueness holds "under the standing hypotheses (completeness, CD(ρ,∞), ρ>0)". True but understated: `bridge_final`
  needs only completeness, connectedness, finite `μ`, smooth `V`. Cosmetic; not wrong.
* Joint satisfiability including `Pt`: check 2.
Remarks on deviations: `V` smooth added (needed for `𝓛`, harmless); the SDE (1.26) replaced by the semigroup (paper: "We shall not make use of
(1.26)"); the ball refinement stated as the inequality (as in the Euclidean theorem). No unflagged deviation beyond these.

## 12. `riemannian_gaussian_splitting` (C:834-857; T:1333-1378). Faithful

Existential structure. `F'`, `N` with all the structure (charted, smooth manifold, Riemannian bundle, smooth bundle, `IsRiemannianManifold`, Borel),
`V', μ'`, and `Φ : M ≃ₘ^∞ ℝ^{k₁} × N` smooth diffeomorphism for the product model. Trivial/degenerate choices do not make it vacuous:
* `Φ` a diffeomorphism forces `dim F = k₁ + dim F'`, so `N` cannot absorb or shrink the Euclidean factor; `k₁` is the fixed
  `mFirstEigenDim`, `N` nonempty (`ConnectedSpace`).
* Distances: `d_M(x,y)² = |p-p'|² + d_N(y,y')²` globally. This is the Riemannian product distance (not the Prod-instance sup distance), and by
  Myers-Steenrod a smooth distance isometry is a Riemannian isometry. Equal in strength to the manuscript's isometry.
* Measure: `μ.map Φ = N(0, ρ⁻¹I_{k₁}) ⊗ μ'` with `μ'` probability (so `Prod` is the genuine product; `ρ>0` so the matrix is positive definite, no Dirac junk).
* Potential identity `V x = ρ|p|²/2 + V'(y) + (k₁/2)log(2π/ρ)`: independently re-derived from the Gaussian density `exp(-ρ|p|²/2-(k/2)log(2π/ρ))`;
  correct sign and constant; it is a real constraint because `V'` is determined by `μ'` via `IsWeightedVolume`.
* Factor: `V'` smooth, `μ'` probability, `IsWeightedVolume F' μ' V'`, `CD F' ρ V'`, `ConnectedSpace N`, `CompleteSpace N` (w.r.t. the existentially
  chosen `EMetricSpace N`, which is the Riemannian distance of the same structure): exactly the manuscript's list (smooth, connected, complete,
  boundaryless, `CD(ρ,∞)`, `μ'=e^{-V'}vol`).
* Lemma 3.7: for every `IsMEigenfunction F μ V ρ f` there is `a` with `f = ⟨a,p⟩` everywhere and `|a|² = ρ∫f²` (no constant `b`: true, centered
  Gaussian); orthogonal eigenfunctions with given vectors `a,b` have `⟨a,b⟩=0`. The last clause is a restatement of
  `∫fg = ⟨a,b⟩/ρ` but matches the lemma's wording. Eigenvalue is `λ₁ = ρ` as in the paper.
* The case `N` a point (the witness) is the trivial splitting `Φ = id × pt`; satisfiable (check 2 and `WitnessMain.splitting_applies`).
No unflagged deviation.

## Agreements/disagreements with the first audit (read after forming the above)

`semantic-audit.md` items 9-12 and `audit-extra-D.md` section 8: full agreement on all four verdicts, on the pathwise strengthening in Lemma 3.3, on
the `b = -Σaᵢmᵢ` absorption, on the Myers-Steenrod remark, on `k/2` cast, on the constant `(k/2)log(2π/ρ)`, on connected/complete `N`, on the
carrier-existence residual risk, and on the junk analysis of the Dynkin integral. Differences or additions of mine:
* `semantic-audit.md` R2 said joint non-vacuity of the Riemannian hypotheses was unwitnessed and, for `IsDiffusionSemigroup`, that uniqueness was
  "a claim in the project which I did not re-audit". Now: the witness exists (WitnessMain), and I checked in Lean the *combined* hypotheses of Thm 1.9 including
  `Pt` (check 2), and read the statements of `bridge_final`/`isDiffusionSemigroup_Kk`, so the uniqueness claim is a kernel-checked theorem with the stated
  hypotheses. `semantic-audit.md` item 12 (original) said `N` connected/complete was implicit; now explicit (the second audit's `audit-extra-D` agrees).
* I confirmed the instance resolution for the tangent-space norm (no model-space/bundle diamond) and the true Levi-Civita connection, which the earlier
  reports asserted without a Lean check (the first states it by reading Mathlib).
* New minor observation: the docstring of `IsDiffusionSemigroup` over-states the hypotheses needed for uniqueness (cosmetic).
* Not independently re-verified: that the `Kk` semigroup is the *same* object as Law of the SDE (1.26) (this is classical: conservative minimal diffusion;
  uniqueness among Markov kernels satisfying the Dynkin identity makes any other reading coincide).
