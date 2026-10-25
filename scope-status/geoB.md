# scope-status/geoB: Riemannian / geometric claims with no Challenge theorem

All scratch files: `/tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/`
(`k1.lean`, `lsi.lean`, `t17.lean`, `sph.lean`, `sph2.lean`, `dys.lean`), all checked with `lake env lean` from the project root.
`k1.lean` and `lsi.lean` contain COMPLETE proofs (no sorry). The others are statements only (sorry).

Summary table (recommended order of work):

| Order | Item | Verdict | Size |
|---|---|---|---|
| 1 | (1) Riemannian `1 ≤ k₁ ≤ dim` | do it (proved in scratch, needs `λ₁ = ρ`) | about 10 lines in Challenge, 0 more in Solution (copy scratch) |
| 2 | (2) Riemannian Poincaré + LSI (constant 2/ρ) + Lichnerowicz `λ₁ ≥ ρ` | do it (proved in scratch) | about 15 lines. Isoperimetry: skip |
| 3 | (5) Dyson-OU on the Weyl chamber | do a weaker faithful version (static: eigenfunction and Poincaré on the chamber); process-level: skip | 1.5k-4k lines, 1-3 agent-weeks, medium risk |
| 4 | (4) Sphere | do at most a weak static version, or skip; cutoff: infeasible | 5k-10k lines for the static part |
| 5 | (3) Theorem 1.7 on manifolds | skip (infeasible in reasonable time) | 10k+ lines, months |

---------------------------------------------------------------------------------------------------

## Item 1: `k₁` bounds on a Riemannian manifold (manuscript L633-636)

### 1. What the manuscript actually claims
L633-636: "when ρ > 0 the spectrum of 𝓛 is discrete and the spectral gap λ₁ is always an eigenvalue of -𝓛 [GMS15, Prop 6.7].
Moreover, the eigenfunctions associated to the spectral gap are continuous." The manuscript does NOT state `1 ≤ k₁ ≤ dim M`
on manifolds. `k₁ ≤ d` is only the Euclidean Remark 1.2 (L154, citing BaKl20), and it is already in Challenge as
`eigenspace_dim_and_lambda`. The user's brief says "1 ≤ k₁ ≤ dim (L633-636)"; that is a natural analogue, but it is NOT a
manuscript claim, and it is FALSE without `λ₁ = ρ`: on the round sphere S^d, `λ₁ = d` and `k₁ = d+1 > d = dim`. So the faithful
statement of the first claim ("λ₁ is an eigenvalue", i.e. `1 ≤ k₁`, with `k₁` finite) must not carry `k₁ ≤ dim` unless
`λ₁ = ρ`. The Riemannian theorems of the paper (Thm 1.9) all have `λ₁ = ρ`, where `k₁ ≤ dim` is true and is used implicitly.

### 2. Draft statement (PROVED in `k1.lean`, 60 lines, no sorry)
```lean
theorem riemannian_k1_bounds {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) :
    1 ≤ mFirstEigenDim F μ V ∧ mFirstEigenDim F μ V ≤ Module.finrank ℝ F
```
(standing Riemannian variables exactly as in `riemannian_wasserstein_estimate`). Hypotheses added relative to the manuscript
sentence: `hgap` (to get `k₁ ≤ dim`; also what the project's finiteness proof uses). It is faithful to what is true. Faithful Challenge
statement: yes (same variables/hypotheses as Theorem 1.9). Proof: `1 ≤` is `gap_attained_of_LSI` with `lsi_of_CD`; `≤ dim F` uses
`finiteDimensional_eigenClasses`, `mFirstEigenDim_eq_finrank`, the injection `f ↦ mgrad f x₀` into the tangent space
(`eigenfunction_eq_zero_of_grad_zero`, `manifold_eigenfunction_parallel_gradient`) and `LinearMap.finrank_le_finrank_of_injective`,
`LinearMap.finrank_range_le`. The statement `1 ≤ k₁` is already used inside `riemannian_wasserstein_estimate` (hpos) so it is
not new mathematics.

### 3. What exists / is missing
Exists: all of the above names (`CutoffRigidity/Riemann/EigenFinite.lean`, `DiffGapAttained2.lean`, `DiffLSI.lean`).
Missing: (a) the version WITHOUT `hgap` (general `λ₁ ≥ ρ > 0`, claim "λ₁ is an eigenvalue, eigenspace finite-dimensional").
In the project, `finiteDimensional_eigenSub` and `gap_attained_of_compact` take `hgap : mSpectralGap = ρ` and
`hCD` (parallel-gradient rigidity), so the general case needs a refactor: finite-dimensionality of E₁ from total boundedness of
energy balls (`Qball_totallyBounded_of_tail` + `tail_of_LSI` exist) and attainment with `ρ := λ₁` in `poincare_D` (the lemma
`poincare_D` needs only `hgap`, not `hCD`, but its callers include `hCD` through `include`). Estimate 200-400 lines, 1 agent, 2-3 days,
low-medium risk. (b) The literal "spectrum is discrete" (compact resolvent, eigenbasis of L²(μ) of smooth eigenfunctions with
eigenvalues → ∞): the compact resolvent core exists (Rellich, Friedrichs), but Mathlib has no spectral theorem for compact
self-adjoint operators on infinite-dim Hilbert spaces; the project has a custom `exists_eigen_of_compact`. A faithful
statement "∃ orthonormal basis of L²(μ) of smooth eigenfunctions, eigenvalues tending to +∞" needs iterating on orthocomplements, 500-1000
lines, 1 agent-week. Continuity of eigenfunctions: already built into `IsMEigenfunction` (smooth by definition).

### 4-5. Effort and recommendation
Do the proved statement (about 0 further work: copy scratch into Solution, add 8 lines to Challenge). The no-`hgap` variant and the
eigenbasis statement are optional upgrades, in that order.

---------------------------------------------------------------------------------------------------

## Item 2: Riemannian Poincaré, LSI (constant 2/ρ), Bakry-Émery consequences (L618-632)

### 1. What the manuscript claims
L623-632: `Ric + Hess V ≥ ρ g` implies `λ₁ ≥ ρ` (Bakry-Émery, Lichnerowicz when unweighted); "the Bakry-Émery approach implies
stronger functional inequalities, such as a logarithmic Sobolev inequality, and a Gaussian isoperimetric inequality". NO constants
(2/ρ, 1/ρ), no exponential decay and no Talagrand statement are written for manifolds; the constants 1/ρ and 2/ρ are the
standard ones and match the project's `LSI` predicate (`Ent(f²) ≤ (2/ρ)∫Γ f`) and the Euclidean Challenge theorem
`optimal_lsi_twice_pi`/`talagrand_logSobolev` (constant 2ρ in H ≤ I/(2ρ)). The grep for "isoperim|concentration" in the tex finds only L632.

### 2. Draft statement (PROVED in `lsi.lean`, no sorry)
```lean
/-- Entropy on a general measurable space (Challenge's `entropyOf` is Rd-specific; a generalization is needed). -/
noncomputable def entropyM (μ : Measure M) (g : M → ℝ) : ℝ :=
  (∫ x, g x * Real.log (g x) ∂μ) - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

theorem riemannian_poincare_lsi {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) :
    ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ ∧
      entropyM μ (fun x => f x ^ 2) ≤ 2 / ρ * ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ
```
Proof (6 lines): `poincare_of_CD`, `lsi_of_CD`, and `carre f f = ‖mgrad f‖²` pointwise. Test class: smooth compactly supported
(same as the project and `mSpectralGap`; the Euclidean Challenge uses smooth bounded Lipschitz; both are standard). Faithful
Challenge statement: yes, as a conservative reading of "implies LSI". Companion (also proved internally, statement only needs
wrapping): `mSpectralGap F μ ≥ ρ` is `mSpectralGap_ge_of_CD'` (hypothesis `0 < finrank F` to add; the project statement
is `ρ ≤ mSpectralGap F μ`). That is the literal "λ₁ ≥ ρ" claim at L627.

### 3. Missing
* Riemannian Fisher information, relative entropy decay, Talagrand and `H ≤ I/(2ρ)` with arbitrary ν: no Riemannian Fisher
  functional is defined. Not claimed by the manuscript for manifolds. Skip.
* Exponential decay `Ent(P_t f) ≤ e^{-2ρt}Ent(f)`: not claimed; the project proves pieces (`DiffLSIBruijn`, `DiffLSIFisher`,
  `BEStrong`) but there is no packaged statement. If wanted: about 200-400 lines (kernel `Kk` plus de Bruijn plus Gronwall). Not recommended (not in manuscript).
* Gaussian isoperimetry (Bakry-Ledoux / Bobkov): needs Gaussian isoperimetric profile `φ∘Φ⁻¹`, sets of finite perimeter or
  Minkowski content, plus Bobkov's functional inequality from the semigroup: 3k+ lines, 1-2 agent-months, the statement itself
  needs new definitions (Minkowski content on a manifold with distance `edist`). Faithful but heavy. Recommend skip; mention as
  prose remark in the manuscript is enough ("such as" is not a precise claim).

### 4-5. Effort/recommendation
Do the Poincaré+LSI statement and the `λ₁ ≥ ρ` statement (each a few lines on top of proved internals; 1 agent, under a day including
Challenge/Solution wiring and the `entropyM` generalization). Skip isoperimetry and decay.

---------------------------------------------------------------------------------------------------

## Item 3: Theorem 1.7 on Riemannian manifolds (L437-439)

### 1. Claim
L437-439: "We state it in the restricted Euclidean setting for simplicity, but it holds in the Riemannian setting, since it is the
curvature bound and the diffusion property that matter." No proof or precise statement is given. The natural statement: for a sequence
of weighted complete manifolds `(M_n, g_n, μ_n = e^{-V_n} vol)` with `CD(κ_n, ∞)`, `κ_n > 0`, diffusion semigroups `P_t^{(n)}`, a
nonempty set `S_n` of initial points, `t₀^{(n)} = inf{t : sup_{S_n} TV(P_t δ_x, μ_n) ≤ η}` finite eventually, `κ_n t₀^{(n)} → ∞`,
there is cutoff of TV and relative entropy at `t₀^{(n)}` (and Fisher/W₂ under `liminf κ_n > 0`, `t₀ → ∞`; for W₂ the
manuscript's Riemannian wording would also need a Riemannian Fisher functional, which does not exist in the project).

### 2. Draft statement (elaborates, `t17.lean`; TV and entropy parts only, no Fisher/W₂)
```lean
noncomputable def mixingTimeK {M : Type} [MeasurableSpace M] (Pt : ℝ≥0 → Kernel M M) (μ : Measure M)
    (S : Set M) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ⨆ x₀ ∈ S, ENNReal.ofReal (tvDist (Pt t x₀) μ) ≤ ENNReal.ofReal η), (t : ℝ≥0∞)

theorem riemannian_product_condition_cutoff   -- sequences F n, M n with all standing instances as `∀ n`
    {V} {μ} [∀ n, IsProbabilityMeasure (μ n)] {Pt : ∀ n, ℝ≥0 → Kernel (M n) (M n)} {κ : ℕ → ℝ} {S} {η : ℝ}
    (hV : ∀ n, ContMDiff … ∞ (V n)) (hμ : ∀ n, IsWeightedVolume (F n) (μ n) (V n))
    (hP : ∀ n, IsDiffusionSemigroup (F n) (V n) (Pt n)) (hκ : ∀ n, 0 < κ n ∧ CD (F n) (κ n) (V n))
    (hS : ∀ n, (S n).Nonempty) (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTimeK (Pt n) (μ n) (S n) η
    (∀ᶠ n in atTop, t₀ n < ⊤) → Tendsto (fun n => κ n * (t₀ n).toReal) atTop atTop →
    ∀ ε, 0 < ε → ε < 1 → (TV before → 1) ∧ (TV after → 0) ∧ (KL before → ⊤) ∧ (KL after → 0)
```
(`tvDist`, `klDiv`, `IsDiffusionSemigroup`, `CD`, `IsWeightedVolume` all exist; the full text is in `t17.lean`). Faithful: yes for the
TV/entropy half; the Fisher/W₂ half needs Riemannian Fisher information `I` and `wasserstein2` for `Pt` (the latter exists).

### 3. What exists / missing, why infeasible
The Euclidean theorem is proved with about 16.5k lines of `Langevin*.lean` plus `Salez*.lean`, `ProductCondition*.lean`, `Varentropy`,
`WeakLogLikelihoodPoincare`, etc. Only the purely arithmetic parts (`SalezDiscreteEntropyWindow`, `SalezGeometricPartition`,
`reciprocal_increment_ge_of_quadratic_drop`) are dimension-free and reusable on a manifold. Not available on the manifold side:
positive-time finiteness of entropy and Fisher information from a point mass (Harnack/log-Harnack, Wang), entropy-drop identity
between positive times with a Riemannian Fisher information, the varentropy bound via local Poincaré applied to log of the
transition density (weak domain approximation), TV continuity/monotonicity of the profile, conservativity-based Markov
properties, Bakry-Émery `Γ₂`-based Fisher contraction (the project has `BEStrong` and de Bruijn, which supply part of it).
Plus the manuscript's own gap: the TV cutoff is cited from [Salez25, Cor. 1] for non-negatively curved diffusions, whose
proof also uses properties of the discrete/continuous-time Markov semigroup in a non-manifold framework. Estimate: 10k-20k
lines, several agent-months, high risk (Harnack inequalities on manifolds under `Ric + Hess V ≥ κ`, with unbounded `V` and `Ric`).
Not feasible at this revision on a reasonable budget.

### 5. Recommendation
Skip. If a token gesture is required: put the draft statement above only as an unproved remark. Do it last (or never).

---------------------------------------------------------------------------------------------------

## Item 4: Sphere claims (L710-713)

### 1. Claim
"For the d-dimensional unit sphere, we have ρ = d-1 and λ₁ = d, so the abstract theorem does not apply. Yet cutoff does occur, and
moreover λ₁/ρ → 1." Four claims: (a) `Ric = (d-1) g` so best `ρ = d-1`; (b) `λ₁ = d` for uniform measure; (c) `d/(d-1) → 1`
(trivial arithmetic); (d) Brownian motion on S^d has cutoff (literature: Saloff-Coste / Lachaud for large d). (d) has no statement
in the manuscript beyond "cutoff does occur" without a time scale or a metric; also no proof or reference is given at that line.

### 2. What Mathlib provides (checked)
* `Mathlib/Geometry/Manifold/Instances/Sphere.lean`: `EuclideanSpace.instChartedSpaceSphere`, `instIsManifoldSphere`
  (`IsManifold (𝓡 n) ∞ (sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)`, checked by `#synth` in `sph.lean`), stereographic charts,
  `mfderiv_coe_sphere_injective`, `range_mfderiv_coe_sphere`, `contMDiff_coe_sphere`, `sphere.compactSpace`.
* Missing (checked): `RiemannianBundle` on the sphere (`#synth` FAILS), `IsRiemannianManifold` (a hand-built `EMetricSpace` with the geodesic
  distance `arccos⟪x,y⟫` would be needed: the subtype's chordal metric is NOT the Riemannian distance, so
  `IsRiemannianManifold` fails for the existing metric), `ConnectedSpace` instance on the sphere (`#synth` FAILS; lemma exists in
  `Analysis/Normed/Module/Connected.lean`), spherical harmonics (none in Mathlib), Ricci curvature (none; only Levi-Civita connection
  `CovariantDerivative.leviCivitaConnection`, used by the project's `mlaplacian`/Hessian), surface measure on the sphere in the chart
  form `IsWeightedVolume` (Mathlib has `Measure.toSphere`, not related to chart densities).
* The project: `CD`, `mSpectralGap`, `IsWeightedVolume`, `mgrad`, `lsi_of_CD`, but all for abstract `M`; no instance other than flat `Rd k`
  (`WitnessEigen.lean`, `Gaussian` witness).

### 3. Draft statement (elaborates, `sph2.lean`): sphere presented through an isometric diffeomorphism
```lean
theorem sphere_curvature_gap {d : ℕ} (hd : 2 ≤ d) (hF : Module.finrank ℝ F = d)
    (Φ : M → EuclideanSpace ℝ (Fin (d + 1))) (hΦ : ∀ x, ‖Φ x‖ = 1)
    (hΦs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) ∞ Φ)
    (hΦi : ∀ x (v w : TangentSpace 𝓘(ℝ, F) x), ⟪v, w⟫ = ⟪mfderiv … Φ x v, mfderiv … Φ x w⟫)   -- induced metric
    (hΦb : Function.Bijective (fun x => (⟨Φ x, _⟩ : sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ (0 : M → ℝ)) :
    CD F ((d : ℝ) - 1) (0 : M → ℝ) ∧ (∀ ρ, (d : ℝ) - 1 < ρ → ¬ CD F ρ (0 : M → ℝ)) ∧ mSpectralGap F μ = d
```
(`M` any complete connected Riemannian manifold satisfying the standing hypotheses; the claim is then about every such model of
the round sphere. Caveat: the theorem is only non-vacuous after exhibiting one such `M`, which is the expensive instance
construction below.) Faithful for (a) and (b); (c) is arithmetic and (d) cannot be stated meaningfully.

### 4. Cost
* Instance for the round sphere (type synonym with geodesic `EMetricSpace`, `RiemannianBundle` from the ambient inner product through
  `mfderiv_coe_sphere_injective`, `IsContMDiffRiemannianBundle`, `IsRiemannianManifold` including the lower bound
  `pathELength ≥ arccos`, `CompleteSpace`, `ConnectedSpace`, `MeasurableSpace`/`BorelSpace`): 1500-3000 lines, high risk (geodesic distance).
* Measure `μ` with `IsWeightedVolume` (chart density `(2/(1+|z|²))^d` in stereographic charts; the normalized surface measure; probability): 800-1500 lines.
* `CD(d-1,∞)` (Γ₂ ≥ (d-1)Γ with the project's `carre2` defined through Mathlib's Levi-Civita connection on the abstract manifold):
  requires computing the Levi-Civita connection of the induced metric (Gauss formula/second fundamental form `II(v,w) = -⟨v,w⟩ x`),
  the Bochner formula on the sphere with the project's `mlaplacian`, and the sharpness `¬CD ρ` for `ρ > d-1`: 2000-4000 lines, very high risk.
* `λ₁ ≤ d`: cheap-ish route avoiding Laplacians: Rayleigh quotient of `f = x₁|_{S^d}` (smooth, compact): `∫|∇f|² = ∫(1-x₁²) = d/(d+1)`,
  `Var f = 1/(d+1)` by symmetry (needs `mgrad` of the restriction = tangential projection, about 400 lines). `λ₁ ≥ d`: the project only has
  `CD(ρ,∞)` (gives `d-1`); needs the dimensional Bochner/Lichnerowicz (`CD(ρ,n)`): integrated Bochner plus
  `‖Hess f‖² ≥ (Δf)²/n` on a compact manifold. The project's `WeightedBochner*` modules supply the integrated Bochner identity, so
  perhaps 1000-2000 lines; eigenfunction smoothness is available. Alternative: spherical harmonic completeness (not in Mathlib): worse.
* Total for (a)+(b): 5k-10k lines, 2-4 agent-months, risk high (instance construction and curvature computation dominate).
* (d) Cutoff on the sphere: needs heat-kernel/spectral asymptotics on `S^d` (Gegenbauer expansions, Funk-Hecke) plus
  TV/W₂ definition for the Riemannian Brownian semigroup (we have `IsDiffusionSemigroup`): infeasible, and the manuscript gives no precise statement.

### 5. Recommendation
Skip, or at most a "weaker faithful version": only the arithmetic `λ₁/ρ = d/(d-1) → 1` plus the hypotheses-only structure statement above
as unproved documentation. The claim is an introductory remark leading to Question 1.10, not used elsewhere. Rank it fourth (heavy) and do not start
before items 1, 2, 5. If any geometric example is wanted for the Riemannian theorems, a cheaper non-trivial example is a product `S^1 × R` or the
flat torus (curvature 0, `CD(0)`: not useful with ρ>0), so there is no cheap substitute with `ρ>0` and `λ₁=ρ` besides the flat Gaussian `ℝ^k` already done.

---------------------------------------------------------------------------------------------------

## Item 5: Dyson-OU on the convex chamber (L320-334)

### 1. Claim
Setting: Theorem 1.? (convex interactions) with `h(x) = -β log x` for `x > 0`, `+∞` for `x ≤ 0` (β ≥ 0 arbitrary), "the degeneracy being
equivalent to define the Dyson-OU process on the convex domain `{x₁ > ⋯ > x_d}` instead of on the whole space", "In this case, the
symmetric Hermite polynomial `x₁+⋯+x_d` is an eigenfunction associated to the spectral gap". So `V(x) = ρ|x|²/2 - β ∑_{i<j} log(x_i - x_j)` on
`D = {x₁>…>x_d}`, `V = +∞` outside; claims: `λ₁ = ρ` and `∑ xᵢ ∈ E₁`. The paper says "this approach can be adapted"; no proof, no cutoff claim for DOU
(cutoff for DOU is BCL23, cited). Does it fit the Euclidean framework? No: `IsLangevin`/`gibbs V` need `V` real-valued `C²` on `ℝ^d`, `RigidCurvature`,
and a global SDE solution with Brownian motion; here `V` is not finite off `D`, not `C²` at the boundary (for β ∈ (0,1) the log-barrier
interplay produces collisions with reflection; for β = 0 the process is reflected OU in a cone; for β ≥ 1 no collisions), and `gibbs` is
`volume.withDensity` (could be adapted with an indicator). Challenge theorems 1.5 and Euclidean `spectralGap` do not apply.

### 2. Draft statement (elaborates, `dys.lean`): static (analytic) form
```lean
def chamber (d : ℕ) : Set (Rd d) := {x | StrictAnti x}
noncomputable def dysonMeasure (d : ℕ) (ρ β : ℝ) : Measure (Rd d) :=
  (volume.restrict (chamber d)).withDensity fun x =>
    ENNReal.ofReal (Real.exp (-(ρ / 2) * ‖x‖ ^ 2) * ∏ i, ∏ j with i < j, (x i - x j) ^ β)

theorem dyson_gap_and_eigenfunction {d : ℕ} (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    let μ := dysonMeasure d ρ β
    let h := fun x : Rd d => ∑ i, x i
    IsFiniteMeasure μ ∧ 0 < μ Set.univ ∧
    (∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →                      -- weak Neumann form of 𝓛h = -ρh
      ∫ x, ⟪gradient h x, gradient φ x⟫ ∂μ = ρ * ∫ x, h x * φ x ∂μ) ∧
    (∀ f, ContDiff ℝ ∞ f → HasCompactSupport f →                     -- Poincaré with constant 1/ρ
      ρ * variance f ((μ univ)⁻¹ • μ) ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂((μ univ)⁻¹ • μ))
```
The last two together say `λ₁ = ρ` (the Poincaré test shows `λ₁ ≥ ρ`; the eigenfunction `h ≠ 0` shows `λ₁ ≤ ρ`)
and `h ∈ E₁` in the weak sense. Hypotheses added: none beyond β ≥ 0, ρ > 0, d > 0 (β ≥ 0 matches). It is a faithful
reading of the sentence at the level of the quadratic form; the process-level reading (the Dyson-OU SDE has this generator) is NOT captured.

### 3. What exists / missing
* Exists: Euclidean Thm 1.5 machinery for `C²` `V` (`GaussianFactorization`, `SplitPotential`, `NoBmMollify`, `NoBmConvex`: mollification and Brownian-free
  Poincaré for convex potentials; `FiniteMeasureC1Poincare`). Gaussian factor along the diagonal is simply Fubini because `V` is translation-invariant
  along `(1,…,1)`.
* Missing: (i) integrability / finiteness of `dysonMeasure` (Selberg-type bound: crude bound `∏(x_i-x_j)^β ≤ C(1+|x|)^{βd²/2}` on the chamber, 100-200 lines);
  (ii) the weak eigenfunction identity: integration by parts on a polyhedral cone with a weight vanishing like `(x_i-x_j)^β` at the walls: needs cutoffs
  near the walls, `∂_i W` summed over `i` is zero by antisymmetry; boundary term is zero because `∇h` is tangent to every wall (normal is `e_i - e_{i+1}`,
  `⟨1,n⟩ = 0`), 500-1500 lines with the cutoff argument at rpow singularities; (iii) the Poincaré inequality for the restricted (extended-valued convex) potential:
  approximate `W` by `C²` convex `W_ε` with Brascamp-Lieb/Thm 1.5-type input (project has Poincaré for `C²` convex `V` with `ρ`-convexity) and pass to the limit
  (monotone/dominated convergence on the Rayleigh quotients): 800-2000 lines, medium-high risk; (iv) the process-level statement (the DOU SDE with `β/(x_i - x_j)` drift,
  reflection or collisions for `β < 1`, a Markov semigroup whose generator is `𝓛`): new SDE theory (Rogers-Shi / AGZ for β ≥ 1; β∈(0,1) is delicate, β = 0 needs a Skorokhod
  reflection problem), months, infeasible in this revision. Even then the corollaries for DOU (cutoff, W₂) would need the whole Euclidean pipeline on a domain.

### 4-5. Effort and recommendation
Static version: 1.5k-4k lines, 1-3 agent-weeks, medium risk (the integration by parts with singular weights and the limit for Poincaré are the risks).
Recommendation: do the static version after items 1-2 (second priority), since it is a precise mathematical statement in the manuscript and uses mostly existing tools;
skip the process-level claim and say so explicitly in the status file (the manuscript only says the approach "can be adapted", with no theorem).
Note: for β = 0 the static statement is a clean exercise (reflected OU in a cone, Gaussian restricted to a convex cone: Neumann eigenfunction `∑ xᵢ` and Poincaré for a log-concave restriction).

---------------------------------------------------------------------------------------------------

## Cross-item remarks
* Items 1-2 can be done together in one afternoon of agent time: a single new Challenge/Solution pair of 3 theorems (`riemannian_k1_bounds`, `riemannian_poincare_lsi`, `riemannian_lichnerowicz`)
  with 0 new mathematics. Needs a general-measurable-space `entropyM` (or a new `Riemannian` namespace definition) since Challenge's `entropyOf` is on `Rd d`.
* Sphere (item 4) conflicts with item 1: it is the counterexample to `k₁ ≤ dim` without `λ₁ = ρ`, so documentation of the hypothesis `hgap` in the Challenge docstring is important.
* The scan's classification B2 (Riemannian `k₁ ≥ 1`, `k₁ ≤ dim`) is "medium-hard"; the actual status is "easy": already available under `λ₁ = ρ` (the case of all Riemannian theorems).
  The hard part (general `ρ`, discreteness of the whole spectrum) is not needed by the paper's theorems.
