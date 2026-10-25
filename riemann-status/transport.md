# Workstream C (`transport`): Wasserstein estimate through the splitting

Files (all compile, no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`;
no existing file was edited; `CutoffRigidity.lean` not touched, the lead must add the imports):

| file | content |
|---|---|
| `CutoffRigidity/Riemann/TransportW2.lean` | generic `W₂` facts for `CutCur.wasserstein2` on a `PseudoEMetricSpace` |
| `CutoffRigidity/Riemann/TransportUpper.lean` | upper bound from invariance + `W₂`-contraction |
| `CutoffRigidity/Riemann/TransportCoupling.lean` | sufficient conditions: coupling kernel => contraction; reversibility => invariance |
| `CutoffRigidity/Riemann/TransportGauss.lean` | exact `W₂` cost of the rescaled Mehler law vs the equilibrium Gaussian on `ℝ^k` |
| `CutoffRigidity/Riemann/TransportLower.lean` | `SplitData`, lower bound through the isometric splitting |
| `CutoffRigidity/Riemann/TransportAlgebra.lean` | `Λ = ρ|p|²` algebra |
| `CutoffRigidity/Riemann/TransportMain.lean` | assembly: `riemannian_wasserstein_estimate_of_transport` |

## 1. Is `IsDiffusionSemigroup` enough?  (analysis, requested FIRST)

`IsDiffusionSemigroup F V Pt` = Markov kernels + semigroup law + Dynkin/Kolmogorov identity
`Pt f(x) = f(x) + ∫₀ᵗ Ps(𝓛f)(x) ds` for `f ∈ C_c^∞` only.  Fix `x`; then `νₜ = Pt(x,·)` is a
probability-valued solution of the weak Fokker–Planck equation `∂ₜν = 𝓛*ν`, `ν₀ = δ_x`, tested
against `C_c^∞` functions.  Everything is therefore equivalent to **uniqueness of probability
solutions of this equation**.  Findings:

**No counterexample to the Challenge statement was found; the three steps are TRUE for the actual
(minimal) diffusion, but they are NOT formal consequences of the hypothesis: each one needs a
uniqueness theorem (`Pt` = minimal diffusion), which is exactly where `CD(ρ,∞)` (non-explosion,
Bakry) enters and which needs parabolic PDE / martingale-problem theory absent from Mathlib.**

(i) *Invariance of `μ`.*  Not derivable from the Dynkin identity alone.  One computes
`d/dt ∫ Pt f dμ = ∫ Pt(𝓛f) dμ`, which is zero only if one already knows `∫ Ps g dμ = ∫ g dμ`
(circular).  The routes are (a) self-adjointness/reversibility of `Pt` in `L²(μ)` (needs
essential self-adjointness of `𝓛` on `C_c^∞`, which uses completeness + cutoffs with controlled
`𝓛χ`), or (b) uniqueness of the FP equation started at `μ` (`μ` is a stationary solution since
`∫ 𝓛f dμ = 0`).  Both need uniqueness.  Minimal extra property that is true for the minimal
diffusion: `Pt` reversible w.r.t. `μ`; then `μ.bind Pt = μ` is the (proved)
`bind_eq_of_reversible`.

(ii) *Exact Mehler law of the affine eigenmap.*  The eigenfunctions `T_i = √ρ p_i` are not compactly
supported, so the identity cannot be applied to them.  Cutoff approximation `χₙ T` needs: (1) a
uniform bound `sup_{s≤t} ∫ |T| dPs(x,·) < ∞` (for dominated convergence), which is NOT implied by
the hypothesis: it is a tightness/moment estimate for the unknown kernel; and (2) smooth
exhausting cutoffs with `|𝓛χₙ|` controlled, which needs a Laplacian comparison (`Ric_V ≥ ρ`) and a
smoothing of the distance function (absent from Mathlib).  The one-sided sign of the
Laplacian comparison (`Δ_V d ≤ C`) is the wrong direction for the term `f²𝓛χₙ` in a Gronwall
argument, so even the moment bound is not a mere Gronwall: it needs a comparison with the
Dirichlet-killed (stopped) process, i.e. uniqueness again.  Beyond that, the full Mehler *law* (not
just mean/covariance) needs the chain rule `𝓛(h∘T) = Σ ∂ᵢh 𝓛Tᵢ + Σ ∂ᵢⱼh Γ(Tᵢ,Tⱼ)` on the manifold
(true, not in the project) with `Γ(Tᵢ,Tⱼ) = ρδᵢⱼ` (from `lem_rig`), plus an ODE/characteristic-function
argument (`Measure.ext_of_charFun`).  Everything is true for the minimal diffusion.

(iii) *Upper bound.*  Needs invariance (i) and the `W₂` contraction `W₂(νPt, ν'Pt) ≤ e^{-ρt}W₂(ν,ν')`
under `CD(ρ,∞)` (von Renesse–Sturm, Bakry–Émery gradient bound + Kuwada duality, or parallel
coupling).  The splitting does not help for the `M'` factor (`μ'` is only `CD(ρ,∞)`), so a genuinely
Riemannian contraction theorem is needed; it relies on regularity of `Pt f` (parabolic regularity)
and is far beyond the hypothesis.  Minimal true extra property: existence of a measurable
coupling kernel with `∫ d² dQ(x,y) ≤ e^{-2ρt} d²(x,y)` (`w2Contraction_of_coupling` proves that this
suffices).

Why uniqueness is not formal (so no "proof from the hypothesis" can exist without it): Feller's
theory shows that on complete weighted manifolds without a Ricci lower bound one can have
stochastically incomplete minimal diffusions with several Markov extensions agreeing on `C_c^∞`
(reflection at a regular point at infinity; the Dynkin identity for functions vanishing near
infinity does not see the boundary condition).  `Ric_V ≥ ρ > 0` plus completeness excludes this
(non-explosion), but proving it requires a Lyapunov function (Laplacian comparison) and then an FP
uniqueness theorem (Bogachev–Röckner–Shaposhnikov type, via Dirichlet Cauchy problems on balls).
Also noted: the hypothesis integrates `s ↦ ∫ 𝓛f dPs(x,·)` with a Bochner interval integral (junk value
`0` if the integrand is non measurable); I found no counterexample exploiting this (a time-change
`Q_{φ(t)}` of a genuine semigroup by an additive non-measurable `φ` violates the identity), but I
did not prove measurability.

Other points that are statement-level, not transport-level:
* The ball refinement when `mFirstEigenDim = 0` reads `q R² ≤ sup W` with no information; it is true
  only because `k₁ ≥ 1` (attainment of the gap under `CD(ρ,∞)`, `λ₁ = ρ`, a Workstream A fact).
  The assembly takes `0 < k₁` as a field of `EigenSplitting`.
* `AEMeasurable Φ μ` is a field of `SplitData`: it cannot be derived from `μ.map Φ = γ ⊗ μ'` when
  `k = 0` (the map of a non-a.e.-measurable function is a junk Dirac mass); for the actual `Φ`
  (diffeomorphism) it holds.

## 2. What is proved (declarations, namespace `CutoffRigidity.Riemann`)

Generic Wasserstein (TransportW2):
* `cost2 μ ν := ⨅ couplings, ∫⁻ edist²`; `wasserstein2_sq_eq_cost2 : wasserstein2 μ ν ^ 2 = cost2 μ ν`.
* `cost2_map_le` : `f` measurable, `edist (f x) (f y) ≤ L * edist x y`, `L : ℝ≥0`, `L ≠ 0` gives
  `cost2 (μ.map f) (ν.map f) ≤ L^2 * cost2 μ ν`.
* `cost2_dirac_left_le : cost2 (dirac x) ν ≤ ∫⁻ edist x y ^ 2 ∂ν`.

Upper bound (TransportUpper, TransportCoupling):
* `W2Contraction P q`; `upper_pointwise`, `upper_iSup`: from `μ.bind P = μ` and `W2Contraction P q`,
  `⨆ x₀∈S, wasserstein2 (P x₀) μ ^ 2 ≤ q * ⨆ x₀∈S, ∫⁻ edist x₀ y ^ 2 ∂μ`.
* `w2Contraction_of_coupling` (measurable coupling kernel `Q` with cost `≤ q d²` => contraction).
* `bind_eq_of_reversible` (reversibility => invariance).

Gaussian computation (TransportGauss): `cost2_eq_squaredWasserstein`, `affineGaussian_map_smul`,
`gaussian_equilibrium_rescaled` (`√ρ`-image of `N(0,ρ⁻¹I)` is `stdGaussian`), `mehler_rescaled`,
`cost2_mehler_rescaled` (exact value `ρ e^{-2ρt}‖z‖² + k(1-√(1-e^{-2ρt}))²`).

Lower bound (TransportLower): `structure SplitData M N k ρ μ` (`Φ`, `μ'`, `prob'`, `aemeasurable`,
`surj`, `dist_sq` = the Challenge's distance identity, `map_eq` = `μ.map Φ = γ ⊗ μ'`);
`SplitData.proj`, `edist_proj_le`, `lipschitz_proj`, `measurable_proj`, `map_proj_eq`,
`SplitData.mehler ρ t z` (the Mehler law), and
`SplitData.lower_of_mehler : ν.map proj = mehler ρ t (proj x₀) →
 ofReal(ρ(e^{-2ρt}‖proj x₀‖²) + k(1-√(1-e^{-2ρt}))²) ≤ ofReal ρ * wasserstein2 ν μ ^ 2`.

Algebra (TransportAlgebra): `sum_sq_inner_of_orthogonal` (`∑⟨aᵢ,z⟩² = ρ‖z‖²` for orthogonal `aᵢ`, `‖aᵢ‖²=ρ`).

Assembly (TransportMain):
* `EigenSplitting F μ V ρ D` (Prop structure: `rep`, `orth` = Challenge's last two bullets, plus
  `basis` = existence of an orthonormal eigenbasis, `pos` = `0 < k₁`).
* `mLambda_eq_of_splitting : mLambda F μ V x = ofReal (ρ * ‖D.proj x‖^2)`.
* `TransportInputs μ ρ D Pt` (Prop structure: `invariant`, `contraction`, `mehler`).
* `pointwise_lower`.
* **`riemannian_wasserstein_estimate_of_transport`** : exactly the conclusion of the Challenge's
  `riemannian_wasserstein_estimate` (both inequalities for every nonempty `S`, and the ball
  refinement), from `hρ`, `hgap`, `SplitData` (with `k = mFirstEigenDim F μ V`), `EigenSplitting`,
  `hP : IsDiffusionSemigroup F V Pt` (only Markov-ness used) and `TransportInputs`.

## 3. What remains / blocked

To obtain `riemannian_wasserstein_estimate` itself one still needs:
1. `SplitData` + `EigenSplitting.rep/orth`: output of `riemannian_gaussian_splitting` (Workstream B/A);
   `EigenSplitting.basis` needs linearity of `mgenerator` (eigenfunctions form a vector space) and
   Gram-Schmidt in the span; `EigenSplitting.pos` is the attainment `k₁ ≥ 1`.
   Also `OpensMeasurableSpace M` (from `BorelSpace M`) and `aemeasurable`/`surj` of `Φ` are routine.
2. `TransportInputs.invariant`, `.mehler`, `.contraction` from `hP`: **blocked** by the uniqueness
   theorem described in section 1 (parabolic PDE on manifolds / Lyapunov + FP uniqueness, Laplacian
   comparison, chain rule for `𝓛` on `ℝ^k × N`, Kuwada/von Renesse–Sturm contraction).  The minimal
   additional properties that are true for the actual minimal diffusion and make the proof
   complete are exactly the three fields of `TransportInputs` (or: `Pt` reversible for `μ`,
   Mehler law for `proj`, coupling kernel for contraction).
