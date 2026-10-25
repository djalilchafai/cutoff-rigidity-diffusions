# DIFFUSION_PLAN: discharging `hpos`, `hinv`, `hcontr`, `hmehler` from `IsDiffusionSemigroup`

Author: `diffplan` architect. Status: plan only, nothing proved. All new code goes in
`CutoffRigidity/Riemann/Diff*.lean`; nobody touches `Challenge/Statements/Solution/CutoffRigidity.lean`
except the lead. The amended `riemannian_wasserstein_estimate` stays intact until the replacement compiles.

Notation: `Γ = carre`, `𝓛 = mgenerator F V`, `𝒟 = C_c^∞(M)` (smooth, compact support), `H = L²(μ) = M →₂[μ] ℝ`,
`semi P t f x := ∫ y, f y ∂(P t x)` (the function `x ↦ P_t f(x)`), `MSmooth F f := ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞ f`.

---------------------------------------------------------------------------------------------------

## 0. Verdicts (read this first)

0.1 The statement WITHOUT the four hypotheses is TRUE (no counterexample; every ingredient below is a known theorem
under Ric_V ≥ ρ > 0, completeness, μ probability). It is, however, a program of the order of
**45k lines (range 35k-65k) of new Lean**, about four times the whole Riemannian branch (11.7k lines, 77 files), plus an
optional geometric moonshot (`CO`, +30k, range 20k-50k, success probability about 1/3) that can be avoided by a
faithful strengthening of the *definition* (section 6). Honest recommendation: do the "canonical diffusion" part (Tier A),
the bridge (Tier B) and the assembly (Tier C); decide `CO` versus strengthening only afterwards.

0.2 New structural facts found while planning (they change the architecture of the lead's guidance):

* **(F1) The Mehler law is not needed.** The Challenge conclusion needs, for each `x₀`, only the mean and the trace of
  the covariance of the eigenmap `T` under `P_t(x₀,·)`; then a Cauchy-Schwarz coupling bound gives exactly
  `ρ^{-1}(q Λ + k (1-√(1-q))²)` (section 2.4, lemma C1). Both moments follow from the single statement
  "`u` smooth, `u ∈ L²(μ)`, `𝓛u = -c u` ⇒ `P_t u(x) = e^{-ct} u(x)` for every x" applied to `u = T_i` (c = ρ) and
  `u = T_i² - ‖T_i‖²` (c = 2ρ, because `Γ T_i = ρ‖T_i‖²` is constant by the splitting).
* **(F2) Only `W₂(P_t δ_x, μ)² ≤ e^{-2ρt} ∫ d²(x,y) dμ` is needed**, not contraction for arbitrary pairs of laws, and
  it can be proved by Kuwada's interpolation WITHOUT geodesics, cut locus, or Hamilton-Jacobi regularity: only
  near-minimizing Lipschitz curves (definition of `edist`), Rademacher (in Mathlib), and the one-sided inequality
  `∂_r Q_r h ≤ -½ |∇Q_r h|²` which follows in three lines from the inf-convolution (section 2.2, A10).
* **(F3) Everything about the abstract `Pt` is reduced to ONE bridge**: `P_t(x,·) = K_t(x,·)` for all `x, t`, where `K`
  is the canonical (Friedrichs) diffusion, built purely in `L²(μ)`. The bridge needs exactly the Dynkin identity for
  *bounded smooth `f` with bounded `∇f` and bounded `𝓛f`* (call it `DynkinBounded`). `DynkinBounded` follows from
  `IsDiffusionSemigroup` plus ONE geometric input `OneSidedCutoffs` (smooth compactly supported `χ_n ↑ 1` with
  `|∇χ_n| ≤ C` and `𝓛χ_n ≥ -C`), by a "mass trick" that uses only ONE-SIDED bounds and Fatou/dominated convergence
  (section 2.3). The sign needed is `𝓛χ_n ≥ -C`, i.e. exactly the Laplacian-comparison direction `𝓛 d ≤ C`; the
  `diffusion.md` objection "wrong direction for `f²𝓛χ_n`" is refuted (it disappears with positivity of `f` and the
  identity `P_t 1 = 1`). BOUNDED below suffices (not small, no log-scale cutoffs, no `Γφ ≤ C(1+φ)²`).
* **(F4) `OneSidedCutoffs` is irreducibly geometric** (equivalent to non-explosion of `P` at every point, hence to a
  Laplacian-comparison/Omori-Yau type statement). Every cheaper route I could find fails (table 2.6). In particular
  a.e./L² identification (reversibility, or hypoellipticity for measures) is NOT enough: the Challenge takes sup over
  arbitrary `S`, even singletons, so pointwise-in-x identification is forced.
* **(F5) The canonical semigroup needs no compactness and no unbounded spectral theory**: with `R = (1+A_F)^{-1}`
  bounded, self-adjoint, `0 ≤ R ≤ 1`, define `T_t := cfc (h_t) R`, `h_t(r) = exp(-t(1/r - 1))`, `h_t(0) = 0`
  (continuous on `[0,1]`); `(1+tA/n)^{-n} = φ_{t/n}(R)^n ↓ h_t(R)` monotonically (since `(1+x/n)^n ↑ e^x`), so Dini
  gives *norm* convergence; semigroup law = multiplicativity of `cfc`. Compactness of the resolvent is needed ONLY for
  `hpos` (attainment of the gap).
* **(F6) Regularity (E) (weak H¹ solutions of `(λ-𝓛)u = g` are smooth) cannot be avoided**: smoothness of eigenfunctions is
  part of the definition of `IsMEigenfunction`, hence of `mFirstEigenDim`; it is also needed for the pointwise
  kernel. ~9k lines. Mathlib's new Fourier-based Sobolev scale (`Analysis/Distribution/Sobolev.lean`) makes the
  difference-quotient step short ("`‖D_h u‖₂ ≤ C` ⇒ `∂u ∈ L²`" is one Fatou on the Fourier side).

0.3 Corrections to the lead's guidance:
(1) pointwise: confirmed, and it is the reason for (F3)/(F4). (2) one-sidedness: confirmed and sharpened to the
"mass trick" (applied to `f` and `C - f`). The lead's `L(ψ∘φ) ≤ ψ' Lφ` is not even needed. (3) Gaffney cutoffs suffice for
the whole `L²` side (K, positivity, conservativity, eigenvalue identities, `hpos` via LSI) and are already in the project
(`weightedCutoffs_of_complete`); they do NOT suffice for the `P` side. (4a) Lyapunov `φ` with `𝓛φ ≤ C(1+φ)` and
`Γφ ≤ C(1+φ)²` is stronger than needed (replace by `OneSidedCutoffs`). (4c) duality with a smooth *backward* solution is
the right idea, and the smooth solution is `u_s = K_{t-s} g` (no parabolic regularity beyond the elliptic one: it comes
from `(E)` applied to `D(A^k)`). (4d) Kuwada is feasible, see (F2); contraction is needed only between `δ_x` and `μ`.
(4e) Mehler: not needed, see (F1). (4f) `hpos`: cheapest rigorous route = LSI(ρ) ⇒ tightness by the entropy
inequality (elementary, 6 lines) + local Rellich + (E); Hardy via Lyapunov is NOT cheaper (needs `CO`).
(5) Elliptic regularity: must be built (F6); parabolic regularity can be avoided entirely.
The splitting `M ≅ ℝ^k × N` helps only for the moment computations; contraction on `N` is irreducibly Riemannian.

---------------------------------------------------------------------------------------------------

## 1. Standing hypotheses (all statements below)

```lean
variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V)
  {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ)
```
Project facts reused as black boxes (all proved, see files): `weightedIBP_of_isWeightedVolume`
(`∫ Γ(u,v) = -∫ u 𝓛v`, `u` compactly supported), `weightedCutoffs_of_complete` (`|∇χ_n| ≤ 1/(n+1)`, eventually 1),
`weightedBochnerIneq_of_CD` (`Γ₂ ≥ ‖Hess‖² + ρΓ`), `caccioppoli`/`hess_cutoff_bound` (WeightedRigidity),
`properSpace_of_complete_riemannian`, `edist_ne_top_of_connected`, `measure_pos_of_isWeightedVolume` (full support),
`exists_smooth_lip_approx` (WeightedSmoothing), chart objects `chartVolumeDensity`, `DiffusionRegular.lean`
(`dynkin_lipschitz`, `continuous_dynkin`, `hasDerivAt_dynkin`: for `f ∈ 𝒟`, `t ↦ P_t f(x)` is C¹ with derivative
`P_t(𝓛f)(x)`), `mFirstEigenDim_pos_iff`, `exists_orthonormal_eigenbasis`, `riemannian_gaussian_splitting`,
and the transport files (`TransportLower`, `TransportMain`, `TransportW2`, `TransportGauss`).

---------------------------------------------------------------------------------------------------

## 2. Mathematics and Lean architecture

### 2.0 Overview of the proof of the unconditional theorem

```
IsDiffusionSemigroup Pt ─┐
CD, complete, μ prob.    ├─ Tier A: canonical diffusion K (pure L²(μ) theory)  ── K Markov, symmetric, smooth kernel,
                         │     eigen identity, gradient bound, contraction      IsDiffusionSemigroup K, hpos
OneSidedCutoffs (CO) ────┤─ Tier B: DynkinBounded Pt ⇒ P_t(x,·) = K_t(x,·) ∀ x t
                         └─ Tier C: hinv, W₂-bound, two moments ⇒ the Challenge conclusion (existing transport files + 2 new lemmas)
```

### 2.1 The canonical operator (A1-A4)

`A := -𝓛 : 𝒟 → H` (note `𝒟 ⊂ H` since μ finite and elements are bounded).

* **A1 (DIR).** `𝒟` is dense in `H`; `⟨Af,g⟩ = ⟨f,Ag⟩`, `⟨Af,f⟩ = ∫Γ f ≥ 0` (project IBP). `𝒟` is stable under smooth
  normal contractions `θ∘f` (`θ(0)=0, |θ'|≤1`), and `Γ(θ∘f) = θ'(f)²Γ f ≤ Γ f`.
* **A2 (FR, generic).** Friedrichs: for a densely defined symmetric nonnegative `A` on a Hilbert space there is a
  bounded self-adjoint injective `R`, `0 ≤ R ≤ 1`, with `R(f + Af) = f` (`f ∈ D`), and a closed form domain `Q ⊃ D`
  with energy `E` such that `E₁(Rg, φ) = ⟨g, φ⟩` (`E₁ = E + ⟨·,·⟩`) for all `φ ∈ Q`. Closability of the form is automatic
  from symmetry of the operator (`q(f_n) = q(f_n, f_n - f_m) + ⟨f_n, A f_m⟩`), so NO vector-valued `L²` and NO
  divergence theorem for general vector fields is needed. Also `R_λ = (λ + A_F)^{-1}` for each `λ > 0`.
* **A3 (MKV).** Beurling-Deny: if `|u| ∈ Q`, `E(|u|) ≤ E(u)` (obtained from `θ_ε(t) = √(t²+ε²) - ε` on `𝒟` and
  closedness), then `E(u⁺,u⁻) ≤ 0`, so `g ≥ 0 ⇒ Rg ≥ 0` (test `E₁(Rg, (Rg)⁻) = ⟨g,(Rg)⁻⟩ ≥ 0`); similarly `g ≤ 1 ⇒ Rg ≤ 1`
  once `R1 = 1`. `R 1 = 1` because `1 ∈ Q`, `E(1) = 0`, by Gaffney cutoffs `χ_n → 1` in `E₁` (`E(χ_n) ≤ 1/(n+1)²`).
* **A4 (CFC).** `T_t = cfc (h_t) R` as in (F5). Properties: `T_0 = 1`, `T_{s+t} = T_sT_t`, `‖T_t‖ ≤ 1`, self-adjoint,
  `T_t = lim ((n/t) R_{n/t})^n` in norm (hence positivity preserving, `T_t 1 = 1`, `∫ T_t u = ∫ u`); if `R u = (1+c)^{-1} u`
  then `T_t u = e^{-ct} u`; for `u = R g`: `HasDerivAt (t ↦ T_t u) (-T_t(g - u))`; in particular for `f ∈ 𝒟`,
  `HasDerivAt (T_t f) (T_t (𝓛 f))`.

### 2.2 Regularity, kernel, and the analytic properties of K (A5-A10)

* **A5 (REG).** (i) (ℝⁿ) Let `Ω ⊂ ℝⁿ` open, `a : Ω → Sym⁺` smooth, `ϱ > 0` smooth, `λ ≥ 0`, `u ∈ H¹_loc(Ω)`, `g ∈ H^m_loc(Ω)` with
  `∫ (⟨a∇u,∇φ⟩ + λuφ) ϱ = ∫ gφϱ` for all `φ ∈ C_c^∞(Ω)`. Then `u ∈ H^{m+2}_loc(Ω)`, with the interior estimate
  `‖u‖_{H^{m+2}(K)} ≤ C(‖g‖_{H^m(K')} + ‖u‖_{L²(K')})`; and `H^m_loc ∀m ⇒ C^∞` with `‖ū‖_{C^j(K)} ≤ C‖u‖_{H^{m}(K)}` for `m > j + n/2`.
  Proof: difference quotients (standard, Evans §6.3); Sobolev embedding via Fourier integrability.
  (ii) (manifold) For `u ∈ Q` the chart restriction is `H¹_loc` and satisfies the weak equation with `a = g^{-1}`,
  `ϱ = e^{-V}√det g` (this is `IsWeightedVolume`, `chartVolumeDensity`), hence `u` has a smooth representative (patch by
  continuity on overlaps). Iterating along `D(A^k)`: for `u ∈ H`, `t > 0`, `T_t u` has a smooth representative, with
  `sup_K |T_t u| + sup_K |∇T_t u| ≤ C(K,t) ‖u‖_H` (use `‖A^j T_t u‖ ≤ C_j t^{-j} ‖u‖`, from `cfc` bounds on `r^j h_t`... bounded
  functions of the spectrum).
* **A6 (KER).** `ℓ_x(u) := (T_t u)(x)` is a bounded functional on `H`; Riesz gives `p_t(x,·) ∈ H`, `p_t(x,·) ≥ 0`, `∫p_t(x,y)dμ = T_t 1 (x) = 1`.
  `Kk t x := (p_t(x,·)) • μ` is a Markov kernel (measurability of `x ↦ Kk t x A` from continuity of `x ↦ p_t(x,·) ∈ H`),
  `Kk (s+t) = Kk t ∘ₖ Kk s` for EVERY `x` (both sides continuous in `x`, equal a.e., full support of `μ`), `Kk t x ≪ μ`,
  `μ.bind (Kk t) = μ` and reversibility from symmetry + `T_t 1 = 1`.
  `Kk 0 x = δ_x`. Pointwise Dynkin: for `f ∈ 𝒟`, `K_t f(x) = f(x) + ∫_0^t K_s(𝓛f)(x) ds` for every `x` (a.e. from A4, then both
  sides are continuous in `x`; the right side is continuous by dominated convergence, `|K_s ψ| ≤ ‖ψ‖_∞`). Hence
  `IsDiffusionSemigroup F V Kk` (consistency: the Challenge hypothesis is not vacuous). Also `𝓛(semi Kk t f) = semi Kk t (𝓛 f)` for `f ∈ 𝒟`
  (`T_t f ∈ D(A_F)`, smooth, weak ⇒ pointwise).
* **A7 (EIG).** `u` smooth, `u ∈ L²(μ)`, `𝓛u = -cu` ⇒ `u ∈ Q` (Gaffney: `∫χ²Γu ≤ c∫χ²u² + 2‖∇χ‖_∞ ∫χ|u|√Γu`, so `Γu ∈ L¹`, and
  `χ_n u → u` in `E₁`) and weakly `E₁(u,φ) = (1+c)⟨u,φ⟩`, so `R u = (1+c)^{-1}u`, `T_t u = e^{-ct}u` a.e., hence everywhere
  (continuity + full support), hence `∫ u dKk t x = e^{-ct}u(x)` (also `Integrable u (Kk t x)`, since `p_t(x,·) ∈ L²`).
* **A8 (BE) Bakry-Émery, pointwise.** For `f ∈ 𝒟`: `semi Kk t f` smooth and
  `Γ(semi Kk t f)(x) ≤ e^{-2ρt} ∫ Γf dKk t x` for every `x`, `t`; and the same for bounded Lipschitz `ψ` with `Γψ` replaced by the a.e.
  slope squared (approximation `exists_smooth_lip_approx`, dominated convergence, `Kk t x ≪ μ`).
  Proof: `ζ ≥ 0` in `𝒟`, `w_s = K_{t-s} f`, `A(s) = ∫ (K_sζ) Γ(w_s) dμ`. Then `A'(s) = 2∫ (K_sζ) Γ₂(w_s) dμ ≥ 2ρ A(s)`
  (uses `Γ₂ ≥ ρΓ` and `K_sζ ≥ 0`), so `A(t) ≥ e^{2ρt}A(0)`, i.e. `∫ζ Γ(K_t f) ≤ e^{-2ρt} ∫ζ K_t(Γf)` for all `ζ ≥ 0`; both sides
  continuous in `x`. Technical lemmas: (i) integrated Bochner for `𝒮 = {u smooth, u,𝓛u ∈ L²}`:
  `Γu ∈ L¹`, `Hess u ∈ L²`, `∫(‖Hess u‖² + ρΓu) ≤ ∫(𝓛u)²` (generalize `caccioppoli`/`hess_cutoff_bound` from eigenfunctions);
  (ii) `∫ Φ 𝓛(Γw) = ∫ (𝓛Φ) Γw` for `Φ` bounded in `𝒮`, `w ∈ 𝒮` with `𝓛w ∈ 𝒮` (cutoff error is `∫|Φ||∇Γw||∇χ| ≤ 2‖Φ‖_∞‖Hess w‖₂‖∇w‖₂/n`);
  (iii) differentiability of `s ↦ Γ(w_s)` in `L¹`. (For LSI one needs the `√` version `|∇K_t g| ≤ e^{-ρt}K_t|∇g|` via Kato
  `|∇|∇w|| ≤ ‖Hess w‖` and `Φ_ε = √(Γw + ε)`.)
* **A9 (HPOS).** `0 < mFirstEigenDim`. Steps: (i) LSI(ρ): `Ent_μ(f²) ≤ (2/ρ) ∫Γf` for `f ∈ 𝒟` (Bakry-Émery interpolation with the `√`
  gradient bound of A8; `d/dt Ent(K_t g) = -∫Γ(K_tg)/K_tg`, Fisher decay `I(K_tg) ≤ e^{-2ρt}I(g)`). (ii) Tightness of the unit ball of
  `(Q,E₁)`: with `h = f²/‖f‖²`, the entropy inequality `∫hg ≤ Ent(h) + log∫e^g` for `g = θ·1_{B^c}` gives
  `∫_{B^c} f² ≤ (1/θ)[(2/ρ)E(f) + ‖f‖² log(1 + e^θ μ(B^c))]`, uniform in the unit ball (choose `θ` then `B`). (iii) Local Rellich
  in charts (translation bound + Arzelà-Ascoli: templates `L2CompactnessTools`, `GibbsCompactEmbedding`, `GibbsLocalizedTranslations`),
  hence `Q ↪ H` compact. (iv) Minimizing sequence `f_j ∈ 𝒟`, centered, `Var f_j = 1`, `E(f_j) → ρ` (`mSpectralGap = ρ`; the infimum over `𝒟`
  equals the infimum over `Q` by density) converges in `H` to `f` with `E(f) ≤ ρ`, `Var f = 1`; Euler-Lagrange gives the weak
  equation `E(u,φ) = ρ⟨u,φ⟩` for `u = f - ∫f`, so by A5 `u` is smooth, `𝓛u = -ρu` pointwise, `u ∈ L²`, `u ≠ 0`: `IsMEigenfunction F μ V ρ u`,
  then `mFirstEigenDim_pos_iff`. (Template: `GibbsSpectralGap.exists_positive_gibbsOperator_eigenvalue`, `gibbsSharpPoincare`.)
* **A10 (KUW) Contraction `δ_x` vs `μ`.** `∀ t x, wasserstein2 (Kk t x) μ ^ 2 ≤ ofReal (e^{-2ρt}) * ∫⁻ y, edist x y ^ 2 ∂μ`.
  Proof: (a) *dual pair inequality*: for bounded Lipschitz `f,g` on `M` with `f(y)+g(z) ≤ d²(y,z)`,
  `∫f dKk t a + ∫g dKk t b ≤ e^{-2ρt} d²(a,b)`. Put `h = -g`, `Q_r h(y) = inf_z (h(z) + d²(y,z)/(2r))`; then `f ≤ Q_{1/2}h`.
  Let `γ : [0,½] → M`, `γ(0)=b`, `γ(½)=a`, Lipschitz with `|γ̇| ≤ 2(d(a,b)+ε)` a.e. (definition of `edist`), and
  `F(r) = K_t(Q_r h)(γ(r))`. `Q_r h` is bounded Lipschitz, Lipschitz in `r` (`|∂_rQ| ≤ Lip(h)²/2`). At a.e. `r` and `μ`-a.e. `y`
  (Rademacher in charts; `μ` equivalent to Lebesgue in charts): `∂_rQ_r h(y) ≤ -d(y,y_r)²/(2r²) ≤ -½|∇Q_r h|²(y)` (use the optimal point
  `y_r` and `Q_{r+δ}h(y) ≤ Q_r h(y) - δ d²/(2r(r+δ))`; and `|∇Q_r h|(y) ≤ d(y,y_r)/r`). Since `Kk t x ≪ μ`,
  `F'(r) ≤ -½ K_t|∇Q_r h|²(γ) + |∇K_tQ_rh|(γ)|γ̇| ≤ -½S + e^{-ρt}√S|γ̇| ≤ ½e^{-2ρt}|γ̇|²` (A8 with `S = K_t|∇Q_rh|²(γ(r))`). Integrate over `[0,½]`.
  (b) integrate `b` against `μ` (invariance) to get the budget `K̃ = e^{-2ρt}∫d²(x,y)dμ(y)`; (c) *Kantorovich budget duality on the proper
  space `M`* (project has compact and Euclidean versions) gives `cost2 ≤ ofReal K̃`.

### 2.3 Tier B: the bridge `P = K`

Definitions (new, `DiffDynkinBounded.lean`):
```lean
def BddSmooth (V) (f : M → ℝ) : Prop := MSmooth F f ∧ ∃ C, ∀ x, |f x| ≤ C ∧ ‖mgrad F f x‖ ≤ C ∧ |mgenerator F V f x| ≤ C
def DynkinBounded (V) (Pt : ℝ≥0 → Kernel M M) : Prop := ∀ f, BddSmooth F V f → ∀ (x : M) (t : ℝ≥0),
  ∫ y, f y ∂Pt t x = f x + ∫ s in (0:ℝ)..(t:ℝ), ∫ y, mgenerator F V f y ∂Pt s.toNNReal x
def OneSidedCutoffs (V) : Prop := ∃ (C : ℝ) (χ : ℕ → M → ℝ), (∀ n, MSmooth F (χ n) ∧ HasCompactSupport (χ n) ∧
  ∀ x, 0 ≤ χ n x ∧ χ n x ≤ 1 ∧ ‖mgrad F (χ n) x‖ ≤ C ∧ -C ≤ mgenerator F V (χ n) x) ∧
  ∀ x, ∃ U ∈ 𝓝 x, ∀ᶠ n in atTop, ∀ y ∈ U, χ n y = 1
```
* **B1.** `IsDiffusionSemigroup F V Pt → OneSidedCutoffs F V → DynkinBounded F V Pt`.
  Proof. Step 1 (`f ≥ 0` in `BddSmooth`, inequality `≥`): apply the given Dynkin identity to `χ_n f ∈ 𝒟`, `𝓛(χ_nf) = χ_n𝓛f + f𝓛χ_n + 2Γ(χ_n,f)`:
  `P_t(χ_nf)(x) ≥ χ_nf(x) + ∫_0^t P_s(χ_n𝓛f) - ‖f‖∫_0^t P_s((𝓛χ_n)^-) - 2C'∫_0^t P_s(|∇χ_n|)`, with `C' = sup|∇f|`. Each `P_s(x,·)` is a probability
  measure, `(𝓛χ_n)^- ≤ C` and `|∇χ_n| ≤ C` uniformly and both tend to `0` pointwise (eventually `χ_n ≡ 1` near the point), so by dominated convergence
  in `y` then in `s` the error terms tend to `0`; `P_t(χ_nf) ≤ P_tf`; `P_s(χ_n𝓛f) → P_s(𝓛f)` (bounded `𝓛f`). Hence `P_tf(x) ≥ f(x) + ∫_0^tP_s(𝓛f)(x)ds`.
  Measurability of `s ↦ P_s g(x)` for bounded Borel `g` by monotone class from the continuity for `g ∈ 𝒟` (`DiffusionRegular`). Step 2 (mass trick): for general
  `f ∈ BddSmooth` with bound `C₀`, apply step 1 to `f + C₀ ≥ 0` and to `C₀ - f ≥ 0` and use `P_t c = c`: the two inequalities give `≤` and `≥`.
* **B2.** (`DiffIdentify.lean`) Let `Pt` satisfy `IsDiffusionSemigroup` and `DynkinBounded`, and let `Kk` be Markov with `IsDiffusionSemigroup F V Kk` and the
  regularity `∀ g ∈ 𝒟, ∀ r, MSmooth (semi Kk r g) ∧ 𝓛(semi Kk r g) = semi Kk r (𝓛 g) ∧ ∃ C, ∀ r y, |semi Kk r g y|, ‖∇ semi Kk r g y‖, |𝓛 semi Kk r g y| ≤ C`
  (A6 + A8). Then `∀ t x, Pt t x = Kk t x`.
  Proof. Fix `g ∈ 𝒟`, `t`, `u_s := semi Kk (t-s) g`. Each `u_s`, `∂_su_s = -𝓛u_s = -semi Kk (t-s)(𝓛g)` is `BddSmooth`, and
  `(u_{s+h}-u_s)/h → ∂_su_s` uniformly in `y` (Lipschitz in time of `semi Kk · (𝓛g)` with constant `‖𝓛²g‖_∞`, `dynkin_bound` for `Kk`). Then
  `F(s) = ∫u_s dP_s(x,·)` satisfies `F(s+h) - F(s) = P_{s+h}(u_{s+h}-u_s) + [P_{s+h}u_s - P_su_s]`, the second bracket equals
  `∫_s^{s+h}P_r(𝓛u_s)dr` by `DynkinBounded`, `r ↦ P_r ψ(x)` is Lipschitz for `ψ ∈ BddSmooth` (again `DynkinBounded`), so `F' = P_s(∂_su_s + 𝓛u_s)(x) = 0`.
  `F(0) = semi Kk t g (x)` (`P_0 = δ` from Dynkin at `t=0`), `F(t) = P_tg(x)`. Thus `P_t g(x) = K_t g(x)` for `g ∈ 𝒟`; measures on a
  locally compact second countable space agree on `𝒟` (density of `𝒟` in `C_c`: Mathlib `Continuous.exists_contMDiff_approx` with support control).

### 2.4 Tier C: the Challenge conclusion

* **C1 (`lower_of_moments`).** Let `D : SplitData M N k ρ μ` (existing), `ν` a probability measure on `M`, `x₀`, `t` with
  `∫ ⟨a,p y⟩ dν = e^{-ρt}⟨a,p x₀⟩` for all `a` (`p = D.proj`), `∫‖p y‖² dν = e^{-2ρt}‖p x₀‖² + (k/ρ)(1-e^{-2ρt})`, `Integrable (‖p ·‖²) ν`. Then
  `ofReal(ρ e^{-2ρt}‖p x₀‖² + k(1-√(1-e^{-2ρt}))²) ≤ ofReal ρ * wasserstein2 ν μ ^ 2`.
  Proof. Coupling `π` of `(ν,μ)`; `edist² ≥ ‖p x - p y‖²`; `E‖X-Z‖² = E‖X‖² + k/ρ - 2E⟨X-m,Z⟩ ` (since `E Z = 0`), and by Cauchy-Schwarz
  `E⟨X-m,Z⟩ ≤ √(tr Σ · k/ρ)` with `tr Σ = E‖X‖²-‖m‖² = (k/ρ)(1-q)`; algebra `q‖p‖² + (k/ρ)(1-√(1-q))²`. (`μ.map p = N(0,ρ^{-1}I)` is in `SplitData`.)
* **C2.** From `hinv` and `hdirac : ∀ x, wasserstein2 (P x) μ ^ 2 ≤ q * ∫⁻ edist x y ^ 2 ∂μ` the upper bound `⨆ x₀∈S` follows directly (cf. `upper_iSup`; no `W2Contraction`).
* **C3 (moments of `P`).** For `P = Kk` (after B2): `u = T_i` (A7, `c = ρ`) gives the mean of `p` (the `a_i` are orthogonal of norm² ρ, hence a basis of `ℝ^k`);
  `u = T_i² - 1` needs `MemLp (T_i²) 2 μ` (Gaussian marginal from `riemannian_gaussian_splitting`) and `𝓛(f²) = 2f𝓛f + 2Γf` (Leibniz, small) with
  `Γ T_i = |a_i|² = ρ`; sum over `i` and use `∑T_i² = ρ‖p‖²` (`sum_sq_inner_of_orthogonal`).
* **C4 (assembly).** `riemannian_wasserstein_estimate_of_canonical`: exactly the Challenge conclusion from `hρ, hgap, hpos`, a `CanonicalDiffusion` family `Kk`, and
  `hPK : ∀ t x, Pt t x = Kk t x`, reusing `riemannian_gaussian_splitting`, `EigenSplitting`, `mLambda_eq_of_splitting`, `SplitData.*`, with C1/C2/C3 in place of `hcontr`, `hmehler`.
  Final theorem = C4 + A1-A10 + B1 + B2 + `CO` (or the strengthening of §6).

### 2.5 `CO`: the geometric input (Laplacian comparison and smoothing). Moonshot, not recommended before everything else.

`theorem oneSidedCutoffs_of_CD : OneSidedCutoffs F V` under `hV, hCD, hρ, [Complete]`. True by classical theory: `ζ = log(2 + d(o,·)²)` smoothed has `Γζ ≤ 1`, `𝓛ζ ≤ C`,
then `χ_n = θ(ζ/n)`, `𝓛χ_n = θ'𝓛ζ/n + θ''Γζ/n² ≥ -C'`. Needed pieces (none in Mathlib; Mathlib has Levi-Civita, `pathELength`, integral curves, partitions of unity):
(CO-1) minimizing curves exist (proper length space, Arzelà-Ascoli, lsc of length) and are smooth geodesics (weak Euler-Lagrange for energy, du Bois-Reymond), ~4k;
(CO-2) link `CD` (Γ₂-form) to `Ric + Hess V ≥ ρ` along curves via the project's Bochner identity and curvature objects (`WeightedBochnerCurv`), ~3k;
(CO-3) second variation barrier: for every `x`, a smooth `B ≥ d²` near `x`, `B(x) = d²(x)`, `𝓛B(x) ≤ C(1+d(x)²)` (test fields `ψ E_i` with `ψ ≡ 1` on `[1/d,1]` so that the weight `Ric_V` appears, near `o` use
`sup_{B(o,1)}|∇V|`), ~8k; (CO-4) smoothing of a function with one-sided barrier Laplacian bounds into a smooth proper function WITHOUT losing uniformity:
chart mollification has an O(1) commutator error `tr((a(x)-a(y))∂²u)` that does not go to 0 with the scale, but it does if the chart is first-order normal at the center
(`∂g(x₀)=0`, obtained by a quadratic coordinate change, no exp map needed); distributional Laplacian inequality from barriers needs Alexandrov's theorem (a.e. second differentiability of
semiconcave functions, absent from Mathlib, ~3k) and a globally bounded `∑|∇ψ_α|` partition of unity (not available without doubling: use heat-flow smoothing + first-order cutoffs fails because second-order
terms reappear; this is the weakest point), ~12k+. Total 25-40k, probability of full success about 30-40%.

### 2.6 Why every cheaper route fails (so nobody re-explores them)

| route | what it gives | why insufficient |
|---|---|---|
| reversibility of `P` (suggested in `transport.md`) | a.e. identification | pointwise-in-x forced by `sup_{x∈S}`; not known to suffice |
| hypoellipticity for measures (finite signed `σ` with `σ((λ-𝓛)f)=0` is smooth) + Kato + Gaffney: gives `μ.bind P = μ` with NO geometry (`σ = λμR^P_λ - μ ≥ -μ`, `η ≥ -1`, mass 0) | invariance, a.e. identification | pointwise needs `P_s(x,·) ≪ μ` for all s; a.c. of the resolvent measure does not give it (a deterministic flow in dimension 1 has a.c. occupation measure) |
| tightness of `P_s(x,·)` without rate (strengthening "no escape to infinity") | nothing | error term `fLχ_n` needs `sup\|𝓛χ_n\| × mass` with no relation between the two |
| analytic vectors / Taylor in `t` | `P_tf = Σ t^k𝓛^kf/k!` | needs `‖𝓛^kf‖_∞ ≤ C^k k!`, false for smooth non-analytic metrics |
| Feller `C_0` property of `R_λ g` (then `f = ψ(u)` compactly supported subsolution) | identification | equivalent to `CO` (needs decay at infinity from curvature) |
| `K_ε`-smoothed cutoffs `𝓛(K_εg) = K_ε(𝓛g) ≥ -C` | smooth cutoffs | not compactly supported (Dynkin only for `𝒟`) |
| `𝓛d ≤ C` from W₁-contraction | `E_x d(o,X_t) - d(o,x) ≲ √t` | need `O(t)`: second-order information is intrinsic |
| Hardy `∫Γf ≥ ∫f²(¼\|∇V\|²-½ΔV)` for tightness | none | no sign on `ΔV` from `Ric_V ≥ ρ` alone |

---------------------------------------------------------------------------------------------------

## 3. Inventory of reusable material

Mathlib (`/chome/djay/S/Maths/Logiciels/Lean/mathlib-v4.35.0-rc2/packages/mathlib/Mathlib`): Lax-Milgram (`InnerProductSpace/LaxMilgram`), Riesz,
continuous functional calculus (use for `T_t`), Rademacher (`Analysis/Calculus/Rademacher`, `LipschitzWith.ae_differentiableAt`), new Sobolev theory on tempered
distributions (`Analysis/Distribution/Sobolev`, `BesselPotentialSpace`, Fourier multipliers; NO Sobolev embedding, NO variable coefficients), Gagliardo-Nirenberg-Sobolev
(`Analysis/FunctionalSpaces/SobolevInequality`, only `C¹_c`), smooth partitions of unity, bump functions, `SmoothApprox` (`Continuous.exists_contMDiff_approx`),
Levi-Civita connection, `pathELength`/`riemannianEDist`, integral curves, tightness (`MeasureTheory/Measure/Tight`), Prokhorov-Levy metric, Riesz-Markov-Kakutani. Absent: Friedrichs extension,
Hille-Yosida, Beurling-Deny, spectral theorem for unbounded operators, Hopf-Rinow, geodesics, exponential map, second variation, Riemannian curvature tensor, Alexandrov, Kantorovich duality.

Project (Euclidean templates, 60 `Gibbs*` files ≈ 10k lines, `Langevin*` 16k): `GibbsSelfAdjoint`, `GibbsResolventOrder` (positivity of the variational resolvent via the negative part), `GibbsEulerApproximation`,
`StrongContractionLimit`, `GibbsHeatSemigroup`, `GibbsHeatMarkov`, `GibbsSpectralGap` (attainment pattern), `GibbsCompactEmbedding` + `L2CompactnessTools` + `GibbsLocalizedTranslations` (tightness + local
translation bounds ⇒ compact inclusion), `LocalPoincareSobolev`, `LogSobolev*`, `HopfLax*`, `Talagrand`. Transport: `CompactTransportDuality`, `CompactLipschitzTransportDuality`,
`EuclideanLipschitzTransportDuality` (budget form of Kantorovich duality via Riesz extension + RMK; Euclidean clipping), `TransportCouplingCompactness`, `Transport.lean`.
Riemannian: see section 1. The Euclidean Gibbs development avoided smoothness (weak `H²_loc` only) and identified the semigroup pointwise through an SDE; neither is available on `M`.

---------------------------------------------------------------------------------------------------

## 4. Interfaces and DAG

### 4.1 The decoupling interface (`CutoffRigidity/Riemann/DiffAPI.lean`, lead writes it first, no `sorry`)

```lean
namespace CutoffRigidity.Riemann.Diff
noncomputable def semi (Pt : ℝ≥0 → Kernel M M) (t : ℝ≥0) (f : M → ℝ) : M → ℝ := fun x => ∫ y, f y ∂(Pt t x)

/-- Output of Tier A = input of Tiers B and C. -/
structure CanonicalDiffusion (V : M → ℝ) (μ : Measure M) (ρ : ℝ) (Kk : ℝ≥0 → Kernel M M) : Prop where
  markov : ∀ t, IsMarkovKernel (Kk t)
  dynkin : IsDiffusionSemigroup F V Kk
  invariant : ∀ t, μ.bind (Kk t) = μ
  eigen : ∀ (c : ℝ) (u : M → ℝ), MSmooth F u → MemLp u 2 μ → (∀ x, mgenerator F V u x = -c * u x) →
      ∀ (t : ℝ≥0) (x : M), Integrable u (Kk t x) ∧ ∫ y, u y ∂Kk t x = Real.exp (-c * t) * u x
  smoothing : ∀ g, MSmooth F g → HasCompactSupport g → ∀ t, MSmooth F (semi Kk t g) ∧
      mgenerator F V (semi Kk t g) = semi Kk t (mgenerator F V g) ∧
      ∃ C, ∀ (s : ℝ≥0) x, |semi Kk s g x| ≤ C ∧ ‖mgrad F (semi Kk s g) x‖ ≤ C ∧ |mgenerator F V (semi Kk s g) x| ≤ C
  contraction : ∀ (t : ℝ≥0) (x : M), CutCur.wasserstein2 (Kk t x) μ ^ 2 ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ∫⁻ y, edist x y ^ 2 ∂μ
```
Workstream outputs: A-stream proves `∃ Kk, CanonicalDiffusion F V μ ρ Kk` (`exists_canonicalDiffusion`) and `diff_gap_attained`; B proves `identification`; C proves
`riemannian_wasserstein_estimate_of_canonical`. `OneSidedCutoffs`, `DynkinBounded`, `BddSmooth` as in 2.3 live in `DiffDynkinBounded.lean`.

### 4.2 DAG (arrows = "uses")

```
        FR ─────────┐
        DIR (A1,A3) ┼─> KER (A4,A6,A7) ─> BE (A8) ─┬─> KUW-B (A10) ──┐
        REGn ─> REG (A5, manifold) ──┘               └─> HPOS (A9) ───┤
        KUW-A (duality on M) ─────────────────────────────────────────┤
                                                                       v
        MOM (C1,C2,C3,C4) ──────────────────────────────> FINAL(canonical, `exists_canonicalDiffusion`)
        ID (B1,B2) ─────────────────────────────────────> FINAL (needs CO, or §6 strengthening)
        CO (moonshot) ──> OneSidedCutoffs
```
Wave 0 (start now, no waiting): FR, REGn, DIR, KUW-A, MOM, ID. Wave 1: KER, REG(manifold), BE, KUW-B, HPOS. Wave 2: FINAL assembly (+ the strengthened statement), decision on CO.
Workstreams that consume `CanonicalDiffusion` (MOM, ID) develop against the structure and are instantiated at FINAL; DIR consumes the generic statement of FR as a
`structure` (fields = FR's conclusions) and REG-manifold consumes REGn the same way.

---------------------------------------------------------------------------------------------------

## 5. Sizes, risks, order

| id | content | files (new) | lines | risk |
|---|---|---|---|---|
| FR | generic Friedrichs resolvent, form domain, `cfc` semigroup, Euler limit | `DiffFriedrichs`, `DiffCfcSemigroup` | 3.5-5k | low-med |
| DIR | density, symmetry, normal contractions, Beurling-Deny, `1∈Q`, chart transfer of weak equation | `DiffForm`, `DiffMarkov`, `DiffChart` | 3-4.5k | med |
| REGn | ℝⁿ elliptic regularity, local Sobolev, embedding, quantitative | `DiffEllipticRn`, `DiffSobolevRn` | 6-9k | med-high (volume) |
| REG | manifold regularity, `T_t` smoothing estimates, kernel `Kk` (A5-A7) | `DiffRegular`, `DiffKernel` | 4-6k | med |
| BE | pointwise Bakry-Émery (A8) | `DiffBakryEmery` | 4-7k | med-high (integrability) |
| HPOS | LSI, tightness, local Rellich, attainment (A9) | `DiffLSI`, `DiffRellich`, `DiffGapAttained` | 6-9k | med |
| KUW-A | Kantorovich budget duality on proper metric space | `DiffKantorovichProper` | 2-3.5k | med |
| KUW-B | Hopf-Lax one-sided inequality, Kuwada interpolation (A10) | `DiffHopfLax`, `DiffKuwada` | 3-5k | med |
| MOM | C1-C4 | `DiffLowerMoments`, `DiffMoments`, `DiffAssembleCanonical` | 2.5-4k | low-med |
| ID | B1, B2 | `DiffDynkinBounded`, `DiffIdentify` | 2.5-3.5k | low-med |
| FINAL | wiring, `exists_canonicalDiffusion`, Solution update | `DiffFinal` | 0.5k | low |
| **Total without CO** | | | **≈ 38-58k (point estimate 45k)** | |
| CO | geometry (2.5) | `DiffGeo*` | 25-40k (+ risk) | very high |

Recommended order: Wave 0 in parallel; as soon as FR+DIR+REGn exist, REG/KER; then BE; then KUW-B, HPOS in parallel; FINAL for the canonical diffusion
(a *conditional* theorem with hypothesis `DynkinBounded Pt` or `OneSidedCutoffs F V`, which is already a strict improvement: it discharges `hpos`, `hinv`, `hcontr`, `hmehler` at once);
then the owner decides between §6-S1/S1' (cheap) and CO (expensive). The whole DAG has depth 4 so wall-clock time is dominated by the longest chain
REGn → REG → BE → KUW-B (≈ 20k lines).

---------------------------------------------------------------------------------------------------

## 6. Open points, possible strengthenings

(a) Statements that I could not fully verify at proof level (all believed true, classical): (U1) BE with the integrability bookkeeping of A8 on a manifold without bounded geometry
(the `(ii)` cutoff bound looks right, `Φ = K_sζ` bounded in `𝒮`, `Hess w ∈ L²`); (U2) the `√`-version needed for LSI (Kato + `√(Γ+ε)`); (U3) `CO-4` smoothing uniformity (see 2.5);
(U4) quantitative interior estimates in A5 with the exact constants needed for `sup_K|T_tu| ≤ C(K,t)‖u‖` (standard).
(b) No statement of the plan is false as stated. Claims of the *existing notes* that I contradict: `diffusion.md` §3(a) "need `Δ_Vd ≤ C(1+d)` and a smoothing preserving two-sided bounds" (one-sided bounded below
suffices, F3); `transport.md` §1 (ii) "the sign of the Laplacian comparison is wrong for `f²𝓛χ_n`" (it is right after the mass trick); "reversibility is the minimal extra property" (not enough for
pointwise statements; not known to suffice at all); "Mehler law needed" (only two moments).
(c) Faithful strengthenings (the lead may offer them to the owner; each avoids CO):
* **S1 (about `Pt`, minimal).** Replace clause 3 of `IsDiffusionSemigroup` (Dynkin for `f ∈ C_c^∞`) by Dynkin for `f ∈ BddSmooth` (smooth with `f`, `‖∇f‖`, `𝓛f` bounded). It is stronger (C_c^∞ ⊂ BddSmooth)
  and still literally "Kolmogorov's equation for the diffusion with generator 𝓛"; it is true for the actual (minimal, conservative) diffusion under completeness + CD(ρ,∞) (Itô + non-explosion + dominated convergence); it excludes
  the Feller re-entry pathologies; with S1 the bridge B2 holds without B1 and without CO. Everything else (Tier A, C) is unchanged.
* **S1' (about `(M,V)` only, leaves `Pt` untouched).** Add the hypothesis `OneSidedCutoffs F V` (`hcut`) to the theorem; it is a classical geometric fact (Laplacian comparison under Ric_V ≥ ρ + smoothing), not a property of `Pt`.
* NOT sufficient (do not propose): reversibility, tightness, invariance of `μ`, `P_t` Feller.
(d) What is irreducibly Riemannian: A5 (regularity on charts), A8 (Bakry-Émery) and A10 (Kuwada on `N`). What the splitting buys: only C3 (explicit moments of the Euclidean factor).
(e) Side result worth keeping: `exists_canonicalDiffusion` shows `IsDiffusionSemigroup F V Pt` is satisfiable under the standing hypotheses.

---------------------------------------------------------------------------------------------------

## 7. The first six workstream briefs (self-contained; launch in parallel)

Common rules: Lean/Mathlib as pinned by the project; read `RIEMANNIAN_PLAN.md` rules; module system headers copied from `CutoffRigidity/Riemann/DiffusionRegular.lean`; no `sorry`, no `axiom`,
no `native_decide`; statements below may be adapted ONLY to make types elaborate (never weakened, never replaced by hypotheses that encode the conclusion); each file < 1500 lines; report in
`riemann-status/diff-<name>.md` (declarations + exact statements + blockers). Do not edit `CutoffRigidity.lean` or any file outside your own `Diff<Name>*.lean`.
Forbidden shortcuts for ALL briefs: assuming the conclusion as a structure field; assuming smoothness, compactness, positivity or conservativity of the objects you construct; stating hypotheses of the form
"`∃ P` with property X" where X is the thing to prove; using `Classical.choice` tricks to define a semigroup without proving its properties.

### WS-FR: generic Friedrichs resolvent and `cfc` semigroup  (`DiffFriedrichs.lean`, `DiffCfcSemigroup.lean`)
Goal: A2 and A4 for an abstract Hilbert space.
```lean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
structure FormData (H) ... where (D : Submodule ℝ H) (dense : Dense (D : Set H)) (A : D →ₗ[ℝ] H)
  (symm : ∀ f g : D, inner ℝ (A f) (g : H) = inner ℝ (f : H) (A g)) (nonneg : ∀ f : D, 0 ≤ inner ℝ (A f) (f : H))
def FormData.Q (S : FormData H) : Set H   -- limits in H of sequences in D that are Cauchy for the energy
noncomputable def FormData.E (S : FormData H) : S.Q → S.Q → ℝ   -- well defined bilinear energy (closability!)
theorem FormData.exists_resolvent (S : FormData H) (λ : ℝ) (hλ : 0 < λ) : ∃ R : H →L[ℝ] H,
  IsSelfAdjoint R ∧ (∀ u, 0 ≤ inner ℝ (R u) u) ∧ Function.Injective R ∧ (∀ g, R g ∈ S.Q) ∧
  (∀ (f : S.D), R (λ • (f : H) + S.A f) = f) ∧ (∀ g (φ : S.Q), S.E (R g) φ + λ * inner ℝ (R g) φ = inner ℝ g φ) ∧ ‖R‖ ≤ 1/λ
-- resolvent identity R_λ - R_μ = (μ-λ) R_λ R_μ; and, with R = R_1:
noncomputable def cfcSemigroup (R : H →L[ℝ] H) (hR : IsSelfAdjoint R) (h0 : 0 ≤ R) (h1 : R ≤ 1) (t : ℝ≥0) : H →L[ℝ] H
theorem cfcSemigroup_zero, cfcSemigroup_add, norm_cfcSemigroup_le_one, cfcSemigroup_isSelfAdjoint
theorem cfcSemigroup_eq_lim_euler (hinj : Function.Injective R) (u : H) (t : ℝ≥0) :
  Tendsto (fun n : ℕ => ((((n+1:ℝ)/t) • resolventλ ((n+1)/t)) ^ (n+1)) u) atTop (𝓝 (cfcSemigroup R .. t u))   -- norm convergence via Dini
theorem cfcSemigroup_eigen (u) (c ≥ 0) (hu : R u = (1+c)⁻¹ • u) : cfcSemigroup R .. t u = Real.exp (-c*t) • u
theorem cfcSemigroup_hasDerivAt (g : H) : HasDerivAt (fun t : ℝ => cfcSemigroup R .. t.toNNReal (R g)) (-(cfcSemigroup R .. t (g - R g))) t  (t > 0, and right-derivative at 0)
```
Math: Friedrichs by completion (closability from symmetry, see A2); `cfc` with `h_t(r) = exp(-t(1/r-1))`, `h_t(0)=0`, monotone Euler functions + Dini. Read: Mathlib `cfc`, `Analysis/InnerProductSpace/LaxMilgram`, project `GibbsSelfAdjoint`, `GibbsEulerApproximation`, `StrongContractionLimit`, `GibbsResolventBounds`.
Forbidden: assuming compactness of `R`, using the spectral theorem for compact operators, assuming `Q` is complete/closed without proof.

### WS-REGn: elliptic regularity in ℝⁿ  (`DiffEllipticRn.lean`, `DiffSobolevRn.lean`)
Goal: A5(i), purely Euclidean, with variable smooth coefficients.
```lean
-- E := EuclideanSpace ℝ (Fin n); H^m_loc defined with Mathlib's `TemperedDistribution.MemSobolev`/`H^{m,2}` applied to `χ u`, or with weak derivatives (your choice, but export the elementary statements below)
theorem weak_solution_regular_step {Ω : Set E} (hΩ : IsOpen Ω) (a : E → E →L[ℝ] E) (ϱ : E → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
  (ha : ContDiffOn ℝ ⊤ a Ω) (hϱ : ContDiffOn ℝ ⊤ ϱ Ω) (hsym : ∀ x ∈ Ω, ∀ v w, inner ℝ (a x v) w = inner ℝ v (a x w))
  (hell : ∀ x ∈ Ω, ∃ c > 0, ∀ v, c * ‖v‖^2 ≤ inner ℝ (a x v) v) (hpos : ∀ x ∈ Ω, 0 < ϱ x)
  (u g : E → ℝ) (m : ℕ) (hu : LocH1 Ω u) (hg : LocSobolev Ω m g)
  (hweak : ∀ φ : E → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
     ∫ x in Ω, (inner ℝ (a x (weakGrad u x)) (gradient φ x) + lam * u x * φ x) * ϱ x = ∫ x in Ω, g x * φ x * ϱ x) :
  LocSobolev Ω (m+2) u
theorem interior_estimate : ∀ K ⊂ Ω' ⊂⊂ Ω compact/open, ∃ C, ∀ u g (as above), ‖u‖_{H^{m+2}(K)} ≤ C (‖g‖_{H^m(Ω')} + ‖u‖_{L²(Ω')})
theorem sobolev_embedding_loc (j m) (hm : j + n/2 < m) : LocSobolev Ω m u → ∃ ū, ContDiffOn ℝ j ū Ω ∧ u =ᵐ[volume.restrict Ω] ū ∧ ∀ K compact, sup_K ‖D^i ū‖ ≤ C ‖u‖_{H^m(K')}
theorem weak_solution_smooth (all m, all g smooth) : ∃ ū, ContDiffOn ℝ ⊤ ū Ω ∧ u =ᵐ ū
```
Math: Evans §6.3 (tangential difference quotients, Caccioppoli-type energy bound, induction on `m`); Mathlib Fourier characterization for "bounded difference quotients ⇒ derivative in `L²`".
Read: Mathlib `Analysis/Distribution/Sobolev`, `FourierMultiplier`, `Analysis/Fourier/LpSpace`; project `GibbsWeakDerivative`, `GibbsLocalizedTranslations`, `GibbsOperatorWeakHessian`, `GibbsCompactSmoothing` (templates for weak derivatives and localization).
Forbidden: assuming H² regularity or a Calderón-Zygmund estimate as hypothesis; constant coefficients only; assuming `u` smooth; Schauder theory (not needed).

### WS-DIR: manifold-side form facts  (`DiffForm.lean`, `DiffMarkov.lean`, `DiffChart.lean`)
Goal: A1, A3, and the chart interface of A5(ii). Works against the generic `FormData`/`exists_resolvent` of WS-FR (take them as a `structure FriedrichsOutput` of fields until FR lands) and against REGn's statement.
```lean
def testSub : Submodule ℝ (M → ℝ)  -- smooth, compact support
theorem dense_test : Dense ((fun f : testSub => (MemLp.toLp f ..)) '' univ)  -- in M →₂[μ] ℝ (μ finite, Radon, full support)
noncomputable def diffFormData : FormData (M →₂[μ] ℝ)  -- A := -𝓛; symm/nonneg from `weightedIBP_of_isWeightedVolume`
theorem normalContraction_stable (θ : ℝ → ℝ) (hθ : ContDiff ℝ ⊤ θ) (h0 : θ 0 = 0) (h1 : ∀ s, |deriv θ s| ≤ 1) (f ∈ testSub) :
  θ ∘ f ∈ testSub ∧ ∀ x, carre F (θ ∘ f) (θ ∘ f) x ≤ carre F f f x
theorem resolvent_posPreserving / resolvent_le_one (Beurling-Deny, general `(α, μ)` Markov-form lemma first)
theorem one_mem_Q : (1 : M →₂[μ] ℝ) ∈ diffFormData.Q ∧ diffFormData.E 1 1 = 0   -- via `weightedCutoffs_of_complete`
theorem Q_chart_weak (x₀ : M) : ∀ u ∈ Q, ∃ (Du : F → F) , IsWeakGradInChart x₀ u Du ∧ [weak equation in the chart for every smooth test function supported in the chart source, with a = g⁻¹, ϱ = e^{-V}·chartVolumeDensity]
theorem Q_smooth_of_weak_eq (REGn instantiated) : u ∈ Q, (weak equation with smooth/H^m g) → ∃ ū, MSmooth F ū ∧ u =ᵐ[μ] ū
```
Read: `Riemann/WeightedInterface`, `WeightedIBPGlobal`, `WeightedIBPChart`, `WeightedIBPCoord`, `WeightedIBPDensity`, `WeightedCutoffs`, `WeightedSupport`, `MeasureChart`; Euclid `GibbsResolventOrder` (positivity pattern), `GibbsSobolevPositivePart`, `GibbsSobolevContraction`.
Forbidden: vector-valued `L²` of the gradient via assuming a divergence theorem for arbitrary vector fields (not needed); assuming closability; proving positivity only on `𝒟`.

### WS-KUW-A: Kantorovich budget duality on a proper metric space  (`DiffKantorovichProper.lean`)
Goal: the non-compact budget duality for `cost2`.
```lean
theorem cost2_le_of_lipschitz_dual_budget {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (K : ℝ)
  (hDual : ∀ (f g : X →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g → (∀ x y, f x + g y ≤ dist x y ^ 2) → ∫ x, f x ∂μ + ∫ y, g y ∂ν ≤ K) :
  CutCur.Riemann.cost2 μ ν ≤ ENNReal.ofReal K
-- corollary for the connected complete Riemannian `M` (edist ≠ ⊤, `properSpace_of_complete_riemannian`), stated with `edist` and `wasserstein2`
theorem wasserstein2_sq_le_of_dual_budget_manifold : ... wasserstein2 μ ν ^ 2 ≤ ENNReal.ofReal K
```
Math: replicate `EuclideanLipschitzTransportDuality`: truncate to compacts by tightness (replace the Euclidean radial clip by restriction to compact `K_n` plus mass sent to a base point, or by clipping the cost), apply `exists_compact_transport_coupling_of_lipschitz_dual_budget`, pass to the limit with `exists_coupling_limit_of_marginals_tendsto`. Handle `edist ≠ ⊤` (metric from `edist` on connected `M`).
Read: `CompactTransportDuality`, `CompactLipschitzTransportDuality`, `EuclideanLipschitzTransportDuality`, `EuclideanCompactClipping`, `TransportCouplingCompactness`, `Transport`, `Riemann/TransportW2`, `Riemann/WeightedProper`.
Forbidden: assuming a finite second moment, assuming Prokhorov for non-tight families without proof, assuming Kantorovich duality.

### WS-MOM: lower bound from two moments, upper bound from Dirac contraction, assembly  (`DiffLowerMoments.lean`, `DiffMoments.lean`, `DiffAssembleCanonical.lean`)
Goal: C1-C4 against `CanonicalDiffusion` (section 4.1) and `hpos` as hypotheses.
```lean
theorem SplitData.lower_of_moments  -- C1 (statement in 2.4)
theorem upper_iSup_dirac (μ) [IsProbabilityMeasure μ] (P : Kernel M M) [IsMarkovKernel P] {q : ℝ≥0∞}
  (h : ∀ x, wasserstein2 (P x) μ ^ 2 ≤ q * ∫⁻ y, edist x y ^ 2 ∂μ) (S : Set M) : ⨆ x₀ ∈ S, wasserstein2 (P x₀) μ ^ 2 ≤ q * ⨆ x₀ ∈ S, ∫⁻ y, edist x₀ y ^ 2 ∂μ
theorem mgenerator_sq (f) (hf : MSmooth F f) : ∀ x, mgenerator F V (fun y => f y ^ 2) x = 2 * f x * mgenerator F V f x + 2 * carre F f f x
theorem eigen_moments (hK : CanonicalDiffusion F V μ ρ Kk) (D : SplitData ..) (E : EigenSplitting ..) (x₀ t) :
  (∀ a, ∫ y, inner ℝ a (D.proj y) ∂Kk t x₀ = exp(-ρ t) * inner ℝ a (D.proj x₀)) ∧ ∫ y, ‖D.proj y‖^2 ∂Kk t x₀ = exp(-2ρ t) * ‖D.proj x₀‖^2 + (k/ρ) * (1 - exp(-2ρ t)) ∧ Integrable (‖D.proj ·‖^2) (Kk t x₀)
theorem riemannian_wasserstein_estimate_of_canonical ... (hpos : 0 < mFirstEigenDim F μ V) {Pt} (Kk) (hK : CanonicalDiffusion F V μ ρ Kk)
  (hPK : ∀ t x, Pt t x = Kk t x) (t : ℝ≥0) : <verbatim conclusion of the Challenge `riemannian_wasserstein_estimate`>
```
Math: 2.4. Obtain `SplitData`/`EigenSplitting` exactly as `WassAssemble.lean` does from `riemannian_gaussian_splitting` (read it; replace its use of `hcontr`, `hmehler`).
Read: `Riemann/WassAssemble`, `WassMehler`, `TransportMain`, `TransportLower`, `TransportUpper`, `TransportGauss`, `TransportAlgebra`, `TransportW2`, `AssembleMain`, `EigenFinite`, Mathlib Gaussian moments.
Forbidden: adding the Gaussian-law hypothesis `hmehler`, assuming `hcontr` for arbitrary pairs, changing the conclusion.

### WS-ID: Dynkin on bounded smooth functions and the bridge `Pt = Kk`  (`DiffDynkinBounded.lean`, `DiffIdentify.lean`)
Goal: B1 and B2 (section 2.3), independent of Tier A except through the regularity field of `CanonicalDiffusion`.
```lean
theorem measurable_semi_time (hP : IsDiffusionSemigroup F V Pt) (g : M → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ y, |g y| ≤ C) (x) : Measurable fun s : ℝ => ∫ y, g y ∂Pt s.toNNReal x
theorem dynkinBounded_of_oneSidedCutoffs (hP : IsDiffusionSemigroup F V Pt) (hc : OneSidedCutoffs F V) : DynkinBounded F V Pt
theorem identification (hP : IsDiffusionSemigroup F V Pt) (hD : DynkinBounded F V Pt) (hK : CanonicalDiffusion F V μ ρ Kk) : ∀ (t : ℝ≥0) x, Pt t x = Kk t x
-- and the stand-alone time-dependent form
theorem hasDerivAt_semi_pair ... : HasDerivAt (fun s => ∫ y, u s y ∂Pt s x) (∫ y, (∂ₛu s y + mgenerator F V (u s) y) ∂Pt s x) s
```
Math: 2.3 (mass trick, then time-dependent derivative; use `DiffusionRegular` for `P_0 = δ`, Lipschitz-in-time, continuity). Measure equality on `𝒟`: `Measure.ext_of_integral_eq_on_compactlySupported` plus `Continuous.exists_contMDiff_approx`.
Read: `Riemann/DiffusionRegular`, `WeightedCutoffs`, `WeightedInterface`, `WeightedPointwise`, Mathlib `Kernel.integral_comp`, monotone class (`MeasurableSpace.induction_on_inter`).
Forbidden: assuming `P` is Feller, symmetric, or tight; assuming the Dynkin identity on `BddSmooth` in the proof of `dynkinBounded_of_oneSidedCutoffs`; using `P_t` smoothing of non-compactly supported functions.

### Next briefs (after Wave 0, same format, written by the lead from sections 2.2-2.5): KER (A4/A6/A7/REG-manifold), BE (A8), HPOS (A9), KUW-B (A10), FINAL, and CO (only on owner's approval).
