# CO_PLAN: how to get the bridge `Pt = Kk` WITHOUT `OneSidedCutoffs` (and without any Laplacian comparison)

Author: `coplan` designer. Status: design only, nothing proved. Reads: `RIEMANNIAN_PLAN.md`, `DIFFUSION_PLAN.md` (2.3, 2.5, 2.6, 6),
`DiffDynkinBounded.lean`, `DiffAPI.lean`, `DiffIdentify.lean`, and the DIR/FR/REGn status files and the actual `DiffInstance/DiffMarkov/DiffForm` APIs.

---------------------------------------------------------------------------------------------------

## 0. Verdict

0.1 **Route (3) works, and in a stronger form than suggested: no geometry at all is needed for the bridge.** For a complete connected
weighted manifold with `μ` FINITE (probability), every `Pt` with `IsDiffusionSemigroup F V Pt` equals the canonical `Kk`, i.e. the classical
statement "a Markov solution of Kolmogorov's (Fokker-Planck) equation on `C_c^∞` dominates the minimal one, and equality of total masses forces
equality" is true and provable with:
* the Friedrichs/Tier-A objects (resolvent, positivity, `R_λ 1 = λ^{-1}`), which exist;
* elliptic regularity (already needed for Tier A) **extended by a bounded smooth zero-order potential** (bootstrap, no new idea);
* a **penalization barrier** (killing potential `κ = K θ(ζ - a)` with `ζ` a smooth proper function) that produces COMPACTLY SUPPORTED smooth
  SUBSOLUTIONS approximating `R_λ g` from below. Only local geometry (continuity of `Γζ`, `𝓛ζ` on a compact shell) enters, never `𝓛 d ≤ C`.
Estimated cost: **5.5-9k lines (point estimate 7k), success probability about 75%**, versus 25-40k lines at about 35% for the classical `CO` route.
`OneSidedCutoffs`, `DynkinBounded`, `dynkinBounded_of_oneSidedCutoffs` (B1) and B2 (time-dependent duality) become UNNECESSARY (they stay as
valid conditional results; nothing already written is wasted for Tier C).

0.2 **Correction of DIFFUSION_PLAN (F4) and table 2.6.** "`OneSidedCutoffs` is irreducibly geometric" is false as a statement about what the *bridge*
needs. The mass trick of B1 needs product cutoffs because it tests Dynkin against `χ_n f` and then needs error control. The right test functions
are not products but `θ_ε(v)` with `v` a *penalized resolvent*: then `(λ-𝓛)θ_ε(v) ≤ g` holds EXACTLY and pointwise (convexity), there are no error terms,
nothing to control at infinity, and compact support is forced by the barrier. The row "Feller `C_0` ... equivalent to CO" is also wrong: on `ℝ` with
`V = x⁴ + x²` (CD(ρ,∞), ρ>0, probability `e^{-V}`) the diffusion comes down from infinity, `K_t g(x) → c_t(g) > 0` as `x → ∞`, so `K` is not Feller,
yet everything below applies. (Every proper Lyapunov function from hitting times, i.e. route (2), also fails there: `E_x τ_B` is bounded in `x`.)

0.3 Consequences for the programme: new minimal dependency of the final theorem is
`Tier A + BRIDGE + PERRON`; drop `CO`, B1, B2. Total programme size drops from "45k + 30k moonshot" to about 45k + 7k, and the last open hypothesis
disappears from the Challenge theorem (no S1/S1' strengthening needed).

---------------------------------------------------------------------------------------------------

## 1. Setting, notation (as in DIFFUSION_PLAN §1; `μ` probability)

`𝒟 = testSub F M` (smooth, compact support), `L = mgenerator F V`, `Γ = carre F`, `H = M →₂[μ] ℝ`, `T = diffT F hV hμ`, `Rλ = (diffFR F hV hμ).resolvent λ`,
`semi P t f x = ∫ f ∂(P t x)`. `U^P_λ g (x) := ∫ s in Ioi 0, exp(-λ s) * semi P s g x` for `g ∈ 𝒟` (the integrand is continuous in `s` by `DiffusionRegular.dynkin_lipschitz`).

---------------------------------------------------------------------------------------------------

## 2. Route (3) in detail (the mathematics)

### 2.1 Resolvent form of Dynkin (elementary)
For `IsDiffusionSemigroup F V P`, `λ>0`, `f ∈ 𝒟`, every `x`:  `λ U^P_λ f - U^P_λ(𝓛 f) = f(x)`, i.e. `U^P_λ((λ-𝓛)f)(x) = f(x)`.
(Multiply `P_t f = f + ∫_0^t P_s 𝓛f ds` by `e^{-λt}`, integrate in `t`, Fubini; everything is continuous and bounded.)
`U^P_λ` is monotone on `𝒟` (`P_s` positive). Hence:

**(Subsolution inequality)** if `f, g ∈ 𝒟`, `g ≥ 0` and `(λ-𝓛) f ≤ g` pointwise, then `f(x) ≤ U^P_λ g(x)` for every `x`.
So `U^P_λ g(x) ≥ sup{ f(x) : f ∈ 𝒟, (λ-𝓛) f ≤ g }` =: Perron value.

### 2.2 Perron property of `K` (the heart, PERRON workstream)
**Claim (MinimalResolvent).** For `g ∈ 𝒟`, `g ≥ 0`, `λ>0`, `x ∈ M`, `η>0` there is `f ∈ 𝒟` with `(λ-𝓛)f ≤ g` and `f(x) ≥ u(x) - η`, where `u` is the smooth
representative of `R_λ g` (equal to `U^K_λ g` everywhere).

Construction (no Dirichlet problem, no boundary regularity, no Laplacian comparison):
1. `ζ : M → [0,∞)` smooth proper (`exists_smooth_lip_approx` applied to `d(o,·)`, plus `properSpace_of_complete_riemannian`): sublevel sets `{ζ ≤ c}` compact.
2. Step function `θ₀` smooth, `0` on `(-∞,0]`, `1` on `[1,∞)`, nondecreasing. For `a` large (`supp g ⊂ {ζ < a}`) and `K>0` put `κ = K·θ₀(ζ - a)`: smooth, `0 ≤ κ ≤ K`, `κ = 0` on `{ζ ≤ a}`, `κ = K` on `{ζ ≥ a+1}`.
3. **Penalized resolvent** `v = v_{a,K} ∈ Q`: the unique `v ∈ Q` with `E(v,φ) + λ⟨v,φ⟩ + ⟨κv,φ⟩ = ⟨g,φ⟩` for all `φ ∈ Q`.
   Construction WITHOUT new form theory: Neumann series `v = Σ_j (R_{λ+K} M_{K-κ})^j R_{λ+K} g` (here `‖R_{λ+K} M_{K-κ}‖ ≤ K/(λ+K) < 1`, `M_{K-κ}` the multiplier by `K-κ ∈ [0,K]`).
   Because `R_{λ+K} ≥ 0` (`diff_resolvent_nonneg`) and `K-κ ≥ 0`, every term is `≥ 0`: **positivity is free**. Same argument gives: `κ ≤ κ' ⇒ v^{κ'} ≤ v^{κ}`
   (`w = v^κ - v^{κ'}` solves the `κ'`-equation with RHS `(κ'-κ) v^κ ≥ 0`), `v^κ ≤ u := R_λ g`, and `v ≤ ‖g‖_∞/λ` (compare with the constant `‖g‖/λ`, using `1 ∈ Q`, `E(1,·)=0`).
   Energy bound: `E(v,v) + λ‖v‖² + ∫κ v² = ⟨g,v⟩ ≤ ‖g‖‖u‖`.
4. **Regularity** (REG, with potential): `v` has a smooth representative with `L v = (λ+κ) v - g` pointwise. (Bootstrap: RHS `g - κ v ∈ H^m_loc ⇒ v ∈ H^{m+2}_loc`; the chart lemma
   `chart_weak_equation` already allows measurable/`L²` right-hand sides, and `locSob_step` of `DiffEllipticRn17` does the induction step.)
5. **Barrier** (only compact-shell geometry). `β(t) = b(t-a-1)`, `b` smooth nondecreasing, `b = 0` on `(-∞,0]`, `b ≡ 1` on `[1,∞)` (so the shell is `ζ ∈ [a+1,a+2]`),
   `ψ = exp(-s β∘ζ)`. Then `(λ+κ-L)ψ = ψ[λ + κ - s²β'²Γζ + s(β' Lζ + β'' Γζ)]`, which is `≥ 0` EVERYWHERE provided `K ≥ s² B₁² G + s(B₁Λ + B₂G)` where
   `G = sup_{shell} Γζ`, `Λ = sup_{shell} |Lζ|`, `B₁ = sup b'`, `B₂ = sup |b''|` (finite because the shell is compact; outside the shell `β' = β'' = 0`, and `ψ ≡ 1` on `{ζ ≤ a+1}`).
   Choose `s = s(K) → ∞` (e.g. `s = min(√(K/(2B₁²G+1)), K/(2(B₁Λ+B₂G)+1))`).
   **Comparison** `u' := v - Cψ`, `C = ‖g‖/λ`: `u' ≤ 0` on `{ζ ≤ a+1}` and `L u' ≥ (λ+κ)u'` on `{u' > 0} ⊂ {ζ > a+1}` (there `g = 0`). Energy maximum principle
   (Gaffney cutoffs `η_n`, `μ(M)<∞`, test function `η_n² G(u')` with `G(s) = e^{-1/s}` for `s>0`, `G=0` otherwise; Cauchy-Schwarz absorption with `G²/G' = G s² ≤ C`):
   `∫η_n² G'(u')Γu' + λ∫η_n² G(u')u' ≤ 4 ‖∇η_n‖²_∞ C μ(M) → 0`, hence `u' ≤ 0`. So `v ≤ C e^{-sβ(ζ)} ≤ C e^{-s}` on `{ζ ≥ a+2}`.
   (Geometry-free: needs only IBP for compactly supported test function, completeness through Gaffney cutoffs, finiteness of `μ`.)
6. **Compactly supported subsolution.** Given `ε>0` choose `K` with `C e^{-s(K)} < ε`. Let `θ_ε` be smooth convex nondecreasing, `θ_ε = 0` on `(-∞,ε]`, `θ_ε' ∈ [0,1]`, `θ_ε(r) ≥ r - 2ε`. Put `f = θ_ε ∘ v`.
   * `f` is smooth, `supp f ⊂ {v ≥ ε} ⊂ {ζ ≤ a+2}` compact: **`f ∈ 𝒟`**.
   * `L f = θ'(v) L v + θ''(v) Γv ≥ θ'(v) L v`, hence
     `(λ-L) f ≤ λθ(v) - θ'(v)((λ+κ)v - g) = λ(θ(v) - vθ'(v)) - κ v θ'(v) + θ'(v) g ≤ θ'(v) g ≤ g`
     (convexity and `θ(0)=0` give `θ(r) ≤ rθ'(r)`; `v ≥ 0`, `κ ≥ 0`). **Exactly, pointwise, no error term.**
   * `f(x) ≥ v(x) - 2ε`.
7. **`v_{a,K}(x) → u(x)`.** For fixed `a`, `v_{a,K}` decreases in `K`; let `v_a^D = lim_K v_{a,K}` in `L²` (monotone, bounded). By `closed_of_bounded` (lower semicontinuity) `v_a^D ∈ Q`, `E(v^D_a) ≤ C₀`;
   for `φ ∈ 𝒟` with `supp φ ⊂ {ζ < a}` (so `κφ = 0`) the weak equation `E(v,φ)+λ⟨v,φ⟩ = ⟨g,φ⟩` passes to the limit since `E(w,φ) = ⟨w, Aφ⟩` for `φ ∈ D` (continuity in `L²`).
   `v^D_a` increases in `a`; let `v_∞` be the `L²` limit; `v_∞ ∈ Q`, `E(v_∞,φ)+λ⟨v_∞,φ⟩=⟨g,φ⟩` for all `φ ∈ 𝒟`, hence for all `φ ∈ Q` (density of `D` in `Q` for the energy norm, `E_lim`),
   hence `v_∞ = R_λ g = u` by `eq_resolvent_of_weak`. (No Liouville theorem: it is built into `Q = closure of C_c^∞`; Gaffney is only used for conservativity.)
   Pointwise: `w_{a,K} := u - v_{a,K} ≥ 0` is smooth with `L w = λ w` on `{ζ < a}`; the interior sup estimate on `W₀ = {ζ < ζ(x)+1}` gives
   `w(x) ≤ C(x,W₀) ‖w‖_{L²(W₀)} ≤ C(x,W₀) ‖u - v^D_a‖_{L²(μ)} → 0` (a → ∞), UNIFORMLY in `K`. Given `η`: choose `a`, then `ε = η/4`, then `K ≥ K₀(a,ε)`: `f(x) ≥ u(x) - η`.

### 2.3 The bridge (BRIDGE workstream; independent of `K`'s construction)
```
(hP : IsDiffusionSemigroup F V Pt) (hK : IsDiffusionSemigroup F V Kk) (hmin : MinimalResolvent F V Kk) ⊢ ∀ t x, Pt t x = Kk t x
```
1. `d_x(g) := U^P_λ g(x) - U^K_λ g(x) ≥ 0` for `g ∈ 𝒟`, `g ≥ 0` (2.1 + MinimalResolvent).
2. **Mass trick**: `g_n ∈ 𝒟`, `0 ≤ g_n ≤ 1`, `g_n → 1` pointwise (Gaffney cutoffs `weightedCutoffs_of_complete`), `g_n = 1` on `supp g`. `g_n - g ≥ 0` in `𝒟`, so `d_x(g) ≤ d_x(g_n) ≤ λ^{-1} - U^K_λ g_n(x) → 0` (`P` Markov gives `U^P_λ g_n ≤ λ^{-1}`; `K` Markov plus dominated convergence give `U^K_λ g_n(x) → λ^{-1}`). So `d_x(g) = 0`: **`U^P_λ g(x) = U^K_λ g(x)` for all `λ>0`, `g ∈ 𝒟`, `x`.**
3. Laplace uniqueness for continuous bounded `s ↦ P_s g(x) - K_s g(x)` (substitute `y = e^{-s}`, `∫_0^1 y^{n-1} h(y) dy = 0 ∀ n ≥ 1`, Weierstrass `⇒ ∫h² = 0`; not in Mathlib, ~200 lines) gives `P_s g(x) = K_s g(x)` for all `s`.
4. Two finite Borel measures on a second countable locally compact space agreeing on `𝒟` are equal (last step of the existing B2: density of `𝒟` in `C_c` via `Continuous.exists_contMDiff_approx`).

What is NOT used: any property of `Pt` beyond Markov + Dynkin on `𝒟`; any regularity of `Pt`; `Pt(x,·) ≪ μ`; Feller; tightness; gradient/Laplacian bounds of anything.

### 2.4 Checking the classical statement carefully (as requested)
* "Markov solution of the forward equation + conservative minimal solution ⇒ equal" is true here. The only delicate point of the textbook proof (`P ≥ K`) is replaced as follows:
  textbook = Dirichlet resolvents on domains `Ω_n` with boundary, extension by zero is a subsolution with a positive singular boundary measure, which one must pair with `P_s(x,·)` that is
  not known to be absolutely continuous (it may charge `∂Ω_n`); that needs boundary regularity (continuity of `G^Ω g` up to `∂Ω`) to cut at a level `ε`. Penalization + barrier removes
  both issues: `θ_ε(v)` is globally smooth with compact support and satisfies the differential inequality pointwise, so `U^P_λ` is applied to a legitimate test function.
* Resolvent level (time-independent test functions) is essential: it avoids time-dependent test functions `K^n_{t-s} g` (which would need Lipschitz-in-time control and `DynkinBounded`-type bookkeeping).
* Without finiteness of `μ` the Friedrichs resolvent could differ from the minimal one only through conservativity; here `μ(M) < ∞` + Gaffney gives `R_λ 1 = λ^{-1}`, used exactly once (mass trick).
* Counter-check of consistency: if `K` were explosive, step 2 would give `U^P ≥ U^K` and `d_x(1) > 0` (re-entry); the proof correctly breaks only at the mass trick.

### 2.5 Other things I examined (and why they are not recommended)
* **(a.e. identification, geometry-free)**: `σ_ψ := ∫ψ(x)U^P_λ(x,·)μ(dx)` and `r_ψ := R_λ ψ·μ` satisfy `(λ-𝓛)*(σ_ψ - r_ψ) = 0`, `σ_ψ - r_ψ ≥ -λ^{-1}‖ψ‖_∞ μ`, mass `0`; hypoellipticity for measures
  makes the density `h` smooth; `h⁻` is BOUNDED, a subsolution, so Gaffney+Kato give `h⁻ = 0`, hence `σ_ψ = r_ψ` (this also proves invariance of `μ`). It gives `U^P_λ = U^K_λ` for `μ`-a.e. `x` only; passing to every
  `x` would need `P_s(x,·) ≪ μ` for all `s` (parabolic hypoellipticity of measure solutions; the resolvent version gives only a.e. `s`, mixtures of singular measures can be a.c.). Needs negative-order regularity, which REGn does not
  provide. Strictly worse than route (3); keep only as a fallback for invariance.
* **(1) cutoffs `χ = θ(1-w)` from λ-harmonic functions on exhausting domains**: the one-sided second-order bound is FREE (`L θ(v) ≥ θ'(v) L v`), but `OneSidedCutoffs` also needs `|∇χ_n| ≤ C` UNIFORMLY in `n`. For the penalized/Dirichlet solutions the
  gradient in the boundary layer is of order `√K`, and Bakry-Emery is destroyed by `∇κ`; the uniform gradient bound is the exact obstacle. Route (3) uses the same `θ(v)` but never needs `∇`: it feeds the pointwise inequality directly to the resolvent.
  Boundary regularity is avoided by penalization (no exhaustion by domains) and the smooth proper `ζ` (from `exists_smooth_lip_approx`).
* **(2) Lyapunov function (Bakry-Barthe-Cattiaux-Guillin)**: needs `W` smooth, proper, `𝓛W ≤ C(1+W)` one-sided, `Γ W ≤ C(1+W)²` (then `χ_n = θ(W/n)` gives `OneSidedCutoffs`). The BBCG `W = ∫_0^∞ e^{θ t}K^{B}_t 1 dt` (hitting times) is not proper in the entrance-from-infinity case
  (`V = x⁴+x²`: `E_xτ_B` bounded in `x`), smoothness and the one-sided bound need Harnack-type local estimates, and the construction is at least as long as route (3). Dead.
* **(4) classical geometric route**, honest re-estimate: geodesics + second variation barrier + Laplacian comparison + smoothing with a uniform partition of unity: 28-40k lines, success about 30%. Not needed any more. If everything above fails,
  the fallback is the owner's strengthening S1/S1' of DIFFUSION_PLAN §6 (Dynkin for `BddSmooth`, or hypothesis `OneSidedCutoffs`).

---------------------------------------------------------------------------------------------------

## 3. What is used from Tier A (exact list)

Everything is with standing hypotheses of §1 (`[IsProbabilityMeasure μ]`, complete connected, `hV`, `hμ`, `hρ`, `hCD` not needed here).

(A-1) *Friedrichs resolvent, positivity, conservativity* (ALREADY PROVED, `DiffInstance`, `DiffMarkov*`, `DiffFrResolvent`):
`diff_resolvent_nonneg : 0 < lam → 0 ≤ᵐ g → 0 ≤ᵐ resolvent lam g`; `diff_resolvent_one : resolvent lam (oneL2 μ) = lam⁻¹ • oneL2 μ`; `diff_oneL2_mem_Q`, `E_one_left : T.E 1 φ = 0`;
`eq_resolvent_of_weak : u ∈ Q → (∀ φ ∈ Q, E u φ + lam ⟪u,φ⟫ = ⟪g,φ⟫) → u = resolvent lam g`; `DirFriedrichs.closed_of_bounded`; `E_lim`; `DirResolvent.weak`.

(A-2) *Interior regularity with a potential and quantitative sup bound on the manifold* (REG-manifold, planned in A5(ii); small generalization of what DIR delivered):
```lean
theorem Q_smooth_of_weak_eq_pot (REG) (κ : M → ℝ) (hκ : MSmooth F κ) (g : M → ℝ) (hg : MSmooth F g) {lam : ℝ} {u : H} (hu : u ∈ T.Q)
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * ⟪u,φ⟫ + ⟪κ • u, φ⟫ = ⟪(g : H), φ⟫) :
    ∃ ū, MSmooth F ū ∧ u =ᵐ[μ] ū          -- and then pointwise  L ū = (lam + κ) ū - g
theorem interior_sup_estimate_manifold {W : Set M} (hW : IsOpen W) {B : Set M} (hB : IsCompact B) (hBW : B ⊆ W) {lam : ℝ} :
    ∃ C, ∀ w : M → ℝ, MSmooth F w → (∀ y ∈ W, mgenerator F V w y = lam * w y) → ∀ x ∈ B, |w x| ≤ C * (∫ y in W, w y ^ 2 ∂μ) ^ (1/2 : ℝ)
```
(The second is the manifold transfer of REGn's `interior_sup_estimate`; Tier A needs the same statement for the kernel `Kk`, so it is not an extra cost.)

(A-3) *Pointwise kernel* (A6): `Kk` Markov, `IsDiffusionSemigroup F V Kk`, and the identification field to be added to `CanonicalDiffusion` (cheap in A6: `K_s g = T_s g` a.e. and continuity in `x`, full support of `μ`):
```lean
resolvent_repr : ∀ (lam : ℝ), 0 < lam → ∀ g, MSmooth F g → HasCompactSupport g → ∃ ū, MSmooth F ū ∧ ((diffFR F hV hμ).resolvent lam (toL2 g) : M → ℝ) =ᵐ[μ] ū ∧
    ∀ x, ū x = ∫ s in Set.Ioi (0:ℝ), Real.exp (-lam * s) * semi Kk s.toNNReal g x
```
Nothing else from Tier A (in particular NOT: Bakry-Emery, smoothing bounds, contraction) is used by the bridge.

(A-4) Project facts: `weightedIBP_of_isWeightedVolume`, `weightedCutoffs_of_complete`, `exists_smooth_lip_approx`, `properSpace_of_complete_riemannian`, `mgrad_comp_real`, `carre_comp_self`, `mgenerator_add/const_mul/mul`, `dynkin_lipschitz`, `continuous_dynkin`, `testSub`, `normalContraction_stable`.
New small lemma to write: `mgenerator_comp_real θ f x : L (θ∘f) x = θ'(f x) L f x + θ''(f x) Γ f f x` (same proof pattern as `mlaplacian_mul`, ~150 lines).

---------------------------------------------------------------------------------------------------

## 4. Lemma list (Lean-style) and sizes

Namespace `CutoffRigidity.Riemann.Diff`. File prefixes: `DiffPenal*` (P1,P2), `DiffPerron*` (P3-P5), `DiffBridge*`.

### P1 `DiffPenal.lean` (0.8-1.0k lines): penalized resolvent from `R_{λ+K}`
```lean
def PotOK (κ : M → ℝ) (B : ℝ) : Prop := MSmooth F κ ∧ ∀ x, 0 ≤ κ x ∧ κ x ≤ B
noncomputable def mulL2 (κ) (hκ : PotOK κ B) : H →L[ℝ] H     -- bounded multiplier (template: liftLp in DiffMarkov1, or Lp.smul by an L∞ class)
theorem penalized_exists (hlam : 0 < lam) (hκ : PotOK κ B) (g : H) : ∃ v : H, v ∈ T.Q ∧ ∀ φ ∈ T.Q, T.E v φ + lam * ⟪v,φ⟫ + ⟪mulL2 κ v, φ⟫ = ⟪g,φ⟫
theorem penalized_unique ...                                 -- coercivity: E v v + lam‖v‖² ≤ 0 ⇒ v = 0
theorem penalized_nonneg : 0 ≤ᵐ g → 0 ≤ᵐ v                     -- Neumann series, positivity of R_{lam+B}
theorem penalized_anti : κ ≤ κ' → 0 ≤ᵐ g → v^{κ'} ≤ᵐ v^{κ}
theorem penalized_le_resolvent : 0 ≤ᵐ g → v^κ ≤ᵐ resolvent lam g
theorem penalized_le_const : g ≤ᵐ c → v^κ ≤ᵐ c / lam          -- compare with constants (uses E_one_left)
theorem penalized_energy : T.E v v + lam * ‖v‖^2 ≤ ⟪g, v⟫
theorem penalized_smooth (REG-pot) (hg : MSmooth g) : ∃ v', MSmooth v' ∧ v =ᵐ v' ∧ ∀ x, L v' x = (lam + κ x) * v' x - g x
```
Risk low-medium (Lean friction in `Lp` multipliers).

### P2 `DiffPerron1.lean` (1.0-1.4k): proper function, chain rule, energy maximum principle, barrier
```lean
theorem mgenerator_comp_real ...                                              -- see §3
theorem exists_smooth_proper : ∃ ζ, MSmooth F ζ ∧ (∀ x, 0 ≤ ζ x) ∧ ∀ c, IsCompact {x | ζ x ≤ c}
theorem energy_max_principle {w : M → ℝ} (hw : MSmooth F w) (hb : ∃ C, ∀ x, |w x| ≤ C) {lam : ℝ} (hlam : 0 < lam)
    {κ : M → ℝ} (hκ : ∀ x, 0 ≤ κ x) (h : ∀ x, 0 < w x → (lam + κ x) * w x ≤ mgenerator F V w x) : ∀ x, w x ≤ 0
theorem barrier_decay (ζ proper) (g smooth, compact support, g ≥ 0) (hlam) (a) (hga : ∀ x, g x ≠ 0 → ζ x < a) (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀, ∀ K ≥ K₀, ∀ v : M → ℝ, MSmooth F v → (∀ x, 0 ≤ v x ∧ v x ≤ ‖g‖_∞/lam) →
      (∀ x, mgenerator F V v x = (lam + K * θ₀ (ζ x - a)) * v x - g x) → ∀ x, a + 2 ≤ ζ x → v x ≤ ε
```
Risk medium (the barrier algebra with explicit constants; the energy argument needs smooth `G` with `G²/G' ≤ C`; both are routine).

### P3 `DiffPerron2.lean` (0.5k): the compactly supported subsolution
```lean
theorem subsolution_of_penalized {v g} (hv : MSmooth v) (h0 : ∀ x, 0 ≤ v x) (hg : ∀ x, 0 ≤ g x) {κ} (hκ : ∀ x, 0 ≤ κ x)
    (hv' : ∀ x, L v x = (lam + κ x) * v x - g x) (ε) (hε : 0 < ε) (hsupp : ∀ x, ε ≤ v x → x ∈ K₀) (hK₀ : IsCompact K₀) :
    ∃ f ∈ testSub F M, (∀ y, lam * f y - L f y ≤ g y) ∧ (∀ y, v y - 2 * ε ≤ f y)
```
Risk low (convexity computation with `mgenerator_comp_real`).

### P4 `DiffPerron3.lean` (1.2-1.6k): convergence `v_{a,K}(x) → u(x)` and the Perron property
```lean
theorem penalized_limit_K : (v_{a,K})_K decreasing, L²-limit v_a^D ∈ T.Q, E v_a^D ≤ C₀, weak equation on D-functions supported in {ζ<a}
theorem penalized_limit_a : v_a^D increasing in a with L²-limit = resolvent lam g          -- closed_of_bounded + E_lim + eq_resolvent_of_weak
theorem minimalResolvent_of_canonical (hK : CanonicalDiffusion' Kk) : MinimalResolvent F V Kk
```
where (to be placed in `DiffAPI`)
```lean
def MinimalResolvent (V) (Kk : ℝ≥0 → Kernel M M) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ g : M → ℝ, MSmooth F g → HasCompactSupport g → (∀ x, 0 ≤ g x) → ∀ (x : M) (η : ℝ), 0 < η →
    ∃ f : M → ℝ, MSmooth F f ∧ HasCompactSupport f ∧ (∀ y, lam * f y - mgenerator F V f y ≤ g y) ∧
      (∫ s in Set.Ioi (0:ℝ), Real.exp (-lam * s) * semi Kk s.toNNReal g x) - η ≤ f x
```
Risk medium (uniform-in-`K` sup bound via `interior_sup_estimate_manifold`; order of limits).

### BRIDGE `DiffBridge.lean`, `DiffBridge1.lean` (1.4-1.8k)
```lean
def resolventU (P) (lam) (g : M → ℝ) (x : M) : ℝ := ∫ s in Set.Ioi (0:ℝ), Real.exp (-lam * s) * semi P s.toNNReal g x
theorem resolventU_dynkin (hP : IsDiffusionSemigroup F V P) (hlam : 0 < lam) {f} (hf : MSmooth F f) (hc : HasCompactSupport f) (x) :
    resolventU P lam (fun y => lam * f y - mgenerator F V f y) x = f x
theorem resolventU_mono (hP) {g h} (hg hh : smooth, compact support) (hgh : g ≤ h) : resolventU P lam g x ≤ resolventU P lam h x
theorem resolventU_ge (hP) (hmin : MinimalResolvent F V Kk) : 0 ≤ g → resolventU Kk lam g x ≤ resolventU P lam g x
theorem resolventU_eq (hP hK hmin) : resolventU P lam g x = resolventU Kk lam g x            -- mass trick
theorem laplace_unique {φ : ℝ → ℝ} (hc : ContinuousOn φ (Ici 0)) (hb : bounded) (h : ∀ n : ℕ, 0 < n → ∫ s in Ioi 0, exp (-n * s) * φ s = 0) : ∀ s ≥ 0, φ s = 0
theorem bridge_of_minimal (hP hK hmin) : ∀ t x, Pt t x = Kk t x                              -- final step reuses DiffIdentify's measure-equality lemma
```
Risk low-medium.

### Totals
| piece | lines | risk |
|---|---|---|
| P1 penalized resolvent | 0.8-1.0k | low-med |
| REG-pot + manifold sup estimate (inside REG, small extra) | 0.6-1.2k | med (depends on REG progress) |
| P2 barrier + energy MP + chain rule | 1.0-1.4k | med |
| P3 subsolution | 0.5k | low |
| P4 limits + Perron | 1.2-1.6k | med |
| BRIDGE | 1.4-1.8k | low-med |
| **Total** | **5.5-7.5k (about 9k pessimistic)** | success about 75% |

Things that could go wrong (honest list): (U1) `interior_sup_estimate_manifold` uniform in the solution (should follow from REGn `interior_sup_estimate` plus a finite chart cover; if REG-manifold only delivers qualitative smoothness, P4
needs a Dini-type argument; ask the REG agent for the quantitative version, it is needed for the kernel anyway). (U2) Variable potential in REGn: not an issue for `chart_weak_equation` (RHS arbitrary), the induction is `locSob_step`.
(U3) Lean multiplier operator on `Lp`. (U4) Order of limits in P4 (monotone in `K` and in `a`, but not jointly): handled by `v_{a,K} ≥ v^D_a` plus a uniform-in-`K` local bound.

---------------------------------------------------------------------------------------------------

## 5. Recommended route and launch order

**Recommended: route (3) as above (penalized Perron subsolutions + resolvent-level mass trick).** Replace in DIFFUSION_PLAN: B1/B2/CO by BRIDGE + PERRON; final theorem = C4 + A + `bridge_of_minimal` + `minimalResolvent_of_canonical`.
Order: BRIDGE and P1/P2/P3 start NOW (they only need the existing DiffInstance/DiffMarkov API and the interface `MinimalResolvent`); P4 and REG-pot after P1-P3 and the quantitative manifold regularity.
Only dependencies on unfinished Tier A: (A-2) and (A-3) of §3.

### Brief WS-BRIDGE
Goal: `bridge_of_minimal` (statement in §4) in `DiffBridge.lean`, `DiffBridge1.lean`; define `MinimalResolvent`, `resolventU`, in `DiffAPI`-style (new file `DiffPerronAPI.lean`, `public import DiffAPI`). Standing hypotheses as §1 plus
`[IsFiniteMeasure μ]`-free: only completeness for `weightedCutoffs_of_complete`. Prove `resolventU_dynkin` (Fubini on `Ioi 0`, use `dynkin_lipschitz`/`continuous_dynkin` for integrability), monotonicity, the mass trick (dominated convergence for `semi Kk s g_n x → 1`),
`laplace_unique` (Weierstrass: Mathlib `polynomialFunctions` dense, `y = e^{-s}`), conclude measures equal by reusing the last step of `DiffIdentify.lean` (find the lemma there; do not duplicate). No `sorry`. Report `riemann-status/diff-BRIDGE.md`.

### Brief WS-PENAL (P1 + P2 + P3)
Goal: `DiffPenal.lean`, `DiffPerron1.lean`, `DiffPerron2.lean` with the statements of §4 (P1-P3). Use `diffFR`, `diff_resolvent_nonneg`, `diff_resolvent_one`, `eq_resolvent_of_weak`, `E_one_left`, `weightedCutoffs_of_complete`, `weightedIBP_of_isWeightedVolume`, `exists_smooth_lip_approx`.
`penalized_smooth` may take the REG-with-potential statement `Q_smooth_of_weak_eq_pot` of §3 as an explicit hypothesis structure (`structure RegPot : Prop`) until REG delivers it. Barrier: follow §2.2 steps 5-6 literally, constants explicit.
Forbidden: assuming the barrier decay or the subsolution property as hypotheses; weakening `v ≤ ε` to a.e. Report `riemann-status/diff-PENAL.md`.

### Brief WS-PERRON (P4), starts when PENAL's statements compile
Goal: `penalized_limit_K`, `penalized_limit_a`, `minimalResolvent_of_canonical` in `DiffPerron3.lean` following §2.2 step 7 (use `DirFriedrichs.closed_of_bounded`, `E_lim`, `eq_resolvent_of_weak`, `interior_sup_estimate_manifold`).
The hypothesis `CanonicalDiffusion'` is `CanonicalDiffusion` plus the field `resolvent_repr` of §3 (A-3); until A6 provides it, take `resolvent_repr` as a hypothesis structure. Report `riemann-status/diff-PERRON.md`.

### Message to REG-manifold / KER owners
(i) state the manifold regularity with a smooth potential `κ` (`Q_smooth_of_weak_eq_pot`) and the quantitative `interior_sup_estimate_manifold` of §3 (A-2);
(ii) add `resolvent_repr` to `CanonicalDiffusion` and prove it in A6. Everything else of Tier A is unchanged. The `smoothing` field of `CanonicalDiffusion` is no longer needed by the bridge.
