# WS-ID (Tier B): Dynkin on bounded smooth functions and the bridge `Pt = Kk`

Status: DONE, fully checked. `lake build CutoffRigidity.Riemann.DiffIdentify` succeeds; no sorry; axioms of the two
main theorems: propext, Classical.choice, Quot.sound. Files (namespace `CutoffRigidity.Riemann.Diff`):
`CutoffRigidity/Riemann/DiffDynkinBounded.lean` (492 lines), `CutoffRigidity/Riemann/DiffIdentify.lean` (378 lines).
No edits to DiffAPI, DiffusionRegular, Challenge, Statements, Solution, CutoffRigidity.lean.

## DiffDynkinBounded.lean
* Definitions: `BddSmooth F V f`, `DynkinBounded F V Pt`, `OneSidedCutoffs F V` (exactly as in plan 2.3).
* New calculus (absent from the project): `mlaplacian_mul`, `mgenerator_mul` (Leibniz: `𝓛(χf) = χ𝓛f + f𝓛χ + 2Γ(χ,f)`),
  `mlaplacian_const`, `mgenerator_const`, `mgrad_add_const`, `mgenerator_add_const`,
  `mgrad_mgenerator_eq_zero_of_eventually_one`, `BddSmooth.affine`, `BddSmooth.generator_affine`.
* `measurable_semi_time_of_cutoffs`: `s ↦ ∫ h dPt s.toNNReal x` is measurable for smooth bounded `h` (via cutoffs and continuity for
  `C_c^∞`). Stated for smooth bounded `h` and a cutoff sequence (not "Borel `g`" as in the brief; Borel is not needed).
* `dynkin_ge_of_nonneg` (step 1: `f x + ∫_0^t P_s(𝓛f) ≤ P_t f` for `f ≥ 0` in `BddSmooth`, using smooth surrogates
  `θ_ε(u) = (√(u²+ε²)-u)/2 ≥ u⁻` and `√(Γχ+ε²) ≥ |∇χ|` with `ε = 1/(n+1)` so that the error terms are smooth, hence time-measurable).
* `dynkin_ge_affine`, **`dynkinBounded_of_oneSidedCutoffs (hP) (hV : MSmooth F V) (hc : OneSidedCutoffs F V) : DynkinBounded F V Pt`**
  (mass trick with `f + C₀`, `C₀ - f`). Extra hypothesis versus the brief: `hV : MSmooth F V` (needed for smoothness of `𝓛f`).

## DiffIdentify.lean
* `eq_of_quadratic_increments`, `measure_eq_of_integral_smooth` (two probability measures agreeing on `C_c^∞` are equal; uses
  `Continuous.exists_contMDiff_approx`, `SigmaCompactSpace`, Gaffney cutoffs `WeightedCutoffs`),
  `measurable_time_of_weightedCutoffs`, `dynkin_increment`, `dynkin_increment_bound`, `semi_time_taylor`, `quad_increment`.
* **`identification [IsRiemannianManifold 𝓘(ℝ,F) M] [ConnectedSpace M] [CompleteSpace M] (hP : IsDiffusionSemigroup F V Pt)
  (hV : MSmooth F V) (hD : DynkinBounded F V Pt) (hK : CanonicalDiffusion F V μ ρ Kk) : ∀ t x, Pt t x = Kk t x`.**
  Needs `[MeasurableSpace M] [BorelSpace M]` (file variables); completeness/connectedness only to get `SigmaCompactSpace` and
  `weightedCutoffs_of_complete` (first-order cutoffs, for measurability in time only).

## Proof of identification (no derivative, no limit of difference quotients)
Fix `g ∈ C_c^∞`, `t`, `x`; `G(a) = ∫ (Kk (t-a) g) dPt a (x,·)`, `a ∈ [0,t]`. For `a ≤ b ≤ t`, `p = t-b`, `q = t-a`, `δ = b-a`:
`G b - G a = [P_b(u_p - u_q) + δ P_b ψ_q] + [(P_b u_q - P_a u_q) - δ P_b ψ_q]`, `u_r = Kk r g`, `ψ_r = Kk r (𝓛g)`. First bracket is `≤ C₃ δ²`
(pointwise Taylor `semi_time_taylor` for `Kk`, `C₃ = sup|𝓛²g|`); second is `≤ C₂ δ²` (`DynkinBounded` on `u_q`, `𝓛u_q = ψ_q`, and
`|P_rψ_q - P_bψ_q| ≤ C₂(b-r)` from `DynkinBounded` on `ψ_q`). So `|G b - G a| ≤ (C₂+C₃)(b-a)²`, hence `G t = G 0`, i.e. `P_t g(x) = Kk_t g(x)`;
then measure equality from `C_c^∞` (approximation + cutoffs). `P_0 = δ` is not needed separately.

## Check of `CanonicalDiffusion` (DiffAPI) -- NO CHANGE NEEDED
The proof uses exactly: `markov`, `dynkin` (for `Kk` on `C_c^∞`, incl. `t = 0` giving `semi Kk 0 g = g`), and `smoothing` applied to `g` and to `𝓛g`:
(i) `semi Kk r g`, `semi Kk r (𝓛g)` smooth, (ii) `𝓛(semi Kk r g) = semi Kk r (𝓛g)`, (iii) uniform bounds of value, gradient, generator in `r`
(the `∃ C` in `smoothing` sits after `∀ t` but only quantifies `∀ s x`, so it is uniform in `s`: I use it at `t = 0`).
`invariant`, `eigen`, `contraction` are not used. Note `smoothing` for `𝓛g` needs `𝓛g` smooth with compact support (proved in DiffusionRegular).
Tier A must prove `smoothing` including the bound of `‖∇ semi Kk s g‖` and `|𝓛 semi Kk s g|` uniformly in `s` (not just a.e.).

## Notes / not done
* Brief's stand-alone `hasDerivAt_semi_pair` was not needed (replaced by the quadratic-increment argument) and is not proved.
* `OneSidedCutoffs F V` itself (CO, geometry) is NOT proved here; `dynkinBounded_of_oneSidedCutoffs` is the bridge, the final assembly
  needs either `OneSidedCutoffs` or the strengthening S1/S1' of plan section 6.
