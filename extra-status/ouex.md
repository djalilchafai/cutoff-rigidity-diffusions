# ouex: OU / convex-interaction / mixing-time extras (scan items A7-A11)

Status: all five items DONE, no sorry, axioms only propext, Classical.choice, Quot.sound
(checked with `#print axioms`). All modules build (`lake build CutoffRigidity.Extra.<M>`). No existing
file edited. Modules NOT yet added to `CutoffRigidity.lean` (lead to do). Every theorem is in namespace
`CutoffRigidity.Paper`, statement uses only `CutCur.*` names plus Mathlib.

| item | file (module CutoffRigidity.Extra.*) | theorem | lines |
|---|---|---|---|
| (d) A10 | PairwiseInteraction | `pairwise_interaction` | 55 |
| (a) A9 | OUEigen | `ou_first_eigenspace` (also public helpers `gradient_ou`, `coord_eq`) | 126 |
| (e) A11 | MixingTime | `mixing_time_rigid` | 183 |
| (b) A7 | OUMeanStart | `ou_mean_start_cutoff` (helpers `ou_gap_rigid`, `ou_mean_zero`, `ou_squaredWasserstein_zero`, `ouMeanW*`) | 352 |
| (c) A8 | OUInfty | `ou_lp_infty_fails` (helper `ou_relLp_top_ge`, Gaussian mgf lemmas) | 274 |

## Important correction to scan A8
The scan says the L^infty norm is +infinity for all t>0 because "the density ratio is unbounded". That is
FALSE: for the OU process from a fixed x0 the law has smaller variance than mu, so the density ratio
d mu_t / d mu is bounded, with sup = (1-q)^{-d/2} exp(rho |x0|^2 / 2), q = e^{-2 rho t}, attained at
x = e^{rho t} x0 (independent of t up to the factor (1-q)^{-d/2}). In particular from the mean (x0 = 0) the
L^infty distance is finite. The manuscript claim "p = infinity fails already for OU" is TRUE for the balls
B(m, c sqrt d), c>0, for a different reason: the worst case over |x0| = c sqrt d has L^infty distance at least
exp(rho c^2 d / 2) - 1 -> infinity at EVERY time. Proved quantitatively: for all x0, t,
`exp(rho |x0|^2/2) - 1 <= relLp(law X_t^{x0}, mu, infinity)` (`ou_relLp_top_ge`), via an exponential-moment test
(if dnu/dmu <= K then E_nu e^{<u,y>} <= K E_mu e^{<u,y>}, choose u = m/q).

## Proposed Challenge text (unqualified names; Paper versions use `CutCur.` prefixes)

### (d) A10, manuscript L289-293
```lean
/-- **Pairwise interaction example** (introduction, after (1.5)): for `h` convex, the potential
`W(x) = ∑_{i<j} h(xᵢ - xⱼ)` is convex and invariant under translations along `(1,…,1)`
(and `C²` if `h` is `C²`, as needed in Theorem 1.5). Evenness of `h` (printed in the manuscript) is not needed. -/
theorem pairwise_interaction {d : ℕ} {h : ℝ → ℝ} (hh : ConvexOn ℝ Set.univ h) :
    let W := fun x : Rd d => ∑ i, ∑ j with i < j, h (x i - x j)
    ConvexOn ℝ Set.univ W ∧ (∀ x (s : ℝ), W (x + s • diagonal d) = W x) ∧
      (ContDiff ℝ 2 h → ContDiff ℝ 2 W) := by
  sorry
```
Note: the manuscript says "convex even h"; the statement drops "even" (stronger, true). No amendment otherwise.

### (a) A9, manuscript L278
```lean
/-- **First eigenspace of the Ornstein–Uhlenbeck process** (introduction, after (1.4)): for
`V(x) = ρ|x|²/2 + c` (the constant `c` normalizing `e^{-V}` to a probability measure) in
dimension `d ≥ 1`, `λ₁ = ρ`, `k₁ = d`, and the functions `fᵢ(x) = √ρ xᵢ`, `i = 1,…,d`, are
eigenfunctions forming an orthonormal family in `L²(μ)` (hence an orthonormal basis of `E₁`). -/
theorem ou_first_eigenspace {d : ℕ} (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {c : ℝ}
    (hp : IsProbabilityMeasure (gibbs fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c)) :
    let V := fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c
    spectralGap V = ρ ∧ firstEigenDim V = d ∧
      (∀ i : Fin d, IsEigenfunction V ρ (fun x => Real.sqrt ρ * x i)) ∧
      ∀ i j : Fin d, ∫ x, (Real.sqrt ρ * x i) * (Real.sqrt ρ * x j) ∂gibbs V =
        if i = j then 1 else 0 := by
  sorry
```
Notes: `hd : 0 < d` is NECESSARY (d = 0: `spectralGap = sInf ∅ = 0`); the manuscript implicitly has d >= 1. The constant `c` is
the normalization (manuscript writes V = rho|x|^2/2 and tacitly normalizes). Because `IsEigenbasis` is indexed by
`Fin (firstEigenDim V)` the statement is phrased with the family indexed by `Fin d` (equal types only after `k₁ = d`).
Proof: Thm 1.5 with W = const gives gap and rigid curvature; Remark 1.2 (`firstEigenDim_le`) gives `k₁ <= d`; d orthonormal
elements of E_1 give `k₁ >= d`.

### (e) A11, manuscript L349, L387-393
```lean
/-- **Mixing time of rigid sequences** (introduction, after Corollary 1.6, and the "Product condition"
subsection): under the hypotheses of Corollary 1.4 and for every `η ∈ (0,1)`, the total variation mixing time
`t₀⁽ⁿ⁾` from the balls `B(m, c√n)` is finite for large `n` and is `(log n/(2λ₁))(1+o(1))`; moreover
`λ₁⁽ⁿ⁾ t₀⁽ⁿ⁾ → ∞` (so the product condition of Theorem 1.7 holds) and `t₀⁽ⁿ⁾ → ∞`. -/
theorem mixing_time_rigid {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)} {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (h : IsRigidSequence V B P X)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTime (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop := by
  sorry
```
Notes: only TV mixing time is formalized (the Challenge `mixingTime` is TV-only); the manuscript's sentence
also says W2 and entropy mixing times equal log d/(2 lambda_1): those would need new mixing-time defs (not done; they
follow from the corresponding cutoffs in the same way, but need monotonicity of the W2/H profiles, which the project
has only for TV). Proof: Cor 1.4 TV cutoff (`information_cutoff`) + antitone TV profile (`curvedTVProfile_antitone`,
`curvedTVProfile_le_after_mixing`); no new assumption.

### (b) A7, manuscript L197-202
```lean
/-- **OU started from the mean** (after Corollary 1.3): for `V⁽ⁿ⁾(x) = ρ|x|²/2 + c⁽ⁿ⁾` with `ρ > 0` independent of
`n` (so `λ₁⁽ⁿ⁾ = ρ`) and the single initial condition `S⁽ⁿ⁾ = {m⁽ⁿ⁾}`, `m⁽ⁿ⁾` the mean of `μ⁽ⁿ⁾`, the Wasserstein
distance has a cutoff at `log n/(4λ₁)`, and there is no cutoff at the critical time `log n/(2λ₁)` of
Corollary 1.3 (so `c > 0` is essential there). -/
theorem ou_mean_start_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {ρ : ℝ} (hρ : 0 < ρ)
    {c : ℕ → ℝ} {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (hL : ∀ n, 0 < n → IsLangevin (fun x : Rd n => ρ / 2 * ‖x‖ ^ 2 + c n) (B n) (P n) (X n)) :
    let V := fun n (x : Rd n) => ρ / 2 * ‖x‖ ^ 2 + c n
    let prof := fun n => worst (P n) (X n) {∫ x, x ∂gibbs (V n)} (wasserstein2 · (gibbs (V n)))
    HasCutoff prof (fun n => Real.log n / (4 * spectralGap (V n))) ⊤ 0 ∧
      ¬ HasCutoff prof (fun n => criticalTime n (spectralGap (V n))) ⊤ 0 := by
  sorry
```
Notes: the manuscript says "a cutoff" without naming the distance; it attributes it to "the second part of the
left-hand side of (eq:maineucl)", i.e. the Wasserstein lower bound, so only W2 is formalized (the TV/KL/Fisher
profiles from the mean for OU would also cut off at log d/(4 rho) but are not proved). The second conjunct
(`¬ HasCutoff` at `log n/(2λ₁)`) is the formalization of "c > 0 is essential" and is an addition to the literal text
(it is true and follows from the same computation). Exact formula proved: W2^2 from the mean =
`n (1-√(1-e^{-2ρt}))²/ρ` (`ou_squaredWasserstein_zero`), by dilation of the Mehler Gaussian law and Lipschitz push-forward both ways.

### (c) A8, manuscript L407
```lean
/-- **`p = ∞` fails for the Ornstein–Uhlenbeck process** (after (1.25)): for `V⁽ⁿ⁾(x) = ρ|x|²/2 + c⁽ⁿ⁾` with
`ρ > 0` and the balls `B(m, c√n)`, `c > 0`, the worst-case `L^∞(μ)` distance `‖dμ_t/dμ - 1‖_{L^∞(μ)}`
tends to `+∞` along every sequence of times (in particular after the critical time), so the analogue of (1.25)
with `p = ∞` (limit `0` at `(1+ε)t_*`) fails. -/
theorem ou_lp_infty_fails {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {ρ : ℝ} (hρ : 0 < ρ)
    {c' : ℕ → ℝ} {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (hL : ∀ n, 0 < n → IsLangevin (fun x : Rd n => ρ / 2 * ‖x‖ ^ 2 + c' n) (B n) (P n) (X n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : Rd n) => ρ / 2 * ‖x‖ ^ 2 + c' n
    let prof := fun n => worst (P n) (X n) (meanBall (V n) c) (relLp · (gibbs (V n)) ⊤)
    (∀ t : ℕ → ℝ, Tendsto (fun n => prof n (t n)) atTop (𝓝 ⊤)) ∧
      ¬ HasCutoff prof (fun n => criticalTime n (spectralGap (V n))) ⊤ 0 := by
  sorry
```
Notes: uses the project `relLp` with `p = ⊤` (`eLpNorm` = essential sup of `|dν/dμ - 1|`), no new definition.
The failure is for c > 0 (balls); from the mean itself L^infty does not fail (see the correction above), so
the manuscript sentence is true only with the initial set B(m, c sqrt d), which is the setting of (1.25). The auxiliary
`ou_relLp_top_ge` (exp(ρ|x0|²/2) - 1 <= L^∞ distance) could be added too if the lead wants the quantitative form.

## Housekeeping
* New modules to add to `CutoffRigidity.lean`: `CutoffRigidity.Extra.PairwiseInteraction`, `.OUEigen`, `.MixingTime`,
  `.OUMeanStart`, `.OUInfty` (OUInfty imports OUMeanStart imports OUEigen).
* Wiring in Challenge/Solution: each Paper theorem should be the proof of the Challenge theorem (statements identical modulo `CutCur.`).
* Upstream edits: none (I wanted `ouDecay` unfolded; avoided via `ouDecay_sq`).
* Not claimed: human review; the lead should recheck statements against the manuscript.
