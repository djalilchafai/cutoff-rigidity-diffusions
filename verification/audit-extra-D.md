# Statement-fidelity audit D (Challenge.lean, 7 statements)

AI audit (LLM agent, adversarial reader), not a human review. Read statements and definitions
(`C:` = Challenge.lean lines, `T:` = cutcur-lean.tex lines). Proofs not used to judge fidelity; I only
looked at `CutoffRigidity/Extra/Dynamics.lean` to see that the `bind` is non-junk (the statement of
`law_bind_eq_comp` shows it), and at `SplitPotential.lean` / `Riemann/WitnessMain.lean` to see how the splitting
statement relates to the Gaussian witness. No file other than this one was written.

## Summary

| Statement | Manuscript | Verdict |
|---|---|---|
| `langevin_moment_bounds` (C:614) | T:~1040-1100, 1111-1131 | faithful with remarks |
| `sup_eigenLambda_ball` (C:631) | T:~953-975, 1000-1010 | faithful with remarks |
| `langevin_w2_contraction` (C:644) | T:943-952 | faithful (slightly more general: `ρ ≥ 0`) |
| `langevin_entropy_decay` (C:658) | T:1133-1195 (expdecH, HWsmallt, HtWX0, HI, fisher_ent_w2) | faithful with remarks (docstring wording) |
| `pinsker_tvDist` (C:682) | eq. CKP | faithful |
| `talagrand_logSobolev` (C:691) | Talagrand paragraph and eq. LSI | faithful with remarks (carrier `hL`) |
| `riemannian_gaussian_splitting` (C:830, strengthened) | Thm 3.6 (T:1333-1362), Lemma 3.7 | faithful; the new conjuncts are correct and consistent with the witness |

No defect found. No junk-value exploit, no vacuity beyond the already-known trivial cases listed below.

## 1. `langevin_moment_bounds`

Hypotheses: `hV2`, `hp`, `RigidCurvature V` (`0 < λ₁` and `Hess V ≥ λ₁`). Conclusions: coordinate variance `≤ 1/λ₁`,
`∫|x-m|² ≤ d/λ₁`, the Steiner identity, `W₂(δ_{x₀}, μ)² = ∫|x-x₀|²dμ`, and `W₂² ≤ (c²+1/λ₁)d` on `B(m, c√d)`.

* No centering needed: correct. The manuscript centers by "WLOG m = 0 by translating V" (T:~1001). Without centering:
  `Var(x_i) ≤ λ₁⁻¹ ∫|∂_i x_i|² = 1/λ₁` is the Poincaré inequality applied to the centered function `x_i - m_i` (variance is
  translation invariant), the sum over `i` gives `∫|x-m|² ≤ d/λ₁`, and the Steiner identity is exact because `∫(x-m)dμ = 0`.
  The statement uses `m = ∫ x dμ` throughout, so it is the translated manuscript statement. Right.
* Junk values. `1/spectralGap V`: `spectralGap V > 0` by `hV.1`, so no division by zero. `variance` (Mathlib, `toReal` of
  `evariance`) would be junk `0` if a coordinate were not `L²`; it is `L²` (strong log-concavity gives Gaussian tails, and Poincaré
  itself gives exponential integrability), so the bound is not a junk-0 triviality. The Bochner mean `m` and the integrals
  `∫|x-x₀|²` are of integrable functions for the same reason, so no integral junk. `wasserstein2` is `(inf over couplings)^{1/2}`
  in `ℝ≥0∞`: the only coupling of `δ_{x₀}` and `μ` is `δ_{x₀} ⊗ μ`, so the infimum equals the `lintegral`, which equals
  `ofReal` of the Bochner integral since the integrand is nonnegative and integrable; `(a^{1/2})^2 = a` holds in `ℝ≥0∞` including `⊤`.
  `ENNReal.ofReal ((c²+1/λ₁) d)`: argument `≥ 0` (c is squared, λ₁>0). No truncation.
* `c`: stated for `0 ≤ c`, the manuscript uses `c > 0`. More general, true (c=0 gives `B = {m}`), harmless.
* The hypothesis `Hess V ≥ λ₁` is not needed for these moment bounds (only `λ₁ > 0` is used) but it is what Corollaries 1.3/1.4 assume,
  and it is how the theorem is used. Harmless extra hypothesis, not a weakening of intent.
* `d = 0`: `spectralGap` is `sInf ∅ = 0` so `hV.1` is false; the statement is vacuously true in `d = 0`. Irrelevant (paper has `d → ∞`).
* `hp`, `hV2` duplicated from `IsLangevin` (no Langevin carrier needed here). Good: no vacuity from Brownian-motion existence.
* Remark: the statement `∀ c ≥ 0, ∀ x₀ ∈ meanBall V c` is the right ball: `meanBall = closedBall m (c√d)` (C:143), matching `B(m, c√d)`.

## 2. `sup_eigenLambda_ball`

Claims `Λ(x₀) ≤ λ₁|x₀-m|²`, `sup_{|x-m|≤R} Λ = λ₁R²`, `sup_{B(m,c√d)} Λ = λ₁c²d`, all in `ℝ≥0∞` via `ofReal`.

* True, and the uncentered form is right. By Theorem 3.1 / Remark 3.2 every `f ∈ E₁` is affine; since `∫ f dμ = 0` (eigenfunction with
  `λ₁ > 0` is orthogonal to constants) the affine part is anchored at the mean: `f(x) = ⟨a, x-m⟩` with `|a|² = λ₁‖f‖²`. For an orthonormal
  basis `(f_i)`, the vectors `a_i` are orthogonal of norm `√λ₁`, so `Λ(x₀) = λ₁|P(x₀-m)|²` with `P` the projection onto their span
  (dimension `k₁ ≥ 1`). Hence `≤ λ₁|x₀-m|²`, and equality is attained on the span, so the sup over a ball of radius `R` is `λ₁R²`
  (needs `k₁ ≥ 1`, which holds, Remark 1.2). This is the manuscript's "centered, `sup_{x∈S}|Ax|² = λ₁R²`" (T:~974), translated by `m`.
* `R = 0` (closedBall `{m}`, value `0 = ofReal 0`) and `c = 0` are fine. `0 ≤ R`, `0 ≤ c` are needed for non-empty balls and are the
  natural ranges (for `R<0` the ball is empty and `⨆ = 0` but `ofReal(gap R²) ≠ 0`, so the hypothesis is not removable; it is present).
* `eigenLambda` is `⨆ over IsEigenbasis` with `Fin (firstEigenDim V)`-indexed families; no `sInf ∅`. Junk: none (all `ofReal` arguments are sums of squares,
  nonnegative; `gap R²` nonnegative since `gap > 0`).
* Same `d = 0` vacuity as above.

## 3. `langevin_w2_contraction`

`W₂(ν₁Pₜ, ν₂Pₜ) ≤ e^{-ρt}W₂(ν₁,ν₂)`, `hρ : 0 ≤ ρ`, `Hess V ≥ ρ I`.

* Manuscript (T:943-952) states it for CD(ρ,∞) with `ρ = λ₁`, all `X₀, Y₀` (so arbitrary initial laws). `0 ≤ ρ` is the natural true range for the
  synchronous-coupling argument (`ρ = 0`: nonexpansive for convex `V`); `ρ < 0` would also hold with a growing factor but is not claimed. Harmless generalization.
* `bind` convention: `ν.bind f = join (map f ν)`; Mathlib's `map` of a non-`AEMeasurable` function is `0`, which would make the law the zero measure
  (junk). Here this does not happen: `Measure.bind` of `x ↦ P.map (X x t)` equals `langevinKernel V B P t ∘ₘ ν` (`law_bind_eq_comp`, stated for
  exactly these hypotheses), a Markov kernel (measurable). So the bind is the law of `X_t` for `X_0 ~ ν` independent of `B`
  (mixture of the laws of the strong solutions; pathwise uniqueness under the monotone drift makes the law version independent). Correct convention.
* `ℝ≥0∞` arithmetic: `ofReal(exp(..)) > 0`, so `ofReal(..) * ⊤ = ⊤` and no `0 * ⊤` appears. `wasserstein2 = ⊤` (infinite second moments) gives a trivially
  true inequality, which is also the true mathematical statement (nothing is lost).
* `hL` is a hypothesis (carrier); see the remark in section 7.

## 4. `langevin_entropy_decay`

Checked each of the 6 conjuncts against the manuscript.

1. `H t ≤ e^{-2ρ(t-s)} H s` for all `s ≤ t` (manuscript: `t ≥ t₀ > 0`, T:1148). Includes `s = 0`. True (Bakry-Émery, valid also from `s = 0`, where `H 0 = H(ν|μ)`
   possibly `⊤`; then `ofReal(·)*⊤ = ⊤`). `X x 0 = x` a.s. since `B 0 = 0` a.s. (projective family at `{0}`), so `H 0 = klDiv ν μ`. Stronger than printed, true.
2. `H t ≤ ρe^{-2ρt}/(1-e^{-2ρt}) W` and `≤ W/(2t)` for `t > 0` (eq. HWsmallt). `ρ > 0` makes `1-e^{-2ρt} > 0` for `t>0`: no division by zero. The second inequality
   is `ρ/(e^{u}-1) ≤ ρ/u` with `u = 2ρt`. True. The footnote "first inequality valid for all ρ ∈ ℝ" is not claimed (`ρ > 0` assumed): harmless omission.
3. For `t ≥ 1`: `2 H t ≤ e^{-2ρ(t-1)} W` (HtWX0) and `TV² ≤ e^{-2ρ(t-1)}W/4`. The statement uses `ofReal(tvDist² )` and CKP `TV² ≤ H/2`. Consistent.
4. `I` nonincreasing, for all `s ≤ t` (manuscript: monotonicity of `I` along the flow). `I 0` may be `⊤`; fine.
5. `I(s+t) ≤ H s / t` for all `s ≥ 0`, `t > 0`. Manuscript has `0 < t₀ < t₁` (eq. HI). With `H s ≥ 0` and de Bruijn it is `I(s+t) ≤ (H s - H(s+t))/t ≤ H s/t`. True also for `s = 0`.
   `ENNReal` division by `ofReal t`, `t > 0`: no junk (finite nonzero divisor).
6. For `1 ≤ t₀ < t₁`: `I t₁ ≤ e^{-2ρ(t₀-1)}/(2(t₁-t₀)) W` (eq. fisher_ent_w2). Manuscript says `t₀ > 1`; `t₀ = 1` also holds because HtWX0 holds at `t = 1`. `t₁ - t₀ > 0`. Fine.

* Positive coefficients throughout, so `W = ⊤` makes the right-hand sides `⊤` (no `0·⊤`), and `W = 0` forces `ν = μ`, then everything is `0`.
* Non-sharp constant remark: I verified on the 1-d OU process (`V = ρx²/2`, `ν = δ_a`, `q = e^{-2ρt}`):
  `H(μ_t|μ) = ½[ρa²q - q - log(1-q)]`, while the printed bound is `q/(1-q)(ρa² + 1)`. The printed constant holds and is not sharp
  (a factor `1/2` is valid since `-log(1-q) ≤ q/(1-q)`), consistent with the manuscript citing BGL Lemma 4.2 without claiming sharpness. The Challenge statement contains
  the printed constant (C:668), not a sharper one. The docstring sentence "stated here as printed; the formalization proves a sharper one" is misleading: it can be read as saying the Lean
  statement is sharper. The statement is exactly the printed one; suggest rewording to "the constant is the printed one, which is not sharp". Documentation-only, severity low.
* `0 < d`: amendment flagged. In `d = 0` everything is trivial (`ν = μ`), so the omission loses nothing.
* `H` is the Mathlib `klDiv ν μ` of probability measures (`⊤` if not `≪` or `llr` not integrable), equal to `∫ h log h dμ`. No junk issue.
* `fisherInfo`: definition audited earlier. The weak-gradient identity is integrated against Lebesgue measure (distributional gradient of `√h`), with `G ∈ L²(μ)`; both sides are
  integrals of `L²_loc` functions times compactly supported smooth `φ` (`e^{-V}` locally bounded below), so no integrability junk.

## 5. `pinsker_tvDist`

`ofReal(tvDist ν μ ²) ≤ klDiv ν μ / 2` for probability measures. `tvDist = sup_A |ν(A)-μ(A)|` (bounded by `1`, nonempty index `A = ∅`: the real `⨆` is the genuine sup). Pinsker's
inequality `TV ≤ √(H/2)` with this normalization (sup over sets, not `½‖·‖₁` doubled) is correct, matches eq. CKP `DTV(μ,ν)² ≤ ½H(ν|μ)`. Order of arguments `klDiv ν μ` = `H(ν|μ)`. Faithful.

## 6. `talagrand_logSobolev`

`ρ W₂(ν,μ)² ≤ 2 H(ν|μ)` and `H(ν|μ) ≤ I(ν|μ)/(2ρ)` for every probability `ν`. Matches the manuscript's Talagrand display and eq. LSI. `ρ > 0`: `ofReal(2ρ) ≠ 0`, so the division is genuine.
`ν` without finite second moment: LHS `= ⊤`, and then `H = ⊤` is required; true by Talagrand (the inequality in `ℝ≥0∞`). `ν` not `≪ μ`: `H = ⊤` and `I = ⊤`. No junk.
`ofReal ρ * W²` with `W²` in `ℝ≥0∞`: fine. `0 < d`: harmless (d = 0 trivial). The Hessian bound and `ρ` are the manuscript's CD(ρ,∞) for `V` on flat space.

## 7. Remark shared by 3, 4, 6: the carrier `hL : IsLangevin V B P X`

The conclusion of `talagrand_logSobolev` does not involve `B, P, X`, but the Lean statement is `∀ Ω B P X, IsLangevin ... → conclusion`. It is equivalent to the
unconditional mathematical statement iff some Langevin carrier exists for each `V` satisfying `C²`, `gibbs V` probability, `Hess V ≥ ρ`. This holds classically (Brownian motion exists; locally Lipschitz monotone drift gives strong solutions, with uniqueness),
but Brownian motion existence is not in Mathlib at the pinned revision (same residual risk (a) as `semantic-audit.md`). So the Lean theorem is not vacuous mathematically but is not unconditionally instantiated inside Lean.
The docstring discloses this. A reader should note `IsLangevin` also silently supplies `ContDiff ℝ 2 V` and `IsProbabilityMeasure (gibbs V)` to all of 3, 4, 6, which are the manuscript's standing assumptions.

## 8. `riemannian_gaussian_splitting` (strengthened)

New conjuncts: `V x = ρ‖(Φ x).1‖²/2 + V'(Φ x).2 + k/2 · log(2π/ρ)` and `ConnectedSpace N ∧ CompleteSpace N`.

* Potential identity versus manuscript (T:1359-1362): `V∘Φ⁻¹(p,y) = ρ|p|²/2 + V'(y) + (k₁/2) log(2π/ρ)`. The Lean form `V x = ... (Φ x)` is the same with `p = (Φ x).1`, `y = (Φ x).2` (Φ bijective). Matches.
* Constant check, independent derivation. `γ_{k,ρ⁻¹}` has density `(ρ/2π)^{k/2} e^{-ρ|p|²/2} = exp(-ρ|p|²/2 - (k/2)log(2π/ρ))`. With `μ' = e^{-V'} vol'` and `μ.map Φ = γ ⊗ μ'`, `Φ` isometric (so volume-preserving) the density
  of `μ∘Φ⁻¹` is `exp(-[ρ|p|²/2 + V'(y) + (k/2)log(2π/ρ)])`, i.e. the identity with the `+` sign and `log(2π/ρ)` (not `ρ/2π`). Correct.
* Witness consistency (read, not re-run). `Riemann/WitnessMain.lean`: `M = ℝ^k`, `V = ρ‖x‖²/2 + (k/2)log(2π/ρ)` (`gaussPot`), `μ = N(0, ρ⁻¹I)`, `mFirstEigenDim = k`. The trivial splitting (`N` a point, `V' = 0`, `μ' = δ`, `Φ = id × pt`) gives
  `ρ‖x‖²/2 + 0 + (k/2)log(2π/ρ)`: exactly `V`. So the constant is the normalization constant of the Gaussian and the identity holds on the witness; the new conjunct is not contradicted by the witness. (The project's `splitting_applies` only
  states the old conjunct list, not the new ones; the full new statement is derived in `Extra/SplitPotential.lean` from `riemannian_gaussian_splitting_potential`, so the new conjuncts are kernel-checked on the general case, hence on the witness.)
  Note `V'` is determined by `μ'` (since `IsWeightedVolume`), so the identity is a genuine constraint, not a free choice, and cannot be satisfied by adjusting `V'`.
* Cast: `k / 2 * Real.log ...` with `k : ℕ` from `let k := mFirstEigenDim ..`. The `binop%` elaborator inserts the cast at the leaf (`(↑k : ℝ) / 2`), not `ℕ` division; the proof's `show ... (k / 2 : ℝ) * ...` confirms. No `k/2` natural-number truncation.
* `ConnectedSpace N` / `CompleteSpace N` refer to the topology / uniformity induced by the existentially quantified `EMetricSpace N` (the only instance in scope; `ChartedSpace F' N`, `IsRiemannianManifold`, `BorelSpace N` are on the same instance),
  i.e. the Riemannian distance `d_{g'}`, which is the intended structure (matches the manuscript "connected, complete"). `ConnectedSpace` includes `Nonempty N`, fine for the witness (`N` a point). Both conjuncts are consequences of the others
  (`snd ∘ Φ` is a continuous surjection from connected `M`; `N` is isometric to the closed slice `{0} × N` of the complete `M` by the edist identity), so they are true and add no vacuity; they correctly record the manuscript's requirement on `M'`.
* The conjunct `μ' probability`, `CD F' ρ V'`, `Φ : ≃ₘ^∞` and the eigenfunction statements are unchanged from `semantic-audit.md` (item 12); not re-audited.
* Residual (inherited from audit item 11/12 (b)): non-vacuity of the standing hypotheses is shown by the witness on `ℝ^k` (for the hypotheses of the old statement), which now also satisfy the new conjuncts as argued.

## Overall

Deviations, all flagged or harmless: `c ≥ 0` vs `c > 0` (1); `ρ ≥ 0` vs `ρ = λ₁` (3); statements for all `s ≥ 0` and `t₀ = 1` where the manuscript requires `t₀ > 0` / `t₀ > 1` (4; true, stronger); `0 < d` and the carrier `hL` (flagged).
Only documentation fix suggested: the docstring of `langevin_entropy_decay` ("formalization proves a sharper one") should say the statement uses the printed, non-sharp constant.
