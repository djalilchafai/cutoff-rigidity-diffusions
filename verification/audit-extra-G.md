# Statement-fidelity audit G (Challenge.lean: product_condition_cutoff, mixingTime use, heat_kernel_score)

AI audit (LLM agent, adversarial reader), not a human review. Statements/definitions read; proofs not read. All checks done by hand
(no scratch Lean file). Manuscript: cutcur-lean.tex 429-493 (Thm 1.7), 1243-1320 (proof), 743-800 (heat kernel section); PAPER_AUDIT.md 104-156.

## Verdicts
| Statement | Verdict |
|---|---|
| `product_condition_cutoff` (hS weakened to `0 < n`) | faithful with remarks (amendments necessary and harmless) |
| `heat_kernel_score` (with `Differentiable ℝ u`) | faithful with remarks (now meaningful; strictly more general than the paper) |

No defect found.

## 1. product_condition_cutoff

### 1a. Dropping `S 0` nonemptiness (and `0<n` guards on hL)
Worst junk case: `S 0 = ∅`, `V 0` arbitrary, `κ 0` arbitrary, `Ω 0` whatever. Then `worst (P 0)(X 0)(S 0) δ t = ⨆ ∅ = 0`, so `mixingTime` at n=0
is `⨅ over all t≥0 (0 ≤ ofReal η) = 0`; finite, harmless anyway. Every use of index n in the statement:
* `∀ᶠ n in atTop, t₀ n < ⊤` : eventual, index 0 irrelevant.
* `Tendsto (κ n * (t₀ n).toReal) atTop atTop` : limit at infinity, a single index does not matter.
* `HasCutoff` unfolds to `∀ ε∈(0,1), Tendsto (profile n ((1∓ε) t n)) atTop (𝓝 _)` : all `Tendsto ... atTop`, so only n large matters (`Tendsto` is
  insensitive to finitely many terms). Same for `profile`, `fun n => (t₀ n).toReal`.
* `liminf (ofReal (κ n)) atTop` : insensitive to n=0; ENNReal liminf, `0<liminf` iff eventually bounded below by a positive constant (liminf=∞ allowed,
  matching the paper's `liminf κ > 0`).
Hence the weakened statement is equivalent to the `∀ n` version restricted to n ≥ 1, i.e. strictly more general and no junk exploit. Also, with
`0<n` guards the hypotheses `IsLangevin`, `0<κ n`, Hessian bound are not imposed at n=0 (where `Rd 0` is a point and `0<κ 0`, Hessian bound would be
true vacuously anyway, but `IsProbabilityMeasure (gibbs V)` etc. are not guaranteed). Harmless. The paper's "non-empty S^(d)" is for each d in the sequence (d ≥ 1); the `0<n` form is the faithful reading.

### 1b. Other points checked on the shared definitions
* `mixingTime`: `⨅ t : ℝ≥0, [worst … t ≤ ofReal η] ↦ t`, in ℝ≥0∞, `⊤` if the set is empty (documented), time domain t ≥ 0 as in the paper. `tvDist ≤ 1` for
  probability laws, `ofReal η` exact since η>0. At t=0 the law is δ_{x₀} (B 0 = 0 a.s.), TV to μ is 1 > η (η<1, μ ≪ Lebesgue), so t₀>0: no degenerate t₀ = 0
  (and κ t₀ → ∞ forces t₀>0 eventually anyway).
* For t < t₀ the set condition fails, hence `worst > ofReal η` with no monotonicity assumed; this is what the paper's lower-bound steps use. Fine.
* `∀ᶠ t₀ < ⊤` plus `(t₀ n).toReal`: `toReal ⊤ = 0` only occurs for finitely many n, so the `toReal` junk is on a finite set of indices; faithful to "t₀ finite for all large d".
* `Tendsto (κ n * t₀.toReal)` = paper's `lim κ t₀ = +∞`. Time ranges: `HasCutoff` uses ε in (0,1) (paper: ε in (0,1) for Thm 1.7), limits TV→1/0, H→⊤/0 exactly as printed.
* Positive constants κ: `0 < κ n` and `κ n ‖z‖² ≤ D²V(z,z)` (V is C² by IsLangevin so `fderiv (fderiv V)` is the genuine Hessian). Convexity is implied. Faithful.
* Fisher: `fisherInfo` is `⊤` when ν is not ≪ μ or √h has no L² weak gradient; at (1-ε)t₀ target is ⊤ (consistent), at (1+ε)t₀ target 0.
* Shared definitions (`worst`, `IsLangevin`, `wasserstein2`, `klDiv`) were already analysed in earlier audits; one residual remark only: `P.map (X x₀ t)` is
  the zero measure if `X x₀ t` were not AE-measurable. Here `X x₀ t = x₀ - ∫… + √2 B t` a.s. with continuous paths and measurable B t, so the law is a probability measure; not a defect.
* Non-vacuity: OU family `V n = n|x|²/2 + c_n`, `κ n = n`, `S n = {√n e₁}`, any fixed η, satisfies all hypotheses (see 1c: `t₀ ~ log n / n`, `κ t₀ ~ log n → ∞`,
  eventually finite), so the first block is applied non-trivially; and the amended Fisher/W₂ block applies to e.g. `V n = |x|²/2 + c_n`, `S n = {0}`: t₀ ~ (1/2) log n → ∞, κ=1.
  (Existence of Brownian motion on some Ω is the same carrier assumption as elsewhere.)

### 1c. Hand check of the PAPER_AUDIT.md OU counterexample (printed Thm 1.7 is false for W₂ and I)
Setup: dX = -∇V dt + √2 dB, V = d|x|²/2 + C, κ=d, μ=N(0, I/d), x₀=√d e₁. Mehler: X_t ~ N(e^{-dt}x₀, ((1-q)/d) I), q=e^{-2dt}. (Variance 2/(2d)·(1-e^{-2dt}) ✓.)
Rescale by √d: target N(0,I), law N(m e₁, (1-q)I), m = d e^{-dt}.
* KL = ½[m² + d(-q - log(1-q))] = ½[d^{2-2a} + d·q²/2·(1+o(1))] at t = a log d/d, q = d^{-2a}: tends to 0 iff a>1 (d^{1-4a}→0 too).
  For a<1, mean shift m=d^{1-a}→∞ with first-coordinate variance ≤1, so TV→1 (Chebyshev half-space). Hence d t₀/log d → 1 for every fixed η∈(0,1): t₀ ~ log d/d → 0, while κ t₀ ~ log d → ∞, κ = d ≥ 1. Printed hypotheses hold, t₀ → 0.
* W₂² (original scale) = |e^{-dt}x₀|² + d·(1/d)(1-√(1-q))² = d q + (1-√(1-q))² ✓ (matches PAPER_AUDIT). At (1-ε)t₀: q = d^{-2(1-ε)+o(1)}, d q = d^{-1+2ε+o(1)} → 0 for ε<1/2.
  The printed claim "W₂ → +∞ before t₀" fails.
* Fisher: ∇log(dν_t/dμ)(x) = -(dq/(1-q)) x + d m_t/(1-q) (m_t=e^{-dt}x₀). Computed E_{ν_t}|·|² = d²|m_t|² + d² q²/(1-q), with |m_t|² = q d, so
  I = d³ q + d² q²/(1-q) ✓ (matches the paper's own OU formula with ρ=d, |x₀|²=d). At (1+ε)t₀: q = d^{-2(1+ε)+o(1)}, d³q = d^{1-2ε+o(1)} → ∞ for ε<1/2.
  The printed claim "I → 0 after t₀" fails.
So the printed version (without t₀ → ∞) is false for the W₂ and I parts, as PAPER_AUDIT.md says. Flag is correct and necessary. (The TV and H parts are unaffected: in this example the OU entropy/TV cutoff does hold.)

### 1d. Is the amended version plausible/true?
With `liminf κ > 0` and `t₀ → ∞` added, the printed proof goes through step by step (I re-derived each):
* W₂ upper: Talagrand κ W² ≤ 2H and κ ≥ c > 0 eventually, H(X_{(1+ε)t₀}) → 0. ✓.
* W₂ lower (before): small-time regularization H(P_s ν|μ) ≤ W₂²/(4s) under CD(0,∞) for L = Δ - ∇V·∇ (the paper uses 1/(2s), weaker, so fine); with s=εt₀/2 and
  sup H(X_{(1-ε/2)t₀}) ≥ 2η² (Pinsker, TV > η before t₀), W² ≥ 2εη² t₀ → ∞ ⇐ t₀ → ∞. No κ lower bound used here, and the counterexample shows t₀→∞ is exactly what is needed.
* Fisher lower (before): LSI 2κH ≤ I with κ ≥ c>0 and H → ∞ ✓.
* Fisher upper (after): I(X_{t₁}) ≤ H(X_{t'})/(t₁-t') since I is nonincreasing along the flow under CD(0) and dH/dt = -I; with t₁ - t' = εt₀/2 → ∞ and sup H(X_{(1+ε/2)t₀}) ≤ C_{η,ε} ⇐ t₀ → ∞ ✓.
* Unamended parts (TV, H) rely on Salez [Cor. 1, proof of Th. 1] (external, not rechecked) and on λ₁ ≥ κ plus H(t') ≤ e^{-2κ(t'-t)}H(t) ✓.
So the amended statement is plausible and consistent with the hand proof; it is the minimal repair (the alternative κ bounded above is not equivalent but also fine; the chosen one is exactly what the proof uses). Hypothesis `0 < liminf (ofReal ∘ κ)` in ℝ≥0∞ matches printed `liminf κ>0` (∞ allowed, like the paper).

### Remarks (no severity beyond cosmetic)
1. The conclusion is stated through `HasCutoff` (ε ∈ (0,1) quantifier both sides): matches the theorem (printed "for all ε ∈ (0,1)").
2. Docstring correctly flags the amendment; the printed text says `S` non-empty and that hypothesis is retained for n ≥ 1.

## 2. heat_kernel_score
Statement: V, p continuous and differentiable, p > 0; ν = p dx. Conclusion: ∃ u, Differentiable u ∧ ν ≪ gibbs V ∧ u = log(rnDeriv).toReal gibbs-a.e. ∧ ∀ x, ∇u = ∇(log p) + ∇V.
* Truth: `gibbs V = e^{-V}dx` has everywhere-positive continuous density, so it is σ-finite and mutually absolutely continuous with Lebesgue; ν ≪ gibbs V; rnDeriv = p e^{V} a.e.;
  u := log p + V works (log∘p differentiable since p>0 differentiable), gradient additivity holds as everything is differentiable. So the statement is true; nothing needed for ν or μ to be probability measures (not assumed), correct for the paper's use ν = μ_t, p = heat kernel (which is smooth and positive for t>0; the paper only claims this identity, not the gradient bound).
* Effect of the new conjunct: with `Differentiable ℝ u`, `gradient u x` is the honest gradient (no `fderiv` junk 0). Combined with the a.e. identification, u is determined: ∇u = ∇(log p + V) everywhere ⇒ u - (log p + V) is constant (ℝ^d connected), and a.e.-equality with the full-support measure `gibbs V` kills the constant (both continuous). Thus the statement is equivalent to "log dν/dμ = log p + V a.e. and has this gradient", i.e. it now says what the paper says. Without the conjunct, u could be non-differentiable somewhere with `gradient u = 0` junk there, only partly constraining it; the repair is right.
* Remarks: `hVc`, `hpc` are redundant (Differentiable ⇒ Continuous); needed continuity of V is used for measurability of the density, harmless. `Real.log (toReal …)` is junk only where rnDeriv is 0 or ⊤, a gibbs-null set. d = 0 is trivial (point space), no `0<d` needed. The paper's statement is for p = p_{t,x₀} only; the formalization is the general fact, strictly stronger.

## Summary of deviations
| Item | Severity | Necessary? |
|---|---|---|
| hS on n>0 only, hL on n>0 only | none (only n large matters in all limits) | harmless generalization |
| `0 < liminf κ` for Fisher/W₂ | none | verbatim from the paper |
| `t₀ → ∞` for Fisher/W₂ | amendment | necessary: OU counterexample verified by hand (§1c) |
| ∀ᶠ t₀<⊤ | none | verbatim ("finite for all sufficiently large d") |
| heat_kernel_score: general p, redundant continuity, `Differentiable u` | none | conjunct makes it meaningful |
