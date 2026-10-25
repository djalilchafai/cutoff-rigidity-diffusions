# Statement-fidelity audit A (new statements): Remarks 3.4/3.5, mixing time, OU examples

Nature: AI audit (LLM agent), not human review. I read `Challenge.lean` statements and the definitions they use
(`IsRigidSequence`, `RigidCurvature`, `spectralGap`, `criticalTime`, `HasCutoff`, `worst`, `mixingTime`, `relLp`,
`meanBall`, `IsLangevin`) and the manuscript `cutcur-lean.tex` (L166-240, L349-412, L1044-1052, L1182-1188, L1225-1250).
I did not read proofs and wrote no Lean scratch files; the checks below are by hand computation with the explicit OU
Gaussian laws. No file was edited except this report. Line numbers: `C:` Challenge.lean, `T:` cutcur-lean.tex.

## Summary

No defect found in any of the five statements. Verdicts:

| Statement | Manuscript item | Verdict |
|---|---|---|
| `wasserstein_cutoff_weak` (C:336) | Remark 3.4 (T:1044-1048) | faithful with remarks |
| `information_cutoff_weak` (C:351) | Remark 3.5 (T:1182-1188) | faithful with remarks |
| `mixing_time_rigid` (C:561) | T:349, T:387-393, T:409 | faithful with remarks |
| `ou_mean_start_cutoff` (C:580) | T:~196-203 (after Cor 1.3) | faithful with remarks |
| `ou_lp_infty_fails` (C:597) | T:~403 ("p=infinity excluded") | faithful with remarks |

## Shared definitions (only what matters here)

- `spectralGap V = sInf {Rayleigh quotients}`: junk value 0 when the set is empty (d = 0, or no non-constant test
  function with positive variance) and `sInf` of a set bounded below by 0 otherwise. Consequences: every use here is
  guarded. `RigidCurvature V` contains `0 < spectralGap V`, so for n > 0 in `IsRigidSequence` and in
  `wasserstein_cutoff_weak` the gap is a genuine positive number, and the inverse `(spectralGap)⁻¹` in Remark 3.4 and
  `criticalTime` (`log n / (2 gap)`) never hit division by zero for n ≥ 1. For `ou_mean_start_cutoff` and
  `ou_lp_infty_fails` there is no `RigidCurvature` hypothesis; `spectralGap` equals ρ for n ≥ 1 (this is the theorem
  `ou_first_eigenspace`), and in `ou_lp_infty_fails` the first conjunct does not use the gap at all, and the second
  follows from the first for any value of the gap. Not exploitable.
- `IsRigidSequence`: hypotheses only for `0 < n` (so n = 0 junk is excluded) plus `0 < liminf ofReal(gap)` in ℝ≥0∞.
  This liminf also admits `gap → ∞` (liminf = ⊤); the manuscript's `liminf λ₁ > 0` (T:~178) admits it as well, so this is
  faithful, and `λ₁ → ∞` is not contradictory with the extra hypotheses used (see Rem. 3.5 and `hsmall` below).
- `criticalTime n gap = log n / (2 gap)`, real; for gap > 0 and n ≥ 1 it is ≥ 0, so `t.toNNReal` in `worst` never
  truncates a negative critical time or `(1-ε)t*`, `(1+ε)t*` (ε in (0,1)). The only truncation case is n = 0 where
  `log 0 = 0`; irrelevant to a limit. In `ou_lp_infty_fails` the times `t n : ℝ` are arbitrary, negative ones truncate
  to 0, which is harmless (profile is ⊤ there, see below).
- `HasCutoff` quantifies all ε in (0,1) and requires both limits; limits are in ℝ≥0∞ (so ⊤ means divergence to +∞).
  Matches the manuscript displays (ε in (0,1), limits +∞/0 or 1/0).
- `worst` takes `⨆ x₀ ∈ S` of the discrepancy of `P.map (X x₀ t.toNNReal)`; `Measure.map` of an a.e.-non-measurable
  map would give the zero measure, but `X t` is a.s. equal to a measurable function of the Brownian path by the
  `IsLangevin` hypotheses (this point was already analyzed in `semantic-audit.md` for the original 12 theorems).
  Same convention as the already audited Corollaries 1.3/1.4.

## 1. `wasserstein_cutoff_weak` (Remark 3.4)

Manuscript: "the assumption liminf λ₁ > 0 could have been replaced by a slow enough growth of λ₁⁻¹, for instance
λ₁⁻¹ ≤ (log d)^α for some α > 0". Lean: Corollary 1.3's conclusion with the hypothesis
`IsRigidSequence` replaced by (Langevin + RigidCurvature for n>0) and
`∃ α > 0, ∀ᶠ n, (spectralGap (V n))⁻¹ ≤ (log n)^α`.

- Faithfulness of the replacement: the manuscript says "slow enough growth, for instance"; Lean formalizes exactly the
  instance, with ∃α>0 and "eventually" (for n large, `log n > 0`, so `(log n)^α` is the real power and positive for
  n ≥ 2). Dropping `liminf > 0` and keeping the Langevin/curvature part is the right reading. Severity: none.
- Junk: `(gap)⁻¹ ≤ (log n)^α` would be trivially true if gap were 0 (inverse 0), but `RigidCurvature` gives gap > 0
  for n > 0. No exploit.
- Truth check by hand (so the statement is neither false nor vacuous): upper bound
  `W₂² ≤ q (c²d + d/λ₁)` with `q = d^{-(1+ε)}` gives `d^{-ε}(c² + 1/λ₁) → 0` because `1/λ₁ ≤ (log d)^α`;
  lower bound uses `q/λ₁ · λ₁ c² d = c² d^{ε}` at `(1-ε)t*` which diverges with no condition on λ₁. Consistent with
  the manuscript's proof (T:1025-1042).
- Remark (minor, not a defect): Lean states only the Wasserstein cutoff (what Remark 3.4 concerns), not the I/H/TV
  corollaries; the manuscript remark is also located in the proof of Cor 1.3 only.
- Hypotheses jointly satisfiable: yes in principle (OU with ρ_n = 1/log n, if a Langevin solution exists as in
  `IsLangevin`); `IsLangevin` satisfiability is an accepted standing assumption (docstring at C:94-97). I did not build
  a Lean witness (constructing a Brownian motion is not available in Mathlib).

Verdict: faithful with remarks.

## 2. `information_cutoff_weak` (Remark 3.5)

Manuscript (T:1182-1188): "the assumption λ₁ = o(log d) could have been replaced by λ₁ = d^{o(1)}", for Corollary 1.4.
Lean: `IsRigidSequence` (so liminf λ₁ > 0 retained, as in Cor 1.4) and
`∀ ε>0, ∀ᶠ n, spectralGap (V n) ≤ n^ε`, concluding the three HasCutoff statements of Cor 1.4 (I, H, TV).

- `λ₁ = d^{o(1)}` is rendered as "for every ε > 0 eventually λ₁ ≤ n^ε". Since λ₁ > 0 is bounded below eventually
  (liminf > 0), this is equivalent to `log λ₁ / log n → 0` from above, and from below it is automatic. Correct reading.
  It is strictly weaker than `o(log n)` (since `log n = n^{o(1)}`), as the remark intends. Good.
- Unflagged deviation: none. The conclusion exactly equals the conclusion of `information_cutoff` (C:198-207),
  including the constants (Fisher: ⊤/0, entropy: ⊤/0, TV: 1/0) and the set `meanBall`.
- The manuscript remark describes only the modification of the upper-bound proof, and says "hence √λ₁ for D_TV, and λ₁²
  for I". The lower bounds in Cor 1.4 are unconditional on λ₁ upper growth beyond liminf>0, so the statement is
  plausible; since Lean's proof is kernel-checked and this statement is no stronger than the manuscript's, the only
  question is whether the manuscript remark is a complete justification, which is a matter for the manuscript, not for
  fidelity of the formal statement. Note that the remark is terse ("could have been replaced") and the Lean statement
  commits to the full I+H+TV package; that is the natural reading.
- Consistency with `hsmall`-free `IsRigidSequence`: liminf λ₁ = ⊤ is allowed by both hypotheses sets (λ₁ = log n
  satisfies `≤ n^ε`), so no contradiction.

Verdict: faithful with remarks (the remark in the manuscript is only a sketch; statement is the natural formalization).

## 3. `mixing_time_rigid`

Manuscript: T:349 ("the mixing time in W₂, H and TV is always log(d)/(2λ₁)"), T:387-393 (under the hypotheses of
Cor 1.4, rigidity implies the product condition `λ₁ t₀ → ∞` and the TV mixing time tends to infinity), T:409 ("give the
mixing time as well as the cutoff"). Lean: under `IsRigidSequence` and `λ₁ = o(log n)`, for every `η ∈ (0,1)` and
`c > 0`: `t₀ < ⊤` eventually, `t₀ / t* → 1`, `λ₁ t₀ → ∞`, `t₀ → ∞`, with
`t₀ = mixingTime` from `meanBall (V n) c`.

- `mixingTime` is `⨅ (t:ℝ≥0) (_ : worst ... TV t ≤ ofReal η), (t : ℝ≥0∞)`; `⨅ ∅ = ⊤`, hence the explicit
  `t₀ < ⊤` eventually, which is also what the theorem asserts. `toReal` of ⊤ is 0 only on a finite set of n (eventually
  finite), so the limits are not affected by that junk value. Division: `t*` > 0 for n ≥ 2 (gap > 0). Good.
- The manuscript's "is `log d/(2λ₁)`" is informal; `t₀/t* → 1` is the correct precise reading (`(1+o(1))` in the
  docstring). The manuscript's statements about W₂ and H mixing times are not formalized (only TV), which is a
  narrowing, not a defect: the lines the statement is attached to (T:387-393) concern the TV mixing time.
- The `η` quantifier: `0 < η < 1`, which is the full non-degenerate range (η ≥ 1 gives t₀ = 0 trivially; η ≤ 0 makes
  the sets empty or degenerate); this matches Theorem 1.7 (η in (0,1)).
- Non-triviality of the conclusion: t₀/t* → 1 gives upper bound via TV → 0 at (1+ε)t* and lower bound via TV → 1
  at (1−ε)t*; the lower bound for the infimum needs monotonicity of the sup-TV profile in t (data processing for the
  Markov semigroup), not only the single-time limit from Cor 1.4. The Lean proof is kernel-checked, so this is not an
  issue of statement fidelity; but it means the statement is genuinely stronger than a restatement of `HasCutoff`.
- `t₀ → ∞` and `λ₁ t₀ → ∞` are true: `t* = log n/(2λ₁) → ∞` since `λ₁ = o(log n)` and `λ₁ t₀ ~ (log n)/2 → ∞`.
  The `o(log n)` hypothesis is needed for `t₀ → ∞`; the manuscript says so ("under the hypotheses of Corollary 1.4,
  including ... λ₁ = o(log d)", T:387-390). Fine.
- Not vacuous: same satisfiability as Cor 1.4 (OU with ρ constant).

Verdict: faithful with remarks (only TV mixing time formalized; `(1+o(1))` made precise as ratio → 1).

## 4. `ou_mean_start_cutoff`

Manuscript (T:196-203 region, after Cor 1.3): "assumption c>0 is essential ... for the d-dimensional OU process with
`S = {m}` and `λ₁ = ρ > 0` independent of d, one has a cutoff at critical time `log(d)/(4λ₁)`" [and, implicit, not at
`log d/(2λ₁)`; the Lean docstring says "no cutoff at the critical time of Cor 1.3"]. Lean:
`HasCutoff prof (log n/(4 gap)) ⊤ 0 ∧ ¬ HasCutoff prof (criticalTime n gap) ⊤ 0` for
`V n = ρ|x|²/2 + c n`, `prof = worst` over `{mean of gibbs}` of W₂.

- `IsLangevin` includes `IsProbabilityMeasure (gibbs V)`, so `c n` is forced to be the log-normalizer; ρ is n-independent
  (as in the manuscript). `gap = ρ` for n ≥ 1; the mean is 0.
- Truth check: from the mean 0, `μ_t = N(0, (1-q)/ρ I)`, `q = e^{-2ρt}`, so
  `W₂² = (d/ρ)(1-√(1-q))² ≈ d q²/(4ρ)`. At `t = (1∓ε) log n/(4ρ)`: `n·n^{-(1∓ε)}`, i.e. `n^{±ε}`: diverges before, tends
  to 0 after. At `t* = log n/(2ρ)`: `W₂² ≈ n^{-1+2ε}/(4ρ)` before (so → 0 for ε < 1/2, not ⊤), so `¬ HasCutoff (⊤,0)`
  holds (take ε = 1/4). Both conjuncts are true, and the negated one is not due to junk.
- Meaning of "no cutoff": Lean proves the negation of the specific pattern (limits `⊤` before and `0` after) that
  Corollary 1.3 asserts. The manuscript's sentence ("one has a cutoff at log d/(4λ₁)", "c>0 is essential") is
  informally the failure of Corollary 1.3's conclusion at `t*`; so this reading is the natural one. It is weaker than
  "no cutoff at t* for any pair of limits" but in this example both profiles at `(1±ε)t*` tend to 0 (for small ε), so
  a cutoff with limits (before, after) ≠ (0,0) is also false; the manuscript has no claim stronger than the Lean one.
  Remark only.
- The cutoff at `log n/(4ρ)` is also stated with limits `(⊤, 0)`; manuscript does not specify limits for this one, and
  `(⊤,0)` is the standard one and what is true. Fine.
- `0 < n` guards: yes (`hL` only for n > 0). `hρ : 0 < ρ`. No `RigidCurvature` hypothesis, none needed.

Verdict: faithful with remarks.

## 5. `ou_lp_infty_fails`

Manuscript (T:403): "The case p = ∞ is excluded: it fails already for the Ornstein-Uhlenbeck process." Lean: for OU
`V n = ρ|x|²/2 + c' n` and balls `meanBall (V n) c`, `c > 0`, `prof = worst (relLp · μ ⊤)`:
`(∀ t : ℕ → ℝ, prof n (t n) → ⊤) ∧ ¬ HasCutoff prof (criticalTime ..) ⊤ 0`.

- `relLp ν μ ⊤ = if ν ≪ μ then eLpNorm (rnDeriv.toReal - 1) ⊤ μ else ⊤` is the essential supremum of `|dν/dμ - 1|`
  (`eLpNorm` at `⊤` is `essSup ‖·‖ₑ`). For `μ` σ-finite, `rnDeriv < ⊤` a.e., so `toReal` truncation does not matter.
  For t = 0 (or negative times, via `toNNReal`), `ν = δ_{x₀}` is not ≪ μ, giving ⊤: correct convention (+∞).
- Truth check by hand: for t > 0, `μ_t = N(e^{-ρt}x₀, (1-q)/ρ I)`, `dμ_t/dμ(x) = (1-q)^{-d/2}
  exp(-ρ|x-a|²/(2(1-q)) + ρ|x|²/2)`, `a = e^{-ρt}x₀`. This density is continuous and positive, so the essential
  supremum equals the supremum; the maximum is at `x = e^{ρt}x₀` with value `(1-q)^{-d/2} exp(ρ|x₀|²/2)`. Taking
  `|x₀| = c√n` (boundary of the ball, which lies in `meanBall` since the mean is 0) gives
  `ess sup |h-1| ≥ exp(ρ c² n/2) - 1 → ∞`, uniformly in t > 0, including times t_n → ∞. So the first conjunct (for
  every sequence of times, including ones tending to ∞) is true, and the quantifier "∀ t" with `Tendsto ... (𝓝 ⊤)` is
  the right way to say it.
- The second conjunct follows from the first; in particular it uses that HasCutoff's second limit 0 at
  `(1+ε)t*` would contradict ⊤. So no dependence on the value of `spectralGap` (junk-free).
- Matching the manuscript: the manuscript only says that the p = ∞ analogue of (1.25) fails; Lean states both the
  failure (`¬ HasCutoff ... ⊤ 0`, i.e. the analogue of (1.25) with max = ⊤) and the stronger statement that the profile
  is ⊤ in the limit for every time sequence. The stronger conjunct is not claimed in the manuscript's text but is the
  true reason and is flagged in the docstring. Remark only.
- Subtle point: "p = ∞ analogue of (1.25)" has no fixed value of `max`; the Lean negation is for the limits `(⊤, 0)`;
  since the profile → ⊤ at all times, no other cutoff pattern with a finite "after" limit exists either. Nothing lost.

Verdict: faithful with remarks.

## Cross-cutting remarks

1. All five statements use the abstract carrier `IsLangevin`/`IsRigidSequence` whose satisfiability relies on the
   classical existence of Brownian motion and of strong solutions of the Langevin SDE; it is accepted and flagged in
   `Challenge.lean` (C:94-97). I could not produce a Lean witness (no Brownian motion construction in Mathlib).
2. No unflagged amendment found: no added `0 < d`-type hypothesis, no dropped hypothesis, no extra test class. The
   n-guards `0 < n` are placed in front of the per-dimension hypotheses and are harmless since only the limits matter.
3. Nothing in these five statements depends on `toReal` of ⊤, `sInf ∅` or division by zero for the n that matter.
