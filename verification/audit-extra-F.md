# Statement-fidelity audit F (Challenge.lean: optimal_lsi_twice_pi, optimal_constants_extremal, talagrand_logSobolev + entropyOf, IsTestFunction, optimalPI, optimalLSI, fisherInfo)

AI audit (LLM agent, adversarial reader), not a human review. Statements/definitions read; proofs not read.
Manuscript: cutcur-lean.tex 808-825 (optimal constants), 219-224 (H, I), 1131-1140 (Talagrand, LSI). No Lean scratch file was run:
every check below was done by hand (non-vacuity is argued explicitly, see 5).

## Verdicts
| Statement | Verdict |
|---|---|
| `optimal_lsi_twice_pi` | faithful (true for every C^2 V meeting the hypotheses) |
| `optimal_constants_extremal` | faithful with remarks (`0<d` necessary; "extremal" made precise) |
| `talagrand_logSobolev` | faithful with remarks (`0<d` unnecessary but harmless) |
| `entropyOf`, `IsTestFunction`, `optimalPI`, `optimalLSI` | faithful, no junk exploit |
| `fisherInfo` | correct extended definition, no junk value |

No defect found.

## 1. Carrier removal: `IsLangevin` vs. new hypotheses
`IsLangevin V B P X` = `ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs V) ∧ IsStdBrownian B P ∧ SDE solutions`. The new statements keep exactly
`hV : ContDiff ℝ 2 V` and `hp : IsProbabilityMeasure (gibbs V)` (`optimal_constants_extremal`: `hW : ContDiff ℝ 2 W` gives V in C^2, `hp` is on V).
Nothing else was in the bundle; nothing added except `hd : 0 < d` (flagged). The conclusions mention only `gibbs V`, so dropping B, P, X removes
a pure existence/vacuity burden, no mathematical content. Statements are strictly stronger than the old ones.

## 2. optimal_lsi_twice_pi
Hyp: C^2 V, gibbs V probability, `0<λ₁ ∧ Hess V ≥ λ₁ I` (λ₁ := `spectralGap V`, the inf of Rayleigh quotients over C_c^∞).
* Set defining `spectralGap` is nonempty (a nonconstant bump has positive variance since e^{-V}>0) and ≥ 0; so the `sInf` is the real inf, no junk.
* `optimalPI` set: nonempty (contains 1/λ₁: Poincaré for C_c^∞ extends to bounded Lipschitz smooth f by cutoffs χ_R f, error ≤ ‖f‖_∞/R), bounded below by 0 (built in `0 ≤ C`).
  Lower bound: C_c^∞ ⊂ test class, so C ≥ sup Var/∫|∇f|² = 1/λ₁. Hence optimalPI = 1/λ₁. (f constant: 0 ≤ 0 fine; ∫|∇f|²=0 forces f constant, no division.)
* `optimalLSI` set: nonempty (Bakry–Émery, Hess ≥ λ₁, gives C = 2/λ₁ for C^2 V; extends to the test class), bounded below by 0. Lower bound by f = 1+εg, g ∈ C_c^∞:
  Ent(f²) = 2ε²Var g + o(ε²), giving C ≥ 2Var g/∫|∇g|², sup over g = 2/λ₁. So optimalLSI = 2/λ₁ = 2·optimalPI.
* All integrands are bounded (f bounded, ∇f bounded by Lipschitz), so no Bochner junk; `variance` = real variance of a bounded function.
* Hypothesis `hR` satisfiable (Gaussian: λ₁ = ρ). Manuscript says "optimal PI constant is 1/λ₁; rigidity ⇒ LSI constant twice" — matches.

## 3. optimal_constants_extremal
V = ρ|x|²/2 + W, W C^2 convex, invariant along 𝟙=`diagonal d`, `hp`. Writing x = s u + y (u = 𝟙/√d), e^{-V} = e^{-ρs²/2} · e^{-ρ|y|²/2 - W(y)}: μ = N(0,1/ρ) ⊗ ν'.
* optimalPI = 1/ρ: ≤ by Hess V ≥ ρ (W convex, so Hess W ≥ 0); ≥ by testing smooth bounded truncations ψ_R(h), ψ_R(s)=Rψ(s/R) (Var → Var h = d/ρ, ∫|∇|² → d), ratio → 1/ρ. OK.
* LSI constant 2/ρ: by part 2-type argument (LSI from Hess ≥ ρ; lower bound from the extremal sequence below). OK.
* h = Σxᵢ = √d·s: MemLp 2 (Gaussian), Var h = d/ρ > 0 (needs d>0: for d=0 h=0 and `0<variance` is false, so `hd` is NECESSARY, not just harmless), ∇h = 𝟙, |∇h|² = d, and Var h = (1/ρ)·d. ✓.
* Exponential: f = e^{αh}, c = 2α√d. E e^{cs} = e^{c²/2ρ}, Ent(e^{cs}) = c²/(2ρ) e^{c²/2ρ} = (2α²d/ρ) e^{c²/2ρ}; RHS = (2/ρ)·α²d·E e^{2αh} = (2α²d/ρ)e^{c²/2ρ}. Equality ✓, all integrals finite (Gaussian), α=0 gives 0=0 and the `α ≠ 0 → 0 < …` clause is correct.
  `Real.log (Real.exp (αh)^2) = 2αh` is exact, so no log junk; `Real.log 0` never occurs (exp>0).
* The integrability conjuncts are not junk-excluding extras: they certify that Bochner integrals in the equality are genuine. Right choice since h, e^{αh} are outside the bounded test class, so "extremal" is expressed as equality with the optimal constants. The manuscript's "extremal for LSI/PI" is exactly this.
* `hp` non-vacuous: W ≡ log((2π/ρ)^{d/2}) (constant is convex, smooth, invariant).
* `hconv` implied-by/consistent with Hess; `hinv` for all x, s as in the manuscript (translation invariance along (1,…,1)).

## 4. talagrand_logSobolev
Hyp: C^2 V, gibbs V probability, d>0, ρ>0, Hess V ≥ ρ I, ν any probability measure.
Normalizations: manuscript H = ∫h log h dμ = `klDiv` (for probability measures klDiv = ofReal(∫llr dν), `⊤` if ν ≪̸ μ or llr not ν-integrable; llr⁻ is always ν-integrable under Jensen, so this is ⊤ iff H=∞) ✓.
W₂ = (inf over couplings ∫ edist² )^{1/2} ✓ (couplings exist; EuclideanSpace edist is the ℓ² distance). I(ν|μ) = 4∫|∇√h|²dμ = ∫|∇h|²/h dμ = ∫|∇log h|²dν ✓.
Hand check, μ = N(0,I/ρ), ν = N(m,I/ρ): W₂ = |m|, H = ρ|m|²/2, I = |∇log h|² = |ρm|² = ρ²|m|². Talagrand ρ|m|² ≤ 2·ρ|m|²/2 equality ✓; LSI H ≤ I/(2ρ) = ρ|m|²/2 equality ✓. Both match manuscript (W₂² ≤ 2H/ρ; H ≤ I/(2ρ)).
Edge cases:
* d=0: statement is true there too (everything is a Dirac mass, H=W₂=I=0), so `hd` is harmless/unneeded; no problem.
* ν ≪̸ μ: H=⊤ and I=⊤ (inf over empty set), 2·⊤=⊤ ≥ anything, ⊤ ≤ ⊤/ofReal(2ρ)=⊤ ✓ (2ρ>0, no division by 0).
* ν with infinite second moment: W₂ = ⊤ and ofReal ρ·⊤ = ⊤ ≤ 2H forces H = ⊤; mathematically true (Talagrand ⇒ W₂²≤2H/ρ, μ has finite 2nd moment), so no counterexample; ENNReal arithmetic `(a^{1/2})^2` fine.
* hp is just normalization: Hess ≥ ρ already makes e^{-V} integrable; so "∫e^{-V}=∞" cannot occur under these hypotheses.
* Only C^2 V (not C^3 etc.): Bakry–Émery/Otto–Villani hold for C^2 strongly convex potentials; Talagrand also holds for any ρ-strongly log-concave probability.

## 5. fisherInfo (C:118) for non-smooth ν
I(ν|μ) = inf over G ∈ L²(μ;ℝ^d) with ν ≪ μ and ∫√h ∇φ dx = -∫ φ G dx for all φ ∈ C_c^∞, value 4∫|G|²dμ. Note the identity uses Lebesgue `∫ x` (no `∂gibbs`): this is the ordinary distributional gradient of √h, which is the right object (the density e^{-V} is C^1, positive, so the weighted and unweighted distributional gradients coincide; a μ-weighted identity would be a different, wrong, one). Checks:
* No junk integrals: √h ∈ L²(μ) ⊂ L²_loc(dx) (e^{-V} bounded below on compacts) and G ∈ L²(μ) ⊂ L²_loc(dx); so both Bochner integrals are over integrable functions, a junk-0 "weak gradient" cannot occur.
* G unique a.e. if it exists, so the inf is a min; ν ≪̸ μ gives `⨅ ∅ = ⊤` ✓; `rnDeriv.toReal` finite a.e. since ν finite.
* Value: for smooth h > 0 equals ∫|∇h|²/h dμ ✓; equals ⊤ if √h ∉ W^{1,2}(μ).
* Truth of LSI with this I for every ν (potential junk-value counterexample): Ent(f²) ≤ (2/ρ)∫|∇f|²dμ for f = √h ∈ L²(μ) with weak ∇f ∈ L²(μ). Smooth compactly supported functions are dense in W^{1,2}(μ) for a weight locally bounded above/below (mollify + cutoff, f ∈ L²), and the entropy is L¹-lower semicontinuous (variational formula), so the inequality passes to the limit. No counterexample; if I=⊤ the inequality is trivial.

## 6. Definitions
* `entropyOf μ g = ∫ g log g − (∫g) log ∫g`: standard Ent. Only applied to bounded f² ≥ 0 (or to e^{2αh}, with integrability asserted) so no junk; `Real.log 0 = 0` agrees with 0·log 0 = 0.
* `IsTestFunction`: smooth + bounded + Lipschitz. Contains C_c^∞, contained in W^{1,2}(μ); inf over this class equals the inf over C_c^∞ (cutoff approximation), so equal to the manuscript's optimal constants. Class not specified in the manuscript; this choice is harmless (flag in docstring is accurate).
* `optimalPI`/`optimalLSI`: `sInf` over sets that include `0 ≤ C` (bounded below) and are nonempty under all three theorems' hypotheses; hence real infima, no junk `sInf ∅ = 0` or unbounded-below `0`.

## 7. Remarks (non-defects)
* `hd` in `talagrand_logSobolev` is not needed; in `optimal_constants_extremal` it is needed.
* The three theorems no longer depend on the existence of a Brownian motion; hypotheses are jointly satisfiable (Gaussian V = ρ|x|²/2 + c; extremal: W constant).
