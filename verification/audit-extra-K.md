# Audit K: kernel (Brownian-free) Euclidean definitions and the 8 replaced statements

Scope: (A) definitions `IsEuclideanDiffusion`, `IsEuclideanLangevin`, `IsSigmaDiffusion`, `IsSigmaLangevin`, `worstK`,
`mixingTimeK`, `mixingTimeW2K`, `mixingTimeKLK`, `IsRigidSequenceK`; (B) statements `main_wasserstein_estimate`,
`wasserstein_cutoff`, `wasserstein_cutoff_weak`, `information_cutoff`, `information_cutoff_weak`, `lp_cutoff`,
`convex_interaction_cutoff`, `product_condition_cutoff` against HEAD~1 and the manuscript; (C) the C^infinity trade-off.
Statements and definitions were read, not proofs. This is an AI audit, not human review.
Scratch files: `<scratchpad>/OU.lean`, `T2.lean`, `T3.lean` (scratchpad dir of this session), all compile against `Solution`.

## Verdicts

| Item | Verdict |
|---|---|
| `IsEuclideanDiffusion` / `IsEuclideanLangevin` | faithful with remarks |
| `IsSigmaDiffusion` / `IsSigmaLangevin` | faithful with remarks (same analysis, sigma-generator checked) |
| `worstK`, `mixingTimeK`, `mixingTimeW2K`, `mixingTimeKLK` | faithful |
| `IsRigidSequenceK` | faithful (identical to `IsRigidSequence` modulo the kernel hypothesis; C^infinity amendment) |
| `main_wasserstein_estimate`, `wasserstein_cutoff`, `wasserstein_cutoff_weak`, `information_cutoff`, `information_cutoff_weak`, `lp_cutoff`, `product_condition_cutoff` | faithful with remark (C^infinity only) |
| `convex_interaction_cutoff` | faithful with remark (C^infinity for `W n` and V; one redundancy) |

No defect found.

## (A) Definitions

### A1. Could a pathological `Pt` satisfy the Dynkin clause yet differ from the SDE law?
Definition: `Pt t` Markov kernel for each t; `Pt (s+t) = Pt t ∘ₖ Pt s`; for every `f ∈ C_c^∞`, every x, t:
`∫ f dPt t x = f x + ∫_0^t ∫ generator V f dPt s x ds`.

Checked statements (all proved, axioms `propext, Classical.choice, Quot.sound` only; `#print axioms` run):
- `isEuclideanDiffusion_unique : ContDiff ℝ ∞ V → IsProbabilityMeasure (gibbs V) → IsEuclideanDiffusion V P₁ → IsEuclideanDiffusion V P₂ → ∀ t x, P₁ t x = P₂ t x`. States exactly: any two such kernels agree pointwise for all t, x. Hence no pathological kernel exists for C^infinity V with probability Gibbs measure; `IsEuclideanLangevin` also contains these two hypotheses, so the uniqueness applies in every use. `isEuclideanLangevin_unique` is the same in the packaged form.
- `isEuclideanDiffusion_langevinKernel` (C² V, `Hess V ≥ rate ≥ 0`, any `IsEuclideanBrownian` carrier): the Brownian Langevin kernel `langevinKernel V B P` is an `IsEuclideanDiffusion`. With uniqueness: `isEuclideanDiffusion_eq_langevinKernel` gives `Pt t x = langevinKernel V B P t x` for any abstract Pt.
- `exists_euclideanLangevin` (C^infinity, convex, probability Gibbs): existence of Pt with `IsEuclideanLangevin V Pt`; `exists_euclideanLangevin_of_smooth` removes convexity (canonical Riemannian kernel `Kk`).
- `exists_isLangevin_of_isEuclideanLangevin` (and `exists_isLangevin_of_rigid`, `exists_isRigidSequence_of_K`): given `IsEuclideanLangevin V Pt` and Hess V ≥ 0, there are Ω, probability P, standard Brownian B, X with `IsLangevin V B P X` and `∀ t x₀, P.map (X x₀ t) = Pt t x₀`. This is exactly Law(X_t^{x₀}) = Pt t x₀, where X solves the integral equation of the SDE (IsLangevin includes `IsLangevinSolution`).
So the encoding is faithful: the kernel hypothesis is satisfiable, determines the law, and transfers to the Brownian setting with the exact law. Because the Challenge conclusions are about `Pt t x` only, a statement over all Pt with `IsEuclideanLangevin` is equivalent to the statement about the unique true kernel.

### A2. Generator and conventions
`generator V f = laplacian f - ⟪gradient V, gradient f⟫`, `laplacian f x = Σ_i D²f(x)(e_i,e_i)` (standard basis of `EuclideanSpace ℝ (Fin d)`), `gradient` is Mathlib's Riesz gradient. This is Δ - ∇V·∇, the generator of dX = -∇V dt + √2 dB (no factor 1/2 error: √2 B gives Δ). Invariant measure e^{-V}: consistent. The sigma version `σ²Δ - ∇V·∇` is the generator of dY = -∇V dt + √2σ dB with invariant measure e^{-V/σ²}; `IsSigmaLangevin` asks `IsProbabilityMeasure (gibbs (V/σ²))`, consistent. (For σ = 0 the gibbs of `V x / 0 = 0` is Lebesgue, not a probability: the hypothesis is false for σ=0, harmless; the statements use `0 < σ`.)

### A3. Junk values in the Dynkin clause
- Test function integral `∫ f dPt t x`: f is C_c^∞, bounded continuous, Pt t x probability: always integrable, no junk.
- Inner integral `∫ generator V f dPt s x`: `generator V f` is continuous and compactly supported (V is C^infinity, hence the gradient is continuous): bounded, integrable w.r.t. a probability measure: no junk. Time integrand `s ↦ Ps(Lf)(x)`: if it were not interval integrable, the interval integral would be 0 (junk). This could only matter for a pathological Pt that is not measurable in s; but the uniqueness theorem is proved for all Pt satisfying the clause as written (junk reading included), and the true kernel has a continuous integrand, so the honest reading holds for it. No loophole.
- t = 0: clause gives `∫ f dP0 x = f x` for all f ∈ C_c^∞, so `P0 x = δ_x`; consistent.
- `s.toNNReal` on `s ∈ [0,t]`: identity on the integration range; no issue. `(t : ℝ)` coercion of `t : ℝ≥0` fine.
- Semigroup order: `(Pt t ∘ₖ Pt s) x = (Pt s x).bind (Pt t)` so s is applied first: correct Chapman–Kolmogorov.
- Kernel measurability in x is part of `Kernel`. `Pt` at all x (not a.e.) is required, as for the true kernel.
- `ContDiff ℝ ∞` is smooth (`∞` from `open scoped ContDiff` is `((⊤ : ℕ∞) : WithTop ℕ∞)`, not analytic; checked `rfl` in scratch).
- Non-vacuity/test: OU potential `gaussPot d ρ = ρ/2‖x‖² + (d/2) log(2π/ρ)` (normalized): scratch `OU.lean` proves `∃ Pt, IsEuclideanLangevin (gaussPot d ρ) Pt` for every d, ρ > 0 via `exists_euclideanLangevin` (hypotheses: `contDiff_gaussPot`, Hessian `ρ‖z‖² ≥ 0`, `isProbabilityMeasure_gibbs_gaussPot`), and the transfer `IsEuclideanLangevin V Pt → RigidCurvature V → ∃ carrier with P.map (X x₀ t) = Pt t x₀` type-checks as stated. For a general `V = ‖x‖²/2 + c`, the probability hypothesis forces `c = (d/2) log(2π)`; this is inherent to Gibbs normalization (also in the manuscript).

### A4. `worstK`
`worstK Pt S δ t = ⨆ x₀ ∈ S, δ (Pt t.toNNReal x₀)`. For t < 0 this is the value at 0; all critical times (`criticalTime n gap = log n / (2 gap) ≥ 0` for n ≥ 1, gap > 0; `t₀.toReal ≥ 0`) are nonnegative, so `(1±ε) t n ≥ 0` and `toNNReal` is the identity wherever it matters. Empty S gives ⊥ = 0 (statements either have nonempty S by `hS` or balls/cubes with c > 0 nonempty: centered at the mean, c·√d ≥ 0, contains the mean). Same as old `worst`.

### A5. Mixing times
`⨅ t (_ : worstK … t ≤ ofReal η), (t : ℝ≥0∞)`: inf over nonnegative t, `⨅ ∅ = ⊤` as documented. `ofReal η` for η ≤ 0 is 0 (all statements assume 0 < η). TV: `ofReal (tvDist ν μ)`; tvDist is a real sup over measurable sets, bounded for probability measures (`Pt t x` Markov, `gibbs (V n)` probability by `IsEuclideanLangevin`), so no unbounded-sup junk. `mixing_time_*` statements use the same mixing time structure as the old ones, with `worst → worstK` only (`mixingTime_eq_mixingTimeK` etc. proved for equal laws).

### A6. `IsRigidSequenceK` vs `IsRigidSequence`
Old: `(∀ n, 0 < n → IsLangevin (V n) (B n) (P n) (X n) ∧ RigidCurvature (V n)) ∧ 0 < liminf ofReal(spectralGap (V n))`. New: same with `IsEuclideanLangevin (V n) (Pt n)`. Same quantifier shape (positive dimensions only), same liminf condition. `RigidCurvature` implies convex (`RigidCurvature.hess_nonneg`), which is what the transfer needs.

## (B) Statement comparison (HEAD~1 vs HEAD vs manuscript)
Compared the old (HEAD~1) text line by line. In all 8 statements the only changes are: (i) the carrier tuple `Ω, B, P, X` and `IsLangevin V B P X` replaced by `Pt` and `IsEuclideanLangevin V Pt`; (ii) `worst P X` → `worstK Pt`, `mixingTime*` → `mixingTime*K`; `P.map (X x₀ t)` → `Pt t x₀` (main estimate); (iii) C^infinity inside `IsEuclideanLangevin` (old `IsLangevin` had `ContDiff ℝ 2`). Everything else identical: hypotheses (`RigidCurvature`, `hsmall` o(log n) / n^{o(1)}, `hgap` `(λ₁)⁻¹ ≤ (log n)^α` with `0 < α`, `0 < c`, `hp : 1 ≤ p`, `p ≠ ⊤`), quantifiers (`∀ n, 0 < n → …`), limits (`⊤ 0`, `1 0`, `if p = 1 then 2 else ⊤`, `⊤ 0` etc.), `liminf` conditions (`0 < liminf ofReal κ n`, `t₀ → ∞`, `κ t₀ → ∞`, `∀ᶠ n, t₀ n < ⊤`), and the ranges `0<η<1`. No hypothesis dropped or added, apart from:

- `convex_interaction_cutoff`: `hW` now asks `ContDiff ℝ ∞ (W n)` (was 2) and `hL` asks (inside `IsEuclideanLangevin`) `ContDiff ℝ ∞ (ρ/2‖x‖²+W n x)` (this part is redundant with `W n` C^infinity, harmless). Both flagged ("Amendments: W n and the potential are C^∞ (not C²)"). For Cor 1.6 the manuscript asks C² (convex).
- `product_condition_cutoff`: C^infinity for `V n` (flagged); `0 < κ n` and Hessian lower bound kept as before. The Hessian bound is stated with `fderiv`, as in old.
- Statement docstrings correctly say "Amendment" (flagged) in main, 1.3, 1.4, lp, 1.6, 1.7, weak remarks. Unflagged deviations: none found. (`main_wasserstein_estimate` docstring says C^infinity amendment; the t in `Pt t x₀` is `t : ℝ≥0` exactly as the old `X x₀ t`.)
- Junk removed: the old `P.map (X x₀ t)` was `0` for non-AE-measurable maps; the kernel version has no such junk. So the new statements are, if anything, less exposed to this junk.
Implication direction: new statement for (V, Pt) with `IsEuclideanLangevin` follows from the old statement via the transfer lemma (needs only convexity, which `RigidCurvature` or the convex-interaction hypotheses supply); `exists_isRigidSequence_of_K` produces the carriers per dimension, in particular for `convex_interaction_cutoff` and `product_condition_cutoff` through the corresponding `_carrier`/`_all` theorems. The kernel statements are therefore equivalent to the old ones restricted to C^infinity potentials.

One non-defect remark: `IsEuclideanLangevin` does not include convexity, so e.g. `main_wasserstein_estimate` has `hV : RigidCurvature V` separately (as before). For non-convex V the notion is still meaningful (kernel exists, `exists_euclideanLangevin_of_smooth`), but no Challenge statement is asserted without rigid curvature or κ-convexity.

## (C) The C^infinity trade-off
Lost in the Challenge (the numbered statements): the cases V ∈ C² \ C^infinity. Concretely, the 21 replaced Challenge statements (Thm 1.1, Cor 1.3, 1.4, (1.25), Cor 1.6, Thm 1.7, Remarks 3.4, 3.5, the OU, temperature, mixing-time and dynamics statements) no longer cover, e.g.: W(x) = Σ_i |x_i|³ or Σ |x_i|^{5/2} (convex, C², not C³), Huber/piecewise-quadratic convex interactions, V = ρ/2|x|² + Σ φ(x_i − x_j) with φ convex C² but not C^3 (nonsmooth third derivative) — all admitted by the manuscript's "strictly convex and C²" setting (line 92) and Cor 1.6's "W convex C²". Not lost: the Dyson-type log-gas singular potentials, because those are not real-valued C² potentials on ℝ^d and were never covered by either version. Not lost either: all C^infinity examples (Gaussian, OU, double-well-free convex smooth V, W smooth interactions such as log-cosh, softplus, quartic).
Also the two equivalent-looking hypotheses differ: the old `IsLangevin` for C² V assumed a given Brownian solution family; new requires a smooth V and kernel. There is no loss on the SDE side for C^infinity.

The old C² versions remain in the repo, proved: `CutoffRigidity.Paper.main_wasserstein_estimate_carrier`, `wasserstein_cutoff_carrier`, `information_cutoff_carrier`, `lp_cutoff_carrier`, `convex_interaction_cutoff_carrier` (C² `W n`), `product_condition_cutoff_carrier` (and `product_condition_cutoff_all`), `wasserstein_cutoff_weak_carrier`, `information_cutoff_weak_carrier`, `mixing_time_rigid_carrier`, and the Extra carriers (`ou_*_carrier`, `langevin_*_carrier`, `temperature_cutoff_carrier`, `normalization_cutoff_carrier`, `optimal_*_carrier`). Verified by `#print axioms` (scratch `T3.lean`): the 8 carrier theorems tested depend only on `propext, Classical.choice, Quot.sound` (no sorry; no file under `CutoffRigidity/` or `Solution.lean` contains `sorry`). Their hypotheses use `IsLangevin` (still defined in `Challenge.lean`, with `ContDiff ℝ 2 V`), defined in `Paper/CarrierDefs.lean` (`worst`, `IsRigidSequence`, mixing times). They are NOT in `comparator.json` (`grep -c carrier = 0`) and not stated in `Challenge.lean`, so they are not covered by the Comparator check of statements; the claim "C² versions are available" is a claim about proved theorems in the library whose statement fidelity rests on this audit of their definitions and the earlier carrier-era audits. Challenge.lean still keeps `exists_stdBrownian` and `exists_langevin` for C² convex V (Brownian existence is tested at the C² level).

## Remarks and suggestions (no defect)
1. Documentation: the README/Challenge preface could state explicitly that the manuscript's C² generality is retained only in the `_carrier` theorems (not Comparator-checked) while the Challenge asserts C^infinity.
2. `convex_interaction_cutoff`: the ContDiff of V inside `IsEuclideanLangevin` is redundant given `hW`; harmless.
3. The uniqueness is proved for `IsProbabilityMeasure (gibbs V)` and C^infinity V via the Riemannian bridge; a C² extension of uniqueness (to restore the old generality at Challenge level) is not available here.
