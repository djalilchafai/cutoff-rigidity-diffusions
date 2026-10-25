# Statement-fidelity audit, batch B (Challenge.lean)

Nature: AI audit (LLM agent), not human review. Read statements and definitions only (not proofs), against
`cutcur-lean.tex` (T: lines) and `Challenge.lean` (C: lines). One scratch Lean file (scratchpad) checked that
`gradient` resolves to Mathlib's `gradient` (generic `RCLike 𝕜`, `InnerProductSpace`, `CompleteSpace`), i.e.
`(toDual ℝ F).symm (fderiv ℝ f x)`; no `CutCur.gradient` exists. On `Rd d = EuclideanSpace ℝ (Fin d)` this is the
Euclidean gradient and `‖·‖` is the L² norm, so `‖∇h‖² = d` for `h = ∑ xᵢ`. Nothing in the project was modified.

## Verdict table

| Challenge theorem | Manuscript | Verdict |
|---|---|---|
| `spectral_gap_ge_curvature` (C:369) | (1.7)/`eq:Lichne`, T:~529-566 | faithful |
| `rigidity_of_gaussian_factor` (C:380) | (R2)⇒(R1), T:~540-566 | faithful with remarks (weaker than printed R2 on "all eigenfunctions affine") |
| `entropyOf`, `IsTestFunction`, `optimalPI`, `optimalLSI` (C:392-409) | "Optimal constants", T:808-825 | faithful with remarks |
| `optimal_lsi_twice_pi` (C:417) | T:808-818 | faithful with remark on `hB` |
| `optimal_constants_extremal` (C:430) | T:821-825 | faithful with remarks (`W ∈ C²`, `0<d`, `hB` added; extremality stated as equality) |
| `pairwise_interaction` (C:537) | intro T:~290-293 | faithful (strictly stronger: no evenness) |
| `ou_first_eigenspace` (C:547) | intro T:~278-282 | faithful |

No defect found.

## 1. `spectral_gap_ge_curvature`

Statement: `d>0`, `V ∈ C²`, `gibbs V` probability, `ρ>0`, `ρ‖z‖² ≤ D²V(x)(z,z)` ∀x,z ⊢ `ρ ≤ spectralGap V`.
Manuscript: (C1)-(C4) ⇒ `λ₁ ≥ ρ` for `ρ>0`, standing assumption `μ=e^{-V}` probability.
* `spectralGap V = sInf` of Rayleigh quotients over `C_c^∞` with positive variance. The set is bounded below by 0 and is
  nonempty for `d>0` and `gibbs V` a probability measure with positive density (take any bump function that is non constant
  on the support). So the `sInf` is a genuine infimum, not the junk 0, and the conclusion `ρ ≤ sInf` with `ρ>0` cannot be
  obtained from a junk value. For `d=0` the set is empty, `sInf ∅ = 0`, conclusion false, so `0<d` is NECESSARY and harmless
  (a 0-dimensional space has no gap in the paper either).
* For `f ∈ C_c^∞`, `variance f` (Mathlib `evariance.toReal`) and the integral are of integrable functions, no junk.
* Hypotheses jointly satisfiable (OU potential with normalizing constant). `hV : ContDiff ℝ 2` is the manuscript's regularity;
  `fderiv (fderiv V) x z z` is the Hessian quadratic form. Statement (C2) is used (equivalent to the rest). Faithful.
* Remark (inherited, already in `semantic-audit.md` R1): `λ₁` is the Rayleigh infimum on `C_c^∞`, equal to the spectral gap
  for `C²` `V` by essential self-adjointness; here the inequality direction is the easy one.

## 2. `rigidity_of_gaussian_factor`

Statement: `‖u‖=1`, `V x = ρ/2(⟨u,x⟩-m)² + U x`, `U(x+tu)=U x`, `ρ‖z‖² ≤ D²U(x)(z,z)` for `z ⟂ u`, `V ∈ C²`, `gibbs V`
probability ⊢ `Hess V ≥ ρI ∧ λ₁ = ρ ∧ ⟨u,·⟩-m` is a `C²`, `L²` eigenfunction for `ρ`.
* No `0<d` needed: `‖u‖=1` forces `d ≥ 1`. (Good: `d=0` would give `sInf ∅`.) No flagged amendment, none needed.
* Generality of "up to translation and rotation": a rotation is encoded by arbitrary unit `u`; a translation `x ↦ x-a` is absorbed in `m`
  (along `u`) and in `U` (arbitrary, still `u`-invariant). So no loss of generality. The factor `N(m,1/ρ)` matches `ρ/2(s-m)²`.
  The additive constant of the second factor's potential is absorbed in `U`, normalization is `hp`.
* (R2) "the second factor is log-concave with ρ-convex potential" is read as Hessian condition on `U` in the directions `⟂u`. Since `U`
  is `u`-invariant, `U = U'∘(projection onto u^⊥)` and the condition is exactly `ρ`-convexity of `U'` (when `C²`). `U` is automatically `C²`
  (`= V - quadratic`). The potential-level reading is equivalent to the product-measure reading for these `V`, and the docstring says so.
  I checked by hand that the conclusion is true (`D²U(x)u = 0` by invariance, so `Hess V(z,z) = ρa² + D²U(w,w)` for `z=au+w`;
  `𝓛f = -⟨∇V,u⟩ = -ρ f` since `⟨∇U,u⟩=0`; `f ∈ L²` by the Gaussian marginal). Non-vacuity: `u = e₁`, `U = ρ/2|x⊥|²+c`.
* Deviations: (a) printed (R2) also asserts "all eigenfunctions of `λ₁` are affine"; not asserted here (only that the given linear
  function is an eigenfunction). Severity low: the fact belongs to the (R1)⇒(R2) direction/Theorem 3.1 (`euclidean_gaussian_factorization`),
  and the manuscript says only "(R2) gives (R1) immediately". (b) The other direction (R1)⇒(R2) is not in this statement
  (the item is named `(R2) ⇒ (R1)`). Neither affects fidelity of what is claimed.

## 3. Definitions `entropyOf`, `IsTestFunction`, `optimalPI`, `optimalLSI`

* Constants. Manuscript (`eq:LSI`, T:1139): `H(ν|μ) ≤ I(ν|μ)/(2ρ)`, `I = 4∫|∇√h|²`. With `f = √h`, `Ent(f²) ≤ (2/ρ)∫|∇f|²`, so LSI
  constant `2/ρ`, PI constant `1/ρ`, "twice". Lean: `Ent(f²) ≤ C∫|∇f|²` and `Var f ≤ C∫|∇f|²`: the factor 2 is exactly the
  manuscript's (`C_LSI = 2/ρ`), consistent with the Gaussian `N(0,1/ρ)` where Ent(e^{λs})=λ²σ²/2·E e^{λs}. Verified by hand
  (see §5), so the convention is not off by 2.
* `entropyOf μ g = ∫g log g - (∫g)log(∫g)`: correct for probability `μ`; `Real.log 0 = 0` is the right convention for `0 log 0`.
  For `g = f²`, `f` bounded: `g log g` bounded, integrable, no junk. If `μ` is not a probability measure the object is not Ent, but all
  statements assume `hp`.
* `IsTestFunction`: smooth, bounded, Lipschitz. The manuscript does not specify a class ("optimal constant"). Standard class is
  `H¹(μ)` or smooth functions. Our class contains `C_c^∞` and is contained in `H¹(μ)` (Lipschitz, bounded), so the Lean optimal constants
  are sandwiched between the `C_c^∞` and the `H¹` ones, which coincide (density + Bakry-Émery); the two theorems assert exactly
  the true values. For these `f` all integrals are of integrable functions (Lipschitz ⇒ `|∇f| ≤ L`, bounded) so `variance`, `∫`,
  `entropyOf` are meaningful, no junk.
* `optimalX = sInf {C | 0 ≤ C ∧ ∀ f test, ineq}`. Bounded below by 0 by the `0 ≤ C` clause (the clause is harmless: a negative `C` would
  require `Var f = 0` and `∫|∇f|² = 0` for all test `f`, false for `d>0` and nondegenerate `μ`). Empty set would give junk 0; this is
  excluded under the theorem hypotheses because the theorems equate the value to a strictly positive number (`1/λ₁ > 0`, `ρ⁻¹`), and a
  junk 0 would contradict; moreover both sets contain `1/λ₁`, `2/λ₁` by the (proved) inequalities. Conversely there is no way for a
  junk value to make the equalities hold.
* One loose point: for `d=0`, `optimalPI = sInf [0,∞) = 0` (all variances are 0), which is why `0<d` is needed in the extremal theorem (§5);
  in `optimal_lsi_twice_pi` `d=0` is excluded by `hR` (`0 < spectralGap` fails since `sInf ∅ = 0`).

## 4. `optimal_lsi_twice_pi`

Statement: `V ∈ C²`, `gibbs V` probability, `RigidCurvature V` (`λ₁>0`, `Hess V ≥ λ₁I`) ⊢ `optimalPI V = λ₁⁻¹ ∧ optimalLSI V = 2 optimalPI V`.
Manuscript T:808-818: "optimal PI constant is `1/λ₁`; rigidity implies optimal LSI = 2× optimal PI". Faithful: `RigidCurvature` is rigidity (curvature `≥ λ₁ > 0`
with equality of gap and curvature constant). `λ₁⁻¹` is not junk because `λ₁>0`. The manuscript statement is under `CD(ρ,∞)` with `ρ = λ₁`, same thing.
* `hB : IsStdBrownian B P` is an added hypothesis not used in the conclusion (`B,P` do not occur). It is an `∀ Ω B P` quantification, hence
  equivalent to the unconditional statement as long as one standard Brownian motion exists (true classically; Mathlib's `IsBrownianReal` is a
  genuine structure: finite-dimensional Gaussian laws and a.s. continuity). Residual risk: its existence is not proved in Lean (no instance of `Ω,B,P` in
  the project), so a reader must trust that `IsStdBrownian` is satisfiable. Not exploitable here, since the hypothesis is not contradictory by inspection. Harmless, flagged. Severity: remark.

## 5. `optimal_constants_extremal`

Statement: `hd: 0<d`, `ρ>0`, `W ∈ C²` convex, `W(x+s·𝟙)=W x`, `gibbs V` probability, `V = ρ|x|²/2+W` ⊢
`optimalPI V = ρ⁻¹`, `optimalLSI V = 2 optimalPI V`, `h = ∑xᵢ ∈ L²(μ)`, `Var h > 0`, `Var h = optimalPI·∫|∇h|²`, and for every `α`:
integrability of `e^{2αh}`, of `e^{2αh}log e^{2αh}`, of `|∇e^{αh}|²`, positivity of the energy for `α≠0`, and
`Ent(e^{2αh}) = optimalLSI·∫|∇e^{αh}|²`.
Manuscript T:821-825: in case (VW), `e^{αΣxᵢ}` is extremal for LSI, `Σxᵢ` for PI.
* Is "extremal" faithfully stated? Extremal = nonconstant function achieving equality in the inequality with the optimal constant. Lean states exactly
  equality with `optimalPI`/`optimalLSI`, plus non-triviality (`Var h > 0`; energy `> 0` for `α≠0`; `α=0` gives `f=1`, `0=0`, harmless and
  not claimed to be extremal) and finiteness of everything, so the equalities are not `0 = 0` or junk-integral artifacts. Hand check: `∇h = 𝟙`, `‖∇h‖² = d`,
  `Var h = d/ρ` (Gaussian marginal along `u=𝟙/√d`, `h=√d⟨u,x⟩`), `optimalPI=1/ρ`, so equality `d/ρ = (1/ρ)d` holds. For `f=e^{αh}`: `Ent(f²)=(2α²d/ρ)E[f²]`,
  `∫|∇f|² = α²d E[f²]`, with `optimalLSI = 2/ρ`: equality. Not an artifact of a wrong factor 2.
* Caveat (remark): `h` and `e^{αh}` are not in the bounded test class. Equality with the constants optimal on the bounded class is the right notion
  (the inequalities extend to `H¹(μ)` by truncation/density), but the statement does not itself assert that the inequality holds for these functions, so
  "extremal" (sup of the ratio attained) is derived with that standard extension, not formally stated. Low severity.
* Deviations: `W ∈ C²` (manuscript (VW) only says convex; Theorem 1.5 and the whole framework use `C²`; flagged in the Theorem 1.5 docstring
  but not in this docstring explicitly: "unflagged but inherited"); `0<d` (necessary: `d=0` gives `optimalPI=0≠ρ⁻¹` and `h=0`); `hB` (as above).
  `hp` normalization: `V` must contain the constant; non-vacuity: `W ≡ c` with `c = log ∫e^{-ρ|x|²/2}`.
* `MemLp h 2`, integrability are true for convex `W` (affine lower bound, Gaussian decay); not vacuous.

## 6. `pairwise_interaction`

`∑ i, ∑ j with i<j, h(xᵢ-xⱼ)` is `∑_{i<j}`. Convexity (composition with linear maps, sum of convex), diagonal invariance, `C²` preservation: true for all `d` including
`d ≤ 1` (empty sum, `W=0`). Evenness of `h` dropped (declared; stronger statement). Faithful. `ConvexOn ℝ univ h` is the right "convex `h:ℝ→ℝ`".

## 7. `ou_first_eigenspace`

`V = ρ|x|²/2+c`, `hp`, `0<d`: `λ₁=ρ`, `k₁=d`, `fᵢ=√ρ xᵢ` eigenfunctions, `∫fᵢfⱼ dμ=δᵢⱼ`. Manuscript: `λ₁=ρ`, `k₁=d`, `fᵢ=√ρ xᵢ`.
* `0<d` necessary (`spectralGap = sInf ∅ = 0` for `d=0`); with `d>0`, `firstEigenDim` is the `finrank` of a genuinely finite-dimensional space (junk 0 for infinite-dimensional
  would not equal `d>0`), so the value `d` is meaningful. Eigenfunction condition: `𝓛fᵢ = -ρ√ρ xᵢ = -ρ fᵢ` correct sign and eigenvalue.
  Orthonormality: covariance of `N(0,I/ρ)` is `I/ρ`, so `∫ρ xᵢxⱼ = δᵢⱼ`: correct. Orthonormal family of size `k₁=d` in `E₁` is a basis (as the docstring says).
* The constant `c` is determined by `hp` (as in the manuscript, where `μ=e^{-V}` is a probability). Faithful.

## 8. Unflagged deviations (summary)

None of consequence: (i) `W ∈ C²` in `optimal_constants_extremal` is not listed in its amendments (it is in Theorem 1.5); (ii) printed "all eigenfunctions affine" omitted in
`rigidity_of_gaussian_factor`; (iii) extremality asserted as equality with the bounded-class optimal constants (§5). Flagged amendments (`0<d`, `hB`, test class) are necessary (the `0<d` ones for
`sInf ∅` junk) and harmless.
