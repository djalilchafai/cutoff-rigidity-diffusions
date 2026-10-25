# Audit extra-C: statement fidelity of five Section 4 ("Further comments") theorems

Scope: `ou_fisher_information`, `normalization_cutoff`, `temperature_bakry_emery`, `temperature_cd`,
`heat_kernel_score` in `Challenge.lean` against `cutcur-lean.tex` lines 739-862. Statements and
definitions were read, not proofs. Shared definitions already analysed in `semantic-audit.md`
(`fisherInfo`, `HasCutoff`, `worst`, `mixingTime`, `IsLangevin`) were only re-checked where they
interact with these statements. Scratch files are in the scratchpad (`t.lean`, `t2.lean`).
No human review is claimed.

Summary: no defect found. Five verdicts, all "faithful" or "faithful with remarks". Remarks are
low severity and concern things the manuscript says in prose that are not formalized.

## 1. `ou_fisher_information` (tex 743-760, Lean 451-473): faithful with remarks

Does `IsLangevin` with the OU potential pin down the law and `c`? Yes.
- `IsLangevin` gives `V` C², `gibbs V` a probability measure, `B` a standard Brownian motion, and
  for every `x₀` an a.s. continuous path satisfying the integral equation. For
  `V = ρ|x|²/2 + c`, `∇V = ρx`, so the equation is linear with the pathwise-unique solution
  `X_t = e^{-ρt}x₀ + √2 ∫₀ᵗ e^{-ρ(t-s)} dB_s`. Its covariance is
  `2∫₀ᵗ e^{-2ρ(t-s)} ds = (1-e^{-2ρt})/ρ`, matching the claimed Mehler law.
- Continuity makes the drift integral a genuine Lebesgue integral, so the `0` junk value for
  non-integrable integrands cannot be triggered.
- `c` is forced by `IsProbabilityMeasure (gibbs V)` (`c = (d/2) log(2π/ρ)`). `c` is a free
  variable constrained by the hypothesis, so the statement is not vacuous in `c`. For `d = 0` the
  constraint gives `c = 0`, still consistent.
- `P.map` is `0` for a non-AEMeasurable map. Here `X_t` is a.s. equal to a measurable functional
  of `B`, and the conclusion asserts the law equals a probability measure, so this is not an issue.

Hand check of the formulas (all agree with the Lean statement and the manuscript):
- Mehler: mean `e^{-ρt}x₀`, covariance `s·I` with `s = (1-e^{-2ρt})/ρ`. The Lean
  `multivariateGaussian m (s • 1)` with `s > 0` has a PSD matrix (checked in scratch), so the
  "not PSD gives Dirac" junk branch of Mathlib's `multivariateGaussian` is not triggered. For
  `t > 0`, `t.toNNReal = t`.
- `∇u = a_t x + b_t x₀` with `a_t = ρ - ρ/D` and `b_t = ρ e^{-ρt}/D`, `D = 1 - e^{-2ρt}`. This
  equals `-ρ(x - e^{-ρt}x₀)/D + ρx`, as in the manuscript. These are explicit and involve neither
  `d` nor `x₀`, so the "do not depend on d, x₀" claim is encoded by the formulas themselves.
- Fisher: under `μt`, `|∇u|²` has mean `ρ² e^{-2ρt}|x₀|²` (since
  `a e^{-ρt} + b = ρ e^{-ρt}`) plus `a² s d = ρ d e^{-4ρt}/D`. This matches the Lean right-hand
  side. `4∫|∇√h|² dμ = ∫|∇log h|² h dμ` holds for this smooth positive `h`.
- `ENNReal.ofReal` of the right-hand side is exact because the argument is `≥ 0`
  (`ρ > 0`, `D > 0`).
- `fisherInfo` junk: the `⨅` is over `G` with `ν ≪ μ` and a weak-gradient identity. Here the
  gradient is the true one and `fisherInfo V μt` is finite. The identity is written against
  Lebesgue measure (a distributional gradient). It is equivalent to the `μ`-weighted version since
  `e^{-V}` is positive and locally bounded, and `√h ∈ L²(μ)`, so `√h` is locally `L²`. This is a
  property of the already-audited definition, not new.
- The conjuncts `∃ u, ContDiff u ∧ μt = (gibbs V).withDensity (ofReal ∘ exp ∘ u) ∧
  (u = log (rnDeriv).toReal a.e.)` are consistent. The last conjunct ties `u` to the genuine
  Radon-Nikodym derivative, so the `ofReal` truncation is harmless (`exp u > 0`).

Remarks (low severity):
- The manuscript's claim "`a_t, b_t` do not depend on `d`" is not stated as a separate
  quantifier, only through the explicit closed forms. This is stronger and fine.
- The theorem is stated for all `t > 0` and all `x₀`, as in the manuscript.
- `ρ > 0` is added, but the manuscript's OU process presupposes it. Not flagged in the docstring,
  but implicit in "`V = ρ|x|²/2`".

## 2. `normalization_cutoff` (tex 826-836, Lean 475-497): faithful with remarks

Time change. `Xα n x₀ u = X n x₀ ((α n).toNNReal * u)`. For `α n > 0` and any real `s ≥ 0`,
`(α.toNNReal * s.toNNReal : ℝ≥0) = (α s).toNNReal` (`toNNReal_mul` with nonneg first factor), so
`worst (Xα) s = worst X (α s)` for `s ≥ 0`. Negative `s` gives `toNNReal = 0` on both sides
consistently (`α s < 0`), so no mismatch.

- Part 1 (cutoff iff cutoff at `t/α`): `profile'((1∓ε) t/α) = profile((1∓ε) t)` exactly. So the
  iff holds with the same limits `b`, `a`, for every `δ`, `t`, `S`. The statement is
  quantified over arbitrary `δ`, `t`, `b`, `a`, with no Langevin hypothesis. This is strictly more
  general than the manuscript and correct, since it is a pure reparametrization.
- Part 2 (mixing time `= t₀/α`): the set `{t : worst Xα t ≤ ofReal η}` equals
  `{s/α : worst X s ≤ ofReal η}`, and the `⨅` scales. The empty case gives `⊤ / ofReal α = ⊤`
  (consistent). `ENNReal.ofReal (α n)` is nonzero and finite for `α n > 0`, so `/` has no junk.
  The manuscript does not state the mixing-time scaling explicitly, so this is an addition
  needed for the product-condition clause.
- Part 3 (product condition): `α κ (t₀/α).toReal = κ t₀.toReal` as sequences when `t₀ < ⊤`. When
  `t₀ = ⊤` both `toReal` give `0`, so both products are `0`. So the two sequences are literally
  equal and the equivalence is a (correct) tautology.

Reading of "κ becomes ακ": the statement treats `κ` as an arbitrary real sequence. It does
not tie `ακ` to the curvature constant of `α𝓛` (i.e. `Hess(αV) ≥ ακ` or `CD(ακ)`). The "κ
becomes ακ" reading is therefore the arithmetic of the product and not a statement about the
generator. This is a faithful rendering of "the product condition is invariant" but does not
formalize "κ is the curvature of the scaled generator". Severity low, informational.

Not formalized (low): the manuscript sentence "`X^{(α)}` solves `dX = -α∇V dt + √(2α) dB` and has
generator `α𝓛`", and the "such scaled processes play a role with respect to mean-field limits"
comment. The Lean statement is only about cutoff, mixing time and the product condition.

## 3. `temperature_bakry_emery` (tex 838-860, Lean 499-522): faithful with remarks

- `L f = σ² laplacian f - ⟨∇V, ∇f⟩`: the right generator `σ²Δ - ∇V·∇`. `laplacian` is
  `∑ᵢ D²f(eᵢ,eᵢ)` with `eᵢ` the standard basis, correct. `gradient` is Mathlib's Riesz gradient,
  correct for `Differentiable f`. All functions here are `C^∞` (`hV`, and `f` is `C^∞` in (i) and (iii)),
  so no derivative junk is hit.
- `Γ(f,g) = σ²⟨∇f,∇g⟩`; `Γ₂ f = L(Γ f f)/2 - Γ f (L f)` is the standard `½LΓ(f,f) - Γ(f,Lf)`.
  Hand check: `Γ = σ²Γ⁰`, `L = σ²L₁` with `L₁ = Δ - ∇(V/σ²)·∇`, so `Γ₂ = σ⁴Γ₂^{(1)}`
  `= σ⁴(‖Hess f‖² + Hess(V/σ²)(∇f,∇f)) = σ⁴‖Hess f‖²_HS + σ²Hess V(∇f,∇f)`. This is exactly the
  manuscript's and the Lean formula. The HS norm `∑ᵢⱼ (D²f(eᵢ,eⱼ))²` is the Frobenius norm in an
  orthonormal basis.
- (ii) invariance as `∫ L f d(gibbs (V/σ²)) = 0` for `C²` compactly supported `f`: `Lf` is
  continuous and compactly supported, so the integral is a true integral. `gibbs` is the
  unnormalized `e^{-V/σ²}dx`, which is the same condition as with the normalized `Z_σ⁻¹e^{-V/σ²}`
  (and also meaningful when `Z_σ = ∞`). This is the standard weak (core) meaning of "`μ_σ` is
  invariant for `L_σ`"; it does not assert invariance of the process `Y^{(σ)}` (which needs
  non-explosion / essential self-adjointness), and the process `Y^{(σ)}` itself is not formalized.
  Low severity, in line with how invariance is treated elsewhere in the project.
- (iii): quantified over all real `ρ` (the manuscript says `ρ > 0`), which is stronger and true
  (`⇐`: `σ⁴‖Hess‖² ≥ 0`; `⇒`: take the linear `f = ⟨z,·⟩`, `Hess f = 0`, `∇f = z`). The
  right-hand side is the pointwise quadratic form `Hess V(x)(z,z) ≥ ρ|z|²` for every `x`, `z`,
  with no `σ`, as the manuscript says. The manuscript's "CD(ρ,∞) of `𝓛`" is ambiguous (`σ = 1` versus
  `L_σ`); the Lean version uses `L_σ`, which is the intended reading.
- Not formalized (low): "in particular, in the rigid case the cutoff critical time is free of σ".
  It is a consequence stated in prose only.
- `0 < d` is not needed and not assumed. For `d = 0` all statements are trivial.

## 4. `temperature_cd` (tex 858-860, Lean 743-752): faithful with remarks

The statement `CD (Rd d) (ρ/σ²) (V/σ²) ↔ Hess V ≥ ρ` formalizes "use `α = σ²` and `V/σ²`
instead of `V`": `CD(ρ/σ²,∞)` for the unit generator `Δ - ∇(V/σ²)·∇` is
`‖Hess f‖² + Hess(V)/σ² (∇f,∇f) ≥ (ρ/σ²)|∇f|²` for all smooth `f`, equivalent to
`Hess V ≥ ρ`. This is consistent with `temperature_bakry_emery` (iii).

Instance argument (checked in `t.lean`):
- `IsContMDiffRiemannianBundle 𝓘(ℝ, Rd d) ∞ (Rd d) (fun x => TangentSpace 𝓘(ℝ, Rd d) x)` is a
  `Prop` class, and `example (d) : ... := inferInstance` succeeds, so the hypothesis holds for
  every `d` (no error). Hence the instance argument is redundant and the theorem is equivalent to
  the unconditional statement; it is not a hidden or contradictory hypothesis.
- The `RiemannianBundle` instance used is Mathlib's canonical
  `instRiemannianBundleTangentSpaceRealModelWithCornersSelf` (found by `#synth`), i.e. the
  standard Euclidean metric on `TangentSpace 𝓘(ℝ,E) x = E`. The tangent inner product is
  definitionally the `Rd d` inner product (`rfl` checked in `t2.lean`). `IsManifold 𝓘(ℝ,Rd d) ∞
  (Rd d)` is also found. So `CD (Rd d)` is the Euclidean `CD`, built from Mathlib's
  `mgrad` (Riesz gradient of `mvfderiv`), `mlaplacian` (trace of the Levi-Civita covariant
  derivative of the gradient) and `carre2 = ½ L Γ - Γ(f, L f)`. On flat space these coincide with
  the Euclidean objects; the (proved) equivalence to the Hessian condition for every `V`, `ρ`
  confirms it is not degenerate (both sides vary with `ρ`; e.g. `V = |x|²/2` gives true for
  `ρ ≤ 1` and false for `ρ > 1`).
- `CD` quantifies over `ContMDiff ∞ f` (smooth `f` on the manifold) which on `Rd d` equals
  `ContDiff ∞`; `V` is required `ContDiff ∞` by `hV`, so no junk derivatives.
- Remark: the quantifier is over all real `ρ`, versus manuscript `ρ > 0`: stronger and true.
- Remark (cosmetic): since the instance is global and unique, the explicit instance binder only
  shadows it; because both are proofs of the same Prop, there is no semantic effect.

## 5. `heat_kernel_score` (tex 762-769, Lean 524-532): faithful with remarks

- Generalization: `p` is an arbitrary positive continuous differentiable function, not
  necessarily a probability density (hence `ν` need not be a probability measure), and `V` is
  arbitrary continuous differentiable. This subsumes `p_{t,x₀}` and `μ_t`. The manuscript's `p_{t,x₀}`
  is positive for `t > 0`, and differentiability in `x` holds, so the instance is covered.
- `ν ≪ gibbs V`: true, since `ofReal (exp (-V))` is strictly positive everywhere, so `gibbs V`
  and Lebesgue measure are mutually absolutely continuous. `ν` and `gibbs V` are σ-finite
  (continuous, locally finite densities), so `rnDeriv` is `p e^{V}` a.e. and finite a.e.
  There is no `toReal ⊤` junk a.e. (and `rnDeriv > 0` a.e., so `log` is not on `0`). The
  `∀ᵐ x ∂gibbs V` is the right null set.
- Weak spot (low): `u` is existentially quantified with only an a.e. link to
  `log rnDeriv`, and the gradient identity is demanded at all `x`. The statement does not itself
  assert `Differentiable ℝ u`. If `u` were not differentiable at some `x`, `gradient u x = 0`
  (Mathlib junk) and the identity would have to hold with `∇log p + ∇V = 0` there. This is not
  exploitable (the witness is `u = log p + V`, and any other witness satisfying the identity at all
  points differs from it only on a null set and also satisfies the identity), but adding
  `Differentiable ℝ u` (or a `ContDiff` clause as in `ou_fisher_information`) would remove the
  junk reading. The identity itself is the trivial calculus fact `log(p e^{V}) = log p + V`;
  this is what the manuscript says.
- `hVc`, `hpc` are redundant given `hVd`, `hpd` (differentiable implies continuous); harmless.
  `0 < d` is not needed.
- `ν` is `volume.withDensity (ofReal ∘ p)`, matching "density `p` with respect to Lebesgue".

## Overall

No unflagged hypothesis addition that makes a conclusion trivial, no vacuity (the only
non-obvious inhabitation, the Brownian carrier in `ou_fisher_information`, is the same one used
by the original theorems; `temperature_cd`'s instance was confirmed inhabited). Items to consider
(all optional): (a) add `Differentiable ℝ u` to `heat_kernel_score`; (b) note in
`normalization_cutoff`'s docstring that `κ ↦ ακ` is only arithmetic and the SDE/generator
statement for `X^{(α)}` is not formalized; (c) note that invariance in `temperature_bakry_emery`
(ii) is the weak/core form and `ρ` ranges over all reals.
