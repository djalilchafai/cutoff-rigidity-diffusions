# Audit N (adversarial, statements only): round-2 statements nos. 58-67, the equality versions 51-52, and the `C²` clause

Method: I read the Lean statements and definitions in `Challenge.lean` and compared them with `cutcur-lean.tex` (text of arXiv:2412.15969v5).
I did not read proofs to judge fidelity. I wrote one scratch file outside the repo, `AuditN.lean`, which imports `Solution`. It compiled with `lake env lean` and checks the following:
(a) the concrete round sphere `Sph d` of `Extra/Sphere5-6` satisfies `CutCur.IsSphereModel`, and `sphere_gap` and `sphere_curvature` instantiate on it (with `exists_isWeightedVolume` and `connectedSpace`);
(b) `@[pp.explicit] #print IsSphereModel`: the inner product on `TangentSpace` is `Bundle.instInnerProductSpaceReal`, i.e. the `RiemannianBundle` metric, not the model-space inner product of `F`;
(c) `gibbs_quadratic_isProb` discharges `hV`/`hp` of the isoperimetric statements;
(d) `temperature_kernel` with `σ = 1` yields `∃ Pt, IsEuclideanLangevin V Pt` for every `C²` `V` with `Hess V ≥ ρ > 0` and probability Gibbs measure (a non-vacuity witness for the `C²` kernel hypothesis, inside the Challenge);
(e) `#check CutoffRigidity.Rothaus.finite_compact`: `Form.Compact` holds for finite irreducible forms (Extra, not a Challenge statement).
I edited no repo file except this report. (A concurrent `lake build` from another session was running during the audit; I did not start one.)

Notation: T = manuscript line, C = `Challenge.lean` line.

## 1. `dyson_spectralGap` with `dysonGap` (no. 58). Verdict: FAITHFUL, with a documented choice (Neumann form)
- T321-333: for `h(x) = -β log x` (`+∞` for `x ≤ 0`), `β ≥ 0`, the process lives on the convex chamber, and "`x₁+⋯+x_d` is an eigenfunction associated to the spectral gap". The gap equals `ρ` by Thm 1.5's argument.
- C638-647: `dysonGap` is the Rayleigh infimum over `C_c^∞(ℝ^d)` (not over `C_c^∞(chamber)`) against `dysonProb`. Conclusion: `dysonGap = ρ` and an explicit `C_c^∞` sequence with positive variance converging to `h = ∑ xᵢ` in `L²(μ)` and in gradient `L²(μ)`.
- Junk: none. For `d ≥ 1` the Rayleigh set is nonempty, it is bounded below by 0, and every variance and integral involves bounded compactly supported functions. If the set were empty, `sInf = 0 ≠ ρ`, so the junk value could only make the statement false, never vacuous.
  The two `Tendsto … (𝓝 0)` integrals cannot be satisfied by Bochner junk 0: `(fₙ - h)²` and `‖∇fₙ - ∇h‖²` are integrable because `fₙ` is bounded with compact support, `h ∈ L²(μ)` (shown in `dyson_ou_static`) and `∇h` is constant.
- Truth check: `μ` is the restriction of a `ρ`-log-concave density to an open convex set, so the Neumann Poincaré constant is `≤ 1/ρ` (Bakry–Émery on convex domains). `h` gives `≥`. For `d = 1` the chamber is all of `ℝ` and `μ = 𝒩(0, 1/ρ)`.
- REMARK (scope): this is the Neumann (reflected) gap. For `0 < β < 1` it could differ from the Dirichlet-type gap built on `C_c^∞(chamber)`, because `h` does not vanish on the walls. The manuscript's "process on the convex domain" supports the Neumann reading, and the docstring of `dysonGap` states the choice ("test functions are not required to vanish on the walls"). Honest.
- Together with `dyson_ou_static` (`𝓛h = -ρh` on the chamber, weak Neumann equation, `Var h = ρ⁻¹∫|∇h|²`), this covers the manuscript claim. The docstring correctly does not claim the Dyson–OU process.

## 2. Gaussian isoperimetry, nos. 59-61. Verdict: FAITHFUL WITH DOCUMENTED RESTRICTION (quadratic potential only)
- T629-632: in the Riemannian `CD(ρ,∞)` setting, "the Bakry–Émery approach implies … a Gaussian isoperimetric inequality". There is no precise statement.
- `gaussianIsoProfile` (C333-334): `φ(Φ⁻¹(u))` on `(0,1)`, `0` elsewhere, with `Φ⁻¹(u) = sInf {x | u ≤ Φ x}`.
  For `u ∈ (0,1)` the set is a nonempty closed half-line `[Φ⁻¹u, ∞)` (cdf monotone and right-continuous, limits 0 and 1), so `sInf` is the genuine quantile. The value `0` at `u ∈ {0,1}` is the true `I(0) = I(1) = 0`.
  `gaussianPDFReal 0 1` is the standard density, and `I` is continuous on `[0,1]`, so `I ∘ f` is measurable. No junk.
- `gaussian_isoperimetric_functional` (C336-340): `I(∫f dμ) ≤ ∫ √(I(f)² + ρ⁻¹|∇f|²) dμ` for `f` smooth, bounded and Lipschitz with values in `[0,1]`, and `μ = e^{-V}`, `V = ρ|x|²/2 + c`, a probability measure.
  This is Bobkov's inequality for `𝒩(0, ρ⁻¹I)`; the scaling `x = y/√ρ` gives exactly `ρ⁻¹|∇f|²`, and it is also the Bakry–Ledoux form under `CD(ρ,∞)`. The integrand is bounded (`I ≤ (2π)^{-1/2}`, `|∇f| ≤ L`), so the right side is not junk.
- `gaussian_isoperimetric_sets` (C342-346): `μ(A) ≥ Φ(a) ⇒ μ(A_r) ≥ Φ(a + √ρ r)` with `A_r = cthickening r A`, `r ≥ 0`, for an ARBITRARY (possibly non-measurable) `A`. With `μ.real` this is the outer measure.
  It is still true: `μ*(A) ≤ μ(cl A)` and `cthickening r A = cthickening r (cl A)`, so the closed-set case suffices. The constant `√ρ` is correct for `𝒩(0, ρ⁻¹I)`. Edge cases `r = 0` and `d = 0` are true.
- `gibbs_quadratic_isProb` (C348-350): `∫ e^{-ρ|x|²/2} dx = (2π/ρ)^{d/2}`, so `c = (d/2) log(2π/ρ)` is correct. It makes `hV ∧ hp` jointly satisfiable (checked in (c)). Since `hp` forces this value of `c`, the hypotheses describe exactly the centred Gaussian `𝒩(0, ρ⁻¹ I_d)`.
- Docstrings: both statements say "QUADRATIC CASE ONLY", and that the general `Hess V ≥ ρ` case is NOT formalized. HUMAN_REVIEW_SUMMARY §3 and §5 and `formalization.yaml` say the same. No overclaim.
  Minor imprecision: the functional docstring calls `V = ρ|x|²/2 + c` "the equality case of `CD(ρ,∞)`". On `ℝ^d` the equality case `Hess V = ρI` is `ρ|x-m|²/2 + c` for any centre `m`, and Lean covers only `m = 0` (the general `m` follows by translation, so this is cosmetic). The manuscript's remark is Riemannian; the Lean statements are Euclidean only. The docstring could say "centred Gaussian on ℝ^d".

## 3. Rothaus, nos. 62-64 (`Form`, `optPI`, `optLSI`, `Compact`). Verdict: FAITHFUL WITH DOCUMENTED RESTRICTION (abstract and finite only); one minor docstring inaccuracy
- T816-821: "in the compact setting, if the optimal LSI constant is not twice the optimal PI constant, then there exists an extremal function for LSI", citing Rothaus, plus Saloff-Coste Th. 2.2.3 for a discrete version.
- `Form` (C352-363) requires `Q` closed under scalar multiplication and adding constants, `E ≥ 0`, `E(cf) = c²E(f)`, `E(f + c) = E(f)`, `Q ⊆ L²`, and `f² log(1+f²) ∈ L¹`.
  It does NOT require `Q` to be closed under addition, or `E` to be a quadratic form (no parallelogram law or bilinearity). The theorems therefore hold for a strictly larger class, so the theorems lose nothing.
  But the docstring "`E ≥ 0` the energy, quadratic and …" over-describes the hypotheses: `E` is only 2-homogeneous. DOCSTRING FIX (minor).
- `optPI`/`optLSI` (C365, C368): `sInf` of `{C ≥ 0 | …}`. The junk value 0 arises only when the set is empty.
  In `rothaus_alternative_ne`, `hPI` and `hLSI` make both sets nonempty. In `two_optPI_le_optLSI`, an empty PI set gives `optPI = 0` and a trivially true conclusion, but linearization `f = 1 + εg` (allowed by `smul_mem` and `add_const_mem`) makes it nonempty anyway. In `finite_rothaus`, if the LSI set were empty, `hgt` would be false, which makes that case vacuous rather than misleading. For finite irreducible forms both sets are nonempty.
- `Form.Compact` (C370-375): mean-zero bounded-energy sequences in `Q` have a subsequence converging in `L²` and in the Orlicz weight `f² log(1+f²)` to some `h ∈ Q`, with `E h ≤` every eventual bound. That is `E h ≤ limsup`, weaker than lower semicontinuity.
  It is not contradictory: `finite_compact` (Extra/Rothaus15, (e)) proves it for finite irreducible forms. It is the right analytic input for `H¹` of a compact manifold (Poincaré bound, Rellich, `H¹ ⊂ L^{2+δ}` gives `L² log L` convergence, weak lower semicontinuity).
- `rothaus_alternative_ne` (C377-381): `optLSI ≠ 2 optPI ⇒ ∃ f ∈ Q, E f > 0 ∧ Ent(f²) = optLSI · E f`.
  `E f > 0` forces `f` non-constant (constants have `E = 0` from `E_smul` and `E_add_const`). The equation rules out `optLSI = 0`: by no. 63, `optLSI = 0` would force `optPI = 0` and contradict `hne`. So the extremal is genuine.
  Non-vacuity: a finite asymmetric two-point form has `optLSI > 2 optPI` (Diaconis–Saloff-Coste) and satisfies `Compact` (Extra). There is no Lean witness inside the Challenge for the combined hypotheses. Remark only.
- `two_optPI_le_optLSI` (C383-386): the standard linearization inequality. True. Docstring accurate.
- `finite_rothaus` (C388-392) matches Saloff-Coste Th. 2.2.3: `α < λ/2 ⇔ 1/α > 2/λ ⇔ optLSI > 2 optPI`, and `Ent(f²)` is his `L(f)`.
  Its weights `w ≥ 0` are arbitrary and not tied to `π` (no reversibility). The form only sees the symmetrization of `w`, and a positive rescaling of `E` multiplies `optPI` and `optLSI` by the same factor. So this generality is harmless, and the result is at least Saloff-Coste's.
  Quantifying over any `F : Form μ` with `hQ`/`hE` is equivalent to the statement for the canonical form: a `Form` is determined by `(Q, E)` (the remaining fields are proofs), and such an `F` exists (`finiteForm`, Extra).
  `|X| = 1` makes `hgt` false. A two-point asymmetric space makes it true.
- Docstrings: "ABSTRACT form", "The compact-manifold theorem … is NOT proved", "the finite case below is unconditional". Honest, and consistent with HUMAN_REVIEW_SUMMARY §3 and §5 and `formalization.yaml`.

## 4. `temperature_kernel` (no. 65). Verdict: FAITHFUL WITH DOCUMENTED RESTRICTION (`Hess V ≥ ρ > 0` added)
- T838-858: the `σ`-diffusion `dY = -∇V dt + √(2σ²) dB` has invariant law `Z_σ⁻¹ e^{-V/σ²}` and generator `σ²Δ - ∇V·∇`, and is the time change via `α = σ²` and `V/σ²`.
- C471-477 claims four things: existence of an `IsSigmaLangevin V σ Pt`; for every such `Pt`, Gibbs invariance; and `Pt t x = Q(σ²t) x` for every `IsEuclideanLangevin (V/σ²) Q`, hence uniqueness.
  The time change is correct: the generator of `Q(σ²·)` is `σ²(Δ - ∇(V/σ²)·∇) = σ²Δ - ∇V·∇`. `(σ²).toNNReal` has no truncation since `σ² ≥ 0`.
- Hypotheses: `C²` (as in the manuscript, T92); `hp` normalizes `Z_σ = 1`, the same convention as `temperature_sde`; `Hess V ≥ ρ > 0` is ADDED and is flagged in the docstring and in HUMAN_REVIEW_SUMMARY.
  The manuscript's standing assumption is "strictly convex, `V → ∞`" (T92), which is weaker than uniform convexity. The restriction is a genuine scope loss, but it is honestly flagged.
- Non-vacuous: `V = σ²(|x|²/2 + (d/2)log 2π)`. As a by-product, `σ = 1` gives a Challenge-internal witness for `IsEuclideanLangevin` (check (d)).

## 5. Sphere, nos. 66-67 (`IsSphereModel`, `sphere_curvature`, `sphere_gap`). Verdict: FAITHFUL WITH DOCUMENTED RESTRICTION (model form)
- T709-712: "For the `d`-dimensional unit sphere, we have `ρ = d-1` and `λ₁ = d`, so the abstract theorem does not apply."
- `IsSphereModel` (C784-786): `‖Φ‖ = 1`, `Φ` smooth, and `⟨v,w⟩_{g_x} = ⟨dΦ v, dΦ w⟩_E`.
  Check (b) confirms that the left-hand inner product is the `RiemannianBundle` metric (`Bundle.instInnerProductSpaceReal`; `TangentSpace` is irreducible and has no other `Inner` instance), so the definition pulls back exactly the Riemannian inner product. It is identical to `Extra/Item6a.IsIsometricSphereMap`.
- `sphere_curvature` (C837-841) quantifies over every `M^d` with `finrank F = d` and such a `Φ` into `S^d ⊂ ℝ^{d+1}`. Such an `M` is a local isometry onto an open subset of `S^d`.
  The section variables add `IsRiemannianManifold`, `ConnectedSpace` and `CompleteSpace`, which the docstring does not mention. They are harmless standing hypotheses.
  All three conjuncts are true for every `d`:
  - `Ric = (d-1)g`. For `d = 0` both sides are 0.
  - `CD(d-1)` for constant potentials.
  - The optimality clause, for `d ≥ 1` and `M` nonempty: take `f` with `Hess f(x) = 0` and `∇f(x) ≠ 0`, e.g. a linear function in normal coordinates times a bump.
- `sphere_gap` (C843-846): compact, `d ≥ 2`, `μ = e^{-c} vol` a probability measure, conclusion `λ₁ = d`. True, since a compact connected complete `M^d` locally isometric to `S^d` with `d ≥ 2` is `S^d`.
  `d ≥ 2` is needed: a `k`-fold circle cover is an isometric immersion into `S¹` with `λ₁ = 1/k²`. `mSpectralGap` is not `sInf ∅`.
- Non-vacuity: check (a) instantiates both theorems on the concrete `Sph d`. So the model-form statements genuinely apply to the round sphere, although the concrete sphere itself is not a Challenge object (as the docstring says).
- Docstrings: `sphere_gap`'s remark that the sphere is NOT a witness of `hgap` (`d ≠ d-1`) is correct and matches T711. No overclaim.

## 6. `langevin_dissipation_eq_K'` and `langevin_dissipation_eq_dirac_K` (nos. 51-52, equality). Verdict: FAITHFUL (remarks)
- T1149-1167: `∂ₜH = -I`, and eq. HI: `H(μ_{t₀}) - H(μ_{t₁}) = ∫_{t₀}^{t₁} I(μ_s) ds` for `0 < t₀ < t₁`, with `μ₀` Dirac.
- `eq_K'` (C593-599): for any initial law `ν`, `H(ν_a) < ∞` with `a < s < t` gives `∫_{(s,t]} I + H(t) = H(s)` in `ℝ≥0∞`.
  Since `H` is nonincreasing, `H(s) < ∞`, so there is no `∞ = ∞` triviality and no subtraction. `r > s ≥ 0`, so `toNNReal` does not truncate. `r ↦ I(μ_r)` is monotone (`langevin_fisher_decay`), hence measurable, so the lower-integral issue does not arise.
  The identity is the energy-dissipation equality for the Wasserstein gradient flow of a `ρ`-convex entropy, which is true from any finite-entropy time `s > 0`.
- `eq_dirac_K` (C601-604): `0 < s < t`, with no finiteness hypothesis. `H(P_s x₀) < ∞` for `s > 0` by regularization, so the identity is non-trivial. This is exactly T1163 with `μ₀ = δ_{x₀}`.
- REMARKS:
  - `eq_K'` does not cover `s = 0` even when `H(ν) < ∞`, because it requires `a < s`. The manuscript uses only `t₀ > 0`, so nothing used is lost.
  - `ρ > 0` is assumed where `ρ ≥ 0` would do. Harmless.
  - The extension to arbitrary `ν` goes beyond the manuscript, a strengthening.
  - The docstrings are accurate. Formalization.yaml's "same hypotheses" is correct.

## 7. The `C²` clause (`IsEuclideanLangevin` C80-82, `IsSigmaLangevin` C416-418, `IsRigidSequenceK` C151-153, `W n` in `convex_interaction_cutoff` C196-208). Verdict: FAITHFUL; convexity visible everywhere; not vacuous
- The manuscript's standing assumption is "`V` strictly convex and `C²`" (T92). `C²` is therefore now the printed regularity, and the former `C^∞` amendment is gone. Weakening a hypothesis can only strengthen a theorem; every conclusion is unchanged.
  The audit-M remark on `isLangevinSolution_map_eq_kernel_of_rigid` (missing "`C^∞`" flag) is now moot.
- Convexity check: I enumerated every Challenge statement that uses one of the three predicates. There are 24: the 23 changed ones plus the new `temperature_kernel`. Each carries an explicit convexity hypothesis.
  - `RigidCurvature`, which contains `Hess V ≥ λ₁ > 0`: nos. 49, 1, 10 and Remarks 3.4.
  - `IsRigidSequenceK`, which includes `RigidCurvature`: Cor 1.3, 1.4, (1.25), Remark 3.5 and the three mixing-time statements.
  - `W n` convex plus `ρ|x|²/2`: Cor 1.6.
  - `κ n > 0` Hessian bound: Thm 1.7.
  - Quadratic `V`: `ou_fisher_information`, `ou_mean_start_cutoff`, `ou_lp_infty_fails`.
  - `hHess` with `ρₙ > 0`: `temperature_cutoff`.
  - `hHess` with `ρ > 0`: `temperature_kernel`.
  - `hHess` with `ρ ≥ 0`: `langevin_w2_contraction`.
  - `hHess` with `ρ > 0`: entropy decay, Fisher decay, Dini, and the two dissipation identities.
  - `normalization_cutoff` is generic in `Pt` and uses none of the predicates.
  No statement silently relies on uniqueness for nonconvex `C²` `V`.
- Well-posedness with `V ∈ C²`: `generator V f` for `f ∈ C_c^∞` needs only `∇V` continuous, and `RigidCurvature` uses the genuine second derivative. No junk is introduced.
- Non-vacuity: check (d) derives `∃ Pt, IsEuclideanLangevin V Pt` from `temperature_kernel` at `σ = 1` for every strongly convex `C²` `V`, which covers every hypothesis family above. Before this, the only satisfiability evidence was outside the Challenge (`exists_euclideanLangevin_C2`).
- REMARK (inherited, not new): the docstring of `IsEuclideanDiffusion` says that uniqueness under convexity makes `Pt` "the law of the SDE (1.1) solution". Inside the Challenge, the link kernel = SDE law is stated only under `RigidCurvature` (no. 49). For merely (strongly) convex `V` it relies on non-Challenge facts (Itô/Dynkin for the SDE law plus `euclideanDiffusion_unique_convex`).

## Summary table
| no. | statement | verdict |
|---|---|---|
| 58 | `dyson_spectralGap` (+`dysonGap`) | faithful (Neumann gap, documented) |
| 59 | `gaussian_isoperimetric_functional` (+`gaussianIsoProfile`) | faithful with documented restriction (centred quadratic `V`, ℝ^d) |
| 60 | `gaussian_isoperimetric_sets` | faithful with documented restriction (same) |
| 61 | `gibbs_quadratic_isProb` | faithful (correct normalization) |
| 62 | `rothaus_alternative_ne` (+`Form`, `optPI`, `optLSI`, `Compact`) | faithful with documented restriction (abstract, `Compact` hypothesis) |
| 63 | `two_optPI_le_optLSI` | faithful |
| 64 | `finite_rothaus` | faithful (unconditional discrete version; generality in `w` harmless) |
| 65 | `temperature_kernel` | faithful with documented restriction (`Hess V ≥ ρ > 0` added) |
| 66 | `sphere_curvature` (+`IsSphereModel`) | faithful with documented restriction (model form; witnessed by `Sph d`) |
| 67 | `sphere_gap` | faithful with documented restriction (same) |
| 51 | `langevin_dissipation_eq_K'` | faithful (s > 0 only; manuscript needs only that) |
| 52 | `langevin_dissipation_eq_dirac_K` | faithful |
| — | `C²` clause in 23 (+1) statements | faithful; convexity explicit in all; non-vacuous (via `temperature_kernel`, σ = 1) |

## Defects
No defect. No statement is false, vacuous, junk-valued or unfaithful beyond what its docstring flags.

## Recommended docstring fixes (minor)
1. `Form`: replace "quadratic" with "2-homogeneous (`E(cf) = c²E(f)`), not necessarily a quadratic form; `Q` need not be closed under addition".
2. `gaussian_isoperimetric_functional`/`_sets`: say "centred Gaussian `𝒩(0, ρ⁻¹I_d)` on `ℝ^d`" rather than "the equality case of `CD(ρ,∞)`". The manuscript remark is Riemannian, and the equality case on `ℝ^d` allows any centre `m`.
3. `temperature_cutoff`: "amendment: `Vₙ` is `C²`" is stale, since `C²` is the manuscript's own assumption (T92). Reword it to "(as in the manuscript)".
4. `IsEuclideanLangevin`: the satisfiability pointer could cite the Challenge-internal witness `temperature_kernel` (σ = 1) in addition to the non-Challenge `exists_euclideanLangevin_C2`. `exists_langevin` concerns `IsLangevin`, not the kernel predicate.
5. `sphere_curvature`/`sphere_gap`: mention that `M` is also assumed connected and complete (section variables).
6. Optional: in `dysonGap`, note that this is the Neumann gap, which may differ from the gap of `C_c^∞(chamber)` for `0 < β < 1`.
7. Out of scope, cosmetic: the `Challenge.lean` header says "based on arXiv:2412.15969v4", while `Solution.lean` and the task say v5.
