# Human review summary for the authors (draft)

Repository: https://github.com/djalilchafai/cutoff-rigidity-diffusions, commit b3cd532 (or later; the 1 November 2026 rounds 1 and 2 are included in the working tree, not yet committed at the time of writing).
Companion files: `HUMAN_REVIEW.md` (full checklist), `PALOMAR.md`, `PAPER_AUDIT.md`, `verification/`.

**No human has reviewed this formalization.** `review.status` in `formalization.yaml` is `unchecked`. Nothing was submitted
to a registry or attested. Everything labelled "AI" below was done by language-model agents. This page says what you would be
signing up to check.

## 1. What is machine-checked
- `Challenge.lean` has 67 theorems and 67 definitions (850 lines, 87 KB). `Solution.lean` proves each theorem with the same statement.
- All 67 use only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, `axiom` or `native_decide`.
- The sandboxed Comparator accepts the solution, with the Lean kernel, nanoda and con-ron (92444 declarations, round 2 pair).
- Rebuild instructions are in the README section "How to rebuild and verify".

Lean does **not** certify that the statements and definitions mean what the manuscript says. That is the review.

## 2. What the 67 theorems cover
- **Euclidean results (Section 1):** Thm 1.1, Cor 1.3, 1.4, (1.25), Thm 1.5, Cor 1.6, Thm 1.7, Remarks 1.2, 3.4, 3.5.
- **Riemannian results:** Thm 1.9, Thm 3.6 and Lemma 3.7, the Bochner and CD equivalence, the `k₁` bounds, and Poincaré/LSI from CD.
- **Section 3 and 4 material:** the Gaussian factorization, Lemma 3.3 (the Ornstein–Uhlenbeck eigenmap), normalization and temperature.
- **Supporting results:** Wasserstein contraction, entropy and Fisher decay, Pinsker, Talagrand, optimal constants.
- **1 November 2026 round (nos. 49-57):** kernel = SDE law, pathwise Lemma 3.3, integrated entropy-dissipation inequality, static Dyson-OU, Γ operator/polarization/chain rule, vector Bochner.
- **Brownian motion:** existence of Brownian motion and of a Langevin solution (nos. 47, 48), from the vendored Degenne et al. library.
- **Round 2 (nos. 58-67, plus changed nos. 51-52):** `dyson_spectralGap`; Gaussian isoperimetry for the **quadratic potential only** (nos. 59-61); the Rothaus alternative for an **abstract form with a compactness hypothesis** and for **finite spaces** (nos. 62-64);
  `temperature_kernel` (65); the sphere in **model form** (66, 67: `Ric = (d-1)g`, `CD(d-1)`, `λ₁ = d`, so the sphere is not a witness of `hgap` of Thm 1.9); the equality in the integrated de Bruijn identity (51, 52).

## 3. Where I would look first (highest risk)
1. **Kernel encoding of the diffusion.** 21 Euclidean statements no longer mention Brownian motion. They use
   `IsEuclideanDiffusion V Pt`: Markov kernels, the semigroup law, and the Dynkin identity on `C_c^∞` with generator `Δ − ∇V·∇`.
   Uniqueness of such `Pt` is proved for convex `C²` `V` (`euclideanDiffusion_unique_convex`). That `Pt t x` is the law of any SDE solution is a Challenge statement (no. 49, rigid curvature, `V ∈ C²`).
2. **`C²` (round 2) instead of `C^∞`.** The 23 statements using `IsEuclideanLangevin`/`IsRigidSequenceK`/`IsSigmaLangevin` now assume `V ∈ C²` (and `W n ∈ C²` for Cor 1.6), as in the manuscript.
   This rests on uniqueness of the diffusion kernel for **convex** `C²` potentials (`euclideanDiffusion_unique_convex`, about 3000 lines in `Extra/C2Uniq*`: mollification, Bakry–Émery for the approximants, radial cutoff). Every statement carries a convexity hypothesis; nonconvex `V` is not covered.
   The earlier `C^∞` statement texts are gone from the Challenge; the `C^∞` results are proof-side only (`IsEuclideanLangevinInf`). The AI audit of this change is pending.
3. **Amendments to the printed statements:**
   - Thm 1.7 is false as printed (OU counterexample in `PAPER_AUDIT.md`, written derivation only). It is amended to `liminf κ > 0` and `t₀ → ∞`.
   - `p` is finite in (1.25); `p = ∞` fails for OU.
   - Thm 3.6 adds that `N` is connected and complete, and the potential identity `V∘Φ⁻¹`.
   - `0 < d` and `0 < finrank` are added to several statements.
   - The `k₁` bounds need `hgap : λ₁ = ρ`, since they are false on spheres without it.
   - `temperature_sde` adds `Hess V ≥ ρ > 0`.
   - `temperature_cutoff` assumes `ρₙ = σ² λ₁(Vₙ/σ²)`.
   - `temperature_kernel` adds `Hess V ≥ ρ > 0` (not in the manuscript).
   - **Gaussian isoperimetry is the quadratic case only** (`V = ρ|x|²/2 + c`); the manuscript's remark concerns general `CD(ρ,∞)`.
   - **Rothaus is abstract/finite only**: `Form.Compact` is a hypothesis; the compact-manifold theorem is not proved. `finite_rothaus` quantifies over any `Form` with domain all functions and the Dirichlet energy.
   - **Sphere in model form**: `IsSphereModel` (isometric smooth map into `S^d ⊂ ℝ^{d+1}`); `sphere_gap` shows `λ₁ = d ≠ d-1`, so the sphere is **not** a witness of `hgap` in Thm 1.9. The concrete sphere is in `Extra` only.
4. **Lemma 3.3 in two forms.** The law form (no. 10) is `(Pt t x₀).map Tv = 𝒩(e^{-ρt} Tv x₀, (1−e^{-2ρt}) I)`. The pathwise form (no. 50, `eigenmap_is_ou_pathwise`) gives a standard Brownian `β` on the same space
   with `Tv(X_t) = Tv(x₀) − ρ∫Tv(X_s)ds + √(2ρ) β_t`, for `IsLangevin` (C² only). It is a re-export of an existing theorem, and it has no filtration statement for `β`.
5. **Definitions with silent junk values:** `spectralGap` (`sInf ∅ = 0`), `fisherInfo`, `wasserstein2`, `mixingTimeKLK` (`⨅ ∅ = ⊤`), `entropyOf`, `mRic` (sign: positive on spheres).
6. **Brownian-level statements** (nos. 42, 43, 47, 48). Solutions are hypotheses, and `exists_langevin` assumes `Hess V ≥ 0`.
7. **New statements nos. 49-57** (audit M, no defect, remarks only):
   - no. 49 kernel = law of any SDE solution (`V ∈ C²`, rigid curvature);
   - nos. 51-52 originally only the inequality half of `H(μ_s) − H(μ_t) = ∫_s^t I`; in round 2 they became the **equality**, with `Hess V ≥ ρ > 0` (AI audit pending);
   - no. 53 static Dyson–OU: the optimal Poincaré constant `1/ρ` follows from the Poincaré inequality plus `Var h = ρ⁻¹∫|∇h|²` for the unbounded `h`, by a truncation argument that is not itself a conjunct;
     `λ₁ = ρ` is no. 58 (`dyson_spectralGap`, round 2, via the separate definition `dysonGap`, not the project's `spectralGap`);
   - nos. 54-56 Γ as the operator, polarization, scalar chain rule;
   - no. 57 vector Bochner: slot order `Ric(v,∇f)`, symmetry of `mRic` not built in, rough Laplacian with chart-constant frame, frame independence not asserted.
8. **Vendored code** (`vendor/`, Apache-2.0). It differs from upstream only by 3 documented patches and one added compatibility module.
   It is imported only privately by `Paper/ExistsBrownian.lean`.

## 4. AI audits (reuse, do not trust)
- Every statement has had at least one AI audit and most have had two. The reports are `verification/semantic-audit.md`,
  `audit-second-{1,2}.md` and `audit-extra-{A..M}.md`. They covered statements and definitions only, not proofs.
- **No audit found a defect.** The agents share blind spots with the tooling that wrote the statements, so form your own verdict first.
- `exists_stdBrownian` and `exists_langevin` were audited in `audit-extra-J.md`. The kernel statements were audited in `-K` and `-L`.
- The nine statements added in the first 1 November 2026 round were audited in `audit-extra-M.md` (no defect). **The round-2 statements (nos. 58-67), the equality versions (51, 52) and the `C²` change have not been audited by an AI agent yet (pending).** Each also went through a worker/adversary pass
  (`extra-status/*-worker.md`, `*-adversary.md`): the adversary found one repair (the entropy-dissipation statement excluded Dirac initial laws; fixed) and one vacuous conditional
  (a sphere result, not in the Challenge; fixed).
- Adversary reports can be read next to the statements, but they are AI work too.

## 5. Known limits
- **Not formalized:** see the README section "What is not formalized". In short:
  - Question 1.10 (open) and `eq:loggradbound` (conjecture).
  - Thm 1.7 on manifolds (no precise statement); the Dyson–OU process (the static statement and the gap are proved).
  - Gaussian isoperimetry for general `CD(ρ,∞)` (quadratic potential only); the Rothaus remark on compact manifolds (abstract form with `Form.Compact` and finite spaces only);
    the concrete round sphere and "`hgap` cannot be dropped" (in `Extra/Sphere*`, not in the Challenge; only the model form is).
- **Attempted in round 2 and only partly achieved:** Gaussian isoperimetry (quadratic case), the Rothaus remark (abstract and finite cases), the sphere (model form in the Challenge; concrete sphere in `Extra`). Achieved: `C²`, the equality in the entropy-dissipation identity.
- **Non-vacuity:** only the Riemannian hypotheses have a committed Lean witness, and it is flat (Gaussian on ℝᵏ).
  `temperature_kernel` (nos. 65) gives existence for the `σ`-diffusion (convex `C²`); `Form.Compact` is satisfied in Lean only for finite spaces (not a Challenge statement).
- **Global instance:** `instIsContMDiffRiemannianBundleRd` is added globally. It should not change any statement, and only `temperature_cd` touches it.
- **`formalization.yaml`:** the alignment entries were not validated against the official schema.

## 6. Suggested review plan (about a day)
1. Run the README rebuild steps and record the commit hash (15 min).
2. Read the definitions: Euclidean (`Challenge.lean` lines 1-150), the kernel definitions, and the Riemannian section from `mgrad` (about line 712).
3. Go through the table in `HUMAN_REVIEW.md` §2 and tick each of the 67 statements against the manuscript.
4. Decide on the convexity requirement hidden in the `C²` kernel statements, the two forms of Lemma 3.3 and the Thm 1.7 amendment, and whether the static Dyson statement plus the gap (nos. 53, 58) suffice, and whether the quadratic-only Gaussian isoperimetry (59-61), the abstract/finite Rothaus (62-64) and the model-form sphere (66-67) are acceptable scopes.
5. Check the vendored code provenance (`vendor/README.md`).
6. Only after a real review: fill the `review` fields in `formalization.yaml` and decide on registry submission and attestation (humans only).

Sign-off: Reviewer(s): ____________  Date: ____________  Commit: ____________
