# Human review summary for the authors (draft)

Repository: https://github.com/djalilchafai/cutoff-rigidity-diffusions, commit a74b7ab (or later).
Companion files: `HUMAN_REVIEW.md` (full checklist), `PALOMAR.md`, `PAPER_AUDIT.md`, `verification/`.

**No human has reviewed this formalization.** `review.status` in `formalization.yaml` is `unchecked`. Nothing was submitted
to a registry or attested. Everything labelled "AI" below was done by language-model agents. This page says what you would be
signing up to check.

## 1. What is machine-checked
- `Challenge.lean` has 48 theorems and 55 definitions (981 lines). `Solution.lean` proves each theorem with the same statement.
- All 48 use only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, `axiom` or `native_decide`.
- The sandboxed Comparator accepts the solution, with the Lean kernel, nanoda and con-ron (91176 declarations).
- Rebuild instructions are in the README section "How to rebuild and verify".

Lean does **not** certify that the statements and definitions mean what the manuscript says. That is the review.

## 2. What the 48 theorems cover
- **Euclidean results (Section 1):** Thm 1.1, Cor 1.3, 1.4, (1.25), Thm 1.5, Cor 1.6, Thm 1.7, Remarks 1.2, 3.4, 3.5.
- **Riemannian results:** Thm 1.9, Thm 3.6 and Lemma 3.7, the Bochner and CD equivalence, the `k₁` bounds, and Poincaré/LSI from CD.
- **Section 3 and 4 material:** the Gaussian factorization, Lemma 3.3 (the Ornstein–Uhlenbeck eigenmap), normalization and temperature.
- **Supporting results:** Wasserstein contraction, entropy and Fisher decay, Pinsker, Talagrand, optimal constants.
- **Brownian motion:** existence of Brownian motion and of a Langevin solution (nos. 47, 48), from the vendored Degenne et al. library.

## 3. Where I would look first (highest risk)
1. **Kernel encoding of the diffusion.** 21 Euclidean statements no longer mention Brownian motion. They use
   `IsEuclideanDiffusion V Pt`: Markov kernels, the semigroup law, and the Dynkin identity on `C_c^∞` with generator `Δ − ∇V·∇`.
   Uniqueness of such `Pt` is proved (`isEuclideanDiffusion_unique`). That `Pt t x` is the law of the SDE solution is argued, not a Challenge statement.
2. **C^∞ instead of C².** Those 21 statements assume `V ∈ C^∞` (and `W n ∈ C^∞` for Cor 1.6), because the uniqueness proof needs smoothness.
   They are weaker than the printed statements in this respect. The `C²` versions survive only as unchecked `*_carrier` theorems.
3. **Amendments to the printed statements:**
   - Thm 1.7 is false as printed (OU counterexample in `PAPER_AUDIT.md`, written derivation only). It is amended to `liminf κ > 0` and `t₀ → ∞`.
   - `p` is finite in (1.25); `p = ∞` fails for OU.
   - Thm 3.6 adds that `N` is connected and complete, and the potential identity `V∘Φ⁻¹`.
   - `0 < d` and `0 < finrank` are added to several statements.
   - The `k₁` bounds need `hgap : λ₁ = ρ`, since they are false on spheres without it.
   - `temperature_sde` adds `Hess V ≥ ρ > 0`.
   - `temperature_cutoff` assumes `ρₙ = σ² λ₁(Vₙ/σ²)`.
4. **Law form of Lemma 3.3.** The statement is `(Pt t x₀).map Tv = 𝒩(e^{-ρt} Tv x₀, (1−e^{-2ρt}) I)`. The pathwise Brownian `β` is not stated.
5. **Definitions with silent junk values:** `spectralGap` (`sInf ∅ = 0`), `fisherInfo`, `wasserstein2`, `mixingTimeKLK` (`⨅ ∅ = ⊤`), `entropyOf`, `mRic` (sign: positive on spheres).
6. **Brownian-level statements** (nos. 42, 43, 47, 48). Solutions are hypotheses, and `exists_langevin` assumes `Hess V ≥ 0`.
7. **Vendored code** (`vendor/`, Apache-2.0). It differs from upstream only by 3 documented patches and one added compatibility module.
   It is imported only privately by `Paper/ExistsBrownian.lean`.

## 4. AI audits (reuse, do not trust)
- Every statement has had at least one AI audit and most have had two. The reports are `verification/semantic-audit.md`,
  `audit-second-{1,2}.md` and `audit-extra-{A..L}.md`. They covered statements and definitions only, not proofs.
- **No audit found a defect.** The agents share blind spots with the tooling that wrote the statements, so form your own verdict first.
- `exists_stdBrownian` and `exists_langevin` were audited in `audit-extra-J.md`. The kernel statements were audited in `-K` and `-L`.

## 5. Known limits
- **Not formalized:**
  - Question 1.10 (open) and `eq:loggradbound` (conjecture).
  - `dH/dt = −I` for general laws, and Thm 1.7 on manifolds.
  - The sphere claims, Dyson, Gaussian isoperimetry, the Leibniz identity for the carré du champ, vector-form Bochner, and the Rothaus remark.
- **Non-vacuity:** only the Riemannian hypotheses have a committed Lean witness, and it is flat (Gaussian on ℝᵏ).
  `IsSigmaLangevin` for `σ ≠ 1` is argued by hand only.
- **Global instance:** `instIsContMDiffRiemannianBundleRd` is added globally. It should not change any statement, and only `temperature_cd` touches it.
- **`formalization.yaml`:** the alignment entries were not validated against the official schema.

## 6. Suggested review plan (about a day)
1. Run the README rebuild steps and record the commit hash (15 min).
2. Read the definitions: Euclidean (`Challenge.lean` lines 1-150), the kernel definitions, and the Riemannian section from `mgrad` (about line 712).
3. Go through the table in `HUMAN_REVIEW.md` §2 and tick each of the 48 statements against the manuscript.
4. Decide on the C^∞ restriction, the law form of Lemma 3.3 and the Thm 1.7 amendment.
5. Check the vendored code provenance (`vendor/README.md`).
6. Only after a real review: fill the `review` fields in `formalization.yaml` and decide on registry submission and attestation (humans only).

Sign-off: Reviewer(s): ____________  Date: ____________  Commit: ____________
