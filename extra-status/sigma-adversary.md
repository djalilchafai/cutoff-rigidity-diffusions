# Adversary report, item R2 (sigma-diffusion kernels, CutoffRigidity/Extra/Sigma.lean)

Verdict: ACCEPT for every theorem listed. No repair needed.

Recompiled: `lake build CutoffRigidity.Extra.Sigma` succeeds. No sorry/axiom/native_decide/#print in the file.
`#print axioms` (scratch file, outside the repo) on isSigmaDiffusion_iff, isSigmaLangevin_iff, exists_sigmaLangevin,
sigmaLangevin_eq_timeChange, isSigmaLangevin_unique, isEuclideanLangevin_invariant, isSigmaLangevin_invariant,
temperature_kernel: only propext, Classical.choice, Quot.sound.

## Checks
1. Faithfulness of `IsSigmaDiffusion` (Challenge.lean l.447): Markov kernels, Chapman-Kolmogorov, Dynkin identity for
   f in C_c^infty with generator `sigma^2 * laplacian f - <grad V, grad f>`, time variable `s.toNNReal`, same shape as
   `IsEuclideanDiffusion` (Statements.lean l.92) with `generator V f = laplacian f - <grad V, grad f>`.
   It encodes exactly sigma^2 Delta - grad V . grad. Manuscript Temperature paragraph agrees (generator, SDE with sqrt(2 sigma^2)).
2. Time-change direction: `isSigmaLangevin_iff`/`isSigmaDiffusion_iff` state Sigma(V,sigma,Pt) <-> Euclid(V/sigma^2, u |-> Pt((sigma^2)^-1 * u)),
   i.e. P~(u) = Pt(u/sigma^2), Pt t = P~(sigma^2 t). Generator check: d/dt P~(sigma^2 t) = sigma^2 (Delta - grad(V/sigma^2).grad)
   = sigma^2 Delta - grad V.grad. Correct. The Lean proof's key identity `sigma^2 * generator (V/sigma^2) f = sigma^2 laplacian f - <grad V, grad f>`
   is used with the matching constants in both directions (ok, compiled). `sigmaLangevin_eq_timeChange`: `Pt t x = Q (sigma^2.toNNReal * t) x`, consistent.
   Junk values: `toNNReal` only of `sigma^2` and `(sigma^2)^-1`, both positive when sigma>0; `sig_coe`, `sig_ne` handle them. No junk issue.
   (`IsSigmaLangevin` itself does not assume sigma>0, but sigma=0 makes `gibbs 0` = Lebesgue, not a probability, so excluded; sigma<0 equals |sigma| since only sigma^2 occurs. Harmless.)
3. Non-vacuity of `temperature_kernel` (scratch files in
   /tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/sigadv/W.lean and N.lean, compile):
   - Convex witness: V = sigma^2 * gaussPot k 1 (so V/sigma^2 = gaussPot, Gibbs probability by `isProbabilityMeasure_gibbs_gaussPot`), any k, any sigma>0:
     `(temperature_kernel hσ hV hp).1` produces `IsSigmaLangevin`. Compiles.
   - NON-CONVEX witness, d=1: Q0(x) = |x|^2/2 + 2cos(x_0) (+ log Z0 normalisation), V = sigma^2 (Q0 + log Z0). Smoothness and `IsProbabilityMeasure (gibbs (V/sigma^2))`
     proven from scratch; `temperature_kernel` then yields the existence of IsSigmaLangevin. Compiles, axioms clean. Hess Q0(0) = 1 - 2 = -1 < 0 (I verified by hand;
     I did not formalize the negativity of the Hessian, only the hypotheses of the theorem).
   - Conclusion non-trivial: existence of kernels, invariance of the normalised Gibbs probability `gibbs (V/sigma^2)` (density e^{-V/sigma^2}, total mass 1 by hypothesis, i.e. Z_sigma = 1),
     and the time-change identity for every Euclid Langevin Q. `gibbs W` is `volume.withDensity (ofReal (exp (-W)))`, so `gibbs (V/sigma^2)` is e^{-V/sigma^2} dx. The manuscript has Z_sigma^-1 e^{-V/sigma^2}dx;
     the project convention (already for sigma=1) is Z=1, by shifting V by a constant (generator unchanged), so nothing is lost.
4. Convexity is legitimately dropped. Uniqueness/invariance go through `isEuclideanDiffusion_unique` (needs only V smooth and Gibbs probability; proof via Riemannian `bridge_final`
   on flat space with `isWeightedVolume_gibbs`, no Hessian assumption; checked in EuclideanDiffusion.lean) and `Diff.Kk`/`Kk_bind` for existence and invariance.
   Existence for nonconvex V was exercised by the double-well-like witness above, so no hidden convexity: the theorem's hypotheses do not include it and the witness is nonconvex.
   Brownian `temperature_sde` needs Hess V >= rho > 0 for the SDE flow construction; the kernel-level statement does not.
5. Weaker-than-claimed? The docstring claim (existence, invariance, time change) matches the statement. `isEuclideanLangevin_invariant` is stated for every Euclid Langevin Pt (via uniqueness with Kk), not only the constructed one.
   `isSigmaLangevin_unique` is pointwise equality of kernels `P1 t x = P2 t x`.

## Per-theorem
- isSigmaDiffusion_iff: ACCEPT
- isSigmaLangevin_iff: ACCEPT
- exists_sigmaLangevin: ACCEPT
- sigmaLangevin_eq_timeChange: ACCEPT
- isSigmaLangevin_unique: ACCEPT
- isEuclideanLangevin_invariant: ACCEPT
- isSigmaLangevin_invariant: ACCEPT
- temperature_kernel: ACCEPT
- (helpers kolmogorov_timeScale, markov_semigroup_timeScale: ACCEPT, public but harmless)

## Recommended compact Challenge entry (one theorem, ~8 lines; the lead should take it verbatim from Sigma.lean with `sorry` as the proof)
```
/-- **Temperature, kernel form** (Section "Temperature"): for `σ > 0`, `V` smooth, `e^{-V/σ²}` a probability density (no convexity), the `σ`-diffusion (generator `σ²Δ - ∇V·∇`) exists, leaves `e^{-V/σ²}dx` invariant, and equals the time change `Pt t = P̃ (σ² t)` of every Euclidean Langevin semigroup `P̃` of `V/σ²` (hence is unique). -/
theorem temperature_kernel {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hV : ContDiff ℝ ∞ V) (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2)) :
    (∃ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsSigmaLangevin V σ Pt) ∧
    ∀ Pt, IsSigmaLangevin V σ Pt →
      (∀ t, (gibbs fun x => V x / σ ^ 2).bind (Pt t) = gibbs fun x => V x / σ ^ 2) ∧
      ∀ Q, IsEuclideanLangevin (fun x => V x / σ ^ 2) Q →
        ∀ t x, Pt t x = Q ((σ ^ 2).toNNReal * t) x
```
This single theorem covers all eight items. It could be shortened by replacing the two `gibbs fun x => V x / σ ^ 2` with a `let μ := ...`.
