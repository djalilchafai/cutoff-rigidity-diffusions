# C2Sigma worker report (R4 continuation, Task B)

Files: `CutoffRigidity/Extra/C2Sigma1.lean`, `C2Sigma2.lean` (new, imported by nothing). Build: `lake build CutoffRigidity.Extra.C2Sigma2`
(covers both; Sigma2 imports Sigma1 which imports C2Uniq9 and Sigma). Compiles, no sorry/axiom/native_decide; `#print axioms` of
`temperature_cutoff_C2`, `normalization_cutoff_C2`, `temperature_kernel_C2`, `isSigmaLangevin2_iff`, `isSigmaLangevin2_unique`, `isEucLangevin2_invariant`:
all `[propext, Classical.choice, Quot.sound]`. No human review claimed; adversary pass pending.

## Statements (exact Lean, C2Sigma1)
```lean
def CutCur.C2U.IsSigmaLangevin2 (V) (σ) (Pt) : Prop :=
  ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2) ∧ IsSigmaDiffusion V σ Pt
theorem CutCur.C2U.isSigmaLangevin2_iff (hσ : 0 < σ) :
  IsSigmaLangevin2 V σ Pt ↔ IsEucLangevin2 (fun x => V x / σ ^ 2) (fun u => Pt (((σ ^ 2)⁻¹).toNNReal * u))
theorem CutCur.C2U.isSigmaLangevin2_unique (hσ) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) (h₁ : IsSigmaLangevin2 V σ P₁) (h₂ : ... P₂) t x : P₁ t x = P₂ t x
theorem CutoffRigidity.Paper.normalization_cutoff_C2  -- same text as normalization_cutoff (no potential in it), proved by normalization_cutoff_K
theorem CutoffRigidity.Paper.temperature_cutoff_C2 {V σ ρ Pt} (hσ) (hY : ∀ n, 0 < n → IsSigmaLangevin2 (V n) σ (Pt n)) (hρ) (hHess) (hgap) (hliminf) (hc) : <same conclusion>
```
C2Sigma2:
```lean
theorem isEucLangevin2_invariant (h : IsEucLangevin2 V Pt) (hr : 0 < r) (hHess : ∀ x z, r * ‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (t) : (gibbs V).bind (Pt t) = gibbs V
theorem temperature_kernel_C2 (hσ : 0 < σ) (hV : ContDiff ℝ 2 V) {ρ} (hρ : 0 < ρ) (hHess : ∀ x z, ρ * ‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2)) :
  (∃ Pt, IsSigmaLangevin2 V σ Pt) ∧ ∀ Pt, IsSigmaLangevin2 V σ Pt →
    (∀ t, (gibbs fun x => V x / σ ^ 2).bind (Pt t) = gibbs fun x => V x / σ ^ 2) ∧
    ∀ Q, IsEucLangevin2 (fun x => V x / σ ^ 2) Q → ∀ t x, Pt t x = Q ((σ ^ 2).toNNReal * t) x
```

## Statement-diff vs Challenge
* `normalization_cutoff`: NO difference at all. The Challenge statement has no potential and no smoothness hypothesis (generic kernels), so it is already the "C²" statement; `normalization_cutoff_C2` is a restatement (term `normalization_cutoff_K hα`). Nothing to port.
* `temperature_cutoff`: only `IsSigmaLangevin (V n) σ (Pt n)` becomes `IsSigmaLangevin2 (V n) σ (Pt n)` (clause `ContDiff ℝ ∞ V` -> `ContDiff ℝ 2 V`). Convexity: yes, supplied by the Challenge's own hypotheses `hρ : 0 < ρ n`, `hHess : ρ n ‖z‖² ≤ Hess V (z,z)` (so no new hypothesis; the proof goes through `IsRigidSeqK2`, `exists_isRigidSequence_of_K2`, `euclideanDiffusion_unique_convex`). No extra smoothness hypothesis is needed. Proof = that of `temperature_cutoff_K` with the C² transfer swapped in; `isSigmaLangevin2_iff` only needs `V` differentiable (existing `isSigmaDiffusion_iff`).
* `temperature_kernel` (Sigma.lean, not a Challenge statement): C² port `temperature_kernel_C2` has extra hypotheses `ρ > 0` and `Hess V ≥ ρ` (instead of only `ContDiff ℝ ∞ V`): uniqueness needs convexity (Hess ≥ 0) and Gibbs invariance needs `ρ > 0` (library `langevinKernel_gibbs_invariant`; invariance for merely convex C² V is not ported). Existence also uses convexity (`exists_euclideanLangevin_C2`), whereas the smooth version `exists_sigmaLangevin` needs none. Without convexity the C² statements are genuinely not available (uniqueness at C² without convexity is not proved anywhere in the project).
* Not ported: `exists_sigmaLangevin` for non-convex smooth V stays in Sigma.lean (smooth only); `sigmaLangevin_eq_timeChange`/`isSigmaLangevin_unique`/`isSigmaLangevin_invariant` of Sigma.lean are replaced in the C² world by `isSigmaLangevin2_unique`, the time-change clause of `temperature_kernel_C2`, `isEucLangevin2_invariant`.

## Integration hint
If the lead changes `IsSigmaLangevin`'s clause to `ContDiff ℝ 2 V` in Challenge/Statements, `temperature_cutoff` keeps its text and the body of `temperature_cutoff_C2` replaces `temperature_cutoff_K` (swap `isEuclideanLangevin_of_sigma` -> `C2U.isEucLangevin2_of_sigma`, `exists_isRigidSequence_of_K` -> `_K2`). `Sigma.lean` then breaks at `isSigmaLangevin_iff` (restate at order 2: this file's `isSigmaLangevin2_iff`), `sigmaLangevin_eq_timeChange`, `isSigmaLangevin_unique`, `isEuclideanLangevin_invariant` (use `isEuclideanDiffusion_unique` which needs C^∞), and `temperature_kernel` (use `temperature_kernel_C2`); `exists_sigmaLangevin` keeps an explicit `ContDiff ℝ ∞ V` hypothesis.
