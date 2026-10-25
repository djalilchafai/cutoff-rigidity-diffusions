# rem34: Remark 3.4 (weaker assumption in Corollary 1.3)

Status: PROVED, no amendment needed. Claim is true as written (in fact for any real alpha).
Math check: at t=(1+eps)t*, e^{-lambda t}=d^{-(1+eps)/2}, so the upper bound is
d^{-eps/2}(c^2+lambda^{-1})^{1/2} <= d^{-eps/2}(c^2+(log d)^alpha)^{1/2} -> 0 (log^alpha = o(d^eps)).
The lower bound (before cutoff) never used liminf. Note: Lean's 0⁻¹=0, so positivity of the gap is
taken from RigidCurvature (rate_pos), not from the new hypothesis.

File: CutoffRigidity/Extra/WassersteinCutoffWeak.lean (builds; axioms propext, Classical.choice, Quot.sound).
Lemma: CutoffRigidity.Paper.barycenter_wasserstein_after_cutoff_weak.
Theorem: CutoffRigidity.Paper.wasserstein_cutoff_weak. No existing file edited.

Proposed Challenge text (IsRigidSequence's liminf conjunct replaced by hypothesis hgap):

/-- **Remark 3.4** (weaker assumption in Corollary 1.3): `liminf λ₁⁽ⁿ⁾ > 0` may be replaced by
`(λ₁⁽ⁿ⁾)⁻¹ ≤ (log n)^α` eventually, for some `α > 0`. -/
theorem wasserstein_cutoff_weak {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)} {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (hL : ∀ n, 0 < n → IsLangevin (V n) (B n) (P n) (X n) ∧ RigidCurvature (V n))
    (hgap : ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, (spectralGap (V n))⁻¹ ≤ (Real.log n) ^ α)
    {c : ℝ} (hc : 0 < c) :
    HasCutoff (fun n => worst (P n) (X n) (meanBall (V n) c) (wasserstein2 · (gibbs (V n))))
      (fun n => criticalTime n (spectralGap (V n))) ⊤ 0

Wiring: Paper version is identical with CutCur.-qualified names (as in the file).
