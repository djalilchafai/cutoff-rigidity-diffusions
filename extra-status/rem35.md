# rem35: Remark 3.5 (weaker assumption lambda_1 = d^{o(1)})

Status: DONE. Proved `CutoffRigidity.Paper.information_cutoff_weak`
(file `CutoffRigidity/Extra/InformationCutoffWeak.lean`, 394 lines, builds with
`lake build CutoffRigidity.Extra.InformationCutoffWeak`; axioms: propext, Classical.choice, Quot.sound;
no sorry). No existing file edited; module NOT yet added to `CutoffRigidity.lean` (lead to do).

## Truth check (the claim is true as stated, no amendment)
* Key identity: rho * t_* = (log n)/2 for rho = lambda_1, so with regularization time T = 1/rho the
  shifted exponent 2 rho((1+eps)t_* - T) = (1+eps) log n - 2 regardless of the size of rho.
  Hence the critical time shrinking when lambda_1 grows is harmless.
* Entropy: H(t) <= e^{-2rho(t-T)}/(2T) W^2 for t >= T; with T=1/rho and W^2 <= (c^2+1/rho) n this is
  (e^2/2)(c^2 rho + 1) n^{-eps}; need rho = n^{o(1)}. TV by Pinsker (existing lemma).
* Fisher: I(t) <= e^{-2rho(t-2T)}/(2T^2) W^2 for t >= 2T (I(2T) <= H(T)/T), giving
  (e^4/2)(c^2 rho^2 + rho) n^{-eps}: prefactor rho^2 as in the manuscript.
* Needs t >= 2/rho at (1+eps)t_*, i.e. log n >= 4/(1+eps): true eventually, no condition on rho.
* Lower bounds (before t_*) are the existing `meanBall_*_before_cutoff`, which only use liminf lambda_1 > 0
  (already in IsRigidSequence); they do not use the o(log n) hypothesis. The Remark 3.4 weakening is not
  needed. So the upper bounds use only rho > 0 and rho <= n^delta eventually for each delta > 0.
* Note: n^{o(1)} contains o(log n), so this strictly generalizes `information_cutoff`.

## Proposed Challenge text (unqualified names)
```lean
/-- **Remark 3.5** (weaker assumption): Corollary 1.4 remains true when `λ₁⁽ⁿ⁾ = o(log n)` is
replaced by `λ₁⁽ⁿ⁾ = n^{o(1)}` (regularization at time `≍ 1/λ₁` instead of `1`). -/
theorem information_cutoff_weak {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)} {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (h : IsRigidSequence V B P X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, spectralGap (V n) ≤ (n : ℝ) ^ ε)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => criticalTime n (spectralGap (V n))
    let S := fun n => meanBall (V n) c
    HasCutoff (fun n => worst (P n) (X n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
    HasCutoff (fun n => worst (P n) (X n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
    HasCutoff (fun n => worst (P n) (X n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  sorry
```
Solution wiring: `CutoffRigidity.Paper.information_cutoff_weak h hsmall hc` (same binders/order as
`information_cutoff`; positivity of lambda_1 comes from `RigidCurvature` inside `IsRigidSequence`).

## Exact lemma names (namespace CutoffRigidity unless noted)
klDiv_langevinKernel_le_exp_transport_shift, relativeFisherInformation_langevinKernel_le_exp_transport_shift
(regularization at arbitrary T > 0), spectralSetKL_upper_shift, spectralSetFisher_upper_shift,
meanBallKL_upper_shift, meanBallFisher_upper_shift, weak_scalar_decay, weak_time_ge,
meanBall_{entropy,Fisher,totalVariation}_after_cutoff_weak, meanBall_information_cutoff_weak;
Paper.information_cutoff_weak (final).

## Open / blockers
None. Not human-reviewed; lead must check.
