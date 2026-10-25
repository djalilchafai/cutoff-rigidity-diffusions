# euc2: kernel (Brownian-free) versions of Thm 1.1, Cor 1.3, W2 contraction

File: `CutoffRigidity/Extra/EuclideanWasserstein.lean` (module `CutoffRigidity.Extra.EuclideanWasserstein`), `lake build` OK, no sorry,
axioms of all three: propext, Classical.choice, Quot.sound. Namespace `CutoffRigidity.Paper`; each is a 3-5 line transfer proof
(recipe of euc1). No amendment beyond C^inf (inside IsEuclideanLangevin): Thm 1.1 and Cor 1.3 assume RigidCurvature (convexity implied);
the contraction assumes `0 <= rho` and `Hess V >= rho`, which implies convexity. No extra convexity hypothesis anywhere.

## Challenge text (unqualified names)
```lean
/-- **Theorem 1.1** (main Wasserstein estimate), including the ball refinement; kernel form without Brownian motion
(`Pt t x₀ = Law(X_t^{x₀})`). Amendment: `V` is `C^∞` (inside `IsEuclideanLangevin`). -/
theorem main_wasserstein_estimate_K {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hL : IsEuclideanLangevin V Pt) (hV : RigidCurvature V) (t : ℝ≥0) :
    let gap := spectralGap V
    let q := Real.exp (-2 * gap * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / gap) * Λ +
      ENNReal.ofReal (firstEigenDim V * (1 - Real.sqrt (1 - q)) ^ 2 / gap)
    let W := fun x₀ => wasserstein2 (Pt t x₀) (gibbs V) ^ 2
    (∀ S : Set (Rd d), S.Nonempty →
      lower (⨆ x₀ ∈ S, eigenLambda V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x x₀ ^ 2 ∂gibbs V) ∧
    (∫ x, x ∂gibbs V = 0 → ∀ R : ℝ, 0 ≤ R →
      lower (ENNReal.ofReal (gap * R ^ 2)) ≤ ⨆ x₀ ∈ Metric.closedBall 0 R, W x₀)

/-- **Corollary 1.3** (Wasserstein cutoff on balls `B(m, c√d)`), kernel form without Brownian motion.
Amendment: `V n` is `C^∞` (inside `IsRigidSequenceK`). -/
theorem wasserstein_cutoff_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt) {c : ℝ} (hc : 0 < c) :
    HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c) (wasserstein2 · (gibbs (V n))))
      (fun n => criticalTime n (spectralGap (V n))) ⊤ 0

/-- **Wasserstein contraction** `W₂(ν₁ Pₜ, ν₂ Pₜ) ≤ e^{-ρt} W₂(ν₁, ν₂)` under `Hess V ≥ ρ`, `ρ ≥ 0`, for arbitrary
initial laws; kernel form (`ν.bind (Pt t)` is the law at time `t` from `ν`). Amendment: `V` is `C^∞`. -/
theorem langevin_w2_contraction_K {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hL : IsEuclideanLangevin V Pt) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν₁ ν₂ : Measure (Rd d)) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (t : ℝ≥0) :
    wasserstein2 (ν₁.bind (Pt t)) (ν₂.bind (Pt t)) ≤
      ENNReal.ofReal (Real.exp (-ρ * t)) * wasserstein2 ν₁ ν₂
```
Paper names: `CutoffRigidity.Paper.main_wasserstein_estimate_K`, `wasserstein_cutoff_K`, `langevin_w2_contraction_K`.
Note: `langevin_w2_contraction` is not in Challenge.lean currently (only in Extra/Dynamics.lean); the `_K` version is stated for the future Challenge.
Dependencies: the foundation file (`IsEuclideanLangevin`, `IsRigidSequenceK`, `worstK` must move to Challenge.lean); `criticalTime`, `meanBall`, `HasCutoff` already Challenge.
