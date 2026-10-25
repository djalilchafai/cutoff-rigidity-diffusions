module

public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Extra.Dynamics
public import CutoffRigidity.Paper.MainWasserstein
public import CutoffRigidity.Paper.WassersteinCutoff

/-! # Brownian-free kernel versions of Theorem 1.1, Corollary 1.3 and the W2 contraction

Each statement replaces the Brownian carrier by the transition kernels `Pt` with hypothesis
`IsEuclideanLangevin` (resp. `IsRigidSequenceK`), and is derived from the Brownian-based
`Paper` theorem through the transfer lemmas of `EuclideanDiffusion`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set CutCur
open scoped ENNReal NNReal Topology

/-- **Theorem 1.1** (main Wasserstein estimate), kernel form (no Brownian motion). -/
theorem main_wasserstein_estimate_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.IsEuclideanLangevin V Pt) (hV : CutCur.RigidCurvature V) (t : ℝ≥0) :
    let gap := CutCur.spectralGap V
    let q := Real.exp (-2 * gap * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / gap) * Λ +
      ENNReal.ofReal (CutCur.firstEigenDim V * (1 - Real.sqrt (1 - q)) ^ 2 / gap)
    let W := fun x₀ => CutCur.wasserstein2 (Pt t x₀) (CutCur.gibbs V) ^ 2
    (∀ S : Set (CutCur.Rd d), S.Nonempty →
      lower (⨆ x₀ ∈ S, CutCur.eigenLambda V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x x₀ ^ 2 ∂CutCur.gibbs V) ∧
    (∫ x, x ∂CutCur.gibbs V = 0 → ∀ R : ℝ, 0 ≤ R →
      lower (ENNReal.ofReal (gap * R ^ 2)) ≤ ⨆ x₀ ∈ Metric.closedBall 0 R, W x₀) := by
  obtain ⟨Ω, _, B, P, X, hP, hLang, key⟩ := CutCur.exists_isLangevin_of_rigid hL hV
  have := main_wasserstein_estimate_carrier hLang hV t
  simpa only [key] using this

/-- **Corollary 1.3** (Wasserstein cutoff), kernel form (no Brownian motion). -/
theorem wasserstein_cutoff_K {V : ∀ n, CutCur.Rd n → ℝ}
    {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)}
    (h : CutCur.IsRigidSequenceK V Pt) {c : ℝ} (hc : 0 < c) :
    CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (CutCur.meanBall (V n) c)
      (CutCur.wasserstein2 · (CutCur.gibbs (V n))))
      (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 := by
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.exists_isRigidSequence_of_K h
  have hcut := wasserstein_cutoff_carrier hrig hc
  exact CutCur.hasCutoff_congr_eventually
    (CutCur.eventually_worst_eq_worstK key (fun n => CutCur.meanBall (V n) c)
      (fun n => (CutCur.wasserstein2 · (CutCur.gibbs (V n))))) hcut

/-- **Wasserstein contraction**, kernel form (no Brownian motion). -/
theorem langevin_w2_contraction_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.IsEuclideanLangevin V Pt) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν₁ ν₂ : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (t : ℝ≥0) :
    CutCur.wasserstein2 (ν₁.bind (Pt t)) (ν₂.bind (Pt t)) ≤
      ENNReal.ofReal (Real.exp (-ρ * t)) * CutCur.wasserstein2 ν₁ ν₂ := by
  have hcv : ∀ x z : CutCur.Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z := fun x z =>
    le_trans (mul_nonneg hρ (sq_nonneg _)) (hHess x z)
  obtain ⟨Ω, _, B, P, X, hP, hLang, key⟩ := CutCur.exists_isLangevin_of_isEuclideanLangevin hL hcv
  have := langevin_w2_contraction_carrier hLang hρ hHess ν₁ ν₂ t
  have e : (fun x => P.map (X x t)) = ⇑(Pt t) := funext fun x => key t x
  simpa only [e] using this

-- Names of the Challenge theorems (kernel statements; the Brownian versions are `*_carrier`).
alias main_wasserstein_estimate := main_wasserstein_estimate_K
alias wasserstein_cutoff := wasserstein_cutoff_K

end CutoffRigidity.Paper
