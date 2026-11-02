module

public import CutoffRigidity.Extra.C2Sigma1
public import CutoffRigidity.Extra.C2Uniq8
public import CutoffRigidity.LangevinGibbsInvariance

/-! # `C²` kernel bundle for the `σ`-diffusion (port of `temperature_kernel`)

For `V ∈ C²` with `Hess V ≥ ρ > 0` and `e^{-V/σ²}` a probability density: the `σ`-diffusion kernel
exists, leaves `e^{-V/σ²}dx` invariant, and is the time change `Pt t = P̃(σ² t)` of every Euclidean
`C²` Langevin kernel `P̃` for `V/σ²`. Uniqueness comes from `euclideanDiffusion_unique_convex`
(no Riemannian bridge); strict convexity is used only for Gibbs invariance (`langevinKernel_gibbs_invariant`).
-/

public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutCur
namespace C2U

open CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

private lemma sg2_c_mul {σ : ℝ} (hσ : 0 < σ) :
    ((σ ^ 2).toNNReal) * (((σ ^ 2)⁻¹).toNNReal) = 1 := by
  rw [← Real.toNNReal_mul (by positivity), mul_inv_cancel₀ (by positivity)]; simp

/-- Gibbs invariance for a `C²` Euclidean Langevin kernel with `Hess V ≥ r > 0`. -/
theorem isEucLangevin2_invariant {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : IsEucLangevin2 V Pt) {r : ℝ} (hr : 0 < r)
    (hHess : ∀ x z : Rd d, r * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (t : ℝ≥0) :
    (gibbs V).bind (Pt t) = gibbs V := by
  obtain ⟨Ω, hΩ, P, B, hP, hB⟩ := CutoffRigidity.Paper.exists_stdBrownian d
  have hB' : IsEuclideanBrownian B P := CutoffRigidity.Paper.isStdBrownian_iff.1 hB
  have hH0 : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z := fun x z =>
    le_trans (by positivity) (hHess x z)
  have hc : ConvexOn ℝ univ V := CutoffRigidity.NoBm.convexOn_univ_of_hessian_nonneg h.1 hH0
  have hK := isEuclideanDiffusion_langevinKernel hB' h.1 r hr.le hHess
  have hfun : ⇑(Pt t) = ⇑(langevinKernel V B P t) :=
    funext fun x => euclideanDiffusion_unique_convex h.1 hc h.2.2 hK t x
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := CutoffRigidity.Paper.gibbs_probability h.2.1
  have hinv := langevinKernel_gibbs_invariant hB' h.1 hp' r hr hHess t
  rw [hfun]
  exact hinv

/-- **`temperature_kernel`, `C²` form.** -/
theorem temperature_kernel_C2 {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hV : ContDiff ℝ 2 V) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2)) :
    (∃ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsSigmaLangevin2 V σ Pt) ∧
    ∀ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsSigmaLangevin2 V σ Pt →
      (∀ t, (gibbs fun x => V x / σ ^ 2).bind (Pt t) = gibbs fun x => V x / σ ^ 2) ∧
      ∀ Q : ℝ≥0 → Kernel (Rd d) (Rd d), IsEucLangevin2 (fun x => V x / σ ^ 2) Q →
        ∀ t x, Pt t x = Q ((σ ^ 2).toNNReal * t) x := by
  have hs2 : 0 < σ ^ 2 := by positivity
  have hHW : ∀ x z : Rd d, (ρ / σ ^ 2) * ‖z‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun x => V x / σ ^ 2)) x z z := by
    intro x z
    rw [CutoffRigidity.Paper.hessian_div_const hV (σ ^ 2) x z, div_mul_eq_mul_div, ← inv_mul_eq_div]
    exact mul_le_mul_of_nonneg_left (hHess x z) (inv_nonneg.mpr hs2.le)
  have hH0 : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ (fun x => V x / σ ^ 2)) x z z := fun x z =>
    le_trans (by positivity) (hHW x z)
  refine ⟨?_, fun Pt h => ⟨fun t => ?_, fun Q hQ t x => ?_⟩⟩
  · obtain ⟨Q, hQ⟩ := exists_euclideanLangevin_C2 (hV.div_const (σ ^ 2)) hH0 hp
    refine ⟨fun u => Q ((σ ^ 2).toNNReal * u), (isSigmaLangevin2_iff hσ).2 ?_⟩
    have : (fun u => (fun u => Q ((σ ^ 2).toNNReal * u)) (((σ ^ 2)⁻¹).toNNReal * u)) = Q := by
      funext u; simp only; rw [← mul_assoc, sg2_c_mul hσ, one_mul]
    rw [this]; exact hQ
  · have hE := (isSigmaLangevin2_iff hσ).1 h
    have := isEucLangevin2_invariant hE (div_pos hρ hs2) hHW ((σ ^ 2).toNNReal * t)
    beta_reduce at this
    rwa [← mul_assoc, mul_comm _ ((σ ^ 2).toNNReal), sg2_c_mul hσ, one_mul] at this
  · have hc : ConvexOn ℝ univ (fun x => V x / σ ^ 2) :=
      CutoffRigidity.NoBm.convexOn_univ_of_hessian_nonneg (hV.div_const _) hH0
    have h' := euclideanDiffusion_unique_convex (hV.div_const _) hc
      ((isSigmaLangevin2_iff hσ).1 h).2.2 hQ.2.2 ((σ ^ 2).toNNReal * t) x
    beta_reduce at h'
    rwa [← mul_assoc, mul_comm _ ((σ ^ 2).toNNReal), sg2_c_mul hσ, one_mul] at h'

end C2U
end CutCur
