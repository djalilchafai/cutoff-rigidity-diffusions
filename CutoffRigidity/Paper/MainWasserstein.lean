module

public import CutoffRigidity.Paper.SpectralBridge
public import CutoffRigidity.Paper.SeqData
public import CutoffRigidity.EuclideanWassersteinTheorem
public import CutoffRigidity.GibbsMoments

/-! # Theorem 1.1 and Remark 1.2 on the statement surface -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-- **Remark 1.2**: `1 ≤ k₁ ≤ d`, and `Λ(x₀) = ∑ᵢ |fᵢ(x₀)|²` for every orthonormal basis of `E₁`. -/
theorem eigenspace_dim_and_lambda {V : CutCur.Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hV : CutCur.RigidCurvature V) :
    1 ≤ CutCur.firstEigenDim V ∧ CutCur.firstEigenDim V ≤ d ∧
      ∀ f, CutCur.IsEigenbasis V f → ∀ x₀, CutCur.eigenLambda V x₀ =
        ENNReal.ofReal (∑ i, f i x₀ ^ 2) :=
  ⟨one_le_firstEigenDim hV2 hp hV, firstEigenDim_le hV2 hp hV,
    fun f hf x₀ => eigenLambda_eq_sum hV2 hp hV f hf x₀⟩

/-- The squared distance integral under the Gibbs measure is finite and equals the lintegral. -/
theorem lintegral_edist_sq_gibbs {V : CutCur.Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x₀ : CutCur.Rd d) :
    ∫⁻ x, edist x x₀ ^ 2 ∂CutCur.gibbs V =
      ENNReal.ofReal (∫ y, ‖y - x₀‖ ^ 2 ∂gibbsMeasure volume V) := by
  have := hp
  have hm := gibbs_memLp_two_id_of_hessian_bound hV2 ρ hρ hHess
  have hint : Integrable (fun y : CutCur.Rd d => ‖y - x₀‖ ^ 2) (gibbsMeasure volume V) := by
    have := (hm.sub (memLp_const x₀)).integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by positivity)]
  apply lintegral_congr
  intro y
  rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg, dist_eq_norm]

/-- **Theorem 1.1** (main Wasserstein estimate), including the ball refinement. -/
theorem main_wasserstein_estimate {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin V B P X) (hV : CutCur.RigidCurvature V) (t : ℝ≥0) :
    let gap := CutCur.spectralGap V
    let q := Real.exp (-2 * gap * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / gap) * Λ +
      ENNReal.ofReal (CutCur.firstEigenDim V * (1 - Real.sqrt (1 - q)) ^ 2 / gap)
    let W := fun x₀ => CutCur.wasserstein2 (P.map (X x₀ t)) (CutCur.gibbs V) ^ 2
    (∀ S : Set (CutCur.Rd d), S.Nonempty →
      lower (⨆ x₀ ∈ S, CutCur.eigenLambda V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x x₀ ^ 2 ∂CutCur.gibbs V) ∧
    (∫ x, x ∂CutCur.gibbs V = 0 → ∀ R : ℝ, 0 ≤ R →
      lower (ENNReal.ofReal (gap * R ^ 2)) ≤ ⨆ x₀ ∈ Metric.closedBall 0 R, W x₀) := by
  intro gap q lower W
  have hV2 := hL.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := gibbs_probability hL.2.1
  have hB : IsEuclideanBrownian B P := isStdBrownian_iff.mp hL.2.2.1
  have hG : gibbsSpectralGap hV2 hp = gap := (spectralGap_eq_gibbsSpectralGap hV2 hp hV).symm
  have hW : ∀ x₀, W x₀ = squaredWasserstein (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
    intro x₀
    change CutCur.wasserstein2 (P.map (X x₀ t)) (CutCur.gibbs V) ^ 2 = _
    rw [wasserstein2_sq, IsLangevin.map_eq_langevinKernel hL gap hV.1.le hV.2 x₀ t]
    rfl
  have hdim : (CutCur.firstEigenDim V : ℝ) =
      Module.finrank ℝ (gibbsFirstEigenspace hV2 hp) := by
    rw [firstEigenDim_eq hV2 hp hV]
  have hΛ : ∀ S : Set (CutCur.Rd d), ⨆ x₀ ∈ S, CutCur.eigenLambda V x₀ =
      firstEigenLambda hV2 hp gap hV.1 hV.2 hG S := by
    intro S
    rw [firstEigenLambda, iSup_subtype']
    exact iSup_congr fun x => eigenLambda_eq hV2 hp hV x.1
  have hWS : ∀ S : Set (CutCur.Rd d), ⨆ x₀ ∈ S, W x₀ =
      ⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : CutCur.Rd d))
        (gibbsMeasure volume V) := by
    intro S
    rw [iSup_subtype']
    exact iSup_congr fun x => hW x.1
  have hlower : ∀ Λ : ℝ≥0∞, lower Λ = ENNReal.ofReal gap⁻¹ *
      (ENNReal.ofReal (Real.exp (-2 * gap * (t : ℝ))) * Λ +
        ENNReal.ofReal (Module.finrank ℝ (gibbsFirstEigenspace hV2 hp) *
          (1 - Real.sqrt (1 - Real.exp (-2 * gap * (t : ℝ)))) ^ 2)) := by
    intro Λ
    have hgp := hV.1
    show ENNReal.ofReal (q / gap) * Λ + ENNReal.ofReal (_ * (1 - Real.sqrt (1 - q)) ^ 2 / gap) = _
    rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hgp.le), ← hdim,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hgp.le)]
    simp only [div_eq_inv_mul, q, mul_comm, mul_left_comm]
    rfl
  have hS : ∀ S : Set (CutCur.Rd d), S.Nonempty →
      lower (⨆ x₀ ∈ S, CutCur.eigenLambda V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x x₀ ^ 2 ∂CutCur.gibbs V := by
    intro S hSne
    obtain ⟨hlow, hup⟩ := euclidean_wasserstein_theorem_of_gap_eq_curvature hB hV2 gap hV.1 hV.2
      hp hG S hSne t
    refine ⟨?_, ?_⟩
    · rw [hlower, hΛ, hWS]
      exact hlow
    · rw [hWS]
      refine hup.trans (le_of_eq ?_)
      congr 1
      rw [iSup_subtype']
      exact iSup_congr fun x => (lintegral_edist_sq_gibbs hV2 hp gap hV.1 hV.2 x.1).symm
  refine ⟨hS, fun hcenter R hR => ?_⟩
  have hd := pos_dim_of_rigidCurvature hL.2.1 hV
  have hΛball := firstEigenLambda_ball hV2 gap hV.1 hV.2 hp hG hcenter hd hR
  obtain ⟨hlow, -⟩ := hS (Metric.closedBall 0 R) ⟨0, Metric.mem_closedBall_self hR⟩
  rwa [hΛ, hΛball] at hlow

end CutoffRigidity.Paper
