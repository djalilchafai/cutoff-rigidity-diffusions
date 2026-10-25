module

public import CutoffRigidity.Paper.FisherBridgeWeak
public import CutoffRigidity.RelativeFisherInformation
public import CutoffRigidity.Statements

/-!
# The weak-gradient Fisher information equals the closed-gradient one

The statement-level relative Fisher information `CutCur.fisherInfo`, defined
with the textbook weak gradient tested against smooth compact functions, equals
the project's `relativeFisherInformation`, defined through the closure of the
classical Gibbs gradient. Closed gradients are weak gradients; conversely weak
gradients in Gibbs L² lie in the closed domain; and weak gradients are unique.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter
open scoped ContDiff ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The statement-level Gibbs measure is the project's Gibbs measure. -/
theorem cutCur_gibbs_eq (V : E → ℝ) : CutCur.gibbs V = gibbsMeasure volume V := rfl

/-- Coordinate weak-derivative identities assemble into the vector identity. -/
theorem weak_gradient_of_coordinates {u φ : E → ℝ} {G : E → E}
    (hu : LocallyIntegrable u volume) (hG : LocallyIntegrable G volume)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hcoord : ∀ j : Fin d,
      (∫ x, φ x * G x j) = -(∫ x, coordinateDerivative j φ x * u x)) :
    ∫ x, u x • gradient φ x = -∫ x, φ x • G x := by
  have h1 : Integrable (fun x => u x • gradient φ x) volume :=
    hu.integrable_smul_right_of_hasCompactSupport (continuous_gradient_of_c1 hφ)
      (gradient_hasCompactSupport hφc)
  have h2 : Integrable (fun x => φ x • G x) volume :=
    hG.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  apply PiLp.ext
  intro j
  rw [PiLp.neg_apply, integral_euclidean_apply h1, integral_euclidean_apply h2]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [hcoord j, neg_neg]
  congr 1
  funext x
  rw [mul_comm, coordinateDerivative, fderiv_single_eq_gradient_coordinate]

/-- **Closed gradients are weak gradients.** Every element of the closed Gibbs
graph satisfies the Lebesgue weak-gradient identity against compact C² tests. -/
theorem gibbsSobolev_weak_gradient_volume {V φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (w : gibbsSobolevGraph hV hprob)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ x, gibbsSobolevInclusion hV hprob w x • gradient φ x =
      -∫ x, φ x • gibbsSobolevDerivative hV hprob w x :=
  weak_gradient_of_coordinates
    (locallyIntegrable_volume_of_memLp_gibbs hV.continuous hprob
      (Lp.memLp (gibbsSobolevInclusion hV hprob w)))
    (locallyIntegrable_volume_of_memLp_gibbs hV.continuous hprob
      (Lp.memLp (gibbsSobolevDerivative hV hprob w)))
    (hφ.of_le (by norm_num)) hφc
    (fun j => gibbsSobolev_coordinate_weak_derivative_volume hV hprob hφ hφc j w)

/-- **Uniqueness of weak gradients.** Two locally integrable weak gradients of
the same function, for smooth compact tests, agree Lebesgue almost everywhere. -/
theorem weak_gradient_ae_unique {u : E → ℝ} {G₁ G₂ : E → E}
    (hG₁ : LocallyIntegrable G₁ volume) (hG₂ : LocallyIntegrable G₂ volume)
    (h₁ : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, u x • gradient φ x = -∫ x, φ x • G₁ x)
    (h₂ : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, u x • gradient φ x = -∫ x, φ x • G₂ x) :
    G₁ =ᵐ[volume] G₂ := by
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hG₁.sub hG₂) (fun φ hφ hφc => by
    have i1 := hG₁.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have i2 := hG₂.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have he := neg_inj.mp ((h₁ φ hφ hφc).symm.trans (h₂ φ hφ hφc))
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub i1 i2, he, sub_self])
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

/-- The squared L² norm of a vector class as a lower Lebesgue integral. -/
theorem ofReal_four_mul_norm_sq_eq_lintegral {μ : Measure E} (f : E →₂[μ] E) :
    ENNReal.ofReal (4 * ‖f‖ ^ 2) = 4 * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have hn : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    rw [real_inner_self_eq_norm_sq]
  rw [hn, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ofReal_integral_eq_lintegral_ofReal (Lp.memLp f).norm.integrable_sq
      (Eventually.of_forall fun x => sq_nonneg _)]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Fisher information bridge.** For a uniformly convex `C²` potential with
normalized Gibbs measure, the statement-level weak-gradient relative Fisher
information equals the project's closed-gradient relative Fisher information,
for every finite measure `ν`. -/
theorem fisherInfo_eq_relativeFisherInformation {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ) (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsFiniteMeasure ν] :
    CutCur.fisherInfo V ν = relativeFisherInformation hV hprob ν := by
  classical
  let μ := gibbsMeasure volume V
  have hVc := hV.continuous
  unfold CutCur.fisherInfo
  rw [cutCur_gibbs_eq]
  by_cases hac : ν ≪ μ
  swap
  · rw [relativeFisherInformation_eq_top_of_not_ac hV hprob ν hac]
    simp only [iInf_eq_top]
    intro G hG
    exact absurd hG.1 hac
  let U := squareRootRNDensityLp ν μ
  have hUae : (U : E → ℝ) =ᵐ[volume] squareRootRNDensity ν μ :=
    (gibbsMeasure_ae_eq_iff volume hVc.measurable).mp (squareRootRNDensity_memLp ν μ).coeFn_toLp
  by_cases hD : U ∈ (closedGibbsGradient hV hprob).domain
  · rw [relativeFisherInformation_eq_closed_energy hV hprob ν hac hD]
    let D := closedGibbsGradient hV hprob ⟨U, hD⟩
    have hgraph : (U, D) ∈ (closedGibbsGradient hV hprob).graph :=
      (closedGibbsGradient hV hprob).mem_graph ⟨U, hD⟩
    let w : gibbsSobolevGraph hV hprob := ⟨WithLp.toLp 2 (U, D), hgraph⟩
    have hweakD : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∫ x, Real.sqrt (ν.rnDeriv μ x).toReal • gradient φ x = -∫ x, φ x • D x := by
      intro φ hφ hφc
      have h := gibbsSobolev_weak_gradient_volume hV hprob w (hφ.of_le (by simp)) hφc
      change ∫ x, U x • gradient φ x = -∫ x, φ x • D x at h
      rw [← h]
      apply integral_congr_ae
      filter_upwards [hUae] with x hx
      rw [hx]
      rfl
    have hDl := locallyIntegrable_volume_of_memLp_gibbs hVc hprob (Lp.memLp D)
    rw [ofReal_four_mul_norm_sq_eq_lintegral]
    apply le_antisymm
    · exact iInf₂_le (D : E → E) ⟨hac, Lp.memLp D, hweakD⟩
    · refine le_iInf₂ fun G hG => ?_
      have hGl := locallyIntegrable_volume_of_memLp_gibbs hVc hprob hG.2.1
      have hae : (D : E → E) =ᵐ[volume] G := weak_gradient_ae_unique hDl hGl hweakD hG.2.2
      have haeμ : (D : E → E) =ᵐ[μ] G := (gibbsMeasure_absolutelyContinuous volume V).ae_eq hae
      change 4 * ∫⁻ x, ‖D x‖ₑ ^ 2 ∂μ ≤ 4 * ∫⁻ x, ‖G x‖ₑ ^ 2 ∂μ
      rw [lintegral_congr_ae (haeμ.mono fun x (hx : D x = G x) => by
        rw [hx])]
  · have hac' : ν ≪ gibbsMeasure volume V := hac
    have hD' : squareRootRNDensityLp ν (gibbsMeasure volume V) ∉
        (closedGibbsGradient hV hprob).domain := hD
    simp only [relativeFisherInformation, hac', hD', dite_true, dite_false, iInf_eq_top]
    intro G hG
    exfalso
    apply hD
    have hmem := smooth_weak_gradient_mem_closedGibbsGradient_graph hV hprob ρ hρ hHess
      (squareRootRNDensity_measurable ν μ) (squareRootRNDensity_memLp ν μ) hG.2.1 hG.2.2
    exact (closedGibbsGradient hV hprob).mem_domain_of_mem_graph hmem

end CutoffRigidity
