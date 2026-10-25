module
public import CutoffRigidity.LogSobolevClosedRoot

/-! # Genuine full relative logarithmic Sobolev inequality

The actual normalized closed-H¹ root inequality is applied to the actual
Radon--Nikodym square root. Singular laws and roots outside the genuine
closed energy domain have infinite canonical Fisher information, so the
extended-valued statement covers every probability law.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The source logarithmic Sobolev inequality for every actual probability
law, using the genuine closed-gradient relative Fisher functional. -/
theorem logSobolev_relativeFisherInformation
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    klDiv ν (gibbsMeasure volume V) ≤
      relativeFisherInformation hV hp ν / ENNReal.ofReal (2 * ρ) := by
  let := hp
  let μ := gibbsMeasure volume V
  let R := squareRootRNDensityLp ν μ
  let G := closedGibbsGradient hV hp
  by_cases hAC : ν ≪ μ
  · by_cases hD : R ∈ G.domain
    · let D := G ⟨R, hD⟩
      have hgraph : (R, D) ∈ G.graph := G.mem_graph ⟨R, hD⟩
      let v : gibbsSobolevGraph hV hp := ⟨WithLp.toLp 2 (R, D), hgraph⟩
      have hIncl : gibbsSobolevInclusion hV hp v = R := rfl
      have hDeriv : gibbsSobolevDerivative hV hp v = D := rfl
      have hRAE : R =ᵐ[μ] squareRootRNDensity ν μ := (squareRootRNDensity_memLp ν μ).coeFn_toLp
      have hNorm : ‖R‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        calc
          _ = ∫ x, squareRootRNDensity ν μ x ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hRAE] with x hx
            rw [hx, Real.inner_apply]
            ring
          _ = ν.real Set.univ := integral_squareRootRNDensity_sq ν μ hAC
          _ = 1 := by simp
      have hRoot := logSobolev_closed_normalized_root hB hV hp hd ρ hρ hHess v
        (hIncl.symm ▸ hNorm)
      rw [hIncl, hDeriv] at hRoot
      have hKL : klDiv ν μ = ∫⁻ x, ENNReal.ofReal (klFun (R x ^ 2)) ∂μ := by
        rw [klDiv_eq_lintegral_klFun_of_ac hAC]
        apply lintegral_congr_ae
        filter_upwards [hRAE] with x hx
        rw [hx, squareRootRNDensity_sq]
      have hFI := relativeFisherInformation_eq_closed_energy hV hp ν hAC hD
      change relativeFisherInformation hV hp ν = ENNReal.ofReal (4 * ‖D‖ ^ 2) at hFI
      change klDiv ν μ ≤ _
      rw [hKL, hFI]
      apply hRoot.trans_eq
      rw [← ENNReal.ofReal_div_of_pos (show 0 < 2 * ρ by positivity)]
      congr 1
      field_simp
      ring
    · have hTop : relativeFisherInformation hV hp ν = ⊤ := by
        have hAC' : ν ≪ gibbsMeasure volume V := hAC
        have hD' : squareRootRNDensityLp ν (gibbsMeasure volume V) ∉
            (closedGibbsGradient hV hp).domain := hD
        simp only [relativeFisherInformation, hAC', dite_true, hD', dite_false]
      rw [hTop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
      exact le_top
  · rw [relativeFisherInformation_eq_top_of_not_ac hV hp ν hAC,
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact le_top

end CutoffRigidity
