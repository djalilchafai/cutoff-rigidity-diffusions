module
public import CutoffRigidity.ClosedOperatorEnergy
public import CutoffRigidity.RelativeFisherInformation

/-! # Genuine Fisher lower semicontinuity under strong RN-root L² convergence

The actual closed-gradient energy is lower semicontinuous by the proved
Hilbert closed-operator theorem. Absolute continuity identifies canonical
Fisher with that actual energy, without a semicontinuity premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Canonical Fisher is the actual extended closed-operator root energy
on absolutely continuous laws, including roots outside the domain. -/
theorem relativeFisherInformation_eq_closedOperatorFisherEnergy {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsFiniteMeasure ν] (hAC : ν ≪ gibbsMeasure volume V) :
    relativeFisherInformation hV hp ν =
      closedOperatorFisherEnergy (closedGibbsGradient hV hp)
        (squareRootRNDensityLp ν (gibbsMeasure volume V)) := by
  classical
  by_cases hD : squareRootRNDensityLp ν (gibbsMeasure volume V) ∈ (closedGibbsGradient hV hp).domain
  · rw [relativeFisherInformation_eq_closed_energy hV hp ν hAC hD,
      closedOperatorFisherEnergy, closedOperatorNorm, dite_eq_left hD]
    simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (norm_nonneg _)]
  · simp only [relativeFisherInformation, hAC, dite_true, hD, dite_false,
      closedOperatorFisherEnergy, closedOperatorNorm, pow_two, ENNReal.top_mul_top,
      ENNReal.mul_top (by norm_num : (4 : ENNReal) ≠ 0)]

/-- Lower semicontinuity of genuine canonical Fisher information under
actual strong L² convergence of actual RN square-root classes. -/
theorem relativeFisherInformation_le_liminf_of_squareRoot_tendsto {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsFiniteMeasure ν] (νn : ℕ → Measure E) [∀ n, IsFiniteMeasure (νn n)]
    (hAC : ν ≪ gibbsMeasure volume V) (hACn : ∀ n, νn n ≪ gibbsMeasure volume V)
    (hlim : Tendsto (fun n => squareRootRNDensityLp (νn n) (gibbsMeasure volume V)) atTop
      (𝓝 (squareRootRNDensityLp ν (gibbsMeasure volume V)))) :
    relativeFisherInformation hV hp ν ≤ liminf (fun n => relativeFisherInformation hV hp (νn n)) atTop := by
  let G := closedGibbsGradient hV hp
  let R := squareRootRNDensityLp ν (gibbsMeasure volume V)
  let Rn := fun n => squareRootRNDensityLp (νn n) (gibbsMeasure volume V)
  have hLSC := lowerSemicontinuous_closedOperatorFisherEnergy G (closedGibbsGradient_isClosed hV hp)
  have hh := (hLSC.le_liminf R).trans hlim.liminf_le_liminf_comp
  change closedOperatorFisherEnergy G R ≤ liminf (fun n => closedOperatorFisherEnergy G (Rn n)) atTop at hh
  rw [relativeFisherInformation_eq_closedOperatorFisherEnergy hV hp ν hAC]
  have heq (n : ℕ) := relativeFisherInformation_eq_closedOperatorFisherEnergy hV hp (νn n) (hACn n)
  simpa only [heq] using hh

end CutoffRigidity
