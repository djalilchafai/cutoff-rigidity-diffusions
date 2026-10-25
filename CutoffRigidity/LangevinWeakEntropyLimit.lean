module
public import CutoffRigidity.LangevinFeller
public import CutoffRigidity.KLWeakLowerSemicontinuity

/-! # Genuine weak-limit transfer through the actual Langevin kernel

The proved Feller property transports bounded-continuous test convergence.
The full KL variational theorem then gives actual entropy lower
semicontinuity of these transitioned laws, with no density premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_integral_langevinKernel_of_weak
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (νn : ℕ → Measure E) [∀ n, IsProbabilityMeasure (νn n)]
    (hν : ∀ φ : E →ᵇ ℝ, Tendsto (fun n => ∫ x, φ x ∂νn n) atTop (𝓝 (∫ x, φ x ∂ν)))
    (t : NNReal) (φ : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, φ x ∂(langevinKernel V B P t ∘ₘ νn n)) atTop
      (𝓝 (∫ x, φ x ∂(langevinKernel V B P t ∘ₘ ν))) := by
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ hHess t
  let F := fun x : E => ∫ y, φ y ∂K x
  have hFc : Continuous F := continuous_langevinKernel_integral_initial hB hV φ.continuous
    ⟨‖φ‖,fun x => φ.norm_coe_le_norm x⟩ ρ hρ hHess t
  have hFb (x : E) : ‖F x‖ ≤ ‖φ‖ := by
    simpa using norm_integral_le_of_norm_le_const (μ := K x)
      (Eventually.of_forall fun y => φ.norm_coe_le_norm y)
  let ψ := BoundedContinuousFunction.ofNormedAddCommGroup F hFc ‖φ‖ hFb
  have he (ζ : Measure E) (hζ : IsProbabilityMeasure ζ) :
      (∫ x, φ x ∂(K ∘ₘ ζ)) = ∫ x, F x ∂ζ := by
    let := hζ
    have hi : Integrable φ (K ∘ₘ ζ) := (integrable_const ‖φ‖).mono'
      φ.continuous.aestronglyMeasurable (Eventually.of_forall fun y => φ.norm_coe_le_norm y)
    rw [Measure.comp_eq_comp_const_apply] at hi ⊢
    exact Kernel.integral_comp hi
  have hh := hν ψ
  change Tendsto (fun n => ∫ x, F x ∂νn n) atTop (𝓝 (∫ x, F x ∂ν)) at hh
  have hlimit : (∫ x, F x ∂ν) = ∫ x, φ x ∂(K ∘ₘ ν) := (he ν inferInstance).symm
  rw [hlimit] at hh
  apply hh.congr'
  exact Eventually.of_forall fun n => (he (νn n) inferInstance).symm

theorem klDiv_langevinKernel_le_liminf_of_weak
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (νn : ℕ → Measure E) [∀ n, IsProbabilityMeasure (νn n)]
    (hν : ∀ φ : E →ᵇ ℝ, Tendsto (fun n => ∫ x, φ x ∂νn n) atTop (𝓝 (∫ x, φ x ∂ν)))
    (t : NNReal) :
    klDiv (langevinKernel V B P t ∘ₘ ν) (gibbsMeasure volume V) ≤
      liminf (fun n => klDiv (langevinKernel V B P t ∘ₘ νn n) (gibbsMeasure volume V)) atTop := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ hHess t
  apply klDiv_le_liminf_of_boundedContinuous_integrals_tendsto
    (langevinKernel V B P t ∘ₘ ν) (gibbsMeasure volume V)
    (fun n => langevinKernel V B P t ∘ₘ νn n) (fun _ => gibbsMeasure volume V)
  · exact fun φ => tendsto_integral_langevinKernel_of_weak hB hV ρ hρ hHess ν νn hν t φ
  · exact fun φ => tendsto_const_nhds

end CutoffRigidity
