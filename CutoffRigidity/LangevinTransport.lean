module

public import CutoffRigidity.LangevinPath
public import CutoffRigidity.RandomMapTransport
public import CutoffRigidity.SecondMoment

/-!
# Quadratic transport contraction from actual Langevin trajectories

The input is a measurable update obtained from actual solutions of the
integral equation driven by the same noise. Curvature gives the pathwise
bound and the coupling construction gives transport contraction. For an
invariant law this yields the upper bound used in Theorem 1.1.

Measurability and invariance are explicit properties of the input model;
they are not asserted here for the selected Brownian solution family.
-/

public section

open MeasureTheory
open scoped NNReal ENNReal

namespace CutoffRigidity

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω]

theorem langevin_update_transport_contraction
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (η : Measure Ω) [IsProbabilityMeasure η]
    (w : Ω → ℝ → E) (X : E → Ω → ℝ → E) {t : ℝ} (ht : 0 ≤ t)
    (hX : ∀ x ω, IsLangevinPathOn V (w ω) x (X x ω) t)
    (hMeas : Measurable (fun z : E × Ω => X z.1 z.2 t))
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    squaredWasserstein
      (randomMapLaw μ η (fun z => X z.1 z.2 t))
      (randomMapLaw ν η (fun z => X z.1 z.2 t)) ≤
      ENNReal.ofReal (Real.exp (-2 * rate * t)) * squaredWasserstein μ ν := by
  let K : ℝ≥0 := ⟨Real.exp (-rate * t), Real.exp_nonneg _⟩
  have hcoeff : (K : ℝ) = Real.exp (-rate * t) := rfl
  have hLip (ω : Ω) : LipschitzWith K (fun x => X x ω t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, hcoeff]
    exact langevin_same_noise_contraction hV rate hHess (hX x ω) (hX y ω) ht
  have h := squaredWasserstein_randomMap_le μ ν η _ hMeas K hLip
  have hK : (K : ℝ≥0∞) ^ 2 = ENNReal.ofReal (Real.exp (-2 * rate * t)) := by
    rw [show (K : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-rate * t)) from
      (ENNReal.ofReal_coe_nnreal (p := K)).symm,
      ← ENNReal.ofReal_pow (Real.exp_nonneg _) 2]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hK] at h

/-- The main upper estimate for a genuinely invariant probability law, with
the deterministic-start transport cost written as its actual second moment. -/
theorem invariant_langevin_update_upper_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (η : Measure Ω) [IsProbabilityMeasure η]
    (w : Ω → ℝ → E) (X : E → Ω → ℝ → E) {t : ℝ} (ht : 0 ≤ t)
    (hX : ∀ x ω, IsLangevinPathOn V (w ω) x (X x ω) t)
    (hMeas : Measurable (fun z : E × Ω => X z.1 z.2 t))
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : E => x) 2 μ)
    (hInvariant : randomMapLaw μ η (fun z => X z.1 z.2 t) = μ) (x₀ : E) :
    squaredWasserstein
      (randomMapLaw (Measure.dirac x₀) η (fun z => X z.1 z.2 t)) μ ≤
      ENNReal.ofReal (Real.exp (-2 * rate * t) * ∫ x, ‖x - x₀‖ ^ 2 ∂μ) := by
  have h := langevin_update_transport_contraction hV rate hHess η w X ht hX hMeas
    (Measure.dirac x₀) μ
  rw [hInvariant, squaredWasserstein_dirac_eq_ofReal μ hμ x₀] at h
  simpa only [ENNReal.ofReal_mul (Real.exp_nonneg _)] using h

end CutoffRigidity
