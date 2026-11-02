module

public import CutoffRigidity.Extra.GaussIso13

/-! # Isoperimetry for sets (stage 7a): smooth `1`-Lipschitz approximation of a `1`-Lipschitz function -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ContDiff Convolution

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A `1`-Lipschitz function is uniformly approximated, within `δ`, by a `C^∞` `1`-Lipschitz function. -/
theorem exists_smooth_lipschitz_approx {e : E → ℝ} (he : LipschitzWith 1 e) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith 1 u ∧ ∀ x, |u x - e x| ≤ δ := by
  let φ : ContDiffBump (0 : E) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let κ : E → ℝ := φ.normed volume
  have hκc : Continuous κ := φ.continuous_normed
  have hκsupp : HasCompactSupport κ := φ.hasCompactSupport_normed
  have hint : ∀ x : E, Integrable (fun t => κ t * e (x - t)) := by
    intro x
    refine Continuous.integrable_of_hasCompactSupport (hκc.mul (he.continuous.comp (by fun_prop))) ?_
    exact hκsupp.mul_right
  refine ⟨κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e, ?_, ?_, ?_⟩
  · exact hκsupp.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed
      he.continuous.locallyIntegrable
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 : ∀ z, (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] e) z = ∫ t, κ t * e (z - t) := fun z => rfl
    rw [h1, h1, Real.dist_eq, ← integral_sub (hint x) (hint y)]
    have hb : ∀ t, |κ t * e (x - t) - κ t * e (y - t)| ≤ κ t * dist x y := by
      intro t
      rw [← mul_sub, abs_mul, abs_of_nonneg (φ.nonneg_normed t)]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
      have := he.dist_le_mul (x - t) (y - t)
      simpa [Real.dist_eq, dist_sub_right] using this
    calc |∫ t, (κ t * e (x - t) - κ t * e (y - t))| ≤ ∫ t, κ t * dist x y := by
          have := norm_integral_le_of_norm_le (μ := volume)
            (f := fun t => κ t * e (x - t) - κ t * e (y - t)) (g := fun t => κ t * dist x y)
            ((φ.integrable_normed).mul_const _) (Eventually.of_forall fun t => by simpa using hb t)
          simpa using this
      _ = dist x y := by
          rw [integral_mul_const]; simp [κ, φ.integral_normed]
      _ = ((1:ℝ≥0) : ℝ) * dist x y := by simp
  · intro x
    have := φ.dist_normed_convolution_le (μ := volume) (g := e) (x₀ := x) (ε := δ)
      he.continuous.aestronglyMeasurable (fun y hy => by
        have := he.dist_le_mul y x
        simp only [NNReal.coe_one, one_mul] at this
        exact this.trans (mem_ball.1 hy).le)
    simpa [Real.dist_eq] using this

end CutoffRigidity.GaussIso
