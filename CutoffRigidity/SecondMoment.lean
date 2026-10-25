module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic
public import CutoffRigidity.Transport

/-!
# Second-moment decomposition

This is the integration step in the proof of Corollary 1.3: for a centered
probability measure the squared distance from a deterministic starting point
is its squared norm plus the second moment. No diffusion estimate is assumed.
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [CompleteSpace E]

theorem centered_second_moment (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : E => x) 2 μ) (hcenter : ∫ x, x ∂μ = 0) (x₀ : E) :
    ∫ x, ‖x - x₀‖ ^ 2 ∂μ = ‖x₀‖ ^ 2 + ∫ x, ‖x‖ ^ 2 ∂μ := by
  have hi : Integrable (fun x : E => x) μ := hμ.integrable (by norm_num)
  have hs : Integrable (fun x : E => ‖x‖ ^ 2) μ := hμ.norm.integrable_sq
  have hc : Integrable (fun x : E => (2 : ℝ) * inner ℝ x x₀) μ :=
    (hi.inner_const x₀).const_mul 2
  simp_rw [norm_sub_sq_real]
  have ha := integral_add (hs.sub hc) (integrable_const (‖x₀‖ ^ 2) (μ := μ))
  simp only [Pi.sub_apply] at ha
  rw [ha]
  have hb := integral_sub hs hc
  rw [hb, integral_const_mul]
  have hinner : ∫ x, inner ℝ x x₀ ∂μ = 0 := by
    calc
      _ = ∫ x, inner ℝ x₀ x ∂μ := integral_congr_ae
        (Filter.Eventually.of_forall (fun x => (real_inner_comm x x₀).symm))
      _ = 0 := by rw [integral_inner hi, hcenter]; simp
  rw [hinner]
  simp [add_comm]

variable [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The genuine coupling infimum from a Dirac measure is the usual real
second moment, embedded in the extended nonnegative reals. -/
theorem squaredWasserstein_dirac_eq_ofReal (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : E => x) 2 μ) (x₀ : E) :
    squaredWasserstein (Measure.dirac x₀) μ =
      ENNReal.ofReal (∫ x, ‖x - x₀‖ ^ 2 ∂μ) := by
  rw [squaredWasserstein_dirac]
  have hs : Integrable (fun x : E => ‖x - x₀‖ ^ 2) μ :=
    (hμ.sub (memLp_const x₀)).norm.integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hs (Filter.Eventually.of_forall
    (fun x => sq_nonneg ‖x - x₀‖))]
  apply lintegral_congr
  intro x
  rw [edist_dist, dist_comm, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _) ]

/-- The deterministic starting-point formula in the centered setting of
Corollary 1.3, now expressed using the actual quadratic transport infimum. -/
theorem squaredWasserstein_dirac_centered (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : E => x) 2 μ) (hcenter : ∫ x, x ∂μ = 0) (x₀ : E) :
    squaredWasserstein (Measure.dirac x₀) μ =
      ENNReal.ofReal (‖x₀‖ ^ 2 + ∫ x, ‖x‖ ^ 2 ∂μ) := by
  rw [squaredWasserstein_dirac_eq_ofReal μ hμ, centered_second_moment μ hμ hcenter]

end CutoffRigidity
