module
public import CutoffRigidity.KLVariationalMeasure
public import CutoffRigidity.CompactC2MeasureApproximation

/-! # Actual KL is determined by genuine compact C² exponential tests

Simultaneous approximation under the actual two probability measures and
uniformly bounded smooth tests extends the proved measurable variational
criterion. Neither absolute continuity nor finite KL is required.
-/
public section
namespace CutoffRigidity
open MeasureTheory InformationTheory Filter Set Topology
open scoped ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The genuine compact C² exponential-test criterion for full actual KL.
This includes singular laws and infinite relative entropy. -/
theorem klDiv_le_of_compact_c2_tests
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (C : ENNReal)
    (hTest : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ENNReal.ofReal (relativeEntropyTest ν μ φ) ≤ C) : klDiv ν μ ≤ C := by
  apply klDiv_le_of_bounded_measurable_tests ν μ C
  intro φ hφ hBound
  obtain ⟨M, hM⟩ := hBound
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0)
  let τ := ν + μ
  have hφI : Integrable φ τ := (integrable_const M).mono' hφ.aestronglyMeasurable (Eventually.of_forall hM)
  obtain ⟨ψ, hψ, hψc, hψB, hL1⟩ := exists_bounded_compact_c2_L1_approx τ hφ M hM0 hM
  have hψI (n : ℕ) : Integrable (ψ n) τ :=
    (integrable_const (M + 1)).mono' (hψ n).continuous.aestronglyMeasurable (Eventually.of_forall (hψB n))
  have hELim : Tendsto (fun n => eLpNorm (ψ n - φ) 1 τ) atTop (𝓝 0) := by
    have hl := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL1
    have heq (n : ℕ) : eLpNorm (ψ n - φ) 1 τ = ENNReal.ofReal (∫ x, ‖φ x - ψ n x‖ ∂τ) := by
      rw [eLpNorm_one_eq_lintegral_enorm ((hψI n).sub hφI).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm ((hψI n).sub hφI)]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      simp only [Pi.sub_apply, norm_sub_rev]
    simpa only [heq, ENNReal.ofReal_zero, Function.comp_def] using hl
  have hIM := tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ENNReal)) (by norm_num) hELim
  obtain ⟨ns, hns, hAE⟩ := hIM.exists_seq_tendsto_ae'
  have hντ : ν ≪ τ := (show ν ≤ τ from le_add_of_nonneg_right (show 0 ≤ μ from bot_le)).absolutelyContinuous
  have hμτ : μ ≪ τ := (show μ ≤ τ from le_add_of_nonneg_left (show 0 ≤ ν from bot_le)).absolutelyContinuous
  have hAEν : ∀ᵐ x ∂ν, Tendsto (fun n => ψ (ns n) x) atTop (𝓝 (φ x)) :=
    hντ.ae_le hAE
  have hAEμ : ∀ᵐ x ∂μ, Tendsto (fun n => ψ (ns n) x) atTop (𝓝 (φ x)) :=
    hμτ.ae_le hAE
  have hνLim : Tendsto (fun n => ∫ x, ψ (ns n) x ∂ν) atTop (𝓝 (∫ x, φ x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M + 1)
      (fun n => (hψ (ns n)).continuous.aestronglyMeasurable) (integrable_const _) ?_ hAEν
    intro n
    exact Eventually.of_forall (hψB (ns n))
  have hμLim : Tendsto (fun n => ∫ x, Real.exp (ψ (ns n) x) ∂μ) atTop
      (𝓝 (∫ x, Real.exp (φ x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp (M + 1))
      (fun n => (Real.continuous_exp.comp (hψ (ns n)).continuous).aestronglyMeasurable) (integrable_const _) ?_ ?_
    · intro n
      apply Eventually.of_forall
      intro x
      rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hψB (ns n) x))
    · filter_upwards [hAEμ] with x hx
      exact Real.continuous_exp.continuousAt.tendsto.comp hx
  have hBudget : Tendsto (fun n => ENNReal.ofReal (relativeEntropyTest ν μ (ψ (ns n)))) atTop
      (𝓝 (ENNReal.ofReal (relativeEntropyTest ν μ φ))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hνLim.sub hμLim).add_const 1)
  exact le_of_tendsto hBudget (Eventually.of_forall (fun n => hTest (ψ (ns n)) (hψ (ns n)) (hψc (ns n))))

/-- Exact compact C² exponential variational representation of actual KL. -/
theorem klDiv_eq_iSup_compact_c2_tests
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] :
    klDiv ν μ = ⨆ φ : {φ : E → ℝ // ContDiff ℝ 2 φ ∧ HasCompactSupport φ},
      ENNReal.ofReal (relativeEntropyTest ν μ φ) := by
  apply le_antisymm
  · apply klDiv_le_of_compact_c2_tests
    intro φ hφ hφc
    exact le_iSup (fun ψ : {φ : E → ℝ // ContDiff ℝ 2 φ ∧ HasCompactSupport φ} =>
      ENNReal.ofReal (relativeEntropyTest ν μ ψ)) ⟨φ, hφ, hφc⟩
  · apply iSup_le
    intro φ
    exact relativeEntropyTest_le_klDiv ν μ φ.property.1.continuous.measurable
      (φ.property.2.exists_bound_of_continuous φ.property.1.continuous)

end CutoffRigidity
