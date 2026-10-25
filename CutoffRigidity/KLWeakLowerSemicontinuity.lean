module
public import CutoffRigidity.KLCompactVariational

/-! # Genuine weak lower semicontinuity of relative entropy

The proved compact C² variational formula gives joint lower
semicontinuity from actual test integral convergence. A full bounded
continuous variational representation is also obtained, without an LSC
or representation premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory InformationTheory Filter Set Topology
open scoped ENNReal BoundedContinuousFunction
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The genuine bounded-continuous exponential variational formula for
actual KL, including singular laws and infinite values. -/
theorem klDiv_eq_iSup_boundedContinuous_tests
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] :
    klDiv ν μ = ⨆ φ : E →ᵇ ℝ, ENNReal.ofReal (relativeEntropyTest ν μ φ) := by
  apply le_antisymm
  · apply klDiv_le_of_compact_c2_tests
    intro φ hφ hφc
    obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ.continuous
    let Φ : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup φ hφ.continuous M hM
    exact le_iSup (fun ψ : E →ᵇ ℝ => ENNReal.ofReal (relativeEntropyTest ν μ ψ)) Φ
  · apply iSup_le
    intro φ
    exact relativeEntropyTest_le_klDiv ν μ φ.continuous.measurable
      ⟨‖φ‖, fun x => φ.norm_coe_le_norm x⟩

/-- A compact C² exponential test can be written using only compact C²
test integrals under both probability measures. -/
private theorem relativeEntropyTest_eq_compact_integrals
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    relativeEntropyTest ν μ φ = (∫ x, φ x ∂ν) - ∫ x, (Real.exp (φ x) - 1) ∂μ := by
  have hψ : ContDiff ℝ 2 (fun x => Real.exp (φ x) - 1) := hφ.exp.sub contDiff_const
  have hψc : HasCompactSupport (fun x => Real.exp (φ x) - 1) :=
    hφc.comp_left (g := fun s : ℝ => Real.exp s - 1) (by simp)
  have hi : Integrable (fun x => Real.exp (φ x) - 1) μ := hψ.continuous.integrable_of_hasCompactSupport hψc
  have heq : (fun x => Real.exp (φ x)) = fun x => (Real.exp (φ x) - 1) + 1 := by funext x; ring
  rw [relativeEntropyTest, heq, integral_add hi (integrable_const 1)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-- Joint genuine weak lower semicontinuity of actual KL. Convergence
of actual compact C² test integrals suffices; no entropy bound or LSC
conclusion is supplied as a premise. -/
theorem klDiv_le_liminf_of_compact_c2_integrals_tendsto
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (νn μn : ℕ → Measure E) [∀ n, IsProbabilityMeasure (νn n)] [∀ n, IsProbabilityMeasure (μn n)]
    (hν : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x, φ x ∂νn n) atTop (𝓝 (∫ x, φ x ∂ν)))
    (hμ : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x, φ x ∂μn n) atTop (𝓝 (∫ x, φ x ∂μ))) :
    klDiv ν μ ≤ liminf (fun n => klDiv (νn n) (μn n)) atTop := by
  apply klDiv_le_of_compact_c2_tests
  intro φ hφ hφc
  let ψ := fun x => Real.exp (φ x) - 1
  have hψ : ContDiff ℝ 2 ψ := hφ.exp.sub contDiff_const
  have hψc : HasCompactSupport ψ := hφc.comp_left (g := fun s : ℝ => Real.exp s - 1) (by simp)
  have hlim : Tendsto (fun n => relativeEntropyTest (νn n) (μn n) φ) atTop
      (𝓝 (relativeEntropyTest ν μ φ)) := by
    have hh := (hν φ hφ hφc).sub (hμ ψ hψ hψc)
    simpa only [relativeEntropyTest_eq_compact_integrals _ _ hφ hφc, ψ] using hh
  have hEnn : Tendsto (fun n => ENNReal.ofReal (relativeEntropyTest (νn n) (μn n) φ)) atTop
      (𝓝 (ENNReal.ofReal (relativeEntropyTest ν μ φ))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hb : ∀ n, ENNReal.ofReal (relativeEntropyTest (νn n) (μn n) φ) ≤ klDiv (νn n) (μn n) :=
    fun n => relativeEntropyTest_le_klDiv (νn n) (μn n) hφ.continuous.measurable
      (hφc.exists_bound_of_continuous hφ.continuous)
  have hh : liminf (fun n => ENNReal.ofReal (relativeEntropyTest (νn n) (μn n) φ)) atTop ≤
      liminf (fun n => klDiv (νn n) (μn n)) atTop := liminf_le_liminf (Eventually.of_forall hb)
  rwa [hEnn.liminf_eq] at hh

/-- Standard bounded-continuous weak convergence in both arguments gives
joint lower semicontinuity of genuine relative entropy. -/
theorem klDiv_le_liminf_of_boundedContinuous_integrals_tendsto
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (νn μn : ℕ → Measure E) [∀ n, IsProbabilityMeasure (νn n)] [∀ n, IsProbabilityMeasure (μn n)]
    (hν : ∀ φ : E →ᵇ ℝ, Tendsto (fun n => ∫ x, φ x ∂νn n) atTop (𝓝 (∫ x, φ x ∂ν)))
    (hμ : ∀ φ : E →ᵇ ℝ, Tendsto (fun n => ∫ x, φ x ∂μn n) atTop (𝓝 (∫ x, φ x ∂μ))) :
    klDiv ν μ ≤ liminf (fun n => klDiv (νn n) (μn n)) atTop := by
  apply klDiv_le_liminf_of_compact_c2_integrals_tendsto ν μ νn μn
  · intro φ hφ hφc
    obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ.continuous
    exact hν (BoundedContinuousFunction.ofNormedAddCommGroup φ hφ.continuous M hM)
  · intro φ hφ hφc
    obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ.continuous
    exact hμ (BoundedContinuousFunction.ofNormedAddCommGroup φ hφ.continuous M hM)

end CutoffRigidity
