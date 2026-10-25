module
public import CutoffRigidity.DistributionalLaplacianApproximation
public import CutoffRigidity.WeakH1Mollification

/-! # Genuine first and second order approximation of localized A-domain vectors -/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual weak first-gradient product rule for every localized full
operator-domain vector, derived directly from its weighted weak gradient. -/
theorem localizedOperatorGraphGradient_first_test {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 3 ψ) (_hψc : HasCompactSupport ψ) (i : Fin d) :
    (∫ x, (χ x * u x) * coordinateDerivative i ψ x) =
      -(∫ x, localizedOperatorGraphGradient hV hprob u g χ i x * ψ x) := by
  let v := gibbsOperatorGraphSobolevLift hV hprob u g
  let G := gibbsSobolevDerivative hV hprob v
  let A (x : E) := (χ x * ψ x) * (G x) i
  let B (x : E) := (coordinateDerivative i χ x * ψ x) * u x
  let D (x : E) := (χ x * coordinateDerivative i ψ x) * u x
  have hA : Integrable A volume := integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hprob
    (hχ.continuous.mul hψ.continuous) (by simpa only [Pi.mul_def] using hχc.mul_right (f' := ψ)) G i
  have hB : Integrable B volume := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
    ((c1_coordinateDerivative_of_c2 (hχ.of_le (by norm_num)) i).continuous.mul hψ.continuous)
    (by simpa only [Pi.mul_def, coordinateDerivative] using
      (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_right (f' := ψ)) u
  have hD : Integrable D volume := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
    (hχ.continuous.mul (c1_coordinateDerivative_of_c2 (hψ.of_le (by norm_num)) i).continuous)
    (by simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative i ψ)) u
  have he := gibbsSobolev_coordinate_weak_derivative_volume hV hprob ((hχ.mul hψ).of_le (by norm_num))
    (by simpa only [Pi.mul_def] using hχc.mul_right (f' := ψ)) i v
  rw [gibbsOperatorGraphSobolevLift_inclusion hV hprob u g hug] at he
  have hp (x : E) : coordinateDerivative i (fun y => χ y * ψ y) x * u x = B x + D x := by
    rw [coordinateDerivative_mul_actual (hχ.differentiable (by norm_num)) (hψ.differentiable (by norm_num))]
    dsimp [B, D]
    ring
  change (∫ x, A x) = -(∫ x, coordinateDerivative i (fun y => χ y * ψ y) x * u x) at he
  simp_rw [hp] at he
  rw [integral_add hB hD] at he
  have hl : (∫ x, (χ x * u x) * coordinateDerivative i ψ x) = ∫ x, D x := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [D]
    ring
  have hr : (∫ x, localizedOperatorGraphGradient hV hprob u g χ i x * ψ x) = (∫ x, A x) + ∫ x, B x := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [localizedOperatorGraphGradient, A, B, G, v]
    ring
  rw [hl, hr]
  linarith

/-- The actual smoothed classical gradients converge strongly to the
localized weak gradient, with every source identity derived from A.graph. -/
theorem gibbsOperatorGraph_mollifiedGradient_tendsto
    {V χ : E → ℝ} (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (φ : ℕ → ContDiffBump (0 : E)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    ∃ (hw : LocallyIntegrable (fun x => χ x * u x) volume)
      (hwc : HasCompactSupport (fun x => χ x * u x)),
      Tendsto (fun n => mollifiedGradientLp (φ n) (fun x => χ x * u x) hw hwc) atTop
        (𝓝 (euclideanL2Assemble (fun i =>
          (localizedOperatorGraphGradient_memLp hV hprob u g hχ hχc i).toLp
            (localizedOperatorGraphGradient hV hprob u g χ i)))) := by
  have hw := (compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ.continuous hχc u).locallyIntegrable (by norm_num)
  have hwc : HasCompactSupport (fun x => χ x * u x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := fun x => u x)
  refine ⟨hw, hwc, mollifiedGradientLp_tendsto_of_weak_derivatives φ hφ hw hwc _ ?_⟩
  intro i ψ hψ hψc
  rw [localizedOperatorGraphGradient_first_test hV hprob u g hug hχ hχc hψ hψc i]
  congr 1
  apply integral_congr_ae
  filter_upwards [(localizedOperatorGraphGradient_memLp hV hprob u g hχ hχc i).coeFn_toLp] with x hx
  rw [hx]

theorem localizedOperatorGraphLaplacian_measurable
    {V χ : E → ℝ} (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ) (hχ : ContDiff ℝ 3 χ) :
    Measurable (localizedOperatorGraphLaplacian hV hprob u g χ) := by
  have huM := (Lp.stronglyMeasurable u).measurable
  have hgM := (Lp.stronglyMeasurable g).measurable
  have hGM := (Lp.stronglyMeasurable (gibbsSobolevDerivative hV hprob
    (gibbsOperatorGraphSobolevLift hV hprob u g))).measurable
  have hGV := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hGχ := continuous_gradient_of_c1 (hχ.of_le (by norm_num))
  have hLap := (euclideanLaplacian_contDiff_one hχ).continuous
  have hχm := hχ.continuous.measurable
  unfold localizedOperatorGraphLaplacian
  fun_prop

end CutoffRigidity
