module
public import CutoffRigidity.GibbsCompactWeakH1
public import CutoffRigidity.LocalPoincareGraphLimit
public import CutoffRigidity.GibbsOperatorLocalization

/-! # Actual compact localization of closed Gibbs H¹ vectors

The weak first-order product identity and actual strong mollifier limits
are derived for every genuine H¹ vector, without an operator-domain premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def localizedSobolevGradient {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hp) (χ : E → ℝ) (i : Fin d) (x : E) : ℝ :=
  χ x * gibbsSobolevDerivative hV hp u x i +
    gibbsSobolevInclusion hV hp u x * coordinateDerivative i χ x

theorem localizedSobolevGradient_memLp {V χ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hp) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (i : Fin d) : MemLp (localizedSobolevGradient hV hp u χ i) 2 volume := by
  have ha := compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hp hχ.continuous hχc
    (gibbsSobolevDerivative hV hp u) i
  have hb := compact_cutoff_gibbsLp_memLp_volume hV.continuous hp
    (c1_coordinateDerivative_of_c2 (hχ.of_le (by norm_num)) i).continuous
    (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)) (gibbsSobolevInclusion hV hp u)
  convert! ha.add hb using 1
  funext x
  simp only [localizedSobolevGradient,Pi.add_apply]
  ring

theorem localizedSobolevGradient_first_test {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hprob)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 3 ψ) (_hψc : HasCompactSupport ψ) (i : Fin d) :
    (∫ x, (χ x * gibbsSobolevInclusion hV hprob u x) * coordinateDerivative i ψ x) =
      -(∫ x, localizedSobolevGradient hV hprob u χ i x * ψ x) := by
  let U := gibbsSobolevInclusion hV hprob u
  let G := gibbsSobolevDerivative hV hprob u
  let A (x : E) := (χ x * ψ x) * (G x) i
  let B (x : E) := (coordinateDerivative i χ x * ψ x) * U x
  let D (x : E) := (χ x * coordinateDerivative i ψ x) * U x
  have hA : Integrable A volume := integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hprob
    (hχ.continuous.mul hψ.continuous) (by simpa only [Pi.mul_def] using hχc.mul_right (f' := ψ)) G i
  have hB : Integrable B volume := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
    ((c1_coordinateDerivative_of_c2 (hχ.of_le (by norm_num)) i).continuous.mul hψ.continuous)
    (by simpa only [Pi.mul_def, coordinateDerivative] using
      (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_right (f' := ψ)) U
  have hD : Integrable D volume := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
    (hχ.continuous.mul (c1_coordinateDerivative_of_c2 (hψ.of_le (by norm_num)) i).continuous)
    (by simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative i ψ)) U
  have he := gibbsSobolev_coordinate_weak_derivative_volume hV hprob (hχ.mul (hψ.of_le (by norm_num)))
    (by simpa only [Pi.mul_def] using hχc.mul_right (f' := ψ)) i u
  have hp (x : E) : coordinateDerivative i (fun y => χ y * ψ y) x * U x = B x + D x := by
    rw [coordinateDerivative_mul_actual (hχ.differentiable (by norm_num)) (hψ.differentiable (by norm_num))]
    dsimp [B, D]
    ring
  change (∫ x, A x) = -(∫ x, coordinateDerivative i (fun y => χ y * ψ y) x * U x) at he
  simp_rw [hp] at he
  rw [integral_add hB hD] at he
  have hl : (∫ x, (χ x * gibbsSobolevInclusion hV hprob u x) * coordinateDerivative i ψ x) = ∫ x, D x := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [D]
    ring
  have hr : (∫ x, localizedSobolevGradient hV hprob u χ i x * ψ x) = (∫ x, A x) + ∫ x, B x := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [localizedSobolevGradient, A, B, G, U]
    ring
  rw [hl, hr]
  linarith



/-- Actual localizing weak gradients are assembled as a genuine L² vector. -/
@[expose] noncomputable def localizedSobolevGradientVector {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hp) (χ : E → ℝ) (x : E) : E :=
  WithLp.toLp 2 (fun i => localizedSobolevGradient hV hp u χ i x)

theorem localizedSobolevGradientVector_memLp {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hp) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    MemLp (localizedSobolevGradientVector hV hp u χ) 2 volume := by
  apply MemLp.of_eval_piLp
  intro i
  exact localizedSobolevGradient_memLp hV hp u hχ hχc i

set_option maxHeartbeats 600000 in
/-- The actual compact weak gradient is the strong limit of true classical
mollified gradients, for every closed H¹ vector. -/
theorem gibbsSobolev_localized_mollifiedGradient_tendsto
    {V χ : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hp) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (φ : ℕ → ContDiffBump (0 : E)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    ∃ (hw : LocallyIntegrable (fun x => χ x * gibbsSobolevInclusion hV hp u x) volume)
      (hwc : HasCompactSupport (fun x => χ x * gibbsSobolevInclusion hV hp u x)),
      Tendsto (fun n => mollifiedGradientLp (φ n) _ hw hwc) atTop
        (𝓝 ((localizedSobolevGradientVector_memLp hV hp u hχ hχc).toLp
          (localizedSobolevGradientVector hV hp u χ))) := by
  let w := fun x => χ x * gibbsSobolevInclusion hV hp u x
  let H := fun i => (localizedSobolevGradient_memLp hV hp u hχ hχc i).toLp
    (localizedSobolevGradient hV hp u χ i)
  have hw := (compact_cutoff_gibbsLp_memLp_volume hV.continuous hp hχ.continuous hχc
    (gibbsSobolevInclusion hV hp u)).locallyIntegrable (by norm_num)
  have hwc : HasCompactSupport w := by
    simpa only [w,Pi.mul_def] using hχc.mul_right (f' := fun x => gibbsSobolevInclusion hV hp u x)
  have hh := mollifiedGradientLp_tendsto_of_weak_derivatives φ hφ hw hwc H (by
    intro i ψ hψ hψc
    rw [localizedSobolevGradient_first_test hV hp u hχ hχc hψ hψc i]
    congr 1
    apply integral_congr_ae
    filter_upwards [(localizedSobolevGradient_memLp hV hp u hχ hχc i).coeFn_toLp] with x hx
    rw [hx])
  have heq : euclideanL2Assemble H =
      (localizedSobolevGradientVector_memLp hV hp u hχ hχc).toLp
        (localizedSobolevGradientVector hV hp u χ) := by
    let Q := (localizedSobolevGradientVector_memLp hV hp u hχ hχc).toLp
      (localizedSobolevGradientVector hV hp u χ)
    have hcoords (i : Fin d) : (EuclideanSpace.proj i : E →L[ℝ] ℝ).compLp Q = H i := by
      apply Lp.ext
      filter_upwards [(EuclideanSpace.proj i : E →L[ℝ] ℝ).coeFn_compLp Q,
        (localizedSobolevGradientVector_memLp hV hp u hχ hχc).coeFn_toLp,
        (localizedSobolevGradient_memLp hV hp u hχ hχc i).coeFn_toLp] with x h1 h2 h3
      rw [h1,h2,h3]
      rfl
    rw [← funext hcoords,euclideanL2_assemble_projections]
  rw [heq] at hh
  exact ⟨hw,hwc,hh⟩

end CutoffRigidity
