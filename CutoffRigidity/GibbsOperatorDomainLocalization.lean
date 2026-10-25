module

public import CutoffRigidity.GibbsOperatorDomainPDE
public import CutoffRigidity.GibbsOperatorLocalization
public import CutoffRigidity.HessianDistributionRepresentation

/-! # Local weak H² estimates on the full actual operator domain

Compact localization converts the genuine distributional equation for an
actual graph pair (u,g) into a global L² Laplace equation. The actual smooth
mollifications consequently have uniformly bounded Hessian energy. Neither
an eigenfunction equation nor a classical representative is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual lower-order source after compactly localizing an operator-domain pair. -/
@[expose] noncomputable def localizedOperatorGraphLaplacian {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u g : E →₂[gibbsMeasure volume V] ℝ) (χ : E → ℝ) (x : E) : ℝ :=
  χ x * (inner ℝ (gradient V x)
    (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x) -
      g x) +
    2 * inner ℝ (gradient χ x)
      (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x) +
        (u : E →₂[gibbsMeasure volume V] ℝ) x * euclideanLaplacian χ x

/-- The actual localized weak Laplace equation for every operator-domain pair.
The input has no classical differentiability assumption. -/
theorem gibbsOperatorGraph_localized_distributional_laplacian {V χ φ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u,g) ∈ (gibbsPositiveGenerator hV hprob).graph)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hφ : ContDiff ℝ 3 φ) (hφc : HasCompactSupport φ) :
    (∫ x, (χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) * euclideanLaplacian φ x) =
      ∫ x, localizedOperatorGraphLaplacian hV hprob u g χ x * φ x := by
  let v := gibbsOperatorGraphSobolevLift hV hprob u g
  let U : E → ℝ := fun x => (u : E →₂[gibbsMeasure volume V] ℝ) x
  let G := gibbsSobolevDerivative hV hprob v
  have hGχ : Continuous (gradient χ) := continuous_gradient_of_c1 (hχ.of_le (by norm_num))
  have hGφ : Continuous (gradient φ) := continuous_gradient_of_c1 (hφ.of_le (by norm_num))
  have hGV : Continuous (gradient V) := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hχφ : ContDiff ℝ 2 (fun x => χ x * φ x) := (hχ.mul hφ).of_le (by norm_num)
  have hχφc : HasCompactSupport (fun x => χ x * φ x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := φ)
  let A (x : E) := χ x * inner ℝ (G x) (gradient φ x)
  let B (x : E) := φ x * inner ℝ (G x) (gradient χ x)
  let D (x : E) := (χ x * φ x) * inner ℝ (G x) (gradient V x)
  let N (x : E) := g x * χ x * φ x
  let Eterm (x : E) := U x * φ x * euclideanLaplacian χ x
  have hA : Integrable A volume := integrable_compact_coeff_inner_gibbsVector_volume
    hV.continuous hprob hχ.continuous hχc hGφ G
  have hB : Integrable B volume := integrable_compact_coeff_inner_gibbsVector_volume
    hV.continuous hprob hφ.continuous hφc hGχ G
  have hD : Integrable D volume := integrable_compact_coeff_inner_gibbsVector_volume
    hV.continuous hprob (hχ.continuous.mul hφ.continuous) hχφc hGV G
  have hN : Integrable N volume := by
    have hh := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (hχ.continuous.mul hφ.continuous) hχφc g
    simpa only [N, U, Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using hh
  have hE : Integrable Eterm volume := by
    have hc : Continuous (fun x => φ x * euclideanLaplacian χ x) :=
      hφ.continuous.mul (euclideanLaplacian_contDiff_one hχ).continuous
    have hs : HasCompactSupport (fun x => φ x * euclideanLaplacian χ x) := by
      simpa only [Pi.mul_def] using hφc.mul_right (f' := euclideanLaplacian χ)
    have hh := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob hc hs
      (u : E →₂[gibbsMeasure volume V] ℝ)
    simpa only [Eterm, U, mul_comm, mul_left_comm, mul_assoc] using hh
  have he := gibbsOperatorGraph_volume_test_equation hV hprob u g hug hχφ hχφc
  have hp (x : E) : inner ℝ (G x) (gradient (fun y => χ y * φ y) x + (χ x * φ x) • gradient V x) =
      A x + B x + D x := by
    rw [gradient_cutoff_mul (hχ.differentiable (by norm_num)) (hφ.differentiable (by norm_num))]
    simp only [inner_add_right, inner_smul_right]
    rfl
  change (∫ x, inner ℝ (G x) (gradient (fun y => χ y * φ y) x + (χ x * φ x) • gradient V x)) = _ at he
  simp_rw [hp] at he
  have ha := integral_add (hA.add hB) hD
  simp only [Pi.add_apply] at ha
  rw [ha, integral_add hA hB] at he
  have he' : (∫ x, A x) + (∫ x, B x) + (∫ x, D x) = (∫ x, N x) := by
    simpa only [N, U, mul_assoc] using he
  have hl := gibbsSobolev_cutoff_laplacian_test hV hprob v hχ hχc hφ hφc
  rw [gibbsOperatorGraphSobolevLift_inclusion hV hprob u g hug] at hl
  change (∫ x, χ x * U x * euclideanLaplacian φ x) =
    -(∫ x, A x) + (∫ x, B x) + (∫ x, Eterm x) at hl
  have hr : (∫ x, localizedOperatorGraphLaplacian hV hprob u g χ x * φ x) =
      2 * (∫ x, B x) + (∫ x, D x) - (∫ x, N x) + (∫ x, Eterm x) := by
    have hp' (x : E) : localizedOperatorGraphLaplacian hV hprob u g χ x * φ x =
        (2 * B x + D x - N x) + Eterm x := by
      dsimp only [localizedOperatorGraphLaplacian, B, D, N, Eterm, U, G, v]
      rw [real_inner_comm (gradient χ x), real_inner_comm (gradient V x)]
      ring
    simp_rw [hp']
    have ha1 := integral_add (((hB.const_mul 2).add hD).sub hN) hE
    have hs1 := integral_sub ((hB.const_mul 2).add hD) hN
    have ha2 := integral_add (hB.const_mul 2) hD
    simp only [Pi.add_apply, Pi.sub_apply] at ha1 hs1 ha2
    rw [ha1, hs1, ha2, integral_const_mul]
  rw [hr]
  change (∫ x, χ x * U x * euclideanLaplacian φ x) = _
  linarith

/-- The actual localized distributional Laplacian is genuinely Lebesgue L². -/
theorem localizedOperatorGraphLaplacian_memLp {V χ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u g : E →₂[gibbsMeasure volume V] ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) :
    MemLp (localizedOperatorGraphLaplacian hV hprob u g χ) 2 volume := by
  let G := gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g)
  have hLower := gibbsOperatorGraph_local_rhs_memLp hV hprob u g hχ.continuous hχc
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by norm_num)
  have hCross : MemLp (fun x => inner ℝ (gradient χ x) (G x)) 2 volume := by
    have hi (i : Fin d) : MemLp (fun x => coordinateDerivative i χ x * (G x) i) 2 volume :=
      compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hprob
        (c1_coordinateDerivative_of_c2 hχ2 i).continuous
        (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)) G i
    have hh := memLp_finsetSum Finset.univ (fun i _ => hi i)
    convert hh using 1
    funext x
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply, coordinateDerivative, fderiv_single_eq_gradient_coordinate]
  have hLapc : HasCompactSupport (euclideanLaplacian χ) := by
    have hh := hasCompactSupport_langevinDifferentialOperator (fun _ : E => (0 : ℝ)) hχc
    have hL : langevinDifferentialOperator (fun _ : E => (0 : ℝ)) χ = euclideanLaplacian χ := by
      funext x
      simp [langevinDifferentialOperator, gradient_fun_const]
    rw [← hL]
    exact hh
  have hLap := compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob
    (euclideanLaplacian_contDiff_one hχ).continuous hLapc (u : E →₂[gibbsMeasure volume V] ℝ)
  convert (hLower.add (hCross.const_mul 2)).add hLap using 1
  funext x
  dsimp only [localizedOperatorGraphLaplacian, G]
  simp only [Pi.add_apply]
  ring

/-- The actual operator-domain localization has uniformly L²-bounded Hessians
under every actual smooth compact mollification. This is the concrete local
weak H² estimate, derived without assuming a classical representative. -/
theorem gibbsOperatorGraph_mollified_local_hessian_energy_le {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u,g) ∈ (gibbsPositiveGenerator hV hprob).graph) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (φ : ContDiffBump (0 : E)) :
    (∫ x, ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i (bumpMollification φ
        (fun y => χ y * (u : E →₂[gibbsMeasure volume V] ℝ) y))) x) ^ 2) ≤
      ∫ x, localizedOperatorGraphLaplacian hV hprob u g χ x ^ 2 := by
  have hwLp := compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ.continuous hχc
    (u : E →₂[gibbsMeasure volume V] ℝ)
  have hwc : HasCompactSupport (fun x => χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := fun x => (u : E →₂[gibbsMeasure volume V] ℝ) x)
  have hFm : Measurable (localizedOperatorGraphLaplacian hV hprob u g χ) := by
    have huM : Measurable (fun x => (u : E →₂[gibbsMeasure volume V] ℝ) x) :=
      (Lp.stronglyMeasurable (u : E →₂[gibbsMeasure volume V] ℝ)).measurable
    have hGM : Measurable (fun x => gibbsSobolevDerivative hV hprob
        (gibbsOperatorGraphSobolevLift hV hprob u g) x) :=
      (Lp.stronglyMeasurable (gibbsSobolevDerivative hV hprob
        (gibbsOperatorGraphSobolevLift hV hprob u g))).measurable
    have hGV := continuous_gradient_of_c1 (hV.of_le (by norm_num))
    have hGχ := continuous_gradient_of_c1 (hχ.of_le (by norm_num))
    have hLap := (euclideanLaplacian_contDiff_one hχ).continuous
    have hχm := hχ.continuous.measurable
    unfold localizedOperatorGraphLaplacian
    fun_prop
  apply mollified_distributional_hessian_energy_le (hwLp.locallyIntegrable (by norm_num)) hwc hFm
    (localizedOperatorGraphLaplacian_memLp hV hprob u g hχ hχc)
  intro ψ hψ hψc
  exact gibbsOperatorGraph_localized_distributional_laplacian hV hprob u g hug hχ hχc hψ hψc


/-- Every actual operator-domain pair has genuine local Lebesgue L²
second-derivative representatives. The norm bound follows from its actual
localized Laplace source, with no H² regularity premise. -/
theorem exists_gibbsOperatorGraph_local_weak_hessian {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (i j : Fin d) :
    ∃ H : E →₂[volume] ℝ,
      ‖H‖ ≤ ‖(localizedOperatorGraphLaplacian_memLp hV hprob u g hχ hχc).toLp
        (localizedOperatorGraphLaplacian hV hprob u g χ)‖ ∧
      ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
        (∫ x, (χ x * u x) * coordinateDerivative j (coordinateDerivative i ψ) x) =
          ∫ x, H x * ψ x := by
  let v := gibbsOperatorGraphSobolevLift hV hprob u g
  let w (x : E) := χ x * u x
  let F := localizedOperatorGraphLaplacian hV hprob u g χ
  have hwm : Measurable w := hχ.continuous.measurable.mul (Lp.stronglyMeasurable u).measurable
  have hw : MemLp w 2 volume := compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob
    hχ.continuous hχc u
  have hwc : HasCompactSupport w := by
    simpa only [w, Pi.mul_def] using hχc.mul_right (f' := fun x => u x)
  have hFm : Measurable F := by
    have huM := (Lp.stronglyMeasurable u).measurable
    have hgM := (Lp.stronglyMeasurable g).measurable
    have hGM := (Lp.stronglyMeasurable (gibbsSobolevDerivative hV hprob v)).measurable
    have hGV := continuous_gradient_of_c1 (hV.of_le (by norm_num))
    have hGχ := continuous_gradient_of_c1 (hχ.of_le (by norm_num))
    have hLap := (euclideanLaplacian_contDiff_one hχ).continuous
    have hχm := hχ.continuous.measurable
    dsimp only [F]
    unfold localizedOperatorGraphLaplacian
    fun_prop
  have hF : MemLp F 2 volume := localizedOperatorGraphLaplacian_memLp hV hprob u g hχ hχc
  obtain ⟨K, hK, hKt⟩ := exists_gibbsSobolev_cutoff_translation_integral_bound hV hprob
    (hχ.of_le (by norm_num)) hχc
  let C := Real.sqrt K * ‖v‖
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have htrans (h : E) : (∫ x, (w (x + h) - w x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2 := by
    have ht := hKt v h
    rw [gibbsOperatorGraphSobolevLift_inclusion hV hprob u g hug] at ht
    have hc : C ^ 2 = K * ‖v‖ ^ 2 := by
      dsimp [C]
      rw [mul_pow, Real.sq_sqrt hK.le]
    rw [hc]
    simpa only [w, mul_assoc, mul_left_comm, mul_comm] using ht
  apply exists_L2_second_derivative_of_distributional_laplacian hwm hw hwc hFm hF C hC htrans
  intro ψ hψ hψc
  exact gibbsOperatorGraph_localized_distributional_laplacian hV hprob u g hug hχ hχc hψ hψc

/-- The actual localized first-gradient coordinate (the genuine product rule
for the weak gradient, expressed as a pointwise measurable representative). -/
@[expose] noncomputable def localizedOperatorGraphGradient {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ) (χ : E → ℝ) (i : Fin d) (x : E) : ℝ :=
  χ x * (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x) i +
    (u : E →₂[gibbsMeasure volume V] ℝ) x * coordinateDerivative i χ x

/-- The localized weak first-gradient coordinate genuinely belongs to L². -/
theorem localizedOperatorGraphGradient_memLp {V χ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i : Fin d) : MemLp (localizedOperatorGraphGradient hV hprob u g χ i) 2 volume := by
  have ha := compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hprob hχ.continuous hχc
    (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g)) i
  have hb := compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob
    (c1_coordinateDerivative_of_c2 (hχ.of_le (by norm_num)) i).continuous
    (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)) (u : E →₂[gibbsMeasure volume V] ℝ)
  convert ha.add hb using 1
  funext x
  simp only [localizedOperatorGraphGradient, Pi.add_apply]
  ring

/-- The actual first weak derivative of the compact localization, tested
against one derivative of a compact C³ function. -/
theorem localizedOperatorGraphGradient_second_test {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 3 ψ) (_hψc : HasCompactSupport ψ) (i j : Fin d) :
    (∫ x, localizedOperatorGraphGradient hV hprob u g χ i x * coordinateDerivative j ψ x) =
      -(∫ x, (χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) *
        coordinateDerivative j (coordinateDerivative i ψ) x) := by
  let v := gibbsOperatorGraphSobolevLift hV hprob u g
  let G := gibbsSobolevDerivative hV hprob v
  let U (x : E) := (u : E →₂[gibbsMeasure volume V] ℝ) x
  have hDψ : ContDiff ℝ 2 (coordinateDerivative j ψ) := by
    apply contDiff_coordinateDerivative
    convert hψ using 1
    norm_num
  have hDχ := c1_coordinateDerivative_of_c2 (hχ.of_le (by norm_num)) i
  have hDDψ := (c1_coordinateDerivative_of_c2 hDψ i).continuous
  have ht : ContDiff ℝ 2 (fun x => χ x * coordinateDerivative j ψ x) :=
    (hχ.of_le (by norm_num)).mul hDψ
  have htc : HasCompactSupport (fun x => χ x * coordinateDerivative j ψ x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative j ψ)
  let A (x : E) := (χ x * coordinateDerivative j ψ x) * (G x) i
  let B (x : E) := (coordinateDerivative i χ x * coordinateDerivative j ψ x) * U x
  let D (x : E) := (χ x * coordinateDerivative i (coordinateDerivative j ψ) x) * U x
  have hA : Integrable A volume := integrable_compact_test_gibbsVector_coordinate_volume
    hV.continuous hprob (hχ.continuous.mul hDψ.continuous) htc G i
  have hB : Integrable B volume := by
    have hc : HasCompactSupport (fun x => coordinateDerivative i χ x * coordinateDerivative j ψ x) := by
      simpa only [Pi.mul_def, coordinateDerivative] using (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_right
        (f' := coordinateDerivative j ψ)
    exact integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (hDχ.continuous.mul hDψ.continuous) hc (u : E →₂[gibbsMeasure volume V] ℝ)
  have hD : Integrable D volume := by
    have hc : HasCompactSupport (fun x => χ x * coordinateDerivative i (coordinateDerivative j ψ) x) := by
      simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative i (coordinateDerivative j ψ))
    exact integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (hχ.continuous.mul hDDψ) hc (u : E →₂[gibbsMeasure volume V] ℝ)
  have he := gibbsSobolev_coordinate_weak_derivative_volume hV hprob ht htc i v
  rw [gibbsOperatorGraphSobolevLift_inclusion hV hprob u g hug] at he
  have hp (x : E) : coordinateDerivative i (fun y => χ y * coordinateDerivative j ψ y) x * U x = D x + B x := by
    rw [coordinateDerivative_mul_actual (hχ.differentiable (by norm_num)) (hDψ.differentiable (by norm_num))]
    dsimp [D, B]
    ring
  change (∫ x, A x) = -(∫ x, coordinateDerivative i (fun y => χ y * coordinateDerivative j ψ y) x * U x) at he
  simp_rw [hp] at he
  rw [integral_add hD hB] at he
  have hleft : (∫ x, localizedOperatorGraphGradient hV hprob u g χ i x * coordinateDerivative j ψ x) =
      (∫ x, A x) + (∫ x, B x) := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [localizedOperatorGraphGradient, A, B, G, U, v]
    ring
  have hright : (∫ x, (χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) *
      coordinateDerivative j (coordinateDerivative i ψ) x) = ∫ x, D x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [coordinateDerivative_commute (hψ.of_le (by norm_num)) j i]
    dsimp [D, U]
    ring
  rw [hleft, hright]
  linarith

/-- The constructed L² Hessian is the genuine weak derivative of the actual
localized first weak gradient, not merely a bounded scalar candidate. -/
theorem exists_gibbsOperatorGraph_local_gradient_weak_derivative {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) :
    ∃ H : E →₂[volume] ℝ,
      ‖H‖ ≤ ‖(localizedOperatorGraphLaplacian_memLp hV hprob u g hχ hχc).toLp
        (localizedOperatorGraphLaplacian hV hprob u g χ)‖ ∧
      ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
        (∫ x, localizedOperatorGraphGradient hV hprob u g χ i x * coordinateDerivative j ψ x) =
          -(∫ x, H x * ψ x) := by
  obtain ⟨H, hH, hpair⟩ := exists_gibbsOperatorGraph_local_weak_hessian hV hprob u g hug hχ hχc i j
  refine ⟨H, hH, ?_⟩
  intro ψ hψ hψc
  rw [localizedOperatorGraphGradient_second_test hV hprob u g hug hχ hχc hψ hψc i j,
    hpair ψ hψ hψc]

end CutoffRigidity
