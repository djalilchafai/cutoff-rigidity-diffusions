module

public import CutoffRigidity.GibbsOperatorLocalElliptic

/-! # The weak PDE on the full actual self-adjoint operator domain

The resolvent graph supplies the H¹ lift and the genuine distributional
elliptic equation for every operator-domain pair (u,g). No eigenvector,
classical representative, or weak second derivative is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The inverse-resolvent graph gives the shifted resolvent equation. -/
theorem gibbsOperatorGraph_resolvent {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    gibbsL2Resolvent hV hprob (u + g) = u := by
  change (u, g) ∈ (positiveResolventOperator (gibbsL2Resolvent hV hprob)).graph at hug
  rw [positiveResolventOperator_graph _ (gibbsL2Resolvent_injective hV hprob),
    mem_positiveResolventGraph] at hug
  obtain ⟨f, hf, hg⟩ := hug
  have hshift : f = u + g := by rw [hf] at hg; rw [← hg]; abel
  rwa [hshift] at hf

/-- A canonical genuine H¹ lift for every actual operator-domain pair. -/
@[expose] noncomputable def gibbsOperatorGraphSobolevLift {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ) : gibbsSobolevGraph hV hprob :=
  gibbsWeakResolvent hV hprob (u + g)

/-- The lift has precisely the original actual L² value. -/
theorem gibbsOperatorGraphSobolevLift_inclusion {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    gibbsSobolevInclusion hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) = u :=
  gibbsOperatorGraph_resolvent hV hprob u g hug

/-- The full form equation follows from the actual operator graph. -/
theorem gibbsOperatorGraph_weak_equation {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph)
    (v : gibbsSobolevGraph hV hprob) :
    gibbsDirichletEnergy hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) v =
      inner ℝ g (gibbsSobolevInclusion hV hprob v) := by
  have hh := gibbsWeakResolvent_equation hV hprob (u + g) v
  change inner ℝ
      (gibbsSobolevInclusion hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g))
      (gibbsSobolevInclusion hV hprob v) +
    gibbsDirichletEnergy hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) v = _ at hh
  rw [gibbsOperatorGraphSobolevLift_inclusion hV hprob u g hug, inner_add_left] at hh
  linarith

/-- The actual graph implies the weighted PDE for genuine compact C² tests. -/
theorem gibbsOperatorGraph_compact_test_equation {V φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) 
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, inner ℝ
      (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x)
      (gradient φ x) ∂gibbsMeasure volume V) =
      (∫ x, g x * φ x ∂gibbsMeasure volume V) := by
  let := hprob
  have hφLp : MemLp φ 2 (gibbsMeasure volume V) := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hgradc : HasCompactSupport (gradient φ) :=
    (hφc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  have hgLp : MemLp (gradient φ) 2 (gibbsMeasure volume V) :=
    (continuous_gradient_of_c1 (hφ.of_le (by norm_num))).memLp_of_hasCompactSupport hgradc
  let v := c2GibbsSobolevLift hV hprob hφ hφLp hgLp
  have he := gibbsOperatorGraph_weak_equation hV hprob u g hug v
  have hleft : gibbsDirichletEnergy hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) v =
      ∫ x, inner ℝ
        (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x)
        (gradient φ x) ∂gibbsMeasure volume V := by
    rw [gibbsDirichletEnergy, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgLp.coeFn_toLp] with x hx
    change inner ℝ _ (hgLp.toLp (gradient φ) x) = _
    rw [hx]
  have hright : inner ℝ g (gibbsSobolevInclusion hV hprob v) =
      ∫ x, g x * φ x ∂gibbsMeasure volume V := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφLp.coeFn_toLp] with x hx
    change inner ℝ _ (hφLp.toLp φ x) = _
    rw [hx, Real.inner_apply]
  rwa [hleft, hright] at he

/-- The full actual operator domain satisfies the ordinary-volume weak PDE. -/
theorem gibbsOperatorGraph_volume_test_equation {V φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) 
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, inner ℝ
      (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x)
      (gradient φ x + φ x • gradient V x) ∂volume) =
      (∫ x, g x * φ x ∂volume) := by
  let ψ (x : E) := Real.exp (V x) * φ x
  have hψ : ContDiff ℝ 2 ψ := hV.exp.mul hφ
  have hψc : HasCompactSupport ψ := by
    simpa only [ψ, Pi.mul_def] using hφc.mul_left (f := fun x => Real.exp (V x))
  have he := gibbsOperatorGraph_compact_test_equation hV hprob u g hug hψ hψc
  have hleft : (∫ x, inner ℝ
      (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x)
      (gradient ψ x) ∂gibbsMeasure volume V) =
      ∫ x, inner ℝ
        (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x)
        (gradient φ x + φ x • gradient V x) ∂volume := by
    rw [← integral_exp_potential_mul_gibbs_eq_volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    rw [gradient_exp_potential_mul_test (hV.differentiable (by norm_num)) (hφ.differentiable (by norm_num)),
      inner_smul_right]
  have hright : (∫ x, g x * ψ x ∂gibbsMeasure volume V) =
      ∫ x, g x * φ x ∂volume := by
    rw [← integral_exp_potential_mul_gibbs_eq_volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [ψ]
    ring
  rwa [hleft, hright] at he

/-- The lower-order elliptic right-hand side is genuinely locally L². -/
theorem gibbsOperatorGraph_local_rhs_memLp {V χ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u g : E →₂[gibbsMeasure volume V] ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (fun x => χ x *
      (inner ℝ (gradient V x)
        (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x) -
          g x)) 2 volume := by
  let G := gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g)
  have hGV : Continuous (gradient V) := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hi (i : Fin d) : MemLp (fun x => (χ x * (gradient V x) i) * (G x) i) 2 volume := by
    have hc : Continuous (fun x => χ x * (gradient V x) i) :=
      hχ.mul ((EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp hGV)
    have hs : HasCompactSupport (fun x => χ x * (gradient V x) i) := by
      simpa only [Pi.mul_def] using hχc.mul_right (f' := fun x => (gradient V x) i)
    exact compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hprob hc hs G i
  have hsum : MemLp (fun x => ∑ i : Fin d, (χ x * (gradient V x) i) * (G x) i) 2 volume :=
    by
      convert memLp_finsetSum' Finset.univ (fun i _ => hi i) using 1
      funext x
      simp
  have hu := (compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ hχc
    g)
  convert hsum.sub hu using 1
  funext x
  dsimp only [G]
  simp only [Pi.sub_apply, PiLp.inner_apply, Real.inner_apply, mul_sub, Finset.mul_sum, mul_assoc]


/-- The full actual operator domain has the genuine distributional Laplacian. -/
theorem gibbsOperatorGraph_distributional_laplacian {V φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) 
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) (hφ : ContDiff ℝ 3 φ) (hφc : HasCompactSupport φ) :
    (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * euclideanLaplacian φ x) =
      ∫ x, φ x * (inner ℝ (gradient V x)
        (gibbsSobolevDerivative hV hprob (gibbsOperatorGraphSobolevLift hV hprob u g) x) -
          g x) := by
  let v := gibbsOperatorGraphSobolevLift hV hprob u g
  let G := gibbsSobolevDerivative hV hprob v
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hgradInt : Integrable (fun x => inner ℝ (G x) (gradient φ x)) volume := by
    have hi (i : Fin d) : Integrable (fun x => coordinateDerivative i φ x * (G x) i) volume :=
      integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hprob
        (c1_coordinateDerivative_of_c2 hφ2 i).continuous
        (hφc.fderiv_apply ℝ (EuclideanSpace.single i 1)) G i
    have hh := integrable_finsetSum Finset.univ (fun i _ => hi i)
    convert hh using 1
    funext x
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply, coordinateDerivative, fderiv_single_eq_gradient_coordinate]
    ring
  have hGV : Continuous (gradient V) := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hDriftInt : Integrable (fun x => φ x * inner ℝ (gradient V x) (G x)) volume := by
    have hi (i : Fin d) : Integrable (fun x => (φ x * (gradient V x) i) * (G x) i) volume := by
      have hc : Continuous (fun x => φ x * (gradient V x) i) :=
        hφ.continuous.mul ((EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp hGV)
      have hs : HasCompactSupport (fun x => φ x * (gradient V x) i) := by
        simpa only [Pi.mul_def] using hφc.mul_right (f' := fun x => (gradient V x) i)
      exact integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hprob hc hs G i
    have hh := integrable_finsetSum Finset.univ (fun i _ => hi i)
    convert hh using 1
    funext x
    rw [PiLp.inner_apply, Finset.mul_sum]
    simp only [Real.inner_apply, mul_assoc]
  have hSourceInt : Integrable (fun x => g x * φ x) volume := by
    have hh := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob hφ.continuous hφc
      g
    simpa only [mul_comm] using hh
  have he := gibbsOperatorGraph_volume_test_equation hV hprob u g hug hφ2 hφc
  have hp (x : E) : inner ℝ (G x) (gradient φ x + φ x • gradient V x) =
      inner ℝ (G x) (gradient φ x) + φ x * inner ℝ (gradient V x) (G x) := by
    rw [inner_add_right, inner_smul_right, real_inner_comm (G x) (gradient V x)]
  change (∫ x, inner ℝ (G x) (gradient φ x + φ x • gradient V x)) = _ at he
  simp_rw [hp] at he
  rw [integral_add hgradInt hDriftInt] at he
  have hlap := gibbsSobolev_laplacian_test_volume hV hprob v hφ hφc
  rw [gibbsOperatorGraphSobolevLift_inclusion hV hprob u g hug] at hlap
  have hr : (∫ x, φ x * (inner ℝ (gradient V x) (G x) - g x)) =
      (∫ x, φ x * inner ℝ (gradient V x) (G x)) -
        (∫ x, g x * φ x) := by
    rw [← integral_sub hDriftInt hSourceInt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  change (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * euclideanLaplacian φ x) = _
  rw [hr]
  linarith

end CutoffRigidity
