module
public import CutoffRigidity.C1LaplacianTest
public import CutoffRigidity.GibbsGeneratorExtension

/-! # Ordinary C¹ weak backward equations imply the genuine Gibbs weak form

The exponential test has exactly C² regularity, matching the paper's C²
potential. Its drift terms cancel by actual Lebesgue integration by parts.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 700000 in
theorem c1_weak_langevin_weighted_compact_test
    {V f h φ : E → ℝ} (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hf : ContDiff ℝ 1 f) (hgrad : MemLp (gradient f) 2 (gibbsMeasure volume V))
    (hh : MemLp h 2 (gibbsMeasure volume V))
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
        ∫ x, ψ x * (h x + inner ℝ (gradient V x) (gradient f x)))
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, inner ℝ (gradient f x) (gradient φ x) ∂gibbsMeasure volume V) =
      -(∫ x, h x * φ x ∂gibbsMeasure volume V) := by
  let := hprob
  let ψ : E → ℝ := fun x => Real.exp (-V x) * φ x
  have hψ : ContDiff ℝ 2 ψ := hV.neg.exp.mul hφ
  have hψc : HasCompactSupport ψ := by
    simpa only [ψ, Pi.mul_def] using hφc.mul_left (f := fun x => Real.exp (-V x))
  have hgradf := continuous_gradient_of_c1 hf
  have hgradV := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hgradφ := continuous_gradient_of_c1 (hφ.of_le (by norm_num))
  have hgradφc : HasCompactSupport (gradient φ) :=
    (hφc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  have hgradφLp : MemLp (gradient φ) 2 (gibbsMeasure volume V) := hgradφ.memLp_of_hasCompactSupport hgradφc
  have hφLp : MemLp φ 2 (gibbsMeasure volume V) := hφ.continuous.memLp_of_hasCompactSupport hφc
  let A : E → ℝ := fun x => Real.exp (-V x) * inner ℝ (gradient f x) (gradient φ x)
  let B : E → ℝ := fun x => (Real.exp (-V x) * φ x) * inner ℝ (gradient V x) (gradient f x)
  let D : E → ℝ := fun x => Real.exp (-V x) * (h x * φ x)
  have hAμ : Integrable (fun x => inner ℝ (gradient f x) (gradient φ x)) (gibbsMeasure volume V) := by
    apply (hgrad.norm.integrable_mul hgradφLp.norm).mono'
      (hgradf.inner hgradφ).aestronglyMeasurable
    exact Eventually.of_forall (fun x => norm_inner_le_norm _ _)
  have hA : Integrable A volume := by
    simpa only [A, smul_eq_mul] using (integrable_gibbsMeasure_iff volume hV.continuous.measurable _).mp hAμ
  have hD : Integrable D volume := by
    simpa only [D, smul_eq_mul, Pi.mul_apply] using (integrable_gibbsMeasure_iff volume hV.continuous.measurable _).mp
      (hh.integrable_mul hφLp)
  have hB : Integrable B volume := by
    have hc : Continuous B := by dsimp [B]; fun_prop
    have hs : HasCompactSupport B := by
      simpa only [B, Pi.mul_def] using hψc.mul_right
        (f' := fun x => inner ℝ (gradient V x) (gradient f x))
    exact hc.integrable_of_hasCompactSupport hs
  have hgradψ (x : E) : gradient ψ x = Real.exp (-V x) • (gradient φ x - φ x • gradient V x) := by
    apply ext_inner_right ℝ
    intro z
    rw [inner_gradient_left]
    change fderiv ℝ (fun y => Real.exp (-V y) * φ y) x z = _
    rw [fderiv_gibbsWeight_mul_apply (hV.differentiable (by norm_num) x) (hφ.differentiable (by norm_num) x),
      real_inner_smul_left, inner_sub_left, real_inner_smul_left, inner_gradient_left, inner_gradient_left]
  have hp (x : E) : inner ℝ (gradient f x) (gradient ψ x) = A x - B x := by
    rw [hgradψ, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_comm (gradient V x) (gradient f x)]
    dsimp [A, B]
    ring
  have he := hweak ψ hψ hψc
  rw [c1_integral_mul_laplacian_compact_test hf hψ hψc] at he
  simp_rw [hp] at he
  rw [integral_sub hA hB] at he
  have hr : (∫ x, ψ x * (h x + inner ℝ (gradient V x) (gradient f x))) = (∫ x, D x) + ∫ x, B x := by
    rw [← integral_add hD hB]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [ψ, D, B]
    ring
  rw [hr] at he
  rw [integral_gibbsMeasure volume hV.continuous.measurable, integral_gibbsMeasure volume hV.continuous.measurable]
  change (∫ x, A x) = -(∫ x, D x)
  linarith

/-- A true ordinary weak Langevin equation for a C¹ L² representative
places that representative in the actual full self-adjoint operator graph. -/
theorem c1_weak_langevin_mem_operatorGraph
    {V f h : E → ℝ} (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgrad : MemLp (gradient f) 2 (gibbsMeasure volume V)) (hh : MemLp h 2 (gibbsMeasure volume V))
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
        ∫ x, ψ x * (h x + inner ℝ (gradient V x) (gradient f x))) :
    (hfLp.toLp f, -hh.toLp h) ∈ (gibbsPositiveGenerator hV hprob).graph := by
  let w := c1GibbsSobolevLift hV hprob ρ hρ hHess hf hfLp hgrad
  have he : ∀ v : gibbsSobolevGraph hV hprob,
      gibbsDirichletEnergy hV hprob w v = inner ℝ (-hh.toLp h) (gibbsSobolevInclusion hV hprob v) := by
    apply gibbs_weak_equation_of_compact_pairing hV hprob
    intro v
    let φ := compactGibbsRepresentative V v
    have hφ := (compactGibbsRepresentative_spec V v).1
    have hφc := (compactGibbsRepresentative_spec V v).2.1
    have hl : inner ℝ (gibbsSobolevDerivative hV hprob w) (compactGibbsGradient hV.continuous hprob v) =
        ∫ x, inner ℝ (gradient f x) (gradient φ x) ∂gibbsMeasure volume V := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hgrad.coeFn_toLp, (compactGibbsGradient_memLp hprob v).coeFn_toLp] with x hx hy
      change inner ℝ (hgrad.toLp (gradient f) x)
        ((compactGibbsGradient_memLp hprob v).toLp (gradient φ) x) = _
      rw [hx, hy]
    have hr : inner ℝ (-hh.toLp h) (v : E →₂[gibbsMeasure volume V] ℝ) =
        -(∫ x, h x * φ x ∂gibbsMeasure volume V) := by
      rw [inner_neg_left, L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [hh.coeFn_toLp, (compactGibbsRepresentative_spec V v).2.2] with x hx hy
      rw [hx, ← hy, Real.inner_apply]
    rw [hl, hr]
    exact c1_weak_langevin_weighted_compact_test hV hprob hf hgrad hh hweak hφ hφc
  exact gibbsPositiveGenerator_of_weak_equation hV hprob w (-hh.toLp h) he

/-- The same genuine domain bridge for supplied actual L² classes, so it
applies directly to the constructed stochastic transition classes. -/
theorem c1_weak_langevin_mem_operatorGraph_of_ae
    {V f h : E → ℝ} (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hgrad : MemLp (gradient f) 2 (gibbsMeasure volume V))
    (U H : E →₂[gibbsMeasure volume V] ℝ)
    (hU : U =ᵐ[gibbsMeasure volume V] f) (hH : H =ᵐ[gibbsMeasure volume V] h)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
        ∫ x, ψ x * (h x + inner ℝ (gradient V x) (gradient f x))) :
    (U, -H) ∈ (gibbsPositiveGenerator hV hprob).graph := by
  have hfLp : MemLp f 2 (gibbsMeasure volume V) := (memLp_congr_ae hU).mp (Lp.memLp U)
  have hhLp : MemLp h 2 (gibbsMeasure volume V) := (memLp_congr_ae hH).mp (Lp.memLp H)
  have hfeq : hfLp.toLp f = U := Lp.ext (hfLp.coeFn_toLp.trans hU.symm)
  have hheq : hhLp.toLp h = H := Lp.ext (hhLp.coeFn_toLp.trans hH.symm)
  have he := c1_weak_langevin_mem_operatorGraph hV hprob ρ hρ hHess hf hfLp hgrad hhLp hweak
  rwa [hfeq, hheq] at he

end CutoffRigidity
