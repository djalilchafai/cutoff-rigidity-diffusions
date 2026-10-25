module
public import CutoffRigidity.GibbsOperatorGraphMollification
public import CutoffRigidity.L2BoundedField
public import CutoffRigidity.GaussianAverageGenerator

/-! # Genuine localized Langevin-generator strong approximation

Both differentiated terms of actual compact smooth mollifications converge:
the distributional Laplacian strongly in L², and the genuine weak gradient
strongly in vector L². Actual compact drift coefficients act continuously.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def localizedOperatorGraphGradientLp
    {V χ : E → ℝ} (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) : E →₂[volume] E :=
  euclideanL2Assemble (fun i => (localizedOperatorGraphGradient_memLp hV hprob u g hχ hχc i).toLp
    (localizedOperatorGraphGradient hV hprob u g χ i))

set_option maxHeartbeats 900000 in
/-- Full actual A-domain localized mollifications have true locally strong
Langevin-generator convergence; no residual-convergence premise is assumed. -/
theorem localized_langevin_mollification_tendsto
    {V χ η : E → ℝ} (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (φ : ℕ → ContDiffBump (0 : E)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    ∃ (hn : ∀ n, MemLp
      (fun x => η x * langevinDifferentialOperator V (bumpMollification (φ n) (fun y => χ y * u y)) x) 2 volume)
      (hlim : MemLp (fun x => η x * localizedOperatorGraphLaplacian hV hprob u g χ x -
        inner ℝ (η x • gradient V x) (localizedOperatorGraphGradientLp hV hprob u g hχ hχc x)) 2 volume),
      Tendsto (fun n => (hn n).toLp
        (fun x => η x * langevinDifferentialOperator V (bumpMollification (φ n) (fun y => χ y * u y)) x)) atTop
        (𝓝 (hlim.toLp (fun x => η x * localizedOperatorGraphLaplacian hV hprob u g χ x -
          inner ℝ (η x • gradient V x) (localizedOperatorGraphGradientLp hV hprob u g hχ hχc x)))) := by
  let w : E → ℝ := fun x => χ x * u x
  obtain ⟨hw, hwc, hGrad⟩ := gibbsOperatorGraph_mollifiedGradient_tendsto hV hprob u g hug hχ hχc φ hφ
  have hFm := localizedOperatorGraphLaplacian_measurable hV hprob u g hχ
  have hF := localizedOperatorGraphLaplacian_memLp hV hprob u g hχ hχc
  have hEq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, w x * euclideanLaplacian ψ x) = ∫ x, localizedOperatorGraphLaplacian hV hprob u g χ x * ψ x :=
    fun ψ hψ hψc => gibbsOperatorGraph_localized_distributional_laplacian hV hprob u g hug hχ hχc hψ hψc
  have hLap := mollifiedLaplacianLp_tendsto hw hFm hF hEq φ hφ
  let H := localizedOperatorGraphGradientLp hV hprob u g hχ hχc
  let b₀ : E → ℝ →L[ℝ] ℝ := fun x => η x • ContinuousLinearMap.id ℝ ℝ
  let b₁ : E → E →L[ℝ] ℝ := fun x => innerSL ℝ (η x • gradient V x)
  have hb₀ : Continuous b₀ := hη.smul continuous_const
  have hb₀c : HasCompactSupport b₀ := hηc.comp_left (g := fun r : ℝ => r • ContinuousLinearMap.id ℝ ℝ) (by simp)
  have hb₁ : Continuous b₁ := (innerSL ℝ).continuous.comp
    (hη.smul (continuous_gradient_of_c1 (hV.of_le (by norm_num))))
  have hb₁c : HasCompactSupport b₁ := by
    have hc : HasCompactSupport (fun x => η x • gradient V x) := by
      simpa only [Pi.smul_def'] using hηc.smul_right (f' := gradient V)
    exact hc.comp_left (g := innerSL ℝ) (by simp)
  obtain ⟨M₀, _, hM₀⟩ := compact_continuous_norm_bound hb₀ hb₀c
  obtain ⟨M₁, _, hM₁⟩ := compact_continuous_norm_bound hb₁ hb₁c
  have hB₀ : ∀ᵐ x ∂(volume : Measure E), ‖b₀ x‖ ≤ M₀ := Eventually.of_forall hM₀
  have hB₁ : ∀ᵐ x ∂(volume : Measure E), ‖b₁ x‖ ≤ M₁ := Eventually.of_forall hM₁
  let A := boundedFieldL2 b₀ hb₀.aestronglyMeasurable M₀ hB₀
  let B := boundedFieldL2 b₁ hb₁.aestronglyMeasurable M₁ hB₁
  have hconv := (boundedFieldL2_tendsto b₀ hb₀.aestronglyMeasurable M₀ hB₀ hLap).sub
    (boundedFieldL2_tendsto b₁ hb₁.aestronglyMeasurable M₁ hB₁ hGrad)
  have hn (n : ℕ) : MemLp
      (fun x => η x * langevinDifferentialOperator V (bumpMollification (φ n) w) x) 2 volume := by
    have hf := (bumpMollification_contDiff (φ n) hw).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
    exact (hη.mul (continuous_langevinDifferentialOperator hV hf)).memLp_of_hasCompactSupport
      (by simpa only [Pi.mul_def] using hηc.mul_right (f' := langevinDifferentialOperator V (bumpMollification (φ n) w)))
  have hL : MemLp (fun x => η x * localizedOperatorGraphLaplacian hV hprob u g χ x -
      inner ℝ (η x • gradient V x) (H x)) 2 volume := by
    have h0 := memLp_bounded_field_apply hb₀.aestronglyMeasurable hB₀ hF
    have h1 := memLp_bounded_field_apply hb₁.aestronglyMeasurable hB₁ (Lp.memLp H)
    exact h0.sub h1
  have heqn (n : ℕ) :
      A (mollifiedLaplacianLp hw hFm hF hEq (φ n)) - B (mollifiedGradientLp (φ n) w hw hwc) =
      (hn n).toLp (fun x => η x * langevinDifferentialOperator V (bumpMollification (φ n) w) x) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (A (mollifiedLaplacianLp hw hFm hF hEq (φ n))) (B (mollifiedGradientLp (φ n) w hw hwc)),
      boundedFieldL2_coeFn b₀ hb₀.aestronglyMeasurable M₀ hB₀ (mollifiedLaplacianLp hw hFm hF hEq (φ n)),
      boundedFieldL2_coeFn b₁ hb₁.aestronglyMeasurable M₁ hB₁ (mollifiedGradientLp (φ n) w hw hwc),
      (mollified_laplacian_memLp hw hFm hF hEq (φ n)).coeFn_toLp,
      (mollifiedGradient_memLp (φ n) hw hwc).coeFn_toLp, (hn n).coeFn_toLp] with x hs h0 h1 hl hg hr
    rw [hs, Pi.sub_apply, h0, h1]
    unfold mollifiedLaplacianLp mollifiedGradientLp
    rw [hl, hg, hr]
    change η x * euclideanLaplacian (bumpMollification (φ n) w) x -
      inner ℝ (η x • gradient V x) (gradient (bumpMollification (φ n) w) x) = _
    rw [real_inner_smul_left]
    change _ = η x * (euclideanLaplacian (bumpMollification (φ n) w) x - inner ℝ (gradient V x) (gradient (bumpMollification (φ n) w) x))
    ring
  have heq : A (hF.toLp _) - B H = hL.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (A (hF.toLp _)) (B H),
      boundedFieldL2_coeFn b₀ hb₀.aestronglyMeasurable M₀ hB₀ (hF.toLp _),
      boundedFieldL2_coeFn b₁ hb₁.aestronglyMeasurable M₁ hB₁ H,
      hF.coeFn_toLp, hL.coeFn_toLp] with x hs h0 h1 hF' hL'
    rw [hs, Pi.sub_apply, h0, h1, hF', hL']
    rfl
  refine ⟨hn, hL, ?_⟩
  change Tendsto (fun n => (hn n).toLp _) atTop (𝓝 (hL.toLp _))
  change Tendsto (fun n => A (mollifiedLaplacianLp hw hFm hF hEq (φ n)) -
    B (mollifiedGradientLp (φ n) w hw hwc)) atTop (𝓝 (A (hF.toLp _) - B H)) at hconv
  simpa only [heqn, heq] using hconv

end CutoffRigidity
