module
public import CutoffRigidity.EuclideanTransportDuality
public import CutoffRigidity.CompactLipschitzTransportDuality

/-! # Genuine Euclidean Kantorovich strong duality

Compact nonexpansive clipping, positive extension, actual representing
couplings, Prokhorov compactness and Portmanteau establish the actual primal
quadratic cost bound from bounded continuous dual tests.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1200000 in
theorem exists_clipped_coupling_of_lipschitz_dual_budget
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ℝ)
    (hDual : ∀ (f g : E →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x+g y ≤ ‖x-y‖^2) →
      (∫ x,f x ∂μ)+(∫ y,g y ∂ν) ≤ K) (n : ℕ) :
    ∃ π : ProbabilityMeasure (E×E),
      ((π.map Prod.fst : ProbabilityMeasure E) : Measure E) = μ.map (euclideanClip n) ∧
      ((π.map Prod.snd : ProbabilityMeasure E) : Measure E) = ν.map (euclideanClip n) ∧
      (∫⁻ z,edist z.1 z.2^2 ∂(π : Measure (E×E))) ≤ ENNReal.ofReal K := by
  let A := euclideanClipBox (d := d) n
  letI : CompactSpace A := isCompact_iff_compactSpace.mp (euclideanClipBox_isCompact n)
  let T : E → A := fun x => ⟨euclideanClip n x,euclideanClip_mem n x⟩
  have hT : Continuous T := (euclideanClip_lipschitz n).continuous.subtype_mk _
  have hTLip : LipschitzWith 1 T := (euclideanClip_lipschitz n).subtype_mk _
  let μn := μ.map T
  let νn := ν.map T
  letI : IsProbabilityMeasure μn := inferInstance
  letI : IsProbabilityMeasure νn := inferInstance
  let c : C(A×A,ℝ) := ⟨fun z => ‖(z.1 : E)-(z.2 : E)‖^2,by fun_prop⟩
  have hd : ∀ (f g : C(A,ℝ)) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x+g y ≤ c (x,y)) →
      (∫ x,f x ∂μn)+(∫ y,g y ∂νn) ≤ K := by
    intro f g L J hf hg hfg
    let fB : A →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
    let gB : A →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact g
    let F : E →ᵇ ℝ := fB.compContinuous ⟨T,hT⟩
    let G : E →ᵇ ℝ := gB.compContinuous ⟨T,hT⟩
    have hfg' (x y : E) : F x+G y ≤ ‖x-y‖^2 := by
      apply (hfg (T x) (T y)).trans
      change ‖euclideanClip n x-euclideanClip n y‖^2 ≤ ‖x-y‖^2
      have hh := (euclideanClip_lipschitz n).norm_sub_le x y
      simp only [NNReal.coe_one,one_mul] at hh
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hh
    have hFLip : LipschitzWith L F := by
      convert! hf.comp hTLip using 1
      simp only [mul_one]
    have hGLip : LipschitzWith J G := by
      convert! hg.comp hTLip using 1
      simp only [mul_one]
    have hh := hDual F G L J hFLip hGLip hfg'
    have hF : (∫ x,f x ∂μn) = ∫ x,F x ∂μ := by
      have hm := integral_map (μ := μ) (f := fun a => f a) hT.measurable.aemeasurable f.continuous.aestronglyMeasurable
      convert! hm using 1
    have hG : (∫ x,g x ∂νn) = ∫ x,G x ∂ν := by
      have hm := integral_map (μ := ν) (f := fun a => g a) hT.measurable.aemeasurable g.continuous.aestronglyMeasurable
      convert! hm using 1
    rwa [hF,hG]
  obtain ⟨π,hπ,hF,hG,hC⟩ := exists_compact_transport_coupling_of_lipschitz_dual_budget μn νn c K hd
  let := hπ
  let ι : A×A → E×E := fun z => ((z.1:E),(z.2:E))
  have hι : Continuous ι := by fun_prop
  let q : ProbabilityMeasure (E×E) := ⟨π.map ι,inferInstance⟩
  refine ⟨q,?_,?_,?_⟩
  · have hh : (π.map ι).map Prod.fst = μ.map (euclideanClip n) := by
      rw [Measure.map_map measurable_fst hι.measurable]
      have he : (Prod.fst ∘ ι) = (Subtype.val ∘ Prod.fst) := rfl
      rw [he,← Measure.map_map measurable_subtype_coe measurable_fst,hF]
      change (μ.map T).map Subtype.val = _
      rw [Measure.map_map measurable_subtype_coe hT.measurable]
      rfl
    convert! hh using 1
  · have hh : (π.map ι).map Prod.snd = ν.map (euclideanClip n) := by
      rw [Measure.map_map measurable_snd hι.measurable]
      have he : (Prod.snd ∘ ι) = (Subtype.val ∘ Prod.snd) := rfl
      rw [he,← Measure.map_map measurable_subtype_coe measurable_snd,hG]
      change (ν.map T).map Subtype.val = _
      rw [Measure.map_map measurable_subtype_coe hT.measurable]
      rfl
    convert! hh using 1
  · change (∫⁻ z,edist z.1 z.2^2 ∂π.map ι) ≤ _
    rw [lintegral_map (by fun_prop) hι.measurable]
    have he : (∫⁻ z : A×A, edist (ι z).1 (ι z).2^2 ∂π) = ENNReal.ofReal (∫ z,c z ∂π) := by
      rw [ofReal_integral_eq_lintegral_ofReal (c.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (Eventually.of_forall fun z => sq_nonneg _)]
      apply lintegral_congr
      intro z
      change edist (z.1:E) (z.2:E)^2 = ENNReal.ofReal (‖(z.1:E)-(z.2:E)‖^2)
      rw [edist_dist,dist_eq_norm,ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [he]
    exact ENNReal.ofReal_le_ofReal hC

set_option maxHeartbeats 800000 in
/-- Genuine Euclidean strong duality in budget form. The conclusion uses
the original infimum over actual couplings, including infinite-moment laws. -/
theorem squaredWasserstein_le_of_lipschitz_dual_budget
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ℝ)
    (hDual : ∀ (f g : E →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x+g y ≤ ‖x-y‖^2) →
      (∫ x,f x ∂μ)+(∫ y,g y ∂ν) ≤ K) :
    squaredWasserstein μ ν ≤ ENNReal.ofReal K := by
  choose π hFirst hSecond hCost using exists_clipped_coupling_of_lipschitz_dual_budget μ ν K hDual
  let μP : ProbabilityMeasure E := ⟨μ,inferInstance⟩
  let νP : ProbabilityMeasure E := ⟨ν,inferInstance⟩
  have hF : Tendsto (fun n => (π n).map Prod.fst) atTop (𝓝 μP) := by
    have he : (fun n => (π n).map Prod.fst) = (fun n => μP.map (euclideanClip n)) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      convert! hFirst n using 1
    rw [he]
    exact tendsto_probabilityMeasure_map_euclideanClip μP
  have hS : Tendsto (fun n => (π n).map Prod.snd) atTop (𝓝 νP) := by
    have he : (fun n => (π n).map Prod.snd) = (fun n => νP.map (euclideanClip n)) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      convert! hSecond n using 1
    rw [he]
    exact tendsto_probabilityMeasure_map_euclideanClip νP
  obtain ⟨q,hq⟩ := exists_coupling_limit_of_marginals_tendsto π μP νP hF hS (ENNReal.ofReal K) hCost
  exact (squaredWasserstein_le_cost q).trans hq

end CutoffRigidity
