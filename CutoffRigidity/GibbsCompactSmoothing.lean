module

public import CutoffRigidity.L2MollificationBCF
public import CutoffRigidity.GibbsLocalizedTranslations
public import CutoffRigidity.GibbsHeatGenerator

/-! # Genuine compact smoothing of actual Gibbs L² heat trajectories

Compact localization is a continuous map into Lebesgue L². Actual smooth
convolution then maps continuously into the supremum norm. This makes
smoothed form-heat trajectories legitimate uniformly differentiable tests.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual compact cutoff multiplication between the two genuine L² spaces. -/
@[expose] noncomputable def gibbsCutoffToVolumeL2Linear {V χ : E → ℝ}
    (hV : Continuous V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    (E →₂[gibbsMeasure volume V] ℝ) →ₗ[ℝ] (E →₂[volume] ℝ) where
  toFun u := (compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc u).toLp (fun x => χ x * u x)
  map_add' u v := by
    apply Lp.ext
    have hinput := (gibbsMeasure_ae_eq_iff volume hV.measurable).mp (Lp.coeFn_add u v)
    filter_upwards [(compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc (u + v)).coeFn_toLp,
      (compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc u).coeFn_toLp,
      (compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc v).coeFn_toLp,
      Lp.coeFn_add ((compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc u).toLp _)
        ((compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc v).toLp _), hinput] with x hs hu hv ha hi
    rw [hs, ha, hi]
    simp only [Pi.add_apply]
    rw [hu, hv]
    ring
  map_smul' r u := by
    apply Lp.ext
    have hinput := (gibbsMeasure_ae_eq_iff volume hV.measurable).mp (Lp.coeFn_smul r u)
    filter_upwards [(compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc (r • u)).coeFn_toLp,
      (compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc u).coeFn_toLp,
      Lp.coeFn_smul r ((compact_cutoff_gibbsLp_memLp_volume hV hp hχ hχc u).toLp _), hinput]
      with x hs hu hr hi
    simp only [RingHom.id_apply]
    rw [hs, hr, hi]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu]
    ring

/-- True bounded localization, using the proved inverse-density cutoff bound. -/
@[expose] noncomputable def gibbsCutoffToVolumeL2CLM {V χ : E → ℝ}
    (hV : Continuous V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[volume] ℝ) :=
  (gibbsCutoffToVolumeL2Linear hV hp hχ.continuous hχc).mkContinuous
    (exists_compact_cutoff_gibbsLp_L2_norm_bound hV hp hχ hχc).choose
    (exists_compact_cutoff_gibbsLp_L2_norm_bound hV hp hχ hχc).choose_spec.2

/-- Actual compact smooth convolution of an actual Gibbs L² class. -/
@[expose] noncomputable def gibbsCompactSmoothing {V χ : E → ℝ}
    (hV : Continuous V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (φ : ContDiffBump (0 : E)) :
    (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →ᵇ ℝ) :=
  (bumpMollificationBCFCLM φ).comp (gibbsCutoffToVolumeL2CLM hV hp hχ hχc)

/-- The actual bounded smoothing has the exact raw cutoff-convolution values. -/
theorem gibbsCompactSmoothing_apply {V χ : E → ℝ}
    (hV : Continuous V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (φ : ContDiffBump (0 : E))
    (u : E →₂[gibbsMeasure volume V] ℝ) (x : E) :
    gibbsCompactSmoothing hV hp hχ hχc φ u x = bumpMollification φ (fun y => χ y * u y) x := by
  change bumpMollification φ ((compact_cutoff_gibbsLp_memLp_volume hV hp hχ.continuous hχc u).toLp _) x = _
  exact congrFun (bumpMollification_congr_ae φ
    (compact_cutoff_gibbsLp_memLp_volume hV hp hχ.continuous hχc u).coeFn_toLp) x

/-- Each actual smoothed class is genuinely compactly supported and smooth. -/
theorem gibbsCompactSmoothing_smooth_compact {V χ : E → ℝ}
    (hV : Continuous V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (φ : ContDiffBump (0 : E))
    (u : E →₂[gibbsMeasure volume V] ℝ) :
    ContDiff ℝ 3 (gibbsCompactSmoothing hV hp hχ hχc φ u) ∧
      HasCompactSupport (gibbsCompactSmoothing hV hp hχ hχc φ u) := by
  have he : (gibbsCompactSmoothing hV hp hχ hχc φ u : E → ℝ) =
      bumpMollification φ (fun y => χ y * u y) := funext (gibbsCompactSmoothing_apply hV hp hχ hχc φ u)
  rw [he]
  refine ⟨(bumpMollification_contDiff φ
    ((compact_cutoff_gibbsLp_memLp_volume hV hp hχ.continuous hχc u).locallyIntegrable (by norm_num))).of_le (by simp), ?_⟩
  apply bumpMollification_hasCompactSupport
  simpa only [Pi.mul_def] using hχc.mul_right (f' := fun y => u y)

/-- The actual operator-domain heat derivative becomes a genuine uniform
bounded-continuous derivative after compact smoothing. -/
theorem gibbsCompactSmoothing_heat_hasDerivAt {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (φ : ContDiffBump (0 : E))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u,g) ∈ (gibbsPositiveGenerator hV hp).graph) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => gibbsCompactSmoothing hV.continuous hp hχ hχc φ
      (gibbsHeatSemigroup hV hp ρ hρ hHess s.toNNReal u))
      (-gibbsCompactSmoothing hV.continuous hp hχ hχc φ
        (gibbsHeatSemigroup hV hp ρ hρ hHess t.toNNReal g)) t := by
  have hh := (gibbsCompactSmoothing hV.continuous hp hχ hχc φ).hasFDerivAt.comp_hasDerivAt t
    (gibbsHeatSemigroup_hasDerivAt_operatorGraph hV hp ρ hρ hHess t ht u g hug)
  convert! hh using 1
  simp only [map_neg]

end CutoffRigidity
