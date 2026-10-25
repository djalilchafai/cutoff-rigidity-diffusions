module
public import CutoffRigidity.GibbsSobolevC1
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Actual weak gradients of Lipschitz functions

Rademacher's theorem and its integration-by-parts theorem identify the
actual almost-everywhere derivative, rather than assuming a weak derivative.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem measurable_euclidean_gradient (f : E → ℝ) : Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem norm_gradient_le_of_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : E) : ‖gradient f x‖ ≤ L := by
  have he : ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _
  rw [he]
  exact norm_fderiv_le_of_lipschitz ℝ hf

theorem compact_lipschitz_gradient_memLp {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hfc : HasCompactSupport f) : MemLp (gradient f) 2 volume := by
  have htop : MemLp (gradient f) ⊤ volume := memLp_top_of_bound
    (measurable_euclidean_gradient f).aestronglyMeasurable L
    (Eventually.of_forall (norm_gradient_le_of_lipschitz hf))
  have hc : HasCompactSupport (gradient f) :=
    (hfc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  exact htop.mono_exponent_of_measure_support_ne_top
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) hc.measure_lt_top.ne le_top

theorem lipschitz_volume_weak_derivative {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (j : Fin d)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, f x * coordinateDerivative j ψ x) = -(∫ x, gradient f x j * ψ x) := by
  obtain ⟨K,hK⟩ : ∃ K, LipschitzWith K ψ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ (by norm_num)
  have hh := hf.integral_lineDeriv_mul_eq (μ := volume) hK hψc (EuclideanSpace.single j 1)
  have hleft : (∫ x, lineDeriv ℝ f x (EuclideanSpace.single j 1) * ψ x) =
      ∫ x, gradient f x j * ψ x := by
    apply integral_congr_ae
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    rw [hx.lineDeriv_eq_fderiv, fderiv_single_eq_gradient_coordinate]
  have hright : (∫ x, lineDeriv ℝ ψ x (-EuclideanSpace.single j 1) * f x) =
      -(∫ x, f x * coordinateDerivative j ψ x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    rw [(hψ.differentiable (by norm_num) x).lineDeriv_eq_fderiv, map_neg]
    simp only [coordinateDerivative]
    ring
  rw [hleft,hright] at hh
  linarith

/-- Compact Lipschitz functions have a genuine closed Gibbs H¹ lift with
actual Rademacher gradient. -/
theorem exists_gibbsSobolev_of_compact_lipschitz {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : ℝ≥0} (hf : LipschitzWith L f) (hfc : HasCompactSupport f) :
    ∃ v : gibbsSobolevGraph hV hp,
      (gibbsSobolevInclusion hV hp v =ᵐ[gibbsMeasure volume V] f) ∧
      (gibbsSobolevDerivative hV hp v =ᵐ[gibbsMeasure volume V] gradient f) := by
  have hfLp := hf.continuous.memLp_of_hasCompactSupport (p := (2:ENNReal)) hfc (μ := volume)
  have hGLp := compact_lipschitz_gradient_memLp hf hfc
  let G := hGLp.toLp (gradient f)
  let H (j : Fin d) := (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp G
  have hw (j : Fin d) (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) :
      (∫ x, f x * coordinateDerivative j ψ x) = -(∫ x, H j x * ψ x) := by
    rw [lipschitz_volume_weak_derivative hf j ψ hψ hψc]
    congr 1
    apply integral_congr_ae
    filter_upwards [(EuclideanSpace.proj j : E →L[ℝ] ℝ).coeFn_compLp G,hGLp.coeFn_toLp]
      with x hx hg
    change gradient f x j * ψ x = (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp G x * ψ x
    rw [hx,hg]
    rfl
  obtain ⟨v,hv,hD⟩ := exists_gibbsSobolev_of_compact_weak_derivatives hV hp ρ hρ hHess
    hf.continuous.measurable hfLp hfc H hw
  refine ⟨v,?_,?_⟩
  · rw [hv]
    exact (volumeToGibbsL2_coeFn hV ρ hρ hHess _).trans
      ((gibbsMeasure_absolutelyContinuous volume V).ae_eq hfLp.coeFn_toLp)
  · have hass : euclideanL2Assemble H = G := euclideanL2_assemble_projections G
    rw [hD,hass]
    exact (volumeToGibbsL2Vector_coeFn hV ρ hρ hHess _).trans
      ((gibbsMeasure_absolutelyContinuous volume V).ae_eq hGLp.coeFn_toLp)

end CutoffRigidity
