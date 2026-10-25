module
public import CutoffRigidity.Transport
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Actual coupling weak duality for quadratic transport

This proves the easy direction of Kantorovich duality for the existing
primal infimum over actual couplings. It does not assume or claim the
strong duality needed to finish the transportation inequality.
-/
public section
namespace CutoffRigidity
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- Actual integrable dual potentials give a lower bound for the genuine
primal quadratic coupling infimum, with infinite costs included. -/
theorem quadratic_transport_weak_duality
    (μ ν : Measure E) (f g : E → ℝ) (hf : Integrable f μ) (hg : Integrable g ν)
    (hdual : ∀ x y, f x + g y ≤ ‖x-y‖^2) :
    ENNReal.ofReal ((∫ x, f x ∂μ) + ∫ y, g y ∂ν) ≤ squaredWasserstein μ ν := by
  apply le_iInf
  intro π
  by_cases htop : (∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val) = ⊤
  · rw [htop]; exact le_top
  have hfMap : Integrable f (π.val.map Prod.fst) := by rwa [π.property.1]
  have hgMap : Integrable g (π.val.map Prod.snd) := by rwa [π.property.2]
  have hfπ := hfMap.comp_measurable measurable_fst
  have hgπ := hgMap.comp_measurable measurable_snd
  have hcost : Integrable (fun z : E×E => ‖z.1-z.2‖^2) π.val := by
    refine ⟨by fun_prop, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
    have he : (∫⁻ z : E×E, ENNReal.ofReal ‖‖z.1-z.2‖^2‖ ∂π.val) =
        ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
      apply lintegral_congr
      intro z
      rw [Real.norm_of_nonneg (sq_nonneg _),edist_dist,dist_eq_norm,
        ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [he]
    exact lt_top_iff_ne_top.mpr htop
  have hi := integral_mono (hfπ.add hgπ) hcost (fun z : E×E => hdual z.1 z.2)
  simp only [Pi.add_def] at hi
  rw [integral_add hfπ hgπ] at hi
  have hF := integral_map measurable_fst.aemeasurable hfMap.aestronglyMeasurable
  have hG := integral_map measurable_snd.aemeasurable hgMap.aestronglyMeasurable
  rw [π.property.1] at hF
  rw [π.property.2] at hG
  change (∫ z, f z.1 ∂π.val) + (∫ z, g z.2 ∂π.val) ≤ _ at hi
  rw [← hF,← hG] at hi
  calc
    _ ≤ ENNReal.ofReal (∫ z : E×E, ‖z.1-z.2‖^2 ∂π.val) := ENNReal.ofReal_le_ofReal hi
    _ = ∫⁻ z : E×E, ENNReal.ofReal (‖z.1-z.2‖^2) ∂π.val :=
      ofReal_integral_eq_lintegral_ofReal hcost (Filter.Eventually.of_forall fun z => sq_nonneg _)
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [edist_dist,dist_eq_norm,ENNReal.ofReal_pow (norm_nonneg _) 2]

end CutoffRigidity
