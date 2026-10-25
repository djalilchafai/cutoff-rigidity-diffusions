module

public import CutoffRigidity.GibbsSobolevClassical
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Actual extended-valued relative Fisher information

For finite measures, Fisher information is four times the actual closed
Gibbs energy of the square root of the Radon--Nikodym density. It is infinite
outside absolute continuity or the genuine closed gradient domain. This
definition uses actual equivalence classes and is independent of pointwise
choices of density representatives.
-/

public section

namespace CutoffRigidity

open MeasureTheory

section Density

variable {X : Type*} [MeasurableSpace X]

@[expose] noncomputable def squareRootRNDensity (ν μ : Measure X) : X → ℝ :=
  fun x => Real.sqrt ((ν.rnDeriv μ x).toReal)

theorem squareRootRNDensity_measurable (ν μ : Measure X) :
    Measurable (squareRootRNDensity ν μ) :=
  (Measure.measurable_rnDeriv ν μ).ennreal_toReal.sqrt

theorem squareRootRNDensity_sq (ν μ : Measure X) (x : X) :
    squareRootRNDensity ν μ x ^ 2 = (ν.rnDeriv μ x).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

/-- The actual square-root density is in L² for every finite measure. -/
theorem squareRootRNDensity_memLp (ν μ : Measure X) [IsFiniteMeasure ν] :
    MemLp (squareRootRNDensity ν μ) 2 μ := by
  apply (memLp_two_iff_integrable_sq (squareRootRNDensity_measurable ν μ).aestronglyMeasurable).mpr
  simp_rw [squareRootRNDensity_sq]
  simpa only [integrableOn_univ] using
    (Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := μ) (s := Set.univ) (measure_ne_top ν _))

@[expose] noncomputable def squareRootRNDensityLp (ν μ : Measure X) [IsFiniteMeasure ν] :
    X →₂[μ] ℝ := (squareRootRNDensity_memLp ν μ).toLp (squareRootRNDensity ν μ)

/-- Absolute continuity gives the exact total mass of the square-root energy. -/
theorem integral_squareRootRNDensity_sq (ν μ : Measure X) [SigmaFinite ν] [SigmaFinite μ]
    (hν : ν ≪ μ) :
    (∫ x, squareRootRNDensity ν μ x ^ 2 ∂μ) = ν.real Set.univ := by
  simp_rw [squareRootRNDensity_sq]
  exact Measure.integral_toReal_rnDeriv hν

end Density

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual extended-valued relative Fisher information for the Gibbs
measure. All derivative-domain requirements are part of the functional,
not additional hypotheses on a probability law. -/
@[expose] noncomputable def relativeFisherInformation {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ν : Measure E) [IsFiniteMeasure ν] :
    ENNReal := by
  classical
  let u := squareRootRNDensityLp ν (gibbsMeasure volume V)
  let G := closedGibbsGradient hV hprob
  exact if _hAC : ν ≪ gibbsMeasure volume V then
    if hD : u ∈ G.domain then ENNReal.ofReal (4 * ‖G ⟨u, hD⟩‖ ^ 2) else ⊤
  else ⊤

/-- Singular laws have infinite relative Fisher information by definition. -/
theorem relativeFisherInformation_eq_top_of_not_ac {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ν : Measure E) [IsFiniteMeasure ν]
    (hν : ¬ν ≪ gibbsMeasure volume V) : relativeFisherInformation hV hprob ν = ⊤ := by
  simp only [relativeFisherInformation, hν, dite_false]

/-- On its actual closed Sobolev domain the functional is the genuine
closed-gradient energy, with the standard factor four. -/
theorem relativeFisherInformation_eq_closed_energy {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ν : Measure E) [IsFiniteMeasure ν]
    (hν : ν ≪ gibbsMeasure volume V)
    (hD : squareRootRNDensityLp ν (gibbsMeasure volume V) ∈ (closedGibbsGradient hV hprob).domain) :
    relativeFisherInformation hV hprob ν =
      ENNReal.ofReal (4 * ‖closedGibbsGradient hV hprob
        ⟨squareRootRNDensityLp ν (gibbsMeasure volume V), hD⟩‖ ^ 2) := by
  simp only [relativeFisherInformation, hν, dite_true, hD]

/-- A genuine C² square-root representative has the expected actual Fisher
integral whenever its gradient is in L². The representative is identified
with the actual Radon--Nikodym density, rather than chosen arbitrarily. -/
theorem relativeFisherInformation_eq_of_c2_squareRoot {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsFiniteMeasure ν] (hν : ν ≪ gibbsMeasure volume V)
    (hg : ContDiff ℝ 2 g)
    (hRN : squareRootRNDensity ν (gibbsMeasure volume V) =ᵐ[gibbsMeasure volume V] g)
    (hgrad : MemLp (gradient g) 2 (gibbsMeasure volume V)) :
    relativeFisherInformation hV hprob ν =
      ENNReal.ofReal (4 * ∫ x, ‖gradient g x‖ ^ 2 ∂gibbsMeasure volume V) := by
  have hglp : MemLp g 2 (gibbsMeasure volume V) :=
    (memLp_congr_ae hRN).mp (squareRootRNDensity_memLp ν (gibbsMeasure volume V))
  have heq : squareRootRNDensityLp ν (gibbsMeasure volume V) = hglp.toLp g :=
    MemLp.toLp_congr _ _ hRN
  let G := closedGibbsGradient hV hprob
  have hgraph : (hglp.toLp g, hgrad.toLp (gradient g)) ∈ G.graph :=
    c2_function_mem_closedGibbsGradient_graph hV hprob hg hglp hgrad
  rw [← heq] at hgraph
  have hD : squareRootRNDensityLp ν (gibbsMeasure volume V) ∈ G.domain :=
    G.mem_domain_of_mem_graph hgraph
  have hval : G ⟨squareRootRNDensityLp ν (gibbsMeasure volume V), hD⟩ =
      hgrad.toLp (gradient g) := (G.image_iff hD).mpr hgraph |>.symm
  rw [relativeFisherInformation_eq_closed_energy hV hprob ν hν hD, hval]
  have hn : ‖hgrad.toLp (gradient g)‖ ^ 2 =
      ∫ x, ‖gradient g x‖ ^ 2 ∂gibbsMeasure volume V := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgrad.coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  rw [hn]

/-- For an actual normalized smooth square density, the Radon--Nikodym
identification and absolute continuity are derived from `withDensity`. -/
theorem relativeFisherInformation_withDensity_square {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgn : ∀ x, 0 ≤ g x)
    (hνprob : IsProbabilityMeasure
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (g x ^ 2))))
    (hgrad : MemLp (gradient g) 2 (gibbsMeasure volume V)) :
    letI := hνprob
    relativeFisherInformation hV hprob
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (g x ^ 2))) =
        ENNReal.ofReal (4 * ∫ x, ‖gradient g x‖ ^ 2 ∂gibbsMeasure volume V) := by
  have := hνprob
  have := hprob
  apply relativeFisherInformation_eq_of_c2_squareRoot hV hprob _
    (withDensity_absolutelyContinuous _ _) hg
  · have hrn := Measure.rnDeriv_withDensity (gibbsMeasure volume V)
      (hg.continuous.measurable.pow_const 2).ennreal_ofReal
    filter_upwards [hrn] with x hx
    change Real.sqrt ((_ : ENNReal).toReal) = g x
    rw [hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (hgn x)]
  · exact hgrad

/-- Equilibrium has zero actual relative Fisher information. -/
theorem relativeFisherInformation_self {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    letI := hprob
    relativeFisherInformation hV hprob (gibbsMeasure volume V) = 0 := by
  have := hprob
  have hg : MemLp (gradient (fun _ : E => (1 : ℝ))) 2 (gibbsMeasure volume V) := by
    rw [gradient_fun_const']
    exact memLp_const (0 : E)
  have hRN : squareRootRNDensity (gibbsMeasure volume V) (gibbsMeasure volume V) =ᵐ[gibbsMeasure volume V]
      fun _ => (1 : ℝ) := by
    filter_upwards [Measure.rnDeriv_self (gibbsMeasure volume V)] with x hx
    change Real.sqrt ((_ : ENNReal).toReal) = 1
    rw [hx]
    norm_num
  have h := relativeFisherInformation_eq_of_c2_squareRoot hV hprob (gibbsMeasure volume V)
    Measure.AbsolutelyContinuous.rfl contDiff_const hRN hg
  simpa only [gradient_fun_const, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    integral_zero, mul_zero, ENNReal.ofReal_zero] using h

end CutoffRigidity
