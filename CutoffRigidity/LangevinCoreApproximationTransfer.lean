module
public import CutoffRigidity.LangevinWeakEntropyLimit
public import CutoffRigidity.LangevinFisherLimit
public import CutoffRigidity.RNDensityWeakConvergence
public import CutoffRigidity.LangevinFisherEntropyEndpoint

/-! # Actual information evolution passes through genuine core approximation

Only raw smooth positive densities and their actual L¹ and KL convergence
are supplied here. The evolution estimates are the proved actual core
estimates, and all kernel and information limit transfers are proved.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_rnDeriv_core_density_of_L1
    (μ ν : Measure E) [IsProbabilityMeasure μ]
    (c : ℕ → ℝ) (g : ℕ → E → ℝ) (hg : ∀ n, Measurable (g n))
    (hpos : ∀ n x, 0 ≤ c n + g n x)
    (hlim : Tendsto (fun n => ∫ x, ‖c n + g n x - (ν.rnDeriv μ x).toReal‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,
      |((μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))).rnDeriv μ x).toReal -
        (ν.rnDeriv μ x).toReal| ∂μ) atTop (𝓝 0) := by
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  have hm : Measurable (fun x : E => c n + g n x) := measurable_const.add (hg n)
  filter_upwards [Measure.rnDeriv_withDensity μ hm.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (hpos n x), Real.norm_eq_abs]

section Transfer
variable {d : ℕ}
variable {B : NNReal → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hAC : ν ≪ gibbsMeasure volume V)
    (c : ℕ → ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ∀ n, ContDiff ℝ 2 (g n)) (hgc : ∀ n, HasCompactSupport (g n))
    (hc : ∀ n, 0 < c n) (hpos : ∀ n x, c n ≤ c n + g n x)
    (hNorm : ∀ n, ∫ x, c n + g n x ∂gibbsMeasure volume V = 1)
    (hL1 : Tendsto (fun n => ∫ x, ‖c n + g n x - (ν.rnDeriv (gibbsMeasure volume V) x).toReal‖
      ∂gibbsMeasure volume V) atTop (𝓝 0))
    (hKL : Tendsto (fun n => klDiv ((gibbsMeasure volume V).withDensity
      (fun x => ENNReal.ofReal (c n + g n x))) (gibbsMeasure volume V)) atTop
      (𝓝 (klDiv ν (gibbsMeasure volume V))))

include hB hV hp hρ hHess hAC hg hgc hc hpos hNorm hL1 hKL in
theorem langevinKernel_entropy_contraction_of_core_approx
    (hdim : 0 < d) (T : ℝ) (hT : 0 ≤ T) :
    klDiv (langevinKernel V B P T.toNNReal ∘ₘ ν) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * T)) * klDiv ν (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let νn := fun n => μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))
  have hprob (n : ℕ) : IsProbabilityMeasure (νn n) :=
    (langevin_core_information_finite hB hV hp ρ hρ hHess ((hg n).of_le (by norm_num))
      (hgc n) (c n) (c n) (hc n) (hpos n) (hNorm n)).choose
  let : ∀ n, IsProbabilityMeasure (νn n) := hprob
  have hACn (n : ℕ) : νn n ≪ μ := withDensity_absolutelyContinuous _ _
  have hRN := tendsto_rnDeriv_core_density_of_L1 μ ν c g (fun n => (hg n).continuous.measurable)
    (fun n x => (hc n).le.trans (hpos n x)) hL1
  have hw : ∀ φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, φ x ∂νn n) atTop (𝓝 (∫ x, φ x ∂ν)) :=
    fun φ => tendsto_integral_of_L1_rnDeriv μ ν νn hAC hACn hRN φ
  have hLSC := klDiv_langevinKernel_le_liminf_of_weak hB hV hp ρ hρ.le hHess ν νn hw T.toNNReal
  have hdecay (n : ℕ) : klDiv (langevinKernel V B P T.toNNReal ∘ₘ νn n) μ ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * T)) * klDiv (νn n) μ := by
    have hh := langevinKernel_entropy_contraction_core hB hV hp hdim ρ hρ hHess
      (hg n) (hgc n) (c n) (c n) (hc n) (hpos n) (hNorm n) (s := 0) (t := T) le_rfl hT
    simpa only [Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess,
      Measure.id_comp, sub_zero] using hh
  have hlimit : Tendsto (fun n => ENNReal.ofReal (Real.exp (-2 * ρ * T)) * klDiv (νn n) μ) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-2 * ρ * T)) * klDiv ν μ)) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt.tendsto.comp hKL
  have hb := liminf_le_liminf (f := atTop) (Eventually.of_forall hdecay)
  rw [hlimit.liminf_eq] at hb
  exact hLSC.trans hb

include hB hV hp hρ hHess hAC hg hgc hc hpos hNorm hL1 hKL in
theorem langevinKernel_fisher_entropy_endpoint_of_core_approx
    (T : ℝ) (hT : 0 < T) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
    relativeFisherInformation hV hp (langevinKernel V B P T.toNNReal ∘ₘ ν) ≤
      klDiv ν (gibbsMeasure volume V) / ENNReal.ofReal T := by
  let := hp
  let μ := gibbsMeasure volume V
  let νn := fun n => μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))
  have hprob (n : ℕ) : IsProbabilityMeasure (νn n) :=
    (langevin_core_information_finite hB hV hp ρ hρ hHess ((hg n).of_le (by norm_num))
      (hgc n) (c n) (c n) (hc n) (hpos n) (hNorm n)).choose
  let : ∀ n, IsProbabilityMeasure (νn n) := hprob
  have hACn (n : ℕ) : νn n ≪ μ := withDensity_absolutelyContinuous _ _
  have hRN := tendsto_rnDeriv_core_density_of_L1 μ ν c g (fun n => (hg n).continuous.measurable)
    (fun n x => (hc n).le.trans (hpos n x)) hL1
  have hLSC := relativeFisherInformation_langevinKernel_le_liminf_of_L1_rnDeriv
    hB hV hp ρ hρ hHess ν νn hAC hACn hRN T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  have hbound (n : ℕ) : relativeFisherInformation hV hp (langevinKernel V B P T.toNNReal ∘ₘ νn n) ≤
      klDiv (νn n) μ / ENNReal.ofReal T := by
    obtain ⟨_,hh⟩ := langevinKernel_fisher_entropy_endpoint_core hB hV hp ρ hρ hHess
      (hg n) (hgc n) (c n) (c n) (hc n) (hpos n) (hNorm n) (s := 0) (t := T) le_rfl hT
    simpa only [Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess,
      Measure.id_comp, sub_zero] using hh
  have hlimit : Tendsto (fun n => klDiv (νn n) μ / ENNReal.ofReal T) atTop
      (𝓝 (klDiv ν μ / ENNReal.ofReal T)) := by
    simp only [div_eq_mul_inv]
    exact (ENNReal.continuous_mul_const (by simpa using hT)).continuousAt.tendsto.comp hKL
  have hb := liminf_le_liminf (f := atTop) (Eventually.of_forall hbound)
  rw [hlimit.liminf_eq] at hb
  exact hLSC.trans hb

end Transfer
end CutoffRigidity
