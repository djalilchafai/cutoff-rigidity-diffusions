module
public import CutoffRigidity.LangevinInformationEvolution
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Actual entropy drop controls endpoint Fisher dissipation

The strengthened FTC comparison passes through genuine core approximation,
retaining both the final entropy and final Fisher term. It supports the
written Salez window argument without postulating classical RN smoothness.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Nonnegative extended-real Fatou for two summands. -/
theorem ennreal_liminf_add_le (H I : ℕ → ENNReal) :
    liminf H atTop + liminf I atTop ≤ liminf (fun n => H n + I n) atTop := by
  let f := fun n (b : Fin 2) => if b = 0 then H n else I n
  have hh := lintegral_liminf_le (μ := (Measure.count : Measure (Fin 2)))
    (f := f) (u := atTop) (fun n => measurable_of_countable (f n))
  simpa [lintegral_count,tsum_fintype,Fin.sum_univ_two,f] using hh

theorem entropy_drop_ge_mul_fisher_endpoint
    (H I : ℝ → ℝ) (hH : ContinuousOn H (Ici 0))
    (hD : ∀ r, 0 < r → HasDerivAt H (-I r) r)
    (hI : AntitoneOn I (Ici 0)) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    H t + (t-s)*I t ≤ H s := by
  have hII : IntervalIntegrable I volume s t :=
    (hI.mono (by rw [uIcc_of_le hst.le]; intro r hr; exact hs.trans hr.1)).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst.le
    (hH.mono (fun r hr => hs.trans hr.1))
    (fun r hr => hD r (hs.trans_lt hr.1)) hII.neg
  rw [intervalIntegral.integral_neg] at hFTC
  have hbound := intervalIntegral.integral_mono_on hst.le (intervalIntegrable_const (c := I t)) hII
    (fun r hr => hI (hs.trans hr.1) (hs.trans hst.le) hr.2)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hbound
  nlinarith only [hFTC,hbound]

set_option maxHeartbeats 800000 in
theorem langevinKernel_entropy_fisher_drop_core
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    let ν := (gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))
    ∃ hν : IsProbabilityMeasure ν, letI := hν
      letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t.toNNReal
      klDiv (langevinKernel V B P t.toNNReal ∘ₘ ν) (gibbsMeasure volume V) +
        ENNReal.ofReal (t-s) * relativeFisherInformation hV hp (langevinKernel V B P t.toNNReal ∘ₘ ν) ≤
        klDiv (langevinKernel V B P s.toNNReal ∘ₘ ν) (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let ν := μ.withDensity (fun x => ENNReal.ofReal (c + g x))
  obtain ⟨hν, _hKL0, hFI0⟩ := langevin_core_information_finite hB hV hp ρ hρ hHess
    (hg.of_le (by norm_num)) hgc c m hm hpos hNorm
  refine ⟨hν, ?_⟩
  let := hν
  have hMarkov (r : ℝ) : IsMarkovKernel (langevinKernel V B P r.toNNReal) :=
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r.toNNReal
  let H := fun r : ℝ => (klDiv (langevinKernel V B P r.toNNReal ∘ₘ ν) μ).toReal
  let I := fun r : ℝ => letI := hMarkov r
    (relativeFisherInformation hV hp (langevinKernel V B P r.toNNReal ∘ₘ ν)).toReal
  have hFIfin (r : ℝ) : letI := hMarkov r
      relativeFisherInformation hV hp (langevinKernel V B P r.toNNReal ∘ₘ ν) ≠ ⊤ := by
    let := hMarkov r
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFI0)
      (relativeFisherInformation_langevinKernel_le hB hV hp ρ hρ hHess ν r.toNNReal)
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hKLfin (r : ℝ) : klDiv (langevinKernel V B P r.toNNReal ∘ₘ ν) μ ≠ ⊤ :=
    langevinKernel_klDiv_ne_top_of_bounded_density hB hV hp ρ hρ hHess
      (measurable_const.add hg.continuous.measurable) (fun x => (hm.trans_le (hpos x)).le)
      ⟨|c| + M, fun x => (norm_add_le _ _).trans (add_le_add (by simp) (hM x))⟩ hν r.toNNReal
  have hc : ContinuousOn H (Ici 0) :=
    ((continuous_klDiv_langevinKernel hB hV hp ρ hρ hHess (hg.of_le (by norm_num)) hgc c m hm hpos hν).comp
      continuous_real_toNNReal).continuousOn
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt H (-I r) r :=
    hasDerivAt_klDiv_langevinKernel hB hV hp ρ hρ hHess hg hgc c m hm hpos hν hr
  have hIanti : AntitoneOn I (Ici 0) := by
    intro a _ha b _hb hab
    let := hMarkov a
    let := hMarkov b
    exact ENNReal.toReal_mono (hFIfin a)
      (relativeFisherInformation_langevinKernel_antitone hB hV hp ρ hρ hHess ν
        a.toNNReal b.toNNReal (Real.toNNReal_mono hab))
  have hh := entropy_drop_ge_mul_fisher_endpoint H I hc hd hIanti hs hst
  let := hMarkov t
  have he := ENNReal.ofReal_le_ofReal hh
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg (sub_pos.mpr hst).le ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (sub_pos.mpr hst).le, ENNReal.ofReal_toReal (hFIfin t),
    ENNReal.ofReal_toReal (hKLfin t), ENNReal.ofReal_toReal (hKLfin s)] at he
  exact he

set_option maxHeartbeats 800000 in
/-- Genuine full-domain dissipation: the entropy drop bounds endpoint
Fisher information. All approximation and information estimates are derived. -/
theorem langevinKernel_entropy_fisher_drop
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
    klDiv (langevinKernel V B P T.toNNReal ∘ₘ ν) (gibbsMeasure volume V) +
      ENNReal.ofReal T * relativeFisherInformation hV hp (langevinKernel V B P T.toNNReal ∘ₘ ν) ≤
        klDiv ν (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P T.toNNReal
  let : IsMarkovKernel K := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  by_cases hfin : klDiv ν μ ≠ ⊤
  · have hAC := (klDiv_ne_top_iff.mp hfin).1
    obtain ⟨c,g,hg,hgc,hc,hFloor,hNorm,hL1,hKL⟩ :=
      exists_finite_entropy_probability_core_L1_KL_approx μ ν hAC hfin
    let νn := fun n => μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))
    have hprob (n : ℕ) : IsProbabilityMeasure (νn n) :=
      (langevin_core_information_finite hB hV hp ρ hρ hHess ((hg n).of_le (by norm_num))
        (hgc n) (c n) (c n) (hc n) (hFloor n) (hNorm n)).choose
    let : ∀ n, IsProbabilityMeasure (νn n) := hprob
    have hACn (n : ℕ) : νn n ≪ μ := withDensity_absolutelyContinuous _ _
    have hRN := tendsto_rnDeriv_core_density_of_L1 μ ν c g (fun n => (hg n).continuous.measurable)
      (fun n x => (hc n).le.trans (hFloor n x)) hL1
    have hweak : ∀ φ : E →ᵇ ℝ, Tendsto (fun n => ∫ x, φ x ∂νn n) atTop (𝓝 (∫ x, φ x ∂ν)) :=
      fun φ => tendsto_integral_of_L1_rnDeriv μ ν νn hAC hACn hRN φ
    let H := fun n => klDiv (K ∘ₘ νn n) μ
    let I := fun n => relativeFisherInformation hV hp (K ∘ₘ νn n)
    have hH := klDiv_langevinKernel_le_liminf_of_weak hB hV hp ρ hρ.le hHess ν νn hweak T.toNNReal
    have hI := relativeFisherInformation_langevinKernel_le_liminf_of_L1_rnDeriv
      hB hV hp ρ hρ hHess ν νn hAC hACn hRN T.toNNReal
    have hmul : ENNReal.ofReal T * relativeFisherInformation hV hp (K ∘ₘ ν) ≤
        liminf (fun n => ENNReal.ofReal T * I n) atTop := by
      apply (mul_le_mul' le_rfl hI).trans
      have hh := ENNReal.le_liminf_mul (u := fun _ : ℕ => ENNReal.ofReal T) (v := I) (f := atTop)
      convert! hh using 1 <;> simp only [liminf_const,Pi.mul_apply,I,K]
    have hadd : liminf H atTop + liminf (fun n => ENNReal.ofReal T * I n) atTop ≤
        liminf (fun n => H n + ENNReal.ofReal T * I n) atTop := by
      exact ennreal_liminf_add_le H (fun n => ENNReal.ofReal T * I n)
    have hcore (n : ℕ) : H n + ENNReal.ofReal T * I n ≤ klDiv (νn n) μ := by
      obtain ⟨_,hh⟩ := langevinKernel_entropy_fisher_drop_core hB hV hp ρ hρ hHess
        (hg n) (hgc n) (c n) (c n) (hc n) (hFloor n) (hNorm n) (s := 0) (t := T) le_rfl hT
      simpa only [Real.toNNReal_zero,langevinKernel_zero hB hV ρ hρ.le hHess,
        Measure.id_comp,sub_zero] using hh
    have hb := liminf_le_liminf (f := atTop) (Eventually.of_forall hcore)
    rw [hKL.liminf_eq] at hb
    exact ((add_le_add hH hmul).trans hadd).trans hb
  · rw [not_ne_iff.mp hfin]
    exact le_top

end CutoffRigidity
