module
public import CutoffRigidity.C1EntropyPairing
public import CutoffRigidity.LangevinDensityEvolution

/-! # Genuine de Bruijn identity on positive compact perturbations

The actual Brownian transition derivative and bounded positive densities
justify entropy differentiation. Actual closed-form operator graph pairing
then identifies its derivative with minus canonical Fisher information.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Probability normalization removes the mass terms in the actual KL
formula; actual RN densities give the genuine density entropy integral. -/
theorem klDiv_toReal_withDensity_eq_density_entropy
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))) :
    (klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ).toReal =
      ∫ x, f x * Real.log (f x) ∂μ := by
  let := hν
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have hAC : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hRN : llr ν μ =ᵐ[μ] fun x => Real.log (f x) := by
    filter_upwards [Measure.rnDeriv_withDensity μ hf.ennreal_ofReal] with x hx
    change Real.log ((_ : ENNReal).toReal) = _
    rw [hx, ENNReal.toReal_ofReal (hn x)]
  rw [toReal_klDiv_of_measure_eq hAC (by simp), integral_congr_ae (hAC.ae_eq hRN),
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

/-- Full pointwise time derivative of the actual compact-test transition,
from the proved actual Dynkin identity and continuity of K_t(Lg). -/
theorem hasDerivAt_langevinKernel_integral_compact
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r : ℝ => ∫ y, g y ∂langevinKernel V B P r.toNNReal x)
      (∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P t.toNNReal x) t := by
  obtain ⟨M, hM⟩ := (hasCompactSupport_langevinDifferentialOperator V hgc).exists_bound_of_continuous
    (continuous_langevinDifferentialOperator hV hg)
  have hc := (continuous_langevinKernel_integral_of_bounded_continuous hB hV
    (continuous_langevinDifferentialOperator hV hg) ⟨M, hM⟩ ρ hρ hHess x).comp continuous_real_toNNReal
  have hh := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (g x)
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with r hr
  exact langevinKernel_dynkin_identity hB hV hg hgc ρ hρ hHess x hr.le

/-- Actual zero eigenvalue membership supplies the constant operator graph. -/
private theorem constant_mem_operatorGraph {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (c : ℝ) :
    (gibbsConstantLp hp c, 0) ∈ (gibbsPositiveGenerator hV hp).graph := by
  exact gibbsConstantLp_graph_mem hV hp c

/-- Actual density entropy dissipation for positive constant-plus-compact
C² initial data. Bounds, time differentiation, and operator-domain
integration by parts are all derived from the genuine transition. -/
theorem hasDerivAt_langevin_density_entropy
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    {t : ℝ} (ht : 0 < t) :
    let q := fun s x => c + ∫ y, g y ∂langevinKernel V B P s.toNNReal x
    HasDerivAt (fun s : ℝ => ∫ x, q s x * Real.log (q s x) ∂gibbsMeasure volume V)
      (-(∫ x, ‖gradient (q t) x‖ ^ 2 / q t x ∂gibbsMeasure volume V)) t := by
  let := hp
  let μ := gibbsMeasure volume V
  let q := fun (s : ℝ) (x : E) => c + ∫ y, g y ∂langevinKernel V B P s.toNNReal x
  let D := fun (s : ℝ) (x : E) => ∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P s.toNNReal x
  have hMarkov (s : ℝ≥0) : IsMarkovKernel (langevinKernel V B P s) :=
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨N, hN⟩ := (hasCompactSupport_langevinDifferentialOperator V hgc).exists_bound_of_continuous
    (continuous_langevinDifferentialOperator hV hg)
  let A := |c| + M
  let C := 1 + |Real.log m| + |Real.log A|
  have hqK (s : ℝ) (x : E) : q s x = ∫ y, (c + g y) ∂langevinKernel V B P s.toNNReal x := by
    let := hMarkov s.toNNReal
    have hgI : Integrable g (langevinKernel V B P s.toNNReal x) :=
      (integrable_const M).mono' hg.continuous.aestronglyMeasurable (Eventually.of_forall hM)
    rw [integral_add (integrable_const c) hgI]
    simp [q]
  have hqpos (s : ℝ) (x : E) : m ≤ q s x := by
    let := hMarkov s.toNNReal
    rw [hqK]
    have hInt : Integrable (fun y => c + g y) (langevinKernel V B P s.toNNReal x) :=
      (integrable_const c).add ((integrable_const M).mono' hg.continuous.aestronglyMeasurable (Eventually.of_forall hM))
    have hh := integral_mono (integrable_const m) hInt hpos
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  have hqnorm (s : ℝ) (x : E) : ‖q s x‖ ≤ A := by
    let := hMarkov s.toNNReal
    have hh : ‖∫ y, g y ∂langevinKernel V B P s.toNNReal x‖ ≤ M := by
      simpa using norm_integral_le_of_norm_le_const
        (μ := langevinKernel V B P s.toNNReal x) (Eventually.of_forall hM)
    exact (norm_add_le _ _).trans (add_le_add (by simp) hh)
  have hqup (s : ℝ) (x : E) : q s x ≤ A := (le_abs_self _).trans (hqnorm s x)
  have hqC1 (s : ℝ) : ContDiff ℝ 1 (q s) := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc s.toNNReal)
  have hDN (s : ℝ) (x : E) : ‖D s x‖ ≤ N :=
    langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hN s.toNNReal x
  have hDM (s : ℝ) : Measurable (D s) :=
    (continuous_langevinDifferentialOperator hV hg).measurable.stronglyMeasurable.integral_kernel.measurable
  have hqD (s : ℝ) (hs : 0 < s) (x : E) :
      HasDerivAt (fun r => q r x) (D s x) s :=
    (hasDerivAt_langevinKernel_integral_compact hB hV hg hgc ρ hρ.le hHess x hs).const_add c
  have hLogBound (s : ℝ) (x : E) : ‖1 + Real.log (q s x)‖ ≤ C :=
    norm_one_add_log_le_of_bounds hm (hqpos s x) (hqup s x)
  have hEntropyInt (s : ℝ) : Integrable (fun x => q s x * Real.log (q s x)) μ := by
    have hc := (hqC1 s).continuous.mul ((hqC1 s).continuous.log (fun x => (hm.trans_le (hqpos s x)).ne'))
    apply (integrable_const (A * (C + 1))).mono' hc.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Pi.mul_apply, norm_mul]
    have hLog : ‖Real.log (q s x)‖ ≤ C + 1 := by
      have hh := norm_sub_le (1 + Real.log (q s x)) (1 : ℝ)
      have heq : 1 + Real.log (q s x) - 1 = Real.log (q s x) := by ring
      rw [heq, norm_one] at hh
      linarith [hLogBound s x]
    exact mul_le_mul (hqnorm s x) hLog (norm_nonneg _) ((norm_nonneg _).trans (hqnorm s x))
  have hEntropyD := hasDerivAt_integral_density_mul_log μ q D (Ioi_mem_nhds ht)
    (Eventually.of_forall (fun x s hs => hm.trans_le (hqpos s x)))
    (Eventually.of_forall (fun x s hs => hqD s hs x))
    (Eventually.of_forall (fun s => (hEntropyInt s).aestronglyMeasurable)) (hEntropyInt t)
    (((continuous_const.add ((hqC1 t).continuous.log (fun x => (hm.trans_le (hqpos t x)).ne'))).measurable.mul (hDM t)).aestronglyMeasurable)
    (fun _ => C * N)
    (Eventually.of_forall (fun x s hs => by
      rw [norm_mul]
      exact mul_le_mul (hLogBound s x) (hDN s x) (norm_nonneg _) (by dsimp [C]; positivity)))
    (integrable_const _)
  have hqLp : MemLp (q t) 2 μ := MemLp.of_bound (hqC1 t).continuous.aestronglyMeasurable A
    (Eventually.of_forall (hqnorm t))
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hKLip := lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess
    (hg.of_le (by norm_num)) hgc hLip t.toNNReal
  have hgqLp : MemLp (gradient (q t)) 2 μ := by
    apply MemLp.of_bound (continuous_gradient_of_c1 (hqC1 t)).aestronglyMeasurable
      (Real.exp (-ρ * t.toNNReal) * L)
    apply Eventually.of_forall
    intro x
    change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => c + ∫ z, g z ∂langevinKernel V B P t.toNNReal y) x)‖ ≤ _
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map, fderiv_const_add]
    exact norm_fderiv_le_of_lipschitz ℝ hKLip
  let U := gibbsConstantLp hp c + langevinCompactTestLp hB hV ρ hρ.le hHess hg.continuous hgc μ t.toNNReal
  let H := -langevinCompactTestLp hB hV ρ hρ.le hHess
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc) μ t.toNNReal
  have hGraph : (U, H) ∈ (gibbsPositiveGenerator hV hp).graph := by
    have hh := (gibbsPositiveGenerator hV hp).graph.add_mem (constant_mem_operatorGraph hV hp c)
      (langevinCompactTestLp_mem_operatorGraph hB hV hp ρ hρ hHess hg hgc t.toNNReal)
    simpa only [Prod.mk_add_mk, zero_add] using hh
  have hUrep : U =ᵐ[μ] q t := by
    filter_upwards [Lp.coeFn_add (gibbsConstantLp hp c)
      (langevinCompactTestLp hB hV ρ hρ.le hHess hg.continuous hgc μ t.toNNReal),
      (memLp_const c : MemLp (fun _ : E => c) 2 μ).coeFn_toLp,
      langevinCompactTestLp_coeFn hB hV ρ hρ.le hHess hg.continuous hgc μ t.toNNReal] with x hadd hc hx
    change _ = c + _
    have hc' : (gibbsConstantLp hp c : E → ℝ) x = c := by convert! hc using 1
    rw [hadd, Pi.add_apply, hc', hx]
  have hHrep : H =ᵐ[μ] fun x => -D t x := by
    filter_upwards [Lp.coeFn_neg (langevinCompactTestLp hB hV ρ hρ.le hHess
      (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc) μ t.toNNReal),
      langevinCompactTestLp_coeFn hB hV ρ hρ.le hHess (continuous_langevinDifferentialOperator hV hg)
        (hasCompactSupport_langevinDifferentialOperator V hgc) μ t.toNNReal] with x hneg hx
    rw [hneg, Pi.neg_apply, hx]
  have hIBP := c1_operatorGraph_entropy_pairing hV hp ρ hρ hHess (hqC1 t) hqLp hgqLp
    hm (hqpos t) (hqup t) U H hGraph hUrep hHrep
  simp only [mul_neg, integral_neg] at hIBP
  convert! hEntropyD.2 using 1
  linarith

/-- Genuine de Bruijn identity for the actual evolved probability law.
Only the initial normalized positive compact perturbation domain is
assumed. Every transition derivative, bound, and closed-domain entropy
pairing used in the proof has been derived above. -/
theorem hasDerivAt_klDiv_langevinKernel
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hν : IsProbabilityMeasure ((gibbsMeasure volume V).withDensity
      (fun x => ENNReal.ofReal (c + g x)))) {t : ℝ} (ht : 0 < t) :
    letI := hν
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t.toNNReal
    HasDerivAt (fun s : ℝ =>
      (klDiv (langevinKernel V B P s.toNNReal ∘ₘ
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))))
        (gibbsMeasure volume V)).toReal)
      (-(relativeFisherInformation hV hp (langevinKernel V B P t.toNNReal ∘ₘ
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))))).toReal) t := by
  let := hp
  let := hν
  let μ := gibbsMeasure volume V
  let ν := μ.withDensity (fun x => ENNReal.ofReal (c + g x))
  let q := fun (s : ℝ) (x : E) => c + ∫ y, g y ∂langevinKernel V B P s.toNNReal x
  have hMarkov (s : ℝ≥0) : IsMarkovKernel (langevinKernel V B P s) :=
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s
  let := hMarkov t.toNNReal
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hfm : Measurable (fun x => c + g x) := measurable_const.add hg.continuous.measurable
  have hfBound : ∃ A : ℝ, ∀ x, ‖c + g x‖ ≤ A := by
    exact ⟨|c| + M, fun x => (norm_add_le _ _).trans (add_le_add (by simp) (hM _))⟩
  have hqK (s : ℝ) : (fun x => ∫ y, (c + g y) ∂langevinKernel V B P s.toNNReal x) = q s := by
    let := hMarkov s.toNNReal
    funext x
    have hgI : Integrable g (langevinKernel V B P s.toNNReal x) :=
      (integrable_const M).mono' hg.continuous.aestronglyMeasurable (Eventually.of_forall hM)
    rw [integral_add (integrable_const c) hgI]
    simp [q]
  have hLaw (s : ℝ) : langevinKernel V B P s.toNNReal ∘ₘ ν =
      μ.withDensity (fun x => ENNReal.ofReal (q s x)) := by
    have hh := langevinKernel_withDensity_eq hB hV hp ρ hρ hHess hfm
      (fun x => (hm.trans_le (hpos x)).le) hfBound hν s.toNNReal
    calc
      _ = μ.withDensity (fun x => ENNReal.ofReal (∫ y, (c + g y) ∂langevinKernel V B P s.toNNReal x)) := hh
      _ = _ := by
        congr 1
        funext x
        exact congrArg ENNReal.ofReal (congrFun (hqK s) x)
  have hqtProb (s : ℝ) : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (q s x))) := by
    let := hMarkov s.toNNReal
    rw [← hLaw s]
    infer_instance
  have hqC1 (s : ℝ) : ContDiff ℝ 1 (q s) := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc s.toNNReal)
  have hqpos (s : ℝ) (x : E) : m ≤ q s x := by
    let := hMarkov s.toNNReal
    have hI : Integrable (fun y => c + g y) (langevinKernel V B P s.toNNReal x) :=
      (integrable_const c).add ((integrable_const M).mono' hg.continuous.aestronglyMeasurable (Eventually.of_forall hM))
    have hh := integral_mono (integrable_const m) hI hpos
    have hqx := congrFun (hqK s) x
    rw [hqx] at hh
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  have hKL (s : ℝ) : (klDiv (langevinKernel V B P s.toNNReal ∘ₘ ν) μ).toReal =
      ∫ x, q s x * Real.log (q s x) ∂μ := by
    rw [hLaw s]
    exact klDiv_toReal_withDensity_eq_density_entropy (hqC1 s).continuous.measurable
      (fun x => (hm.trans_le (hqpos s x)).le) (hqtProb s)
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hKLip := lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess
    (hg.of_le (by norm_num)) hgc hLip t.toNNReal
  have hGrad : MemLp (gradient (q t)) 2 μ := by
    apply MemLp.of_bound (continuous_gradient_of_c1 (hqC1 t)).aestronglyMeasurable
      (Real.exp (-ρ * t.toNNReal) * L)
    apply Eventually.of_forall
    intro x
    change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => c + ∫ z, g z ∂langevinKernel V B P t.toNNReal y) x)‖ ≤ _
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map, fderiv_const_add]
    exact norm_fderiv_le_of_lipschitz ℝ hKLip
  let := hqtProb t
  have hFIq := relativeFisherInformation_toReal_withDensity_c1 hV hp ρ hρ hHess
    (hqC1 t) (fun x => hm.trans_le (hqpos t x)) (hqtProb t)
    (integrable_weighted_gradient_of_memLp (hqC1 t) hm (hqpos t) hGrad)
  have hFI : (relativeFisherInformation hV hp (langevinKernel V B P t.toNNReal ∘ₘ ν)).toReal =
      ∫ x, ‖gradient (q t) x‖ ^ 2 / q t x ∂μ := by
    simpa only [hLaw t] using hFIq
  have hEntropy := hasDerivAt_langevin_density_entropy hB hV hp ρ hρ hHess hg hgc c m hm hpos ht
  have hh := hEntropy.congr_of_eventuallyEq (Eventually.of_forall hKL)
  change HasDerivAt (fun s : ℝ => (klDiv (langevinKernel V B P s.toNNReal ∘ₘ ν) μ).toReal)
    (-(∫ x, ‖gradient (q t) x‖ ^ 2 / q t x ∂μ)) t at hh
  rw [← hFI] at hh
  exact hh

/-- Positive interval bounds supply a genuine uniform entropy integrand
bound, including at time zero. -/
private theorem norm_mul_log_le_of_bounds {a m A : ℝ} (hm : 0 < m)
    (hlow : m ≤ a) (hnorm : ‖a‖ ≤ A) :
    ‖a * Real.log a‖ ≤ A * (2 + |Real.log m| + |Real.log A|) := by
  have hup : a ≤ A := (le_abs_self a).trans hnorm
  have hh := norm_one_add_log_le_of_bounds hm hlow hup
  have hlog : ‖Real.log a‖ ≤ 2 + |Real.log m| + |Real.log A| := by
    have ht := norm_sub_le (1 + Real.log a) (1 : ℝ)
    have heq : 1 + Real.log a - 1 = Real.log a := by ring
    rw [heq, norm_one] at ht
    linarith
  rw [norm_mul]
  exact mul_le_mul hnorm hlog (norm_nonneg _) ((norm_nonneg _).trans hnorm)

/-- Actual entropy of the density c+K_tg is continuous at every time,
including zero; positivity and compact initial data derive the domination. -/
theorem continuous_langevin_density_entropy
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x) :
    Continuous (fun s : ℝ≥0 => ∫ x,
      (c + ∫ y, g y ∂langevinKernel V B P s x) *
        Real.log (c + ∫ y, g y ∂langevinKernel V B P s x) ∂gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let q := fun (s : ℝ≥0) (x : E) => c + ∫ y, g y ∂langevinKernel V B P s x
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  let A := |c| + M
  have hMarkov (s : ℝ≥0) : IsMarkovKernel (langevinKernel V B P s) :=
    langevinKernel_isMarkovKernel hB hV ρ hρ hHess s
  have hqnorm (s : ℝ≥0) (x : E) : ‖q s x‖ ≤ A := by
    let := hMarkov s
    have hh : ‖∫ y, g y ∂langevinKernel V B P s x‖ ≤ M := by
      simpa using norm_integral_le_of_norm_le_const
        (μ := langevinKernel V B P s x) (Eventually.of_forall hM)
    exact (norm_add_le _ _).trans (add_le_add (by simp) hh)
  have hqpos (s : ℝ≥0) (x : E) : m ≤ q s x := by
    let := hMarkov s
    have hgI : Integrable g (langevinKernel V B P s x) :=
      (integrable_const M).mono' hg.continuous.aestronglyMeasurable (Eventually.of_forall hM)
    have hh := integral_mono (integrable_const m) ((integrable_const c).add hgI) hpos
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const c) hgI] at hh
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  have hqC (s : ℝ≥0) : Continuous (q s) := continuous_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ hHess hg hgc s).continuous
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ : E => A * (2 + |Real.log m| + |Real.log A|)) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall (fun s => ((hqC s).mul ((hqC s).log
      (fun x => (hm.trans_le (hqpos s x)).ne'))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun s => Eventually.of_forall (fun x =>
      norm_mul_log_le_of_bounds hm (hqpos s x) (hqnorm s x)))
  · apply Eventually.of_forall
    intro x
    have htq : Tendsto (fun s : ℝ≥0 => q s x) (𝓝 t) (𝓝 (q t x)) :=
      (continuous_const.add (continuous_langevinKernel_integral_of_bounded_continuous
        hB hV hg.continuous ⟨M, hM⟩ ρ hρ hHess x)).tendsto t
    exact htq.mul ((Real.continuousAt_log (hm.trans_le (hqpos t x)).ne').tendsto.comp htq)

/-- The actual evolved-law entropy curve is continuous from time zero,
with all normalization and density identifications derived from the true
kernel and its symmetry. -/
theorem continuous_klDiv_langevinKernel
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hν : IsProbabilityMeasure ((gibbsMeasure volume V).withDensity
      (fun x => ENNReal.ofReal (c + g x)))) :
    Continuous (fun s : ℝ≥0 =>
      (klDiv (langevinKernel V B P s ∘ₘ
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))))
        (gibbsMeasure volume V)).toReal) := by
  let := hp
  let := hν
  let μ := gibbsMeasure volume V
  let ν := μ.withDensity (fun x => ENNReal.ofReal (c + g x))
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hfm : Measurable (fun x => c + g x) := measurable_const.add hg.continuous.measurable
  have hBound : ∃ A : ℝ, ∀ x, ‖c + g x‖ ≤ A :=
    ⟨|c| + M, fun x => (norm_add_le _ _).trans (add_le_add (by simp) (hM _))⟩
  apply (continuous_langevin_density_entropy hB hV hp ρ hρ.le hHess hg hgc c m hm hpos).congr
  intro s
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s
  let q := fun x => c + ∫ y, g y ∂langevinKernel V B P s x
  have heq (x : E) : (∫ y, c + g y ∂langevinKernel V B P s x) = q x := by
    have hgI : Integrable g (langevinKernel V B P s x) :=
      (integrable_const M).mono' hg.continuous.aestronglyMeasurable (Eventually.of_forall hM)
    rw [integral_add (integrable_const c) hgI]
    simp [q]
  have hLaw : langevinKernel V B P s ∘ₘ ν = μ.withDensity (fun x => ENNReal.ofReal (q x)) := by
    have hh := langevinKernel_withDensity_eq hB hV hp ρ hρ hHess hfm
      (fun x => (hm.trans_le (hpos x)).le) hBound hν s
    convert! hh using 1
    congr 1
    funext x
    exact congrArg ENNReal.ofReal (heq x).symm
  have hqProb : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (q x))) := by
    rw [← hLaw]
    infer_instance
  have hqC : Continuous q := continuous_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess hg hgc s).continuous
  have hqn (x : E) : 0 ≤ q x := by
    rw [← heq]
    exact integral_nonneg (fun x => (hm.trans_le (hpos x)).le)
  have hh := klDiv_toReal_withDensity_eq_density_entropy hqC.measurable hqn hqProb
  rw [← hLaw] at hh
  exact hh.symm

end CutoffRigidity
