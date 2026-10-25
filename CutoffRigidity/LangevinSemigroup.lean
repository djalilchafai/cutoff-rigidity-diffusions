module

public import CutoffRigidity.LangevinKernel
public import CutoffRigidity.BrownianIndependence
public import CutoffRigidity.LangevinFlow
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Brownian restart laws for the actual Langevin semigroup

Brownian future increments have the original Brownian path law and are
independent from the past. These statements are lifted from genuine raw
process laws to actual continuous-path laws using their evaluation-generated
Borel algebra. No measurable-embedding assertion is made for the set of all
continuous functions inside an uncountable raw product space.
-/

public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace CutoffRigidity

section ContinuousPathBorel

variable {D F Ω : Type*} [TopologicalSpace D] [SecondCountableTopology D]
  [LocallyCompactSpace D] [NormedAddCommGroup F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Ω]

/-- The actual continuous-path Borel algebra is induced by raw evaluation.
This equality suffices for law and independence arguments; it does not assert
that the range of continuous functions is a measurable raw-product subset. -/
theorem continuousMap_measurableSpace_eq_comap_coe :
    (ContinuousMap.measurableSpace (X := D) (Y := F)) =
      (inferInstance : MeasurableSpace (D → F)).comap (fun f : C(D, F) => fun t => f t) := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-- Equality of raw path pushforwards determines measures on continuous paths. -/
theorem continuousMap_measure_eq_of_coe_map_eq (μ ν : Measure C(D, F))
    (h : μ.map (fun f : C(D, F) => fun t => f t) =
      ν.map (fun f : C(D, F) => fun t => f t)) : μ = ν := by
  have hm : Measurable (fun f : C(D, F) => fun t => f t) :=
    Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)
  ext S hS
  rw [continuousMap_measurableSpace_eq_comap_coe (D := D) (F := F)] at hS
  obtain ⟨A, hA, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hS
  exact ((Measure.map_apply hm hA).symm.trans (congrArg (fun m => m A) h)).trans
    (Measure.map_apply hm hA)

/-- Independence of raw evaluations implies independence of the actual
continuous-path-valued random variable, by its induced measurable structure. -/
theorem indepFun_continuousMap_left_of_coe
    {G : Type*} [MeasurableSpace G] {P : Measure Ω} {f : Ω → C(D, F)} {g : Ω → G}
    (h : IndepFun (fun ω t => f ω t) g P) : IndepFun f g P := by
  rw [IndepFun_iff_Indep, continuousMap_measurableSpace_eq_comap_coe (D := D) (F := F),
    MeasurableSpace.comap_comp]
  exact (IndepFun_iff_Indep _ _ _).mp h

end ContinuousPathBorel

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

/-- Actual independent Euclidean Brownian motions have identical raw full-path
laws, proved from the scalar finite-dimensional Brownian laws and coordinate
independence. -/
theorem euclideanBrownian_identDistrib_path
    {B C : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (hC : IsEuclideanBrownian C P) :
    IdentDistrib (fun ω t => B t ω) (fun ω t => C t ω) P P := by
  let := hB.isProbabilityMeasure
  have hBm (i : ι) := realBrownian_aemeasurable_path (hB.coordinate i)
  have hCm (i : ι) := realBrownian_aemeasurable_path (hC.coordinate i)
  have hscalar (i : ι) : P.map (fun ω t => B t ω i) = P.map (fun ω t => C t ω i) := by
    apply (map_eq_iff_forall_finset_map_restrict_eq (hBm i) (hCm i)).mpr
    intro I
    exact ((hB.coordinate i).hasLaw I).map_eq.trans ((hC.coordinate i).hasLaw I).map_eq.symm
  have hBLaw := hB.independent.hasLaw_pi (fun i => hasLaw_map (hBm i))
  have hCLaw := hC.independent.hasLaw_pi (fun i =>
    (show HasLaw (fun ω t => C t ω i) (P.map (fun ω t => B t ω i)) P from
      ⟨hCm i, (hscalar i).symm⟩))
  have hΦ : Measurable (fun f : ι → ℝ≥0 → ℝ => fun t => WithLp.toLp 2 (fun i => f i t)) := by
    fun_prop
  exact (hBLaw.identDistrib hCLaw).comp hΦ

/-- Actual continuous Brownian driving-path laws are determined by the
Brownian assumptions, independent of the particular Brownian realization. -/
theorem brownianNoiseLaw_eq_of_brownian
    {B C : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (hC : IsEuclideanBrownian C P) :
    brownianNoiseLaw B P = brownianNoiseLaw C P := by
  have hraw := euclideanBrownian_identDistrib_path hB hC
  have hΦ : Measurable (fun f : ℝ≥0 → E => fun t : ℝ => Real.sqrt 2 • f t.toNNReal) := by
    fun_prop
  have hnoise := hraw.comp hΦ
  have hBm := brownianContinuousDrivingPath_aemeasurable hB
  have hCm := brownianContinuousDrivingPath_aemeasurable hC
  have hcoe : Measurable (fun f : C(ℝ, E) => fun t => f t) :=
    Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)
  apply continuousMap_measure_eq_of_coe_map_eq
  rw [brownianNoiseLaw, brownianNoiseLaw,
    hcoe.aemeasurable.map_map_of_aemeasurable hBm,
    hcoe.aemeasurable.map_map_of_aemeasurable hCm]
  exact (Measure.map_congr (brownianContinuousDrivingPath_coe_ae hB)).trans
    (hnoise.map_eq.trans (Measure.map_congr (brownianContinuousDrivingPath_coe_ae hC)).symm)

/-- The genuine Brownian future-increment driving-path law is the original
continuous Brownian driving law. -/
theorem brownianNoiseLaw_shift
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P) (s : ℝ≥0) :
    brownianNoiseLaw (fun t ω => B (s + t) ω - B s ω) P = brownianNoiseLaw B P :=
  brownianNoiseLaw_eq_of_brownian (hB.shift s) hB

omit [DecidableEq ι] in
/-- The actual continuous future driving path is independent from the whole
raw vector past. -/
theorem brownianContinuousDrivingPath_indep_past
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P) (s : ℝ≥0) :
    IndepFun (brownianContinuousDrivingPath (fun t ω => B (s + t) ω - B s ω))
      (fun ω (t : Iic s) => B t ω) P := by
  have hΦ : Measurable (fun f : ℝ≥0 → E => fun t : ℝ => Real.sqrt 2 • f t.toNNReal) := by
    fun_prop
  have hraw := (hB.indepFun_shift s).comp hΦ measurable_id
  have heq := brownianContinuousDrivingPath_coe_ae (hB.shift s)
  apply indepFun_continuousMap_left_of_coe
  exact hraw.congr heq.symm Filter.EventuallyEq.rfl

omit [DecidableEq ι] in
/-- The actual continuous future driving path is independent of the actual
continuous finite-interval noise history. -/
theorem brownianContinuousDrivingPath_indep_history
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P) (s : ℝ≥0) :
    IndepFun (brownianContinuousDrivingPath (fun t ω => B (s + t) ω - B s ω))
      (fun ω => (brownianContinuousDrivingPath B ω).restrict (Icc 0 (s : ℝ))) P := by
  have htime (t : Icc 0 (s : ℝ)) : t.1.toNNReal ≤ s := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal t.1 t.2.1]
    exact t.2.2
  let Φ : (Iic s → E) → (Icc 0 (s : ℝ) → E) :=
    fun f t => Real.sqrt 2 • f ⟨t.1.toNNReal, htime t⟩
  have hΦ : Measurable Φ := by fun_prop
  have hraw := (brownianContinuousDrivingPath_indep_past hB s).comp measurable_id hΦ
  have heq : (fun ω => Φ (fun t : Iic s => B t ω)) =ᵐ[P]
      (fun ω => fun t : Icc 0 (s : ℝ) =>
        ((brownianContinuousDrivingPath B ω).restrict (Icc 0 (s : ℝ))) t) := by
    filter_upwards [brownianContinuousDrivingPath_coe_ae hB] with ω hω
    funext t
    exact (congrFun hω t.1).symm
  have hraw' := hraw.congr Filter.EventuallyEq.rfl heq
  exact (indepFun_continuousMap_left_of_coe hraw'.symm).symm

omit [DecidableEq ι] in
/-- The actual state at time s is independent of the continuous future noise,
proved by nonanticipative evaluation of the actual finite-interval history. -/
theorem langevinProcess_indep_future_noise
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s : ℝ≥0) :
    IndepFun (langevinProcess V B x₀ s)
      (brownianContinuousDrivingPath (fun t ω => B (s + t) ω - B s ω)) P := by
  have hm : Measurable (fun w : C(Icc 0 (s : ℝ), E) =>
      intervalLangevinEvaluation V s.property (x₀, w)) :=
    ((intervalLangevinEvaluation_continuous hV rate hrate hHess s.property).comp
      (continuous_const.prodMk continuous_id)).measurable
  have h := (brownianContinuousDrivingPath_indep_history hB s).symm.comp hm measurable_id
  have heq : (fun ω => intervalLangevinEvaluation V s.property
      (x₀, (brownianContinuousDrivingPath B ω).restrict (Icc 0 (s : ℝ)))) =ᵐ[P]
      langevinProcess V B x₀ s := by
    filter_upwards [brownianContinuousDrivingPath_coe_ae hB] with ω hω
    exact (intervalLangevinEvaluation_restrict hV rate hrate hHess s.property x₀
      (brownianContinuousDrivingPath B ω)).trans
      (congrArg (fun w => langevinSolution V w x₀ (s : ℝ)) hω)
  exact h.congr heq Filter.EventuallyEq.rfl

omit [DecidableEq ι] in
/-- Only noise increments matter in the actual integral equation. -/
theorem langevinSolution_eqOn_of_noise_increments_eqOn
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w v : ℝ → E} (hw : Continuous w) (hv : Continuous v) (x₀ : E)
    {T : ℝ} (hT : 0 ≤ T)
    (heq : ∀ t ∈ Icc 0 T, w t - w 0 = v t - v 0) :
    EqOn (langevinSolution V w x₀) (langevinSolution V v x₀) (Icc 0 T) := by
  have hX := langevinSolution_isLangevinPathOn hV rate hrate hHess hw x₀ hT
  have hXv : IsLangevinPathOn V v x₀ (langevinSolution V w x₀) T := by
    refine ⟨hX.1, ?_⟩
    intro t ht
    rw [← heq t ht]
    exact hX.2 t ht
  exact langevin_path_unique hV rate hHess hXv
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hv x₀ hT)

omit [DecidableEq ι] in
/-- The deterministic cocycle restarts the actual Brownian-driven solution
using the actual continuous future-increment path, almost surely. -/
theorem langevinProcess_restart_ae
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s t : ℝ≥0) :
    (fun ω => langevinEvaluation V t (langevinProcess V B x₀ s ω,
      brownianContinuousDrivingPath (fun r ω => B (s + r) ω - B s ω) ω)) =ᵐ[P]
      langevinProcess V B x₀ (s + t) := by
  filter_upwards [brownianDrivingPath_continuous_ae hB,
    brownianDrivingPath_continuous_ae (hB.shift s),
    brownianContinuousDrivingPath_coe_ae (hB.shift s)] with ω hω hωs hcoe
  let w := brownianDrivingPath B ω
  let v := brownianDrivingPath (fun r ω => B (s + r) ω - B s ω) ω
  have hinc (u : ℝ) (hu : u ∈ Icc 0 (t : ℝ)) :
      w ((s : ℝ) + u) - w ((s : ℝ) + 0) = v u - v 0 := by
    have htime : ((s : ℝ) + u).toNNReal = s + u.toNNReal := by
      apply NNReal.coe_injective
      calc
        (((s : ℝ) + u).toNNReal : ℝ) = (s : ℝ) + u :=
          Real.coe_toNNReal _ (add_nonneg s.property hu.1)
        _ = (s : ℝ) + (u.toNNReal : ℝ) :=
          congrArg (fun a : ℝ => (s : ℝ) + a) (Real.coe_toNNReal u hu.1).symm
        _ = ((s + u.toNNReal : ℝ≥0) : ℝ) := (NNReal.coe_add _ _).symm
    simp only [w, v, brownianDrivingPath, add_zero, Real.toNNReal_coe, Real.toNNReal_zero,
      sub_self, smul_zero, sub_zero, htime, smul_sub]
  have hsame := langevinSolution_eqOn_of_noise_increments_eqOn hV rate hrate hHess
    (hω.comp (continuous_const.add continuous_id)) hωs (langevinSolution V w x₀ s)
    t.property hinc ⟨t.property, le_rfl⟩
  have hcocycle := langevinSolution_cocycle hV rate hrate hHess hω x₀ s.property t.property
  change langevinSolution V
    (brownianContinuousDrivingPath (fun r ω => B (s + r) ω - B s ω) ω)
      (langevinSolution V w x₀ s) t = langevinSolution V w x₀ ((s + t : ℝ≥0) : ℝ)
  rw [hcoe]
  exact hsame.symm.trans hcocycle.symm

/-- The actual Brownian-driven nonlinear Langevin kernels satisfy the Markov
semigroup law. It follows from genuine Brownian future/past independence,
the proved future-noise law, and the actual deterministic restart identity. -/
theorem langevinKernel_comp
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (s t : ℝ≥0) :
    langevinKernel V B P t ∘ₖ langevinKernel V B P s = langevinKernel V B P (s + t) := by
  let := hB.isProbabilityMeasure
  let := brownianNoiseLaw_isProbabilityMeasure hB
  let := langevinKernel_isMarkovKernel hB hV rate hrate hHess s
  have hm := (langevinEvaluation_continuous hV rate hrate hHess t).measurable
  apply Kernel.ext
  intro x
  have hX := langevinProcess_aemeasurable_eval hB hV rate hrate hHess x s
  have hW := brownianContinuousDrivingPath_aemeasurable (hB.shift s)
  have hprod := (langevinProcess_indep_future_noise hB hV rate hrate hHess x s).map_prod_eq_prod_map_map
    hX hW
  have hNoise : P.map (brownianContinuousDrivingPath (fun r ω => B (s + r) ω - B s ω)) =
      brownianNoiseLaw B P := brownianNoiseLaw_shift hB s
  rw [hNoise] at hprod
  change langevinKernel V B P t ∘ₘ (langevinKernel V B P s x) = langevinKernel V B P (s + t) x
  rw [langevinKernel_comp_eq_randomMapLaw hB hV rate hrate hHess,
    langevinKernel_apply_eq_process_law hB hV rate hrate hHess s x]
  change ((P.map (langevinProcess V B x s)).prod (brownianNoiseLaw B P)).map
    (langevinEvaluation V t) = _
  rw [← hprod, hm.aemeasurable.map_map_of_aemeasurable (hX.prodMk hW),
    langevinKernel_apply_eq_process_law hB hV rate hrate hHess]
  exact Measure.map_congr (langevinProcess_restart_ae hB hV rate hrate hHess x s t)

end CutoffRigidity
