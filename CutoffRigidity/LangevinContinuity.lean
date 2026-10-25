module

public import CutoffRigidity.LangevinNoiseDependence
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.ProjIcc

/-!
# Joint continuity in the initial point and continuous noise

Noise on a fixed compact time interval carries its actual uniform topology.
It is extended constantly outside that interval by the continuous interval
projection. Uniform bounds for nearby initial points and noise paths give one
compact spatial ball containing all corresponding solutions. The actual `C¹`
gradient is Lipschitz on that ball, so the previously proved quantitative
estimate establishes local Lipschitz continuity of solution evaluation.
-/

public section

open Set Metric MeasureTheory
open scoped Topology NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E]

/-- Continuous constant extension of noise outside its compact time interval. -/
@[expose] noncomputable def intervalNoiseExtension {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T, E)) : ℝ → E :=
  IccExtend hT w

theorem intervalNoiseExtension_continuous {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T, E)) :
    Continuous (intervalNoiseExtension hT w) := w.continuous.Icc_extend'

theorem intervalNoiseExtension_norm_le {T : ℝ} (hT : 0 ≤ T)
    (w : C(Icc 0 T, E)) (s : ℝ) : ‖intervalNoiseExtension hT w s‖ ≤ ‖w‖ :=
  w.norm_coe_le_norm (projIcc 0 T hT s)

theorem intervalNoiseExtension_sub_norm_le {T : ℝ} (hT : 0 ≤ T)
    (w v : C(Icc 0 T, E)) (s : ℝ) :
    ‖intervalNoiseExtension hT w s - intervalNoiseExtension hT v s‖ ≤ ‖w - v‖ :=
  (w - v).norm_coe_le_norm (projIcc 0 T hT s)

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual solution evaluated at the fixed final time, as a function of
its initial point and compact-interval noise path. -/
@[expose] noncomputable def intervalLangevinEvaluation
    (V : E → ℝ) {T : ℝ} (hT : 0 ≤ T) (p : E × C(Icc 0 T, E)) : E :=
  langevinSolution V (intervalNoiseExtension hT p.2) p.1 T

/-- Bounded initial points and uniformly bounded compact-interval noise give
a shared finite spatial bound for all actual corresponding solutions. -/
theorem exists_uniform_interval_solution_bound [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {T A W : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    ∃ B ≥ (0 : ℝ), ∀ x₀ : E, ‖x₀‖ ≤ A → ∀ w : C(Icc 0 T, E), ‖w‖ ≤ W →
      ∀ t ∈ Icc 0 T,
        ‖langevinSolution V (intervalNoiseExtension hT w) x₀ t‖ ≤ B := by
  have hgrad := (differentiable_gradient_of_contDiff_two hV).continuous
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : E) (2 * W)).exists_bound_of_continuousOn
    hgrad.continuousOn
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  let C := Real.exp T * (A ^ 2 + M ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Real.sqrt C + 2 * W, by positivity, ?_⟩
  intro x₀ hx₀ w hw t ht
  let v := intervalNoiseExtension hT w
  have hv : Continuous v := intervalNoiseExtension_continuous hT w
  have hvinc (s : ℝ) : ‖v s - v 0‖ ≤ 2 * W := by
    have h := norm_sub_le (v s) (v 0)
    have hs := (intervalNoiseExtension_norm_le hT w s).trans hw
    have h0 := (intervalNoiseExtension_norm_le hT w 0).trans hw
    linarith
  have hMbound : ∀ s ∈ Icc 0 T, ‖gradient V (v s - v 0)‖ ≤ M := by
    intro s _
    exact (hM₀ (v s - v 0) (by simpa only [mem_closedBall, dist_zero_right] using hvinc s)).trans
      (le_max_left _ _)
  have hpath := langevinSolution_isLangevinPathOn hV rate hrate hHess hv x₀ ht.1
  have henergy := langevin_compensated_energy_bound hV rate hrate hHess hv.continuousOn
    ht hM hMbound hpath
  have hx₀sq : ‖x₀‖ ^ 2 ≤ A ^ 2 := (sq_le_sq₀ (norm_nonneg _) hA).mpr hx₀
  have hCbound : ‖langevinSolution V v x₀ t - (v t - v 0)‖ ^ 2 ≤ C := by
    apply henergy.trans
    exact mul_le_mul_of_nonneg_left (add_le_add hx₀sq le_rfl) (Real.exp_nonneg _)
  have hnorm : ‖langevinSolution V v x₀ t - (v t - v 0)‖ ≤ Real.sqrt C := by
    have hsqrt := Real.sq_sqrt hC
    have hsqrt0 := Real.sqrt_nonneg C
    nlinarith [norm_nonneg (langevinSolution V v x₀ t - (v t - v 0))]
  exact (norm_le_norm_sub_add (langevinSolution V v x₀ t) (v t - v 0)).trans
    (add_le_add hnorm (hvinc t))

/-- Around each input, one compact spatial ball gives a uniform Lipschitz
constant for the actual potential gradient along every nearby trajectory. -/
theorem intervalLangevinEvaluation_locally_lipschitz [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {T : ℝ} (hT : 0 ≤ T) (p : E × C(Icc 0 T, E)) :
    ∃ L : ℝ≥0, LipschitzOnWith L (intervalLangevinEvaluation V hT) (closedBall p 1) := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_interval_solution_bound hV rate hrate hHess hT
    (A := ‖p.1‖ + 1) (W := ‖p.2‖ + 1) (by positivity) (by positivity)
  let Riesz : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad : ContDiff ℝ 1 (gradient V) :=
    Riesz.contDiff.comp (hV.fderiv_right (m := 1) (by norm_num))
  obtain ⟨K, hLip⟩ := hgrad.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) B) (isCompact_closedBall (0 : E) B)
  have himage (q : E × C(Icc 0 T, E)) (hq : q ∈ closedBall p 1) :
      MapsTo (langevinSolution V (intervalNoiseExtension hT q.2) q.1) (Icc 0 T)
        (closedBall 0 B) := by
    have hparts : ‖q.1 - p.1‖ ≤ 1 ∧ ‖q.2 - p.2‖ ≤ 1 := by
      rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hq
      constructor
      · simpa only [dist_eq_norm] using hq.1
      · simpa only [dist_eq_norm] using hq.2
    have hq₁ : ‖q.1‖ ≤ ‖p.1‖ + 1 := by
      have h := norm_le_norm_sub_add q.1 p.1
      linarith [hparts.1]
    have hq₂ : ‖q.2‖ ≤ ‖p.2‖ + 1 := by
      have h := norm_le_norm_sub_add q.2 p.2
      linarith [hparts.2]
    intro s hs
    simpa only [mem_closedBall, dist_zero_right] using hbound q.1 hq₁ q.2 hq₂ s hs
  let C := Real.exp ((K + 1) * T) * (1 + 2 * K) + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨⟨C, hC⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro q hq r hr
  have hestimate := langevinSolution_noise_difference_bound hV rate hrate hHess
    (intervalNoiseExtension_continuous hT q.2) (intervalNoiseExtension_continuous hT r.2)
    q.1 r.1 hT (norm_nonneg (q.2 - r.2)) hLip (himage q hq) (himage r hr)
    (fun s _ => intervalNoiseExtension_sub_norm_le hT q.2 r.2 s)
  have hqrd₁ : ‖q.1 - r.1‖ ≤ dist q r := by
    rw [Prod.dist_eq, ← dist_eq_norm]
    exact le_max_left _ _
  have hqrd₂ : ‖q.2 - r.2‖ ≤ dist q r := by
    rw [Prod.dist_eq, ← dist_eq_norm]
    exact le_max_right _ _
  rw [dist_eq_norm]
  change ‖intervalLangevinEvaluation V hT q - intervalLangevinEvaluation V hT r‖ ≤ C * dist q r
  calc
    _ ≤ Real.exp ((K + 1) * T) * (‖q.1 - r.1‖ + K * (2 * ‖q.2 - r.2‖)) +
        2 * ‖q.2 - r.2‖ := hestimate
    _ ≤ Real.exp ((K + 1) * T) * (dist q r + K * (2 * dist q r)) + 2 * dist q r := by
      gcongr
    _ = C * dist q r := by dsimp [C]; ring

/-- Joint continuity of actual solution evaluation in its initial point and
continuous driving path with the genuine compact-interval uniform topology. -/
theorem intervalLangevinEvaluation_continuous [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {T : ℝ} (hT : 0 ≤ T) : Continuous (intervalLangevinEvaluation V hT) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨L, hL⟩ := intervalLangevinEvaluation_locally_lipschitz hV rate hrate hHess hT p
  exact hL.continuousOn.continuousAt (closedBall_mem_nhds p (by norm_num))

/-- The actual evaluation map is Borel measurable; this is a proved consequence
of joint continuity, not an assumption on a selected solution. -/
theorem intervalLangevinEvaluation_borel_measurable [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {T : ℝ} (hT : 0 ≤ T) :
    @Measurable (E × C(Icc 0 T, E)) E (borel _) (borel _) (intervalLangevinEvaluation V hT) :=
  (intervalLangevinEvaluation_continuous hV rate hrate hHess hT).borel_measurable

/-- Two continuous noises agreeing through time T produce identical actual
solutions through T. This proves nonanticipativity from the integral equation
and pathwise uniqueness. -/
theorem langevinSolution_eqOn_of_noise_eqOn [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w v : ℝ → E} (hw : Continuous w) (hv : Continuous v) (x₀ : E)
    {T : ℝ} (hT : 0 ≤ T) (heq : EqOn w v (Icc 0 T)) :
    EqOn (langevinSolution V w x₀) (langevinSolution V v x₀) (Icc 0 T) := by
  have hX := langevinSolution_isLangevinPathOn hV rate hrate hHess hw x₀ hT
  have hXv : IsLangevinPathOn V v x₀ (langevinSolution V w x₀) T := by
    refine ⟨hX.1, ?_⟩
    intro t ht
    rw [← heq ht, ← heq ⟨le_rfl, hT⟩]
    exact hX.2 t ht
  exact langevin_path_unique hV rate hHess hXv
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hv x₀ hT)

/-- Restricting a continuous global noise to the interval, then extending it
constantly, preserves the actual solution evaluation at its final time. -/
theorem intervalLangevinEvaluation_restrict [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : E) (w : C(ℝ, E)) :
    intervalLangevinEvaluation V hT (x₀, w.restrict (Icc 0 T)) = langevinSolution V w x₀ T := by
  apply langevinSolution_eqOn_of_noise_eqOn hV rate hrate hHess
    (intervalNoiseExtension_continuous hT _) w.continuous x₀ hT ?_ ⟨hT, le_rfl⟩
  intro t ht
  exact IccExtend_of_mem hT _ ht

/-- Actual solution evaluation is jointly continuous also for global noise
paths with the compact-open topology. -/
theorem langevinSolution_evaluation_continuous [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 T) := by
  have h := (intervalLangevinEvaluation_continuous hV rate hrate hHess hT).comp
    (continuous_fst.prodMk ((ContinuousMap.continuous_restrict (Icc 0 T)).comp continuous_snd))
  have heq : (fun p : E × C(ℝ, E) => intervalLangevinEvaluation V hT
      (p.1, p.2.restrict (Icc 0 T))) = fun p => langevinSolution V p.2 p.1 T := by
    funext p
    exact intervalLangevinEvaluation_restrict hV rate hrate hHess hT p.1 p.2
  change Continuous (fun p : E × C(ℝ, E) => intervalLangevinEvaluation V hT
    (p.1, p.2.restrict (Icc 0 T))) at h
  rwa [heq] at h

end CutoffRigidity
