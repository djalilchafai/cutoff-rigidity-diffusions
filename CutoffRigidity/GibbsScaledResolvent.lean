module
public import CutoffRigidity.GibbsResolventOrder
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! # Genuine scaled variational Gibbs resolvents

For every positive step h, Lax–Milgram constructs the weak solution of
(I+hA)u=f on the actual closed weighted gradient form. No invertibility
premise or stochastic invariance is used.
-/
public section
set_option maxHeartbeats 900000
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def gibbsScaledForm
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) :
    gibbsSobolevGraph hV hprob →L[ℝ] gibbsSobolevGraph hV hprob →L[ℝ] ℝ :=
  (innerSL ℝ).comp
    ((gibbsSobolevInclusion hV hprob).adjoint.comp (gibbsSobolevInclusion hV hprob) +
      h • (gibbsSobolevDerivative hV hprob).adjoint.comp (gibbsSobolevDerivative hV hprob))

theorem gibbsScaledForm_apply
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ)
    (u v : gibbsSobolevGraph hV hprob) :
    gibbsScaledForm hV hprob h u v =
      inner ℝ (gibbsSobolevInclusion hV hprob u) (gibbsSobolevInclusion hV hprob v) +
        h * gibbsDirichletEnergy hV hprob u v := by
  change inner ℝ
    (((gibbsSobolevInclusion hV hprob).adjoint (gibbsSobolevInclusion hV hprob u)) +
      h • (gibbsSobolevDerivative hV hprob).adjoint (gibbsSobolevDerivative hV hprob u)) v = _
  exact (inner_add_left _ _ _).trans (congrArg₂ (· + ·)
    (ContinuousLinearMap.adjoint_inner_left (gibbsSobolevInclusion hV hprob) v
      (gibbsSobolevInclusion hV hprob u))
    ((real_inner_smul_left _ v h).trans (congrArg (h * ·)
      (ContinuousLinearMap.adjoint_inner_left (gibbsSobolevDerivative hV hprob) v
        (gibbsSobolevDerivative hV hprob u)))))

theorem gibbsScaledForm_isCoercive
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) {h : ℝ} (hh : 0 < h) :
    IsCoercive (gibbsScaledForm hV hprob h) := by
  refine ⟨min 1 h, lt_min zero_lt_one hh, ?_⟩
  intro u
  rw [gibbsScaledForm_apply]
  rw [real_inner_self_eq_norm_sq]
  have hnorm := gibbsSobolev_norm_sq hV hprob u
  have he := gibbsDirichletEnergy_nonneg hV hprob u
  have h1 : min 1 h ≤ 1 := min_le_left _ _
  have hh' : min 1 h ≤ h := min_le_right _ _
  nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖gibbsSobolevInclusion hV hprob u‖),
    mul_le_mul_of_nonneg_right hh' he]

@[expose] noncomputable def gibbsScaledWeakResolvent
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h) :
    (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] gibbsSobolevGraph hV hprob :=
  (gibbsScaledForm_isCoercive hV hprob hh).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (gibbsSobolevInclusion hV hprob).adjoint

theorem gibbsScaledWeakResolvent_equation
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f : E →₂[gibbsMeasure volume V] ℝ) (v : gibbsSobolevGraph hV hprob) :
    inner ℝ (gibbsSobolevInclusion hV hprob (gibbsScaledWeakResolvent hV hprob h hh f))
      (gibbsSobolevInclusion hV hprob v) +
      h * gibbsDirichletEnergy hV hprob (gibbsScaledWeakResolvent hV hprob h hh f) v =
      inner ℝ f (gibbsSobolevInclusion hV hprob v) := by
  rw [← gibbsScaledForm_apply]
  rw [← IsCoercive.continuousLinearEquivOfBilin_apply (gibbsScaledForm_isCoercive hV hprob hh)]
  change inner ℝ
    ((gibbsScaledForm_isCoercive hV hprob hh).continuousLinearEquivOfBilin
      ((gibbsScaledForm_isCoercive hV hprob hh).continuousLinearEquivOfBilin.symm
        ((gibbsSobolevInclusion hV hprob).adjoint f))) v = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

@[expose] noncomputable def gibbsScaledL2Resolvent
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h) :
    (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ) :=
  (gibbsSobolevInclusion hV hprob).comp (gibbsScaledWeakResolvent hV hprob h hh)

theorem gibbsScaledWeakResolvent_unique
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f : E →₂[gibbsMeasure volume V] ℝ) (u : gibbsSobolevGraph hV hprob)
    (hu : ∀ v : gibbsSobolevGraph hV hprob,
      inner ℝ (gibbsSobolevInclusion hV hprob u) (gibbsSobolevInclusion hV hprob v) +
        h * gibbsDirichletEnergy hV hprob u v = inner ℝ f (gibbsSobolevInclusion hV hprob v)) :
    u = gibbsScaledWeakResolvent hV hprob h hh f := by
  apply (gibbsScaledForm_isCoercive hV hprob hh).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  exact ((IsCoercive.continuousLinearEquivOfBilin_apply _ u v).trans
    ((gibbsScaledForm_apply hV hprob h u v).trans (hu v))).trans
    (((IsCoercive.continuousLinearEquivOfBilin_apply _ _ v).trans
      ((gibbsScaledForm_apply hV hprob h _ v).trans
        (gibbsScaledWeakResolvent_equation hV hprob h hh f v))).symm)

/-- Actual operator-domain membership and the scaled resolvent equation. -/
theorem gibbsScaledL2Resolvent_graph
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f : E →₂[gibbsMeasure volume V] ℝ) :
    (gibbsScaledL2Resolvent hV hprob h hh f,
      h⁻¹ • (f - gibbsScaledL2Resolvent hV hprob h hh f)) ∈
      (gibbsPositiveGenerator hV hprob).graph := by
  apply gibbsPositiveGenerator_of_weak_equation hV hprob
    (gibbsScaledWeakResolvent hV hprob h hh f)
  intro v
  rw [real_inner_smul_left, inner_sub_left]
  have he := gibbsScaledWeakResolvent_equation hV hprob h hh f v
  change _ = h⁻¹ * (inner ℝ f (gibbsSobolevInclusion hV hprob v) -
    inner ℝ (gibbsSobolevInclusion hV hprob (gibbsScaledWeakResolvent hV hprob h hh f))
      (gibbsSobolevInclusion hV hprob v))
  rw [← he]
  field_simp
  ring

theorem norm_gibbsScaledL2Resolvent_apply_le
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f : E →₂[gibbsMeasure volume V] ℝ) :
    ‖gibbsScaledL2Resolvent hV hprob h hh f‖ ≤ ‖f‖ := by
  let u := gibbsScaledWeakResolvent hV hprob h hh f
  have he := gibbsScaledWeakResolvent_equation hV hprob h hh f u
  rw [real_inner_self_eq_norm_sq] at he
  change ‖gibbsSobolevInclusion hV hprob u‖ ^ 2 + h * gibbsDirichletEnergy hV hprob u u =
    inner ℝ f (gibbsSobolevInclusion hV hprob u) at he
  have hnon := mul_nonneg hh.le (gibbsDirichletEnergy_nonneg hV hprob u)
  have hcs := real_inner_le_norm f (gibbsSobolevInclusion hV hprob u)
  change ‖gibbsSobolevInclusion hV hprob u‖ ≤ ‖f‖
  by_cases hz : ‖gibbsSobolevInclusion hV hprob u‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hpos : 0 < ‖gibbsSobolevInclusion hV hprob u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith only [he, hnon, hcs, hpos]

theorem gibbsScaledL2Resolvent_symmetric
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f g : E →₂[gibbsMeasure volume V] ℝ) :
    inner ℝ (gibbsScaledL2Resolvent hV hprob h hh f) g =
      inner ℝ f (gibbsScaledL2Resolvent hV hprob h hh g) := by
  have hf := gibbsScaledWeakResolvent_equation hV hprob h hh f (gibbsScaledWeakResolvent hV hprob h hh g)
  have hg := gibbsScaledWeakResolvent_equation hV hprob h hh g (gibbsScaledWeakResolvent hV hprob h hh f)
  have hc := real_inner_comm
    (gibbsSobolevInclusion hV hprob (gibbsScaledWeakResolvent hV hprob h hh g))
    (gibbsSobolevInclusion hV hprob (gibbsScaledWeakResolvent hV hprob h hh f))
  rw [gibbsDirichletEnergy_symmetric, ← hc] at hg
  exact (real_inner_comm g _).trans (hg.symm.trans hf)

/-- Constants are fixed by every actual scaled resolvent. -/
theorem gibbsScaledL2Resolvent_constant {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h) (c : ℝ) :
    gibbsScaledL2Resolvent hV hprob h hh (gibbsConstantLp hprob c) = gibbsConstantLp hprob c := by
  have := hprob
  have hf : MemLp (fun _ : E => c) 2 (gibbsMeasure volume V) := memLp_const c
  have hg : MemLp (gradient (fun _ : E => c)) 2 (gibbsMeasure volume V) := by
    rw [gradient_fun_const']
    exact memLp_const (0 : E)
  let u := c2GibbsSobolevLift hV hprob contDiff_const hf hg
  have hd : gibbsSobolevDerivative hV hprob u = 0 := by
    apply Lp.ext
    filter_upwards [hg.coeFn_toLp, Lp.coeFn_zero E 2 (gibbsMeasure volume V)] with x hx hz
    change hg.toLp (gradient (fun _ : E => c)) x = (0 : E →₂[gibbsMeasure volume V] E) x
    rw [hx, hz, gradient_fun_const]
    rfl
  have hu : ∀ v : gibbsSobolevGraph hV hprob,
      inner ℝ (gibbsSobolevInclusion hV hprob u) (gibbsSobolevInclusion hV hprob v) +
        h * gibbsDirichletEnergy hV hprob u v =
      inner ℝ (gibbsConstantLp hprob c) (gibbsSobolevInclusion hV hprob v) := by
    intro v
    change inner ℝ (gibbsConstantLp hprob c) (gibbsSobolevInclusion hV hprob v) +
      h * inner ℝ (gibbsSobolevDerivative hV hprob u) (gibbsSobolevDerivative hV hprob v) = _
    rw [hd, inner_zero_left, mul_zero, add_zero]
  have hueq := gibbsScaledWeakResolvent_unique hV hprob h hh (gibbsConstantLp hprob c) u hu
  change gibbsSobolevInclusion hV hprob (gibbsScaledWeakResolvent hV hprob h hh (gibbsConstantLp hprob c)) = _
  rw [← hueq]
  rfl

/-- Every actual operator graph vector has its genuine H¹ weak-form lift. -/
theorem gibbsPositiveGenerator_graph_form
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hg : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    ∃ w : gibbsSobolevGraph hV hprob,
      gibbsSobolevInclusion hV hprob w = u ∧
      ∀ v : gibbsSobolevGraph hV hprob,
        gibbsDirichletEnergy hV hprob w v = inner ℝ g (gibbsSobolevInclusion hV hprob v) := by
  change (u, g) ∈ (positiveResolventOperator (gibbsL2Resolvent hV hprob)).graph at hg
  rw [positiveResolventOperator_graph _ (gibbsL2Resolvent_injective hV hprob),
    mem_positiveResolventGraph] at hg
  obtain ⟨q, hq, hg⟩ := hg
  let w := gibbsWeakResolvent hV hprob q
  have hw : gibbsSobolevInclusion hV hprob w = u := hq
  refine ⟨w, hw, ?_⟩
  intro v
  have he := gibbsWeakResolvent_equation hV hprob q v
  have hrep : g = q - gibbsSobolevInclusion hV hprob w := hg.symm
  rw [hrep, inner_sub_left]
  change inner ℝ (gibbsSobolevInclusion hV hprob w) (gibbsSobolevInclusion hV hprob v) +
    gibbsDirichletEnergy hV hprob w v = inner ℝ q (gibbsSobolevInclusion hV hprob v) at he
  linarith

/-- The scaled variational construction is the actual inverse of I+hA
on the whole actual operator domain. -/
theorem gibbsScaledL2Resolvent_of_graph
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hg : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    gibbsScaledL2Resolvent hV hprob h hh (u + h • g) = u := by
  obtain ⟨w, hw, he⟩ := gibbsPositiveGenerator_graph_form hV hprob u g hg
  have hsolve : w = gibbsScaledWeakResolvent hV hprob h hh (u + h • g) := by
    apply gibbsScaledWeakResolvent_unique hV hprob h hh
    intro v
    rw [hw, he v, inner_add_left, real_inner_smul_left]
  exact (congrArg (gibbsSobolevInclusion hV hprob) hsolve.symm).trans hw

/-- The construction agrees with the original resolvent at step one. -/
theorem gibbsScaledL2Resolvent_one
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    gibbsScaledL2Resolvent hV hprob 1 zero_lt_one = gibbsL2Resolvent hV hprob := by
  apply ContinuousLinearMap.ext
  intro f
  have heq : gibbsWeakResolvent hV hprob f =
      gibbsScaledWeakResolvent hV hprob 1 zero_lt_one f := by
    apply gibbsScaledWeakResolvent_unique
    intro v
    simpa only [one_mul] using gibbsWeakResolvent_equation hV hprob f v
  exact congrArg (gibbsSobolevInclusion hV hprob) heq.symm

end CutoffRigidity
