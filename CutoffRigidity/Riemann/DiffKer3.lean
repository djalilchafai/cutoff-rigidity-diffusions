module

public import CutoffRigidity.Riemann.DiffKer2

/-! # The Riesz density and the kernel `Kk` (KER, A6) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Dens

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- The evaluation functional `u ↦ (T_t u)(x)` (for `t ≠ 0`). -/
noncomputable def evalCLM (t : ℝ≥0) (x : M) : (M →₂[μ] ℝ) →L[ℝ] ℝ :=
  open Classical in
  if ht : t ≠ 0 then
    LinearMap.mkContinuous
      { toFun := fun u => Tc F hV hμ t u x
        map_add' := fun u v => by simp [Tc_add]
        map_smul' := fun c u => by simp [Tc_smul] }
      (Classical.choose (Tc_bound F hV hμ ht (isCompact_singleton (x := x))))
      (fun u => by
        have := Classical.choose_spec (Tc_bound F hV hμ ht (isCompact_singleton (x := x))) u x rfl
        simpa using this)
  else 0

theorem evalCLM_apply {t : ℝ≥0} (ht : t ≠ 0) (x : M) (u : M →₂[μ] ℝ) :
    evalCLM F hV hμ t x u = Tc F hV hμ t u x := by
  simp [evalCLM, ht]

/-- The Riesz density `p_t(x, ·) ∈ L²(μ)`. -/
noncomputable def pk (t : ℝ≥0) (x : M) : M →₂[μ] ℝ :=
  (InnerProductSpace.toDual ℝ (M →₂[μ] ℝ)).symm (evalCLM F hV hμ t x)

theorem inner_pk {t : ℝ≥0} (ht : t ≠ 0) (x : M) (u : M →₂[μ] ℝ) :
    inner ℝ (pk F hV hμ t x) u = Tc F hV hμ t u x := by
  rw [pk, InnerProductSpace.toDual_symm_apply, evalCLM_apply F hV hμ ht]

theorem pk_nonneg {t : ℝ≥0} (ht : t ≠ 0) (x : M) : 0 ≤ᵐ[μ] (pk F hV hμ t x : M → ℝ) := by
  set p := pk F hV hμ t x with hp
  have hmeas : Measurable (fun y => max (-(p y)) 0) :=
    ((Lp.stronglyMeasurable p).measurable.neg).max measurable_const
  have hm : MemLp (fun y => max (-(p y)) 0) 2 μ :=
    (Lp.memLp p).of_le hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rcases le_total (p y) 0 with h | h
      · rw [max_eq_left (by linarith), abs_neg]
      · rw [max_eq_right (by linarith), abs_zero]; exact abs_nonneg _)
  set φ := hm.toLp (fun y => max (-(p y)) 0) with hφ
  have hφae : (φ : M → ℝ) =ᵐ[μ] fun y => max (-(p y)) 0 := MemLp.coeFn_toLp hm
  have hφ0 : 0 ≤ᵐ[μ] φ := by
    filter_upwards [hφae] with y hy
    rw [hy]; exact le_max_right _ _
  have h1 := Tc_nonneg F hV hμ ht φ hφ0 x
  rw [← inner_pk F hV hμ ht x φ] at h1
  have h2 : inner ℝ p φ = -∫ y, (max (-(p y)) 0) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hφae] with y hy
    rw [hy]
    simp only [RCLike.inner_apply, conj_trivial]
    rcases le_total (p y) 0 with h | h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith)]; ring
  have h3 : ∫ y, (max (-(p y)) 0) ^ 2 ∂μ = 0 := by
    have := integral_nonneg (μ := μ) (f := fun y => (max (-(p y)) 0) ^ 2) (fun y => sq_nonneg _)
    linarith
  have h4 : (fun y => (max (-(p y)) 0) ^ 2) =ᵐ[μ] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) ?_).1 h3
    exact (hm.integrable_sq)
  filter_upwards [h4] with y hy
  have : max (-(p y)) 0 = 0 := by simpa using hy
  have := le_max_left (-(p y)) 0
  simp only [Pi.zero_apply]
  linarith

end Dens

end CutoffRigidity.Riemann.Diff
