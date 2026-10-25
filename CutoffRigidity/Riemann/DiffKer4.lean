module

public import CutoffRigidity.Riemann.DiffKer3

/-! # The measures `Kk t x` (KER, A6) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section KMeas

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- `p_t(x,·) μ` (for `t ≠ 0`). -/
noncomputable def kmeas (t : ℝ≥0) (x : M) : Measure M :=
  μ.withDensity fun y => ENNReal.ofReal (pk F hV hμ t x y)

/-- Indicator of `A` in `L²(μ)`. -/
noncomputable def indL (μ : Measure M) [IsFiniteMeasure μ] {A : Set M} (hA : MeasurableSet A) :
    M →₂[μ] ℝ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)

theorem kmeas_apply {t : ℝ≥0} (ht : t ≠ 0) (x : M) {A : Set M} (hA : MeasurableSet A) :
    kmeas F hV hμ t x A = ENNReal.ofReal (Tc F hV hμ t (indL μ hA) x) := by
  unfold kmeas
  rw [withDensity_apply _ hA]
  have hint : Integrable (pk F hV hμ t x : M → ℝ) (μ.restrict A) :=
    ((Lp.memLp _).integrable one_le_two).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_ae (pk_nonneg F hV hμ ht x))]
  congr 1
  rw [← inner_pk F hV hμ ht x, real_inner_comm, indL, L2.inner_indicatorConstLp_one]

theorem kmeas_nonneg_density {t : ℝ≥0} (ht : t ≠ 0) (x : M) :
    ∀ᵐ y ∂μ, ((pk F hV hμ t x : M → ℝ) y).toNNReal = (pk F hV hμ t x : M → ℝ) y := by
  filter_upwards [pk_nonneg F hV hμ ht x] with y hy
  simp [Real.coe_toNNReal _ hy]

/-- Integration against `Kk t x` of an `L²` function. -/
theorem kmeas_integral {t : ℝ≥0} (ht : t ≠ 0) (x : M) (h : M →₂[μ] ℝ) :
    Integrable (h : M → ℝ) (kmeas F hV hμ t x) ∧
      ∫ y, h y ∂kmeas F hV hμ t x = Tc F hV hμ t h x := by
  set p := pk F hV hμ t x with hp
  have hpm : Measurable (fun y => (p y).toNNReal) :=
    (Lp.stronglyMeasurable p).measurable.real_toNNReal
  have e : kmeas F hV hμ t x = μ.withDensity (fun y => (((p y).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  have hprod : Integrable (fun y => (p y) * h y) μ :=
    (Lp.memLp p).integrable_mul (Lp.memLp h)
  have hae : (fun y => (((p y).toNNReal : ℝ≥0)) • (h y)) =ᵐ[μ] fun y => p y * h y := by
    filter_upwards [kmeas_nonneg_density F hV hμ ht x] with y hy
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [hy]
  refine ⟨?_, ?_⟩
  · rw [e, integrable_withDensity_iff_integrable_smul hpm]
    exact hprod.congr hae.symm
  · rw [e, integral_withDensity_eq_integral_smul hpm]
    rw [integral_congr_ae hae, ← inner_pk F hV hμ ht x h, MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [RCLike.inner_apply, conj_trivial]
    ring

end KMeas

end CutoffRigidity.Riemann.Diff
