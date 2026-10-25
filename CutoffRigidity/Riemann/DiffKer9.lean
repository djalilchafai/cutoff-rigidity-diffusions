module

public import CutoffRigidity.Riemann.DiffKer8

/-! # The pointwise Dynkin identity: `IsDiffusionSemigroup F V Kk` (KER, A6) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Dyn2

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem hasDerivAt_semi_time {r : ℝ} (hr : 0 < r) (f : testSub F M) (x : M) :
    HasDerivAt (fun q : ℝ => semi (Kk F hV hμ) q.toNNReal (f : M → ℝ) x)
      (semi (Kk F hV hμ) r.toNNReal (testGen F hV f : M → ℝ) x) r := by
  have hr' : r.toNNReal ≠ 0 := by
    intro h0; rw [Real.toNNReal_eq_zero] at h0; exact absurd hr (not_lt.2 h0)
  rw [semi_Kk_eq_Tc F hV hμ hr']
  refine (hasDerivAt_Tc F hV hμ hr f x).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hr] with q hq
  have hq' : q.toNNReal ≠ 0 := by
    intro h0; rw [Real.toNNReal_eq_zero] at h0; exact absurd hq (not_lt.2 h0)
  exact semi_Kk_eq_Tc F hV hμ hq' f x

theorem continuous_semi_time (f : testSub F M) (x : M) :
    Continuous (fun q : ℝ => semi (Kk F hV hμ) q.toNNReal (f : M → ℝ) x) := by
  rw [continuous_iff_continuousAt]
  intro r
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have : (fun q : ℝ => semi (Kk F hV hμ) q.toNNReal (f : M → ℝ) x) =ᶠ[𝓝 r]
        fun _ => (f : M → ℝ) x := by
      filter_upwards [Iio_mem_nhds hr] with q hq
      rw [Real.toNNReal_of_nonpos (le_of_lt hq), semi_Kk_zero]
    exact continuousAt_const.congr this.symm
  · subst hr
    obtain ⟨B, hB0, hB⟩ := exists_abs_mgenerator_le F hV f.2.1 f.2.2
    have key : ∀ q : ℝ, |semi (Kk F hV hμ) q.toNNReal (f : M → ℝ) x - (f : M → ℝ) x| ≤ B * |q| := by
      intro q
      rcases le_or_gt q 0 with hq | hq
      · rw [Real.toNNReal_of_nonpos hq, semi_Kk_zero]; simp; positivity
      · have hq' : q.toNNReal ≠ 0 := by
          intro h0; rw [Real.toNNReal_eq_zero] at h0; exact absurd hq (not_lt.2 h0)
        rw [semi_Kk_eq_Tc F hV hμ hq']
        have := abs_Tc_sub_le F hV hμ hq' f hB x
        rw [Real.coe_toNNReal _ hq.le] at this
        rwa [abs_of_pos hq]
    rw [ContinuousAt, Real.toNNReal_zero, semi_Kk_zero]
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun q => dist_nonneg) (fun q => by simpa [Real.dist_eq] using key q) ?_
    have : Tendsto (fun q : ℝ => B * |q|) (𝓝 0) (𝓝 (B * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using this
  · exact (hasDerivAt_semi_time F hV hμ hr f x).continuousAt

/-- **Pointwise Dynkin identity** for `Kk`. -/
theorem dynkin_Kk (f : testSub F M) (x : M) (t : ℝ≥0) :
    ∫ y, (f : M → ℝ) y ∂Kk F hV hμ t x = (f : M → ℝ) x +
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, mgenerator F V (f : M → ℝ) y ∂Kk F hV hμ s.toNNReal x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0:ℝ)) (b := (t : ℝ))
    (f := fun q : ℝ => semi (Kk F hV hμ) q.toNNReal (f : M → ℝ) x)
    (f' := fun q : ℝ => semi (Kk F hV hμ) q.toNNReal (testGen F hV f : M → ℝ) x) t.2
    (continuous_semi_time F hV hμ f x).continuousOn
    (fun q hq => hasDerivAt_semi_time F hV hμ hq.1 f x)
    ((continuous_semi_time F hV hμ (testGen F hV f) x).intervalIntegrable _ _)
  simp only [Real.toNNReal_coe, Real.toNNReal_zero, semi_Kk_zero] at h
  have e : ∀ q : ℝ, semi (Kk F hV hμ) q.toNNReal (testGen F hV f : M → ℝ) x =
      ∫ y, mgenerator F V (f : M → ℝ) y ∂Kk F hV hμ q.toNNReal x := fun q => rfl
  simp only [e] at h
  have e2 : semi (Kk F hV hμ) t (f : M → ℝ) x = ∫ y, (f : M → ℝ) y ∂Kk F hV hμ t x := rfl
  rw [e2] at h
  linarith

theorem isDiffusionSemigroup_Kk : IsDiffusionSemigroup F V (Kk F hV hμ) :=
  ⟨Kk_markov F hV hμ, Kk_comp F hV hμ, fun f hf hc x t =>
    dynkin_Kk F hV hμ ⟨f, hf, hc⟩ x t⟩

end Dyn2

end CutoffRigidity.Riemann.Diff
