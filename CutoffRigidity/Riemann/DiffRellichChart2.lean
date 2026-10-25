module

public import CutoffRigidity.Riemann.DiffRellichChart1

/-! # `L²` and gradient comparison between `M` and a chart (workstream HPOS) -/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Cmp

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M) {K₀ : Set M}

include hV in
/-- Two-sided bounds of the weights on a compact subset of the chart target. -/
theorem exists_chart_bounds {K : Set F} (hK : IsCompact K) (hKT : K ⊆ (chartAt F x₀).target) :
    ∃ ρmin ρmax κmin : ℝ, 0 < ρmin ∧ 0 < ρmax ∧ 0 < κmin ∧ ∀ z ∈ K,
      ρmin ≤ chartRho F V x₀ z ∧ chartRho F V x₀ z ≤ ρmax ∧ κmin ≤ chartKappa F V x₀ z := by
  have hρ : ContinuousOn (chartRho F V x₀) K := fun z hz =>
    ((contDiffAt_chartRho F hV x₀ (by rw [CutoffRigidity.extChartAt_target_eq]; exact hKT hz)).continuousAt).continuousWithinAt
  have hκ : ContinuousOn (chartKappa F V x₀) K :=
    (continuousOn_chartKappa F hV x₀).mono hKT
  obtain ⟨a, ha, hmin⟩ := hK.exists_forall_le' hρ (a := 0) (fun z hz => chartRho_pos F V x₀ (hKT hz))
  obtain ⟨b, hb, hbmin⟩ := hK.exists_forall_le' hκ (a := 0) (fun z hz => chartKappa_pos F V x₀ (hKT hz))
  obtain ⟨c, hc⟩ := (hK.image_of_continuousOn hρ).bddAbove
  refine ⟨a, max c 1, b, ha, lt_max_of_lt_right one_pos, hb, fun z hz => ⟨hmin z hz, ?_, hbmin z hz⟩⟩
  exact (hc ⟨z, hz, rfl⟩).trans (le_max_left _ _)

variable {x₀}

/-- Pointwise comparison of `ρ g̃²` and `g̃²` on the target. -/
theorem chartRho_mul_sq_bounds {g : M → ℝ} (hs : tsupport g ⊆ K₀) {ρmin ρmax : ℝ}
    (hb : ∀ z ∈ (chartAt F x₀) '' K₀, ρmin ≤ chartRho F V x₀ z ∧ chartRho F V x₀ z ≤ ρmax) (z : F) :
    ρmin * chartRestr F x₀ g z ^ 2 ≤ chartRho F V x₀ z * chartRestr F x₀ g z ^ 2 ∧
    chartRho F V x₀ z * chartRestr F x₀ g z ^ 2 ≤ ρmax * chartRestr F x₀ g z ^ 2 := by
  by_cases hz : z ∈ (chartAt F x₀) '' K₀
  · exact ⟨mul_le_mul_of_nonneg_right (hb z hz).1 (sq_nonneg _),
      mul_le_mul_of_nonneg_right (hb z hz).2 (sq_nonneg _)⟩
  · have : chartRestr F x₀ g z = 0 := chartRestr_eq_zero' F hs hz
    simp [this]

include hV hμ in
/-- The `μ`-integral of `g²` in the chart. -/
theorem integral_sq_eq_chart {g : M → ℝ} (hg : Continuous g) (hs : tsupport g ⊆ K₀) (hsrc : K₀ ⊆ (chartAt F x₀).source) :
    ∫ x, g x ^ 2 ∂μ = ∫ z in (chartAt F x₀).target, chartRho F V x₀ z * chartRestr F x₀ g z ^ 2 := by
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hcont : ContinuousOn (fun z => chartRestr F x₀ g z ^ 2) (chartAt F x₀).target := by
    refine ((hg.comp_continuousOn (chartAt F x₀).continuousOn_symm).pow 2).congr fun z hz => ?_
    simp [chartRestr_of_mem F x₀ hz]
  have h1 := integral_chart_comp F hV hμ x₀ (fun z => chartRestr F x₀ g z ^ 2)
    (hcont.aestronglyMeasurable hTm)
  rw [← h1]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (chartAt F x₀).source)]
  · refine setIntegral_congr_fun (chartAt F x₀).open_source.measurableSet fun x hx => ?_
    rw [chartRestr_of_mem F x₀ ((chartAt F x₀).map_source hx), (chartAt F x₀).left_inv hx]
  · intro x hx
    have : g x = 0 := by
      by_contra h
      exact hx (hsrc (hs (subset_tsupport _ h)))
    simp [this]

include hV hμ in
/-- Two-sided comparison of `∫ g̃²` and `∫ g² dμ`. -/
theorem chart_sq_bounds {g : M → ℝ} (hg : MSmooth F g)
    (hs : tsupport g ⊆ K₀) (hK₀ : IsCompact K₀) (hsrc : K₀ ⊆ (chartAt F x₀).source)
    {ρmin ρmax : ℝ}
    (hb : ∀ z ∈ (chartAt F x₀) '' K₀, ρmin ≤ chartRho F V x₀ z ∧ chartRho F V x₀ z ≤ ρmax) :
    ρmin * ∫ z, chartRestr F x₀ g z ^ 2 ≤ ∫ x, g x ^ 2 ∂μ ∧
      ∫ x, g x ^ 2 ∂μ ≤ ρmax * ∫ z, chartRestr F x₀ g z ^ 2 := by
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hcd := contDiff_chartRestr F hg hs hK₀ hsrc
  have hcs := hasCompactSupport_chartRestr F hs hK₀ hsrc
  have hGc : Continuous (fun z => chartRestr F x₀ g z ^ 2) := hcd.continuous.pow 2
  have hGi : Integrable (fun z => chartRestr F x₀ g z ^ 2) := by
    refine hGc.integrable_of_hasCompactSupport ?_
    have := hcs.mul_left (f := chartRestr F x₀ g)
    simp only [pow_two]
    exact this
  have hG0 : ∀ z, z ∉ (chartAt F x₀).target → chartRestr F x₀ g z ^ 2 = 0 := fun z hz => by
    simp [chartRestr_of_notMem F x₀ hz]
  have hTint : ∫ z in (chartAt F x₀).target, chartRestr F x₀ g z ^ 2 =
      ∫ z, chartRestr F x₀ g z ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hG0
  have hρc : ContinuousOn (chartRho F V x₀) (chartAt F x₀).target := fun z hz =>
    ((contDiffAt_chartRho F hV x₀ (by rw [CutoffRigidity.extChartAt_target_eq]; exact hz)).continuousAt).continuousWithinAt
  have hρGi : IntegrableOn (fun z => chartRho F V x₀ z * chartRestr F x₀ g z ^ 2)
      (chartAt F x₀).target := by
    refine Integrable.mono' (g := fun z => ρmax * chartRestr F x₀ g z ^ 2)
      (hGi.restrict.const_mul ρmax) ((hρc.mul hGc.continuousOn).aestronglyMeasurable hTm) ?_
    refine ae_restrict_of_forall_mem hTm fun z hz => ?_
    have := (chartRho_mul_sq_bounds F hs hb z).2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (chartRho_pos F V x₀ hz).le (sq_nonneg _))]
    exact this
  rw [integral_sq_eq_chart F hV hμ hg.continuous hs hsrc, ← hTint]
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hGi.restrict.const_mul ρmin) hρGi
      fun z => (chartRho_mul_sq_bounds F hs hb z).1
  · rw [← integral_const_mul]
    exact integral_mono hρGi (hGi.restrict.const_mul ρmax)
      fun z => (chartRho_mul_sq_bounds F hs hb z).2

include hV hμ in
/-- Control of `∫ ‖∇g̃‖² dz` by the energy of `g`. -/
theorem chart_grad_bound (a : testSub F M) (hs : tsupport (a : M → ℝ) ⊆ K₀) (hK₀ : IsCompact K₀)
    (hsrc : K₀ ⊆ (chartAt F x₀).source) {κmin : ℝ} (hκ0 : 0 < κmin)
    (hb : ∀ z ∈ (chartAt F x₀) '' K₀, κmin ≤ chartKappa F V x₀ z) :
    ∫ z, ‖gradient (chartRestr F x₀ (a : M → ℝ)) z‖ ^ 2 ≤
      κmin⁻¹ * ∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ := by
  set X : F → ℝ := fun z => ‖gradient (chartRestr F x₀ (a : M → ℝ)) z‖ ^ 2 with hX
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hcd := contDiff_chartRestr F a.2.1 hs hK₀ hsrc
  have hXc : Continuous X := by
    have h1 : Continuous (fderiv ℝ (chartRestr F x₀ (a : M → ℝ))) :=
      hcd.continuous_fderiv (by simp)
    have h2 : Continuous (gradient (chartRestr F x₀ (a : M → ℝ))) :=
      (InnerProductSpace.toDual ℝ F).symm.continuous.comp h1
    exact h2.norm.pow 2
  have hX0 : ∀ z, z ∉ (chartAt F x₀) '' K₀ → X z = 0 := fun z hz => by
    simp [hX, gradient_chartRestr_eq_zero F hs hK₀ hsrc hz]
  have hXT : ∀ z, z ∈ (chartAt F x₀).target ∨ X z = 0 := fun z => by
    by_cases hz : z ∈ (chartAt F x₀).target
    · exact Or.inl hz
    · refine Or.inr (hX0 z fun h => hz ?_)
      obtain ⟨y, hy, rfl⟩ := h
      exact (chartAt F x₀).map_source (hsrc hy)
  have hE0 : 0 ≤ ∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ :=
    integral_nonneg fun x => carre_nonneg F _ x
  have hint : ∫ z, X z = (∫⁻ z, ENNReal.ofReal (X z)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by positivity)
      hXc.aestronglyMeasurable
  have hsupp : ∫⁻ z in (chartAt F x₀).target, ENNReal.ofReal (X z) =
      ∫⁻ z, ENNReal.ofReal (X z) := by
    refine setLIntegral_eq_of_support_subset ?_
    intro z hz
    rcases hXT z with h | h
    · exact h
    · exact absurd (by simp [h]) hz
  have hν := chartGrad_lintegral_le F hV hμ x₀ a
  have hν' : ∫⁻ z, ‖chartGrad F x₀ (a : M → ℝ) z‖ₑ ^ 2 ∂(chartNu F V x₀) =
      ∫⁻ z in (chartAt F x₀).target, ENNReal.ofReal (chartKappa F V x₀ z) *
        ENNReal.ofReal (X z) := by
    have hgm : AEMeasurable (fun z => ‖chartGrad F x₀ (a : M → ℝ) z‖ₑ ^ 2)
        (volume.restrict (chartAt F x₀).target) :=
      (((continuousOn_chartGrad F x₀ a.2.1).aestronglyMeasurable hTm).enorm).pow_const 2
    unfold chartNu
    rw [lintegral_withDensity_eq_lintegral_mul₀ (aemeasurable_chartKappa F hV x₀) hgm]
    refine setLIntegral_congr_fun hTm fun z hz => ?_
    have : ‖chartGrad F x₀ (a : M → ℝ) z‖ₑ ^ 2 = ENNReal.ofReal (X z) := by
      rw [hX]
      simp only
      rw [gradient_chartRestr_of_mem F hz, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp [this]
  have hlow : ENNReal.ofReal κmin * ∫⁻ z in (chartAt F x₀).target, ENNReal.ofReal (X z) ≤
      ∫⁻ z in (chartAt F x₀).target, ENNReal.ofReal (chartKappa F V x₀ z) *
        ENNReal.ofReal (X z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ (chartAt F x₀) '' K₀
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hb z hz)) _
    · simp [hX0 z hz]
  have hL : ∫⁻ z, ENNReal.ofReal (X z) ≤
      ENNReal.ofReal κmin⁻¹ * ENNReal.ofReal (∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ) := by
    rw [← hsupp]
    calc ∫⁻ z in (chartAt F x₀).target, ENNReal.ofReal (X z)
        = ENNReal.ofReal κmin⁻¹ * (ENNReal.ofReal κmin *
            ∫⁻ z in (chartAt F x₀).target, ENNReal.ofReal (X z)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hκ0.le), inv_mul_cancel₀ hκ0.ne']
          simp
      _ ≤ _ := by
          gcongr
          exact hlow.trans (hν' ▸ hν)
  rw [hint]
  have hfin : ENNReal.ofReal κmin⁻¹ * ENNReal.ofReal (∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ)
      ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc (∫⁻ z, ENNReal.ofReal (X z)).toReal
      ≤ (ENNReal.ofReal κmin⁻¹ * ENNReal.ofReal (∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ)).toReal :=
        ENNReal.toReal_mono hfin hL
    _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hκ0.le), ENNReal.toReal_ofReal (by positivity)]

end Cmp

end CutoffRigidity.Riemann.Diff
