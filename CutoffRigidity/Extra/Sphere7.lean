module

public import CutoffRigidity.Riemann.MeasureChart
public import CutoffRigidity.Riemann.WeightedIBPDensity

/-! # Sphere, stage 7: constructing weighted volume measures from one chart

General (any manifold with the standing instances).  If `μ` has density `e^{-V} ρ_Ξ` in one chart `Ξ`
whose source misses a set that is Lebesgue-negligible in every chart, then `IsWeightedVolume F μ V`.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Transfer of the chart density formula between two charts (generalization of `CutCur.local_chart_mass`
where the base chart `φ` is arbitrary and the hypothesis is the density formula for subsets of `U`). -/
theorem chart_mass_transfer {V : M → ℝ} {μ : Measure M} (φ Ξ : OpenPartialHomeomorph M F)
    (hφ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 φ.symm φ.target)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ Ξ.source)
    (hΞ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target)
    {U : Set M} (hUφ : U ⊆ φ.source) (hUS : U ⊆ Ξ.source)
    (hbase : ∀ C ⊆ U, MeasurableSet C → μ C = ∫⁻ z in φ '' C,
      ENNReal.ofReal (Real.exp (-V (φ.symm z)) * chartDensity φ z))
    {C : Set M} (hCU : C ⊆ U) (hCm : MeasurableSet C) :
    μ C = ∫⁻ w in Ξ '' C, ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w) := by
  have hCφ : C ⊆ φ.source := hCU.trans hUφ
  have hφCm : MeasurableSet (φ '' C) := by
    rw [φ.image_eq_target_inter_inv_preimage hCφ]
    exact measurableSet_inter_preimage_of_continuousOn φ.open_target.measurableSet
      φ.continuousOn_symm hCm
  have hφCt : φ '' C ⊆ φ.target := fun z ⟨x, hx, hxz⟩ => hxz ▸ φ.map_source (hCφ hx)
  have h1 := hbase C hCU hCm
  set T : F → F := fun z => Ξ (φ.symm z) with hT
  have hpt : ∀ z ∈ φ '' C, φ.symm z ∈ C := by
    rintro z ⟨x, hx, rfl⟩
    rwa [φ.left_inv (hCφ hx)]
  have h2 : ∀ z ∈ φ '' C, ENNReal.ofReal (Real.exp (-V (φ.symm z)) * chartDensity φ z) =
      ENNReal.ofReal |(fderiv ℝ T z).det| *
        ENNReal.ofReal (Real.exp (-V (Ξ.symm (T z))) * chartDensity Ξ (T z)) := by
    intro z hz
    have hx := hpt z hz
    have hxS : φ.symm z ∈ Ξ.source := hUS (hCU hx)
    have hsy : Ξ.symm (T z) = φ.symm z := Ξ.left_inv hxS
    rw [← ENNReal.ofReal_mul (abs_nonneg _), hsy,
      chartDensity_transition φ Ξ hφ' hΞ hΞ' (hφCt hz) hxS]
    congr 1
    ring
  have hInj : InjOn T (φ '' C) := by
    intro z hz z' hz' h
    have h1 := hpt z hz
    have h2 := hpt z' hz'
    have : φ.symm z = φ.symm z' := Ξ.injOn (hUS (hCU h1)) (hUS (hCU h2)) h
    exact φ.symm.injOn (hφCt hz) (hφCt hz') this
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hφCm
    (f := T) (f' := fun z => fderiv ℝ T z) (fun z hz =>
      (differentiableAt_transition φ Ξ hφ' hΞ (hφCt hz)
        (hUS (hCU (hpt z hz)))).hasFDerivAt.hasFDerivWithinAt) hInj
    (fun w => ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w))
  have h4 : T '' (φ '' C) = Ξ '' C := by
    rw [← image_comp]
    have h5 : (T ∘ φ) '' C = Ξ '' C := by
      refine image_congr fun x hx => ?_
      simp only [Function.comp, hT]
      rw [φ.left_inv (hCφ hx)]
    exact h5
  rw [h1, setLIntegral_congr_fun hφCm h2, ← hcv, h4]


/-- **Weighted volume from a single chart.** If `μ` has the chart density in one `C¹` chart `Ξ`, does not charge
`Ξ.sourceᶜ`, and `Ξ.sourceᶜ` is Lebesgue-negligible in every `chartAt`, then `IsWeightedVolume F μ V`. -/
theorem isWeightedVolume_of_chart {V : M → ℝ} {μ : Measure M} (Ξ : OpenPartialHomeomorph M F)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ Ξ.source)
    (hΞ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target)
    (hmap : (μ.restrict Ξ.source).map Ξ = (volume.restrict Ξ.target).withDensity
      fun w => ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w))
    (hnull0 : μ Ξ.sourceᶜ = 0)
    (hnull : ∀ x₀ : M, volume ((chartAt F x₀) '' ((chartAt F x₀).source ∩ Ξ.sourceᶜ)) = 0) :
    IsWeightedVolume F μ V := by
  intro x₀
  set φ := chartAt F x₀ with hφdef
  have hφ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 φ.symm φ.target :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, F)) (n := 1) (x := x₀))
  have hφ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 φ φ.source :=
    (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := 1) (x := x₀))
  set U := φ.source ∩ Ξ.source with hU
  have hUo : IsOpen U := φ.open_source.inter Ξ.open_source
  have hbase : ∀ C ⊆ U, MeasurableSet C → μ C = ∫⁻ w in Ξ '' C,
      ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w) := by
    intro C hCU hCm
    have hCS : C ⊆ Ξ.source := hCU.trans inter_subset_right
    have himgm : MeasurableSet (Ξ '' C) := by
      rw [Ξ.image_eq_target_inter_inv_preimage hCS]
      exact measurableSet_inter_preimage_of_continuousOn Ξ.open_target.measurableSet
        Ξ.continuousOn_symm hCm
    have hmΞ : AEMeasurable Ξ (μ.restrict Ξ.source) :=
      Ξ.continuousOn.aemeasurable Ξ.open_source.measurableSet
    have := congrArg (fun ν => ν (Ξ '' C)) hmap
    simp only [Measure.map_apply_of_aemeasurable hmΞ himgm,
      Measure.restrict_apply' Ξ.open_source.measurableSet, withDensity_apply _ himgm,
      Measure.restrict_restrict himgm] at this
    rw [Ξ.injOn.preimage_image_inter hCS] at this
    rw [this, inter_eq_left.2 (by rw [← Ξ.image_source_eq_target]; exact Set.image_mono hCS)]
  have hUt : IsOpen U := hUo
  -- the exceptional part of the target of `φ`
  have hexc : φ.target \ φ '' U = φ '' (φ.source ∩ Ξ.sourceᶜ) := by
    rw [← φ.image_source_eq_target]
    ext z
    simp only [mem_sdiff, mem_image, hU, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, h⟩
      exact ⟨x, ⟨hx, fun hS => h ⟨x, ⟨hx, hS⟩, rfl⟩⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hS⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro ⟨y, ⟨hy, hyS⟩, hyx⟩
      have : y = x := φ.injOn hy hx hyx
      exact hS (this ▸ hyS)
  have hexc0 : volume (φ.target \ φ '' U) = 0 := by rw [hexc]; exact hnull x₀
  ext B hB
  have hmφ : AEMeasurable φ (μ.restrict φ.source) :=
    φ.continuousOn.aemeasurable φ.open_source.measurableSet
  rw [Measure.map_apply_of_aemeasurable hmφ hB, Measure.restrict_apply' φ.open_source.measurableSet,
    withDensity_apply _ hB, Measure.restrict_restrict hB]
  set C := U ∩ φ ⁻¹' B with hC
  have hCm : MeasurableSet C := measurableSet_inter_preimage_of_continuousOn hUo.measurableSet
    (φ.continuousOn.mono inter_subset_left) hB
  have hCU : C ⊆ U := inter_subset_left
  have hmu : μ (φ ⁻¹' B ∩ φ.source) = μ C := by
    rw [← measure_inter_conull (s := φ ⁻¹' B ∩ φ.source) (t := Ξ.source) hnull0]
    congr 1
    ext x
    simp only [hC, hU, mem_inter_iff, mem_preimage]
    tauto
  rw [hmu]
  have htr := chart_mass_transfer (V := V) (μ := μ) Ξ φ hΞ' hφ (hφ' ) (U := U) inter_subset_right
    inter_subset_left hbase hCU hCm
  rw [htr]
  have himg : φ '' C = B ∩ φ '' U := by
    rw [hC, Set.image_inter_preimage, inter_comm]
  rw [himg]
  have hsplit : B ∩ φ.target = (B ∩ φ '' U) ∪ (B ∩ (φ.target \ φ '' U)) := by
    ext z
    have hsub : φ '' U ⊆ φ.target := by
      rw [← φ.image_source_eq_target]; exact Set.image_mono inter_subset_left
    simp only [mem_inter_iff, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hb, ht⟩
      by_cases h : z ∈ φ '' U
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, ht, h⟩
    · rintro (⟨hb, h⟩ | ⟨hb, ht, _⟩)
      · exact ⟨hb, hsub h⟩
      · exact ⟨hb, ht⟩
  have hopen : IsOpen (φ '' U) := φ.isOpen_image_of_subset_source hUo inter_subset_left
  have hm2 : MeasurableSet (B ∩ (φ.target \ φ '' U)) :=
    hB.inter (φ.open_target.measurableSet.diff hopen.measurableSet)
  have hdisj : Disjoint (B ∩ φ '' U) (B ∩ (φ.target \ φ '' U)) := by
    rw [Set.disjoint_left]
    rintro z ⟨_, h1⟩ ⟨_, _, h2⟩
    exact h2 h1
  rw [hsplit, lintegral_union hm2 hdisj]
  have hz : ∫⁻ w in B ∩ (φ.target \ φ '' U), ENNReal.ofReal (Real.exp (-V (φ.symm w)) *
      chartVolumeDensity F x₀ w) = 0 :=
    setLIntegral_measure_zero _ _ (measure_mono_null inter_subset_right hexc0)
  rw [hz, add_zero]
  simp only [chartVolumeDensity_eq_chartDensity]
  rfl


section construction

variable (x₁ : M)

/-- The chart-density measure of the chart `chartAt x₁`, with constant `a`: density `a · ρ_Ξ` in that chart. -/
noncomputable def chartMeasure (a : ℝ) : Measure M :=
  ((volume.restrict (chartAt F x₁).target).withDensity
    fun w => ENNReal.ofReal (a * chartDensity (chartAt F x₁) w)).map (chartAt F x₁).symm

lemma aemeasurable_symm_chartMeasure (a : ℝ) :
    AEMeasurable (chartAt F x₁).symm ((volume.restrict (chartAt F x₁).target).withDensity
      fun w => ENNReal.ofReal (a * chartDensity (chartAt F x₁) w)) :=
  ((chartAt F x₁).continuousOn_symm.aemeasurable (chartAt F x₁).open_target.measurableSet).mono_ac
    (withDensity_absolutelyContinuous _ _)

lemma chartMeasure_apply_of_subset (a : ℝ) {C : Set M} (hC : C ⊆ (chartAt F x₁).source)
    (hCm : MeasurableSet C) :
    chartMeasure (F := F) x₁ a C =
      ∫⁻ w in (chartAt F x₁) '' C, ENNReal.ofReal (a * chartDensity (chartAt F x₁) w) := by
  set Ξ := chartAt F x₁ with hΞ
  unfold chartMeasure
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_symm_chartMeasure x₁ a) hCm,
    withDensity_apply' _ _, Measure.restrict_restrict' Ξ.open_target.measurableSet,
    inter_comm, ← Ξ.image_eq_target_inter_inv_preimage hC]

lemma chartMeasure_compl (a : ℝ) : chartMeasure (F := F) x₁ a (chartAt F x₁).sourceᶜ = 0 := by
  set Ξ := chartAt F x₁ with hΞ
  unfold chartMeasure
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_symm_chartMeasure x₁ a)
    Ξ.open_source.measurableSet.compl]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply' Ξ.open_target.measurableSet]
  have : Ξ.symm ⁻¹' Ξ.sourceᶜ ∩ Ξ.target = ∅ := by
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hw hwt
    exact hw (Ξ.map_target hwt)
  rw [this]; simp

lemma chartMeasure_map (a : ℝ) :
    ((chartMeasure (F := F) x₁ a).restrict (chartAt F x₁).source).map (chartAt F x₁) =
      (volume.restrict (chartAt F x₁).target).withDensity
        fun w => ENNReal.ofReal (a * chartDensity (chartAt F x₁) w) := by
  set Ξ := chartAt F x₁ with hΞ
  ext B hB
  rw [Measure.map_apply_of_aemeasurable
    (Ξ.continuousOn.aemeasurable Ξ.open_source.measurableSet) hB,
    Measure.restrict_apply' Ξ.open_source.measurableSet, withDensity_apply _ hB,
    Measure.restrict_restrict hB]
  have hm : MeasurableSet (Ξ.source ∩ Ξ ⁻¹' B) :=
    measurableSet_inter_preimage_of_continuousOn Ξ.open_source.measurableSet Ξ.continuousOn hB
  rw [inter_comm, chartMeasure_apply_of_subset x₁ a inter_subset_left hm,
    Set.image_inter_preimage, Ξ.image_source_eq_target, inter_comm]

theorem chartMeasure_isWeightedVolume {a : ℝ} (ha : 0 < a)
    (hnull : ∀ x₀ : M, volume ((chartAt F x₀) '' ((chartAt F x₀).source ∩ (chartAt F x₁).sourceᶜ)) = 0) :
    IsWeightedVolume F (chartMeasure (F := F) x₁ a) (fun _ => -Real.log a) := by
  refine isWeightedVolume_of_chart (chartAt F x₁) (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := 1) (x := x₁))
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, F)) (n := 1) (x := x₁)) ?_ (chartMeasure_compl x₁ a) hnull
  rw [chartMeasure_map]
  congr 1
  funext w
  simp [Real.exp_log ha]

lemma chartMeasure_univ (a : ℝ) :
    chartMeasure (F := F) x₁ a univ =
      ∫⁻ w in (chartAt F x₁).target, ENNReal.ofReal (a * chartDensity (chartAt F x₁) w) := by
  set Ξ := chartAt F x₁ with hΞ
  have h1 : chartMeasure (F := F) x₁ a univ = chartMeasure (F := F) x₁ a Ξ.source := by
    have := measure_add_measure_compl (μ := chartMeasure (F := F) x₁ a) Ξ.open_source.measurableSet
    rw [chartMeasure_compl, add_zero] at this
    exact this.symm
  rw [h1, chartMeasure_apply_of_subset x₁ a subset_rfl Ξ.open_source.measurableSet,
    Ξ.image_source_eq_target]

end construction

section finiteness

variable [CompactSpace M] (x₁ : M)

lemma chartMeasure_locallyFinite :
    IsLocallyFiniteMeasure (chartMeasure (F := F) x₁ 1) := by
  haveI : ProperSpace F := FiniteDimensional.proper_real F
  refine ⟨fun p => ?_⟩
  set Ξ := chartAt F x₁ with hΞ
  set φ := chartAt F p with hφ
  have hφ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 φ.symm φ.target :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, F)) (n := 1) (x := p))
  have hφ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 φ φ.source :=
    (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := 1) (x := p))
  have hΞ1 : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ Ξ.source :=
    contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := 1) (x := x₁)
  have hΞ1' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target :=
    contMDiffOn_chart_symm (I := 𝓘(ℝ, F)) (n := 1) (x := x₁)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 φ.open_target (φ p) (φ.map_source (mem_chart_source F p))
  set K := Metric.closedBall (φ p) (r / 2) with hK
  have hKt : K ⊆ φ.target := fun z hz => hball (by
    simp only [hK, Metric.mem_closedBall] at hz
    exact Metric.mem_ball.2 (by linarith [hz]))
  have hKc : IsCompact K := isCompact_closedBall _ _
  set A := φ.source ∩ φ ⁻¹' K with hA
  have hAm : MeasurableSet A := by
    have := measurableSet_inter_preimage_of_continuousOn φ.open_source.measurableSet
      φ.continuousOn hKc.isClosed.measurableSet
    exact this
  have hnhds : A ∈ 𝓝 p := by
    rw [mem_nhds_iff]
    refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ p) (r / 2), ?_, ?_, ?_⟩
    · exact inter_subset_inter_right _ (preimage_mono Metric.ball_subset_closedBall)
    · exact φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
    · exact ⟨mem_chart_source F p, Metric.mem_ball_self (by linarith)⟩
  refine ⟨A, hnhds, ?_⟩
  set μ := chartMeasure (F := F) x₁ 1 with hμ
  set U := φ.source ∩ Ξ.source with hU
  set C := A ∩ Ξ.source with hC
  have hCm : MeasurableSet C := hAm.inter Ξ.open_source.measurableSet
  have hCU : C ⊆ U := inter_subset_inter inter_subset_left subset_rfl
  have hμA : μ A = μ C := (measure_inter_conull (chartMeasure_compl x₁ 1)).symm
  have hbase : ∀ C' ⊆ U, MeasurableSet C' → μ C' = ∫⁻ z in Ξ '' C',
      ENNReal.ofReal (Real.exp (-(fun _ : M => (0 : ℝ)) (Ξ.symm z)) * chartDensity Ξ z) := by
    intro C' hC' hC'm
    rw [hμ, chartMeasure_apply_of_subset x₁ 1 (hC'.trans inter_subset_right) hC'm]
    simp
    rfl
  have htr := chart_mass_transfer (V := fun _ : M => (0 : ℝ)) (μ := μ) Ξ φ hΞ1' hφ hφ'
    (U := U) inter_subset_right inter_subset_left hbase hCU hCm
  have himg : φ '' C ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1.2
  have hint : IntegrableOn (fun w => chartVolumeDensity F p w) K := by
    refine ContinuousOn.integrableOn_compact hKc ?_
    exact (continuousOn_chartVolumeDensity F p).mono hKt
  rw [hμA, htr]
  refine lt_of_le_of_lt (lintegral_mono_set himg) ?_
  have := hint.integrable.lintegral_lt_top
  simpa [chartVolumeDensity_eq_chartDensity] using this

lemma chartMeasure_univ_lt_top : chartMeasure (F := F) x₁ 1 univ < ⊤ := by
  haveI := chartMeasure_locallyFinite (F := F) x₁
  exact isCompact_univ.measure_lt_top

lemma chartMeasure_univ_pos : 0 < chartMeasure (F := F) x₁ 1 univ := by
  rw [chartMeasure_univ, pos_iff_ne_zero]
  intro hI0
  set Ξ := chartAt F x₁ with hΞ
  have hmeas : AEMeasurable (fun w => ENNReal.ofReal (1 * chartDensity Ξ w)) (volume.restrict Ξ.target) := by
    have h := (continuousOn_chartVolumeDensity F x₁).aemeasurable (μ := volume) Ξ.open_target.measurableSet
    simp only [one_mul]
    exact h.ennreal_ofReal
  have h1 := (lintegral_eq_zero_iff' hmeas).1 hI0
  have h2 : ∀ᵐ w ∂(volume.restrict Ξ.target), w ∈ Ξ.target := ae_restrict_mem Ξ.open_target.measurableSet
  have h3 : ∀ᵐ w ∂(volume.restrict Ξ.target), False := by
    filter_upwards [h1, h2] with w a b
    have := chartVolumeDensity_pos F x₁ b
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero, one_mul] at a
    have h4 : chartDensity Ξ w = chartVolumeDensity F x₁ w := (chartVolumeDensity_eq_chartDensity x₁ w).symm
    linarith
  have h5 := ae_iff.1 h3
  simp only [not_false_eq_true, ofPred_true] at h5
  rw [Measure.restrict_apply_univ] at h5
  have hne : (Ξ.target).Nonempty := ⟨_, Ξ.map_source (mem_chart_source F x₁)⟩
  exact (Ξ.open_target.measure_pos volume hne).ne' h5

end finiteness

section final

/-- **Existence of a normalized Riemannian volume**: on a compact manifold such that one chart `chartAt x₁`
misses a set that is Lebesgue-negligible in every `chartAt`, there is a probability measure and a constant `c`
with `IsWeightedVolume F μ (fun _ => c)`. -/
theorem exists_probability_isWeightedVolume [CompactSpace M] (x₁ : M)
    (hnull : ∀ x₀ : M, volume ((chartAt F x₀) '' ((chartAt F x₀).source ∩ (chartAt F x₁).sourceᶜ)) = 0) :
    ∃ (μ : Measure M) (c : ℝ), IsProbabilityMeasure μ ∧ IsWeightedVolume F μ (fun _ => c) := by
  set I := chartMeasure (F := F) x₁ 1 univ with hI
  have hIt : I ≠ ⊤ := (chartMeasure_univ_lt_top x₁).ne
  have hI0 : I ≠ 0 := (chartMeasure_univ_pos x₁).ne'
  have hIr : 0 < I.toReal := ENNReal.toReal_pos hI0 hIt
  set a : ℝ := (I.toReal)⁻¹ with ha
  have hapos : 0 < a := inv_pos.2 hIr
  refine ⟨chartMeasure (F := F) x₁ a, -Real.log a, ⟨?_⟩, chartMeasure_isWeightedVolume x₁ hapos hnull⟩
  rw [chartMeasure_univ]
  have hI' : I = ∫⁻ w in (chartAt F x₁).target, ENNReal.ofReal (1 * chartDensity (chartAt F x₁) w) :=
    chartMeasure_univ x₁ 1
  have : ∀ w, ENNReal.ofReal (a * chartDensity (chartAt F x₁) w) =
      ENNReal.ofReal a * ENNReal.ofReal (1 * chartDensity (chartAt F x₁) w) := fun w => by
    rw [← ENNReal.ofReal_mul hapos.le, one_mul]
  simp only [this]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hI', ← ENNReal.ofReal_toReal hIt,
    ← ENNReal.ofReal_mul hapos.le, ha, inv_mul_cancel₀ hIr.ne']
  simp

end final


end CutoffRigidity.Extra.Sphere
