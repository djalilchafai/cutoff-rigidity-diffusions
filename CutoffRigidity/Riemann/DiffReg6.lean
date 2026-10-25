module

public import CutoffRigidity.Riemann.DiffReg5
public import CutoffRigidity.Riemann.WeightedIBPGlobal

/-! # Interior sup estimate, part 2: smooth eigenfunctions satisfy the chart weak equation
(workstream KER-REG)

`chart_eq_of_generator`: if `w` is smooth on `M` with `𝓛 w = lam w` on an open set `W`, then in every chart,
for all test functions `ψ` supported in `φ(W ∩ source)`,
`∫_T (⟪a ∇w̃, ∇ψ⟫ + lam w̃ ψ) ρ dz = 0`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section EqGen

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

include hV hμ in
/-- `∫ h · b dμ` for `b` supported in the chart, as a chart integral (`h` measurable). -/
theorem integral_mul_chartTestFn (h : M → ℝ) (hm : Measurable h) {ψ : F → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) :
    ∫ x, h x * (chartExtend F x₀ ψ) x ∂μ =
      ∫ z in (chartAt F x₀).target, chartRho F V x₀ z * (h ((chartAt F x₀).symm z) * ψ z) := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hb0 : ∀ x, x ∉ φ.source → h x * (chartExtend F x₀ ψ) x = 0 := fun x hx => by
    rw [chartExtend_eq_zero F x₀ hx, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hb0]
  have hG : AEStronglyMeasurable (fun z => h (φ.symm z) * ψ z) (volume.restrict φ.target) := by
    have h1 : AEMeasurable (fun z => h (φ.symm z)) (volume.restrict φ.target) :=
      hm.comp_aemeasurable (φ.continuousOn_symm.aemeasurable hTm)
    exact (h1.aestronglyMeasurable).mul hψ.continuous.aestronglyMeasurable
  rw [← integral_chart_comp F hV hμ x₀ _ hG]
  refine setIntegral_congr_fun φ.open_source.measurableSet fun x hx => ?_
  rw [chartExtend_eq F x₀ hx, φ.left_inv hx]

omit [IsFiniteMeasure μ] in
theorem integrableOn_target_of_support {ψ : F → ℝ} (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) {f : F → ℝ}
    (hf : ContinuousOn f (chartAt F x₀).target) (hz : ∀ z, z ∉ tsupport ψ → f z = 0) :
    IntegrableOn f (chartAt F x₀).target := by
  have h1 : IntegrableOn f (tsupport ψ) := (hf.mono hψT).integrableOn_compact hψc
  exact h1.of_forall_diff_eq_zero (chartAt F x₀).open_target.measurableSet
    (fun z hz' => hz z (fun h => hz'.2 h))

theorem gradient_continuousOn_of_contDiffOn (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {Ω : Set F} (hΩ : IsOpen Ω) {u : F → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) : ContinuousOn (gradient u) Ω := by
  have h1 : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hΩ (by simp)
  exact (InnerProductSpace.toDual ℝ F).symm.continuous.comp_continuousOn h1

include hV hμ in
/-- **Chart weak equation of a smooth solution of `𝓛 w = lam w` on `W`.** -/
theorem chart_eq_of_generator {W : Set M} {w : M → ℝ} (hw : MSmooth F w) {lam : ℝ}
    (hgen : ∀ y ∈ W, mgenerator F V w y = lam * w y) {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψT : tsupport ψ ⊆ (chartAt F x₀).target)
    (hψW : ∀ z ∈ tsupport ψ, (chartAt F x₀).symm z ∈ W) :
    ∫ z in (chartAt F x₀).target,
      (inner ℝ (chartCoeff F x₀ z (gradient (fun z => w ((chartAt F x₀).symm z)) z))
        (gradient ψ z) + lam * w ((chartAt F x₀).symm z) * ψ z) * chartRho F V x₀ z = 0 := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  obtain ⟨hûmem, hûS⟩ := chartExtend_mem F x₀ hψ hψc hψT
  obtain ⟨hû, hûc⟩ := hûmem
  have hibp := weightedIBP_of_isWeightedVolume F hV hμ _ w hû hw hûc
  have hch := integral_carre_chart F hV hμ x₀ hû hw hûS
  have hwT : ContDiffOn ℝ ∞ (fun z => w (φ.symm z)) φ.target := contDiffOn_chartCoord F x₀ hw
  have e1 : ∫ z in φ.target, chartRho F V x₀ z *
      inner ℝ (gradient (chartExtend F x₀ ψ ∘ φ.symm) z)
        (chartCoeff F x₀ z (gradient (w ∘ φ.symm) z)) =
      ∫ z in φ.target, inner ℝ (chartCoeff F x₀ z (gradient (fun z => w (φ.symm z)) z))
        (gradient ψ z) * chartRho F V x₀ z := by
    refine setIntegral_congr_fun hTm fun z hz => ?_
    have := chartGrad_chartExtend F x₀ (ψ := ψ) hz
    unfold chartGrad at this
    rw [this, real_inner_comm, mul_comm]
    rfl
  have e2 : ∫ x, chartExtend F x₀ ψ x * mgenerator F V w x ∂μ =
      lam * ∫ z in φ.target, chartRho F V x₀ z * (w (φ.symm z) * ψ z) := by
    rw [← integral_mul_chartTestFn F hV hμ x₀ w hw.continuous.measurable hψ hψc hψT,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases h0 : chartExtend F x₀ ψ x = 0
    · simp [h0]
    · have hxS : x ∈ φ.source := by
        by_contra hx; exact h0 (chartExtend_eq_zero F x₀ hx)
      have hxz : φ x ∈ tsupport ψ := by
        rw [chartExtend_eq F x₀ hxS] at h0
        exact subset_tsupport _ h0
      have hxW : x ∈ W := by
        have := hψW _ hxz
        rwa [φ.left_inv hxS] at this
      simp only [hgen x hxW]
      ring
  have hmain : ∫ z in φ.target, chartRho F V x₀ z *
      inner ℝ (gradient (chartExtend F x₀ ψ ∘ φ.symm) z)
        (chartCoeff F x₀ z (gradient (w ∘ φ.symm) z)) =
      -(lam * ∫ z in φ.target, chartRho F V x₀ z * (w (φ.symm z) * ψ z)) := by
    rw [← hch, hibp, e2]
  rw [e1] at hmain
  -- integrability
  have hz1 : ∀ z, z ∉ tsupport ψ → (inner ℝ (chartCoeff F x₀ z (gradient (fun z => w (φ.symm z)) z))
        (gradient ψ z)) * chartRho F V x₀ z = 0 := by
    intro z hz
    have hev := notMem_tsupport_iff_eventuallyEq.1 hz
    have : fderiv ℝ ψ z = 0 := by rw [hev.fderiv_eq]; simp
    simp [gradient, this]
  have hz2 : ∀ z, z ∉ tsupport ψ → w (φ.symm z) * ψ z * chartRho F V x₀ z = 0 := by
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  have hρ : ContinuousOn (chartRho F V x₀) φ.target := (contDiffOn_chartRho F hV x₀).continuousOn
  have hgψ : Continuous (gradient ψ) :=
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp (hψ.continuous_fderiv (by simp))
  have hI1 : IntegrableOn (fun z => inner ℝ (chartCoeff F x₀ z (gradient (fun z => w (φ.symm z)) z))
        (gradient ψ z) * chartRho F V x₀ z) φ.target := by
    refine integrableOn_target_of_support F x₀ hψc hψT ?_ hz1
    exact (((contDiffOn_chartCoeff F x₀).continuousOn.clm_apply
      (gradient_continuousOn_of_contDiffOn F φ.open_target hwT)).inner hgψ.continuousOn).mul hρ
  have hI2 : IntegrableOn (fun z => w (φ.symm z) * ψ z * chartRho F V x₀ z) φ.target := by
    refine integrableOn_target_of_support F x₀ hψc hψT ?_ hz2
    exact ((hwT.continuousOn.mul hψ.continuous.continuousOn)).mul hρ
  have hsplit : ∫ z in φ.target, (inner ℝ (chartCoeff F x₀ z (gradient (fun z => w (φ.symm z)) z))
        (gradient ψ z) + lam * w (φ.symm z) * ψ z) * chartRho F V x₀ z =
      (∫ z in φ.target, inner ℝ (chartCoeff F x₀ z (gradient (fun z => w (φ.symm z)) z))
        (gradient ψ z) * chartRho F V x₀ z) +
      lam * ∫ z in φ.target, w (φ.symm z) * ψ z * chartRho F V x₀ z := by
    rw [← integral_const_mul, ← integral_add hI1 (hI2.const_mul lam)]
    refine setIntegral_congr_fun hTm fun z hz => ?_
    ring
  have e3 : ∫ z in φ.target, chartRho F V x₀ z * (w (φ.symm z) * ψ z) =
      ∫ z in φ.target, w (φ.symm z) * ψ z * chartRho F V x₀ z :=
    setIntegral_congr_fun hTm fun z hz => by ring
  rw [hsplit, hmain, ← e3]
  ring

end EqGen

end CutoffRigidity.Riemann.Diff
