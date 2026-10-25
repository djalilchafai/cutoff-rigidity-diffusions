module

public import CutoffRigidity.Riemann.DiffMarkov
public import CutoffRigidity.Riemann.DiffAPI
public import CutoffRigidity.Riemann.EigenLinear
public import CutoffRigidity.Riemann.WeightedIBPGlobal
public import CutoffRigidity.Riemann.WeightedIBPDensity
public import CutoffRigidity.Riemann.WeightedSupport
public import CutoffRigidity.Riemann.WeightedGradHelpers
public import CutoffRigidity.Riemann.WeightedCutoffs

/-! # Test functions, the operator `A = -𝓛` and the energy on `L²(μ)` (workstream DIR)

`testSub F M` is the space `𝒟 = C_c^∞(M)` of smooth compactly supported functions.  For a finite
measure `μ` which is `e^{-V} vol` in every chart, `𝒟` embeds linearly and injectively in
`L²(μ)` (`testToL2`) and `A = -𝓛 : 𝒟 → L²(μ)` is symmetric and nonnegative with
`⟨A f, g⟩ = ∫ Γ(f,g) dμ` (`inner_testGen`), by the project integration by parts.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Test

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  (M : Type) [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- `𝒟 = C_c^∞(M)`: smooth functions with compact support. -/
def testSub : Submodule ℝ (M → ℝ) where
  carrier := {f | MSmooth F f ∧ HasCompactSupport f}
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨contMDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c f hf => ⟨(by exact (contMDiff_const (c := c)).mul hf.1 : MSmooth F (fun x => c * f x)), hf.2.smul_left⟩

variable {M}

theorem mem_testSub {f : M → ℝ} : f ∈ testSub F M ↔ MSmooth F f ∧ HasCompactSupport f := Iff.rfl

theorem testSub_continuous (f : testSub F M) : Continuous (f : M → ℝ) := f.2.1.continuous

theorem testSub_memLp (f : testSub F M) (μ : Measure M) [IsFiniteMeasure μ] :
    MemLp (f : M → ℝ) 2 μ :=
  (testSub_continuous F f).memLp_of_hasCompactSupport f.2.2

theorem testSub_bounded (f : testSub F M) : ∃ C : ℝ, ∀ x, |(f : M → ℝ) x| ≤ C := by
  obtain ⟨C, hC⟩ := (testSub_continuous F f).bounded_above_of_compact_support f.2.2
  exact ⟨C, fun x => by simpa using hC x⟩

/-- The embedding `𝒟 → L²(μ)`. -/
noncomputable def testToL2 (μ : Measure M) [IsFiniteMeasure μ] :
    testSub F M →ₗ[ℝ] (M →₂[μ] ℝ) where
  toFun f := (testSub_memLp F f μ).toLp (f : M → ℝ)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (testSub_memLp F (f + g) μ),
      MemLp.coeFn_toLp (testSub_memLp F f μ), MemLp.coeFn_toLp (testSub_memLp F g μ),
      Lp.coeFn_add ((testSub_memLp F f μ).toLp (f : M → ℝ)) ((testSub_memLp F g μ).toLp (g : M → ℝ))] with x h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (testSub_memLp F (c • f) μ),
      MemLp.coeFn_toLp (testSub_memLp F f μ),
      Lp.coeFn_smul c ((testSub_memLp F f μ).toLp (f : M → ℝ))] with x h1 h2 h3
    rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2]
    rfl

theorem testToL2_apply (μ : Measure M) [IsFiniteMeasure μ] (f : testSub F M) :
    testToL2 F μ f = (testSub_memLp F f μ).toLp (f : M → ℝ) := rfl

theorem coeFn_testToL2 (μ : Measure M) [IsFiniteMeasure μ] (f : testSub F M) :
    (testToL2 F μ f : M → ℝ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp (testSub_memLp F f μ)

/-- `μ = e^{-V} vol` charges every nonempty open set. -/
theorem isOpenPosMeasure_of_isWeightedVolume {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
    (hμ : IsWeightedVolume F μ V) : μ.IsOpenPosMeasure :=
  ⟨fun _ hU hne => (measure_pos_of_isWeightedVolume F hV hμ (continuousOn_chartVolumeDensity F)
    (fun x₀ _ hz => chartVolumeDensity_pos F x₀ hz) hU hne).ne'⟩

theorem testToL2_injective {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
    (hμ : IsWeightedVolume F μ V) : Function.Injective (testToL2 F μ) := by
  have := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  intro f g hfg
  apply Subtype.ext
  have h1 := coeFn_testToL2 F μ f
  have h2 := coeFn_testToL2 F μ g
  rw [hfg] at h1
  exact (testSub_continuous F f).ae_eq_iff_eq μ (testSub_continuous F g) |>.1
    (h1.symm.trans h2)

/-- `𝓛` as a linear endomorphism of `𝒟`. -/
noncomputable def testGen {V : M → ℝ} (hV : MSmooth F V) : testSub F M →ₗ[ℝ] testSub F M where
  toFun f := ⟨fun x => mgenerator F V (f : M → ℝ) x, msmooth_mgenerator F hV f.2.1,
    hasCompactSupport_mgenerator F V f.2.1 f.2.2⟩
  map_add' f g := Subtype.ext (funext fun x => mgenerator_add F f.2.1 g.2.1 x)
  map_smul' c f := Subtype.ext (funext fun x => mgenerator_const_mul F c f.2.1 x)

theorem testGen_apply {V : M → ℝ} (hV : MSmooth F V) (f : testSub F M) (x : M) :
    (testGen F hV f : M → ℝ) x = mgenerator F V (f : M → ℝ) x := rfl

/-- `⟪f, g⟫_{L²}` for test functions is the integral of the product. -/
theorem inner_testToL2 (μ : Measure M) [IsFiniteMeasure μ] (f g : testSub F M) :
    inner ℝ (testToL2 F μ f) (testToL2 F μ g) = ∫ x, (f : M → ℝ) x * (g : M → ℝ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testToL2 F μ f, coeFn_testToL2 F μ g] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- **Green's formula on test functions**: `⟪f, -𝓛g⟫ = ∫ Γ(f,g) dμ`. -/
theorem inner_testGen {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
    (hμ : IsWeightedVolume F μ V) (f g : testSub F M) :
    inner ℝ (testToL2 F μ f) (-(testToL2 F μ (testGen F hV g))) =
      ∫ x, carre F (f : M → ℝ) (g : M → ℝ) x ∂μ := by
  rw [inner_neg_right, inner_testToL2]
  have := weightedIBP_of_isWeightedVolume F hV hμ (f : M → ℝ) (g : M → ℝ) f.2.1 g.2.1 f.2.2
  rw [this]
  rfl

/-- Chain rule for the gradient with a smooth real function. -/
theorem mgrad_comp_real {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ} (hf : MSmooth F f) (x : M) :
    mgrad F (θ ∘ f) x = deriv θ (f x) • mgrad F f x := by
  apply ext_inner_right ℝ
  intro v
  rw [mgrad_inner F, mvfderiv_comp_real F θ f (hθ.differentiable (by simp) _)
    (mdifferentiableAt_of_msmooth F hf x) v, inner_smul_left, mgrad_inner F]
  simp

theorem carre_comp_left {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ} (hf : MSmooth F f)
    (g : M → ℝ) (x : M) : carre F (θ ∘ f) g x = deriv θ (f x) * carre F f g x := by
  simp only [carre, mgrad_comp_real F hθ hf, real_inner_smul_left]

theorem carre_comp_self {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ} (hf : MSmooth F f)
    (x : M) : carre F (θ ∘ f) (θ ∘ f) x = deriv θ (f x) ^ 2 * carre F f f x := by
  simp only [carre, mgrad_comp_real F hθ hf, real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Stability of `𝒟` under smooth normal contractions**: `θ ∘ f ∈ 𝒟` and
`Γ(θ∘f) = θ'(f)² Γ(f) ≤ Γ(f)`. -/
theorem normalContraction_stable (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (h0 : θ 0 = 0)
    (h1 : ∀ s, |deriv θ s| ≤ 1) (f : M → ℝ) (hf : f ∈ testSub F M) :
    θ ∘ f ∈ testSub F M ∧ ∀ x, carre F (θ ∘ f) (θ ∘ f) x ≤ carre F f f x := by
  refine ⟨⟨hθ.contMDiff.comp hf.1, hf.2.comp_left h0⟩, fun x => ?_⟩
  rw [carre_comp_self F hθ hf.1]
  have h2 : deriv θ (f x) ^ 2 ≤ 1 := by
    have := h1 (f x)
    nlinarith [abs_nonneg (deriv θ (f x)), sq_abs (deriv θ (f x))]
  nlinarith [carre_nonneg F f x]

/-- Lipschitz version: if `|θ'| ≤ L` then `Γ(θ∘f) ≤ L² Γ(f)`. -/
theorem normalContraction_stable' (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (h0 : θ 0 = 0) {L : ℝ}
    (h1 : ∀ s, |deriv θ s| ≤ L) (f : M → ℝ) (hf : f ∈ testSub F M) :
    θ ∘ f ∈ testSub F M ∧ ∀ x, carre F (θ ∘ f) (θ ∘ f) x ≤ L ^ 2 * carre F f f x := by
  refine ⟨⟨hθ.contMDiff.comp hf.1, hf.2.comp_left h0⟩, fun x => ?_⟩
  rw [carre_comp_self F hθ hf.1]
  have h2 : deriv θ (f x) ^ 2 ≤ L ^ 2 := by
    have := h1 (f x)
    nlinarith [abs_nonneg (deriv θ (f x)), sq_abs (deriv θ (f x))]
  nlinarith [carre_nonneg F f x]

end Test

end CutoffRigidity.Riemann.Diff
