module

public import CutoffRigidity.Riemann.DiffGapAttained2
public import CutoffRigidity.Extra.Sphere11

/-! # Sphere, stage 12: existence of a first eigenfunction on a compact manifold WITHOUT any `CD` hypothesis

Copy of the proof of `CutoffRigidity.Riemann.Diff.gap_attained_of_compact` (project, `DiffGapAttained.lean`), where
the hypothesis `CD F ρ V` was used only in the last line (`mFirstEigenDim_pos_iff`, finite-dimensionality of the
eigenspace).  Here the conclusion is only the existence of a nonzero smooth `L²` eigenfunction for `ρ = mSpectralGap`
(any `ρ > 0` with `mSpectralGap F μ = ρ`), which is all the Obata-type argument needs.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set ProbabilityTheory
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutoffRigidity.Riemann.Diff

section Gap

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ]
  (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
  (hgap : mSpectralGap F μ = ρ)

include hV hμ hρ hgap in
/-- Eigenfunction attainment from compactness of the energy balls, without `CD`. -/
theorem exists_eigenfunction_of_compact_gap
    (hcomp : ∀ C : ℝ, TotallyBounded {u : M →₂[μ] ℝ | u ∈ (diffT F hV hμ).Q ∧
      (diffT F hV hμ).E u u + ‖u‖ ^ 2 ≤ C}) :
    ∃ f, IsMEigenfunction F μ V ρ f ∧ ∃ x, f x ≠ 0 := by
  have hopen := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  obtain ⟨v, hvQ, hv1, hv0, hEL⟩ := (diffT F hV hμ).exists_eigen_of_compact (oneL2 μ)
    (one_mem_Q F hV hμ (diffT F hV hμ)).1 (norm_oneL2 (μ := μ))
    (one_mem_Q F hV hμ (diffT F hV hμ)).2 hρ (poincare_D F hV hμ hρ hgap)
    (fun δ hδ => poincare_D_sharp F hV hμ hρ hgap hδ) hcomp
  obtain ⟨vb, hvb, hvae⟩ := diff_eigen_smooth F hV hμ (c := ρ) hvQ hEL
  refine ⟨vb, ⟨hvb, (Lp.memLp v).ae_eq hvae, ?_⟩, ?_⟩
  · -- pointwise equation
    have hg : Continuous (fun x => mgenerator F V vb x + ρ * vb x) :=
      (continuous_iff_continuousAt.mpr (continuousAt_mgenerator F hV hvb)).add
        (continuous_const.mul hvb.continuous)
    have key : ∀ b : M → ℝ, MSmooth F b → HasCompactSupport b →
        ∫ x, b x * (mgenerator F V vb x + ρ * vb x) ∂μ = 0 := by
      intro b hb hbc
      let bt : testSub F M := ⟨b, hb, hbc⟩
      have h1 : (diffT F hV hμ).E v (testToL2 F μ bt) =
          inner ℝ v (-(testToL2 F μ (testGen F hV bt))) := by
        have := (diffT F hV hμ).E_coe_right v hvQ ⟨testToL2 F μ bt, bt, rfl⟩
        rw [this]
        show inner ℝ v (diffA F hV hμ ⟨testToL2 F μ bt, bt, rfl⟩) = _
        rw [diffA_toL2]
      have h2 := hEL (testToL2 F μ bt) ((diffT F hV hμ).coe_mem ⟨testToL2 F μ bt, bt, rfl⟩)
      rw [h1] at h2
      rw [L2_inner_eq', L2_inner_eq'] at h2
      have h3 : ∫ x, (v : M → ℝ) x * (-(testToL2 F μ (testGen F hV bt)) : M →₂[μ] ℝ) x ∂μ =
          -∫ x, vb x * mgenerator F V b x ∂μ := by
        rw [← integral_neg]
        refine integral_congr_ae ?_
        filter_upwards [hvae, Lp.coeFn_neg (testToL2 F μ (testGen F hV bt)),
          coeFn_testToL2 F μ (testGen F hV bt)] with x hx h4 h5
        rw [h4, Pi.neg_apply, h5, hx]
        simp [testGen_apply]
        exact Or.inl rfl
      have h4 : ∫ x, (v : M → ℝ) x * (testToL2 F μ bt : M → ℝ) x ∂μ =
          ∫ x, vb x * b x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hvae, coeFn_testToL2 F μ bt] with x hx h5
        rw [hx, h5]
      rw [h3, h4] at h2
      have h5 := integral_mul_generator_comm F hV hμ hvb hb hbc
      have hi1 : Integrable (fun x => b x * mgenerator F V vb x) μ := by
        have hc : Continuous (fun x => b x * mgenerator F V vb x) :=
          hb.continuous.mul (continuous_iff_continuousAt.mpr (continuousAt_mgenerator F hV hvb))
        exact hc.integrable_of_hasCompactSupport
          (HasCompactSupport.intro hbc fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
      have hi2 : Integrable (fun x => b x * (ρ * vb x)) μ := by
        have hc : Continuous (fun x => b x * (ρ * vb x)) :=
          hb.continuous.mul (continuous_const.mul hvb.continuous)
        exact hc.integrable_of_hasCompactSupport
          (HasCompactSupport.intro hbc fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
      simp only [mul_add]
      rw [integral_add hi1 hi2]
      have h6 : ∫ x, b x * (ρ * vb x) ∂μ = ρ * ∫ x, vb x * b x ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      rw [h6, ← h5]
      linarith
    intro x
    have := eq_zero_of_integral_test F hg key x
    linarith
  · by_contra hall
    push Not at hall
    have h0 : (v : M → ℝ) =ᵐ[μ] 0 := by
      filter_upwards [hvae] with x hx
      rw [hx]; exact hall x
    have : v = 0 := Lp.eq_zero_iff_ae_eq_zero.2 h0
    rw [this, norm_zero] at hv1
    exact zero_ne_one hv1


end Gap

end CutoffRigidity.Extra.Sphere
