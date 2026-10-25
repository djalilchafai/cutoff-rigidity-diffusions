module

public import CutoffRigidity.Statements
public import CutoffRigidity.Riemann.DiffFinal
public import CutoffRigidity.Extra.RiemannLichnerowicz

/-! # Riemannian Poincaré and log-Sobolev inequalities from `CD(ρ,∞)` (manuscript lines ~618-632)

No assumption on the spectral gap: `ρ Var f ≤ ∫ |∇f|²` and `Ent_μ(f²) ≤ (2/ρ) ∫ |∇f|²` for smooth
compactly supported `f`. -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Manifold ContDiff RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CutoffRigidity.Paper
open CutCur CutoffRigidity.Riemann CutoffRigidity.Riemann.Diff

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem riemannian_poincare_lsi {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : CutCur.IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CutCur.CD F ρ V) :
    ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, ‖CutCur.mgrad F f x‖ ^ 2 ∂μ ∧
      CutCur.entropyOf μ (fun x => f x ^ 2) ≤ 2 / ρ * ∫ x, ‖CutCur.mgrad F f x‖ ^ 2 ∂μ := by
  intro f hf hc
  have hVs : MSmooth F V := hV
  have h1 := poincare_of_CD F hVs hμ hρ hCD f hf hc
  have h2 := lsi_of_CD F hVs hμ hρ hCD ⟨f, hf, hc⟩
  have hcar : ∫ x, carre F f f x ∂μ = ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [carre, real_inner_self_eq_norm_sq])
  rw [hcar] at h1
  refine ⟨h1, ?_⟩
  have h3 : entL μ (fun x => f x ^ 2) ≤ 2 / ρ * ∫ x, carre F f f x ∂μ := h2
  rw [hcar] at h3
  exact h3

end CutoffRigidity.Paper
