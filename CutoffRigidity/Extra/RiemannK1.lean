module

public import CutoffRigidity.Statements
public import CutoffRigidity.Riemann.DiffFinal
public import CutoffRigidity.Extra.RiemannLichnerowicz

/-! # `1 ≤ k₁ ≤ dim M` under the hypotheses of Theorem 1.9 without the semigroup
(manuscript lines ~633-636; `k₁ ≤ dim` needs `λ₁ = ρ`, false on spheres otherwise) -/

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

theorem riemannian_k1_bounds {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : CutCur.IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CutCur.CD F ρ V) (hgap : CutCur.mSpectralGap F μ = ρ) :
    1 ≤ CutCur.mFirstEigenDim F μ V ∧ CutCur.mFirstEigenDim F μ V ≤ Module.finrank ℝ F := by
  have hVs : MSmooth F V := hV
  have hpos : 0 < mFirstEigenDim F μ V :=
    gap_attained_of_LSI F hVs hμ hρ hCD hgap (lsi_of_CD F hVs hμ hρ hCD)
  refine ⟨hpos, ?_⟩
  haveI : Nonempty M := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hpos
    have h1 : μ Set.univ = 1 := measure_univ
    have : (Set.univ : Set M) = ∅ := Set.univ_eq_empty_iff.mpr h
    rw [this] at h1; simp at h1
  have hfin := finiteDimensional_eigenClasses F hVs hμ hρ hCD hgap
  rw [mFirstEigenDim_eq_finrank F hVs hμ hρ hCD hgap]
  obtain ⟨x₀⟩ := ‹Nonempty M›
  have hE : ∀ f : eigenSub F μ V ρ, IsMEigenfunction F μ V ρ f.1 := fun f => f.2
  let Φ : eigenSub F μ V ρ →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) x₀ :=
    { toFun := fun f => mgrad F f.1 x₀
      map_add' := fun f g => mgrad_add' F (hE f).1 (hE g).1 x₀
      map_smul' := fun c f => mgrad_const_mul F c (hE f).1 x₀ }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    exact eigenfunction_eq_zero_of_grad_zero F hρ.ne' f.2
      (fun x => manifold_eigenfunction_parallel_gradient F hVs hμ hρ hCD hgap f.2 x) x₀ hf
  have h1 : Module.finrank ℝ (eigenSub F μ V ρ) ≤ Module.finrank ℝ F :=
    LinearMap.finrank_le_finrank_of_injective hinj
  let ψ : eigenSub F μ V ρ →ₗ[ℝ] (M →₂[μ] ℝ) :=
    { toFun := fun f => (hE f).2.1.toLp f.1
      map_add' := fun f g => MemLp.toLp_add (hE f).2.1 (hE g).2.1
      map_smul' := fun c f => MemLp.toLp_const_smul c (hE f).2.1 }
  have hr : eigenClasses F μ V ρ = LinearMap.range ψ := by
    ext u
    constructor
    · rintro ⟨f, hf, hfu⟩
      refine ⟨⟨f, hf⟩, ?_⟩
      change (hf.2.1).toLp f = u
      refine Lp.ext ?_
      filter_upwards [MemLp.coeFn_toLp hf.2.1, hfu] with x h1 h2
      rw [h1, h2]
    · rintro ⟨f, rfl⟩
      exact ⟨f.1, hE f, (MemLp.coeFn_toLp (hE f).2.1).symm⟩
  have := finiteDimensional_eigenSub F hVs hμ hρ hCD hgap
  rw [hr]
  exact (LinearMap.finrank_range_le ψ).trans h1

end CutoffRigidity.Paper
