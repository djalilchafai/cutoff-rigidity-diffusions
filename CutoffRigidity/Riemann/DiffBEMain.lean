module

public import CutoffRigidity.Riemann.DiffBEMain3

/-! # The pointwise Bakry-Emery gradient bound (workstream BE, part D: A8)

`beStrong_of_CD`: `‖∇ K_t f‖ ≤ e^{-ρ t} K_t ‖∇f‖` pointwise, from `CD F ρ V`;
`bePointwise_of_CD`: `Γ(K_t f) ≤ e^{-2ρ t} K_t Γ(f)`; `gradBound_of_CD`; `exists_kernel_canonical`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Main

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- Strong (gradient) form of the Bakry-Emery bound. -/
def BEStrong (V : M → ℝ) (μ : Measure M) (ρ : ℝ) (Kk : ℝ≥0 → Kernel M M) : Prop :=
  ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
    Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x

/-- Quadratic form of the Bakry-Emery bound. -/
def BEPointwise (V : M → ℝ) (μ : Measure M) (ρ : ℝ) (Kk : ℝ≥0 → Kernel M M) : Prop :=
  ∀ (f : testSub F M) (t : ℝ≥0) (x : M), carre F (semi Kk t (f : M → ℝ)) (semi Kk t (f : M → ℝ)) x ≤
    Real.exp (-2 * ρ * t) * ∫ y, carre F (f : M → ℝ) (f : M → ℝ) y ∂Kk t x

variable {V : M → ℝ} {μ : Measure M} {ρ : ℝ}

/-- **Pointwise Bakry-Emery gradient bound** (sqrt version). -/
theorem beStrong_of_CD (hV : MSmooth F V) [IsFiniteMeasure μ] (hμ : IsWeightedVolume F μ V)
    (hρ : 0 < ρ) (hCD : CD F ρ V) : BEStrong F V μ ρ (Kk F hV hμ) := by
  intro f t x
  haveI := Kk_markov F hV hμ t
  by_cases ht : t = 0
  · subst ht
    simp [Kk_zero, semi_Kk_zero, Kernel.id_apply, integral_dirac]
  · haveI := isOpenPosMeasure_of_isWeightedVolume F hV hμ
    have hIBP := weightedIBP_of_isWeightedVolume F hV hμ
    have hReg := weightedRegular V hV
    have hC := weightedCutoffs_of_complete F (M := M)
    have hB := weightedBochnerIneq_of_CD (F := F) hV hCD
    have hfg : Continuous fun y => ‖mgrad F (f : M → ℝ) y‖ := continuous_norm_mgrad F hReg f.2.1
    have hGc : Continuous (semi (Kk F hV hμ) t (fun y => ‖mgrad F (f : M → ℝ) y‖)) :=
      continuous_semi_bdd F hV hμ ht hfg (bdd_norm_mgrad F hReg f)
    refine le_of_integral_le F (μ := μ) (u := fun x => ‖mgrad F (semi (Kk F hV hμ) t (f : M → ℝ)) x‖)
      (v := fun x => Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk F hV hμ t x)
      (continuous_norm_mgrad F hReg (continuous_semi_test F hV hμ ht f))
      (continuous_const.mul hGc) ?_ x
    intro ζ hζ
    have := integrated_grad F hV hμ hIBP hReg hC hρ.le hB f ζ hζ ht
    show _ ≤ _
    simp_rw [mul_left_comm _ (Real.exp _), integral_const_mul]
    exact this

/-- **Pointwise Bakry-Emery bound**, quadratic version (Jensen). -/
theorem bePointwise_of_CD (hV : MSmooth F V) [IsFiniteMeasure μ] (hμ : IsWeightedVolume F μ V)
    (hρ : 0 < ρ) (hCD : CD F ρ V) : BEPointwise F V μ ρ (Kk F hV hμ) := by
  intro f t x
  haveI := Kk_markov F hV hμ t
  have hReg := weightedRegular V hV
  have hs := beStrong_of_CD F hV hμ hρ hCD f t x
  set P := Kk F hV hμ t x
  set g : M → ℝ := fun y => ‖mgrad F (f : M → ℝ) y‖ with hg
  obtain ⟨Cf, hCf⟩ := bdd_norm_mgrad F hReg f
  have hmem : MemLp g 2 P :=
    MemLp.of_bound (continuous_norm_mgrad F hReg f.2.1).aestronglyMeasurable Cf
      (Eventually.of_forall fun y => by simpa [hg] using hCf y)
  have hj := sq_integral_le_integral_sq hmem
  have e1 : ∫ y, carre F (f : M → ℝ) (f : M → ℝ) y ∂P = ∫ y, g y ^ 2 ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hg, carre_self_eq]
  have hn := norm_nonneg (mgrad F (semi (Kk F hV hμ) t (f : M → ℝ)) x)
  have h2 := pow_le_pow_left₀ hn hs 2
  rw [← carre_self_eq] at h2
  refine h2.trans ?_
  have hexp : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [mul_pow, hexp, e1]
  exact mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le

/-- Uniform-in-time gradient bound. -/
theorem gradBound_of_CD (hV : MSmooth F V) [IsFiniteMeasure μ] (hμ : IsWeightedVolume F μ V)
    (hρ : 0 < ρ) (hCD : CD F ρ V) :
    ∀ g : M → ℝ, MSmooth F g → HasCompactSupport g →
      ∃ C : ℝ, ∀ (s : ℝ≥0) x, ‖mgrad F (semi (Kk F hV hμ) s g) x‖ ≤ C := by
  intro g hg hc
  have hReg := weightedRegular V hV
  have hΓ : Continuous (carre F g g) := (hReg.1 g g hg hg).continuous
  obtain ⟨C0, hC0⟩ := hΓ.bounded_above_of_compact_support (hasCompactSupport_carre F g hc)
  refine ⟨Real.sqrt C0, fun s x => ?_⟩
  haveI := Kk_markov F hV hμ s
  have h1 := bePointwise_of_CD F hV hμ hρ hCD ⟨g, hg, hc⟩ s x
  simp only at h1
  rw [carre_self_eq] at h1
  have hint : ∫ y, carre F g g y ∂Kk F hV hμ s x ≤ C0 := by
    have := norm_integral_le_of_norm_le_const (μ := Kk F hV hμ s x) (f := carre F g g) (C := C0)
      (Eventually.of_forall fun y => by simpa using hC0 y)
    simpa using (le_abs_self _).trans (by simpa using this)
  have hexp : Real.exp (-2 * ρ * s) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ s := s.2; nlinarith
  have hI0 : 0 ≤ ∫ y, carre F g g y ∂Kk F hV hμ s x := integral_nonneg (carre_nonneg F g)
  have h3 : ‖mgrad F (semi (Kk F hV hμ) s g) x‖ ^ 2 ≤ C0 := by
    refine h1.trans ?_
    calc Real.exp (-2 * ρ * s) * ∫ y, carre F g g y ∂Kk F hV hμ s x
        ≤ 1 * ∫ y, carre F g g y ∂Kk F hV hμ s x := mul_le_mul_of_nonneg_right hexp hI0
      _ ≤ C0 := by rw [one_mul]; exact hint
  have := Real.abs_le_sqrt h3
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- The canonical kernel with all the Bakry-Emery properties. -/
theorem exists_kernel_canonical (hV : MSmooth F V) [IsFiniteMeasure μ]
    (hμ : IsWeightedVolume F μ V) (hρ : 0 < ρ) (hCD : CD F ρ V) :
    ∃ Kk : ℝ≥0 → Kernel M M, KerCanonical F V μ Kk ∧ BEPointwise F V μ ρ Kk ∧
      ∀ g : M → ℝ, MSmooth F g → HasCompactSupport g →
        ∃ C : ℝ, ∀ (s : ℝ≥0) x, ‖mgrad F (semi Kk s g) x‖ ≤ C :=
  ⟨Kk F hV hμ, kerCanonical_Kk F hV hμ, bePointwise_of_CD F hV hμ hρ hCD,
    gradBound_of_CD F hV hμ hρ hCD⟩

end Main

end CutoffRigidity.Riemann.Diff
