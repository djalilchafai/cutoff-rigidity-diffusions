module

public import CutoffRigidity.Riemann.DiffKerGrad1

/-! # Local gradient bounds on the manifold (workstream KER-GRAD)

Gradient analogue of `local_bound_of_smooth_rep`, and the corollary for the semigroup `Tc`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Grad2

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV hμ

/-- Gradient bound near a point. -/
theorem local_grad_bound_nhds (B : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ))
    (hB : ∀ u, ∃ ū : M → ℝ, MSmooth F ū ∧ (B u : M → ℝ) =ᵐ[μ] ū) (x₀ : M) :
    ∃ N ∈ 𝓝 x₀, ∃ C : ℝ, ∀ (u : M →₂[μ] ℝ) (ū : M → ℝ), MSmooth F ū →
      (B u : M → ℝ) =ᵐ[μ] ū → ∀ x ∈ N, ‖mgrad F ū x‖ ≤ C * ‖u‖ := by
  set φ := chartAt F x₀ with hφ
  have hx₀ : φ x₀ ∈ φ.target := mem_chart_target F x₀
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 φ.open_target _ hx₀
  have hcb : Metric.closedBall (φ x₀) (r / 2) ⊆ φ.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrT
  set W : Set F := Metric.ball (φ x₀) (r / 2) with hW
  have hWo : IsOpen W := Metric.isOpen_ball
  have hcl : closure W ⊆ Metric.closedBall (φ x₀) (r / 2) := Metric.closure_ball_subset_closedBall
  have hclc : IsCompact (closure W) :=
    (isCompact_closedBall (φ x₀) (r / 2)).of_isClosed_subset isClosed_closure hcl
  have hWT : closure W ⊆ φ.target := hcl.trans hcb
  obtain ⟨C, hC⟩ := chart_deriv_bound F hV hμ B hB x₀ hWo hclc hWT
  obtain ⟨A, hA⟩ := hclc.exists_bound_of_continuousOn
    (((contDiffOn_chartCoeff F x₀).continuousOn).mono hWT)
  have hNo : IsOpen (φ.source ∩ φ ⁻¹' W) :=
    φ.continuousOn.isOpen_inter_preimage φ.open_source hWo
  have hxN : x₀ ∈ φ.source ∩ φ ⁻¹' W :=
    ⟨mem_chart_source F x₀, Metric.mem_ball_self (by linarith)⟩
  refine ⟨_, hNo.mem_nhds hxN, Real.sqrt |A| * |C|, fun u ū hū hūe x hx => ?_⟩
  have hz : φ x ∈ W := hx.2
  have hxe : φ.symm (φ x) = x := φ.left_inv hx.1
  have hg := hC u ū hū hūe _ hz
  have hg' : ‖gradient (ū ∘ φ.symm) (φ x)‖ ≤ |C| * ‖u‖ :=
    hg.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hform := carre_chart_formula F x₀ (hWT (subset_closure hz)) hū hū
  rw [hxe] at hform
  have hsq : ‖mgrad F ū x‖ ^ 2 ≤ |A| * (|C| * ‖u‖) ^ 2 := by
    rw [← carre_self_eq, hform]
    set g := gradient (ū ∘ φ.symm) (φ x)
    set a := chartCoeff F x₀ (φ x)
    have h1 : inner ℝ g (a g) ≤ ‖g‖ * ‖a g‖ := real_inner_le_norm _ _
    have h2 : ‖a g‖ ≤ ‖a‖ * ‖g‖ := a.le_opNorm g
    have h3 : ‖a‖ ≤ |A| := (hA _ (subset_closure hz)).trans (le_abs_self _)
    have h4 : ‖g‖ ≤ |C| * ‖u‖ := hg'
    have hn := norm_nonneg g
    calc inner ℝ g (a g) ≤ ‖g‖ * (‖a‖ * ‖g‖) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hn)
      _ ≤ ‖g‖ * (|A| * ‖g‖) := by gcongr
      _ = |A| * ‖g‖ ^ 2 := by ring
      _ ≤ |A| * (|C| * ‖u‖) ^ 2 := by gcongr
  have hnn : 0 ≤ Real.sqrt |A| * |C| * ‖u‖ := by positivity
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hnn (two_ne_zero)).1 ?_
  calc ‖mgrad F ū x‖ ^ 2 ≤ |A| * (|C| * ‖u‖) ^ 2 := hsq
    _ = (Real.sqrt |A| * |C| * ‖u‖) ^ 2 := by
      have := Real.sq_sqrt (abs_nonneg A)
      calc |A| * (|C| * ‖u‖) ^ 2 = (√|A|) ^ 2 * (|C| * ‖u‖) ^ 2 := by rw [this]
        _ = _ := by ring

/-- **Local gradient bound** for operators with smooth values. -/
theorem local_grad_bound_of_smooth_rep (B : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ))
    (hB : ∀ u, ∃ ū : M → ℝ, MSmooth F ū ∧ (B u : M → ℝ) =ᵐ[μ] ū)
    {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ (u : M →₂[μ] ℝ) (ū : M → ℝ), MSmooth F ū → (B u : M → ℝ) =ᵐ[μ] ū →
      ∀ x ∈ K, ‖mgrad F ū x‖ ≤ C * ‖u‖ := by
  refine hK.induction_on (p := fun s => ∃ C : ℝ, ∀ (u : M →₂[μ] ℝ) (ū : M → ℝ), MSmooth F ū →
      (B u : M → ℝ) =ᵐ[μ] ū → ∀ x ∈ s, ‖mgrad F ū x‖ ≤ C * ‖u‖) ?_ ?_ ?_ ?_
  · exact ⟨0, fun u ū _ _ x hx => absurd hx (notMem_empty x)⟩
  · rintro s t hst ⟨C, hC⟩
    exact ⟨C, fun u ū h1 h2 x hx => hC u ū h1 h2 x (hst hx)⟩
  · rintro s t ⟨C1, h1⟩ ⟨C2, h2⟩
    refine ⟨max C1 C2, fun u ū hū hūe x hx => ?_⟩
    have hn := norm_nonneg u
    rcases hx with hx | hx
    · exact (h1 u ū hū hūe x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn)
    · exact (h2 u ū hū hūe x hx).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hn)
  · intro x _
    obtain ⟨N, hN, C, hC⟩ := local_grad_bound_nhds F hV hμ B hB x
    exact ⟨N, mem_nhdsWithin_of_mem_nhds hN, C, hC⟩

/-- Gradient bound for the continuous representative of the semigroup. -/
theorem Tc_grad_bound {t : ℝ≥0} (ht : t ≠ 0) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ u : M →₂[μ] ℝ, ∀ x ∈ K, ‖mgrad F (Tc F hV hμ t u) x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := local_grad_bound_of_smooth_rep F hV hμ ((diffFR F hV hμ).semigroup t)
    (fun u => ⟨_, Tc_smooth F hV hμ ht u, Tc_ae F hV hμ ht u⟩) hK
  exact ⟨C, fun u x hx => hC u _ (Tc_smooth F hV hμ ht u) (Tc_ae F hV hμ ht u) x hx⟩

end Grad2

end CutoffRigidity.Riemann.Diff
