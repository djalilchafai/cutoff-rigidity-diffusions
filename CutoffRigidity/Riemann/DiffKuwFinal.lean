module

public import CutoffRigidity.Riemann.DiffKuwPre
public import CutoffRigidity.Riemann.DiffKantorovichProper
public import CutoffRigidity.Riemann.DiffMoments

/-! # KUW-B, last step: from the dual-pair inequality to the contraction `W₂(K_t x, μ)²`

If `K` is a Markov semigroup of kernels with `μ.bind (K t) = μ` satisfying the *dual-pair
inequality* `∫ f dK_t(a) + ∫ g dK_t(b) ≤ e^{-2ρt} d(a,b)²` for bounded Lipschitz `f(y) + g(z) ≤
d(y,z)²`, then `W₂(K_t(x,·), μ)² ≤ e^{-2ρt} ∫ d(x,y)² dμ(y)`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal Topology BoundedContinuousFunction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Final

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

include F

/-- The dual-pair inequality for all pairs of points implies the contraction. -/
theorem contraction_of_dualPair {μ : Measure M} [IsProbabilityMeasure μ] {ρ : ℝ}
    (Kk : ℝ≥0 → Kernel M M) (hmarkov : ∀ t, IsMarkovKernel (Kk t))
    (hinv : ∀ t, μ.bind (Kk t) = μ)
    (hdual : ∀ (t : ℝ≥0) (f g : M →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x + g y ≤ (edist x y).toReal ^ 2) → ∀ a b : M,
        ∫ y, f y ∂(Kk t a) + ∫ y, g y ∂(Kk t b) ≤ Real.exp (-2 * ρ * t) * (edist a b).toReal ^ 2)
    (t : ℝ≥0) (x : M) :
    CutCur.wasserstein2 (Kk t x) μ ^ 2 ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ∫⁻ y, edist x y ^ 2 ∂μ := by
  have := hmarkov t
  have : IsProbabilityMeasure (Kk t x) := inferInstance
  set q := Real.exp (-2 * ρ * t) with hq
  have hqpos : 0 < q := Real.exp_pos _
  by_cases htop : ∫⁻ y, edist x y ^ 2 ∂μ = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hqpos).ne']; exact le_top
  have hfin : ∀ y, edist x y ≠ ⊤ := fun y => CutCur.edist_ne_top_of_connected F x y
  have hmeas : Measurable fun y => (edist x y).toReal ^ 2 :=
    (((continuous_const.edist continuous_id).measurable).ennreal_toReal).pow_const 2
  have hint : Integrable (fun y => (edist x y).toReal ^ 2) μ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by positivity)]
    have : ∀ y, ENNReal.ofReal ((edist x y).toReal ^ 2) = edist x y ^ 2 := fun y => by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin y)]
    simp_rw [this]
    exact lt_top_iff_ne_top.2 htop
  set K : ℝ := q * ∫ y, (edist x y).toReal ^ 2 ∂μ with hK
  have hKeq : ENNReal.ofReal K = ENNReal.ofReal q * ∫⁻ y, edist x y ^ 2 ∂μ := by
    rw [hK, ENNReal.ofReal_mul hqpos.le]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by positivity)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin y)]
  rw [← hKeq]
  refine wasserstein2_sq_le_of_dual_budget_manifold F (Kk t x) μ K ?_
  intro f g L J hf hg hfg
  have hgmeas : Measurable g := g.continuous.measurable
  have hgbd : ∃ C, ∀ y, ‖g y‖ ≤ C := ⟨‖g‖, fun y => g.norm_coe_le_norm y⟩
  have hgint : Integrable g (μ.bind (Kk t)) := by
    rw [hinv t]
    exact g.integrable μ
  have h1 := integral_bind_eq (Kk t) (μ := μ) hgint
  rw [hinv t] at h1
  have hmeas2 : Measurable fun b => ∫ y, g y ∂(Kk t b) :=
    (hgmeas.stronglyMeasurable.integral_kernel (κ := Kk t)).measurable
  have hint2 : Integrable (fun b => ∫ y, g y ∂(Kk t b)) μ := by
    obtain ⟨C, hC⟩ := hgbd
    refine Integrable.mono' (integrable_const C) hmeas2.aestronglyMeasurable
      (Eventually.of_forall fun b => ?_)
    calc ‖∫ y, g y ∂(Kk t b)‖ ≤ C * (Kk t b).real univ := by
          refine norm_integral_le_of_norm_le_const (Eventually.of_forall hC) |>.trans_eq ?_
          ring
      _ = C := by simp
  rw [h1]
  have h2 : ∫ y, f y ∂(Kk t x) = ∫ b, ∫ y, f y ∂(Kk t x) ∂μ := by simp
  rw [h2, ← integral_add (integrable_const _) hint2]
  calc ∫ b, (∫ y, f y ∂(Kk t x) + ∫ y, g y ∂(Kk t b)) ∂μ
      ≤ ∫ b, q * (edist x b).toReal ^ 2 ∂μ :=
        integral_mono ((integrable_const _).add hint2) (hint.const_mul q)
          (fun b => hdual t f g L J hf hg hfg x b)
    _ = K := by rw [hK, integral_const_mul]

end Final

end CutoffRigidity.Riemann.Diff
