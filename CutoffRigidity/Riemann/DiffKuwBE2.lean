module

public import CutoffRigidity.Riemann.DiffKuwBE1

/-! # KUW-BE2: L2 stability of the gradient of the semigroup -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section BE2

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem norm_sq_L2 (u : M →₂[μ] ℝ) : ‖u‖ ^ 2 = ∫ a, (u a) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp [sq]

/-- `L²` stability of the gradient of the semigroup of bounded continuous functions. -/
theorem grad_semi_sub_le_L2 {t : ℝ≥0} (ht : t ≠ 0) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ₁ ψ₂ : M → ℝ) (B₁ B₂ : ℝ), Continuous ψ₁ → Continuous ψ₂ →
      (∀ x, |ψ₁ x| ≤ B₁) → (∀ x, |ψ₂ x| ≤ B₂) →
      ∀ x ∈ K, ‖mgrad F (semi (Kk F hV hμ) t ψ₁) x - mgrad F (semi (Kk F hV hμ) t ψ₂) x‖
        ≤ C * Real.sqrt (∫ y, (ψ₁ y - ψ₂ y) ^ 2 ∂μ) := by
  obtain ⟨C0, hC0⟩ := Tc_grad_bound F hV hμ ht hK
  refine ⟨|C0|, abs_nonneg _, fun ψ₁ ψ₂ B₁ B₂ hc₁ hc₂ hB₁ hB₂ x hx => ?_⟩
  obtain ⟨u₁, hu₁ae, hu₁⟩ := semi_eq_Tc_of_lip F hV hμ hc₁ hB₁ ht
  obtain ⟨u₂, hu₂ae, hu₂⟩ := semi_eq_Tc_of_lip F hV hμ hc₂ hB₂ ht
  have e1 : semi (Kk F hV hμ) t ψ₁ = Tc F hV hμ t u₁ := funext hu₁
  have e2 : semi (Kk F hV hμ) t ψ₂ = Tc F hV hμ t u₂ := funext hu₂
  have hs : Tc F hV hμ t (u₁ - u₂) = fun y => Tc F hV hμ t u₁ y - Tc F hV hμ t u₂ y := by
    funext y; rw [Tc_sub]; rfl
  have hg : mgrad F (Tc F hV hμ t (u₁ - u₂)) x =
      mgrad F (Tc F hV hμ t u₁) x - mgrad F (Tc F hV hμ t u₂) x := by
    rw [hs]; exact mgrad_sub' F (Tc_smooth F hV hμ ht u₁) (Tc_smooth F hV hμ ht u₂) x
  rw [e1, e2, ← hg]
  refine (hC0 _ x hx).trans ?_
  have hn : ‖u₁ - u₂‖ = Real.sqrt (∫ y, (ψ₁ y - ψ₂ y) ^ 2 ∂μ) := by
    have h2 := norm_sq_L2 (u₁ - u₂)
    have h3 : ∫ a, ((u₁ - u₂) a) ^ 2 ∂μ = ∫ y, (ψ₁ y - ψ₂ y) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub u₁ u₂, hu₁ae, hu₂ae] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    rw [h3] at h2
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [hn]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)

/-- If `f n → ψ` pointwise with a uniform bound, then `mgrad (semi t (f n)) x → mgrad (semi t ψ) x`. -/
theorem tendsto_grad_semi {t : ℝ≥0} (ht : t ≠ 0) (x : M) {f : ℕ → M → ℝ} {ψ : M → ℝ} {D : ℝ}
    (hfc : ∀ n, Continuous (f n)) (hψc : Continuous ψ) (hfB : ∀ n y, |f n y| ≤ D)
    (hψB : ∀ y, |ψ y| ≤ D) (hlim : ∀ y, Tendsto (fun n => f n y) atTop (𝓝 (ψ y))) :
    Tendsto (fun n => mgrad F (semi (Kk F hV hμ) t (f n)) x) atTop
      (𝓝 (mgrad F (semi (Kk F hV hμ) t ψ) x)) := by
  obtain ⟨C, hC0, hC⟩ := grad_semi_sub_le_L2 F hV hμ ht (isCompact_singleton (x := x))
  have hint : Tendsto (fun n => ∫ y, (f n y - ψ y) ^ 2 ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun n y => (f n y - ψ y) ^ 2)
      (f := fun _ => (0 : ℝ)) (bound := fun _ => (2 * D) ^ 2)
      (fun n => ((hfc n).sub hψc).pow 2 |>.aestronglyMeasurable) (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_pow]
        have : |f n y - ψ y| ≤ 2 * D := by
          have h1 := abs_le.1 (hfB n y); have h2 := abs_le.1 (hψB y)
          rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2)
      (Filter.Eventually.of_forall fun y => by
        have := ((hlim y).sub_const (ψ y)).pow 2
        simpa using this)
    simpa using this
  have hs : Tendsto (fun n => C * Real.sqrt (∫ y, (f n y - ψ y) ^ 2 ∂μ)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hint
    simpa using this.const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hs
  exact hC (f n) ψ D D (hfc n) hψc (hfB n) hψB x rfl

end BE2

end CutoffRigidity.Riemann.Diff
