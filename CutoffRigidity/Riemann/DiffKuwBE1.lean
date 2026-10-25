module

public import CutoffRigidity.Riemann.DiffKer
public import CutoffRigidity.Riemann.DiffKuwPre
public import CutoffRigidity.Riemann.DiffMarkov2
public import CutoffRigidity.Riemann.EigenLinear
public import CutoffRigidity.Riemann.WeightedPointwise

/-! # KUW-BE1: semigroup of bounded continuous functions via `Tc` -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section BE1

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem memLp_of_bdd_cont {ψ : M → ℝ} {B : ℝ} (hc : Continuous ψ) (hB : ∀ x, |ψ x| ≤ B) :
    MemLp ψ 2 μ :=
  MemLp.of_bound hc.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hB x)

/-- **(B0)** the semigroup of a bounded continuous function is `Tc` of its `L²` class. -/
theorem semi_eq_Tc_of_lip {ψ : M → ℝ} {B : ℝ} (hc : Continuous ψ) (hB : ∀ x, |ψ x| ≤ B)
    {t : ℝ≥0} (ht : t ≠ 0) :
    ∃ u : M →₂[μ] ℝ, (u : M → ℝ) =ᵐ[μ] ψ ∧
      ∀ x, semi (Kk F hV hμ) t ψ x = Tc F hV hμ t u x := by
  have hm := memLp_of_bdd_cont (μ := μ) hc hB
  refine ⟨hm.toLp ψ, hm.coeFn_toLp, fun x => ?_⟩
  have h := (kmeas_integral F hV hμ ht x (hm.toLp ψ)).2
  unfold semi
  rw [Kk_apply_of_ne F hV hμ ht, ← h]
  refine integral_congr_ae ?_
  exact (withDensity_absolutelyContinuous μ _).ae_le (hm.coeFn_toLp).symm

theorem semi_smooth_of_lip {ψ : M → ℝ} {B : ℝ} (hc : Continuous ψ) (hB : ∀ x, |ψ x| ≤ B)
    {t : ℝ≥0} (ht : t ≠ 0) : MSmooth F (semi (Kk F hV hμ) t ψ) := by
  obtain ⟨u, -, hu⟩ := semi_eq_Tc_of_lip F hV hμ hc hB ht
  have : semi (Kk F hV hμ) t ψ = Tc F hV hμ t u := funext hu
  rw [this]; exact Tc_smooth F hV hμ ht u

/-- Zeroth order stability. -/
theorem integrable_Kk_of_bdd {ψ : M → ℝ} {B : ℝ} (hc : Continuous ψ) (hB : ∀ x, |ψ x| ≤ B)
    (t : ℝ≥0) (x : M) : Integrable ψ (Kk F hV hμ t x) := by
  haveI := Kk_markov F hV hμ t
  exact Integrable.of_bound hc.aestronglyMeasurable B (Filter.Eventually.of_forall fun y => by
    simpa [Real.norm_eq_abs] using hB y)

theorem semi_sub_le {ψ₁ ψ₂ : M → ℝ} {B₁ B₂ δ : ℝ} (hc₁ : Continuous ψ₁) (hc₂ : Continuous ψ₂)
    (hB₁ : ∀ x, |ψ₁ x| ≤ B₁) (hB₂ : ∀ x, |ψ₂ x| ≤ B₂) (t : ℝ≥0)
    (h : ∀ y, |ψ₁ y - ψ₂ y| ≤ δ) (x : M) :
    |semi (Kk F hV hμ) t ψ₁ x - semi (Kk F hV hμ) t ψ₂ x| ≤ δ := by
  haveI := Kk_markov F hV hμ t
  have hi1 := integrable_Kk_of_bdd F hV hμ hc₁ hB₁ t
  have hi2 := integrable_Kk_of_bdd F hV hμ hc₂ hB₂ t
  unfold semi
  rw [← integral_sub (hi1 x) (hi2 x)]
  calc |∫ y, (ψ₁ y - ψ₂ y) ∂(Kk F hV hμ t x)| ≤ ∫ y, |ψ₁ y - ψ₂ y| ∂(Kk F hV hμ t x) := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := Kk F hV hμ t x)
          (fun y => ψ₁ y - ψ₂ y)
    _ ≤ ∫ y, δ ∂(Kk F hV hμ t x) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall h)
    _ = δ := by simp

/-- **(B1)** gradient stability. -/
theorem grad_semi_sub_le {t : ℝ≥0} (ht : t ≠ 0) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ₁ ψ₂ : M → ℝ) (B₁ B₂ : ℝ), Continuous ψ₁ → Continuous ψ₂ →
      (∀ x, |ψ₁ x| ≤ B₁) → (∀ x, |ψ₂ x| ≤ B₂) → ∀ δ : ℝ, 0 ≤ δ → (∀ y, |ψ₁ y - ψ₂ y| ≤ δ) →
      ∀ x ∈ K, ‖mgrad F (semi (Kk F hV hμ) t ψ₁) x - mgrad F (semi (Kk F hV hμ) t ψ₂) x‖
        ≤ C * δ := by
  obtain ⟨C0, hC0⟩ := Tc_grad_bound F hV hμ ht hK
  refine ⟨|C0| * (measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0), by positivity,
    fun ψ₁ ψ₂ B₁ B₂ hc₁ hc₂ hB₁ hB₂ δ hδ h x hx => ?_⟩
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
  have hn : ‖u₁ - u₂‖ ≤ (measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) * δ := by
    refine Lp.norm_le_of_ae_bound hδ ?_
    filter_upwards [Lp.coeFn_sub u₁ u₂, hu₁ae, hu₂ae] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]; exact h y
  calc C0 * ‖u₁ - u₂‖ ≤ |C0| * ‖u₁ - u₂‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |C0| * ((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) * δ) :=
        mul_le_mul_of_nonneg_left hn (abs_nonneg _)
    _ = _ := by ring

end BE1

end CutoffRigidity.Riemann.Diff
