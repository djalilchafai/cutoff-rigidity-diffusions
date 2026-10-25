module

public import CutoffRigidity.Riemann.DiffPenal
public import CutoffRigidity.Riemann.DiffRegPot

/-! # Smoothness of the penalized resolvent (workstream PENAL, P1)

`penalized_smooth`: the penalized solution `v` (for a smooth bounded potential `κ ≥ 0` and smooth
`g`) has a smooth representative solving `𝓛 v = (lam + κ) v - g` pointwise.  The elliptic
regularity with potential is the theorem `Q_smooth_of_weak_eq_pot` of the KER-REG workstream
(delivered, so no `RegPot` hypothesis is needed).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Penal1

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV hμ in
/-- Continuous functions that are a.e. `≤` are everywhere `≤` (`μ` charges open sets). -/
theorem continuous_le_of_ae_le {f g : M → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f ≤ᵐ[μ] g) : ∀ x, f x ≤ g x := by
  have := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  intro x
  by_contra hx
  rw [not_le] at hx
  have hU : IsOpen {y | g y < f y} := isOpen_lt hg hf
  have hpos : 0 < μ {y | g y < f y} := hU.measure_pos μ ⟨x, hx⟩
  have h0 : μ {y | g y < f y} = 0 := by
    have : ∀ᵐ y ∂μ, ¬ (g y < f y) := by
      filter_upwards [h] with y hy
      exact not_lt.2 hy
    simpa using ae_iff.1 this
  exact hpos.ne' h0

/-- **Smoothness of the penalized resolvent.** -/
theorem penalized_smooth {lam : ℝ} {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B)
    {g : M →₂[μ] ℝ} {g' : M → ℝ} (hg' : MSmooth F g') (hgg' : (g : M → ℝ) =ᵐ[μ] g')
    {v : M →₂[μ] ℝ} (h : IsPenal hV hμ lam κ g v) :
    ∃ v' : M → ℝ, MSmooth F v' ∧ (v : M → ℝ) =ᵐ[μ] v' ∧
      ∀ x, mgenerator F V v' x = (lam + κ x) * v' x - g' x := by
  obtain ⟨v', hv's, hvv'⟩ := Q_smooth_of_weak_eq_pot F hV hμ hκ.1 g g' hg' hgg' h.mem lam h.weak
  refine ⟨v', hv's, hvv', ?_⟩
  have hgs : MSmooth F (fun x => g' x - κ x * v' x) := hg'.sub (hκ.1.mul hv's)
  have key := pointwise_of_weak F hV hμ (lam := lam) (uL := v) (gL := g - potMul hκ v)
    (ū := v') (g' := fun x => g' x - κ x * v' x) hv's hgs hvv'
    (by
      filter_upwards [Lp.coeFn_sub g (potMul hκ v), potMul_coeFn hκ v, hgg', hvv'] with x h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, h4])
    h.mem (fun φ hφ => by
      have e := h.weak φ hφ
      rw [inner_sub_left, inner_potMul hκ]
      linarith)
  intro x
  have := key x
  linarith

end Penal1

end CutoffRigidity.Riemann.Diff
