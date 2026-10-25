module

public import CutoffRigidity.Riemann.DiffReg8

/-! # Smooth potentials and interior sup estimate on the manifold (workstream KER-REG)

* `Q_smooth_of_weak_eq_pot`, `Q_smooth_of_weak_eq_pot_bdd` (in `DiffReg4`).
* `interior_sup_estimate_manifold`: interior sup estimate for smooth solutions of `𝓛 w = lam w` on `W`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section SupFinal

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV hμ in
/-- **Interior sup estimate on the manifold.**  For `W` open, `B ⊆ W` compact and `lam`, there is `C`
such that every smooth `w` with `𝓛 w = lam w` on `W` and `w ∈ L²(μ|W)` satisfies
`|w x| ≤ C (∫_W w² dμ)^{1/2}` on `B`.  (The hypothesis `MemLp w 2 (μ.restrict W)` is necessary since
Bochner integrals of non-integrable functions are junk `0`.) -/
theorem interior_sup_estimate_manifold {W : Set M} (hW : IsOpen W) {B : Set M} (hB : IsCompact B)
    (hBW : B ⊆ W) (lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : M → ℝ, MSmooth F w → (∀ y ∈ W, mgenerator F V w y = lam * w y) →
      MemLp w 2 (μ.restrict W) →
      ∀ x ∈ B, |w x| ≤ C * (∫ y in W, w y ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  classical
  have hloc := fun x (hx : x ∈ B) => local_sup_bound F hV hμ hW lam (hBW hx)
  choose! N D hNo hxN hD hbound using hloc
  obtain ⟨t, htB, hcov⟩ := hB.elim_nhds_subcover N (fun x hx => (hNo x hx).mem_nhds (hxN x hx))
  refine ⟨∑ x ∈ t, D x, Finset.sum_nonneg fun x hx => hD x (htB x hx), fun w hw hgen hmem x hx => ?_⟩
  have hint : Integrable (fun y => w y ^ 2) (μ.restrict W) :=
    (memLp_two_iff_integrable_sq hw.continuous.aestronglyMeasurable).1 hmem
  obtain ⟨x', hx't, hxN'⟩ := Set.mem_iUnion₂.1 (hcov hx)
  have h1 := hbound x' (htB x' hx't) w hw hgen hint x hxN'
  refine h1.trans ?_
  have hJ : 0 ≤ (∫ y in W, w y ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg
    (setIntegral_nonneg hW.measurableSet fun y _ => sq_nonneg _) _
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := D) (fun y hy => hD y (htB y hy)) hx't) hJ

end SupFinal

end CutoffRigidity.Riemann.Diff

#print axioms CutoffRigidity.Riemann.Diff.Q_smooth_of_weak_eq_pot
#print axioms CutoffRigidity.Riemann.Diff.interior_sup_estimate_manifold
