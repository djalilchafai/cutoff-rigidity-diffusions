module

public import CutoffRigidity.Riemann.DiffForm1

/-! # The form data of `-𝓛` on `L²(μ)` (workstream DIR)

`diffFormData` packages `D = C_c^∞(M) ⊂ L²(μ)` (dense), `A = -𝓛` (symmetric, nonnegative) as a
`DirFormData`, the generic input of the Friedrichs construction (workstream FR).  Its energy is
`en (f) (g) = ∫ Γ(f,g) dμ` (`en_diffFormData`).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section FormData

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- The operator `A = -𝓛` on `D = C_c^∞(M) ⊂ L²(μ)`. -/
noncomputable def diffA : (LinearMap.range (testToL2 F μ)) →ₗ[ℝ] (M →₂[μ] ℝ) :=
  (-((testToL2 F μ).comp (testGen F hV))).comp
    (LinearEquiv.ofInjective (testToL2 F μ) (testToL2_injective F hV hμ)).symm.toLinearMap

theorem diffA_toL2 (a : testSub F M) :
    diffA F hV hμ ⟨testToL2 F μ a, a, rfl⟩ = -(testToL2 F μ (testGen F hV a)) := by
  have : (⟨testToL2 F μ a, a, rfl⟩ : LinearMap.range (testToL2 F μ)) =
      LinearEquiv.ofInjective (testToL2 F μ) (testToL2_injective F hV hμ) a := rfl
  simp only [diffA, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearEquiv.symm_apply_apply,
    LinearMap.neg_apply]

theorem carre_comm (f g : M → ℝ) (x : M) : carre F f g x = carre F g f x := by
  simp only [carre, real_inner_comm]

/-- **Form data of `-𝓛` on `L²(μ)`**: dense domain `C_c^∞(M)`, symmetric and nonnegative. -/
noncomputable def diffFormData : DirFormData (M →₂[μ] ℝ) where
  D := LinearMap.range (testToL2 F μ)
  dense := by
    have := dense_test (F := F) (M := M) (μ := μ)
    exact this
  A := diffA F hV hμ
  symm := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    show inner ℝ (diffA F hV hμ ⟨testToL2 F μ a, a, rfl⟩) (testToL2 F μ b) =
      inner ℝ (testToL2 F μ a) (diffA F hV hμ ⟨testToL2 F μ b, b, rfl⟩)
    rw [diffA_toL2, diffA_toL2, real_inner_comm, inner_testGen F hV hμ b a,
      inner_testGen F hV hμ a b]
    exact integral_congr_ae (Eventually.of_forall fun x => carre_comm F _ _ x)
  nonneg := by
    rintro ⟨_, a, rfl⟩
    show 0 ≤ inner ℝ (diffA F hV hμ ⟨testToL2 F μ a, a, rfl⟩) (testToL2 F μ a)
    rw [diffA_toL2, real_inner_comm, inner_testGen F hV hμ a a]
    exact integral_nonneg fun x => carre_nonneg F _ x

/-- The energy of the form data of `-𝓛` is `∫ Γ(f,g) dμ`. -/
theorem en_diffFormData (a b : testSub F M) :
    (diffFormData F hV hμ).en ⟨testToL2 F μ a, a, rfl⟩ ⟨testToL2 F μ b, b, rfl⟩ =
      ∫ x, carre F (a : M → ℝ) (b : M → ℝ) x ∂μ := by
  show inner ℝ (diffA F hV hμ ⟨testToL2 F μ a, a, rfl⟩) (testToL2 F μ b) = _
  rw [diffA_toL2, real_inner_comm, inner_testGen F hV hμ b a]
  exact integral_congr_ae (Eventually.of_forall fun x => carre_comm F _ _ x)

end FormData

end CutoffRigidity.Riemann.Diff
