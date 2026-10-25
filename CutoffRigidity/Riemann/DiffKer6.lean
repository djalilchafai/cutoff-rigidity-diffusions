module

public import CutoffRigidity.Riemann.DiffKer5
public import CutoffRigidity.Riemann.DiffAPI

/-! # `semi Kk t f = T_t f`, generator commutation, time derivative (KER, A6) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Semi

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem semi_Kk_eq_Tc {t : ℝ≥0} (ht : t ≠ 0) (f : testSub F M) (x : M) :
    semi (Kk F hV hμ) t (f : M → ℝ) x = Tc F hV hμ t (testToL2 F μ f) x := by
  have h := (kmeas_integral F hV hμ ht x (testToL2 F μ f)).2
  unfold semi
  rw [Kk_apply_of_ne F hV hμ ht, ← h]
  refine integral_congr_ae ?_
  exact (withDensity_absolutelyContinuous μ _).ae_le (coeFn_testToL2 F μ f).symm

theorem semi_Kk_zero (g : M → ℝ) : semi (Kk F hV hμ) 0 g = g := by
  funext x
  simp [semi, Kk_zero, Kernel.id_apply]

theorem semigroup_comm_R (t : ℝ≥0) :
    Commute ((diffFR F hV hμ).R) ((diffFR F hV hμ).semigroup t) := by
  have h := (diffFR F hV hμ).R_unitOp.commute_rcfc id (hfun t)
  rw [(diffFR F hV hμ).R_unitOp.rcfc_id] at h
  exact h

/-- `f = R (f - 𝓛 f)` for test functions. -/
theorem testFun_eq_R (f : testSub F M) :
    (diffFR F hV hμ).R (testToL2 F μ f - testToL2 F μ (testGen F hV f)) = testToL2 F μ f := by
  have h := (diffFR F hV hμ).resolvent_apply_D one_pos ⟨testToL2 F μ f, f, rfl⟩
  have hA : (diffFR F hV hμ).A ⟨testToL2 F μ f, f, rfl⟩ = -(testToL2 F μ (testGen F hV f)) :=
    diffA_toL2 F hV hμ f
  rw [(diffFR F hV hμ).resolvent_one, hA, one_smul] at h
  simpa [sub_eq_add_neg] using h

/-- `𝓛 (T_t f) = T_t (𝓛 f)` pointwise, for `t > 0` and test functions. -/
theorem Tc_generator {t : ℝ≥0} (ht : t ≠ 0) (f : testSub F M) (x : M) :
    mgenerator F V (Tc F hV hμ t (testToL2 F μ f)) x =
      Tc F hV hμ t (testToL2 F μ (testGen F hV f)) x := by
  set S := diffFR F hV hμ with hS
  set h := testToL2 F μ f - testToL2 F μ (testGen F hV f) with hh
  have hR : S.R (S.semigroup t h) = S.semigroup t (testToL2 F μ f) := by
    have := congrArg (fun T => T h) (semigroup_comm_R F hV hμ t).eq
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [this, hh, testFun_eq_R F hV hμ f]
  have hres := diff_dirResolvent F hV hμ (one_pos : (0:ℝ) < 1)
  rw [S.resolvent_one] at hres
  have := pointwise_of_weak F hV hμ (lam := 1) (uL := S.R (S.semigroup t h))
    (gL := S.semigroup t h) (ū := Tc F hV hμ t (testToL2 F μ f))
    (g' := Tc F hV hμ t h) (Tc_smooth F hV hμ ht _) (Tc_smooth F hV hμ ht _)
    (by rw [hR]; exact Tc_ae F hV hμ ht _) (Tc_ae F hV hμ ht _) (hres.mem _)
    (fun φ hφ => hres.weak _ φ hφ) x
  rw [hh, Tc_sub] at this
  simp only [Pi.sub_apply, one_mul] at this
  linarith

end Semi

end CutoffRigidity.Riemann.Diff
