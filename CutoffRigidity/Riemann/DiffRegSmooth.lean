module

public import CutoffRigidity.Riemann.DiffReg2

/-! # Smoothness along `⋂_k range(R^k)` and of the semigroup (workstream KER-REG)

* `smooth_rep_of_pow`: if `v = R^k w_k` for all `k` (`R = (-𝓛 + 1)⁻¹`, Friedrichs resolvent), then
  `v` has a smooth representative.
* `smooth_rep_of_pow_R`: the same with `S.R`.
* `smooth_rep_semigroup`: for `t ≠ 0`, `T_t u` has a smooth representative.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal NNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section RegSmooth

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- `R^k w` is `H^{2k}_loc` in every chart. -/
theorem chartLocSob_resolvent_pow (k : ℕ) (w : M →₂[μ] ℝ) :
    ChartLocSob F (2 * k) ((((diffFR F hV hμ).resolvent 1) ^ k) w : M → ℝ) := by
  induction k with
  | zero => simpa using chartLocSob_zero F hV hμ w
  | succ k ih =>
    have hR := diff_dirResolvent F hV hμ (lam := 1) one_pos
    have e : (((diffFR F hV hμ).resolvent 1) ^ (k + 1)) w =
        (diffFR F hV hμ).resolvent 1 ((((diffFR F hV hμ).resolvent 1) ^ k) w) := by
      rw [pow_succ']; rfl
    rw [e, show 2 * (k + 1) = 2 * k + 2 by ring]
    exact chartLocSob_step F hV hμ (diffT F hV hμ)
      (hR.mem _) _ (hR.weak _) (2 * k) ih

/-- **Smoothness along `⋂_k range(R^k)`.** -/
theorem smooth_rep_of_pow (v : M →₂[μ] ℝ)
    (h : ∀ k : ℕ, ∃ w : M →₂[μ] ℝ, v = (((diffFR F hV hμ).resolvent 1) ^ k) w) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (v : M → ℝ) =ᵐ[μ] ū := by
  refine exists_smooth_of_chartLocSob F hV hμ v fun m => ?_
  obtain ⟨w, hw⟩ := h m
  rw [hw]
  exact (chartLocSob_resolvent_pow F hV hμ m w).mono F (by omega)

/-- Same statement with `(diffFR F hV hμ).R`. -/
theorem smooth_rep_of_pow_R (v : M →₂[μ] ℝ)
    (h : ∀ k : ℕ, ∃ w : M →₂[μ] ℝ, v = (((diffFR F hV hμ).R) ^ k) w) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (v : M → ℝ) =ᵐ[μ] ū := by
  refine smooth_rep_of_pow F hV hμ v fun k => ?_
  rw [(diffFR F hV hμ).resolvent_one]
  exact h k

/-- **Smoothing of the semigroup**: for `t ≠ 0`, `T_t u` has a smooth representative. -/
theorem smooth_rep_semigroup {t : ℝ≥0} (ht : t ≠ 0) (u : M →₂[μ] ℝ) :
    ∃ ū : M → ℝ, MSmooth F ū ∧
      (((diffFR F hV hμ).semigroup t u : M →₂[μ] ℝ) : M → ℝ) =ᵐ[μ] ū := by
  refine smooth_rep_of_pow_R F hV hμ _ fun k => ?_
  obtain ⟨B, hB⟩ := (diffFR F hV hμ).semigroup_eq_pow_mul ht k
  exact ⟨B u, by rw [hB]; rfl⟩

end RegSmooth

end CutoffRigidity.Riemann.Diff

/-! ## Axiom check -/
#print axioms CutoffRigidity.Riemann.Diff.smooth_rep_of_pow
#print axioms CutoffRigidity.Riemann.Diff.smooth_rep_of_pow_R
#print axioms CutoffRigidity.Riemann.Diff.smooth_rep_semigroup
#print axioms CutoffRigidity.Riemann.Diff.regularity_step_Rn
#print axioms CutoffRigidity.Riemann.Diff.weak_solution_locSob_step
