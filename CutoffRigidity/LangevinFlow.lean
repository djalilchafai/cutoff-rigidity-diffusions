module

public import CutoffRigidity.LangevinSolution

/-!
# Restarting the actual Langevin solution

The integral equation restarts at a forward time with the shifted driving
path. Pathwise uniqueness then gives the exact cocycle identity. This is
the deterministic input for the Markov property with independent Brownian
increments; it does not assume a transition semigroup.
-/

public section

open Set MeasureTheory

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem IsLangevinPathOn.shift {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {w X : ℝ → E} {x₀ : E} {s T : ℝ} (hs : 0 ≤ s) (hT : 0 ≤ T)
    (hX : IsLangevinPathOn V w x₀ X (s + T)) :
    IsLangevinPathOn V (fun u => w (s + u)) (X s) (fun u => X (s + u)) T := by
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  have hG : ContinuousOn (fun r => gradient V (X r)) (Icc 0 (s + T)) :=
    hg.comp_continuousOn hX.1
  constructor
  · exact hX.1.comp (continuous_const.add continuous_id).continuousOn
      (fun u hu => ⟨add_nonneg hs hu.1, by linarith [hu.2]⟩)
  · intro u hu
    have hi0 : IntervalIntegrable (fun r => gradient V (X r)) volume 0 s :=
      (hG.mono (fun r hr => ⟨hr.1, hr.2.trans (le_add_of_nonneg_right hT)⟩)).intervalIntegrable_of_Icc hs
    have hi1 : IntervalIntegrable (fun r => gradient V (X r)) volume s (s + u) :=
      (hG.mono (fun r hr => ⟨hs.trans hr.1, by linarith [hr.2, hu.2]⟩)).intervalIntegrable_of_Icc
        (le_add_of_nonneg_right hu.1)
    have hi := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
    have hchange : (∫ r in 0..u, gradient V (X (s + r))) =
        ∫ r in s..s + u, gradient V (X r) := by
      simpa only [add_zero] using intervalIntegral.integral_comp_add_left
        (f := fun r => gradient V (X r)) (a := 0) (b := u) s
    change X (s + u) = X s + (w (s + u) - w (s + 0)) -
      ∫ r in 0..u, gradient V (X (s + r))
    rw [hchange, hX.2 (s + u) ⟨add_nonneg hs hu.1, by linarith [hu.2]⟩,
      hX.2 s ⟨hs, le_add_of_nonneg_right hT⟩, ← hi]
    simp only [add_zero]
    abel

/-- The exact pathwise restart identity; Brownian independence is not used. -/
theorem langevinSolution_cocycle [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x₀ : E) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    langevinSolution V w x₀ (s + t) =
      langevinSolution V (fun u => w (s + u)) (langevinSolution V w x₀ s) t := by
  have hX := langevinSolution_isLangevinPathOn hV rate hrate hHess hw x₀
    (add_nonneg hs ht)
  have hshift := hX.shift hV hs ht
  have hY := langevinSolution_isLangevinPathOn (w := fun u => w (s + u)) hV rate hrate hHess
    (hw.comp (continuous_const.add continuous_id)) (langevinSolution V w x₀ s) ht
  exact langevin_path_unique hV rate hHess hshift hY ⟨ht, le_rfl⟩

end CutoffRigidity
