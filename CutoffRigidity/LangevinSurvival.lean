module
public import CutoffRigidity.LangevinLocalizedLaw
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Genuine time-dependent compact-ball survival event

The prefix-survival event is closed using continuous initial/noise evaluation
at fixed times and continuity of actual trajectories at their terminal time.
This event depends only on the path prefix, not on future survival.
-/
public section
namespace CutoffRigidity
open MeasureTheory Set Metric Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinSurvivalSet (V : E → ℝ) (R : ℝ) : Set (ℝ × (E × C(ℝ, E))) :=
  {q | 0 ≤ q.1 ∧ q.2 ∈ langevinStayingInputSet V q.1 R}

set_option maxHeartbeats 700000 in
/-- The actual prefix-survival event is closed in time, initial point and
continuous driving path. -/
theorem isClosed_langevinSurvivalSet
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (R : ℝ) :
    IsClosed (langevinSurvivalSet V R) := by
  let Q := fun r : NNReal =>
    ((fun q : ℝ × (E × C(ℝ, E)) => q.1) ⁻¹' Iic (r : ℝ)) ∪
      ((fun q : ℝ × (E × C(ℝ, E)) => langevinSolution V q.2.2 q.2.1 r) ⁻¹' closedBall (0 : E) R)
  have heq : langevinSurvivalSet V R =
      ((fun q : ℝ × (E × C(ℝ, E)) => q.1) ⁻¹' Ici 0) ∩
      ((fun q : ℝ × (E × C(ℝ, E)) => q.2.1) ⁻¹' closedBall (0 : E) R) ∩ ⋂ r : NNReal, Q r := by
    ext q
    constructor
    · rintro ⟨ht, hstay⟩
      refine ⟨⟨ht, ?_⟩, ?_⟩
      · have h0 := hstay (show (0 : ℝ) ∈ Icc 0 q.1 from ⟨le_rfl, ht⟩)
        rw [langevinSolution_initial hV rate hrate hHess q.2.2.continuous q.2.1] at h0
        exact h0
      · apply mem_iInter.mpr
        intro r
        by_cases hr : q.1 ≤ (r : ℝ)
        · exact Or.inl hr
        · exact Or.inr (hstay ⟨r.property, (lt_of_not_ge hr).le⟩)
    · rintro ⟨⟨ht, hinit⟩, hq⟩
      have hstrict (r : ℝ) (hr0 : 0 ≤ r) (hrt : r < q.1) :
          langevinSolution V q.2.2 q.2.1 r ∈ closedBall (0 : E) R := by
        have hh := mem_iInter.mp hq (⟨r, hr0⟩ : NNReal)
        exact hh.resolve_left (not_le.mpr hrt)
      refine ⟨ht, ?_⟩
      intro r hr
      by_cases hrt : r < q.1
      · exact hstrict r hr.1 hrt
      · have hrt' : r = q.1 := le_antisymm hr.2 (le_of_not_gt hrt)
        subst r
        by_cases ht0 : q.1 = 0
        · rw [ht0, langevinSolution_initial hV rate hrate hHess q.2.2.continuous q.2.1]
          exact hinit
        · have htpos : 0 < q.1 := lt_of_le_of_ne ht (Ne.symm ht0)
          let a : ℕ → ℝ := fun n => (1 - 1 / ((n : ℝ) + 1)) * q.1
          have ha0 (n : ℕ) : 0 ≤ a n := by
            have hn : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
            exact mul_nonneg (sub_nonneg.mpr hn) ht
          have halt (n : ℕ) : a n < q.1 := by
            have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            dsimp [a]
            nlinarith
          have halim : Tendsto a atTop (𝓝 q.1) := by
            have hh : Tendsto a atTop (𝓝 ((1 - 0) * q.1)) := (tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const q.1
            simpa only [sub_zero, one_mul] using hh
          have hp := langevinSolution_continuousOn hV rate hrate hHess q.2.2.continuous q.2.1
          have hlim : Tendsto (fun n => langevinSolution V q.2.2 q.2.1 (a n)) atTop
              (𝓝 (langevinSolution V q.2.2 q.2.1 q.1)) :=
            (hp q.1 ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨halim, Eventually.of_forall ha0⟩)
          exact isClosed_closedBall.mem_of_tendsto hlim (Eventually.of_forall (fun n => hstrict _ (ha0 n) (halt n)))
  rw [heq]
  apply IsClosed.inter
  · exact (isClosed_Ici.preimage continuous_fst).inter
      (isClosed_closedBall.preimage (continuous_fst.comp continuous_snd))
  · apply isClosed_iInter
    intro r
    exact (isClosed_Iic.preimage continuous_fst).union
      (isClosed_closedBall.preimage ((langevinSolution_evaluation_continuous hV rate hrate hHess r.property).comp continuous_snd))

end CutoffRigidity
