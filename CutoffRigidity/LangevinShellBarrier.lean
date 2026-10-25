module

public import CutoffRigidity.LangevinPath
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact

/-!
# A compact-shell barrier for additive-noise Langevin paths

A path cannot cross a fixed compact shell in a short time when its driving
noise has small oscillation. The gradient bound is needed only inside the
outer ball, so no global bound on the drift is imposed.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

/-- The last crossing of an outer sphere leaves the remaining path inside
that sphere. This topological fact uses only continuity on the time interval. -/
theorem exists_last_outer_sphere_crossing {X : ℝ → E} {T outer : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn X (Icc 0 T))
    (hstart : outer ≤ ‖X 0‖) (hend : ‖X T‖ ≤ outer) :
    ∃ s ∈ Icc 0 T, ‖X s‖ = outer ∧ ∀ u ∈ Icc s T, ‖X u‖ ≤ outer := by
  let K := Icc 0 T ∩ (fun s => ‖X s‖) ⁻¹' {outer}
  have hKclosed : IsClosed K := hc.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hKcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed (fun s hs => hs.1)
  have hKne : K.Nonempty := by
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc' hT hc.norm ⟨hend, hstart⟩
    exact ⟨s, hs, hsv⟩
  obtain ⟨s, hsK, hmax⟩ := hKcompact.exists_isMaxOn hKne continuous_id.continuousOn
  have hs : s ∈ Icc 0 T := hsK.1
  have hlevel : ‖X s‖ = outer := hsK.2
  refine ⟨s, hs, hlevel, ?_⟩
  intro u hu
  by_contra hn
  have houter : outer < ‖X u‖ := lt_of_not_ge hn
  have hcu : ContinuousOn (fun t => ‖X t‖) (Icc u T) :=
    hc.norm.mono (fun t ht => ⟨hs.1.trans (hu.1.trans ht.1), ht.2⟩)
  obtain ⟨v, hv, hvlevel⟩ := intermediate_value_Icc' hu.2 hcu ⟨hend, houter.le⟩
  have hvK : v ∈ K := ⟨⟨hs.1.trans (hu.1.trans hv.1), hv.2⟩, hvlevel⟩
  have hvs : v ≤ s := hmax hvK
  have hus : u = s := le_antisymm (hv.1.trans hvs) hu.1
  rw [hus, hlevel] at houter
  exact (lt_irrefl outer) houter

/-- A continuous path with a local displacement bound cannot cross a shell
faster than the sum of its noise oscillation and integrated drift allows. -/
theorem norm_terminal_gt_of_shell_increment_bound {X : ℝ → E} {T inner outer δ M : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn X (Icc 0 T))
    (hstart : outer ≤ ‖X 0‖) (hM : 0 ≤ M) (hgap : inner < outer)
    (hshort : δ + M * T < outer - inner)
    (hinc : ∀ s ∈ Icc 0 T, (∀ u ∈ Icc s T, ‖X u‖ ≤ outer) →
      ‖X T - X s‖ ≤ δ + M * (T - s)) :
    inner < ‖X T‖ := by
  by_contra hn
  have hend : ‖X T‖ ≤ inner := le_of_not_gt hn
  obtain ⟨s, hs, hlevel, hinside⟩ := exists_last_outer_sphere_crossing hT hc hstart (hend.trans hgap.le)
  have hi := hinc s hs hinside
  have hrev := norm_sub_norm_le (X s) (X T)
  rw [norm_sub_rev, hlevel] at hrev
  have hMt : M * (T - s) ≤ M * T := mul_le_mul_of_nonneg_left (by linarith [hs.1]) hM
  linarith

section Langevin

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The exact source integral equation gives its increment from any time
inside the horizon, with no differentiability of the noise required. -/
theorem IsLangevinPathOn.increment {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {w X : ℝ → E} {x₀ : E} {T s : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (hs : s ∈ Icc 0 T) :
    X T - X s = w T - w s - ∫ u in s..T, gradient V (X u) := by
  have hg := ((differentiable_gradient_of_contDiff_two hV).continuous.comp_continuousOn hX.1)
  have hiT : IntervalIntegrable (fun u => gradient V (X u)) volume 0 T :=
    hg.intervalIntegrable_of_Icc (hs.1.trans hs.2)
  have his : IntervalIntegrable (fun u => gradient V (X u)) volume 0 s := (hg.mono (fun u hu => ⟨hu.1, hu.2.trans hs.2⟩)).intervalIntegrable_of_Icc hs.1
  have heq := intervalIntegral.integral_interval_sub_left hiT his
  rw [hX.2 T ⟨hs.1.trans hs.2, le_rfl⟩, hX.2 s hs, ← heq]
  abel

/-- Actual additive-noise Langevin solutions cannot enter the inner ball
through a compact shell faster than its bounded local drift permits. -/
theorem IsLangevinPathOn.shell_barrier {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {w X : ℝ → E} {x₀ : E} {T inner outer δ M : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (hT : 0 ≤ T)
    (hstart : outer ≤ ‖x₀‖) (hM : 0 ≤ M)
    (hgrad : ∀ x : E, ‖x‖ ≤ outer → ‖gradient V x‖ ≤ M)
    (hnoise : ∀ s ∈ Icc 0 T, ‖w T - w s‖ ≤ δ)
    (hshort : δ + M * T < outer - inner) : inner < ‖X T‖ := by
  have hδ : 0 ≤ δ := by
    simpa only [sub_self, norm_zero] using hnoise T ⟨hT, le_rfl⟩
  have hgap : inner < outer := by nlinarith
  apply norm_terminal_gt_of_shell_increment_bound hT hX.1
    (by rwa [hX.initial hT]) hM hgap hshort
  intro s hs hinside
  rw [hX.increment hV hs]
  have hi : ‖∫ u in s..T, gradient V (X u)‖ ≤ M * (T - s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := T) (f := fun u => gradient V (X u)) (C := M) (fun u hu => by
        rw [uIoc_of_le hs.2] at hu
        exact hgrad (X u) (hinside u ⟨le_of_lt hu.1, hu.2⟩))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hs.2)] using h
  exact (norm_sub_le _ _).trans (add_le_add (hnoise s hs) hi)

end Langevin

end CutoffRigidity
