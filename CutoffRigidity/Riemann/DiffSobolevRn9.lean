module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Limits of smooth functions that are Cauchy in `C^j`
-/

@[expose] public section

open Filter Topology
open scoped ContDiff

namespace CutoffRigidity.Riemann.Diff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem exists_uniform_limit_aux (f : ℕ → E → F) (hf : ∀ n, Continuous (f n))
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N, ∀ x, ‖f n x - f n' x‖ ≤ ε) :
    ∃ g : E → F, Continuous g ∧ TendstoUniformly f g atTop := by
  have hp : ∀ x, ∃ y, Tendsto (fun n => f n x) atTop (𝓝 y) := by
    intro x
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (by positivity)
    exact ⟨N, fun n hn => by
      have := hN n hn N le_rfl x
      rw [dist_eq_norm]; linarith⟩
  choose g hg using hp
  have hu : TendstoUniformly f g atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have : ‖f n x - g x‖ ≤ ε / 2 := by
      refine le_of_tendsto (((continuous_const.sub continuous_id).norm.tendsto _).comp (hg x)) ?_
      filter_upwards [eventually_ge_atTop N] with m hm
      exact hN n hn m hm x
    rw [dist_comm, dist_eq_norm]; linarith
  exact ⟨g, hu.continuous (Eventually.of_forall hf).frequently, hu⟩

theorem exists_contDiff_limit_aux' (j : ℕ) (f : ℕ → E → F) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hc : ∀ i ≤ j, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N, ∀ x,
      ‖iteratedFDeriv ℝ i (f n) x - iteratedFDeriv ℝ i (f n') x‖ ≤ ε) :
    ∃ g : E → F, ContDiff ℝ j g ∧ ∀ i ≤ j, ∀ x, Tendsto (fun n => iteratedFDeriv ℝ i (f n) x)
      atTop (𝓝 (iteratedFDeriv ℝ i g x)) := by
  have hp : ∀ i : ℕ, ∃ p : E → ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F, i ≤ j →
      Continuous p ∧ TendstoUniformly (fun n => iteratedFDeriv ℝ i (f n)) p atTop := by
    intro i
    by_cases hi : i ≤ j
    · obtain ⟨p, hp1, hp2⟩ := exists_uniform_limit_aux
        (fun n => iteratedFDeriv ℝ i (f n))
        (fun n => (hf n).continuous_iteratedFDeriv (by exact_mod_cast le_top))
        (hc i hi)
      exact ⟨p, fun _ => ⟨hp1, hp2⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose p hp using hp
  let q : E → FormalMultilinearSeries ℝ E F := fun x i => p i x
  let g : E → F := fun x => continuousMultilinearCurryFin0 ℝ E F (p 0 x)
  have hder : ∀ m : ℕ, m < j → ∀ x, HasFDerivAt (fun y => q y m) ((q x m.succ).curryLeft) x := by
    intro m hm x
    have h1 := (hp m hm.le).2
    have h2 := hp (m + 1) hm
    have hu : TendstoUniformly
        (fun n => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F) ∘
          iteratedFDeriv ℝ (m + 1) (f n))
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F) ∘ p (m + 1))
        atTop :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).isometry.uniformContinuous.comp_tendstoUniformly
        h2.2
    refine hasFDerivAt_of_tendstoUniformly (f := fun n => iteratedFDeriv ℝ m (f n)) hu ?_
      (fun y => (hp m hm.le).2.tendsto_at y) x
    intro n y
    have := ((hf n).differentiable_iteratedFDeriv (m := m) (by
        norm_cast; exact ENat.natCast_lt_top m)) y
    exact this.hasFDerivAt
  have hT : HasFTaylorSeriesUpTo (j : ℕ∞) g q := by
    refine ⟨fun x => rfl, fun m hm x => hder m (by exact_mod_cast hm) x, fun m hm => ?_⟩
    exact (hp m (by exact_mod_cast hm)).1
  refine ⟨g, by exact_mod_cast hT.contDiff, fun i hi x => ?_⟩
  have := hT.eq_iteratedFDeriv (m := i) (by exact_mod_cast hi) x
  show Tendsto _ _ (𝓝 (iteratedFDeriv ℝ i g x))
  rw [← this]
  exact (hp i hi).2.tendsto_at x

/-- If smooth `f n` are uniformly Cauchy together with all derivatives of order `≤ j`, the limit is
`C^j` and the iterated derivatives converge pointwise to those of the limit. -/
theorem exists_contDiff_limit (j : ℕ) (f : ℕ → E → F) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hc : ∀ i ≤ j, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N, ∀ x,
      ‖iteratedFDeriv ℝ i (f n) x - iteratedFDeriv ℝ i (f n') x‖ ≤ ε) :
    ∃ g : E → F, ContDiff ℝ j g ∧ (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧
      ∀ i ≤ j, ∀ x, Tendsto (fun n => iteratedFDeriv ℝ i (f n) x) atTop
        (𝓝 (iteratedFDeriv ℝ i g x)) := by
  obtain ⟨g, h1, h2⟩ := exists_contDiff_limit_aux' j f hf hc
  refine ⟨g, h1, fun x => ?_, h2⟩
  have := (continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto _ |>.comp (h2 0 (Nat.zero_le _) x)
  exact this.congr fun n => rfl

end CutoffRigidity.Riemann.Diff
