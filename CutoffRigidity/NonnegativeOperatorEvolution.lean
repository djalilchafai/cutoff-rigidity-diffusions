module

public import CutoffRigidity.SynchronousContraction
public import CutoffRigidity.GibbsHeatGenerator

/-! # Uniqueness of genuine strong evolutions in a nonnegative operator graph

The difference equation decreases the actual squared Hilbert norm. This
supplies uniqueness for the actual Gibbs form heat evolution without any
semigroup-identification premise.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory Filter Topology

/-- A nonnegative linear operator graph contracts the difference of its
actual strong forward evolutions. -/
theorem norm_sub_le_of_nonnegative_graph_evolution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Submodule ℝ (H × H))
    (hA : ∀ u g : H, (u,g) ∈ A → 0 ≤ inner ℝ g u)
    {U V G K : ℝ → H} {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hUd : ∀ s ∈ Ioo 0 T, HasDerivAt U (-G s) s)
    (hVd : ∀ s ∈ Ioo 0 T, HasDerivAt V (-K s) s)
    (hUG : ∀ s ∈ Ioo 0 T, (U s,G s) ∈ A)
    (hVK : ∀ s ∈ Ioo 0 T, (V s,K s) ∈ A) :
    ‖U T - V T‖ ≤ ‖U 0 - V 0‖ := by
  have he := norm_contraction_of_dissipative_derivative (rate := 0) hT (hU.sub hV)
    (fun s hs => (hUd s hs).sub (hVd s hs)) (fun s hs => by
      have hh := hA (U s - V s) (G s - K s) (A.sub_mem (hUG s hs) (hVK s hs))
      change inner ℝ (U s - V s) (-G s - -K s) ≤ -0 * ‖U s - V s‖ ^ 2
      rw [show -G s - -K s = -(G s - K s) by abel, inner_neg_right]
      have hi := real_inner_comm (U s - V s) (G s - K s)
      simp only [neg_zero, zero_mul]
      nlinarith [hi])
  simpa only [Pi.sub_apply, neg_zero, zero_mul, Real.exp_zero, one_mul] using he

/-- Initial equality gives actual strong-solution uniqueness. -/
theorem eq_of_nonnegative_graph_evolution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Submodule ℝ (H × H))
    (hA : ∀ u g : H, (u,g) ∈ A → 0 ≤ inner ℝ g u)
    {U V G K : ℝ → H} {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hUd : ∀ s ∈ Ioo 0 T, HasDerivAt U (-G s) s)
    (hVd : ∀ s ∈ Ioo 0 T, HasDerivAt V (-K s) s)
    (hUG : ∀ s ∈ Ioo 0 T, (U s,G s) ∈ A)
    (hVK : ∀ s ∈ Ioo 0 T, (V s,K s) ∈ A) (hzero : U 0 = V 0) : U T = V T := by
  have hh := norm_sub_le_of_nonnegative_graph_evolution A hA hT hU hV hUd hVd hUG hVK
  rw [hzero, sub_self, norm_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual Gibbs self-adjoint graph has a nonnegative pairing at every
actual graph pair, with no spectral or domain positivity assumption. -/
theorem gibbsPositiveGenerator_graph_nonneg {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u,g) ∈ (gibbsPositiveGenerator hV hp).graph) : 0 ≤ inner ℝ g u := by
  obtain ⟨v,hv,hg⟩ := (gibbsPositiveGenerator hV hp).mem_graph_iff.mp hug
  have hh := gibbsPositiveGenerator_nonneg hV hp v
  rwa [hg,hv] at hh

/-- Every actual strong solution with the same operator-domain initial
value is the canonical form heat trajectory. -/
theorem gibbsHeatSemigroup_unique_strong_solution {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u,g) ∈ (gibbsPositiveGenerator hV hp).graph)
    (U G : ℝ → E →₂[gibbsMeasure volume V] ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T))
    (hUd : ∀ s ∈ Ioo 0 T, HasDerivAt U (-G s) s)
    (hUG : ∀ s ∈ Ioo 0 T, (U s,G s) ∈ (gibbsPositiveGenerator hV hp).graph)
    (hzero : U 0 = u) : U T = gibbsHeatSemigroup hV hp ρ hρ hHess T.toNNReal u := by
  apply eq_of_nonnegative_graph_evolution (gibbsPositiveGenerator hV hp).graph
    (gibbsPositiveGenerator_graph_nonneg hV hp) hT hU
    (((continuous_gibbsHeatSemigroup_apply hV hp ρ hρ hHess u).comp continuous_real_toNNReal).continuousOn)
    hUd (fun s hs => gibbsHeatSemigroup_hasDerivAt_operatorGraph hV hp ρ hρ hHess s hs.1 u g hug)
    hUG (fun s hs => gibbsHeatSemigroup_preserves_operatorGraph hV hp ρ hρ hHess s.toNNReal u g hug)
  change U 0 = gibbsHeatSemigroup hV hp ρ hρ hHess (0 : ℝ).toNNReal u
  rw [Real.toNNReal_zero, gibbsHeatSemigroup_zero, ContinuousLinearMap.id_apply]
  exact hzero

end CutoffRigidity
