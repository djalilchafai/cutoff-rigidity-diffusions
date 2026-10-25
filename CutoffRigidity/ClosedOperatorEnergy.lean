module
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Lower semicontinuity of actual closed Hilbert operator energy

Banach--Alaoglu is applied to actual Riesz duals of bounded operator
images. Closed-graph orthogonal-complement tests identify the weak limit.
No weak compactness, graph membership, or energy semicontinuity premise
is substituted for a conclusion.
-/
public section
namespace CutoffRigidity
open Set Filter Topology
open scoped ENNReal

section Hilbert
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- An actual closed graph contains the strong/weak limit of a sequence
with bounded second components. The image norm bound is preserved. -/
theorem exists_mem_closedGraph_of_tendsto_bounded
    (G : H →ₗ.[ℝ] K) (hG : IsClosed (G.graph : Set (H × K)))
    {Un : ℕ → H} {Dn : ℕ → K} {U : H} (hU : Tendsto Un atTop (𝓝 U))
    (hgraph : ∀ n, (Un n, Dn n) ∈ G.graph)
    {C : ℝ} (_hC : 0 ≤ C) (hbound : ∀ n, ‖Dn n‖ ≤ C) :
    ∃ D : K, (U, D) ∈ G.graph ∧ ‖D‖ ≤ C := by
  let φ : ℕ → WeakDual ℝ K := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ K (Dn n))
  have hφball (n : ℕ) : φ n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ K) C := by
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ K (Dn n)‖ ≤ C
    simpa only [sub_zero, (InnerProductSpace.toDual ℝ K).norm_map] using hbound n
  have hmap : Filter.map φ atTop ≤ 𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ K) C) := by
    apply Filter.le_principal_iff.mpr
    change ∀ᶠ n : ℕ in atTop, φ n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ K) C
    exact Eventually.of_forall hφball
  obtain ⟨ℓ, hℓball, hcluster⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ K) C).exists_mapClusterPt hmap
  let D := (InnerProductSpace.toDual ℝ K).symm (WeakDual.toStrongDual ℓ)
  have hDnorm : ‖D‖ ≤ C := by
    have hh := hℓball
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hh
    simpa only [sub_zero, D, (InnerProductSpace.toDual ℝ K).symm.norm_map] using hh
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ H K
  let S : Submodule ℝ (WithLp 2 (H × K)) := G.graph.comap e.toLinearMap
  have hS : IsClosed (S : Set (WithLp 2 (H × K))) := hG.preimage e.continuous
  have hmem : WithLp.toLp 2 (U, D) ∈ Sᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    let a := (WithLp.ofLp w).1
    let b := (WithLp.ofLp w).2
    have horth (n : ℕ) : inner ℝ (Un n) a + inner ℝ (Dn n) b = 0 := by
      have hn : WithLp.toLp 2 (Un n, Dn n) ∈ S := hgraph n
      have hh := (Submodule.mem_orthogonal S w).mp hw _ hn
      exact hh
    have hscalar : Tendsto (fun n => φ n b) atTop (𝓝 (-inner ℝ U a)) := by
      apply ((hU.inner tendsto_const_nhds).neg).congr'
      apply Eventually.of_forall
      intro n
      change -inner ℝ (Un n) a = inner ℝ (Dn n) b
      linarith [horth n]
    have hcl := hcluster.continuousAt_comp (WeakDual.eval_continuous b).continuousAt
    obtain ⟨ns, hns, hsub⟩ := hcl.tendsto_subseq
    have heq : ℓ b = -inner ℝ U a := tendsto_nhds_unique hsub (hscalar.comp hns.tendsto_atTop)
    have hDb : inner ℝ D b = ℓ b := InnerProductSpace.toDual_symm_apply
    change inner ℝ U a + inner ℝ D b = 0
    rw [hDb, heq]
    ring
  rw [S.orthogonal_orthogonal_eq_closure] at hmem
  have hmem' : WithLp.toLp 2 (U, D) ∈ S := by
    have hh : WithLp.toLp 2 (U, D) ∈ closure (S : Set (WithLp 2 (H × K))) := hmem
    rw [hS.closure_eq] at hh
    exact hh
  exact ⟨D, hmem', hDnorm⟩

/-- Extended image norm of an actual partially defined operator. -/
@[expose] noncomputable def closedOperatorNorm (G : H →ₗ.[ℝ] K) (U : H) : ENNReal :=
  by
    classical
    exact if hD : U ∈ G.domain then ENNReal.ofReal ‖G ⟨U, hD⟩‖ else ⊤

/-- The extended norm of an actual closed Hilbert operator is lower
semicontinuous, proved through genuine closed energy sublevels. -/
theorem lowerSemicontinuous_closedOperatorNorm (G : H →ₗ.[ℝ] K)
    (hG : IsClosed (G.graph : Set (H × K))) : LowerSemicontinuous (closedOperatorNorm G) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r = ⊤
  · subst r
    simp
  · apply IsSeqClosed.isClosed
    intro Un U hUn hlim
    have hD (n : ℕ) : Un n ∈ G.domain := by
      by_contra hn
      have hh : closedOperatorNorm G (Un n) ≤ r := hUn n
      simp only [closedOperatorNorm, hn, dite_false] at hh
      exact hr (top_le_iff.mp hh)
    let Dn := fun n => G ⟨Un n, hD n⟩
    have hbound (n : ℕ) : ‖Dn n‖ ≤ r.toReal := by
      have hh : ENNReal.ofReal ‖Dn n‖ ≤ r := by
        have hh : closedOperatorNorm G (Un n) ≤ r := hUn n
        simpa only [closedOperatorNorm, hD n, dite_true, Dn] using hh
      have ht := ENNReal.toReal_mono hr hh
      simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using ht
    obtain ⟨D, hgraph, hnorm⟩ := exists_mem_closedGraph_of_tendsto_bounded G hG hlim
      (fun n => G.mem_graph ⟨Un n, hD n⟩) ENNReal.toReal_nonneg hbound
    have hDU : U ∈ G.domain := G.mem_domain_of_mem_graph hgraph
    have hval : G ⟨U, hDU⟩ = D := ((G.image_iff hDU).mpr hgraph).symm
    change closedOperatorNorm G U ≤ r
    rw [closedOperatorNorm, dite_eq_left hDU, hval, ← ENNReal.ofReal_toReal hr]
    exact ENNReal.ofReal_le_ofReal hnorm

/-- Extended squared-gradient energy, with the conventional Fisher factor
four. It is infinite outside the actual operator domain. -/
@[expose] noncomputable def closedOperatorFisherEnergy (G : H →ₗ.[ℝ] K) (U : H) : ENNReal :=
  4 * closedOperatorNorm G U ^ 2

/-- Genuine lower semicontinuity of closed squared-gradient energy. -/
theorem lowerSemicontinuous_closedOperatorFisherEnergy (G : H →ₗ.[ℝ] K)
    (hG : IsClosed (G.graph : Set (H × K))) : LowerSemicontinuous (closedOperatorFisherEnergy G) := by
  have hc : Continuous (fun r : ENNReal => 4 * r ^ 2) :=
    (ENNReal.continuous_const_mul (by norm_num : (4 : ENNReal) ≠ ⊤)).comp (ENNReal.continuous_pow 2)
  have hm : Monotone (fun r : ENNReal => 4 * r ^ 2) := by
    intro a b hab
    change 4 * a ^ 2 ≤ 4 * b ^ 2
    gcongr
  exact hc.comp_lowerSemicontinuous (lowerSemicontinuous_closedOperatorNorm G hG) hm

end Hilbert
end CutoffRigidity
