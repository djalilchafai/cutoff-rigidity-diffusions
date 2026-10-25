module

public import CutoffRigidity.Riemann.DiffEllipticRn10

/-! # Smoothness of weak solutions: induction, local smooth representatives, gluing
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

/-- Induction on the order of local Sobolev regularity. -/
theorem locSob_all {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {u : E → ℝ} {u' : ι → E → ℝ} (hu : LocH1 b Ω u u') {F : E → ℝ} (hF : LocL2 Ω F)
    (heq : LocEq b Ω A u' F)
    (hFreg : ∀ m, LocSob b Ω (m + 1) u → LocSob b Ω m F) :
    ∀ m, LocSob b Ω (m + 1) u := by
  intro m
  induction m with
  | zero => exact hu.locSob b hΩ
  | succ m ih => exact locSob_step b hΩ hAs hAsym hAell hu hF heq m ih (hFreg m ih)

/-- Local smooth representative around each point. -/
theorem exists_smooth_local {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hall : ∀ m, LocSob b Ω m u) {x : E} (hx : x ∈ Ω) :
    ∃ (V : Set E) (h : E → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ ∞ h ∧
      h =ᵐ[volume.restrict V] u := by
  obtain ⟨χ, hχ, ⟨V, hV, hKV, hV1⟩, -⟩ := exists_cutoff_nhds (isCompact_singleton (x := x)) hΩ
    (Set.singleton_subset_iff.2 hx)
  have hVΩ : V ⊆ Ω := fun y hy => hχ.2.2 (subset_tsupport _ (by simp [hV1 y hy]))
  have hemb : ∀ j : ℕ, ∃ g : E → ℝ, ContDiff ℝ j g ∧ g =ᵐ[volume] (fun y => χ y * u y) := by
    intro j
    obtain ⟨C, -, hCe⟩ := sobolev_embedding b (j := j) (m := Module.finrank ℝ E + j + 1) (by omega)
    obtain ⟨g, hg, hae, -⟩ := hCe _ (hall _ χ hχ) (aesupp_of_testMul hχ)
    exact ⟨g, hg, hae⟩
  choose g hg hgae using hemb
  have hgeq : ∀ j, g j = g 0 := fun j =>
    ((hg j).continuous.ae_eq_iff_eq volume (hg 0).continuous).1 ((hgae j).trans (hgae 0).symm)
  have hsm : ContDiff ℝ ∞ (g 0) := by
    rw [contDiff_infty]
    intro n
    have := hg n
    rwa [hgeq n] at this
  refine ⟨V, g 0, hV, hKV rfl, hVΩ, hsm, ?_⟩
  have h1 : g 0 =ᵐ[volume.restrict V] fun y => χ y * u y := ae_restrict_of_ae (hgae 0)
  refine h1.trans ?_
  filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
  simp [hV1 y hy]

/-- Gluing the local smooth representatives. -/
theorem exists_smooth_global {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hall : ∀ m, LocSob b Ω m u) :
    ∃ ū : E → ℝ, ContDiffOn ℝ ∞ ū Ω ∧ u =ᵐ[volume.restrict Ω] ū := by
  classical
  have hex : ∀ x : E, ∃ (V : Set E) (h : E → ℝ), x ∈ Ω → (IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ContDiff ℝ ∞ h ∧ h =ᵐ[volume.restrict V] u) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨V, h, h1, h2, h3, h4, h5⟩ := exists_smooth_local b hΩ hall hx
      exact ⟨V, h, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨∅, fun _ => 0, fun h => absurd h hx⟩
  choose V h hVh using hex
  set ū : E → ℝ := fun y => h y y with hū
  -- agreement on the neighbourhoods
  have hagree : ∀ y ∈ Ω, ∀ z ∈ V y, ū z = h y z := by
    intro y hy z hz
    have hzΩ : z ∈ Ω := (hVh y hy).2.2.1 hz
    have hW : IsOpen (V z ∩ V y) := (hVh z hzΩ).1.inter (hVh y hy).1
    have hae : h z =ᵐ[volume.restrict (V z ∩ V y)] h y := by
      have a1 : h z =ᵐ[volume.restrict (V z ∩ V y)] u :=
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hVh z hzΩ).2.2.2.2
      have a2 : h y =ᵐ[volume.restrict (V z ∩ V y)] u :=
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hVh y hy).2.2.2.2
      exact a1.trans a2.symm
    have := Measure.eqOn_open_of_ae_eq hae hW (hVh z hzΩ).2.2.2.1.continuous.continuousOn
      (hVh y hy).2.2.2.1.continuous.continuousOn
    exact this ⟨(hVh z hzΩ).2.1, hz⟩
  refine ⟨ū, ?_, ?_⟩
  · intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    have : ū =ᶠ[nhds y] h y := by
      filter_upwards [(hVh y hy).1.mem_nhds (hVh y hy).2.1] with z hz using hagree y hy z hz
    exact ((hVh y hy).2.2.2.1.contDiffAt).congr_of_eventuallyEq this
  · obtain ⟨T, hTΩ, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable Ω V
      (fun y hy => (hVh y hy).1)
    have hcov : Ω ⊆ ⋃ y ∈ T, V y := by
      intro z hz
      rw [hTU]
      exact Set.mem_biUnion hz (hVh z hz).2.1
    have hloc : ∀ y ∈ T, ∀ᵐ z ∂(volume.restrict (V y)), u z = ū z := by
      intro y hy
      have hyΩ := hTΩ hy
      have e1 : ∀ᵐ z ∂(volume.restrict (V y)), z ∈ V y := ae_restrict_mem (hVh y hyΩ).1.measurableSet
      filter_upwards [e1, (hVh y hyΩ).2.2.2.2] with z hz hzh
      rw [hagree y hyΩ z hz, ← hzh]
    have := (ae_restrict_biUnion_iff V hTc (fun z => u z = ū z)).2 hloc
    exact ae_restrict_of_ae_restrict_of_subset hcov this

end CutoffRigidity.Riemann.Diff
