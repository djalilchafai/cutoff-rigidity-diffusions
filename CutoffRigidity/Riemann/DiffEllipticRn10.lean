module

public import CutoffRigidity.Riemann.DiffEllipticRn9

/-! # The local regularity step and the induction on the order
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

theorem aesupp_of_testMul {Ω : Set E} {χ₁ u : E → ℝ} (h : IsTest Ω χ₁) :
    AESupp (fun x => χ₁ x * u x) := by
  obtain ⟨R, hR⟩ := exists_norm_bound_of_compactSupport h.2.1
  exact ⟨R, Filter.Eventually.of_forall fun x hx => by simp [hR x hx]⟩

/-- One regularity step for the local problem. -/
theorem locSob_step {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {u : E → ℝ} {u' : ι → E → ℝ} (hu : LocH1 b Ω u u') {F : E → ℝ} (hF : LocL2 Ω F)
    (heq : LocEq b Ω A u' F) (m : ℕ) (hum : LocSob b Ω (m + 1) u) (hFm : LocSob b Ω m F) :
    LocSob b Ω (m + 2) u := by
  intro χ hχ
  obtain ⟨χ₁, hχ₁, ⟨V, hV, hKV, hV1⟩, -⟩ := exists_cutoff_nhds hχ.2.1 hΩ hχ.2.2
  obtain ⟨ψ, θ, Kb, AR, hψ, hθ, hEll, hAhat, hWeak⟩ :=
    localized_weakEq b hΩ hAs hAsym hAell hu hF heq hχ₁ (m + 1)
  obtain ⟨C, hC0, hC⟩ := global_regularity b θ Kb hθ m
  have hd := fun j => hu.wd j
  have hu'm : ∀ j, LocSob b Ω m (u' j) := fun j => hum.deriv b hΩ hd j
  have ht : ∀ i j, ContDiff ℝ ∞ (fun x => ψ x * A i j x * pd (b i) χ₁ x) := fun i j =>
    (hAhat i j).1.mul (contDiff_pd hχ₁.1 _)
  have htc : ∀ i j, HasCompactSupport (fun x => ψ x * A i j x * pd (b i) χ₁ x) := fun i j =>
    (hAhat i j).2.1.mul_right
  have hts : ∀ i j, tsupport (fun x => ψ x * A i j x * pd (b i) χ₁ x) ⊆ Ω := fun i j =>
    tsupport_mul_subset_left.trans (hAhat i j).2.2
  have hFt : Sob b m (fun x => χ₁ x * F x -
      ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) := by
    have h1 := hFm χ₁ hχ₁
    have h2 : ∀ i, Sob b m (fun x => ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) := fun i =>
      (Sob.sum b m Finset.univ (fun j x => ψ x * A i j x * pd (b i) χ₁ x * u' j x)
        (fun j _ => sob_mul_of_locSob b hΩ (hu'm j) (ht i j) (htc i j) (hts i j))).1
    have h3 := (Sob.sum b m Finset.univ (fun i x => ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x)
      (fun i _ => h2 i)).1
    exact (Sob.sub b h1 h3).1
  have hGt : ∀ i, Sob b (m + 1) (fun x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) := by
    intro i
    have t : ∀ j, ContDiff ℝ ∞ (fun x => ψ x * A i j x * pd (b j) χ₁ x) := fun j =>
      (hAhat i j).1.mul (contDiff_pd hχ₁.1 _)
    have tc : ∀ j, HasCompactSupport (fun x => ψ x * A i j x * pd (b j) χ₁ x) := fun j =>
      (hAhat i j).2.1.mul_right
    have tsub : ∀ j, tsupport (fun x => ψ x * A i j x * pd (b j) χ₁ x) ⊆ Ω := fun j =>
      tsupport_mul_subset_left.trans (hAhat i j).2.2
    have := (Sob.sum b (m + 1) Finset.univ
      (fun j x => (ψ x * A i j x * pd (b j) χ₁ x) * u x)
      (fun j _ => sob_mul_of_locSob b hΩ hum (t j) (tc j) (tsub j))).1
    refine Sob.congr_ae b this (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  obtain ⟨hsob, -⟩ := hC AR hEll (fun x => χ₁ x * u x) _ _ ((hum.mono b (by omega)) χ₁ hχ₁)
    (aesupp_of_testMul hχ₁) hFt hGt hWeak
  obtain ⟨Kc, hKc⟩ := exists_iteratedFDeriv_bound hχ.1 hχ.2.1 (m + 2)
  have h2 := (Sob.mul_smooth b hχ.1 hKc hsob).1
  refine Sob.congr_ae b h2 (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport χ
  · simp [hV1 x (hKV hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end CutoffRigidity.Riemann.Diff
