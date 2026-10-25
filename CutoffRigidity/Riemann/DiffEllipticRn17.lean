module

public import CutoffRigidity.Riemann.DiffEllipticRn16

/-! # Final statements of the `ℝⁿ` elliptic regularity programme (WS-REGn)

* `weak_solution_smooth` (in `DiffEllipticRn12`): weak `H¹_loc` solutions are smooth.
* `weak_solution_regular_step`: local gain of two derivatives (`H^{m+1}_loc` data gives `H^{m+2}_loc`).
* `interior_estimate`: quantitative interior estimate in cutoff form.
* `sobolev_embedding_loc`, `interior_sup_estimate`: Sobolev embedding and sup bounds.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

/-- Local gain of two derivatives for `-div(A ∇u) = F`. -/
theorem weak_solution_regular_step {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {u : E → ℝ} {u' : ι → E → ℝ} (hu : LocH1 b Ω u u') {F : E → ℝ} (hF : LocL2 Ω F)
    (heq : LocEq b Ω A u' F) (m : ℕ) (hum : LocSob b Ω (m + 1) u) (hFm : LocSob b Ω m F) :
    LocSob b Ω (m + 2) u :=
  locSob_step b hΩ hAs hAsym hAell hu hF heq m hum hFm

/-- Sobolev embedding, local form: a locally `H^m` function (`m > j + n/2`) has, near any cutoff,
a `C^j` representative with a sup bound by the `H^m` norm of the cutoff function. -/
theorem sobolev_embedding_loc {Ω : Set E} {j m : ℕ}
    (hm : Module.finrank ℝ E + 2 * j < 2 * m) {χ : E → ℝ} (hχ : IsTest Ω χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E → ℝ, LocSob b Ω m u →
      ∃ g : E → ℝ, ContDiff ℝ j g ∧ g =ᵐ[volume] (fun x => χ x * u x) ∧
        ∀ x, ∀ i ≤ j, ‖iteratedFDeriv ℝ i g x‖ ^ 2 ≤ C * sobSq b m (fun x => χ x * u x) := by
  obtain ⟨C, hC0, hC⟩ := sobolev_embedding b hm
  exact ⟨C, hC0, fun u hu => hC _ (hu χ hχ) (aesupp_of_testMul hχ)⟩

/-- Interior `C^j` estimate: sup norms of derivatives of the cutoff solution are bounded by
`‖χ' g‖_{H^{m-2}}` and `‖χ' u‖_{L²}`, with a constant independent of the solution. -/
theorem interior_sup_estimate {Ω : Set E} {A : ι → ι → E → ℝ} {ϱ : E → ℝ}
    (hc : WCoeff Ω A ϱ) (lam : ℝ) {j m : ℕ} (hm : Module.finrank ℝ E + 2 * j < 2 * m)
    {χ : E → ℝ} (hχ : IsTest Ω χ) :
    ∃ (χ' : E → ℝ) (C : ℝ), IsTest Ω χ' ∧ 0 ≤ C ∧
      ∀ (u : E → ℝ) (u' : ι → E → ℝ) (g : E → ℝ), WSol b Ω A ϱ lam u u' g →
        ∃ gχ : E → ℝ, ContDiff ℝ j gχ ∧ gχ =ᵐ[volume] (fun x => χ x * u x) ∧
          ∀ x, ∀ i ≤ j, ‖iteratedFDeriv ℝ i gχ x‖ ^ 2 ≤
            C * (sobSq b (m - 2) (fun x => χ' x * g x) + sobSq b 0 (fun x => χ' x * u x)) := by
  obtain ⟨Ce, hCe0, hCe⟩ := sobolev_embedding_loc b (Ω := Ω) hm hχ
  obtain ⟨χ', Ck, hχ', hCk0, hCk⟩ := interior_estimate b hc lam m χ hχ
  refine ⟨χ', Ce * Ck, hχ', by positivity, fun u u' g hs => ?_⟩
  obtain ⟨gχ, hg1, hg2, hg3⟩ := hCe u (hs.locSob_all b hc m)
  refine ⟨gχ, hg1, hg2, fun x i hi => ?_⟩
  refine (hg3 x i hi).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hCk u u' g hs) hCe0

end CutoffRigidity.Riemann.Diff
