module

public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.Dyson7

/-! # Thin wrappers for the Challenge statements proved in `Extra`

`dyson_ou_static` (`CutoffRigidity.Dyson`), restated over the `CutCur` definitions of `Challenge.lean`
(the Dyson definitions are inlined there; they are definitionally equal to the worker's). The integrated de Bruijn
identities (`DissipEq`), the Dyson gap, the Gaussian isoperimetry, the Rothaus alternative and the sphere theorems
are applied directly in `Solution.lean` (see `scripts/gen-solution.py`), through `ChallengeBridge`.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ContDiff
open CutCur

theorem dyson_ou_static {d : ℕ} (hd : 0 < d) {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (dysonProb d ρ β) ∧ IsOpen (chamber d) ∧ Convex ℝ (chamber d) ∧
    ConvexOn ℝ (chamber d) (fun x => ∑ i, ∑ j with i < j, -β * Real.log (x i - x j)) ∧
    (∀ x ∈ chamber d, generator (fun x => ρ / 2 * ‖x‖ ^ 2 + ∑ i, ∑ j with i < j, -β * Real.log (x i - x j))
        (fun x => ∑ i, x i) x = -ρ * ∑ i, x i) ∧
    (∀ φ, IsTestFunction φ → ∫ x, inner ℝ (gradient (fun x : Rd d => ∑ i, x i) x) (gradient φ x) ∂dysonProb d ρ β =
        ρ * ∫ x, (∑ i, x i) * φ x ∂dysonProb d ρ β) ∧
    (∀ f, IsTestFunction f → variance f (dysonProb d ρ β) ≤ ρ⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) ∧
    (MemLp (fun x : Rd d => ∑ i, x i) 2 (dysonProb d ρ β) ∧ 0 < variance (fun x : Rd d => ∑ i, x i) (dysonProb d ρ β) ∧
      variance (fun x : Rd d => ∑ i, x i) (dysonProb d ρ β) =
        ρ⁻¹ * ∫ x, ‖gradient (fun x : Rd d => ∑ i, x i) x‖ ^ 2 ∂dysonProb d ρ β) := by
  have key := Dyson.dyson_ou_static hd hρ hβ
  obtain ⟨⟨-, -, hp⟩, ⟨ho, hc, hcv⟩, hg, hn, hpo, -, hm, hv, he⟩ := key
  have hP : Dyson.dysonProb d ρ β = CutCur.dysonProb d ρ β := rfl
  have hC : Dyson.chamber d = CutCur.chamber d := rfl
  rw [hP] at hp hn hpo hm hv he
  refine ⟨hp, ho, hc, ?_, hg, hn, hpo, hm, hv, ?_⟩
  · have e : (fun x : Rd d => ∑ i, ∑ j with i < j, -β * Real.log (x i - x j)) =
        fun x => Dyson.dysonV d ρ β x - ρ / 2 * ‖x‖ ^ 2 := by
      funext x; simp [Dyson.dysonV]
    rw [e]; exact hcv
  · rw [he, Dyson.optimalPIDyson_eq hd hρ hβ]

end CutoffRigidity.Paper
