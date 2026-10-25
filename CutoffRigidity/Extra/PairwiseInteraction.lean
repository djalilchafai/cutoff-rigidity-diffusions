module

public import CutoffRigidity.Paper.ConvexInteraction

/-! # Pairwise interaction example (manuscript L289-293)

For `h : ℝ → ℝ` convex, `W(x) = ∑_{i<j} h(xᵢ - xⱼ)` is convex and invariant under translations
along `(1,…,1)`; it is `C²` when `h` is.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory
open scoped ContDiff

/-- **Pairwise interaction example** (introduction, after (1.5)): for `h` convex, the potential
`W(x) = ∑_{i<j} h(xᵢ - xⱼ)` is convex and invariant under translations along `(1,…,1)`
(and `C²` if `h` is `C²`, as needed in Theorem 1.5). Evenness of `h` is not needed. -/
theorem pairwise_interaction {d : ℕ} {h : ℝ → ℝ} (hh : ConvexOn ℝ Set.univ h) :
    let W := fun x : CutCur.Rd d => ∑ i, ∑ j with i < j, h (x i - x j)
    ConvexOn ℝ Set.univ W ∧ (∀ x (s : ℝ), W (x + s • CutCur.diagonal d) = W x) ∧
      (ContDiff ℝ 2 h → ContDiff ℝ 2 W) := by
  intro W
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → CutCur.Rd d → ℝ),
      (∀ i, ConvexOn ℝ Set.univ (f i)) → ConvexOn ℝ Set.univ (fun x => ∑ i ∈ s, f i x) := by
    intro ι s f hf
    classical
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) convex_univ
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a).add ih
  have hlin : ∀ i j : Fin d, ConvexOn ℝ Set.univ (fun x : CutCur.Rd d => h (x i - x j)) := by
    intro i j
    have := hh.comp_linearMap
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i -
        LinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).comp
        (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap)
    simpa [Function.comp_def] using this
  refine ⟨?_, ?_, ?_⟩
  · exact hsum _ _ fun i => hsum _ _ fun j => hlin i j
  · intro x s
    simp only [W]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [CutCur.diagonal]
  · intro h2
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    refine h2.comp ?_
    have : ∀ k : Fin d, ContDiff ℝ 2 (fun x : CutCur.Rd d => x k) := fun k =>
      (EuclideanSpace.proj k : CutCur.Rd d →L[ℝ] ℝ).contDiff
    exact (this i).sub (this j)

end CutoffRigidity.Paper
