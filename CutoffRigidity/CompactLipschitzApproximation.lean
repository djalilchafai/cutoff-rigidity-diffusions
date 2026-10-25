module
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Actual uniform Lipschitz approximation on compact metric spaces

The Lipschitz continuous functions form a separating real subalgebra.
Stone–Weierstrass supplies genuine uniform approximants.
-/
public section
namespace CutoffRigidity
open Set
open scoped Topology NNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X]

@[expose] def compactLipschitzSubalgebra : Subalgebra ℝ C(X,ℝ) where
  carrier := {f | ∃ L : ℝ≥0, LipschitzWith L f}
  algebraMap_mem' r := ⟨0,LipschitzWith.const r⟩
  add_mem' := by
    rintro f g ⟨L,hf⟩ ⟨K,hg⟩
    exact ⟨L+K,hf.add hg⟩
  mul_mem' := by
    rintro f g ⟨L,hf⟩ ⟨K,hg⟩
    refine ⟨Real.toNNReal (‖f‖*K+‖g‖*L),LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [ContinuousMap.mul_apply,Real.dist_eq]
    calc
      |f x*g x-f y*g y| = |f x*(g x-g y)+(f x-f y)*g y| := by congr 1; ring
      _ ≤ |f x| * |g x-g y|+|f x-f y| * |g y| := by
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
      _ ≤ ‖f‖*(K*dist x y)+(L*dist x y)*‖g‖ := by
        gcongr
        · exact f.norm_coe_le_norm x
        · exact hg.dist_le_mul x y
        · exact hf.dist_le_mul x y
        · exact g.norm_coe_le_norm y
      _ = _ := by ring
  zero_mem' := ⟨0,LipschitzWith.const 0⟩
  one_mem' := ⟨0,LipschitzWith.const 1⟩

theorem compactLipschitzSubalgebra_separatesPoints :
    (compactLipschitzSubalgebra (X := X)).SeparatesPoints := by
  intro x y hxy
  let f : C(X,ℝ) := ⟨fun z => dist z y,continuous_id.dist continuous_const⟩
  refine ⟨f,⟨f,⟨1,LipschitzWith.dist_left y⟩,rfl⟩,?_⟩
  simpa [f] using hxy

/-- A real continuous function on an actual compact metric space has a
genuine globally Lipschitz uniform approximation to any positive precision. -/
theorem exists_lipschitz_near_compact_continuous
    (f : C(X,ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : C(X,ℝ)) (L : ℝ≥0), LipschitzWith L g ∧ ∀ x, |g x-f x| < ε := by
  obtain ⟨g,hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (compactLipschitzSubalgebra (X := X)) compactLipschitzSubalgebra_separatesPoints f ε hε
  obtain ⟨L,hL⟩ := g.property
  refine ⟨g.val,L,hL,?_⟩
  intro x
  exact ((g.val-f).norm_coe_le_norm x).trans_lt hg

end CutoffRigidity
