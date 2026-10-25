module

public import CutoffRigidity.Riemann.DiffEllipticRn5

/-! # Sums in `Sob`, and the induction on the order of regularity
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem Sob.zero (m : ℕ) : Sob b m (fun _ => (0 : ℝ)) ∧ sobSq b m (fun _ => (0 : ℝ)) = 0 := by
  have h := (Sob.of_smooth b m (f := fun _ : E => (0 : ℝ)) contDiff_const
    (by exact HasCompactSupport.zero))
  have h2 := Sob.smul b (m := m) 0 h.1
  simp only [zero_mul] at h2
  refine ⟨h2.1, ?_⟩
  rw [h2.2]; ring

theorem Sob.sum {J : Type*} (m : ℕ) (s : Finset J) (f : J → E → ℝ) (hf : ∀ j ∈ s, Sob b m (f j)) :
    Sob b m (fun x => ∑ j ∈ s, f j x) ∧
      sobSq b m (fun x => ∑ j ∈ s, f j x) ≤ 2 ^ s.card * ∑ j ∈ s, sobSq b m (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := Sob.zero b m
    simp only [Finset.sum_empty, Finset.card_empty, pow_zero, one_mul]
    exact ⟨h1, h2.le⟩
  | insert a s ha ih =>
    have ih' := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨h1, h2⟩ := Sob.add b hfa ih'.1
    have e : (fun x => ∑ j ∈ insert a s, f j x) = (f a + fun x => ∑ j ∈ s, f j x) := by
      funext x; simp [Finset.sum_insert ha]
    rw [e]
    refine ⟨h1, h2.trans ?_⟩
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have p1 : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    have n1 : 0 ≤ sobSq b m (f a) := sobSq_nonneg b m _
    have n2 : 0 ≤ ∑ j ∈ s, sobSq b m (f j) := Finset.sum_nonneg (fun j _ => sobSq_nonneg b m _)
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih'.2 (by norm_num : (0 : ℝ) ≤ 2), mul_nonneg n1 (sub_nonneg.2 p1)]

theorem Ell.mono {A : ι → ι → E → ℝ} {θ K : ℝ} {N N' : ℕ} (h : N ≤ N') (hA : Ell A θ K N') :
    Ell A θ K N :=
  ⟨hA.smooth, hA.symm, hA.elliptic, fun i j k hk x => hA.bound i j k (hk.trans h) x⟩

end CutoffRigidity.Riemann.Diff
