module
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Strong convergence domains of actual uniformly contracting operators -/
public section
namespace CutoffRigidity
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

@[expose] noncomputable def strongConvergenceDomain (F : ℕ → H →L[ℝ] H) : Submodule ℝ H where
  carrier := {x | ∃ y, Tendsto (fun n => F n x) atTop (𝓝 y)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa only [map_add] using ha.add hb⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c • a, by simpa only [map_smul] using ha.const_smul c⟩

theorem strongConvergenceDomain_isClosed (F : ℕ → H →L[ℝ] H)
    (hF : ∀ n x, ‖F n x‖ ≤ ‖x‖) : IsClosed (strongConvergenceDomain F : Set H) := by
  apply closure_subset_iff_isClosed.mp
  intro x hx
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by positivity)
  obtain ⟨z, hz⟩ := hy
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hz.cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hnxy : dist (F n x) (F n y) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using hF n (x - y)
  have hmxy : dist (F m y) (F m x) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub, norm_sub_rev] using hF m (y - x)
  have hmid := hN n hn m hm
  have htri := dist_triangle4 (F n x) (F n y) (F m y) (F m x)
  have hd : dist x y < ε / 3 := by simpa only [dist_comm] using hxy
  linarith

omit [CompleteSpace H] in
theorem norm_clm_pow_apply_le (F : H →L[ℝ] H) (hF : ∀ x, ‖F x‖ ≤ ‖x‖)
    (k : ℕ) (x : H) : ‖(F ^ k) x‖ ≤ ‖x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact (hF _).trans ih

omit [CompleteSpace H] in
theorem clm_pow_apply_eigen (F : H →L[ℝ] H) (a : ℝ) (x : H) (hx : F x = a • x)
    (k : ℕ) : (F ^ k) x = a ^ k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hx, smul_smul]
    congr 1

variable {ι : Type*} [TopologicalSpace ι]

omit [CompleteSpace H] in
@[expose] noncomputable def strongContinuityDomain (F : ι → H →L[ℝ] H) (t : ι) : Submodule ℝ H where
  carrier := {x | ContinuousAt (fun s => F s x) t}
  zero_mem' := by simpa using (continuousAt_const : ContinuousAt (fun _ : ι => (0 : H)) t)
  add_mem' := by
    intro x y hx hy
    change ContinuousAt (fun s => F s x) t at hx
    change ContinuousAt (fun s => F s y) t at hy
    change ContinuousAt (fun s => F s (x + y)) t
    have heq : (fun s => F s (x + y)) = (fun s => F s x) + (fun s => F s y) :=
      funext (fun s => map_add (F s) x y)
    exact heq.symm ▸ hx.add hy
  smul_mem' := by
    intro c x hx
    change ContinuousAt (fun s => F s x) t at hx
    change ContinuousAt (fun s => F s (c • x)) t
    have heq : (fun s => F s (c • x)) = c • (fun s => F s x) :=
      funext (fun s => map_smul (F s) c x)
    exact heq.symm ▸ hx.const_smul c

omit [CompleteSpace H] in
theorem strongContinuityDomain_isClosed (F : ι → H →L[ℝ] H) (t : ι)
    (hF : ∀ s x, ‖F s x‖ ≤ ‖x‖) : IsClosed (strongContinuityDomain F t : Set H) := by
  apply closure_subset_iff_isClosed.mp
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by positivity)
  change ContinuousAt (fun s => F s y) t at hy
  have hh : ∀ᶠ s in 𝓝 t, dist (F s y) (F t y) < ε / 3 :=
    Metric.tendsto_nhds.mp hy _ (by positivity)
  filter_upwards [hh] with s hs
  have hsxy : dist (F s x) (F s y) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using hF s (x - y)
  have htxy : dist (F t y) (F t x) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub, norm_sub_rev] using hF t (y - x)
  have htri := dist_triangle4 (F s x) (F s y) (F t y) (F t x)
  linarith

end CutoffRigidity
