module

public import CutoffRigidity.Riemann.TransportLower

/-! # Transport, step 5: `Λ = ρ|p|²` algebra

If `a₁,…,a_k ∈ ℝ^k` are orthogonal of squared norm `ρ`, then `∑ᵢ ⟨aᵢ, z⟩² = ρ‖z‖²`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace CutoffRigidity.Riemann

theorem sum_sq_inner_of_orthogonal {k : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (a : Fin k → EuclideanSpace ℝ (Fin k))
    (ha : ∀ i j, inner ℝ (a i) (a j) = if i = j then ρ else 0) (z : EuclideanSpace ℝ (Fin k)) :
    ∑ i, inner ℝ (a i) z ^ 2 = ρ * ‖z‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Subsingleton.elim z 0]
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  set s := Real.sqrt ρ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hρ
  have hv : Orthonormal ℝ (fun i => s⁻¹ • a i) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_smul_left, inner_smul_right, ha]
    have : s⁻¹ * s⁻¹ * ρ = 1 := by
      rw [← mul_inv, hs, Real.mul_self_sqrt hρ.le, inv_mul_cancel₀ hρ.ne']
    by_cases h : i = j
    · simp only [h, ite_true]; rw [← mul_assoc]; exact this
    · simp [h]
  have hcard : Fintype.card (Fin k) = Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) := by simp
  let b := (basisOfOrthonormalOfCardEqFinrank hv hcard).toOrthonormalBasis (by simpa using hv)
  have hb : ∀ i, b i = s⁻¹ • a i := fun i => by
    simp [b]
  have h := OrthonormalBasis.sum_sq_inner_right b z
  simp_rw [hb, real_inner_smul_left] at h
  have : ∀ i, inner ℝ (a i) z ^ 2 = ρ * (s⁻¹ * inner ℝ (a i) z) ^ 2 := fun i => by
    rw [mul_pow, ← mul_assoc]
    have : ρ * (s⁻¹) ^ 2 = 1 := by
      rw [inv_pow, hs, Real.sq_sqrt hρ.le, mul_inv_cancel₀ hρ.ne']
    rw [this, one_mul]
  simp_rw [this, ← Finset.mul_sum, h]

end CutoffRigidity.Riemann
