module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus7

/-! # Rothaus remark (stage 8): Gibbs bound for forms -/

@[expose] public section

open MeasureTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem scaled_identity {m g : ℝ} (hm : 0 < m) :
    (g + m) ^ 2 * Real.log ((g + m) ^ 2) - (g + m) ^ 2 * Real.log (m ^ 2) - (g + m) ^ 2 + m ^ 2 =
      m ^ 2 * ψ (g / m) := by
  have e : g + m = m * (1 + g / m) := by field_simp; ring
  by_cases h0 : 1 + g / m = 0
  · have : g + m = 0 := by rw [e, h0]; simp
    rw [this]; unfold ψ; rw [h0]; simp
  · unfold ψ
    rw [e, mul_pow, Real.log_mul (by positivity) (by positivity)]
    ring

/-- `Ent((g+m)²) ≤ ∫ m² ψ(g/m)` for `g ∈ Q`, `m > 0` (Gibbs bound at the constant `m²`). -/
theorem entropy_le_scaled [IsProbabilityMeasure μ] (F : Form μ) {g : X → ℝ} (hg : g ∈ F.Q) {m : ℝ} (hm : 0 < m) :
    CutCur.entropyOf μ (fun x => (g x + m) ^ 2) ≤ ∫ x, m ^ 2 * ψ (g x / m) ∂μ := by
  have hf := F.add_const_mem m g hg
  have h := entropyOf_le_integral (μ := μ) (h := fun x => (g x + m) ^ 2) (fun x => sq_nonneg _)
    (F.integrable_sq hf) (F.integrable_flog hf) (c := m ^ 2) (by positivity)
  refine h.trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun x => ?_)))
  exact scaled_identity hm

end CutoffRigidity.Rothaus
