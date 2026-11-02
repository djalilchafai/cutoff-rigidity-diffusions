module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus5

/-! # Rothaus remark (stage 6): continuity of the entropy along Orlicz-convergent sequences (case of bounded means) -/

@[expose] public section

open MeasureTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem entropy_tendsto [IsFiniteMeasure μ] (F : Form μ) {g : ℕ → X → ℝ} {h : X → ℝ} {m : ℕ → ℝ} {m₀ : ℝ}
    (hg : ∀ n, g n ∈ F.Q) (hh : h ∈ F.Q) (hm : Tendsto m atTop (𝓝 m₀))
    (hL2 : Tendsto (fun n => ∫ x, (g n x - h x) ^ 2 ∂μ) atTop (𝓝 0))
    (hΘ : Tendsto (fun n => ∫ x, |Θ (g n x) - Θ (h x)| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => CutCur.entropyOf μ (fun x => (g n x + m n) ^ 2)) atTop
      (𝓝 (CutCur.entropyOf μ (fun x => (h x + m₀) ^ 2))) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n, |m n| ≤ K := by
    obtain ⟨K, hK⟩ := hm.norm.bddAbove_range
    exact ⟨K, fun n => hK ⟨n, rfl⟩⟩
  obtain ⟨c, hc0, hc⟩ := Θ_add_le K
  have hmg := fun n => F.memLp _ (hg n)
  have hΘg := fun n => F.integrable_Θ _ (hg n)
  have hmh := F.memLp _ hh
  have hΘh := F.integrable_Θ _ hh
  -- the squares
  have hsq : Tendsto (fun n => ∫ x, (g n x + m n) ^ 2 ∂μ) atTop (𝓝 (∫ x, (h x + m₀) ^ 2 ∂μ)) := by
    refine tendsto_integral_comp (H := fun t => t ^ 2) (continuous_pow 2) (c := 2 * K ^ 2 + 2) (K := K) ?_
      hmg hΘg hmh hΘh hm hK hL2 hΘ
    intro a b ha
    have hK2 : a ^ 2 ≤ K ^ 2 := sq_le_sq' (by linarith [abs_nonneg a, neg_abs_le a]) (le_trans (le_abs_self a) ha)
    rw [abs_of_nonneg (sq_nonneg _)]
    have := Θ_nonneg b
    nlinarith [sq_nonneg (a - b), sq_nonneg K, sq_nonneg b]
  have hlog : Tendsto (fun n => ∫ x, (g n x + m n) ^ 2 * Real.log ((g n x + m n) ^ 2) ∂μ) atTop
      (𝓝 (∫ x, (h x + m₀) ^ 2 * Real.log ((h x + m₀) ^ 2) ∂μ)) := by
    refine tendsto_integral_comp (H := fun t => t ^ 2 * Real.log (t ^ 2))
      (Real.continuous_mul_log.comp (continuous_pow 2)) (c := c + 1) (K := K) ?_
      hmg hΘg hmh hΘh hm hK hL2 hΘ
    intro a b ha
    have h1 := abs_sq_mul_log_sq_le (a + b)
    have h2 := hc a b ha
    have h3 := Θ_nonneg b
    have h4 : 0 ≤ 1 + b ^ 2 + Θ b := by positivity
    nlinarith
  have hM : Tendsto (fun n => (∫ x, (g n x + m n) ^ 2 ∂μ) * Real.log (∫ x, (g n x + m n) ^ 2 ∂μ)) atTop
      (𝓝 ((∫ x, (h x + m₀) ^ 2 ∂μ) * Real.log (∫ x, (h x + m₀) ^ 2 ∂μ))) :=
    (Real.continuous_mul_log.tendsto _).comp hsq
  exact hlog.sub hM

end CutoffRigidity.Rothaus
