module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus8

/-! # Rothaus remark (stage 9): the two cases of the minimising-sequence argument -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Bounded means: the entropy passes to the limit. -/
theorem caseA [IsFiniteMeasure μ] (F : Form μ) {g : ℕ → X → ℝ} {h : X → ℝ} {m : ℕ → ℝ} {m₀ : ℝ}
    (hg : ∀ n, g n ∈ F.Q) (hh : h ∈ F.Q) (hm : Tendsto m atTop (𝓝 m₀))
    (hL2 : Tendsto (fun n => ∫ x, (g n x - h x) ^ 2 ∂μ) atTop (𝓝 0))
    (hΘ : Tendsto (fun n => ∫ x, |Θ (g n x) - Θ (h x)| ∂μ) atTop (𝓝 0))
    (hent : ∀ n, CutCur.entropyOf μ (fun x => (g n x + m n) ^ 2) = 1) :
    CutCur.entropyOf μ (fun x => (h x + m₀) ^ 2) = 1 := by
  have := entropy_tendsto F hg hh hm hL2 hΘ
  simp_rw [hent] at this
  exact (tendsto_nhds_unique tendsto_const_nhds this).symm

/-- Means escaping to infinity: the limiting variance is at least `1/2`. -/
theorem caseB [IsProbabilityMeasure μ] (F : Form μ) {g : ℕ → X → ℝ} {h : X → ℝ} {m : ℕ → ℝ}
    (hg : ∀ n, g n ∈ F.Q) (hh : h ∈ F.Q) (hm1 : ∀ n, 1 ≤ m n) (hm : Tendsto m atTop atTop)
    (hL2 : Tendsto (fun n => ∫ x, (g n x - h x) ^ 2 ∂μ) atTop (𝓝 0))
    (hΘ : Tendsto (fun n => ∫ x, |Θ (g n x) - Θ (h x)| ∂μ) atTop (𝓝 0))
    (hent : ∀ n, CutCur.entropyOf μ (fun x => (g n x + m n) ^ 2) = 1) :
    1 ≤ 2 * ∫ x, h x ^ 2 ∂μ := by
  have hlim := tendsto_scaled (fun n => F.memLp _ (hg n)) (fun n => F.integrable_Θ _ (hg n)) (F.memLp _ hh)
    (F.integrable_Θ _ hh) hm1 hm hL2 hΘ
  have hle : ∀ n, (1 : ℝ) ≤ ∫ x, m n ^ 2 * ψ (g n x / m n) ∂μ := fun n => by
    rw [← hent n]
    exact entropy_le_scaled F (hg n) (by linarith [hm1 n])
  have := ge_of_tendsto' hlim hle
  rwa [integral_const_mul] at this

end CutoffRigidity.Rothaus
