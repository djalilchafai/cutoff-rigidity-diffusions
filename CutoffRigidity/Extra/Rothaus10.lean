module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus9

/-! # Rothaus remark (stage 10): optimal constants and normalised minimising sequences -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

namespace Form

/-- The analytic input of the Rothaus argument on a form `(Q, E)`: energy balls (on mean-zero functions) are
sequentially compact for `L²`-convergence together with `L¹`-convergence of the Orlicz weight `Θ(g) = g² log(1+g²)`
(compact embedding of `H¹` into `L² log L`), and the energy is lower semicontinuous along the extracted subsequence. -/
def Compact (F : Form μ) : Prop :=
  ∀ (B : ℝ) (g : ℕ → X → ℝ), (∀ n, g n ∈ F.Q) → (∀ n, ∫ x, g n x ∂μ = 0) → (∀ n, F.E (g n) ≤ B) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h ∈ F.Q,
      Tendsto (fun n => ∫ x, (g (φ n) x - h x) ^ 2 ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, |Θ (g (φ n) x) - Θ (h x)| ∂μ) atTop (𝓝 0) ∧
      ∀ b : ℝ, (∀ᶠ n in atTop, F.E (g (φ n)) ≤ b) → F.E h ≤ b

theorem lsi_spec (F : Form μ) (hLSI : ∃ c, 0 ≤ c ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f)
    {f : X → ℝ} (hf : f ∈ F.Q) : CutCur.entropyOf μ (fun x => f x ^ 2) ≤ F.optLSI * F.E f := by
  obtain ⟨c₀, hc₀, h₀⟩ := hLSI
  rcases (F.E_nonneg f hf).eq_or_lt with h0 | h0
  · have := h₀ f hf
    rw [← h0] at this ⊢
    simpa using this
  · rw [← div_le_iff₀ h0]
    refine le_csInf ⟨c₀, hc₀, h₀⟩ fun c ⟨_, hc⟩ => ?_
    rw [div_le_iff₀ h0]
    exact hc f hf

theorem pi_spec (F : Form μ) (hPI : ∃ c, 0 ≤ c ∧ ∀ f ∈ F.Q, variance f μ ≤ c * F.E f)
    {f : X → ℝ} (hf : f ∈ F.Q) : variance f μ ≤ F.optPI * F.E f := by
  obtain ⟨c₀, hc₀, h₀⟩ := hPI
  rcases (F.E_nonneg f hf).eq_or_lt with h0 | h0
  · have := h₀ f hf
    rw [← h0] at this ⊢
    simpa using this
  · rw [← div_le_iff₀ h0]
    refine le_csInf ⟨c₀, hc₀, h₀⟩ fun c ⟨_, hc⟩ => ?_
    rw [div_le_iff₀ h0]
    exact hc f hf

theorem optPI_nonneg (F : Form μ) : 0 ≤ F.optPI := Real.sInf_nonneg fun _ hc => hc.1

theorem optLSI_le (F : Form μ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f) : F.optLSI ≤ c :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hc0, hc⟩

/-- For `c < optLSI` the Rothaus inequality with constant `c` fails somewhere. -/
theorem exists_gt_of_lt_optLSI (F : Form μ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < F.optLSI) :
    ∃ f ∈ F.Q, c * F.E f < CutCur.entropyOf μ (fun x => f x ^ 2) := by
  by_contra hcon
  push Not at hcon
  exact absurd (F.optLSI_le hc0 hcon) (not_le.2 hc)

/-- Replace `u` by `±u` so that the mean is nonnegative. -/
theorem exists_sign (F : Form μ) {u : X → ℝ} (hu : u ∈ F.Q) :
    ∃ v ∈ F.Q, (∀ x, v x ^ 2 = u x ^ 2) ∧ F.E v = F.E u ∧ 0 ≤ ∫ x, v x ∂μ := by
  by_cases h : 0 ≤ ∫ x, u x ∂μ
  · exact ⟨u, hu, fun x => rfl, rfl, h⟩
  · refine ⟨(-1 : ℝ) • u, F.smul_mem _ _ hu, fun x => by simp, ?_, ?_⟩
    · rw [F.E_smul _ _ hu]; ring
    · have : ∫ x, ((-1 : ℝ) • u) x ∂μ = -∫ x, u x ∂μ := by
        simp [integral_neg]
      rw [this]; linarith [not_le.1 h]

end Form

end CutoffRigidity.Rothaus
