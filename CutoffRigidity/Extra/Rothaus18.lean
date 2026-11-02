module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus12

/-! # Rothaus remark (stage 18): `C_LSI ≥ 2 C_PI` and the dichotomy "twice or extremal"

`Ent((g + m)²) = ∫ m² ψ(g/m) - (defect)` with `0 ≤ defect ≤ (∫g²)²/m²`, so `Ent((g+m)²) → 2 ∫ g²` as `m → ∞` for fixed
mean-zero `g`; linearising the LSI at the constant `m` gives the Poincaré inequality with constant `C_LSI/2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Exact form of the Gibbs identity. -/
theorem integral_gibbs_eq [IsProbabilityMeasure μ] {h : X → ℝ} (h1 : Integrable h μ)
    (h2 : Integrable (fun x => h x * Real.log (h x)) μ) {c : ℝ} :
    ∫ x, (h x * Real.log (h x) - h x * Real.log c - h x + c) ∂μ =
      CutCur.entropyOf μ h + ((∫ x, h x ∂μ) * Real.log (∫ x, h x ∂μ) - (∫ x, h x ∂μ) * Real.log c -
        (∫ x, h x ∂μ) + c) := by
  unfold CutCur.entropyOf
  have hA : Integrable (fun x => h x * Real.log (h x) - h x * Real.log c) μ := h2.sub (h1.mul_const _)
  have hB : Integrable (fun x => h x * Real.log (h x) - h x * Real.log c - h x) μ := hA.sub h1
  rw [integral_add hB (integrable_const c), integral_sub hA h1, integral_sub h2 (h1.mul_const _),
    integral_mul_const]
  simp
  ring

/-- Lower bound for the entropy at a large constant. -/
theorem entropy_ge_scaled [IsProbabilityMeasure μ] (F : Form μ) {g : X → ℝ} (hg : g ∈ F.Q)
    (h0 : ∫ x, g x ∂μ = 0) {m : ℝ} (hm : 0 < m) :
    ∫ x, m ^ 2 * ψ (g x / m) ∂μ - (∫ x, g x ^ 2 ∂μ) ^ 2 / m ^ 2 ≤
      CutCur.entropyOf μ (fun x => (g x + m) ^ 2) := by
  have hf := F.add_const_mem m g hg
  have hI : ∫ x, m ^ 2 * ψ (g x / m) ∂μ = ∫ x, ((g x + m) ^ 2 * Real.log ((g x + m) ^ 2) -
      (g x + m) ^ 2 * Real.log (m ^ 2) - (g x + m) ^ 2 + m ^ 2) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => (scaled_identity hm).symm)
  rw [hI, integral_gibbs_eq (F.integrable_sq hf) (F.integrable_flog hf)]
  -- M = m² + ∫ g²
  have hM : ∫ x, (g x + m) ^ 2 ∂μ = m ^ 2 + ∫ x, g x ^ 2 ∂μ := by
    have : ∀ x, (g x + m) ^ 2 = g x ^ 2 + 2 * m * g x + m ^ 2 := fun x => by ring
    simp_rw [this]
    have i1 : Integrable (fun x => g x ^ 2 + 2 * m * g x) μ :=
      (F.integrable_sq hg).add ((F.integrable_self hg).const_mul _)
    have i2 : Integrable (fun x => 2 * m * g x) μ := (F.integrable_self hg).const_mul _
    rw [integral_add i1 (integrable_const _), integral_add (F.integrable_sq hg) i2, integral_const_mul, h0]
    simp
    ring
  set G := ∫ x, g x ^ 2 ∂μ with hG
  have hG0 : 0 ≤ G := integral_nonneg fun x => sq_nonneg _
  rw [hM]
  set M := m ^ 2 + G with hMdef
  have hMpos : 0 < M := by positivity
  -- defect bound
  have hdef : M * Real.log M - M * Real.log (m ^ 2) - M + m ^ 2 ≤ G ^ 2 / m ^ 2 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hMpos (by positivity : 0 < m ^ 2))
    have h2 : Real.log (M / m ^ 2) = Real.log M - Real.log (m ^ 2) := Real.log_div hMpos.ne' (by positivity)
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hMpos.le
    have h4 : M * (M / m ^ 2 - 1) - M + m ^ 2 = G ^ 2 / m ^ 2 := by
      rw [hMdef]; field_simp; ring
    linarith
  linarith

/-- Linearisation of the LSI at large constants: an LSI with constant `c` gives a Poincaré inequality with constant `c/2`. -/
theorem pi_of_lsi [IsProbabilityMeasure μ] (F : Form μ) {c : ℝ}
    (hc : ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f) {h : X → ℝ} (hh : h ∈ F.Q) :
    2 * variance h μ ≤ c * F.E h := by
  set a := ∫ x, h x ∂μ with ha
  set g : X → ℝ := fun x => h x + -a with hg
  have hgQ : g ∈ F.Q := F.add_const_mem _ _ hh
  have hg0 : ∫ x, g x ∂μ = 0 := by
    simp only [hg]
    rw [integral_add (F.integrable_self hh) (integrable_const _)]
    simp [ha]
  have hgE : F.E g = F.E h := F.E_add_const _ _ hh
  have hvar : variance h μ = ∫ x, g x ^ 2 ∂μ := by
    have : variance h μ = variance g μ := by
      simp only [hg]
      have := variance_add_const (F.memLp h hh).aestronglyMeasurable (-a)
      simpa using this.symm
    rw [this, variance_eq_of_mean_zero (F.memLp g hgQ) hg0]
  -- the limit
  have hlim : Tendsto (fun n : ℕ => ∫ x, ((n : ℝ) + 1) ^ 2 * ψ (g x / ((n : ℝ) + 1)) ∂μ) atTop
      (𝓝 (∫ x, 2 * g x ^ 2 ∂μ)) := by
    refine tendsto_scaled (g := fun _ => g) (h := g) (m := fun n : ℕ => (n : ℝ) + 1)
      (fun _ => F.memLp g hgQ) (fun _ => F.integrable_Θ g hgQ) (F.memLp g hgQ) (F.integrable_Θ g hgQ)
      (fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) ?_ (by simp) (by simp)
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlow : Tendsto (fun n : ℕ => (∫ x, ((n : ℝ) + 1) ^ 2 * ψ (g x / ((n : ℝ) + 1)) ∂μ) -
      (∫ x, g x ^ 2 ∂μ) ^ 2 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 (∫ x, 2 * g x ^ 2 ∂μ - 0)) := by
    refine hlim.sub ?_
    have : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa using tendsto_const_nhds.div_atTop this
  have hle : ∀ n : ℕ, (∫ x, ((n : ℝ) + 1) ^ 2 * ψ (g x / ((n : ℝ) + 1)) ∂μ) -
      (∫ x, g x ^ 2 ∂μ) ^ 2 / ((n : ℝ) + 1) ^ 2 ≤ c * F.E h := by
    intro n
    have hn : 0 < (n : ℝ) + 1 := by positivity
    refine (entropy_ge_scaled F hgQ hg0 hn).trans ?_
    have hf := F.add_const_mem ((n : ℝ) + 1) g hgQ
    have := hc _ hf
    rw [F.E_add_const _ _ hgQ, hgE] at this
    exact this
  have := le_of_tendsto' hlow hle
  rw [sub_zero, integral_const_mul] at this
  rw [hvar]; linarith

/-- `C_LSI ≥ 2 C_PI` (if the LSI holds with some constant). -/
theorem two_optPI_le_optLSI [IsProbabilityMeasure μ] (F : Form μ)
    (hLSI : ∃ c, 0 ≤ c ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f) :
    2 * F.optPI ≤ F.optLSI := by
  refine le_csInf hLSI fun c ⟨hc0, hc⟩ => ?_
  have : F.optPI ≤ c / 2 := by
    refine csInf_le ⟨0, fun _ h => h.1⟩ ⟨by positivity, fun f hf => ?_⟩
    have := pi_of_lsi F hc hf
    linarith
  linarith

/-- **Rothaus alternative, as in the manuscript**: if `C_LSI < ∞` and `C_LSI ≠ 2 C_PI`, there is an LSI extremal function. -/
theorem rothaus_alternative_ne [IsProbabilityMeasure μ] (F : Form μ)
    (hPI : ∃ P, 0 ≤ P ∧ ∀ f ∈ F.Q, variance f μ ≤ P * F.E f)
    (hLSI : ∃ c, 0 ≤ c ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f)
    (hcomp : F.Compact) (hne : F.optLSI ≠ 2 * F.optPI) :
    ∃ f ∈ F.Q, 0 < F.E f ∧ CutCur.entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f :=
  rothaus_alternative F hPI hcomp (lt_of_le_of_ne (two_optPI_le_optLSI F hLSI) (Ne.symm hne))

end CutoffRigidity.Rothaus
