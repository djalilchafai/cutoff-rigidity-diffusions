module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus10

/-! # Rothaus remark (stage 11): normalised minimising sequences -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- If `0 < optLSI`, there are `u_n ∈ Q` with `Ent(u_n²) = 1`, nonnegative mean, and `E(u_n) → 1/optLSI`
(from above, at rate `1/(C (n+1))`). -/
theorem exists_normalized [IsProbabilityMeasure μ] (F : Form μ)
    (hLSI : ∃ c, 0 ≤ c ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f)
    (hC : 0 < F.optLSI) :
    ∃ u : ℕ → X → ℝ, (∀ n, u n ∈ F.Q) ∧ (∀ n, CutCur.entropyOf μ (fun x => u n x ^ 2) = 1) ∧
      (∀ n, 0 ≤ ∫ x, u n x ∂μ) ∧ (∀ n, 1 / F.optLSI ≤ F.E (u n)) ∧
      (∀ n : ℕ, F.E (u n) ≤ 1 / F.optLSI + 1 / (F.optLSI * (n + 1))) := by
  set C := F.optLSI with hCdef
  have key : ∀ n : ℕ, ∃ u ∈ F.Q, CutCur.entropyOf μ (fun x => u x ^ 2) = 1 ∧ 0 ≤ ∫ x, u x ∂μ ∧
      1 / C ≤ F.E u ∧ F.E u ≤ 1 / C + 1 / (C * (n + 1)) := by
    intro n
    set c : ℝ := C * (n + 1) / (n + 2) with hc
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hn2 : (0 : ℝ) < n + 2 := by positivity
    have hcpos : 0 < c := by positivity
    have hclt : c < C := by
      rw [hc, div_lt_iff₀ hn2]; nlinarith
    obtain ⟨f, hf, hfe⟩ := F.exists_gt_of_lt_optLSI hcpos.le hclt
    set e := CutCur.entropyOf μ (fun x => f x ^ 2) with he
    have hE0 := F.E_nonneg f hf
    have hepos : 0 < e := lt_of_le_of_lt (mul_nonneg hcpos.le hE0) hfe
    set a : ℝ := 1 / Real.sqrt e with ha
    have ha2 : a ^ 2 = 1 / e := by
      rw [ha, div_pow, Real.sq_sqrt hepos.le]; simp
    have hapos : 0 < a ^ 2 := by rw [ha2]; positivity
    have hu0 : a • f ∈ F.Q := F.smul_mem a f hf
    have hent : CutCur.entropyOf μ (fun x => (a • f) x ^ 2) = 1 := by
      have : (fun x => (a • f) x ^ 2) = fun x => a ^ 2 * f x ^ 2 := by
        funext x; simp [smul_eq_mul, mul_pow]
      rw [this, entropyOf_const_mul hapos (F.integrable_sq hf) (F.integrable_flog hf), ← he, ha2]
      field_simp
    have hE : F.E (a • f) = F.E f / e := by
      rw [F.E_smul a f hf, ha2]; field_simp
    obtain ⟨v, hv, hv2, hvE, hv0⟩ := F.exists_sign hu0
    have hent' : CutCur.entropyOf μ (fun x => v x ^ 2) = 1 := by
      have : (fun x => v x ^ 2) = fun x => (a • f) x ^ 2 := funext hv2
      rw [this, hent]
    refine ⟨v, hv, hent', hv0, ?_, ?_⟩
    · have := F.lsi_spec hLSI hv
      rw [hent'] at this
      rw [div_le_iff₀ hC]
      linarith [mul_comm C (F.E v)]
    · rw [hvE, hE]
      have h1 : F.E f / e ≤ 1 / c := by
        rw [div_le_div_iff₀ hepos hcpos]; linarith
      have h2 : 1 / c = 1 / C + 1 / (C * (n + 1)) := by
        rw [hc]; field_simp; ring
      linarith
  choose u hu using key
  exact ⟨u, fun n => (hu n).1, fun n => (hu n).2.1, fun n => (hu n).2.2.1, fun n => (hu n).2.2.2.1,
    fun n => (hu n).2.2.2.2⟩

end CutoffRigidity.Rothaus
