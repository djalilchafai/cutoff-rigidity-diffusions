module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus12

/-! # Rothaus remark (stage 19): tail estimates for the Orlicz weight under a Sobolev-type moment bound -/

@[expose] public section

open MeasureTheory Filter Topology Real

namespace CutoffRigidity.Rothaus

/-- For `R ≥ 1`, `|t| > R`: `Θ t ≤ (1 + 4/δ) R^{-δ/2} |t|^{2+δ}`. -/
theorem Θ_tail_le {δ R t : ℝ} (hδ : 0 < δ) (hR : 1 ≤ R) (ht : R < |t|) :
    Θ t ≤ (1 + 4 / δ) * R ^ (-(δ / 2)) * |t| ^ (2 + δ) := by
  have ht1 : 1 ≤ |t| := hR.trans ht.le
  have hpos : 0 < |t| := by linarith
  set ε : ℝ := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  have h1 : Real.log (1 + t ^ 2) ≤ Real.log 2 + 2 * Real.log |t| := by
    have : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by
      rw [sq_abs] at *
      nlinarith [sq_abs t, (one_le_sq_iff_one_le_abs t).2 ht1]
    calc Real.log (1 + t ^ 2) ≤ Real.log (2 * |t| ^ 2) := Real.log_le_log (by positivity) this
      _ = Real.log 2 + 2 * Real.log |t| := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
  have h2 : Real.log |t| ≤ |t| ^ ε / ε := Real.log_le_rpow_div (abs_nonneg t) hε0
  have h3 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have h4 : (1 : ℝ) ≤ |t| ^ ε := Real.one_le_rpow ht1 hε0.le
  have h5 : Real.log (1 + t ^ 2) ≤ (1 + 2 / ε) * |t| ^ ε := by
    have : 2 * Real.log |t| ≤ 2 * (|t| ^ ε / ε) := by linarith
    have e : 2 * (|t| ^ ε / ε) = 2 / ε * |t| ^ ε := by ring
    nlinarith
  have h6 : Θ t ≤ (1 + 2 / ε) * |t| ^ (2 + ε) := by
    unfold Θ
    have e : |t| ^ (2 + ε) = t ^ 2 * |t| ^ ε := by
      rw [Real.rpow_add hpos, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [e]
    have := mul_le_mul_of_nonneg_left h5 (sq_nonneg t)
    nlinarith
  have h7 : R ^ ε * |t| ^ (2 + ε) ≤ |t| ^ (2 + δ) := by
    have e : |t| ^ (2 + δ) = |t| ^ (2 + ε) * |t| ^ ε := by
      rw [← Real.rpow_add hpos]; congr 1; rw [hε]; ring
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) ht.le hε0.le) (by positivity)
  have hRε : 0 < R ^ ε := Real.rpow_pos_of_pos (by linarith) _
  have e2 : R ^ (-(δ / 2)) = (R ^ ε)⁻¹ := by rw [Real.rpow_neg (by linarith)]
  rw [e2]
  have hc : 1 + 2 / ε = 1 + 4 / δ := by rw [hε]; field_simp; ring
  rw [← hc]
  calc Θ t ≤ (1 + 2 / ε) * |t| ^ (2 + ε) := h6
    _ ≤ (1 + 2 / ε) * ((R ^ ε)⁻¹ * |t| ^ (2 + δ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [inv_mul_eq_div, le_div_iff₀ hRε]
        linarith
    _ = _ := by ring

theorem Θ_mono {a b : ℝ} (h : |a| ≤ |b|) : Θ a ≤ Θ b := by
  unfold Θ
  have h1 : a ^ 2 ≤ b ^ 2 := by rw [← sq_abs a, ← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h2 : Real.log (1 + a ^ 2) ≤ Real.log (1 + b ^ 2) := Real.log_le_log (by positivity) (by linarith)
  have h3 : 0 ≤ Real.log (1 + a ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg a])
  exact mul_le_mul h1 h2 h3 (sq_nonneg _)

theorem Θ_even (t : ℝ) : Θ (-t) = Θ t := by unfold Θ; simp

/-- Clamp to `[-R, R]`. -/
noncomputable def clampR (R t : ℝ) : ℝ := max (-R) (min t R)

theorem continuous_clampR (R : ℝ) : Continuous (clampR R) := by
  unfold clampR; fun_prop

theorem clampR_of_abs_le {R t : ℝ} (h : |t| ≤ R) : clampR R t = t := by
  rw [abs_le] at h
  unfold clampR
  rw [min_eq_left h.2, max_eq_right h.1]

theorem abs_clampR_le (R t : ℝ) (hR : 0 ≤ R) : |clampR R t| ≤ R := by
  unfold clampR
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem abs_clampR_le_abs (R t : ℝ) (hR : 0 ≤ R) : |clampR R t| ≤ |t| := by
  by_cases h : |t| ≤ R
  · rw [clampR_of_abs_le h]
  · have h := not_le.1 h
    -- |clamp| ≤ R < |t|
    exact (abs_clampR_le R t hR).trans h.le

/-- Pointwise decomposition of `|Θ a - Θ b|` through the clamped weight. -/
theorem abs_Θ_sub_le {R : ℝ} (hR : 0 ≤ R) (a b : ℝ) :
    |Θ a - Θ b| ≤ |Θ (clampR R a) - Θ (clampR R b)| + (if R < |a| then Θ a else 0) +
      (if R < |b| then Θ b else 0) := by
  have key : ∀ t : ℝ, |Θ t - Θ (clampR R t)| ≤ (if R < |t| then Θ t else 0) := by
    intro t
    by_cases h : |t| ≤ R
    · rw [clampR_of_abs_le h]; simp [not_lt.2 h]
    · have h' := not_le.1 h
      have hif : (if R < |t| then Θ t else 0) = Θ t := by simp [h']
      rw [hif]
      have h1 : Θ (clampR R t) ≤ Θ t := Θ_mono (abs_clampR_le_abs R t hR)
      rw [abs_of_nonneg (by linarith)]
      linarith [Θ_nonneg (clampR R t)]
  have ha := key a
  have hb := key b
  calc |Θ a - Θ b| = |(Θ a - Θ (clampR R a)) + (Θ (clampR R a) - Θ (clampR R b)) -
        (Θ b - Θ (clampR R b))| := by ring_nf
    _ ≤ |Θ a - Θ (clampR R a)| + |Θ (clampR R a) - Θ (clampR R b)| + |Θ b - Θ (clampR R b)| := by
        refine (abs_sub _ _).trans ?_
        have := abs_add_le (Θ a - Θ (clampR R a)) (Θ (clampR R a) - Θ (clampR R b))
        linarith
    _ ≤ _ := by linarith

end CutoffRigidity.Rothaus
