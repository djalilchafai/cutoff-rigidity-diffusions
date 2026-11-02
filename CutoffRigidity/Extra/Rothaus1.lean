module

public import Mathlib

/-! # Rothaus remark (stage 1): elementary real-variable estimates

The functions `Θ t = t² log (1+t²)` (Orlicz weight) and `ψ t = (1+t)² log (1+t)² - (1+t)² + 1`
(the integrand of the Gibbs variational upper bound for the entropy at the constant `m²`, after scaling `t = g/m`),
with the bounds used in the proof of the Rothaus alternative:
`ψ t ≤ 2t² + 9|t|³` for `|t| ≤ 1/2`, and `ψ t ≤ 32 t² + 9 Θ t` for `|t| ≥ 1/2`;
`|t² log t²| ≤ Θ t + 1`; `Θ (a+b) ≤ c_K (1 + b² + Θ b)` for `|a| ≤ K`.
-/

@[expose] public section

open Real

namespace CutoffRigidity.Rothaus

/-- Orlicz weight `Θ t = t² log (1 + t²)`. -/
noncomputable def Θ (t : ℝ) : ℝ := t ^ 2 * Real.log (1 + t ^ 2)

/-- `ψ t = (1+t)² log (1+t)² - (1+t)² + 1`. -/
noncomputable def ψ (t : ℝ) : ℝ := (1 + t) ^ 2 * Real.log ((1 + t) ^ 2) - (1 + t) ^ 2 + 1

theorem Θ_nonneg (t : ℝ) : 0 ≤ Θ t := by
  unfold Θ
  exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by nlinarith [sq_nonneg t]))

theorem continuous_Θ : Continuous Θ := by
  unfold Θ
  refine continuous_pow 2 |>.mul (Continuous.log (by fun_prop) fun t => by positivity)

/-- `|u log u| ≤ 1` for `0 ≤ u ≤ 1`. -/
theorem abs_mul_log_le_one {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |u * Real.log u| ≤ 1 := by
  rcases h0.eq_or_lt with rfl | hu
  · simp
  · have hl : Real.log u ≤ 0 := Real.log_nonpos h0 h1
    have hge : Real.log u ≥ 1 - 1 / u := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hu)
      rw [Real.log_inv] at this
      have h2 : (u⁻¹ : ℝ) = 1 / u := by simp
      linarith
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h0 hl)]
    have : u * Real.log u ≥ u - 1 := by
      have := mul_le_mul_of_nonneg_left hge h0
      have h3 : u * (1 - 1 / u) = u - 1 := by field_simp
      linarith
    linarith

/-- `|t² log t²| ≤ Θ t + 1`. -/
theorem abs_sq_mul_log_sq_le (t : ℝ) : |t ^ 2 * Real.log (t ^ 2)| ≤ Θ t + 1 := by
  by_cases h : t ^ 2 ≤ 1
  · have := abs_mul_log_le_one (sq_nonneg t) h
    linarith [Θ_nonneg t]
  · have h := not_le.1 h
    have h1 : 0 ≤ Real.log (t ^ 2) := Real.log_nonneg h.le
    have h2 : Real.log (t ^ 2) ≤ Real.log (1 + t ^ 2) := Real.log_le_log (by positivity) (by linarith)
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) h1)]
    unfold Θ
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg t)]

/-- Two-sided Taylor-type bound for `ψ` near `0`: `|ψ t - 2 t²| ≤ 10 |t|³`. -/
theorem ψ_sub_small {t : ℝ} (ht : |t| ≤ 1 / 2) : |ψ t - 2 * t ^ 2| ≤ 10 * |t| ^ 3 := by
  have hx : |-t| < 1 := by rw [abs_neg]; linarith
  have hR := Real.abs_log_sub_add_sum_range_le hx 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hR
  rw [abs_neg] at hR
  have hpos : 0 < 1 + t := by
    have := neg_abs_le t; linarith
  have e1 : (1 : ℝ) - -t = 1 + t := by ring
  rw [e1] at hR
  have hden : |t| ^ (2 + 1) / (1 - |t|) ≤ 2 * |t| ^ 3 := by
    have h1 : 1 / 2 ≤ 1 - |t| := by linarith
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ |t| ^ 3 := by positivity
    norm_num
    nlinarith
  set R := Real.log (1 + t) - t + t ^ 2 / 2 with hRdef
  have hRb : |R| ≤ 2 * |t| ^ 3 := by
    refine le_trans (le_of_eq ?_) (hR.trans hden)
    congr 1
    simp only [hRdef]; norm_num; ring
  have hlog : Real.log ((1 + t) ^ 2) = 2 * Real.log (1 + t) := by
    rw [Real.log_pow]; norm_num
  have hψ : ψ t - 2 * t ^ 2 = 2 * (1 + t) ^ 2 * R - t ^ 4 := by
    unfold ψ; rw [hlog, hRdef]; ring
  have h94 : (1 + t) ^ 2 ≤ 9 / 4 := by
    have := abs_le.1 ht; nlinarith
  have hb : |2 * (1 + t) ^ 2 * R| ≤ 9 * |t| ^ 3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (1 + t) ^ 2)]
    have h2 : 2 * (1 + t) ^ 2 * |R| ≤ 2 * (9 / 4) * (2 * |t| ^ 3) :=
      mul_le_mul (by linarith) hRb (abs_nonneg _) (by norm_num)
    linarith
  have h4 : t ^ 4 ≤ |t| ^ 3 / 2 := by
    have : t ^ 4 = |t| ^ 3 * |t| := by
      have := sq_abs t
      calc t ^ 4 = (t ^ 2) ^ 2 := by ring
        _ = (|t| ^ 2) ^ 2 := by rw [this]
        _ = _ := by ring
    rw [this]
    have : 0 ≤ |t| ^ 3 := by positivity
    nlinarith
  have h4' : 0 ≤ t ^ 4 := by positivity
  rw [hψ, abs_le]
  have := abs_le.1 hb
  constructor <;> nlinarith [pow_nonneg (abs_nonneg t) 3]

theorem ψ_le_small {t : ℝ} (ht : |t| ≤ 1 / 2) : ψ t ≤ 2 * t ^ 2 + 10 * |t| ^ 3 := by
  have := (abs_le.1 (ψ_sub_small ht)).2
  linarith

theorem ψ_nonneg (t : ℝ) : 0 ≤ ψ t := by
  unfold ψ
  set u := (1 + t) ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg _
  rcases hu0.eq_or_lt with h | h
  · rw [← h]; simp
  · have := Real.log_le_sub_one_of_pos (inv_pos.2 h)
    rw [Real.log_inv] at this
    have h2 := mul_le_mul_of_nonneg_left this h.le
    have : u * u⁻¹ = 1 := mul_inv_cancel₀ h.ne'
    nlinarith

/-- Global bound for `ψ` away from `0`. -/
theorem ψ_le_large {t : ℝ} (ht : 1 / 2 ≤ |t|) : ψ t ≤ 32 * t ^ 2 + 9 * Θ t := by
  have hu : (1 + t) ^ 2 ≤ 9 * t ^ 2 := by
    have h1 : |t| ≤ |t| := le_rfl
    have : (1 + t) ^ 2 ≤ (1 + |t|) ^ 2 := by
      have := le_abs_self t
      have := neg_abs_le t
      nlinarith [abs_nonneg t]
    have h3 : (1 + |t|) ^ 2 ≤ 9 * |t| ^ 2 := by nlinarith [abs_nonneg t]
    rw [sq_abs] at h3
    linarith
  set u := (1 + t) ^ 2 with hu0
  have hu_nn : 0 ≤ u := sq_nonneg _
  have ht2 : 1 / 4 ≤ t ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg t] : -|t| ≤ 1 / 2) (by linarith : 1 / 2 ≤ |t|) |> fun _ => 0
    nlinarith [abs_nonneg t, sq_abs t]
  have key : ψ t ≤ max 1 (u * Real.log (1 + u)) := by
    unfold ψ
    rw [← hu0]
    by_cases h : u ≤ 1
    · have : u * Real.log u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu_nn (Real.log_nonpos hu_nn h)
      exact le_max_of_le_left (by linarith)
    · have h := not_le.1 h
      refine le_max_of_le_right ?_
      have : Real.log u ≤ Real.log (1 + u) := Real.log_le_log (by linarith) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left this hu_nn]
  have h2 : u * Real.log (1 + u) ≤ 9 * t ^ 2 * Real.log (1 + 9 * t ^ 2) := by
    have h3 : Real.log (1 + u) ≤ Real.log (1 + 9 * t ^ 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
    calc u * Real.log (1 + u) ≤ 9 * t ^ 2 * Real.log (1 + u) :=
          mul_le_mul_of_nonneg_right hu this
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h4 : Real.log (1 + 9 * t ^ 2) ≤ 3 + Real.log (1 + t ^ 2) := by
    have : 1 + 9 * t ^ 2 ≤ Real.exp 3 * (1 + t ^ 2) := by
      have : (9 : ℝ) ≤ Real.exp 3 := by
        have h5 : (2.7 : ℝ) ≤ Real.exp 1 := by
          have := Real.exp_one_gt_d9; linarith
        have h6 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [h6]; nlinarith [sq_nonneg (Real.exp 1)]
      nlinarith [sq_nonneg t]
    calc Real.log (1 + 9 * t ^ 2) ≤ Real.log (Real.exp 3 * (1 + t ^ 2)) :=
          Real.log_le_log (by positivity) this
      _ = 3 + Real.log (1 + t ^ 2) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have h5 : 9 * t ^ 2 * Real.log (1 + 9 * t ^ 2) ≤ 27 * t ^ 2 + 9 * Θ t := by
    unfold Θ
    nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 9 * t ^ 2)]
  have h6 : (1 : ℝ) ≤ 4 * t ^ 2 := by linarith
  calc ψ t ≤ max 1 (u * Real.log (1 + u)) := key
    _ ≤ 32 * t ^ 2 + 9 * Θ t := by
      refine max_le ?_ ?_
      · nlinarith [Θ_nonneg t]
      · nlinarith [Θ_nonneg t]

/-- `Θ (a + b) ≤ c (1 + b² + Θ b)` when `|a| ≤ K`. -/
theorem Θ_add_le (K : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ a b : ℝ, |a| ≤ K → Θ (a + b) ≤ c * (1 + b ^ 2 + Θ b) := by
  set L : ℝ := Real.log (1 + 2 * K ^ 2) + Real.log 2 with hL
  have hL0 : 0 ≤ L := by
    have h1 : 0 ≤ Real.log (1 + 2 * K ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg K])
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  refine ⟨2 * K ^ 2 * L + 2 * L + 2 * K ^ 2 + 2, by positivity, fun a b ha => ?_⟩
  have hK : a ^ 2 ≤ K ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg a, neg_abs_le a] : -K ≤ a) (le_trans (le_abs_self a) ha)
    exact this
  have hs : (a + b) ^ 2 ≤ 2 * K ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hlog : Real.log (1 + (a + b) ^ 2) ≤ L + Real.log (1 + b ^ 2) := by
    have h1 : 1 + (a + b) ^ 2 ≤ (1 + 2 * K ^ 2) * (2 * (1 + b ^ 2)) := by
      nlinarith [sq_nonneg K, sq_nonneg b, mul_nonneg (sq_nonneg K) (sq_nonneg b)]
    calc Real.log (1 + (a + b) ^ 2) ≤ Real.log ((1 + 2 * K ^ 2) * (2 * (1 + b ^ 2))) :=
          Real.log_le_log (by positivity) h1
      _ = L + Real.log (1 + b ^ 2) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), hL]
          ring
  have hlb : Real.log (1 + b ^ 2) ≤ b ^ 2 := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + b ^ 2)
    linarith
  have hlb0 : 0 ≤ Real.log (1 + b ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg b])
  unfold Θ at *
  have h2 : (a + b) ^ 2 * Real.log (1 + (a + b) ^ 2) ≤ (2 * K ^ 2 + 2 * b ^ 2) * (L + Real.log (1 + b ^ 2)) :=
    mul_le_mul hs hlog (Real.log_nonneg (by nlinarith [sq_nonneg (a + b)])) (by positivity)
  have h3 : (2 * K ^ 2 + 2 * b ^ 2) * (L + Real.log (1 + b ^ 2)) ≤
      (2 * K ^ 2 * L + 2 * L + 2 * K ^ 2 + 2) * (1 + b ^ 2 + b ^ 2 * Real.log (1 + b ^ 2)) := by
    nlinarith [mul_nonneg (sq_nonneg K) hL0, mul_nonneg (sq_nonneg b) hL0, mul_nonneg (sq_nonneg K) hlb0,
      mul_nonneg (sq_nonneg K) (sub_nonneg.2 hlb), mul_nonneg (sq_nonneg b) hlb0, sq_nonneg K, sq_nonneg b,
      mul_nonneg (mul_nonneg (sq_nonneg K) hL0) (sq_nonneg b), mul_nonneg (sq_nonneg b) (sq_nonneg K)]
  linarith

end CutoffRigidity.Rothaus
