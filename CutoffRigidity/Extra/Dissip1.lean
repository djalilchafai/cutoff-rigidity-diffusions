module

public import Mathlib

/-! # Integrated entropy dissipation from the drop inequality (calculus step)

If `H t + (t - s) I t ≤ H s` for all `0 < s < t` and `I` is antitone on `(0, ∞)`, then
`∫_s^t I ≤ H s - H t` for `0 < s < t`. This is the Riemann-sum argument behind the lower half of
the de Bruijn identity (manuscript eq. `eq:HI`) for general initial laws.
-/

public section

namespace CutoffRigidity.Dissip

open MeasureTheory Set Finset

theorem integral_le_sub_of_drop {H I : ℝ → ℝ}
    (hdrop : ∀ s t : ℝ, 0 < s → s < t → H t + (t - s) * I t ≤ H s)
    (hanti : AntitoneOn I (Ioi 0)) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∫ r in s..t, I r ≤ H s - H t := by
  have hint : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable I volume a b := fun a b ha hab =>
    (hanti.mono (by
      intro r hr
      rw [uIcc_of_le hab] at hr
      exact lt_of_lt_of_le ha hr.1)).intervalIntegrable
  -- discrete estimate with `n+1` steps
  have key : ∀ n : ℕ, ∫ r in s..t, I r ≤
      H s - H t + ((t - s) / (n + 1)) * (I s - I t) := by
    intro n
    set δ : ℝ := (t - s) / (n + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set F : ℕ → ℝ := fun i => s + i * δ with hF
    have hFpos : ∀ i, 0 < F i := fun i => by
      have : 0 ≤ (i : ℝ) * δ := by positivity
      simp only [hF]; linarith
    have hFsucc : ∀ i, F (i + 1) = F i + δ := fun i => by simp only [hF]; push_cast; ring
    have hF0 : F 0 = s := by simp [hF]
    have hFn : F (n + 1) = t := by
      simp only [hF]; push_cast; rw [hδ]; field_simp; ring
    have hmono : ∀ i, F i < F (i + 1) := fun i => by rw [hFsucc]; linarith
    have hsum : ∫ r in s..t, I r = ∑ i ∈ range (n + 1), ∫ r in F i..F (i + 1), I r := by
      rw [← hF0, ← hFn]
      rw [intervalIntegral.sum_integral_adjacent_intervals]
      intro i _
      exact hint _ _ (hFpos i) (hmono i).le
    have hpiece : ∀ i, ∫ r in F i..F (i + 1), I r ≤ δ * I (F i) := by
      intro i
      have h1 : ∫ r in F i..F (i + 1), I r ≤ ∫ r in F i..F (i + 1), I (F i) := by
        apply intervalIntegral.integral_mono_on (hmono i).le (hint _ _ (hFpos i) (hmono i).le)
          intervalIntegrable_const
        intro r hr
        exact hanti (show F i ∈ Ioi (0:ℝ) from hFpos i)
          (show r ∈ Ioi (0:ℝ) from lt_of_lt_of_le (hFpos i) hr.1) hr.1
      have hd : F (i + 1) - F i = δ := by rw [hFsucc]; ring
      rw [intervalIntegral.integral_const, smul_eq_mul, hd] at h1
      exact h1
    have hstep : ∀ i, δ * I (F i) ≤ (H (F i) - H (F (i + 1))) + δ * (I (F i) - I (F (i + 1))) := by
      intro i
      have h := hdrop (F i) (F (i + 1)) (hFpos i) (hmono i)
      have hd : F (i + 1) - F i = δ := by rw [hFsucc]; ring
      rw [hd] at h
      nlinarith
    calc ∫ r in s..t, I r ≤ ∑ i ∈ range (n + 1), δ * I (F i) := by
          rw [hsum]; exact sum_le_sum fun i _ => hpiece i
      _ ≤ ∑ i ∈ range (n + 1), ((H (F i) - H (F (i + 1))) + δ * (I (F i) - I (F (i + 1)))) :=
          sum_le_sum fun i _ => hstep i
      _ = H s - H t + δ * (I s - I t) := by
          rw [sum_add_distrib, ← mul_sum, sum_range_sub', sum_range_sub', hF0, hFn]
  -- let the mesh go to zero
  have hnn : 0 ≤ I s - I t := sub_nonneg.mpr (hanti (show s ∈ Ioi (0:ℝ) from hs)
    (show t ∈ Ioi (0:ℝ) from hs.trans hst) hst.le)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt ((t - s) * (I s - I t) / ε)
  have := key n
  have h2 : (t - s) / (n + 1) * (I s - I t) ≤ ε := by
    have hn1 : (0:ℝ) < n + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hn1]
    have := (div_lt_iff₀ hε).mp hn
    nlinarith
  linarith

end CutoffRigidity.Dissip
