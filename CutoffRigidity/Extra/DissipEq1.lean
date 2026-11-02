module

public import Mathlib

/-! # Integrated entropy dissipation from the reverse drop inequality (calculus step)

If `H r ≤ H (r + u) + u * I r` for all `r ≥ s`, `u > 0`, and `I` is nonnegative and antitone on
`[s, ∞)`, then `H s - H t ≤ ∫_s^t I` for `s < t`. This is the Riemann-sum argument for the upper
half of the integrated de Bruijn identity (dual of `Dissip.integral_le_sub_of_drop`).
-/

public section

namespace CutoffRigidity.DissipEq

open MeasureTheory Set Finset

theorem sub_le_integral_of_rdrop {H I : ℝ → ℝ} {s : ℝ}
    (hrdrop : ∀ r u : ℝ, s ≤ r → 0 < u → H r ≤ H (r + u) + u * I r)
    (hanti : AntitoneOn I (Ici s)) (hnn : ∀ r, s ≤ r → 0 ≤ I r) {t : ℝ} (hst : s < t) :
    H s - H t ≤ ∫ r in s..t, I r := by
  have hint : ∀ a b : ℝ, s ≤ a → a ≤ b → IntervalIntegrable I volume a b := fun a b ha hab =>
    (hanti.mono (by
      intro r hr
      rw [uIcc_of_le hab] at hr
      exact le_trans ha hr.1)).intervalIntegrable
  have key : ∀ n : ℕ, H s - H t ≤ (∫ r in s..t, I r) + ((t - s) / (n + 1)) * I s := by
    intro n
    set δ : ℝ := (t - s) / (n + 1) with hδ
    have hδpos : 0 < δ := by
      have : (0:ℝ) < n + 1 := by positivity
      rw [hδ]; exact div_pos (by linarith) this
    set F : ℕ → ℝ := fun i => s + i * δ with hF
    have hFge : ∀ i, s ≤ F i := fun i => by
      have : 0 ≤ (i : ℝ) * δ := by positivity
      simp only [hF]; linarith
    have hFsucc : ∀ i, F (i + 1) = F i + δ := fun i => by simp only [hF]; push_cast; ring
    have hF0 : F 0 = s := by simp [hF]
    have hFn : F (n + 1) = t := by
      simp only [hF]; push_cast; rw [hδ]; field_simp; ring
    have hmono : ∀ i, F i ≤ F (i + 1) := fun i => by rw [hFsucc]; linarith
    -- telescoping of H
    have hstep : ∀ i, H (F i) - H (F (i + 1)) ≤ δ * I (F i) := by
      intro i
      have h := hrdrop (F i) δ (hFge i) hδpos
      rw [← hFsucc] at h
      linarith
    have hsumH : H s - H t ≤ ∑ i ∈ range (n + 1), δ * I (F i) := by
      calc H s - H t = ∑ i ∈ range (n + 1), (H (F i) - H (F (i + 1))) := by
            rw [sum_range_sub', hF0, hFn]
        _ ≤ _ := sum_le_sum fun i _ => hstep i
    -- compare with integral
    have hpiece : ∀ i, δ * I (F (i + 1)) ≤ ∫ r in F i..F (i + 1), I r := by
      intro i
      have h1 : ∫ r in F i..F (i + 1), I (F (i + 1)) ≤ ∫ r in F i..F (i + 1), I r := by
        apply intervalIntegral.integral_mono_on (hmono i) intervalIntegrable_const
          (hint _ _ (hFge i) (hmono i))
        intro r hr
        exact hanti (show r ∈ Ici s from le_trans (hFge i) hr.1)
          (show F (i + 1) ∈ Ici s from hFge _) hr.2
      have hd : F (i + 1) - F i = δ := by rw [hFsucc]; ring
      rw [intervalIntegral.integral_const, smul_eq_mul, hd] at h1
      exact h1
    have hsum_int : ∫ r in s..F n, I r = ∑ i ∈ range n, ∫ r in F i..F (i + 1), I r := by
      rw [← hF0]
      rw [intervalIntegral.sum_integral_adjacent_intervals]
      intro i _
      exact hint _ _ (hFge i) (hmono i)
    have hFnle : F n ≤ t := by
      have := hmono n
      rw [hFn] at this; exact this
    have hrest : ∫ r in s..F n, I r ≤ ∫ r in s..t, I r := by
      have h1 : s ≤ F n := hFge n
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint _ _ le_rfl h1)
        (hint _ _ (hFge n) hFnle)]
      have : 0 ≤ ∫ r in F n..t, I r :=
        intervalIntegral.integral_nonneg hFnle fun r hr => hnn r (le_trans (hFge n) hr.1)
      linarith
    calc H s - H t ≤ ∑ i ∈ range (n + 1), δ * I (F i) := hsumH
      _ = δ * I s + ∑ i ∈ range n, δ * I (F (i + 1)) := by
          rw [sum_range_succ', hF0]; ring
      _ ≤ δ * I s + ∑ i ∈ range n, ∫ r in F i..F (i + 1), I r := by
          gcongr with i hi
          exact hpiece i
      _ = δ * I s + (∫ r in s..F n, I r) := by rw [hsum_int]
      _ ≤ (∫ r in s..t, I r) + δ * I s := by linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hIs : 0 ≤ I s := hnn s le_rfl
  obtain ⟨n, hn⟩ := exists_nat_gt ((t - s) * I s / ε)
  have := key n
  have h2 : (t - s) / (n + 1) * I s ≤ ε := by
    have hn1 : (0:ℝ) < n + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hn1]
    have := (div_lt_iff₀ hε).mp hn
    nlinarith
  linarith

end CutoffRigidity.DissipEq
