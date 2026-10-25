module

public import CutoffRigidity.Asymptotics
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Sublogarithmic curvature rates in the written entropy/Fisher cutoff proof

These analytic lemmas justify the two uses of `ρ = o(log d)` in the proof
of Corollary `co:cutoff:tv:H`: divergence of the critical time and absorption
of a fixed time shift into the negative dimension power. They assert no
probabilistic or functional inequality.
-/

public section

open Filter Topology

namespace CutoffRigidity

/-- The paper's sublogarithmic assumption makes its critical time diverge. -/
theorem criticalTime_tendsto_atTop_of_sublogarithmic {ρ : ℕ → ℝ}
    (hρ : ∀ᶠ n in atTop, 0 < ρ n)
    (hsub : Tendsto (fun n : ℕ => ρ n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => criticalTime n (ρ n)) atTop atTop := by
  have hpos : ∀ᶠ n in atTop, 0 < ρ n / Real.log (n : ℝ) := by
    filter_upwards [hρ, eventually_ge_atTop 2] with n hn hd
    exact div_pos hn (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  have hgt : Tendsto (fun n : ℕ => ρ n / Real.log (n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsub, hpos⟩
  have h := (tendsto_inv_nhdsGT_zero.comp hgt).atTop_div_const (by norm_num : (0 : ℝ) < 2)
  apply h.congr'
  filter_upwards [hρ] with n hn
  change (ρ n / Real.log (n : ℝ))⁻¹ / 2 = criticalTime n (ρ n)
  simp only [criticalTime, inv_div]
  field_simp

/-- A fixed positive time shift does not prevent the post-cutoff scale
from vanishing when the curvature rate is sublogarithmic. -/
theorem shifted_dimension_decay_tendsto_zero {ρ : ℕ → ℝ} {ε s : ℝ}
    (hρ : ∀ᶠ n in atTop, 0 < ρ n) (hε : 0 < ε) (hs : 0 ≤ s)
    (hsub : Tendsto (fun n : ℕ => ρ n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp
      (-2 * ρ n * ((1 + ε) * criticalTime n (ρ n) - s))) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n in atTop, ρ n / Real.log (n : ℝ) < ε / (4 * (s + 1)) :=
    hsub.eventually (gt_mem_nhds (div_pos hε (by positivity)))
  apply squeeze_zero' (Eventually.of_forall (fun n : ℕ => mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le))
    (g := fun n : ℕ => (n : ℝ) ^ (-(ε / 2)))
  · filter_upwards [hρ, hsmall, eventually_ge_atTop 2] with n hn hq hd
    have hd1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hd1
    have hd0 : (0 : ℝ) < n := by positivity
    have hsmall' := (div_lt_iff₀ hlog).mp hq
    have hcoeff : 2 * ρ n * s ≤ ε / 2 * Real.log (n : ℝ) := by
      have haux : ρ n * (4 * (s + 1)) < ε * Real.log (n : ℝ) := by
        exact (lt_div_iff₀ (by positivity : 0 < 4 * (s + 1))).mp
          (by simpa only [div_mul_eq_mul_div] using hsmall')
      nlinarith
    have heq : -2 * ρ n * ((1 + ε) * criticalTime n (ρ n) - s) =
        -(1 + ε) * Real.log (n : ℝ) + 2 * ρ n * s := by
      unfold criticalTime
      field_simp
      ring
    rw [heq, Real.rpow_def_of_pos hd0]
    calc
      (n : ℝ) * Real.exp (-(1 + ε) * Real.log (n : ℝ) + 2 * ρ n * s) ≤
          (n : ℝ) * Real.exp ((-1 - ε / 2) * Real.log (n : ℝ)) := by
        gcongr
        nlinarith
      _ = Real.exp (Real.log (n : ℝ) * (-(ε / 2))) := by
        conv_lhs => lhs; rw [← Real.exp_log hd0]
        rw [← Real.exp_add]
        congr 1
        ring
  · exact power_after_cutoff (by positivity : 0 < ε / 2)

/-- The preceding critical-time conclusion with the paper's literal
little-o hypothesis. -/
theorem criticalTime_tendsto_atTop_of_isLittleO {ρ : ℕ → ℝ}
    (hρ : ∀ᶠ n in atTop, 0 < ρ n)
    (hsub : ρ =o[atTop] (fun n : ℕ => Real.log (n : ℝ))) :
    Tendsto (fun n : ℕ => criticalTime n (ρ n)) atTop atTop :=
  criticalTime_tendsto_atTop_of_sublogarithmic hρ hsub.tendsto_div_nhds_zero

/-- The post-cutoff scale with a fixed time shift, written using exactly
the sublogarithmic hypothesis from the paper. -/
theorem shifted_dimension_decay_tendsto_zero_of_isLittleO {ρ : ℕ → ℝ} {ε s : ℝ}
    (hρ : ∀ᶠ n in atTop, 0 < ρ n) (hε : 0 < ε) (hs : 0 ≤ s)
    (hsub : ρ =o[atTop] (fun n : ℕ => Real.log (n : ℝ))) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp
      (-2 * ρ n * ((1 + ε) * criticalTime n (ρ n) - s))) atTop (𝓝 0) :=
  shifted_dimension_decay_tendsto_zero hρ hε hs hsub.tendsto_div_nhds_zero

end CutoffRigidity
