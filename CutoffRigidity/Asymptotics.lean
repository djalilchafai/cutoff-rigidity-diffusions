module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Scalar estimates at the logarithmic cutoff time

These are conditional analytic ingredients of Corollary 1.3 of
Chafaï–Fathi, arXiv:2412.15969v4. They do not construct a diffusion or
prove the Wasserstein estimates needed to apply them.
-/

public section

open Filter Topology

namespace CutoffRigidity

/-- The critical time appearing in Corollary 1.3. -/
@[expose] noncomputable def criticalTime (dimension rate : ℝ) : ℝ := Real.log dimension / (2 * rate)

/-- Exact cancellation of the spectral gap at a multiple of the critical time. -/
theorem decay_at_criticalTime (dimension rate factor : ℝ)
    (hdimension : 0 < dimension) (hrate : rate ≠ 0) :
    Real.exp (-2 * rate * (factor * criticalTime dimension rate)) =
      dimension ^ (-factor) := by
  rw [Real.rpow_def_of_pos hdimension]
  congr 1
  unfold criticalTime
  field_simp


/-- Multiplication by the dimension leaves the expected power. -/
theorem dimension_decay_at_criticalTime (dimension rate factor : ℝ)
    (hdimension : 0 < dimension) (hrate : rate ≠ 0) :
    dimension * Real.exp (-2 * rate * (factor * criticalTime dimension rate)) =
      dimension ^ (1 - factor) := by
  rw [decay_at_criticalTime dimension rate factor hdimension hrate]
  rw [sub_eq_add_neg, Real.rpow_add hdimension, Real.rpow_one]

/-- The upper-bound scale tends to zero after the critical time. -/
theorem power_after_cutoff {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop

/-- The lower-bound scale diverges before the critical time. -/
theorem power_before_cutoff {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
  (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop

/-- A nonnegative quantity bounded by the post-cutoff scale converges to zero. -/
theorem upper_bound_transfer {D : ℕ → ℝ} {C ε : ℝ} (hε : 0 < ε)
    (hnonneg : ∀ᶠ n in atTop, 0 ≤ D n)
    (hbound : ∀ᶠ n in atTop, D n ≤ C * (n : ℝ) ^ (-ε)) :
    Tendsto D atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    simpa using (power_after_cutoff hε).const_mul C
  exact squeeze_zero' hnonneg hbound hscale

/-- A quantity bounded below by a positive pre-cutoff scale diverges. -/
theorem lower_bound_transfer {D : ℕ → ℝ} {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hbound : ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ ε ≤ D n) :
    Tendsto D atTop atTop := by
  exact tendsto_atTop_mono' _ hbound ((power_before_cutoff hε).const_mul_atTop hc)

/-- Conditional post-cutoff conclusion from an exponential upper bound.
The bound is supplied explicitly; no diffusion estimate is assumed implicitly. -/
theorem exponential_upper_cutoff {D rate : ℕ → ℝ} {C ε : ℝ} (hε : 0 < ε)
    (hrate : ∀ n, rate n ≠ 0)
    (hnonneg : ∀ᶠ n in atTop, 0 ≤ D n)
    (hbound : ∀ᶠ n : ℕ in atTop,
      D n ≤ C * ((n : ℝ) * Real.exp
        (-2 * rate n * ((1 + ε) * criticalTime n (rate n))))) :
    Tendsto D atTop (𝓝 0) := by
  apply upper_bound_transfer hε hnonneg
  filter_upwards [hbound, eventually_ge_atTop 1] with n hn hnpos
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [dimension_decay_at_criticalTime n (rate n) (1 + ε) hpos (hrate n)] at hn
  simpa only [show (1 : ℝ) - (1 + ε) = -ε by ring] using hn

/-- Conditional pre-cutoff conclusion from an exponential lower bound.
For squared distances one can use this theorem with `D n = distance n ^ 2`. -/
theorem exponential_lower_cutoff {D rate : ℕ → ℝ} {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hrate : ∀ n, rate n ≠ 0)
    (hbound : ∀ᶠ n : ℕ in atTop,
      c * ((n : ℝ) * Real.exp
        (-2 * rate n * ((1 - ε) * criticalTime n (rate n)))) ≤ D n) :
    Tendsto D atTop atTop := by
  apply lower_bound_transfer hc hε
  filter_upwards [hbound, eventually_ge_atTop 1] with n hn hnpos
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [dimension_decay_at_criticalTime n (rate n) (1 - ε) hpos (hrate n)] at hn
  simpa only [show (1 : ℝ) - (1 - ε) = ε by ring] using hn

end CutoffRigidity
