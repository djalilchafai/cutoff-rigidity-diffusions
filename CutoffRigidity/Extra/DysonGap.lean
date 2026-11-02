module

public import CutoffRigidity.Extra.Dyson7

/-! # Dyson--OU: spectral gap as the Rayleigh infimum over `C_c^∞(ℝ^d)` (stage 1: cutoffs) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal NNReal

namespace CutoffRigidity.Dyson

variable {d : ℕ}

/-- A fixed smooth bump on `ℝ^d`, equal to `1` on the unit ball and supported in the ball of radius `2`. -/
noncomputable def bump (d : ℕ) : ContDiffBump (0 : CutCur.Rd d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The dilated cutoff `χ_R(x) = bump(x / R)`. -/
noncomputable def cut (d : ℕ) (R : ℝ) (x : CutCur.Rd d) : ℝ := bump d (R⁻¹ • x)

theorem cut_contDiff (R : ℝ) : ContDiff ℝ ∞ (cut d R) :=
  ((bump d).contDiff (n := ⊤)).comp (contDiff_const_smul _)

theorem cut_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (cut d R) :=
  (bump d).hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))

theorem cut_nonneg (R : ℝ) (x : CutCur.Rd d) : 0 ≤ cut d R x := (bump d).nonneg
theorem cut_le_one (R : ℝ) (x : CutCur.Rd d) : cut d R x ≤ 1 := (bump d).le_one

theorem cut_eq_one {R : ℝ} (hR : 0 < R) {x : CutCur.Rd d} (hx : ‖x‖ ≤ R) : cut d R x = 1 := by
  apply (bump d).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hR]
  show R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]; simpa using hx

/-- Uniform gradient bound `‖∇χ_R‖ ≤ M / R`. -/
theorem exists_fderiv_cut_bound :
    ∃ M : ℝ, ∀ R : ℝ, 0 < R → ∀ x : CutCur.Rd d, ‖fderiv ℝ (cut d R) x‖ ≤ M / R := by
  obtain ⟨M, hM⟩ := ((bump d).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (((bump d).contDiff (n := ⊤)).continuous_fderiv (by simp))
  refine ⟨M, fun R hR x => ?_⟩
  have h1 : HasFDerivAt (fun y : CutCur.Rd d => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ _) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have h2 := (((bump d).contDiff (n := ⊤)).differentiable (by simp) (R⁻¹ • x)).hasFDerivAt.comp x h1
  have e : fderiv ℝ (cut d R) x = (fderiv ℝ (bump d) (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ _) :=
    h2.fderiv
  rw [e]
  calc _ ≤ ‖fderiv ℝ (bump d) (R⁻¹ • x)‖ * ‖R⁻¹ • ContinuousLinearMap.id ℝ (CutCur.Rd d)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * R⁻¹ := by
        have hn : ‖R⁻¹ • ContinuousLinearMap.id ℝ (CutCur.Rd d)‖ ≤ R⁻¹ :=
          calc _ ≤ ‖R⁻¹‖ * ‖ContinuousLinearMap.id ℝ (CutCur.Rd d)‖ := norm_smul_le _ _
            _ ≤ ‖R⁻¹‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
            _ = R⁻¹ := by simp [abs_of_pos hR]
        exact mul_le_mul (hM _) hn (norm_nonneg _) ((norm_nonneg _).trans (hM 0))
    _ = M / R := by ring

/-- The compactly supported approximants `f_R = χ_R · h`, `h = x_1 + ⋯ + x_d`. -/
noncomputable def fR (d : ℕ) (R : ℝ) (x : CutCur.Rd d) : ℝ := cut d R x * hsum d x

theorem hsum_contDiff : ContDiff ℝ ∞ (hsum d) := by
  have : hsum d = innerSL ℝ (CutCur.diagonal d) := funext fun y => hsum_eq_inner y
  rw [this]; exact (innerSL ℝ (CutCur.diagonal d)).contDiff

theorem fR_contDiff (R : ℝ) : ContDiff ℝ ∞ (fR d R) := (cut_contDiff R).mul hsum_contDiff

theorem fR_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (fR d R) :=
  (cut_compact hR).mul_right

theorem norm_gradient_eq (f : CutCur.Rd d → ℝ) (x : CutCur.Rd d) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

theorem fderiv_fR (R : ℝ) (x : CutCur.Rd d) :
    fderiv ℝ (fR d R) x = cut d R x • innerSL ℝ (CutCur.diagonal d) + hsum d x • fderiv ℝ (cut d R) x := by
  have h1 := ((cut_contDiff (d := d) R).differentiable (by simp) x).hasFDerivAt
  exact (h1.mul (hasFDerivAt_hsum x)).fderiv

theorem norm_fderiv_hsum_sq : ‖innerSL ℝ (CutCur.diagonal d)‖ ^ 2 = d := by
  have h := gradient_hsum_sq (d := d) 0
  rw [norm_gradient_eq, (hasFDerivAt_hsum (d := d) 0).fderiv] at h
  exact h

/-- Pointwise gradient bound for the cutoff approximants. -/
theorem norm_gradient_fR_sq_le {M R : ℝ} (hR : 0 < R)
    (hM : ∀ x : CutCur.Rd d, ‖fderiv ℝ (cut d R) x‖ ≤ M / R) (x : CutCur.Rd d) :
    ‖gradient (fR d R) x‖ ^ 2 ≤ (1 + 1 / R) * d + (1 + R) * (M / R) ^ 2 * hsum d x ^ 2 := by
  rw [norm_gradient_eq]
  set A := ‖innerSL ℝ (CutCur.diagonal d)‖ with hA
  have hA2 := norm_fderiv_hsum_sq (d := d)
  have hMR : 0 ≤ M / R := (norm_nonneg _).trans (hM 0)
  set a := cut d R x * A with ha
  set b := |hsum d x| * (M / R) with hb
  have h0 : ‖fderiv ℝ (fR d R) x‖ ≤ a + b := by
    rw [fderiv_fR]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg R x)]
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  have ha0 : 0 ≤ a := mul_nonneg (cut_nonneg R x) (norm_nonneg _)
  have hb0 : 0 ≤ b := mul_nonneg (abs_nonneg _) hMR
  have ha2 : a ^ 2 ≤ d := by
    rw [ha, mul_pow, ← hA2]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (cut_nonneg R x) (cut_le_one R x))
  have hb2 : b ^ 2 = (M / R) ^ 2 * hsum d x ^ 2 := by
    rw [hb, mul_pow, sq_abs]; ring
  have h1 : (a + b) ^ 2 ≤ (1 + 1 / R) * a ^ 2 + (1 + R) * b ^ 2 := by
    have : 2 * a * b ≤ a ^ 2 / R + R * b ^ 2 := by
      rw [← sub_nonneg]
      have : a ^ 2 / R + R * b ^ 2 - 2 * a * b = (a - R * b) ^ 2 / R := by field_simp; ring
      rw [this]; positivity
    have e : a ^ 2 / R = 1 / R * a ^ 2 := by ring
    nlinarith [this, e]
  calc ‖fderiv ℝ (fR d R) x‖ ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
    _ ≤ (1 + 1 / R) * a ^ 2 + (1 + R) * b ^ 2 := h1
    _ ≤ (1 + 1 / R) * d + (1 + R) * b ^ 2 := by gcongr
    _ = (1 + 1 / R) * d + (1 + R) * (M / R) ^ 2 * hsum d x ^ 2 := by rw [hb2]; ring

end CutoffRigidity.Dyson
