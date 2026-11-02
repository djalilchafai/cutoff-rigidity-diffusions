module

public import CutoffRigidity.Extra.C2Uniq3
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # `C²` uniqueness, stage 4a: radial cutoffs and their one-sided generator control -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open Bundle
open scoped ENNReal NNReal ContDiff Manifold

namespace C2U

variable {d : ℕ}

/-- Profile of the radial cutoff: `1` on `(-∞,1]`, `0` on `[4,∞)`, smooth, nonincreasing. -/
noncomputable def theta (t : ℝ) : ℝ := Real.smoothTransition ((4 - t) / 3)

theorem theta_contDiff : ContDiff ℝ ∞ theta :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem theta_nonneg (t : ℝ) : 0 ≤ theta t := Real.smoothTransition.nonneg _

theorem theta_le_one (t : ℝ) : theta t ≤ 1 := Real.smoothTransition.le_one _

theorem theta_of_le_one {t : ℝ} (h : t ≤ 1) : theta t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem theta_of_ge_four {t : ℝ} (h : 4 ≤ t) : theta t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem deriv_theta_nonpos (t : ℝ) : deriv theta t ≤ 0 := by
  have hanti : Antitone theta := by
    intro s t hst
    exact Real.smoothTransition.monotone (by linarith)
  exact hanti.deriv_nonpos

theorem deriv_theta_eq_zero {t : ℝ} (h : t ∉ Icc (1 : ℝ) 4) : deriv theta t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · have : theta =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      exact theta_of_le_one hs.le
    rw [this.deriv_eq]; simp
  · have : theta =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      exact theta_of_ge_four hs.le
    rw [this.deriv_eq]; simp

theorem deriv_deriv_theta_eq_zero {t : ℝ} (h : t ∉ Icc (1 : ℝ) 4) : deriv (deriv theta) t = 0 := by
  have : deriv theta =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds h] with s hs
    exact deriv_theta_eq_zero hs
  rw [this.deriv_eq]; simp

theorem contDiff_deriv_theta : ContDiff ℝ ∞ (deriv theta) :=
  (contDiff_infty_iff_deriv.mp theta_contDiff).2

theorem contDiff_deriv_deriv_theta : ContDiff ℝ ∞ (deriv (deriv theta)) :=
  (contDiff_infty_iff_deriv.mp contDiff_deriv_theta).2

theorem exists_theta_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv theta t| ≤ B ∧ |deriv (deriv theta) t| ≤ B := by
  have h1 : Continuous (deriv theta) := (contDiff_deriv_theta.continuous)
  have h2 : Continuous (deriv (deriv theta)) := contDiff_deriv_deriv_theta.continuous
  have hc1 : HasCompactSupport (deriv theta) :=
    HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 4)) fun t ht => deriv_theta_eq_zero ht
  have hc2 : HasCompactSupport (deriv (deriv theta)) :=
    HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 4)) fun t ht => deriv_deriv_theta_eq_zero ht
  obtain ⟨B1, hB1⟩ := h1.bounded_above_of_compact_support hc1
  obtain ⟨B2, hB2⟩ := h2.bounded_above_of_compact_support hc2
  refine ⟨max (max B1 B2) 0, le_max_right _ _, fun t => ⟨?_, ?_⟩⟩
  · have := hB1 t; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have := hB2 t; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))


/-- Radial profile composed with `c‖y‖²`. -/
noncomputable def cutc (c : ℝ) (y : Rd d) : ℝ := theta (c * ‖y‖ ^ 2)

theorem cutc_contDiff (c : ℝ) : ContDiff ℝ ∞ (cutc (d := d) c) :=
  theta_contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem hasFDerivAt_comp_normsq {θ : ℝ → ℝ} {θ' : ℝ} (c : ℝ) (x : Rd d)
    (hθ : HasDerivAt θ θ' (c * ‖x‖ ^ 2)) :
    HasFDerivAt (fun y : Rd d => θ (c * ‖y‖ ^ 2)) ((θ' * (2 * c)) • innerSL ℝ x) x := by
  have hq : HasFDerivAt (fun y : Rd d => c * ‖y‖ ^ 2) (c • 2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul c
  have h2 : HasFDerivAt (θ ∘ fun y : Rd d => c * ‖y‖ ^ 2) (θ' • c • 2 • innerSL ℝ x) x :=
    hθ.comp_hasFDerivAt x hq
  have e : (θ' * (2 * c)) • innerSL ℝ x = θ' • c • 2 • innerSL ℝ x := by
    ext z
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [e]; exact h2

theorem hasFDerivAt_cutc (c : ℝ) (x : Rd d) :
    HasFDerivAt (cutc c) ((deriv theta (c * ‖x‖ ^ 2) * (2 * c)) • innerSL ℝ x) x :=
  hasFDerivAt_comp_normsq c x (((theta_contDiff.differentiable (by simp)) _).hasDerivAt)

theorem fderiv_cutc (c : ℝ) (x : Rd d) :
    fderiv ℝ (cutc c) x = (deriv theta (c * ‖x‖ ^ 2) * (2 * c)) • innerSL ℝ x :=
  (hasFDerivAt_cutc c x).fderiv

theorem gradient_cutc (c : ℝ) (x : Rd d) :
    gradient (cutc c) x = (deriv theta (c * ‖x‖ ^ 2) * (2 * c)) • x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, fderiv_cutc]
  simp [real_inner_smul_right, real_inner_comm]


theorem laplacian_cutc (c : ℝ) (x : Rd d) :
    laplacian (cutc c) x = 2 * c * d * deriv theta (c * ‖x‖ ^ 2) +
      4 * c ^ 2 * deriv (deriv theta) (c * ‖x‖ ^ 2) * ‖x‖ ^ 2 := by
  have hθ' : ∀ y : Rd d, HasDerivAt (deriv theta) (deriv (deriv theta) (c * ‖y‖ ^ 2)) (c * ‖y‖ ^ 2) :=
    fun y => ((contDiff_deriv_theta.differentiable (by simp)) _).hasDerivAt
  have hm : HasFDerivAt (fun y : Rd d => deriv theta (c * ‖y‖ ^ 2) * (2 * c))
      ((((deriv (deriv theta) (c * ‖x‖ ^ 2)) * (2 * c)) * (2 * c)) • innerSL ℝ x) x := by
    have := (hasFDerivAt_comp_normsq (θ := deriv theta) c x (hθ' x)).mul_const (2 * c)
    convert this using 1
    ext z; simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  have hI : HasFDerivAt (⇑(innerSL ℝ : Rd d →L[ℝ] Rd d →L[ℝ] ℝ)) (innerSL ℝ) x :=
    (innerSL ℝ : Rd d →L[ℝ] Rd d →L[ℝ] ℝ).hasFDerivAt
  have hsm := hm.smul hI
  have hfd : fderiv ℝ (cutc (d := d) c) =
      fun y => (deriv theta (c * ‖y‖ ^ 2) * (2 * c)) • innerSL ℝ y := funext (fderiv_cutc c)
  set I : Rd d →L[ℝ] Rd d →L[ℝ] ℝ := innerSL ℝ with hIdef
  have h2 : fderiv ℝ (fderiv ℝ (cutc (d := d) c)) x =
      (deriv theta (c * ‖x‖ ^ 2) * (2 * c)) • I +
        ((((deriv (deriv theta) (c * ‖x‖ ^ 2)) * (2 * c)) * (2 * c)) • I x).smulRight
          (I x) := by
    rw [hfd]; exact hsm.fderiv
  unfold laplacian
  rw [h2]
  have hI1 : ∀ i : Fin d, I (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 1 := by
    intro i
    have : I (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
        inner ℝ (EuclideanSpace.single i (1 : ℝ) : Rd d) (EuclideanSpace.single i 1) := rfl
    rw [this]; simp
  have hI2 : ∀ i : Fin d, I x (EuclideanSpace.single i 1) = x i := by
    intro i
    have : I x (EuclideanSpace.single i 1) = inner ℝ x (EuclideanSpace.single i (1 : ℝ) : Rd d) := rfl
    rw [this]; simp [EuclideanSpace.inner_single_right]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hI1, hI2]
  have hn : ‖x‖ ^ 2 = ∑ i, x i * x i := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]; ring
  set K1 := deriv theta (c * ‖x‖ ^ 2) * (2 * c) with hK1
  set K2 := deriv (deriv theta) (c * ‖x‖ ^ 2) * (2 * c) * (2 * c) with hK2
  have hs : ∑ i : Fin d, (K1 * 1 + K2 * x i * x i) = K1 * d + K2 * ‖x‖ ^ 2 := by
    rw [hn, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hs, hK1, hK2]
  ring


/-- Radial cutoffs of scale `R ≥ 1` with the one-sided control of `⟨∇V, ∇χ⟩` coming from convexity
(`⟨∇V(y), y⟩ ≥ -a ‖y‖`). -/
theorem exists_cutoff (V : Rd d → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hVa : ∀ y, -(a * ‖y‖) ≤ inner ℝ (gradient V y) y) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∃ χ : Rd d → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y, ‖y‖ ≤ R → χ y = 1) ∧ (∀ y, 2 * R ≤ ‖y‖ → χ y = 0) ∧
      (∀ y, ‖gradient χ y‖ ≤ A / R) ∧
      (∀ y, |laplacian χ y| ≤ A / R ^ 2) ∧ (∀ y, inner ℝ (gradient V y) (gradient χ y) ≤ A / R) := by
  obtain ⟨B, hB0, hB⟩ := exists_theta_bound
  refine ⟨(20 + 2 * d) * B * (1 + a), by positivity, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  have hcd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hA1 : 4 * B ≤ (20 + 2 * d) * B * (1 + a) := by
    nlinarith [mul_nonneg hB0 ha, mul_nonneg hB0 hcd, mul_nonneg (mul_nonneg hB0 hcd) ha]
  have hA2 : (2 * d + 16) * B ≤ (20 + 2 * d) * B * (1 + a) := by
    nlinarith [mul_nonneg hB0 ha, mul_nonneg hB0 hcd, mul_nonneg (mul_nonneg hB0 hcd) ha]
  have hA3 : 4 * B * a ≤ (20 + 2 * d) * B * (1 + a) := by
    nlinarith [mul_nonneg hB0 ha, mul_nonneg hB0 hcd, mul_nonneg (mul_nonneg hB0 hcd) ha]
  set c : ℝ := 1 / R ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hcR : c * R ^ 2 = 1 := by rw [hc]; field_simp
  -- support facts
  have hsupp : ∀ y : Rd d, 2 * R ≤ ‖y‖ → cutc c y = 0 := by
    intro y hy
    apply theta_of_ge_four
    have : (2 * R) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
    nlinarith
  -- bounds where the derivatives of θ are nonzero
  have hq4 : ∀ y : Rd d, deriv theta (c * ‖y‖ ^ 2) ≠ 0 ∨ deriv (deriv theta) (c * ‖y‖ ^ 2) ≠ 0 →
      ‖y‖ ≤ 2 * R := by
    intro y h
    by_contra hy
    rw [not_le] at hy
    have : (2 * R) ^ 2 < ‖y‖ ^ 2 := pow_lt_pow_left₀ hy (by positivity) (by norm_num)
    have hq : 4 < c * ‖y‖ ^ 2 := by nlinarith
    have h1 : c * ‖y‖ ^ 2 ∉ Icc (1 : ℝ) 4 := fun hm => absurd hm.2 (not_le.2 hq)
    rcases h with h | h
    · exact h (deriv_theta_eq_zero h1)
    · exact h (deriv_deriv_theta_eq_zero h1)
  refine ⟨cutc c, cutc_contDiff c, HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) (2 * R)) ?_,
    fun y => ⟨theta_nonneg _, theta_le_one _⟩, ?_, hsupp, ?_, ?_, ?_⟩
  · intro y hy
    apply hsupp
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact hy.le
  · intro y hy
    apply theta_of_le_one
    have : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    nlinarith
  · intro y
    rw [gradient_cutc, norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases h0 : deriv theta (c * ‖y‖ ^ 2) = 0
    · rw [h0]; simp; positivity
    · have hy := hq4 y (Or.inl h0)
      have h1 := (hB (c * ‖y‖ ^ 2)).1
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * c)]
      calc |deriv theta (c * ‖y‖ ^ 2)| * (2 * c) * ‖y‖ ≤ B * (2 * c) * (2 * R) := by gcongr
        _ = 4 * B / R := by rw [hc]; field_simp; ring
        _ ≤ (20 + 2 * d) * B * (1 + a) / R := div_le_div_of_nonneg_right hA1 hR0.le
  · intro y
    rw [laplacian_cutc]
    by_cases h0 : deriv theta (c * ‖y‖ ^ 2) = 0 ∧ deriv (deriv theta) (c * ‖y‖ ^ 2) = 0
    · rw [h0.1, h0.2]; simp; positivity
    · have hy := hq4 y (by by_contra hh; push_neg at hh; exact h0 hh)
      have h1 := (hB (c * ‖y‖ ^ 2)).1
      have h2 := (hB (c * ‖y‖ ^ 2)).2
      have hy2 : ‖y‖ ^ 2 ≤ 4 * R ^ 2 := by nlinarith [norm_nonneg y]
      calc |2 * c * d * deriv theta (c * ‖y‖ ^ 2) + 4 * c ^ 2 * deriv (deriv theta) (c * ‖y‖ ^ 2) * ‖y‖ ^ 2|
          ≤ |2 * c * d * deriv theta (c * ‖y‖ ^ 2)| +
            |4 * c ^ 2 * deriv (deriv theta) (c * ‖y‖ ^ 2) * ‖y‖ ^ 2| := abs_add_le _ _
        _ ≤ 2 * c * d * B + 4 * c ^ 2 * B * (4 * R ^ 2) := by
          gcongr
          · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c * d)]
            gcongr
          · rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * c ^ 2),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)]
            gcongr
        _ = (2 * d + 16) * B / R ^ 2 := by rw [hc]; field_simp; ring
        _ ≤ (20 + 2 * d) * B * (1 + a) / R ^ 2 := div_le_div_of_nonneg_right hA2 (by positivity)
  · intro y
    rw [gradient_cutc, inner_smul_right]
    by_cases h0 : deriv theta (c * ‖y‖ ^ 2) = 0
    · rw [h0]; simp; positivity
    · have hy := hq4 y (Or.inl h0)
      have h1 := (hB (c * ‖y‖ ^ 2)).1
      have hneg := deriv_theta_nonpos (c * ‖y‖ ^ 2)
      have hin := hVa y
      have hb : |deriv theta (c * ‖y‖ ^ 2)| = - deriv theta (c * ‖y‖ ^ 2) := abs_of_nonpos hneg
      have hk : 0 ≤ 2 * c := by positivity
      calc deriv theta (c * ‖y‖ ^ 2) * (2 * c) * inner ℝ (gradient V y) y
          = (-deriv theta (c * ‖y‖ ^ 2)) * (2 * c) * (-(inner ℝ (gradient V y) y)) := by ring
        _ ≤ (-deriv theta (c * ‖y‖ ^ 2)) * (2 * c) * (a * ‖y‖) := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            exact mul_nonneg (by linarith) hk
        _ ≤ B * (2 * c) * (a * (2 * R)) := by
            have : -deriv theta (c * ‖y‖ ^ 2) ≤ B := by rw [← hb]; exact h1
            gcongr
        _ = 4 * B * a / R := by rw [hc]; field_simp; ring
        _ ≤ (20 + 2 * d) * B * (1 + a) / R := div_le_div_of_nonneg_right hA3 hR0.le

end C2U

end CutCur
