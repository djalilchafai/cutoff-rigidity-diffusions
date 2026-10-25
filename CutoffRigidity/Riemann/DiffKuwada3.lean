module

public import CutoffRigidity.Riemann.DiffKuwada2

/-! # Interpolation along a `C^1` curve: assembly -/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Assembly

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

include F

/-- Continuity of `τ ↦ W (r τ) (γ τ)` on `[η, 1]`. -/
theorem curve_G_continuousOn {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ)
    {W : ℝ → M → ℝ} (h1 : ∀ r, 0 < r → MSmooth F (W r)) {r : ℝ → ℝ} (hrc : Continuous r)
    {η r0 C2 : ℝ} (hrr : ∀ τ ∈ Icc η 1, r0 ≤ r τ ∧ r τ ≤ 1) (hr0 : 0 < r0)
    (h2 : ∀ r s y, r0 ≤ r → r ≤ 1 → r0 ≤ s → s ≤ 1 → |W r y - W s y| ≤ C2 * |r - s|) :
    ContinuousOn (fun τ => W (r τ) (γ τ)) (Icc η 1) := by
  intro σ hσ
  have hσpos : 0 < r σ := lt_of_lt_of_le hr0 (hrr σ hσ).1
  have hc1 : ContinuousAt (fun τ => W (r σ) (γ τ)) σ :=
    ((h1 (r σ) hσpos).continuous.comp hγ.continuous).continuousAt
  have hd : Tendsto (fun τ => W (r τ) (γ τ) - W (r σ) (γ τ)) (𝓝[Icc η 1] σ) (𝓝 0) := by
    have hb : Tendsto (fun τ => C2 * |r τ - r σ|) (𝓝[Icc η 1] σ) (𝓝 0) := by
      have hcont : Continuous (fun τ => C2 * |r τ - r σ|) := by fun_prop
      have := hcont.tendsto σ
      rw [show C2 * |r σ - r σ| = 0 by simp] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [Real.norm_eq_abs]
    exact h2 _ _ _ (hrr τ hτ).1 (hrr τ hτ).2 (hrr σ hσ).1 (hrr σ hσ).2
  have := hd.add (hc1.tendsto.mono_left (nhdsWithin_le_nhds (s := Icc η 1)))
  simp only [zero_add] at this
  refine this.congr (fun τ => ?_)
  ring

/-- The fixed-`κ` interpolation inequality. -/
theorem curve_interp_aux {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ)
    {c : ℝ} {W : ℝ → M → ℝ} {W0 : M → ℝ} {Sg : ℝ → M → ℝ}
    (h1 : ∀ r, 0 < r → MSmooth F (W r))
    (h2 : ∀ r₀, 0 < r₀ → ∃ C : ℝ, ∀ r s y, r₀ ≤ r → r ≤ 1 → r₀ ≤ s → s ≤ 1 →
      |W r y - W s y| ≤ C * |r - s|)
    (h3 : ∀ r₀, 0 < r₀ → ∃ C : ℝ, ∀ r s, r₀ ≤ r → r ≤ 1 → r₀ ≤ s → s ≤ 1 →
      ∀ τ ∈ Set.Icc (0:ℝ) 1,
        ‖mgrad F (W r) (γ τ) - mgrad F (W s) (γ τ)‖ ≤ C * |r - s|)
    (h4 : ∀ r, 0 < r → ∀ y, ‖mgrad F (W r) y‖ ^ 2 ≤ c ^ 2 * Sg r y)
    (h5 : ∀ r, 0 < r → ∀ y, 0 ≤ Sg r y ∧ ∀ s, r < s →
      (W s y - W r y) / (s - r) ≤ -(1 / 2) * (r / s) * Sg r y)
    (h6 : Continuous W0 ∧ ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → ∀ y, |W r y - W0 y| ≤ C * r)
    {κ : ℝ} (hκ : 0 < κ) :
    W (1 / 2) (γ 1) - W0 (γ 0) ≤
      c ^ 2 * ((∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖) + κ) *
        (∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖) := by
  set v : ℝ → ℝ := fun τ => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ with hvdef
  have hvc : Continuous v := continuous_speed F hγ
  have hv0 : ∀ τ, 0 ≤ v τ := fun τ => norm_nonneg _
  have hint : ∀ a b : ℝ, IntervalIntegrable v volume a b := fun a b => hvc.intervalIntegrable a b
  set ℓ : ℝ := ∫ τ in (0:ℝ)..1, v τ with hℓ
  have hℓ0 : 0 ≤ ℓ := intervalIntegral.integral_nonneg zero_le_one (fun τ _ => hv0 τ)
  set K : ℝ := ℓ + κ with hKdef
  have hK : 0 < K := by positivity
  set r : ℝ → ℝ := fun τ => ((∫ s in (0:ℝ)..τ, v s) + κ * τ) / (2 * K) with hrdef
  have hr : ∀ τ, HasDerivAt r ((v τ + κ) / (2 * K)) τ := by
    intro τ
    have := ((hvc.integral_hasStrictDerivAt 0 τ).hasDerivAt.add
      ((hasDerivAt_id τ).const_mul κ)).div_const (2 * K)
    simpa [hrdef] using this
  have hrc : Continuous r := continuous_iff_continuousAt.2 fun τ => (hr τ).continuousAt
  have hr_0 : r 0 = 0 := by simp [hrdef]
  have hr_1 : r 1 = 1 / 2 := by
    simp only [hrdef, mul_one]
    rw [← hℓ, ← hKdef]; field_simp
  have hmono : StrictMono r := by
    refine strictMono_of_deriv_pos (fun τ => ?_)
    rw [(hr τ).deriv]
    have := hv0 τ
    positivity
  -- Lipschitz bound of r
  obtain ⟨V, hV⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := v) (s := Icc (0:ℝ) 1)
    hvc.continuousOn
  have hlip : ∀ τ ∈ Icc (0:ℝ) 1, ∀ σ ∈ Icc (0:ℝ) 1,
      |r σ - r τ| ≤ ((V + κ) / (2 * K)) * |σ - τ| := by
    intro τ hτ σ hσ
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := r) (s := Icc (0:ℝ) 1) (C := (V + κ) / (2 * K)) (x := τ) (y := σ)
      (f' := fun τ => (v τ + κ) / (2 * K))
      (fun x _ => (hr x).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := hv0 x; positivity)]
        have := (hV x hx); rw [Real.norm_eq_abs] at this
        have := le_abs_self (v x)
        gcongr; linarith)
      (convex_Icc 0 1) hτ hσ
    simpa [Real.norm_eq_abs] using this
  have hr_le : ∀ τ ∈ Icc (0:ℝ) 1, r τ ≤ 1 / 2 := fun τ hτ => hr_1 ▸ hmono.monotone hτ.2
  -- main inequality for η
  have hmain : ∀ η ∈ Ioo (0:ℝ) 1, W (r 1) (γ 1) ≤ W (r η) (γ η) + c ^ 2 * K * ℓ := by
    intro η hη
    have hr0 : 0 < r η := hr_0 ▸ hmono hη.1
    obtain ⟨C2, hC2⟩ := h2 (r η) hr0
    obtain ⟨C3, hC3⟩ := h3 (r η) hr0
    have hrr : ∀ τ ∈ Icc η 1, r η ≤ r τ ∧ r τ ≤ 1 := fun τ hτ =>
      ⟨hmono.monotone hτ.1, (hr_le τ ⟨hη.1.le.trans hτ.1, hτ.2⟩).trans (by norm_num)⟩
    have hGc := curve_G_continuousOn F hγ h1 hrc hrr hr0 hC2
    have hL : ∀ τ ∈ Icc η 1, ∀ σ ∈ Icc η 1, |r σ - r τ| ≤ ((V + κ) / (2 * K)) * |σ - τ| :=
      fun τ hτ σ hσ => hlip τ ⟨hη.1.le.trans hτ.1, hτ.2⟩ σ ⟨hη.1.le.trans hσ.1, hσ.2⟩
    have hdini := curve_dini_step F hγ hK hκ h1 h4 h5 hr (fun τ σ h => hmono h) hη.1.le hr0 hrr hL hC3
    have key : ∀ ε > 0, W (r 1) (γ 1) ≤ W (r η) (γ η) + c ^ 2 * K * (∫ s in η..1, v s) +
        ε * (1 - η) := by
      intro ε hε
      have := image_le_of_liminf_slope_right_lt_deriv_boundary'
        (f := fun τ => W (r τ) (γ τ)) (f' := fun x => c ^ 2 * K * v x) (a := η) (b := 1)
        hGc
        (fun x hx ρ hρ => (hdini x hx ρ (by simpa [hvdef, mul_assoc] using hρ)).frequently)
        (B := fun x => W (r η) (γ η) + c ^ 2 * K * (∫ s in η..x, v s) + ε * (x - η))
        (B' := fun x => c ^ 2 * K * v x + ε)
        (by simp)
        (by
          have : Continuous fun x => W (r η) (γ η) + c ^ 2 * K * (∫ s in η..x, v s) + ε * (x - η) :=
            (continuous_const.add (continuous_const.mul
              (intervalIntegral.continuous_primitive hint η))).add
              (continuous_const.mul (continuous_id.sub continuous_const))
          exact this.continuousOn)
        (fun x hx => by
          have h' := (((hvc.integral_hasStrictDerivAt η x).hasDerivAt.const_mul (c ^ 2 * K)).const_add
            (W (r η) (γ η))).add (((hasDerivAt_id x).sub_const η).const_mul ε)
          have h'' : HasDerivAt (fun x => W (r η) (γ η) + c ^ 2 * K * (∫ s in η..x, v s) +
              ε * (x - η)) (c ^ 2 * K * v x + ε) x := by
            convert h' using 1
            · rfl
            · simp
          exact h''.hasDerivWithinAt)
        (fun x hx _ => by show c ^ 2 * K * v x < c ^ 2 * K * v x + ε; linarith)
        (x := 1) ⟨hη.2.le, le_rfl⟩
      simpa using this
    have hle : ∫ s in η..1, v s ≤ ℓ := by
      have := intervalIntegral.integral_add_adjacent_intervals (hint 0 η) (hint η 1)
      have h0 : 0 ≤ ∫ s in (0:ℝ)..η, v s :=
        intervalIntegral.integral_nonneg hη.1.le (fun τ _ => hv0 τ)
      linarith
    have hcK : 0 ≤ c ^ 2 * K := by positivity
    have := mul_le_mul_of_nonneg_left hle hcK
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have := key (ε / 2) (by linarith)
    have h12 : (ε / 2) * (1 - η) ≤ ε := by nlinarith [hη.1, hη.2]
    linarith
  -- η → 0
  obtain ⟨hW0, C6, hC6⟩ := h6
  have hlim : Tendsto (fun η => W (r η) (γ η)) (𝓝[>] 0) (𝓝 (W0 (γ 0))) := by
    have hb : Tendsto (fun η => |C6| * r η) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous (fun η => |C6| * r η) := by fun_prop
      have := hcont.tendsto 0
      rw [hr_0, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hd : Tendsto (fun η => W (r η) (γ η) - W0 (γ η)) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with η hη
      rw [Real.norm_eq_abs]
      have hrp : 0 < r η := hr_0 ▸ hmono hη.1
      exact (hC6 (r η) hrp ((hr_le η ⟨hη.1.le, hη.2⟩).trans (by norm_num)) (γ η)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) hrp.le)
    have hc : Tendsto (fun η => W0 (γ η)) (𝓝[>] 0) (𝓝 (W0 (γ 0))) :=
      ((hW0.comp hγ.continuous).tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using hd.add hc
  have hfin : W (r 1) (γ 1) - c ^ 2 * K * ℓ ≤ W0 (γ 0) := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with η hη
    have := hmain η hη
    linarith
  rw [hr_1] at hfin
  linarith

/-- **Interpolation along a `C^1` curve.** -/
theorem curve_interpolation {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ)
    {c : ℝ} {W : ℝ → M → ℝ} {W0 : M → ℝ} {Sg : ℝ → M → ℝ}
    (h1 : ∀ r, 0 < r → MSmooth F (W r))
    (h2 : ∀ r₀, 0 < r₀ → ∃ C : ℝ, ∀ r s y, r₀ ≤ r → r ≤ 1 → r₀ ≤ s → s ≤ 1 →
      |W r y - W s y| ≤ C * |r - s|)
    (h3 : ∀ r₀, 0 < r₀ → ∃ C : ℝ, ∀ r s, r₀ ≤ r → r ≤ 1 → r₀ ≤ s → s ≤ 1 →
      ∀ τ ∈ Set.Icc (0:ℝ) 1,
        ‖mgrad F (W r) (γ τ) - mgrad F (W s) (γ τ)‖ ≤ C * |r - s|)
    (h4 : ∀ r, 0 < r → ∀ y, ‖mgrad F (W r) y‖ ^ 2 ≤ c ^ 2 * Sg r y)
    (h5 : ∀ r, 0 < r → ∀ y, 0 ≤ Sg r y ∧ ∀ s, r < s →
      (W s y - W r y) / (s - r) ≤ -(1 / 2) * (r / s) * Sg r y)
    (h6 : Continuous W0 ∧ ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → ∀ y, |W r y - W0 y| ≤ C * r) :
    W (1 / 2) (γ 1) - W0 (γ 0) ≤
      c ^ 2 * (∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖) ^ 2 := by
  set ℓ : ℝ := ∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ with hℓ
  have hℓ0 : 0 ≤ ℓ := intervalIntegral.integral_nonneg zero_le_one (fun τ _ => norm_nonneg _)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hκ : 0 < ε / (c ^ 2 * ℓ + 1) := by positivity
  have := curve_interp_aux F hγ h1 h2 h3 h4 h5 h6 hκ
  have hq : c ^ 2 * ℓ * (ε / (c ^ 2 * ℓ + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg c) hℓ0]
  nlinarith [hq]

end Assembly

end CutoffRigidity.Riemann.Diff
