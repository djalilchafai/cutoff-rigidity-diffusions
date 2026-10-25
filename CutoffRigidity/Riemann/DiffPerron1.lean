module

public import CutoffRigidity.Riemann.DiffPerron0
public import CutoffRigidity.Riemann.DiffForm
public import CutoffRigidity.Riemann.WeightedSmoothing
public import CutoffRigidity.Riemann.WeightedProper
public import CutoffRigidity.Riemann.WeightedCutoffs
public import CutoffRigidity.Riemann.WeightedPointwise

/-! # Smooth proper function and energy maximum principle (workstream PENAL, P2)

* `exists_smooth_proper`: a smooth proper `ζ ≥ 0` on a complete connected Riemannian manifold.
* `energy_max_principle`: a bounded smooth subsolution `(lam + κ) w ≤ 𝓛 w` on `{w > 0}` is `≤ 0`
  (Gaffney cutoffs, finite measure, test function `η² G(w)`, `G(s) = exp(-1/s)`).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Proper

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- A smooth nonnegative proper function. -/
theorem exists_smooth_proper :
    ∃ ζ : M → ℝ, MSmooth F ζ ∧ (∀ x, 0 ≤ ζ x) ∧ ∀ c, IsCompact {x | ζ x ≤ c} := by
  by_cases hne : Nonempty M
  · obtain ⟨x₀⟩ := hne
    haveI := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
    have hfin := edist_ne_top_of_connected (F := F) (M := M)
    set f : M → ℝ := fun x => (edist x₀ x).toReal with hfdef
    have hf : LipschitzWith 1 f := by
      intro x y
      simp only [ENNReal.coe_one, one_mul]
      have hxy : |f x - f y| ≤ (edist x y).toReal := by
        have h1 : edist x₀ x ≤ edist x₀ y + edist y x := edist_triangle _ _ _
        have h2 : edist x₀ y ≤ edist x₀ x + edist x y := edist_triangle _ _ _
        have t1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩) h1
        have t2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩) h2
        rw [ENNReal.toReal_add (hfin _ _) (hfin _ _)] at t1 t2
        rw [edist_comm y x] at t1
        rw [abs_le]
        constructor <;> simp only [hfdef] <;> linarith
      rw [edist_dist, Real.dist_eq]
      calc ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal (edist x y).toReal :=
            ENNReal.ofReal_le_ofReal hxy
        _ = edist x y := ENNReal.ofReal_toReal (hfin _ _)
    obtain ⟨ψ, hψs, hψf, -⟩ := exists_smooth_lip_approx F hfin hf
    have hf0 : ∀ x, 0 ≤ f x := fun x => ENNReal.toReal_nonneg
    refine ⟨fun x => ψ x + 1, hψs.add contMDiff_const, fun x => ?_, fun c => ?_⟩
    · have := (abs_le.1 (hψf x)).1
      linarith [hf0 x]
    · by_cases hc : 0 ≤ c
      · refine (isCompact_edist_le F x₀ hc).of_isClosed_subset ?_ ?_
        · exact isClosed_le (hψs.continuous.add continuous_const) continuous_const
        · intro x hx
          have h1 : f x ≤ c := by
            have := (abs_le.1 (hψf x)).1
            have hx' : ψ x + 1 ≤ c := hx
            linarith
          show edist x₀ x ≤ ENNReal.ofReal c
          calc edist x₀ x = ENNReal.ofReal (f x) := (ENNReal.ofReal_toReal (hfin _ _)).symm
            _ ≤ _ := ENNReal.ofReal_le_ofReal h1
      · push Not at hc
        have : {x : M | ψ x + 1 ≤ c} = ∅ := by
          ext x
          simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
          have := (abs_le.1 (hψf x)).1
          linarith [hf0 x]
        rw [this]; exact isCompact_empty
  · refine ⟨fun _ => 0, contMDiff_const, fun _ => le_rfl, fun c => ?_⟩
    have : IsEmpty M := not_nonempty_iff.1 hne
    exact (Set.toFinite _).isCompact

end Proper


section Energy

/-- The smooth function `G(s) = exp(-1/s)` for `s > 0`, `0` otherwise. -/
noncomputable abbrev Gfun : ℝ → ℝ := _root_.expNegInvGlue

theorem Gfun_contDiff : ContDiff ℝ ∞ Gfun := expNegInvGlue.contDiff

theorem Gfun_nonneg (s : ℝ) : 0 ≤ Gfun s := expNegInvGlue.nonneg s

theorem Gfun_le_one (s : ℝ) : Gfun s ≤ 1 := by
  by_cases hs : s ≤ 0
  · show expNegInvGlue s ≤ 1
    rw [expNegInvGlue.zero_of_nonpos hs]; exact zero_le_one
  · push Not at hs
    show expNegInvGlue s ≤ 1
    simp only [expNegInvGlue, not_le.2 hs, ite_false]
    rw [Real.exp_le_one_iff]
    have := inv_pos.2 hs
    linarith

theorem deriv_Gfun_nonneg (s : ℝ) : 0 ≤ deriv Gfun s :=
  expNegInvGlue.monotone.deriv_nonneg

theorem Gfun_eq_deriv_mul {s : ℝ} (hs : 0 < s) : Gfun s = deriv Gfun s * s ^ 2 := by
  have h1 : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s := hasDerivAt_inv hs.ne'
  have h2 := (h1.neg).exp
  have h3 : (fun t : ℝ => Real.exp (-t⁻¹)) =ᶠ[𝓝 s] Gfun := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp [expNegInvGlue, not_le.2 (show 0 < t from ht)]
  have h4 : HasDerivAt Gfun (Real.exp (-s⁻¹) * -(-(s ^ 2)⁻¹)) s := h2.congr_of_eventuallyEq h3.symm
  rw [h4.deriv]
  have : Gfun s = Real.exp (-s⁻¹) := by
    simp [expNegInvGlue, not_le.2 hs]
  rw [this]
  field_simp

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV hμ

/-- One step of the energy argument, for a cutoff `η` with `‖∇η‖ ≤ δ`. -/
theorem energy_step {η : M → ℝ} (hη : MSmooth F η) (hηc : HasCompactSupport η) {δ : ℝ}
    (hδ : ∀ x, ‖mgrad F η x‖ ≤ δ) {w : M → ℝ} (hw : MSmooth F w) {C : ℝ}
    (hb : ∀ x, |w x| ≤ C) {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} (hκ : ∀ x, 0 ≤ κ x)
    (h : ∀ x, 0 < w x → (lam + κ x) * w x ≤ mgenerator F V w x) :
    lam * ∫ x, η x * η x * Gfun (w x) * w x ∂μ ≤ C ^ 2 * δ ^ 2 * (μ Set.univ).toReal := by
  have hGs := Gfun_contDiff
  have hGw : MSmooth F (fun y => Gfun (w y)) := hGs.contMDiff.comp hw
  have hηη : MSmooth F (fun y => η y * η y) := hη.mul hη
  set u : M → ℝ := (fun y => η y * η y) * (fun y => Gfun (w y)) with hu
  have hus : MSmooth F u := hηη.mul hGw
  have huc : HasCompactSupport u := (hηc.mul_right (f' := η)).mul_right
  have hIBP := weightedIBP_of_isWeightedVolume F hV hμ u w hus hw huc
  -- continuity facts
  have hLw : MSmooth F (mgenerator F V w) := msmooth_mgenerator F hV hw
  have hint1 : Integrable (fun x => u x * mgenerator F V w x) μ :=
    ((hus.continuous.mul hLw.continuous)).integrable_of_hasCompactSupport huc.mul_right
  have hint2 : Integrable (fun x => u x * w x) μ :=
    ((hus.continuous.mul hw.continuous)).integrable_of_hasCompactSupport huc.mul_right
  have hcar : MSmooth F (carre F u w) := (weightedRegular V hV).1 _ _ hus hw
  have hint3 : Integrable (fun x => carre F u w x) μ :=
    hcar.continuous.integrable_of_hasCompactSupport (hasCompactSupport_carre F _ huc)
  -- P1
  have P1 : ∀ x, lam * (u x * w x) ≤ u x * mgenerator F V w x := by
    intro x
    have hux : 0 ≤ u x := by
      simp only [hu, Pi.mul_apply]
      exact mul_nonneg (mul_self_nonneg _) (Gfun_nonneg _)
    by_cases hwx : 0 < w x
    · have := h x hwx
      have hk : 0 ≤ κ x * w x := mul_nonneg (hκ x) hwx.le
      nlinarith [mul_le_mul_of_nonneg_left this hux]
    · push Not at hwx
      have : u x = 0 := by
        simp only [hu, Pi.mul_apply, expNegInvGlue.zero_of_nonpos hwx, mul_zero]
      simp [this]
  -- P2
  have P2 : ∀ x, -carre F u w x ≤ C ^ 2 * δ ^ 2 := by
    intro x
    have hc1 : carre F u w x = (η x * η x) * (deriv Gfun (w x) * carre F w w x) +
        Gfun (w x) * (η x * carre F η w x + η x * carre F η w x) := by
      have e1 := carre_mul_left F (f := fun y => η y * η y) (g := fun y => Gfun (w y)) (h := w)
        hηη hGw x
      have e2 := carre_comp_left F hGs hw w x
      have e3 := carre_mul_left F (f := η) (g := η) (h := w) hη hη x
      have e4 : carre F u w x = (η x * η x) * carre F (fun y => Gfun (w y)) w x +
          Gfun (w x) * carre F (fun y => η y * η y) w x := e1
      rw [e4]
      have e5 : carre F (fun y => Gfun (w y)) w x = deriv Gfun (w x) * carre F w w x := e2
      have e6 : carre F (fun y => η y * η y) w x = η x * carre F η w x + η x * carre F η w x := e3
      rw [e5, e6]
    set a := ‖mgrad F η x‖ with ha
    set b := ‖mgrad F w x‖ with hbdef
    have hww : carre F w w x = b ^ 2 := carre_self_eq F w x
    have hcs : |carre F η w x| ≤ a * b := abs_carre_le F η w x
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have had : a ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ ha0 (hδ x) 2
    set g' := deriv Gfun (w x) with hg'
    set g := Gfun (w x) with hg
    have hg'0 : 0 ≤ g' := deriv_Gfun_nonneg _
    have hg0 : 0 ≤ g := Gfun_nonneg _
    have hC2 : 0 ≤ C ^ 2 := sq_nonneg _
    have hbound : C ^ 2 * a ^ 2 ≤ C ^ 2 * δ ^ 2 := mul_le_mul_of_nonneg_left had hC2
    rw [hc1, hww]
    set e := η x with he
    have hX : -(2 * e * g * carre F η w x) ≤ 2 * |e| * g * (a * b) := by
      have : -(2 * e * g * carre F η w x) ≤ |2 * e * g * carre F η w x| := neg_le_abs _
      rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hg0] at this
      calc _ ≤ _ := this
        _ ≤ 2 * |e| * g * (a * b) := by
          have := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 2 * |e| * g)
          linarith
    by_cases hwx : 0 < w x
    · have hgw : g = g' * w x ^ 2 := Gfun_eq_deriv_mul hwx
      have hw2 : w x ^ 2 ≤ C ^ 2 := by
        have := hb x
        have h0 : 0 ≤ w x := hwx.le
        rw [abs_of_nonneg h0] at this
        nlinarith
      have hg1 : g ≤ 1 := Gfun_le_one _
      have hgw2 : g' * (w x) ^ 4 ≤ C ^ 2 := by
        calc g' * (w x) ^ 4 = g * w x ^ 2 := by rw [hgw]; ring
          _ ≤ 1 * C ^ 2 := mul_le_mul hg1 hw2 (sq_nonneg _) zero_le_one
          _ = C ^ 2 := one_mul _
      have key : 0 ≤ g' * (|e| * b - w x ^ 2 * a) ^ 2 + (C ^ 2 - g' * w x ^ 4) * a ^ 2 :=
        add_nonneg (mul_nonneg hg'0 (sq_nonneg _))
          (mul_nonneg (by linarith) (sq_nonneg _))
      have hid : g' * (|e| * b - w x ^ 2 * a) ^ 2 + (C ^ 2 - g' * w x ^ 4) * a ^ 2 =
          g' * |e| ^ 2 * b ^ 2 + C ^ 2 * a ^ 2 - 2 * |e| * g * (a * b) := by
        rw [hgw]; ring
      have hee : e * e = |e| ^ 2 := by rw [sq_abs]; ring
      have : -(e * e * (g' * b ^ 2) + g * (e * carre F η w x + e * carre F η w x)) =
          -(g' * |e| ^ 2 * b ^ 2) + -(2 * e * g * carre F η w x) := by
        rw [hee]; ring
      rw [this]
      linarith
    · push Not at hwx
      have hg : g = 0 := expNegInvGlue.zero_of_nonpos hwx
      rw [hg]
      have : 0 ≤ e * e * (g' * b ^ 2) := mul_nonneg (mul_self_nonneg _) (mul_nonneg hg'0 (sq_nonneg _))
      nlinarith
  have h1 : lam * ∫ x, u x * w x ∂μ ≤ ∫ x, u x * mgenerator F V w x ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (hint2.const_mul lam) hint1 P1
  have h2 : ∫ x, -carre F u w x ∂μ ≤ ∫ _x, C ^ 2 * δ ^ 2 ∂μ :=
    integral_mono hint3.neg (integrable_const _) P2
  rw [integral_neg, hIBP, neg_neg] at h2
  rw [integral_const] at h2
  have e : (fun x => η x * η x * Gfun (w x) * w x) = fun x => u x * w x := rfl
  rw [e]
  refine h1.trans (h2.trans ?_)
  simp [Measure.real, mul_comm]

/-- **Energy maximum principle.**  A bounded smooth `w` with `(lam + κ) w ≤ 𝓛 w` on `{w > 0}`
(`lam > 0`, `κ ≥ 0`) satisfies `w ≤ 0`, on a complete connected manifold with finite weighted
volume. -/
theorem energy_max_principle {w : M → ℝ} (hw : MSmooth F w) (hb : ∃ C, ∀ x, |w x| ≤ C)
    {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} (hκ : ∀ x, 0 ≤ κ x)
    (h : ∀ x, 0 < w x → (lam + κ x) * w x ≤ mgenerator F V w x) : ∀ x, w x ≤ 0 := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨χ, hχ, hev⟩ := weightedCutoffs_of_complete (M := M) F
  have hGs := Gfun_contDiff
  set H : M → ℝ := fun x => Gfun (w x) * w x with hH
  have hHc : Continuous H :=
    (hGs.continuous.comp hw.continuous).mul hw.continuous
  have hH0 : ∀ x, 0 ≤ H x := by
    intro x
    by_cases hx : 0 < w x
    · exact mul_nonneg (Gfun_nonneg _) hx.le
    · push Not at hx
      simp [hH, expNegInvGlue.zero_of_nonpos hx]
  have hHC : ∀ x, H x ≤ C := by
    intro x
    by_cases hx : 0 < w x
    · calc H x ≤ 1 * w x := mul_le_mul_of_nonneg_right (Gfun_le_one _) hx.le
        _ ≤ C := by rw [one_mul]; exact (le_abs_self _).trans (hC x)
    · push Not at hx
      have : H x = 0 := by simp [hH, expNegInvGlue.zero_of_nonpos hx]
      rw [this]
      exact (abs_nonneg _).trans (hC x)
  set Fn : ℕ → M → ℝ := fun n x => χ n x * χ n x * Gfun (w x) * w x with hFn
  have hFnH : ∀ n x, Fn n x = (χ n x * χ n x) * H x := fun n x => by simp only [hFn, hH]; ring
  have hFc : ∀ n, Continuous (Fn n) := fun n => by
    have := (hχ n).1.continuous
    exact ((this.mul this).mul (hGs.continuous.comp hw.continuous)).mul hw.continuous
  have hstep : ∀ n : ℕ, lam * ∫ x, Fn n x ∂μ ≤ C ^ 2 * (1 / ((n : ℝ) + 1)) ^ 2 * (μ Set.univ).toReal :=
    fun n => energy_step F hV hμ (hχ n).1 (hχ n).2.1 (fun x => (hχ n).2.2 x |>.2.2) hw hC hlam hκ h
  have hlim : Tendsto (fun n => ∫ x, Fn n x ∂μ) atTop (𝓝 (∫ x, H x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => (hFc n).aestronglyMeasurable)
      (integrable_const _) (fun n => ?_) ?_
    · refine Filter.Eventually.of_forall (fun x => ?_)
      obtain ⟨h0, h1, -⟩ := (hχ n).2.2 x
      rw [Real.norm_eq_abs, hFnH, abs_of_nonneg (mul_nonneg (mul_self_nonneg _) (hH0 x))]
      calc (χ n x * χ n x) * H x ≤ 1 * H x :=
            mul_le_mul_of_nonneg_right (by nlinarith) (hH0 x)
        _ ≤ C := by rw [one_mul]; exact hHC x
    · refine Filter.Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hFnH, hn]; ring
  have hzero : Tendsto (fun n : ℕ => (C ^ 2 * (μ Set.univ).toReal / lam) * (1 / ((n : ℝ) + 1)) ^ 2)
      atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    simpa using this.const_mul (C ^ 2 * (μ Set.univ).toReal / lam)
  have hle : ∫ x, H x ∂μ ≤ 0 := by
    refine le_of_tendsto_of_tendsto hlim hzero (Filter.Eventually.of_forall (fun n => ?_))
    have := hstep n
    show _ ≤ C ^ 2 * (μ Set.univ).toReal / lam * (1 / ((n : ℝ) + 1)) ^ 2
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith [this]
  have hint : Integrable H μ :=
    Integrable.mono' (integrable_const C) hHc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hH0 x)]; exact hHC x))
  have h0 : ∫ x, H x ∂μ = 0 :=
    le_antisymm hle (integral_nonneg hH0)
  have hae : H =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => hH0 x) hint).1 h0
  have := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  have hHz : H = 0 := (hHc.ae_eq_iff_eq μ continuous_const).1 hae
  intro x
  by_contra hx
  push Not at hx
  have := congrFun hHz x
  have hp : 0 < H x := mul_pos (expNegInvGlue.pos_of_pos hx) hx
  simp only [Pi.zero_apply] at this
  linarith

end Energy

end CutoffRigidity.Riemann.Diff
