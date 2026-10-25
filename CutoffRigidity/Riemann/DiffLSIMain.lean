module

public import CutoffRigidity.Riemann.DiffLSIFisher

/-! # LSI from the strong Bakry-Emery gradient bound (workstream BE, part E2)

* `poincare_of_gap`: Poincare inequality on test functions from `mSpectralGap F μ = ρ`.
* `lsi_of_strong_BE`: Bakry-Emery interpolation `Ent(f²) ≤ (2/ρ) ∫ Γ f` from
  `‖∇ K_t f‖ ≤ e^{-ρ t} K_t ‖∇ f‖`, the de Bruijn identity, and the Poincare inequality.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Main

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} [IsProbabilityMeasure μ] {Kk : ℝ≥0 → Kernel M M}

/-- Poincare inequality on test functions from the spectral gap. -/
theorem poincare_of_gap {ρ : ℝ} (hgap : mSpectralGap F μ = ρ) :
    ∀ f : M → ℝ, MSmooth F f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, carre F f f x ∂μ := by
  intro f hf hfc
  have hcar : ∫ x, carre F f f x ∂μ = ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => carre_self_eq F f x)
  rw [hcar]
  have hvar : 0 ≤ variance f μ := variance_nonneg _ _
  have hint : 0 ≤ ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  rcases hvar.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hint
  · have hmem : (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ ∈
        {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧
          0 < variance f μ ∧ r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} :=
      ⟨f, hf, hfc, hpos, rfl⟩
    have hbdd : BddBelow {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧
        HasCompactSupport f ∧ 0 < variance f μ ∧
        r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} := by
      refine ⟨0, ?_⟩
      rintro r ⟨f, -, -, hf, rfl⟩
      exact div_nonneg (integral_nonneg fun x => by positivity) hf.le
    have := csInf_le hbdd hmem
    have hg : mSpectralGap F μ = sInf {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧
        HasCompactSupport f ∧ 0 < variance f μ ∧
        r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} := rfl
    rw [← hg, hgap, le_div_iff₀ hpos] at this
    exact this

/-- `K_0 g = g` for a test function. -/
theorem semi_zero_of_canonical (hK : KerCanonical F V μ Kk) (g : testSub F M) (y : M) :
    semi Kk 0 (g : M → ℝ) y = (g : M → ℝ) y := by
  have := hK.dynkin.2.2 (g : M → ℝ) g.2.1 g.2.2 y 0
  simpa [semi] using this

/-- Monotonicity step: `entFun 0 ≤ entFun T + (2C/ρ)`. -/
theorem entFun_zero_le (hK : KerCanonical F V μ Kk) (hV : MSmooth F V)
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x)
    (f : testSub F M) {δ : ℝ} (hδ : 0 < δ) {T : ℝ} (hT : 0 ≤ T) :
    entFun Kk μ (sqf F f : M → ℝ) δ 0 ≤ entFun Kk μ (sqf F f : M → ℝ) δ T +
      2 * (∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ) / ρ := by
  set C := ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ with hCdef
  have hC0 : 0 ≤ C := integral_nonneg fun x => carre_nonneg F _ x
  set c := 2 * C / ρ with hc
  have hc0 : 0 ≤ c := by positivity
  set ψ : ℝ → ℝ := fun s => entFun Kk μ (sqf F f : M → ℝ) δ s + c * (1 - Real.exp (-2 * ρ * s)) with hψ
  have hg0 : ∀ x, 0 ≤ (sqf F f : M → ℝ) x := fun x => by simp only [sqf_apply]; positivity
  have hcont : ContinuousOn ψ (Ici 0) :=
    (entFun_continuousOn F hK (sqf F f) hg0 hδ).add
      ((continuous_const.mul (continuous_const.sub (by fun_prop))).continuousOn)
  have hderiv : ∀ s ∈ interior (Ici (0:ℝ)), HasDerivAt ψ
      (-(∫ x, carre F (semi Kk s.toNNReal (sqf F f : M → ℝ)) (semi Kk s.toNNReal (sqf F f : M → ℝ)) x /
        (semi Kk s.toNNReal (sqf F f : M → ℝ) x + δ) ∂μ) +
        c * (0 - Real.exp (-2 * ρ * s) * (-2 * ρ))) s := by
    intro s hs
    rw [interior_Ici] at hs
    have hE := entFun_hasDerivAt F hK hV hIBP hReg hC (sqf F f) hg0 hδ hs
    have hd : HasDerivAt (fun s : ℝ => Real.exp (-2 * ρ * s)) (Real.exp (-2 * ρ * s) * (-2 * ρ)) s := by
      simpa using ((hasDerivAt_id s).const_mul (-2 * ρ)).exp
    exact hE.add (((hasDerivAt_const s (1:ℝ)).sub hd).const_mul c)
  have hmono : MonotoneOn ψ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
      (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [(hderiv s hs).deriv]
    have hs' : 0 < s := by rwa [interior_Ici] at hs
    have h1 := fisher_int F hK hReg hBE f hδ s.toNNReal
    rw [Real.coe_toNNReal _ hs'.le] at h1
    have : c * (0 - Real.exp (-2 * ρ * s) * (-2 * ρ)) = 4 * Real.exp (-2 * ρ * s) * C := by
      rw [hc]; field_simp; ring
    rw [this]
    linarith
  have h := hmono (show (0:ℝ) ∈ Ici 0 from le_refl _) (show T ∈ Ici (0:ℝ) from hT) hT
  simp only [hψ, mul_zero, Real.exp_zero, sub_self, add_zero] at h
  have : c * (1 - Real.exp (-2 * ρ * T)) ≤ c := by
    have := Real.exp_pos (-2 * ρ * T)
    nlinarith
  linarith

/-- Fixed `δ`, fixed time bound. -/
theorem lsi_delta_time_bound (hK : KerCanonical F V μ Kk) (hV : MSmooth F V)
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x)
    (hP : ∀ f : M → ℝ, MSmooth F f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, carre F f f x ∂μ)
    (f : testSub F M) {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) :
    ∫ x, ((sqf F f : M → ℝ) x + δ) * Real.log ((sqf F f : M → ℝ) x + δ) ∂μ ≤
      (∫ x, (sqf F f : M → ℝ) x ∂μ + δ) * Real.log (∫ x, (sqf F f : M → ℝ) x ∂μ + δ) +
      Real.exp (-2 * ρ * T) *
        ((∫ x, carre F (sqf F f : M → ℝ) (sqf F f : M → ℝ) x ∂μ) /
          (ρ * (∫ x, (sqf F f : M → ℝ) x ∂μ + δ))) +
      2 * (∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ) / ρ := by
  set g := sqf F f with hg
  have hg0 : ∀ x, 0 ≤ (g : M → ℝ) x := fun x => by simp only [hg, sqf_apply]; positivity
  have hgm : Measurable (g : M → ℝ) := (testSub_continuous F g).measurable
  obtain ⟨Bg, hBg⟩ := testSub_bounded F g
  have hmono := entFun_zero_le F hK hV hIBP hReg hC hρ hBE f hδ (T := (T : ℝ)) T.2
  have e0 : entFun Kk μ (g : M → ℝ) δ 0 = ∫ x, ((g : M → ℝ) x + δ) * Real.log ((g : M → ℝ) x + δ) ∂μ := by
    unfold entFun
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.toNNReal_zero, semi_zero_of_canonical F hK g x]
  have eT : entFun Kk μ (g : M → ℝ) δ T = ∫ x, (semi Kk T (g : M → ℝ) x + δ) *
      Real.log (semi Kk T (g : M → ℝ) x + δ) ∂μ := by
    unfold entFun; simp
  set w := semi Kk T (g : M → ℝ) with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => semi_nonneg' hg0 T x
  have hwm : Measurable w := semi_measurable hgm T
  have hwB : ∀ x, w x ≤ Bg := fun x => (le_abs_self _).trans (semi_abs_le_lsi F hK hBg T x)
  have hint : ∫ x, w x ∂μ = ∫ x, (g : M → ℝ) x ∂μ :=
    integral_semi F hK hgm ⟨Bg, hBg⟩ T
  have hent := entropy_le_var (μ := μ) hw0 hwm hwB hδ
  rw [hint] at hent
  have hvar : (∫ x, (w x - ∫ y, (g : M → ℝ) y ∂μ) ^ 2 ∂μ) = variance w μ := by
    rw [variance_eq_integral hwm.aemeasurable]
    simp only [hint]
  rw [hvar] at hent
  have hSw := inS_semi F hK hReg g T
  have hpoin := poincare_of_InS F hIBP hReg hC hρ.le hP hSw.1
  have hdec := grad_decay_int F hK hReg hBE g T
  have ha0 : 0 ≤ ∫ x, (g : M → ℝ) x ∂μ := integral_nonneg hg0
  set m := ∫ x, (g : M → ℝ) x ∂μ + δ with hm
  have hm0 : 0 < m := by linarith
  have hvle : variance w μ ≤ Real.exp (-2 * ρ * T) *
      ((∫ x, carre F (g : M → ℝ) (g : M → ℝ) x ∂μ) / ρ) := by
    rw [← mul_div_assoc, le_div_iff₀ hρ]
    nlinarith [hpoin, hdec]
  have h2 : variance w μ / m ≤ Real.exp (-2 * ρ * T) *
      ((∫ x, carre F (g : M → ℝ) (g : M → ℝ) x ∂μ) / (ρ * m)) := by
    rw [div_le_iff₀ hm0]
    have : Real.exp (-2 * ρ * T) * ((∫ x, carre F (g : M → ℝ) (g : M → ℝ) x ∂μ) / (ρ * m)) * m =
        Real.exp (-2 * ρ * T) * ((∫ x, carre F (g : M → ℝ) (g : M → ℝ) x ∂μ) / ρ) := by
      field_simp
    rw [this]; exact hvle
  rw [e0, eT] at hmono
  linarith

/-- **Bakry-Emery interpolation**: `Ent(f²) ≤ (2/ρ) ∫ Γ f`. -/
theorem lsi_of_strong_BE (hK : KerCanonical F V μ Kk) (hV : MSmooth F V)
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x)
    (hP : ∀ f : M → ℝ, MSmooth F f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, carre F f f x ∂μ) :
    LSI F V μ ρ := by
  intro f
  set g := sqf F f with hg
  have hg0 : ∀ x, 0 ≤ (g : M → ℝ) x := fun x => by simp only [hg, sqf_apply]; positivity
  have hgm : Measurable (g : M → ℝ) := (testSub_continuous F g).measurable
  obtain ⟨Bg, hBg⟩ := testSub_bounded F g
  set C := ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ with hCdef
  have key : ∀ δ : ℝ, 0 < δ → ∫ x, ((g : M → ℝ) x + δ) * Real.log ((g : M → ℝ) x + δ) ∂μ -
      (∫ x, (g : M → ℝ) x ∂μ + δ) * Real.log (∫ x, (g : M → ℝ) x ∂μ + δ) ≤ 2 / ρ * C := by
    intro δ hδ
    set m := ∫ x, (g : M → ℝ) x ∂μ + δ with hm
    set G := ∫ x, carre F (g : M → ℝ) (g : M → ℝ) x ∂μ with hG
    have hb : ∀ T : ℝ≥0, ∫ x, ((g : M → ℝ) x + δ) * Real.log ((g : M → ℝ) x + δ) ∂μ -
        m * Real.log m ≤ Real.exp (-2 * ρ * T) * (G / (ρ * m)) + 2 * C / ρ := fun T => by
      have := lsi_delta_time_bound F hK hV hIBP hReg hC hρ hBE hP f hδ T
      linarith
    have hlim : Tendsto (fun T : ℝ => Real.exp (-2 * ρ * T) * (G / (ρ * m)) + 2 * C / ρ) atTop
        (𝓝 (0 * (G / (ρ * m)) + 2 * C / ρ)) := by
      refine Tendsto.add (Tendsto.mul_const _ ?_) tendsto_const_nhds
      have : Tendsto (fun T : ℝ => 2 * ρ * T) atTop atTop :=
        tendsto_id.const_mul_atTop (by positivity)
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp this
      refine h2.congr fun T => ?_
      simp only [Function.comp]; congr 1; ring
    rw [zero_mul, zero_add] at hlim
    have := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, fun T hT => by
      have := hb T.toNNReal
      rwa [Real.coe_toNNReal _ hT] at this⟩)
    calc _ ≤ 2 * C / ρ := this
      _ = _ := by ring
  have := ent_delta_limit (μ := μ) hg0 hgm (R := Bg) (fun x => (le_abs_self _).trans (hBg x))
    (B := 2 / ρ * C) key
  exact this

end Main

end CutoffRigidity.Riemann.Diff
