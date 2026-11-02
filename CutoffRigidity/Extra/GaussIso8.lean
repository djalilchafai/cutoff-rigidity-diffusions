module

public import CutoffRigidity.Extra.GaussIso7

/-! # One-dimensional Bobkov inequality for `[0,1]`-valued `C¹` functions (stage 4c) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

lemma BC.integrable_g {h : ℝ → ℝ} (hh : BC h) : Integrable h γ1 := by
  obtain ⟨C, hC⟩ := hh.bdd
  exact Integrable.mono' (integrable_const C) hh.cont.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hC x)

lemma continuousWithinAt_gI {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : ContinuousWithinAt gI (Icc (0:ℝ) 1) u :=
  continuousOn_gI u hu

/-- **Bobkov's inequality for the standard Gaussian on `ℝ`**: `f : ℝ → [0,1]` of class `C¹` with bounded
derivative. -/
theorem bobkov_C1 {f f1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f1 x) x) (b0 : BC f) (b1 : BC f1)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gI (∫ y, f y ∂γ1) ≤ ∫ x, Real.sqrt (gI (f x) ^ 2 + f1 x ^ 2) ∂γ1 := by
  obtain ⟨C1, hC1⟩ := b1.bdd
  have hC1' : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  set m := ∫ y, f y ∂γ1 with hm
  have hm01 : m ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact integral_nonneg fun x => (h01 x).1
    · calc m ≤ ∫ y, (1:ℝ) ∂γ1 := integral_mono b0.integrable_g (integrable_const 1) fun x => (h01 x).2
        _ = 1 := by simp
  -- the approximants
  let fε : ℝ → ℝ → ℝ := fun ε x => ε + (1 - 2 * ε) * f x
  let gε : ℝ → ℝ → ℝ := fun ε x => (1 - 2 * ε) * f1 x
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num)] with ε h1 h2
    exact ⟨h1, h2.2⟩
  have hgood : ∀ ε, 0 < ε → ε < 1 / 2 → Good1 ε (fε ε) (gε ε) := by
    intro ε hε hε2
    refine ⟨hε, fun x => ?_, ?_, b1.const_mul _, fun x => ?_⟩
    · have := ((hd x).const_mul (1 - 2 * ε)).const_add ε
      exact this
    · obtain ⟨C, hC⟩ := b0.bdd
      refine ⟨b0.cont.const_mul _ |>.const_add ε, |ε| + |1 - 2 * ε| * C, fun x => ?_⟩
      calc |ε + (1 - 2 * ε) * f x| ≤ |ε| + |(1 - 2 * ε) * f x| := abs_add_le _ _
        _ ≤ _ := by rw [abs_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _))
    · obtain ⟨h0, h1⟩ := h01 x
      constructor <;> nlinarith
  have hineq : ∀ᶠ ε in 𝓝[>] (0:ℝ), gI (ε + (1 - 2 * ε) * m) ≤
      ∫ x, Real.sqrt (gI (fε ε x) ^ 2 + gε ε x ^ 2) ∂γ1 := by
    filter_upwards [hev] with ε ⟨h1, h2⟩
    have := (hgood ε h1 h2).bobkov
    have hint : ∫ y, fε ε y ∂γ1 = ε + (1 - 2 * ε) * m := by
      show ∫ y, (ε + (1 - 2 * ε) * f y) ∂γ1 = _
      rw [integral_add (integrable_const ε) (b0.integrable_g.const_mul _), integral_const_mul]
      simp [hm]
    rw [hint] at this
    exact this
  -- limits
  have hL : Tendsto (fun ε : ℝ => gI (ε + (1 - 2 * ε) * m)) (𝓝[>] 0) (𝓝 (gI m)) := by
    have hpath : Tendsto (fun ε : ℝ => ε + (1 - 2 * ε) * m) (𝓝[>] 0) (𝓝[Icc (0:ℝ) 1] m) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun ε : ℝ => ε + (1 - 2 * ε) * m) (𝓝 0) (𝓝 (0 + (1 - 2 * 0) * m)) :=
          (by fun_prop : Continuous fun ε : ℝ => ε + (1 - 2 * ε) * m).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [hev] with ε ⟨h1, h2⟩
        constructor <;> nlinarith [hm01.1, hm01.2]
    exact (continuousWithinAt_gI hm01).tendsto.comp hpath
  have hR : Tendsto (fun ε : ℝ => ∫ x, Real.sqrt (gI (fε ε x) ^ 2 + gε ε x ^ 2) ∂γ1) (𝓝[>] 0)
      (𝓝 (∫ x, Real.sqrt (gI (f x) ^ 2 + f1 x ^ 2) ∂γ1)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := γ1) (l := 𝓝[>] (0:ℝ))
      (bound := fun _ => gφ 0 + C1) ?_ ?_ (integrable_const _) ?_
    · filter_upwards [hev] with ε ⟨h1, h2⟩
      have hc : Continuous fun x => gI (fε ε x) := by
        refine continuous_iff_continuousAt.2 fun x => ContinuousAt.comp (f := fε ε) (x := x)
          (hasDerivAt_gI ?_).continuousAt (by have := b0.cont; fun_prop)
        obtain ⟨h0, h1'⟩ := h01 x
        constructor <;> simp only [fε] <;> nlinarith
      exact (Real.continuous_sqrt.comp ((hc.pow 2).add (((b1.cont.const_mul _).pow 2)))).aestronglyMeasurable
    · filter_upwards [hev] with ε ⟨h1, h2⟩
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (gI (fε ε x) ^ 2 + gε ε x ^ 2) ≤ Real.sqrt ((gφ 0 + C1) ^ 2) := by
            apply Real.sqrt_le_sqrt
            have a1 : gI (fε ε x) ≤ gφ 0 := gI_le _
            have a2 : gε ε x ^ 2 ≤ C1 ^ 2 := by
              have : |gε ε x| ≤ C1 := by
                show |(1 - 2 * ε) * f1 x| ≤ C1
                rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * ε)]
                calc (1 - 2 * ε) * |f1 x| ≤ 1 * C1 := by
                      apply mul_le_mul (by linarith) (hC1 x) (abs_nonneg _) (by norm_num)
                  _ = C1 := one_mul _
              nlinarith [abs_nonneg (gε ε x), sq_abs (gε ε x)]
            nlinarith [gI_nonneg (fε ε x), gφ_pos 0]
        _ = gφ 0 + C1 := Real.sqrt_sq (by have := gφ_pos 0; linarith)
    · refine Eventually.of_forall fun x => ?_
      have hx : f x ∈ Icc (0:ℝ) 1 := h01 x
      have hpath : Tendsto (fun ε : ℝ => ε + (1 - 2 * ε) * f x) (𝓝[>] 0) (𝓝[Icc (0:ℝ) 1] (f x)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun ε : ℝ => ε + (1 - 2 * ε) * f x) (𝓝 0) (𝓝 (0 + (1 - 2 * 0) * f x)) :=
            (by fun_prop : Continuous fun ε : ℝ => ε + (1 - 2 * ε) * f x).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [hev] with ε ⟨h1, h2⟩
          constructor <;> nlinarith [hx.1, hx.2]
      have h1 : Tendsto (fun ε : ℝ => gI (fε ε x)) (𝓝[>] 0) (𝓝 (gI (f x))) :=
        (continuousWithinAt_gI hx).tendsto.comp hpath
      have h2 : Tendsto (fun ε : ℝ => gε ε x) (𝓝[>] 0) (𝓝 (f1 x)) := by
        have : Tendsto (fun ε : ℝ => (1 - 2 * ε) * f1 x) (𝓝 0) (𝓝 ((1 - 2 * 0) * f1 x)) :=
          (by fun_prop : Continuous fun ε : ℝ => (1 - 2 * ε) * f1 x).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      exact (Real.continuous_sqrt.tendsto _).comp ((h1.pow 2).add (h2.pow 2))
  exact le_of_tendsto_of_tendsto hL hR hineq

end CutoffRigidity.GaussIso
