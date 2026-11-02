module

public import Mathlib
public import CutoffRigidity.InvariantKernelL1

/-! # Lower semicontinuity of the Jensen defect of an invariant Markov kernel

For a Markov kernel `K` with invariant probability `μ`, a density `f` and `φ = klFun`, the entropy
drop `∫ φ(f) dμ - ∫ φ(K f) dμ` equals `∫ (K(φ ∘ f) - φ(K f)) dμ` whose integrand is a.e.
nonnegative (Jensen). It is lower semicontinuous under a.e. convergence of `f_n` and of `K f_n`
(Fatou under each `K y`, then Fatou in `y`).
-/

public section

namespace CutoffRigidity.DissipEq

open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Kernel average of a real function. -/
@[expose] noncomputable def kavg (K : Kernel X X) (g : X → ℝ) (y : X) : ℝ := ∫ z, g z ∂K y

theorem measurable_kavg (K : Kernel X X) [IsMarkovKernel K] {g : X → ℝ} (hg : Measurable g) :
    Measurable (kavg K g) :=
  hg.stronglyMeasurable.integral_kernel.measurable

theorem integral_kavg_invariant [IsProbabilityMeasure μ] {K : Kernel X X} [IsMarkovKernel K]
    (hInv : K ∘ₘ μ = μ) {f : X → ℝ} (hi : Integrable f μ) :
    ∫ x, kavg K f x ∂μ = ∫ y, f y ∂μ := by
  have hi' : Integrable f (K ∘ₘ μ) := by rw [hInv]; exact hi
  rw [Measure.comp_eq_comp_const_apply] at hi'
  have hh := Kernel.integral_comp hi'
  unfold kavg
  simpa only [← Measure.comp_eq_comp_const_apply, hInv, Kernel.const_apply] using hh.symm

theorem ae_integrable_kernel [IsProbabilityMeasure μ] {K : Kernel X X} [IsMarkovKernel K]
    (hInv : K ∘ₘ μ = μ) {f : X → ℝ} (hi : Integrable f μ) :
    ∀ᵐ y ∂μ, Integrable f (K y) := by
  have hi' : Integrable f (K ∘ₘ μ) := by rw [hInv]; exact hi
  exact Measure.ae_integrable_of_integrable_comp hi'

theorem ae_ae_kernel [IsProbabilityMeasure μ] {K : Kernel X X} [IsMarkovKernel K]
    (hInv : K ∘ₘ μ = μ) {p : X → Prop} (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ y ∂μ, ∀ᵐ x ∂K y, p x := by
  have h' : ∀ᵐ x ∂(K ∘ₘ μ), p x := by rw [hInv]; exact h
  exact Measure.ae_ae_of_ae_comp h'

/-- Jensen: the defect is a.e. nonnegative. -/
theorem defect_nonneg [IsProbabilityMeasure μ] {K : Kernel X X} [IsMarkovKernel K]
    (hInv : K ∘ₘ μ = μ) {f : X → ℝ} (hn : ∀ x, 0 ≤ f x) (hi : Integrable f μ)
    (hk : Integrable (fun x => klFun (f x)) μ) :
    ∀ᵐ y ∂μ, klFun (kavg K f y) ≤ kavg K (fun x => klFun (f x)) y := by
  filter_upwards [ae_integrable_kernel hInv hi, ae_integrable_kernel hInv hk] with y h1 h2
  exact convexOn_klFun.map_integral_le continuous_klFun.continuousOn isClosed_Ici
    (Eventually.of_forall hn) h1 h2

/-- The entropy drop as the integral of the Jensen defect, with integrability. -/
theorem integrable_klFun_kavg [IsProbabilityMeasure μ] {K : Kernel X X} [IsMarkovKernel K]
    (hInv : K ∘ₘ μ = μ) {f : X → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hi : Integrable f μ) (hk : Integrable (fun x => klFun (f x)) μ) :
    Integrable (fun y => klFun (kavg K f y)) μ := by
  have hkm : Measurable (fun x => klFun (f x)) := measurable_klFun.comp hm
  have hK := invariantKernel_integral_integrable K hInv hkm hk
  refine hK.mono' (measurable_klFun.comp (measurable_kavg K hm)).aestronglyMeasurable ?_
  filter_upwards [defect_nonneg hInv hn hi hk] with y hy
  have h0 : 0 ≤ klFun (kavg K f y) := klFun_nonneg (integral_nonneg hn)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact hy

theorem integral_defect [IsProbabilityMeasure μ] {K : Kernel X X} [IsMarkovKernel K]
    (hInv : K ∘ₘ μ = μ) {f : X → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hi : Integrable f μ) (hk : Integrable (fun x => klFun (f x)) μ) :
    ∫ y, (kavg K (fun x => klFun (f x)) y - klFun (kavg K f y)) ∂μ =
      ∫ x, klFun (f x) ∂μ - ∫ y, klFun (kavg K f y) ∂μ := by
  have hkm : Measurable (fun x => klFun (f x)) := measurable_klFun.comp hm
  have h := integral_sub (invariantKernel_integral_integrable K hInv hkm hk)
    (integrable_klFun_kavg hInv hm hn hi hk)
  refine h.trans ?_
  rw [show (∫ a, ∫ y, klFun (f y) ∂K a ∂μ) = ∫ x, klFun (f x) ∂μ from
    integral_kavg_invariant hInv hk]

/-- Real-sequence lemma for the pointwise liminf of the defect. -/
theorem ofReal_sub_le_liminf {a b : ℕ → ℝ} {a₀ b₀ : ℝ} (hb0 : ∀ n, 0 ≤ b n) (hb₀ : 0 ≤ b₀)
    (ha : ENNReal.ofReal a₀ ≤ liminf (fun n => ENNReal.ofReal (a n)) atTop)
    (hb : Tendsto b atTop (𝓝 b₀)) :
    ENNReal.ofReal (a₀ - b₀) ≤ liminf (fun n => ENNReal.ofReal (a n - b n)) atTop := by
  have hε : ∀ ε : ℝ, 0 < ε →
      ENNReal.ofReal (a₀ - b₀ - ε) ≤ liminf (fun n => ENNReal.ofReal (a n - b n)) atTop := by
    intro ε hε
    have hev : ∀ᶠ n in atTop, b n ≤ b₀ + ε := by
      have := hb.eventually (Iic_mem_nhds (show b₀ < b₀ + ε by linarith))
      exact this
    have h1 : liminf (fun n => ENNReal.ofReal (a n) - ENNReal.ofReal (b₀ + ε)) atTop ≤
        liminf (fun n => ENNReal.ofReal (a n - b n)) atTop := by
      exact liminf_le_liminf (by
        filter_upwards [hev] with n hn
        rw [← ENNReal.ofReal_sub _ (by linarith)]
        exact ENNReal.ofReal_le_ofReal (by linarith))
    rw [ENNReal.liminf_sub_const] at h1
    refine le_trans ?_ h1
    calc ENNReal.ofReal (a₀ - b₀ - ε) ≤ ENNReal.ofReal a₀ - ENNReal.ofReal (b₀ + ε) := by
          rw [← ENNReal.ofReal_sub _ (by linarith)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ _ := tsub_le_tsub_right ha _
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (a₀ - b₀ - 1 / ((k : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal (a₀ - b₀))) := by
    have : Tendsto (fun k : ℕ => a₀ - b₀ - 1 / ((k : ℝ) + 1)) atTop (𝓝 (a₀ - b₀ - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at this
    exact (ENNReal.continuous_ofReal.tendsto _).comp this
  exact le_of_tendsto' hlim fun k : ℕ => hε (1 / ((k:ℝ)+1)) (by positivity)

/-- **Lower semicontinuity of the entropy drop** along a.e. convergent densities. -/
theorem defect_lsc [IsProbabilityMeasure μ] {K : Kernel X X} [IsMarkovKernel K]
    (hInv : K ∘ₘ μ = μ) {f : ℕ → X → ℝ} {f₀ : X → ℝ}
    (hm : ∀ n, Measurable (f n)) (hm₀ : Measurable f₀)
    (hn : ∀ n x, 0 ≤ f n x) (hn₀ : ∀ x, 0 ≤ f₀ x)
    (hi : ∀ n, Integrable (f n) μ) (hi₀ : Integrable f₀ μ)
    (hk : ∀ n, Integrable (fun x => klFun (f n x)) μ) (hk₀ : Integrable (fun x => klFun (f₀ x)) μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hae' : ∀ᵐ y ∂μ, Tendsto (fun n => kavg K (f n) y) atTop (𝓝 (kavg K f₀ y))) :
    ENNReal.ofReal (∫ x, klFun (f₀ x) ∂μ - ∫ y, klFun (kavg K f₀ y) ∂μ) ≤
      liminf (fun n => ENNReal.ofReal
        (∫ x, klFun (f n x) ∂μ - ∫ y, klFun (kavg K (f n) y) ∂μ)) atTop := by
  set J : ℕ → X → ℝ := fun n y => kavg K (fun x => klFun (f n x)) y - klFun (kavg K (f n) y) with hJ
  set J₀ : X → ℝ := fun y => kavg K (fun x => klFun (f₀ x)) y - klFun (kavg K f₀ y) with hJ₀
  have hkm : ∀ n, Measurable (fun x => klFun (f n x)) := fun n => measurable_klFun.comp (hm n)
  have hkm₀ : Measurable (fun x => klFun (f₀ x)) := measurable_klFun.comp hm₀
  have hJm : ∀ n, Measurable (J n) := fun n =>
    (measurable_kavg K (hkm n)).sub (measurable_klFun.comp (measurable_kavg K (hm n)))
  have hJ0m : Measurable J₀ :=
    (measurable_kavg K hkm₀).sub (measurable_klFun.comp (measurable_kavg K hm₀))
  have hJint : ∀ n, Integrable (J n) μ := fun n =>
    (invariantKernel_integral_integrable K hInv (hkm n) (hk n)).sub
      (integrable_klFun_kavg hInv (hm n) (hn n) (hi n) (hk n))
  have hJ0int : Integrable J₀ μ :=
    (invariantKernel_integral_integrable K hInv hkm₀ hk₀).sub
      (integrable_klFun_kavg hInv hm₀ hn₀ hi₀ hk₀)
  have hJnn : ∀ n, ∀ᵐ y ∂μ, 0 ≤ J n y := fun n => by
    filter_upwards [defect_nonneg hInv (hn n) (hi n) (hk n)] with y hy
    exact sub_nonneg.mpr hy
  have hJ0nn : ∀ᵐ y ∂μ, 0 ≤ J₀ y := by
    filter_upwards [defect_nonneg hInv hn₀ hi₀ hk₀] with y hy
    exact sub_nonneg.mpr hy
  have hEq : ∀ n, ENNReal.ofReal (∫ x, klFun (f n x) ∂μ - ∫ y, klFun (kavg K (f n) y) ∂μ) =
      ∫⁻ y, ENNReal.ofReal (J n y) ∂μ := fun n => by
    rw [← integral_defect hInv (hm n) (hn n) (hi n) (hk n)]
    exact ofReal_integral_eq_lintegral_ofReal (hJint n) (hJnn n)
  have hEq₀ : ENNReal.ofReal (∫ x, klFun (f₀ x) ∂μ - ∫ y, klFun (kavg K f₀ y) ∂μ) =
      ∫⁻ y, ENNReal.ofReal (J₀ y) ∂μ := by
    rw [← integral_defect hInv hm₀ hn₀ hi₀ hk₀]
    exact ofReal_integral_eq_lintegral_ofReal hJ0int hJ0nn
  simp only [hEq, hEq₀]
  -- pointwise liminf
  have hpt : ∀ᵐ y ∂μ, ENNReal.ofReal (J₀ y) ≤ liminf (fun n => ENNReal.ofReal (J n y)) atTop := by
    have hK : ∀ᵐ y ∂μ, ∀ᵐ x ∂K y, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)) :=
      ae_ae_kernel hInv hae
    have hI1 := ae_integrable_kernel hInv hi₀
    have hI2 := ae_integrable_kernel hInv hk₀
    have hIn : ∀ᵐ y ∂μ, ∀ n, Integrable (fun x => klFun (f n x)) (K y) := by
      rw [ae_all_iff]; exact fun n => ae_integrable_kernel hInv (hk n)
    have hdn : ∀ᵐ y ∂μ, ∀ n, 0 ≤ J n y := by
      rw [ae_all_iff]; exact hJnn
    filter_upwards [hK, hI2, hIn, hae'] with y hy h2 h3 h5
    -- Fatou under `K y`
    have hfat : ENNReal.ofReal (kavg K (fun x => klFun (f₀ x)) y) ≤
        liminf (fun n => ENNReal.ofReal (kavg K (fun x => klFun (f n x)) y)) atTop := by
      have e0 : ENNReal.ofReal (kavg K (fun x => klFun (f₀ x)) y) =
          ∫⁻ x, ENNReal.ofReal (klFun (f₀ x)) ∂K y :=
        ofReal_integral_eq_lintegral_ofReal h2 (Eventually.of_forall fun x => klFun_nonneg (hn₀ x))
      have en : ∀ n, ENNReal.ofReal (kavg K (fun x => klFun (f n x)) y) =
          ∫⁻ x, ENNReal.ofReal (klFun (f n x)) ∂K y := fun n =>
        ofReal_integral_eq_lintegral_ofReal (h3 n)
          (Eventually.of_forall fun x => klFun_nonneg (hn n x))
      simp only [en, e0]
      calc ∫⁻ x, ENNReal.ofReal (klFun (f₀ x)) ∂K y
          = ∫⁻ x, liminf (fun n => ENNReal.ofReal (klFun (f n x))) atTop ∂K y := by
            apply lintegral_congr_ae
            filter_upwards [hy] with x hx
            have : Tendsto (fun n => ENNReal.ofReal (klFun (f n x))) atTop
                (𝓝 (ENNReal.ofReal (klFun (f₀ x)))) :=
              (ENNReal.continuous_ofReal.tendsto _).comp
                ((continuous_klFun.tendsto _).comp hx)
            exact this.liminf_eq.symm
        _ ≤ _ := lintegral_liminf_le fun n =>
            (ENNReal.measurable_ofReal.comp (measurable_klFun.comp (hm n)))
    have hbn : ∀ n, 0 ≤ klFun (kavg K (f n) y) := fun n => klFun_nonneg (integral_nonneg (hn n))
    have hb : Tendsto (fun n => klFun (kavg K (f n) y)) atTop (𝓝 (klFun (kavg K f₀ y))) :=
      (continuous_klFun.tendsto _).comp h5
    exact ofReal_sub_le_liminf hbn (klFun_nonneg (integral_nonneg hn₀)) hfat hb
  calc ∫⁻ y, ENNReal.ofReal (J₀ y) ∂μ
      ≤ ∫⁻ y, liminf (fun n => ENNReal.ofReal (J n y)) atTop ∂μ := lintegral_mono_ae hpt
    _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (J n y) ∂μ) atTop :=
        lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp (hJm n)

end CutoffRigidity.DissipEq
