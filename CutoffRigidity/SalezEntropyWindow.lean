module

public import CutoffRigidity.Varentropy
public import CutoffRigidity.GibbsEnergy
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Salez's actual post-mixing entropy comparison on an explicit domain

This is the reciprocal-entropy integration in the proof of Theorem 1 of
https://arxiv.org/html/2501.01304v1 . The local Poincaré functional inequality
and density-curve differentiation domain remain explicit; this module does
not claim their derivation from curvature for the canonical Langevin kernel.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory InformationTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A genuine local Poincaré inequality on smooth functions, for the
specified actual probability law. No entropy conclusion is a field. -/
@[expose] def HasLocalSmoothPoincare (ν : Measure E) (C : ℝ) : Prop :=
  ∀ g : E → ℝ, ContDiff ℝ 1 g → MemLp g 2 ν →
    Integrable (fun x => ‖gradient g x‖ ^ 2) ν →
    variance g ν ≤ C * ∫ x, ‖gradient g x‖ ^ 2 ∂ν

/-- The actual log-likelihood gradient energy on the explicit smooth
information domain. It is not a definition of extended Fisher information. -/
@[expose] noncomputable def likelihoodGradientEnergy (ν μ : Measure E) : ℝ :=
  ∫ x, ‖gradient (llr ν μ) x‖ ^ 2 ∂ν

theorem likelihoodGradientEnergy_nonneg (ν μ : Measure E) :
    0 ≤ likelihoodGradientEnergy ν μ := by
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Applying genuine local Poincaré to the actual RN log likelihood proves
the varentropy bound used in Salez's differential comparison. -/
theorem varentropy_le_localPoincare_energy (ν μ : Measure E)
    (C : ℝ) (hP : HasLocalSmoothPoincare ν C)
    (hL : ContDiff ℝ 1 (llr ν μ)) (hL2 : MemLp (llr ν μ) 2 ν)
    (hI : Integrable (fun x => ‖gradient (llr ν μ) x‖ ^ 2) ν) :
    (varentropy ν μ).toReal ≤ C * likelihoodGradientEnergy ν μ :=
  hP _ hL hL2 hI

private theorem entropy_window_comparison {H I : ℝ → ℝ} {a b ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε)
    (hD : ∀ s ∈ Icc a b, HasDerivAt H (-I s) s)
    (hI : ∀ s ∈ Icc a b, 0 ≤ I s)
    (hvar : ∀ s ∈ Icc a b, 1 / ε < H s → (ε * H s - 1) ^ 2 ≤ 2 * s * I s) :
    H b ≤ 1 / ε + 2 / (ε ^ 2 * Real.log (b / a)) := by
  have hb : 0 < b := ha.trans hab
  have hlog : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div ha).mpr hab)
  have hHcont : ContinuousOn H (Icc a b) := fun s hs => (hD s hs).continuousAt.continuousWithinAt
  have hmono : AntitoneOn H (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hHcont
    · intro s hs
      exact (hD s (Ioo_subset_Icc_self (by simpa only [interior_Icc] using hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Icc a b := Ioo_subset_Icc_self (by simpa only [interior_Icc] using hs)
      rw [(hD s hs').deriv]
      exact neg_nonpos.mpr (hI s hs')
  by_cases hsmall : H b ≤ 1 / ε
  · exact hsmall.trans (le_add_of_nonneg_right (div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hlog.le)))
  have hlarge : 1 / ε < H b := lt_of_not_ge hsmall
  have hden (s : ℝ) (hs : s ∈ Icc a b) : 0 < ε * H s - 1 := by
    have hh := hmono hs ⟨hab.le, le_rfl⟩ hs.2
    have he : 1 < H b * ε := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  let F : ℝ → ℝ := fun s => (ε * H s - 1)⁻¹ - (ε / 2) * Real.log s
  have hFD (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt F
      (ε * I s / (ε * H s - 1) ^ 2 - ε / (2 * s)) s := by
    have hspos : 0 < s := ha.trans_le hs.1
    have hh := (((hD s hs).const_mul ε).sub_const 1).inv (ne_of_gt (hden s hs))
    have hh' := hh.sub ((Real.hasDerivAt_log hspos.ne').const_mul (ε / 2))
    convert! hh' using 1
    ring
  have hFmono : MonotoneOn F (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun s hs => (hFD s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hFD s (Ioo_subset_Icc_self (by simpa only [interior_Icc] using hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Icc a b := Ioo_subset_Icc_self (by simpa only [interior_Icc] using hs)
      rw [(hFD s hs').deriv]
      have hh := hvar s hs' (lt_of_lt_of_le hlarge (hmono hs' ⟨hab.le, le_rfl⟩ hs'.2))
      have hspos : 0 < s := ha.trans_le hs'.1
      apply sub_nonneg.mpr
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hspos) (sq_pos_of_pos (hden s hs'))).mpr
      nlinarith
  have hFa : 0 < (ε * H a - 1)⁻¹ := inv_pos.mpr (hden a ⟨le_rfl, hab.le⟩)
  have hh := hFmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
  dsimp only [F] at hh
  have hlogeq : Real.log (b / a) = Real.log b - Real.log a := Real.log_div hb.ne' ha.ne'
  have hrecip : (ε / 2) * Real.log (b / a) ≤ (ε * H b - 1)⁻¹ := by
    rw [hlogeq]
    linarith
  have hm := mul_le_mul_of_nonneg_right hrecip (hden b ⟨hab.le, le_rfl⟩).le
  rw [inv_mul_cancel₀ (ne_of_gt (hden b ⟨hab.le, le_rfl⟩))] at hm
  have hfin : H b - 1 / ε ≤ 2 / (ε ^ 2 * Real.log (b / a)) := by
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hε) hlog)).mpr
    field_simp
    nlinarith
  linarith

/-- The actual post-mixing entropy bound used in the source proof of
Theorem 1.7. The coefficient is derived explicitly, not supplied as a bound.
The analytic obligations are the actual entropy differentiation identity,
a local Poincaré inequality on the evolving law, and the stated information
regularity domain. Curvature-to-domain bridges are not asserted here. -/
theorem salez_post_mixing_entropy_bound (μ : Measure E)
    [IsProbabilityMeasure μ] (ν : ℝ → Measure E)
    (hprob : ∀ s, IsProbabilityMeasure (ν s))
    {a b ε : ℝ} (ha : 0 < a) (hab : a < b) (hε : 0 < ε) (hε1 : ε < 1)
    (hac : ∀ s ∈ Icc a b, ν s ≪ μ)
    (hL : ∀ s ∈ Icc a b, ContDiff ℝ 1 (llr (ν s) μ))
    (hL2 : ∀ s ∈ Icc a b, MemLp (llr (ν s) μ) 2 (ν s))
    (hInt : ∀ s ∈ Icc a b, Integrable
      (fun x => ‖gradient (llr (ν s) μ) x‖ ^ 2) (ν s))
    (hP : ∀ s ∈ Icc a b, HasLocalSmoothPoincare (ν s) (2 * s))
    (hTV : ∀ s ∈ Icc a b, totalVariationDistance (ν s) μ ≤ 1 - ε)
    (hD : ∀ s ∈ Icc a b, HasDerivAt (fun t => (klDiv (ν t) μ).toReal)
      (-likelihoodGradientEnergy (ν s) μ) s) :
    (klDiv (ν b) μ).toReal ≤ 1 / ε + 2 / (ε ^ 2 * Real.log (b / a)) := by
  apply entropy_window_comparison ha hab hε hD
  · intro s _
    exact likelihoodGradientEnergy_nonneg _ _
  · intro s hs hlarge
    let := hprob s
    have hrev := klDiv_toReal_le_varentropy_of_tv_le (ν s) μ (hac s hs)
      (hL2 s hs) hε hε1 (hTV s hs)
    have hrev' : ε * (klDiv (ν s) μ).toReal - 1 ≤
        Real.sqrt (variance (llr (ν s) μ) (ν s)) := by
      have hh := (le_div_iff₀ hε).mp hrev
      nlinarith
    have hpos : 0 ≤ ε * (klDiv (ν s) μ).toReal - 1 := by
      have hh := (div_lt_iff₀ hε).mp hlarge
      nlinarith
    have hsquare : (ε * (klDiv (ν s) μ).toReal - 1) ^ 2 ≤
        variance (llr (ν s) μ) (ν s) := by
      calc
        _ ≤ Real.sqrt (variance (llr (ν s) μ) (ν s)) ^ 2 :=
          (sq_le_sq₀ hpos (Real.sqrt_nonneg _)).mpr hrev'
        _ = _ := Real.sq_sqrt (variance_nonneg _ _)
    exact hsquare.trans (varentropy_le_localPoincare_energy (ν s) μ (2 * s)
      (hP s hs) (hL s hs) (hL2 s hs) (hInt s hs))

/-- The explicit dimension-independent constant at a multiplicative time
past a mixing threshold. This is the bounded post-mixing entropy input
cited in the source, on the displayed analytic domain. -/
theorem salez_entropy_at_dilated_time (μ : Measure E)
    [IsProbabilityMeasure μ] (ν : ℝ → Measure E)
    (hprob : ∀ s, IsProbabilityMeasure (ν s))
    {a η δ : ℝ} (ha : 0 < a) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 < δ)
    (hac : ∀ s ∈ Icc a ((1 + δ) * a), ν s ≪ μ)
    (hL : ∀ s ∈ Icc a ((1 + δ) * a), ContDiff ℝ 1 (llr (ν s) μ))
    (hL2 : ∀ s ∈ Icc a ((1 + δ) * a), MemLp (llr (ν s) μ) 2 (ν s))
    (hInt : ∀ s ∈ Icc a ((1 + δ) * a), Integrable
      (fun x => ‖gradient (llr (ν s) μ) x‖ ^ 2) (ν s))
    (hP : ∀ s ∈ Icc a ((1 + δ) * a), HasLocalSmoothPoincare (ν s) (2 * s))
    (hTV : ∀ s ∈ Icc a ((1 + δ) * a), totalVariationDistance (ν s) μ ≤ η)
    (hD : ∀ s ∈ Icc a ((1 + δ) * a), HasDerivAt (fun t => (klDiv (ν t) μ).toReal)
      (-likelihoodGradientEnergy (ν s) μ) s) :
    klDiv (ν ((1 + δ) * a)) μ ≤ ENNReal.ofReal
      (1 / (1 - η) + 2 / ((1 - η) ^ 2 * Real.log (1 + δ))) := by
  have hab : a < (1 + δ) * a := by nlinarith
  have hbound := salez_post_mixing_entropy_bound μ ν hprob ha hab
    (sub_pos.mpr hη1) (by linarith : 1 - η < 1) hac hL hL2 hInt hP
    (fun s hs => by simpa only [sub_sub_cancel] using hTV s hs) hD
  have hratio : ((1 + δ) * a) / a = 1 + δ := by field_simp
  rw [hratio] at hbound
  let := hprob ((1 + δ) * a)
  have hfinite := klDiv_ne_top_of_memLp_llr (ν ((1 + δ) * a)) μ
    (hac _ ⟨hab.le, le_rfl⟩) (hL2 _ ⟨hab.le, le_rfl⟩)
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hbound

end CutoffRigidity
