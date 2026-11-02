module

public import CutoffRigidity.Extra.GaussIso18

/-! # Gaussian isoperimetric inequality for sets (final statements)

`μ(A) ≥ Φ(a) ⇒ μ(A_r) ≥ Φ(a + √ρ r)` for `μ = N(0, ρ⁻¹ I_d) = e^{-V}dx`, `V = ρ|x|²/2 + c`, where
`A_r` is the closed (resp. open) `r`-neighbourhood. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

variable {d : ℕ}

lemma setOf_infDist_le_eq_cthickening {A : Set (EuclideanSpace ℝ (Fin d))} (hA : A.Nonempty) {r : ℝ}
    (hr : 0 ≤ r) : {x | infDist x A ≤ r} = cthickening r A := by
  ext x
  rw [mem_setOf_eq, mem_cthickening_iff, infDist]
  rw [← ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hA) hr]

/-- Closed-neighbourhood form. -/
theorem gaussρ_isoperimetric_cthickening {ρ : ℝ} (hρ : 0 < ρ) {A : Set (EuclideanSpace ℝ (Fin d))}
    {a : ℝ} (hA : cdf (gaussianReal 0 1) a ≤ (gaussρ d ρ).real A) {r : ℝ} (hr : 0 ≤ r) :
    cdf (gaussianReal 0 1) (a + Real.sqrt ρ * r) ≤ (gaussρ d ρ).real (cthickening r A) := by
  have hΦ : 0 < cdf (gaussianReal 0 1) a := gΦ_pos a
  have hne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h] at hA
    simp at hA
    exact absurd hA (not_le.2 hΦ)
  have hc : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have h0 : gΦ a ≤ nA ρ A 0 := by
    refine hA.trans ?_
    unfold nA
    refine measureReal_mono (fun x hx => ?_)
    show infDist x A ≤ 0
    rw [infDist_zero_of_mem hx]
  have := comparison (nA_mono (ρ := ρ) A) (nA_rightContinuous A) hc h0
    (fun r hr s hs η hη => fs_sets hρ hne hs hη) r hr
  have e : nA ρ A r = (gaussρ d ρ).real (cthickening r A) := by
    unfold nA; rw [setOf_infDist_le_eq_cthickening hne hr]
  rw [e] at this
  exact this

/-- Open-neighbourhood form. -/
theorem gaussρ_isoperimetric_thickening {ρ : ℝ} (hρ : 0 < ρ) {A : Set (EuclideanSpace ℝ (Fin d))}
    {a : ℝ} (hA : cdf (gaussianReal 0 1) a ≤ (gaussρ d ρ).real A) {r : ℝ} (hr : 0 < r) :
    cdf (gaussianReal 0 1) (a + Real.sqrt ρ * r) ≤ (gaussρ d ρ).real (thickening r A) := by
  have hΦ : 0 < cdf (gaussianReal 0 1) a := gΦ_pos a
  have hne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h] at hA
    simp at hA
    exact absurd hA (not_le.2 hΦ)
  have hlim : Tendsto (fun t : ℝ => cdf (gaussianReal 0 1) (a + Real.sqrt ρ * t)) (𝓝[<] r)
      (𝓝 (cdf (gaussianReal 0 1) (a + Real.sqrt ρ * r))) :=
    ((continuous_gΦ.comp (by fun_prop : Continuous fun t : ℝ => a + Real.sqrt ρ * t)).tendsto r).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hr] with t ht
  refine (gaussρ_isoperimetric_cthickening hρ hA ht.1.le).trans ?_
  refine measureReal_mono (fun x hx => ?_)
  rw [← setOf_infDist_le_eq_cthickening hne ht.1.le] at hx
  rw [mem_thickening_iff_infDist_lt hne]
  exact lt_of_le_of_lt hx ht.2

end CutoffRigidity.GaussIso

namespace CutoffRigidity.GaussIso

open CutCur

/-- **Gaussian isoperimetric inequality** (Sudakov–Tsirelson, Borell), for the Gibbs measure of
`V = ρ|x|²/2 + c` (a probability measure, i.e. `N(0, ρ⁻¹ I_d)`): if `μ(A) ≥ Φ(a)` then the closed
`r`-neighbourhood satisfies `μ(A_r) ≥ Φ(a + √ρ r)`. -/
theorem gaussian_isoperimetric_sets {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {V : Rd d → ℝ}
    (hV : ∃ c : ℝ, ∀ x, V x = ρ / 2 * ‖x‖ ^ 2 + c) (hp : IsProbabilityMeasure (gibbs V))
    {A : Set (Rd d)} {a : ℝ} (hA : cdf (gaussianReal 0 1) a ≤ (gibbs V).real A) {r : ℝ} (hr : 0 ≤ r) :
    cdf (gaussianReal 0 1) (a + Real.sqrt ρ * r) ≤ (gibbs V).real (Metric.cthickening r A) := by
  obtain ⟨c, hc⟩ := hV
  have hVe : V = fun x => ρ / 2 * ‖x‖ ^ 2 + c := funext hc
  subst hVe
  have hg : gibbs (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) = gaussρ d ρ :=
    gibbs_quadratic_eq_gaussρ hρ c hp
  rw [hg] at hA ⊢
  exact gaussρ_isoperimetric_cthickening hρ hA hr

/-- Open-neighbourhood version of `gaussian_isoperimetric_sets`. -/
theorem gaussian_isoperimetric_sets_thickening {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {V : Rd d → ℝ}
    (hV : ∃ c : ℝ, ∀ x, V x = ρ / 2 * ‖x‖ ^ 2 + c) (hp : IsProbabilityMeasure (gibbs V))
    {A : Set (Rd d)} {a : ℝ} (hA : cdf (gaussianReal 0 1) a ≤ (gibbs V).real A) {r : ℝ} (hr : 0 < r) :
    cdf (gaussianReal 0 1) (a + Real.sqrt ρ * r) ≤ (gibbs V).real (Metric.thickening r A) := by
  obtain ⟨c, hc⟩ := hV
  have hVe : V = fun x => ρ / 2 * ‖x‖ ^ 2 + c := funext hc
  subst hVe
  have hg : gibbs (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) = gaussρ d ρ :=
    gibbs_quadratic_eq_gaussρ hρ c hp
  rw [hg] at hA ⊢
  exact gaussρ_isoperimetric_thickening hρ hA hr

end CutoffRigidity.GaussIso
