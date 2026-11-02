module

public import CutoffRigidity.Extra.DysonGap2

/-! # Dyson--OU: the spectral gap (Rayleigh infimum over `C_c^∞(ℝ^d)`) equals `ρ`

`dysonSpectralGap d ρ β` has exactly the shape of `CutCur.spectralGap V` (infimum of
`∫|∇f|² dμ / Var_μ f` over smooth compactly supported `f : ℝ^d → ℝ` with `Var_μ f > 0`, junk value
`sInf ∅ = 0`), with `μ = dysonProb d ρ β` the (normalised) Dyson--OU Gibbs law on the Weyl chamber.
Test functions are `C_c^∞(ℝ^d)` restricted to the chamber (they need not vanish on the walls): the
Neumann/Friedrichs realisation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal NNReal

namespace CutoffRigidity.Dyson

variable {d : ℕ}

/-- Spectral gap of the Dyson--OU Gibbs measure on the Weyl chamber: Rayleigh infimum over smooth
compactly supported `f : ℝ^d → ℝ`, as in `CutCur.spectralGap` (same test class, same junk value),
with the Gibbs law `dysonProb d ρ β` (a probability measure, so `Var_μ` is the usual variance). -/
noncomputable def dysonSpectralGap (d : ℕ) (ρ β : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    0 < variance f (dysonProb d ρ β) ∧
    r = (∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) / variance f (dysonProb d ρ β)}

theorem isTestFunction_of_compact {f : CutCur.Rd d → ℝ} (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : CutCur.IsTestFunction f := by
  obtain ⟨M, hM⟩ := h2.exists_bound_of_continuous h1.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport h2 h1 (by simp)
  exact ⟨h1, ⟨M, fun x => by simpa using hM x⟩, ⟨L, hL⟩⟩

section Main
variable (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
include hd hρ hβ

/-- Every Rayleigh quotient is at least `ρ` (Poincaré inequality). -/
theorem rayleigh_ge {f : CutCur.Rd d → ℝ} (h1 : ContDiff ℝ ∞ f) (h2 : HasCompactSupport f)
    (hv : 0 < variance f (dysonProb d ρ β)) :
    ρ ≤ (∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) / variance f (dysonProb d ρ β) := by
  have := dyson_poincare hd hρ hβ (isTestFunction_of_compact h1 h2)
  rw [le_div_iff₀ hv]
  have := mul_le_mul_of_nonneg_left this hρ.le
  rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at this
  linarith

/-- The Rayleigh quotients of the cutoff approximants `χ_R h` converge to `ρ`. -/
theorem tendsto_rayleigh_fR :
    Tendsto (fun R : ℝ => (∫ x, ‖gradient (fR d R) x‖ ^ 2 ∂dysonProb d ρ β) /
      variance (fR d R) (dysonProb d ρ β)) atTop (𝓝 ρ) := by
  obtain ⟨M, hM⟩ := exists_fderiv_cut_bound (d := d)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hV := tendsto_variance_fR hd hρ hβ
  have hVpos : ∀ᶠ R in atTop, 0 < variance (fR d R) (dysonProb d ρ β) :=
    hV.eventually (lt_mem_nhds (by positivity))
  set u : ℝ → ℝ := fun t => (1 + t) * d + (t ^ 2 + t) * M ^ 2 * (d / ρ) with hu
  have ht : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hu0 : Tendsto (fun R : ℝ => u (1 / R)) atTop (𝓝 d) := by
    have hc : Continuous u := by simp only [hu]; fun_prop
    have := (hc.tendsto 0).comp ht
    have e : u 0 = d := by simp [hu]
    rw [e] at this
    exact this
  have hup : Tendsto (fun R : ℝ => u (1 / R) / variance (fR d R) (dysonProb d ρ β)) atTop (𝓝 ρ) := by
    have := hu0.div hV (by positivity)
    convert this using 2
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hVpos, eventually_gt_atTop 0] with R hv hR
    exact rayleigh_ge hd hρ hβ (fR_contDiff R) (fR_compact hR) hv
  · filter_upwards [hVpos, eventually_gt_atTop 0] with R hv hR
    refine div_le_div_of_nonneg_right ?_ hv.le
    refine (integral_gradient_fR_le hd hρ hβ (fun R hR x => hM R hR x) hR).trans (le_of_eq ?_)
    simp only [hu]
    field_simp

/-- **The spectral gap of the Dyson--OU Gibbs measure on the Weyl chamber is `ρ`.** -/
theorem dysonSpectralGap_eq : dysonSpectralGap d ρ β = ρ := by
  have hq := tendsto_rayleigh_fR hd hρ hβ
  have hV := tendsto_variance_fR hd hρ hβ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hVpos : ∀ᶠ R in atTop, 0 < variance (fR d R) (dysonProb d ρ β) :=
    hV.eventually (lt_mem_nhds (by positivity))
  have hmem : ∀ᶠ R : ℝ in atTop, (∫ x, ‖gradient (fR d R) x‖ ^ 2 ∂dysonProb d ρ β) /
      variance (fR d R) (dysonProb d ρ β) ∈
      {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        0 < variance f (dysonProb d ρ β) ∧
        r = (∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) / variance f (dysonProb d ρ β)} := by
    filter_upwards [hVpos, eventually_gt_atTop 0] with R hv hR
    exact ⟨fR d R, fR_contDiff R, fR_compact hR, hv, rfl⟩
  have hne : {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        0 < variance f (dysonProb d ρ β) ∧
        r = (∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) / variance f (dysonProb d ρ β)}.Nonempty :=
    by obtain ⟨r, hr⟩ := hmem.exists; exact ⟨_, hr⟩
  have hlow : ∀ r ∈ {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        0 < variance f (dysonProb d ρ β) ∧
        r = (∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) / variance f (dysonProb d ρ β)}, ρ ≤ r := by
    rintro r ⟨f, h1, h2, hv, rfl⟩
    exact rayleigh_ge hd hρ hβ h1 h2 hv
  unfold dysonSpectralGap
  refine le_antisymm ?_ (le_csInf hne hlow)
  exact ge_of_tendsto hq (hmem.mono fun R hR => csInf_le ⟨ρ, hlow⟩ hR)

end Main

end CutoffRigidity.Dyson
