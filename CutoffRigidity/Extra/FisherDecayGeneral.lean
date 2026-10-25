module

public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.Dynamics

/-! # Exponential decay of the Fisher information along the Langevin flow (general initial law)

Manuscript, eq. `eq:expdecI` (proof of Corollary 1.4), and its upper Dini form `dI/dt ≤ -2ρ I`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- **Exponential decay of Fisher information** (eq. expdecI) for an arbitrary initial law. -/
theorem langevin_fisher_decay_carrier {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin V B P X) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    ∀ s t : ℝ≥0, s ≤ t →
      CutCur.fisherInfo V (ν.bind fun x => P.map (X x t)) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) *
          CutCur.fisherInfo V (ν.bind fun x => P.map (X x s)) := by
  intro s t hst
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hV := hL.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := hL.2.1
  have hlaw := law_bind_eq_comp hL hρ.le hHess ν
  have hmk : ∀ t : ℝ≥0, IsMarkovKernel (langevinKernel V B P t) := fun t =>
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hIeq : ∀ t, CutCur.fisherInfo V (ν.bind fun x => P.map (X x t)) =
      relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) := by
    intro t
    rw [hlaw]
    let := hmk t
    exact fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess _
  rw [hIeq, hIeq]
  let := hmk s
  let := hmk t
  have h := relativeFisherInformation_langevinKernel_le hB hV hp ρ hρ hHess
    (langevinKernel V B P s ∘ₘ ν) (t - s)
  have he : s + (t - s) = t := add_tsub_cancel_of_le hst
  simpa only [Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess, he,
      NNReal.coe_sub hst] using h

/-- Dini form of `dI/dt ≤ -2ρ I` from the exponential decay of `I`, for a real function. -/
theorem dini_of_exp_decay {I : ℝ → ℝ} {ρ t : ℝ}
    (hdec : ∀ h : ℝ, 0 ≤ h → I (t + h) ≤ Real.exp (-2 * ρ * h) * I t) :
    ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ), (I (t + h) - I t) / h ≤ -2 * ρ * I t + ε := by
  intro ε hε
  have hd : HasDerivAt (fun h : ℝ => Real.exp (-2 * ρ * h)) (-2 * ρ) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_mul (-2 * ρ)).exp
    simpa using this
  have hs := hd.tendsto_slope_zero_right
  have hlim : Tendsto (fun h : ℝ => h⁻¹ • (Real.exp (-2 * ρ * (0 + h)) - Real.exp (-2 * ρ * 0)))
      (𝓝[>] 0) (𝓝 (-2 * ρ)) := hs
  have hε' : (-2 * ρ) * I t < (-2 * ρ) * I t + ε := by linarith
  have hev := (hlim.mul_const (I t)).eventually (gt_mem_nhds hε')
  filter_upwards [hev, self_mem_nhdsWithin] with h hh hpos
  have hh0 : (0:ℝ) < h := hpos
  have := hdec h hh0.le
  simp only [smul_eq_mul, zero_add, mul_zero, Real.exp_zero] at hh
  rw [div_le_iff₀ hh0]
  have h2 : (h⁻¹ * (Real.exp (-2 * ρ * h) - 1)) * I t * h = (Real.exp (-2 * ρ * h) - 1) * I t := by
    field_simp
  nlinarith [mul_lt_mul_of_pos_right hh hh0]

/-- **Upper Dini form of `dI/dt ≤ -2ρ I`** at every time `t` with `I(μ_t) < ∞`: the real number
`I(μ_{t+h})` is eventually (as `h → 0+`) below `I(μ_t) + h (-2ρ I(μ_t) + ε)`. -/
theorem langevin_fisher_dini_carrier {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin V B P X) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] (t : ℝ≥0)
    (ht : CutCur.fisherInfo V (ν.bind fun x => P.map (X x t)) ≠ ∞) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ((CutCur.fisherInfo V (ν.bind fun x => P.map (X x (t + h.toNNReal)))).toReal -
          (CutCur.fisherInfo V (ν.bind fun x => P.map (X x t))).toReal) / h ≤
        -2 * ρ * (CutCur.fisherInfo V (ν.bind fun x => P.map (X x t))).toReal + ε := by
  set J : ℝ≥0 → ℝ≥0∞ := fun u => CutCur.fisherInfo V (ν.bind fun x => P.map (X x u)) with hJ
  have hdec : ∀ h : ℝ, 0 ≤ h →
      (J (t + h.toNNReal)).toReal ≤ Real.exp (-2 * ρ * h) * (J t).toReal := by
    intro h h0
    have h1 := langevin_fisher_decay_carrier hL hρ hHess ν t (t + h.toNNReal) le_self_add
    have hc : ((t + h.toNNReal : ℝ≥0) : ℝ) - t = h := by
      push_cast; rw [Real.coe_toNNReal _ h0]; ring
    rw [hc] at h1
    have h2 : ENNReal.ofReal (Real.exp (-2 * ρ * h)) * J t ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht
    have h3 := ENNReal.toReal_mono h2 h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h3
  have := dini_of_exp_decay (I := fun h : ℝ => (J (t + h.toNNReal)).toReal) (ρ := ρ) (t := 0)
    (by simpa using hdec) ε hε
  simpa using this

end CutoffRigidity.Paper

