module

public import CutoffRigidity.Extra.Dissip2
public import CutoffRigidity.Extra.EuclideanDiffusion

/-! # Entropy dissipation (de Bruijn), kernel form

For the Euclidean Langevin semigroup `Pt` of a smooth potential `V` (`IsEuclideanLangevin V Pt`),
`μ_r := ν.bind (Pt r)`:

* `langevin_dissipation_ge_K` (arbitrary `ν` with `H(ν|μ) < ∞`, `0 < s < t`):
  `∫_s^t I(μ_r|μ) dr + H(μ_t|μ) ≤ H(μ_s|μ)`.
* `langevin_dissipation_core_K` (`ν = (c+g) μ`, `g ∈ C²` compactly supported, `c+g ≥ m > 0`):
  `H(μ_s|μ) = H(μ_t|μ) + ∫_s^t I(μ_r|μ) dr` for `0 ≤ s < t`.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity.Dissip

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal Topology

private theorem hess_nonneg' {d : ℕ} {V : CutCur.Rd d → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x z : CutCur.Rd d) : 0 ≤ fderiv ℝ (fderiv ℝ V) x z z :=
  le_trans (by positivity) (hHess x z)

/-- **Integrated de Bruijn inequality, kernel form, arbitrary initial law of finite entropy.** -/
theorem langevin_dissipation_ge_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν]
    (hfin : klDiv ν (CutCur.gibbs V) ≠ ⊤) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal))) +
        klDiv (ν.bind (Pt t)) (CutCur.gibbs V) ≤
      klDiv (ν.bind (Pt s)) (CutCur.gibbs V) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_isEuclideanLangevin hL (hess_nonneg' hρ hHess)
  have hb : ∀ u : ℝ≥0, (fun x => P.map (X x u)) = ⇑(Pt u) := fun u => funext fun x => key u x
  have hB := Paper.isStdBrownian_iff.mp hLang.2.2.1
  have hbind : ∀ u : ℝ≥0, ν.bind (Pt u) = langevinKernel V B P u ∘ₘ ν := fun u => by
    rw [← Paper.law_bind_eq_comp hLang hρ.le hHess ν u, hb]
  have hbind' : ∀ r : ℝ, ν.bind (Pt r.toNNReal) = lawAt (B := B) (P := P) V ν r :=
    fun r => hbind _
  simp only [hbind', hbind]
  have h := langevin_dissipation_ge hB hLang.1 hLang.2.1 ρ hρ hHess ν hfin
    (NNReal.coe_pos.mpr hs) (NNReal.coe_lt_coe.mpr hst)
  simpa only [lawAt, Real.toNNReal_coe] using h

/-- **Full integrated de Bruijn identity, kernel form, compact-perturbation initial densities.** -/
theorem langevin_dissipation_core_K {d : ℕ} {V g : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂CutCur.gibbs V = 1) {s t : ℝ≥0} (hst : s < t) :
    klDiv (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt s))
        (CutCur.gibbs V) =
      klDiv (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt t))
        (CutCur.gibbs V) +
      ∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V
        (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt r.toNNReal)) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_isEuclideanLangevin hL (hess_nonneg' hρ hHess)
  have hb : ∀ u : ℝ≥0, (fun x => P.map (X x u)) = ⇑(Pt u) := fun u => funext fun x => key u x
  have hB := Paper.isStdBrownian_iff.mp hLang.2.2.1
  set ν := (CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x)) with hν
  have hbind : ∀ u : ℝ≥0, ν.bind (Pt u) = langevinKernel V B P u ∘ₘ ν := fun u => by
    rw [← Paper.law_bind_eq_comp hLang hρ.le hHess ν u, hb]
  have hbind' : ∀ r : ℝ, ν.bind (Pt r.toNNReal) = lawAt (B := B) (P := P) V ν r :=
    fun r => hbind _
  simp only [hbind', hbind]
  have h := langevin_dissipation_core hB hLang.1 hLang.2.1 ρ hρ hHess hg hgc c m hm hpos hNorm
    (NNReal.coe_nonneg s) (NNReal.coe_lt_coe.mpr hst)
  simp only [lawAt, Real.toNNReal_coe] at h
  exact h

end CutoffRigidity.Dissip
