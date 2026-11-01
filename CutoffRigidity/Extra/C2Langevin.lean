module

public import CutoffRigidity.Extra.EuclideanKernelStatements
public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Paper.ExistsBrownian

/-! # `C²` kernel setting: what is recovered, and the exact remaining gap

`IsEuclideanLangevinC2` is `IsEuclideanLangevin` with `ContDiff ℝ ∞ V` weakened to `ContDiff ℝ 2 V`.

* Unconditional: for a smooth potential the two notions coincide; in particular for the quadratic
  potentials `ρ/2 ‖x‖² + c` of the Ornstein-Uhlenbeck statements the `C^∞` clause of
  `IsEuclideanLangevin` is automatic, so those kernel statements hold verbatim under the `C²` hypothesis.
* Conditional: the transfer to a Brownian carrier (hence all kernel statements) holds for a `C²` potential
  as soon as uniqueness of `IsEuclideanDiffusion V` holds (`C2Uniqueness V`). The uniqueness itself is NOT
  proved for non-smooth `V`; see `extra-status/c2-worker.md`.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutCur

open CutoffRigidity CutoffRigidity.Riemann
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

/-- `C²` version of `IsEuclideanLangevin`. -/
def IsEuclideanLangevinC2 {d : ℕ} (V : Rd d → ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs V) ∧ IsEuclideanDiffusion V Pt

/-- Uniqueness of the Euclidean diffusion semigroup of `V` (proved for `C^∞` `V`, open for `C²`). -/
def C2Uniqueness {d : ℕ} (V : Rd d → ℝ) : Prop :=
  ∀ P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d), IsEuclideanDiffusion V P₁ → IsEuclideanDiffusion V P₂ →
    ∀ t x, P₁ t x = P₂ t x

theorem IsEuclideanLangevin.toC2 {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : IsEuclideanLangevin V Pt) : IsEuclideanLangevinC2 V Pt :=
  ⟨h.1.of_le (by norm_cast), h.2.1, h.2.2⟩

theorem IsEuclideanLangevinC2.toSmooth {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : IsEuclideanLangevinC2 V Pt) (hV : ContDiff ℝ ∞ V) : IsEuclideanLangevin V Pt :=
  ⟨hV, h.2.1, h.2.2⟩

theorem c2Uniqueness_of_smooth {d : ℕ} {V : Rd d → ℝ} (hV : ContDiff ℝ ∞ V)
    (hp : IsProbabilityMeasure (gibbs V)) : C2Uniqueness V :=
  fun _ _ h₁ h₂ => isEuclideanDiffusion_unique hV hp h₁ h₂

/-- Quadratic potentials are smooth, so the `C²` and `C^∞` kernel hypotheses are equivalent. -/
theorem isEuclideanLangevinC2_quadratic_iff {d : ℕ} {ρ c : ℝ}
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} :
    IsEuclideanLangevinC2 (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Pt ↔
      IsEuclideanLangevin (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Pt := by
  have hs : ContDiff ℝ ∞ (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add contDiff_const
  exact ⟨fun h => h.toSmooth hs, fun h => h.toC2⟩

/-- **Transfer lemma, `C²` version, conditional on uniqueness.** -/
theorem exists_isLangevin_of_C2 {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hL : IsEuclideanLangevinC2 V Pt) (hU : C2Uniqueness V)
    (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω)
      (X : Rd d → ℝ≥0 → Ω → Rd d),
      IsProbabilityMeasure P ∧ IsLangevin V B P X ∧
        ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀ := by
  obtain ⟨Ω, hΩ, P, B, hP, hB⟩ := Paper.exists_stdBrownian d
  have hB' : IsEuclideanBrownian B P := Paper.isStdBrownian_iff.1 hB
  have hH : ∀ x z : Rd d, (0 : ℝ) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z; simpa using hHess x z
  refine ⟨Ω, hΩ, B, P, fun x₀ => langevinProcess V B x₀, hP, ⟨hL.1, hL.2.1, hB, fun x₀ => ?_⟩,
    fun t x₀ => ?_⟩
  · exact Paper.isLangevinSolution_langevinProcess hB' hL.1 0 le_rfl hH x₀
  · exact (langevinKernel_apply_eq_process_law hB' hL.1 0 le_rfl hH t x₀).symm.trans
      (hU _ _ hL.2.2 (isEuclideanDiffusion_langevinKernel hB' hL.1 0 le_rfl hH) t x₀).symm

end CutCur

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

/-- `ou_fisher_information_K` under the `C²` hypothesis (unconditional). -/
theorem ou_fisher_information_C2 {d : ℕ} {ρ c : ℝ} (hρ : 0 < ρ)
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.IsEuclideanLangevinC2 (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Pt)
    (x₀ : CutCur.Rd d) {t : ℝ} (ht : 0 < t) :
    let V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c
    let μt := Pt t.toNNReal x₀
    μt = multivariateGaussian (Real.exp (-ρ * t) • x₀)
        (((1 - Real.exp (-2 * ρ * t)) / ρ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
      (∃ u : CutCur.Rd d → ℝ, ContDiff ℝ ∞ u ∧
        μt = (CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (Real.exp (u x))) ∧
        (∀ᵐ x ∂CutCur.gibbs V, u x = Real.log (μt.rnDeriv (CutCur.gibbs V) x).toReal) ∧
        ∀ x, gradient u x = (ρ - ρ / (1 - Real.exp (-2 * ρ * t))) • x +
          (ρ * Real.exp (-ρ * t) / (1 - Real.exp (-2 * ρ * t))) • x₀) ∧
      CutCur.fisherInfo V μt = ENNReal.ofReal
        (ρ * d * Real.exp (-4 * ρ * t) / (1 - Real.exp (-2 * ρ * t)) +
          ρ ^ 2 * Real.exp (-2 * ρ * t) * ‖x₀‖ ^ 2) :=
  ou_fisher_information_K hρ (CutCur.isEuclideanLangevinC2_quadratic_iff.1 hL) x₀ ht

/-- `ou_mean_start_cutoff_K` under the `C²` hypothesis (unconditional). -/
theorem ou_mean_start_cutoff_C2 {ρ : ℝ} (hρ : 0 < ρ)
    {c : ℕ → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)} (hL : ∀ n, 0 < n →
      CutCur.IsEuclideanLangevinC2 (fun x : CutCur.Rd n => ρ / 2 * ‖x‖ ^ 2 + c n) (Pt n)) :
    let V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + c n
    let prof := fun n => CutCur.worstK (Pt n) {∫ x, x ∂CutCur.gibbs (V n)}
      (CutCur.wasserstein2 · (CutCur.gibbs (V n)))
    CutCur.HasCutoff prof (fun n => Real.log n / (4 * CutCur.spectralGap (V n))) ⊤ 0 ∧
      ¬ CutCur.HasCutoff prof (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 :=
  ou_mean_start_cutoff_K hρ fun n hn => CutCur.isEuclideanLangevinC2_quadratic_iff.1 (hL n hn)

/-- `ou_lp_infty_fails_K` under the `C²` hypothesis (unconditional). -/
theorem ou_lp_infty_fails_C2 {ρ : ℝ} (hρ : 0 < ρ)
    {c' : ℕ → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)} (hL : ∀ n, 0 < n →
      CutCur.IsEuclideanLangevinC2 (fun x : CutCur.Rd n => ρ / 2 * ‖x‖ ^ 2 + c' n) (Pt n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + c' n
    let prof := fun n => CutCur.worstK (Pt n) (CutCur.meanBall (V n) c)
      (CutCur.relLp · (CutCur.gibbs (V n)) ⊤)
    (∀ t : ℕ → ℝ, Tendsto (fun n => prof n (t n)) atTop (𝓝 ⊤)) ∧
      ¬ CutCur.HasCutoff prof (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 :=
  ou_lp_infty_fails_K hρ (fun n hn => CutCur.isEuclideanLangevinC2_quadratic_iff.1 (hL n hn)) hc

/-- `langevin_fisher_decay` under `C²` and the (open) uniqueness hypothesis. -/
theorem langevin_fisher_decay_C2_of_unique {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevinC2 V Pt)
    (hU : CutCur.C2Uniqueness V)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    ∀ s t : ℝ≥0, s ≤ t →
      CutCur.fisherInfo V (ν.bind (Pt t)) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) *
          CutCur.fisherInfo V (ν.bind (Pt s)) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_C2 hL hU (hess_nonneg_of_rate hρ hHess)
  have hb : ∀ t : ℝ≥0, (fun x => P.map (X x t)) = ⇑(Pt t) := fun t => funext fun x => key t x
  have h := langevin_fisher_decay_carrier hLang hρ hHess ν
  simp only [hb] at h
  exact h

end CutoffRigidity.Paper
