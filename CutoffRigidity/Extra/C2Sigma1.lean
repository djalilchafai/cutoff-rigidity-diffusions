module

public import CutoffRigidity.Extra.C2Uniq9
public import CutoffRigidity.Extra.Sigma

/-! # `C²` versions of the `σ`-diffusion (temperature) statements

`IsSigmaLangevin2` is `IsSigmaLangevinInf` with the smoothness clause `C^∞` weakened to `C²`. The time change
`isSigmaLangevin2_iff` (only `C¹` is used there), the cutoff statement `temperature_cutoff_C2` (via the `C²`
transfer `exists_isRigidSequence_of_K2`; convexity comes from `hHess` with `ρ n > 0`), the generic
`normalization_cutoff_C2` (no potential in the statement) and the `C²` kernel bundle `temperature_kernel_C2`
(existence, Gibbs invariance, time change; uniqueness through `euclideanDiffusion_unique_convex`; here
`Hess V ≥ ρ > 0` is needed because Gibbs invariance goes through `langevinKernel_gibbs_invariant`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutCur
namespace C2U

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

/-- `IsSigmaLangevinInf` with `C²` smoothness. -/
def IsSigmaLangevin2 {d : ℕ} (V : Rd d → ℝ) (σ : ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2) ∧ IsSigmaDiffusion V σ Pt

theorem IsSigmaLangevin2.of_smooth {d : ℕ} {V : Rd d → ℝ} {σ : ℝ}
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (h : IsSigmaLangevinInf V σ Pt) : IsSigmaLangevin2 V σ Pt :=
  ⟨h.1.of_le (by norm_cast), h.2.1, h.2.2⟩

/-- `C²` time change: `IsSigmaLangevin2` is `IsEucLangevin2` for `V/σ²` after `Pt (u/σ²)`. -/
theorem isSigmaLangevin2_iff {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} :
    IsSigmaLangevin2 V σ Pt ↔
      IsEucLangevin2 (fun x => V x / σ ^ 2) (fun u => Pt (((σ ^ 2)⁻¹).toNNReal * u)) := by
  unfold IsSigmaLangevin2 IsEucLangevin2
  have hc : ContDiff ℝ 2 V ↔ ContDiff ℝ 2 (fun x => V x / σ ^ 2) := by
    constructor
    · exact fun h => h.div_const _
    · intro (h : ContDiff ℝ 2 (fun x => V x / σ ^ 2))
      have := ContDiff.mul h (contDiff_const (c := σ ^ 2))
      simpa [div_mul_cancel₀ _ (pow_ne_zero 2 hσ.ne')] using this
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hc.1 h1, h2, (isSigmaDiffusion_iff hσ (h1.differentiable (by norm_num))).1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    have h1' := hc.2 h1
    exact ⟨h1', h2, (isSigmaDiffusion_iff hσ (h1'.differentiable (by norm_num))).2 h3⟩

theorem isEucLangevin2_of_sigma {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (h : IsSigmaLangevin2 V σ Pt) :
    IsEucLangevin2 (fun x => V x / σ ^ 2) (fun u => Pt (((σ ^ 2)⁻¹).toNNReal * u)) :=
  (isSigmaLangevin2_iff hσ).1 h

private lemma sg_c_mul {σ : ℝ} (hσ : 0 < σ) :
    ((σ ^ 2).toNNReal) * (((σ ^ 2)⁻¹).toNNReal) = 1 := by
  rw [← Real.toNNReal_mul (by positivity), mul_inv_cancel₀ (by positivity)]; simp

/-- Uniqueness of `σ`-diffusion kernels for convex `C²` potentials (no Gibbs hypothesis used). -/
theorem isSigmaLangevin2_unique {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d)} (h₁ : IsSigmaLangevin2 V σ P₁)
    (h₂ : IsSigmaLangevin2 V σ P₂) (t : ℝ≥0) (x : Rd d) : P₁ t x = P₂ t x := by
  have hc : ConvexOn ℝ univ V :=
    CutoffRigidity.NoBm.convexOn_univ_of_hessian_nonneg h₁.1 hHess
  have hc' : ConvexOn ℝ univ (fun x => V x / σ ^ 2) := by
    simpa [div_eq_inv_mul, smul_eq_mul] using hc.smul (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ σ ^ 2))
  have e := euclideanDiffusion_unique_convex (P₁ := fun u => P₁ (((σ ^ 2)⁻¹).toNNReal * u))
    (P₂ := fun u => P₂ (((σ ^ 2)⁻¹).toNNReal * u)) (h₁.1.div_const _) hc'
    ((isSigmaLangevin2_iff hσ).1 h₁).2.2 ((isSigmaLangevin2_iff hσ).1 h₂).2.2
    ((σ ^ 2).toNNReal * t) x
  beta_reduce at e
  rwa [← mul_assoc, mul_comm _ ((σ ^ 2).toNNReal), sg_c_mul hσ, one_mul] at e

end C2U
end CutCur

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Topology Set CutCur
open scoped ENNReal NNReal ContDiff Asymptotics

/-- **Normalization (`C²` port)**: the Challenge statement `normalization_cutoff` mentions no potential, so
it is literally the same (generic transition kernels); restated here for the record. -/
theorem normalization_cutoff_C2 {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)}
    {S : ∀ n, Set (CutCur.Rd n)} {α : ℕ → ℝ} (hα : ∀ n, 0 < α n) :
    let Ptα := fun n (u : ℝ≥0) => Pt n ((α n).toNNReal * u)
    (∀ (δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞) (t : ℕ → ℝ) (b a : ℝ≥0∞),
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n) (δ n)) t b a ↔
        CutCur.HasCutoff (fun n => CutCur.worstK (Ptα n) (S n) (δ n))
          (fun n => t n / α n) b a) ∧
    (∀ (μ : ∀ n, Measure (CutCur.Rd n)) (η : ℝ) (n : ℕ),
      CutCur.mixingTimeK (Ptα n) (μ n) (S n) η =
        CutCur.mixingTimeK (Pt n) (μ n) (S n) η / ENNReal.ofReal (α n)) ∧
    (∀ (μ : ∀ n, Measure (CutCur.Rd n)) (η : ℝ) (κ : ℕ → ℝ),
      Tendsto (fun n => α n * κ n * (CutCur.mixingTimeK (Ptα n) (μ n) (S n) η).toReal)
          atTop atTop ↔
        Tendsto (fun n => κ n * (CutCur.mixingTimeK (Pt n) (μ n) (S n) η).toReal)
          atTop atTop) :=
  normalization_cutoff_K hα

/-- **Temperature, cutoff (`C²` port)**: `temperature_cutoff` with `IsSigmaLangevinInf` replaced by
`IsSigmaLangevin2` (smoothness `C²` instead of `C^∞`; the rest of the statement is unchanged). -/
theorem temperature_cutoff_C2 {V : ∀ n, CutCur.Rd n → ℝ} {σ : ℝ} (hσ : 0 < σ) {ρ : ℕ → ℝ}
    {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)}
    (hY : ∀ n, 0 < n → CutCur.C2U.IsSigmaLangevin2 (V n) σ (Pt n))
    (hρ : ∀ n, 0 < n → 0 < ρ n)
    (hHess : ∀ n, 0 < n → ∀ x z : CutCur.Rd n,
      ρ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hgap : ∀ n, 0 < n → ρ n = σ ^ 2 * CutCur.spectralGap (fun x => V n x / σ ^ 2))
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (ρ n)) atTop)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (ρ n)
    let S := fun n => CutCur.meanBall (fun x => V n x / σ ^ 2) c
    CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n)
      (CutCur.wasserstein2 · (CutCur.gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
    ((ρ =o[atTop] (fun n : ℕ => Real.log n)) →
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n)
        (CutCur.fisherInfo fun x => V n x / σ ^ 2)) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n)
        (InformationTheory.klDiv · (CutCur.gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n)
        (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs fun x => V n x / σ ^ 2)))) t 1 0) := by
  classical
  intro t S
  set W : ∀ n, CutCur.Rd n → ℝ := fun n x => V n x / σ ^ 2 with hW
  set Q : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n) :=
    fun n u => Pt n (((σ ^ 2)⁻¹).toNNReal * u) with hQ
  have hs2 : 0 < σ ^ 2 := by positivity
  have hgap' : ∀ n, 0 < n → CutCur.spectralGap (W n) = ρ n / σ ^ 2 := fun n hn => by
    rw [hgap n hn]; field_simp; rfl
  have hK : CutCur.C2U.IsRigidSeqK2 W Q := by
    refine ⟨fun n hn => ⟨CutCur.C2U.isEucLangevin2_of_sigma hσ (hY n hn), ?_, ?_⟩, ?_⟩
    · rw [hgap' n hn]; exact div_pos (hρ n hn) hs2
    · rw [hgap' n hn]
      intro x z
      have hV2 : ContDiff ℝ 2 (V n) := (hY n hn).1
      have h1 := hessian_div_const hV2 (σ ^ 2) x z
      simp only [hW]
      rw [h1, div_mul_eq_mul_div, ← inv_mul_eq_div]
      exact mul_le_mul_of_nonneg_left (hHess n hn x z) (inv_nonneg.mpr hs2.le)
    · have h1 : (fun n => ENNReal.ofReal (CutCur.spectralGap (W n))) =ᶠ[atTop]
          fun n => ENNReal.ofReal ((σ ^ 2)⁻¹) * ENNReal.ofReal (ρ n) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [hW]; simp only
        rw [hgap' n hn, ← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
      rw [liminf_congr h1, ENNReal.liminf_const_mul_of_ne_zero_of_ne_top
        (by simpa using hσ.ne') ENNReal.ofReal_ne_top]
      exact ENNReal.mul_pos (by simpa using hσ.ne') hliminf.ne'
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.C2U.exists_isRigidSequence_of_K2 hK
  have hα : ∀ n, 0 < (fun _ : ℕ => (σ ^ 2)⁻¹) n := fun n => by positivity
  have hnorm := fun δ t' b a => (normalization_cutoff_K (Pt := Pt)
    (S := fun n => CutCur.meanBall (W n) c) hα).1 δ t' b a
  have ht : (fun n => CutCur.criticalTime n (ρ n) / (σ ^ 2)⁻¹) =
      fun n => CutCur.criticalTime n (CutCur.spectralGap (W n)) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [CutCur.criticalTime]
    · rw [hgap' n hn]
      have := (hρ n hn).ne'
      unfold CutCur.criticalTime
      field_simp
  have hcongr : ∀ δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞, ∀ (t' : ℕ → ℝ) (b a : ℝ≥0∞),
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (CutCur.meanBall (W n) c) (δ n)) t' b a →
      CutCur.HasCutoff (fun n => CutCur.worstK (Q n) (CutCur.meanBall (W n) c) (δ n)) t' b a :=
    fun δ t' b a h => (hasCutoff_congr_eventually_iff
      (CutCur.eventually_worst_eq_worstK key (fun n => CutCur.meanBall (W n) c) δ)).1 h
  have hfin : ∀ δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞, ∀ (b a : ℝ≥0∞),
      CutCur.HasCutoff (fun n => CutCur.worstK (Q n) (CutCur.meanBall (W n) c) (δ n))
        (fun n => CutCur.criticalTime n (CutCur.spectralGap (W n))) b a →
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (CutCur.meanBall (W n) c) (δ n)) t b a := by
    intro δ b a h
    rw [hnorm δ t b a, ht]
    exact h
  refine ⟨?_, fun hsmall => ?_⟩
  · exact hfin (fun n ν => CutCur.wasserstein2 ν (CutCur.gibbs (W n))) ⊤ 0
      (hcongr _ _ _ _ (Paper.wasserstein_cutoff_carrier hrig hc))
  · have hsmall' : (fun n => CutCur.spectralGap (W n)) =o[atTop] (fun n : ℕ => Real.log n) := by
      have h1 : (fun n => CutCur.spectralGap (W n)) =ᶠ[atTop] fun n => (σ ^ 2)⁻¹ * ρ n := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [hgap' n hn, div_eq_inv_mul]
      exact (hsmall.const_mul_left _).congr' h1.symm (EventuallyEq.refl _ _)
    have hZi := Paper.information_cutoff_carrier hrig hsmall' hc
    exact ⟨hfin (fun n => CutCur.fisherInfo (W n)) ⊤ 0 (hcongr _ _ _ _ hZi.1),
      hfin (fun n ν => InformationTheory.klDiv ν (CutCur.gibbs (W n))) ⊤ 0
        (hcongr _ _ _ _ hZi.2.1),
      hfin (fun n ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (W n)))) 1 0
        (hcongr _ _ _ _ hZi.2.2)⟩

end CutoffRigidity.Paper
