module

public import CutoffRigidity.Extra.Sphere9
public import CutoffRigidity.Riemann.WeightedIBPGlobal

/-! # Sphere, stage 10: `λ₁ ≤ d` from the eigenfunction property of the coordinate functions

For a probability measure `μ` with `IsWeightedVolume F μ (fun _ => c)` on a compact isometrically immersed
model of `S^d`, integration by parts gives `∫ φ_a = 0` and `∫ Γ(φ_a) = d ∫ φ_a²`; hence
`mSpectralGap ≤ d`.  No rotation invariance of `μ` is used.
-/

@[expose] public section

open Bundle Filter Set VectorField MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutCur.WBoch CutoffRigidity CutoffRigidity.Extra

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "bb" => stdOrthonormalBasis ℝ 𝔼

/-- Integrated eigenfunction identities for `φ_a`: `∫ φ_a = 0` and `∫ ‖∇φ_a‖² = d ∫ φ_a²`. -/
theorem integral_phi_identities (hF : Module.finrank ℝ F = d) (hd : 1 ≤ d) {Φ : M → 𝔼}
    (hΦ : IsIsometricSphereMap F Φ) {μ : Measure M} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume F μ (fun _ => c)) (a : 𝔼) :
    ∫ x, phi Φ a x ∂μ = 0 ∧
      ∫ x, ‖mgrad F (phi Φ a) x‖ ^ 2 ∂μ = (d : ℝ) * ∫ x, (phi Φ a x) ^ 2 ∂μ := by
  have hibp := CutCur.weightedIBP_of_isWeightedVolume F (contMDiff_const (c := c)) hμ
  have hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (phi Φ a) := contMDiff_phi hΦ a
  have hcont : Continuous (phi Φ a) := hf.continuous
  have hdpos : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have h0 := hibp (fun _ => (1 : ℝ)) (phi Φ a) contMDiff_const hf (HasCompactSupport.of_compactSpace _)
  have h1 := hibp (phi Φ a) (phi Φ a) hf hf (HasCompactSupport.of_compactSpace _)
  simp only [mgenerator_phi hF hΦ] at h0 h1
  have hc0 : ∀ x, carre F (fun _ : M => (1 : ℝ)) (phi Φ a) x = 0 := by
    intro x; simp [carre, mgrad_const]
  simp only [hc0, integral_zero] at h0
  have hint : Integrable (phi Φ a) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨?_, ?_⟩
  · have : ∫ x, 1 * (-(d : ℝ) * phi Φ a x) ∂μ = -(d : ℝ) * ∫ x, phi Φ a x ∂μ := by
      simp only [one_mul]
      rw [integral_const_mul]
    rw [this] at h0
    have h2 : -(d : ℝ) * ∫ x, phi Φ a x ∂μ = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (neg_eq_zero.1 h) hdpos
    · exact h
  · have e1 : ∀ x, carre F (phi Φ a) (phi Φ a) x = ‖mgrad F (phi Φ a) x‖ ^ 2 := fun x => carre_self_eq F _ x
    simp only [e1] at h1
    rw [h1]
    have : ∫ x, phi Φ a x * (-(d : ℝ) * phi Φ a x) ∂μ = -((d : ℝ) * ∫ x, (phi Φ a x) ^ 2 ∂μ) := by
      rw [← integral_const_mul, ← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    rw [this]; ring


/-- Some coordinate function has positive `L²` norm. -/
lemma exists_coord_pos {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ) (μ : Measure M) [IsProbabilityMeasure μ] :
    ∃ i : Fin (Module.finrank ℝ 𝔼), 0 < ∫ x, (phi Φ (bb i) x) ^ 2 ∂μ := by
  have hint : ∀ i, Integrable (fun x => (phi Φ (bb i) x) ^ 2) μ := fun i =>
    ((contMDiff_phi hΦ (bb i)).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : ∑ i, ∫ x, (phi Φ (bb i) x) ^ 2 ∂μ = 1 := by
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    have : ∀ x, ∑ i, (phi Φ (bb i) x) ^ 2 = 1 := by
      intro x
      have h := (bb).sum_sq_norm_inner_right (Φ x)
      rw [hΦ.1 x] at h
      simpa [phi, real_inner_comm, sq_abs] using h
    simp [this]
  by_contra hcon
  push_neg at hcon
  have : ∀ i, ∫ x, (phi Φ (bb i) x) ^ 2 ∂μ = 0 := fun i =>
    le_antisymm (hcon i) (integral_nonneg fun x => sq_nonneg _)
  simp [this] at hsum

/-- **`λ₁ ≤ d` on the model of the round `S^d`** for any weighted volume with constant potential. -/
theorem sphere_gap_le (hF : Module.finrank ℝ F = d) (hd : 1 ≤ d) {Φ : M → 𝔼}
    (hΦ : IsIsometricSphereMap F Φ) {μ : Measure M} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume F μ (fun _ => c)) : mSpectralGap F μ ≤ d := by
  obtain ⟨i, hi⟩ := exists_coord_pos hΦ μ
  set f := phi Φ (bb i) with hfdef
  obtain ⟨hm, hg⟩ := integral_phi_identities hF hd hΦ hμ (bb i)
  have hfs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f := contMDiff_phi hΦ _
  have hcont : Continuous f := hfs.continuous
  have hvar : variance f μ = ∫ x, (f x) ^ 2 ∂μ := by
    rw [variance_of_integral_eq_zero hcont.aemeasurable hm]
  have hpos : 0 < variance f μ := by rw [hvar]; exact hi
  have hmem : (d : ℝ) ∈ {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧
      0 < variance f μ ∧ r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} := by
    refine ⟨f, hfs, HasCompactSupport.of_compactSpace f, hpos, ?_⟩
    rw [hg, hvar]
    field_simp
    rfl
  have hbdd : BddBelow {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧
      HasCompactSupport f ∧ 0 < variance f μ ∧
      r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} := by
    refine ⟨0, ?_⟩
    rintro r ⟨g, -, -, hg, rfl⟩
    exact div_nonneg (integral_nonneg fun x => by positivity) hg.le
  exact csInf_le hbdd hmem

end CutoffRigidity.Extra.Sphere
