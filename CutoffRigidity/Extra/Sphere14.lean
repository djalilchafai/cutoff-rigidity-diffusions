module

public import CutoffRigidity.Extra.Sphere13

/-! # Sphere, stage 14: `λ₁ ≥ d` (Lichnerowicz-Obata) on the model of `S^d`

Existence of a first eigenfunction (stage 12), the Bochner identity with `Ric = (d-1) g`, the dimensional
inequality `(Δf)² ≤ d‖Hess f‖²` and integration by parts give `λ² ≥ λ²/d + (d-1) λ`, i.e. `λ ≥ d`.
-/

@[expose] public section

open Bundle Filter Set VectorField MeasureTheory
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutoffRigidity.Riemann.Diff

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- Pointwise dimensional Bochner inequality on the model of the sphere (constant potential):
`Γ₂(f) ≥ (𝓛 f)²/d + (d-1) Γ(f)`. -/
theorem carre2_ge (hF : Module.finrank ℝ F = d) (hd : 1 ≤ d) {Φ : M → 𝔼}
    (hΦ : IsIsometricSphereMap F Φ) (c : ℝ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (mgenerator F (fun _ : M => c) f x) ^ 2 / d + ((d : ℝ) - 1) * carre F f f x ≤
      carre2 F (fun _ : M => c) f x := by
  rw [CutoffRigidity.Paper.bochner_identity F (contMDiff_const (c := c)) hf x,
    mHess_const, sphere_mRic hF hΦ, ← carre, add_zero]
  have h1 := mlaplacian_sq_le (F := F) f x
  rw [hF] at h1
  have hgen : mgenerator F (fun _ : M => c) f x = mlaplacian F f x := by
    unfold mgenerator; rw [mgrad_const]; simp
  rw [hgen]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have : (mlaplacian F f x) ^ 2 / d ≤ mHessSq F f x := by
    rw [div_le_iff₀ hdpos]; linarith
  have e : carre F f f x = inner ℝ (mgrad F f x) (mgrad F f x) := rfl
  rw [e]
  linarith


/-- **`λ₁ ≥ d` on the model of the round `S^d`** (`d ≥ 2`), for a probability weighted volume with constant potential:
Lichnerowicz-Obata, from the existence of a first eigenfunction (no `CD`/`hgap` hypothesis needed). -/
theorem sphere_gap_ge (hF : Module.finrank ℝ F = d) (hd : 2 ≤ d) {Φ : M → 𝔼}
    (hΦ : IsIsometricSphereMap F Φ) {μ : Measure M} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume F μ (fun _ => c)) : (d : ℝ) ≤ mSpectralGap F μ := by
  have hV : MSmooth F (fun _ : M => c) := contMDiff_const
  set lam := mSpectralGap F μ with hlam
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlam1 : (d : ℝ) - 1 ≤ lam :=
    CutoffRigidity.Paper.mSpectralGap_ge_of_CD F (by omega) contMDiff_const hμ (by linarith)
      (sphere_CD hF hΦ c)
  have hlampos : 0 < lam := by linarith
  have hcomp := fun C : ℝ => Qball_totallyBounded_of_tail F hV hμ
    (fun C ε hε => ⟨univ, isCompact_univ, fun f _ => by simpa using hε.le⟩) C
  obtain ⟨f, ⟨hfs, -, hEq⟩, x0, hx0⟩ :=
    exists_eigenfunction_of_compact_gap F hV hμ hlampos rfl hcomp
  have hfc : Continuous f := hfs.continuous
  have hopen := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  have hsq : MSmooth F (fun x => f x ^ 2) := by
    have : (fun x => f x ^ 2) = fun x => f x * f x := by funext x; ring
    rw [this]; exact hfs.mul hfs
  set I := ∫ x, (f x) ^ 2 ∂μ with hI
  have hIpos : 0 < I :=
    (hfc.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
      (fun x => sq_nonneg _) (pow_ne_zero 2 hx0) |>.trans_eq' rfl
  have hibp := CutCur.weightedIBP_of_isWeightedVolume F hV hμ
  have hcarre : MSmooth F (carre F f f) := CutCur.WReg.msmooth_carre hfs hfs
  -- E1 : ∫ 𝓛 (Γ f) = 0
  have E1 : ∫ x, mgenerator F (fun _ : M => c) (carre F f f) x ∂μ = 0 := by
    have h := hibp (fun _ => (1 : ℝ)) (carre F f f) contMDiff_const hcarre
      (HasCompactSupport.of_compactSpace _)
    have hc0 : ∀ x, carre F (fun _ : M => (1 : ℝ)) (carre F f f) x = 0 := by
      intro x; simp [carre, mgrad_const]
    simp only [hc0, integral_zero, one_mul] at h
    linarith
  -- E2 : ∫ Γ(f) = lam ∫ f²
  have E2 : ∫ x, carre F f f x ∂μ = lam * I := by
    have h := hibp f f hfs hfs (HasCompactSupport.of_compactSpace _)
    simp only [hEq] at h
    rw [h, hI, ← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  -- E3 : Γ(f, 𝓛 f) = -lam Γ(f)
  have E3 : ∀ x, carre F f (mgenerator F (fun _ : M => c) f) x = -lam * carre F f f x := by
    intro x
    have hfun : mgenerator F (fun _ : M => c) f = fun y => -lam * f y := funext hEq
    rw [hfun]
    simp only [carre, mgrad_const_mul F (-lam) hfs x, real_inner_smul_right]
  have hG : ∀ x, carre2 F (fun _ : M => c) f x =
      mgenerator F (fun _ : M => c) (carre F f f) x / 2 + lam * carre F f f x := by
    intro x
    unfold carre2
    rw [E3 x]; ring
  have hint1 : Integrable (mgenerator F (fun _ : M => c) (carre F f f)) μ :=
    (continuous_iff_continuousAt.mpr (CutCur.continuousAt_mgenerator F hV hcarre)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (carre F f f) μ :=
    (CutCur.continuous_carre F hfs hfs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint3 : Integrable (fun x => (f x) ^ 2) μ :=
    (hfc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdpos : (0 : ℝ) < d := by linarith
  -- integrate Bochner
  have hlow : Integrable (fun x => (mgenerator F (fun _ : M => c) f x) ^ 2 / d + ((d : ℝ) - 1) * carre F f f x) μ := by
    have : (fun x => (mgenerator F (fun _ : M => c) f x) ^ 2 / d + ((d : ℝ) - 1) * carre F f f x) =
        fun x => lam ^ 2 / d * (f x) ^ 2 + ((d : ℝ) - 1) * carre F f f x := by
      funext x; rw [hEq x]; ring
    rw [this]
    exact (hint3.const_mul _).add (hint2.const_mul _)
  have hhigh : Integrable (carre2 F (fun _ : M => c) f) μ := by
    have : carre2 F (fun _ : M => c) f = fun x =>
        mgenerator F (fun _ : M => c) (carre F f f) x / 2 + lam * carre F f f x := funext hG
    rw [this]
    exact (hint1.div_const _).add (hint2.const_mul _)
  have hmono := integral_mono hlow hhigh (fun x => carre2_ge hF (by omega) hΦ c hfs x)
  have hL : ∫ x, (mgenerator F (fun _ : M => c) f x) ^ 2 / d + ((d : ℝ) - 1) * carre F f f x ∂μ =
      lam ^ 2 / d * I + ((d : ℝ) - 1) * (lam * I) := by
    have : (fun x => (mgenerator F (fun _ : M => c) f x) ^ 2 / d + ((d : ℝ) - 1) * carre F f f x) =
        fun x => lam ^ 2 / d * (f x) ^ 2 + ((d : ℝ) - 1) * carre F f f x := by
      funext x; rw [hEq x]; ring
    rw [this, integral_add (hint3.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul, E2]
  have hH : ∫ x, carre2 F (fun _ : M => c) f x ∂μ = lam * (lam * I) := by
    have : carre2 F (fun _ : M => c) f = fun x =>
        mgenerator F (fun _ : M => c) (carre F f f) x / 2 + lam * carre F f f x := funext hG
    rw [this, integral_add (hint1.div_const _) (hint2.const_mul _), integral_div, E1, integral_const_mul, E2]
    ring
  rw [hL, hH] at hmono
  -- λ² I ≥ λ² I / d + (d-1) λ I  ⇒  λ ≥ d
  have h5 : 0 ≤ lam * I * (lam - d) := by
    have : lam * (lam * I) - lam ^ 2 / d * I - ((d : ℝ) - 1) * (lam * I) =
        lam * I * (lam - d) * ((d : ℝ) - 1) / d := by field_simp
    have h6 : 0 ≤ lam * (lam * I) - lam ^ 2 / d * I - ((d : ℝ) - 1) * (lam * I) := by linarith
    rw [this] at h6
    have h7 : 0 < ((d : ℝ) - 1) / d := by apply div_pos <;> linarith
    have : lam * I * (lam - d) * ((d : ℝ) - 1) / d = lam * I * (lam - d) * (((d : ℝ) - 1) / d) := by ring
    rw [this] at h6
    exact nonneg_of_mul_nonneg_left h6 h7
  have h8 : 0 < lam * I := mul_pos hlampos hIpos
  have := nonneg_of_mul_nonneg_right h5 h8
  linarith

end CutoffRigidity.Extra.Sphere
