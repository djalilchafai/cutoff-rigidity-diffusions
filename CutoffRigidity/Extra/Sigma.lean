module

public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Extra.Temperature

/-! # The `σ`-diffusion kernels: time change, existence, uniqueness, invariance

`IsSigmaLangevinInf V σ Pt` (generator `σ²Δ - ∇V·∇`) is the time change by `σ²` of
`IsEuclideanLangevinInf (V/σ²)`: `Pt t = P̃ (σ² t)`. Consequences: existence (no convexity needed),
uniqueness, and invariance of the Gibbs probability `e^{-V/σ²}dx`.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutCur

open CutoffRigidity CutoffRigidity.Riemann
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Manifold

/-- Kolmogorov's equation is transported by the time change `u ↦ a u`. -/
theorem kolmogorov_timeScale {d : ℕ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    {A B : (Rd d → ℝ) → Rd d → ℝ} (a : ℝ≥0) (ha : a ≠ 0)
    (hAB : ∀ f, ContDiff ℝ ∞ f → ∀ y, (a : ℝ) * A f y = B f y)
    (h : ∀ f : Rd d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ (x : Rd d) (t : ℝ≥0),
      ∫ y, f y ∂Pt t x = f x + ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, A f y ∂Pt s.toNNReal x) :
    ∀ f : Rd d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ (x : Rd d) (t : ℝ≥0),
      ∫ y, f y ∂(fun u => Pt (a * u)) t x = f x + ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ y, B f y ∂(fun u => Pt (a * u)) s.toNNReal x := by
  intro f hf hfc x t
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hd := h f hf hfc x (a * t)
  simp only
  rw [hd]
  congr 1
  set G : ℝ → ℝ := fun s => ∫ y, A f y ∂Pt s.toNNReal x with hG
  have hF : ∀ r : ℝ, ∫ y, B f y ∂Pt (a * r.toNNReal) x = (a : ℝ) * G ((a : ℝ) * r) := by
    intro r
    have e1 : ((a : ℝ) * r).toNNReal = a * r.toNNReal := by
      rw [Real.toNNReal_mul a.coe_nonneg, Real.toNNReal_coe]
    simp only [hG, e1]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hAB f hf y).symm)
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := (t : ℝ))
    (fun s => G s) ha'
  simp only [intervalIntegral.integral_congr (fun r _ => hF r), intervalIntegral.integral_const_mul]
  rw [this]
  simp only [mul_zero, NNReal.coe_mul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ ha', one_mul]

/-- The time change `u ↦ a u` preserves the Markov-semigroup part. -/
theorem markov_semigroup_timeScale {d : ℕ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (a : ℝ≥0)
    (hm : ∀ t, IsMarkovKernel (Pt t)) (hs : ∀ s t, Pt (s + t) = Pt t ∘ₖ Pt s) :
    (∀ t, IsMarkovKernel ((fun u => Pt (a * u)) t)) ∧
      ∀ s t, (fun u => Pt (a * u)) (s + t) = (fun u => Pt (a * u)) t ∘ₖ (fun u => Pt (a * u)) s :=
  ⟨fun t => hm _, fun s t => by simp only; rw [mul_add]; exact hs _ _⟩

private lemma sig_c_mul {σ : ℝ} (hσ : 0 < σ) :
    ((σ ^ 2).toNNReal) * (((σ ^ 2)⁻¹).toNNReal) = 1 := by
  rw [← Real.toNNReal_mul (by positivity), mul_inv_cancel₀ (by positivity)]; simp

private lemma sig_ne {σ : ℝ} (hσ : 0 < σ) : ((σ ^ 2).toNNReal) ≠ 0 := by
  intro h
  have := sig_c_mul hσ
  rw [h, zero_mul] at this; exact zero_ne_one this

private lemma sig_ne' {σ : ℝ} (hσ : 0 < σ) : (((σ ^ 2)⁻¹).toNNReal) ≠ 0 := by
  intro h
  have := sig_c_mul hσ
  rw [h, mul_zero] at this; exact zero_ne_one this

private lemma sig_coe {σ : ℝ} (hσ : 0 < σ) : (((σ ^ 2).toNNReal : ℝ≥0) : ℝ) = σ ^ 2 :=
  Real.coe_toNNReal _ (by positivity)

private lemma sig_coe' {σ : ℝ} (hσ : 0 < σ) :
    ((((σ ^ 2)⁻¹).toNNReal : ℝ≥0) : ℝ) = (σ ^ 2)⁻¹ :=
  Real.coe_toNNReal _ (by positivity)

/-- **Time change, diffusion part.** The `σ`-diffusion semigroup `Pt` (generator `σ²Δ - ∇V·∇`) is
the same thing as a Euclidean diffusion semigroup for `V/σ²` after the time change `u ↦ Pt (u/σ²)`,
i.e. `Pt t = P̃ (σ² t)`. -/
theorem isSigmaDiffusion_iff {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hV : Differentiable ℝ V) {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} :
    IsSigmaDiffusion V σ Pt ↔
      IsEuclideanDiffusion (fun x => V x / σ ^ 2) (fun u => Pt (((σ ^ 2)⁻¹).toNNReal * u)) := by
  have hs2 : (σ ^ 2) ≠ 0 := by positivity
  have key : ∀ f : Rd d → ℝ, ∀ y,
      generator (fun x => V x / σ ^ 2) f y =
        (σ ^ 2)⁻¹ * (σ ^ 2 * laplacian f y - inner ℝ (gradient V y) (gradient f y)) := by
    intro f y
    simp only [generator, CutoffRigidity.Paper.gradient_div_const hV, inner_smul_left,
      conj_trivial]
    field_simp
  have key' : ∀ f : Rd d → ℝ, ∀ y,
      σ ^ 2 * generator (fun x => V x / σ ^ 2) f y =
        σ ^ 2 * laplacian f y - inner ℝ (gradient V y) (gradient f y) := by
    intro f y; rw [key]; field_simp
  constructor
  · rintro ⟨hm, hs, hk⟩
    obtain ⟨hm', hs'⟩ := markov_semigroup_timeScale (((σ ^ 2)⁻¹).toNNReal) hm hs
    refine ⟨hm', hs', kolmogorov_timeScale _ (sig_ne' hσ) (A := fun f y =>
      σ ^ 2 * laplacian f y - inner ℝ (gradient V y) (gradient f y)) ?_ hk⟩
    intro f _ y
    rw [sig_coe' hσ, ← key]
  · rintro ⟨hm, hs, hk⟩
    have hPt : Pt = fun u => (fun u => Pt (((σ ^ 2)⁻¹).toNNReal * u)) (((σ ^ 2).toNNReal) * u) := by
      funext u; simp only; rw [← mul_assoc, mul_comm _ ((σ ^ 2).toNNReal), sig_c_mul hσ, one_mul]
    obtain ⟨hm', hs'⟩ := markov_semigroup_timeScale ((σ ^ 2).toNNReal) hm hs
    rw [hPt]
    refine ⟨hm', hs', kolmogorov_timeScale _ (sig_ne hσ) (A := generator (fun x => V x / σ ^ 2))
      ?_ hk⟩
    intro f _ y
    rw [sig_coe hσ, key']

/-- `IsSigmaLangevinInf` is `IsEuclideanLangevinInf` for `V/σ²` after the time change `Pt (u/σ²)`. -/
theorem isSigmaLangevin_iff {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} :
    IsSigmaLangevinInf V σ Pt ↔
      IsEuclideanLangevinInf (fun x => V x / σ ^ 2) (fun u => Pt (((σ ^ 2)⁻¹).toNNReal * u)) := by
  unfold IsSigmaLangevinInf IsEuclideanLangevinInf
  have hc : ContDiff ℝ ∞ V ↔ ContDiff ℝ ∞ (fun x => V x / σ ^ 2) := by
    constructor
    · exact fun h => h.div_const _
    · intro (h : ContDiff ℝ ∞ (fun x => V x / σ ^ 2))
      have := ContDiff.mul h (contDiff_const (c := σ ^ 2))
      simpa [div_mul_cancel₀ _ (pow_ne_zero 2 hσ.ne')] using this
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hc.1 h1, h2, (isSigmaDiffusion_iff hσ (h1.differentiable (by simp))).1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    have h1' := hc.2 h1
    exact ⟨h1', h2, (isSigmaDiffusion_iff hσ (h1'.differentiable (by simp))).2 h3⟩

/-- **Existence** of the `σ`-diffusion (no convexity needed): for every `σ > 0` and smooth `V` with
`e^{-V/σ²}` a probability density there is `Pt` with `IsSigmaLangevinInf V σ Pt`. -/
theorem exists_sigmaLangevin {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hV : ContDiff ℝ ∞ V) (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2)) :
    ∃ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsSigmaLangevinInf V σ Pt := by
  obtain ⟨Q, hQ⟩ := exists_euclideanLangevin_of_smooth (hV.div_const (σ ^ 2)) hp
  refine ⟨fun u => Q ((σ ^ 2).toNNReal * u), (isSigmaLangevin_iff hσ).2 ?_⟩
  have : (fun u => (fun u => Q ((σ ^ 2).toNNReal * u)) (((σ ^ 2)⁻¹).toNNReal * u)) = Q := by
    funext u; simp only; rw [← mul_assoc, sig_c_mul hσ, one_mul]
  rw [this]; exact hQ

/-- **Time change in kernel form**: `Pt t = P̃ (σ² t)` for any Euclidean Langevin semigroup `P̃` of
`V/σ²` (so the `σ`-diffusion is unique, and determined by `P̃`). -/
theorem sigmaLangevin_eq_timeChange {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {Pt Q : ℝ≥0 → Kernel (Rd d) (Rd d)} (hP : IsSigmaLangevinInf V σ Pt)
    (hQ : IsEuclideanLangevinInf (fun x => V x / σ ^ 2) Q) (t : ℝ≥0) (x : Rd d) :
    Pt t x = Q ((σ ^ 2).toNNReal * t) x := by
  have h := isEuclideanLangevin_unique ((isSigmaLangevin_iff hσ).1 hP) hQ ((σ ^ 2).toNNReal * t) x
  beta_reduce at h
  rwa [← mul_assoc, mul_comm _ ((σ ^ 2).toNNReal), sig_c_mul hσ, one_mul] at h

/-- Uniqueness of the `σ`-diffusion kernels. -/
theorem isSigmaLangevin_unique {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d)} (h₁ : IsSigmaLangevinInf V σ P₁)
    (h₂ : IsSigmaLangevinInf V σ P₂) (t : ℝ≥0) (x : Rd d) : P₁ t x = P₂ t x := by
  rw [sigmaLangevin_eq_timeChange hσ h₁ ((isSigmaLangevin_iff hσ).1 h₂) t x]
  show P₂ (((σ ^ 2)⁻¹).toNNReal * ((σ ^ 2).toNNReal * t)) x = P₂ t x
  rw [← mul_assoc, mul_comm _ ((σ ^ 2).toNNReal), sig_c_mul hσ, one_mul]

/-- Invariance of the Gibbs probability for a Euclidean Langevin semigroup. -/
theorem isEuclideanLangevin_invariant {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : IsEuclideanLangevinInf V Pt) (t : ℝ≥0) : (gibbs V).bind (Pt t) = gibbs V := by
  have : IsProbabilityMeasure (gibbs V) := h.2.1
  have hV' : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) ∞ V := contMDiff_iff_contDiff.2 h.1
  have hμ := Riemann.Witness.isWeightedVolume_gibbs V
  have hK : IsEuclideanLangevinInf V (Diff.Kk (Rd d) hV' hμ) :=
    ⟨h.1, h.2.1, isEuclideanDiffusion_iff.2 (Diff.isDiffusionSemigroup_Kk (Rd d) hV' hμ)⟩
  have hfun : ⇑(Pt t) = ⇑(Diff.Kk (Rd d) hV' hμ t) :=
    funext fun x => isEuclideanLangevin_unique h hK t x
  rw [hfun]
  exact Diff.Kk_bind (Rd d) hV' hμ t

/-- **Invariance** of the Gibbs probability `e^{-V/σ²}dx` under the `σ`-diffusion kernels. -/
theorem isSigmaLangevin_invariant {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (h : IsSigmaLangevinInf V σ Pt) (t : ℝ≥0) :
    (gibbs fun x => V x / σ ^ 2).bind (Pt t) = gibbs fun x => V x / σ ^ 2 := by
  have hE := (isSigmaLangevin_iff hσ).1 h
  have := isEuclideanLangevin_invariant hE ((σ ^ 2).toNNReal * t)
  beta_reduce at this
  rwa [← mul_assoc, mul_comm _ ((σ ^ 2).toNNReal), sig_c_mul hσ, one_mul] at this

/-- Compact Challenge-style bundle (kernel form of `temperature_sde`): for `σ > 0`, smooth `V` with
`e^{-V/σ²}` a probability density, the `σ`-diffusion exists, leaves the Gibbs probability
`e^{-V/σ²}dx` invariant, and is the time change `Pt t = P̃ (σ² t)` of every Euclidean Langevin
semigroup `P̃` for `V/σ²`. -/
theorem temperature_kernel_smooth {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hV : ContDiff ℝ ∞ V) (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2)) :
    (∃ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsSigmaLangevinInf V σ Pt) ∧
    ∀ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsSigmaLangevinInf V σ Pt →
      (∀ t, (gibbs fun x => V x / σ ^ 2).bind (Pt t) = gibbs fun x => V x / σ ^ 2) ∧
      ∀ Q : ℝ≥0 → Kernel (Rd d) (Rd d), IsEuclideanLangevinInf (fun x => V x / σ ^ 2) Q →
        ∀ t x, Pt t x = Q ((σ ^ 2).toNNReal * t) x := by
  exact ⟨exists_sigmaLangevin hσ hV hp, fun Pt h =>
    ⟨isSigmaLangevin_invariant hσ h, fun Q hQ => sigmaLangevin_eq_timeChange hσ h hQ⟩⟩

end CutCur
