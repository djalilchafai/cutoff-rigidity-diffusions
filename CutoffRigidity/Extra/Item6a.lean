module

public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.RiemannLichnerowicz

/-! # Item 6(a): the round sphere, upper bound `lambda_1 <= d` (model-theoretic form)

Manuscript (about line 711): "for the d-dimensional unit sphere, rho = d - 1 and lambda_1 = d".
Mathlib has no `RiemannianBundle` on the sphere, so the statements below are about any
Riemannian manifold `M` carrying an isometric smooth map `Phi : M -> S^d ⊂ R^(d+1)` (a model of
the round sphere), exactly the `sphere_curvature_gap` format of `scope-status/geoB.md`.
No instance of such an `M` is constructed here (see `extra-status/item6-worker.md`).
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- `Phi` is an isometric immersion into the unit sphere of `E`: the pulled back Euclidean
inner product is the Riemannian one. -/
def IsIsometricSphereMap {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Φ : M → E) : Prop :=
  (∀ x, ‖Φ x‖ = 1) ∧ ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ Φ ∧
    ∀ (x : M) (v w : TangentSpace 𝓘(ℝ, F) x),
      inner ℝ v w = inner ℝ (mvfderiv 𝓘(ℝ, F) Φ x v) (mvfderiv 𝓘(ℝ, F) Φ x w)

variable {d : ℕ}

lemma mvfderiv_comp_clm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : M → E)
    (hΦ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ Φ) (L : E →L[ℝ] ℝ) (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => L (Φ y)) x v = L (mvfderiv 𝓘(ℝ, F) Φ x v) := by
  have h1 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) Φ x :=
    (hΦ.mdifferentiable (by simp)) x
  have h2 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) L (Φ x) := L.differentiableAt.mdifferentiableAt
  have := mvfderiv_comp_apply x h2 h1 v
  rw [show (fun y => L (Φ y)) = (L ∘ Φ) from rfl, this, mvfderiv_eq_fderiv]
  simp
  rfl


section sphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_Phi_deriv {Φ : M → E} (hΦ : IsIsometricSphereMap F Φ) (x : M)
    (v : TangentSpace 𝓘(ℝ, F) x) : inner ℝ (Φ x) (mvfderiv 𝓘(ℝ, F) Φ x v) = 0 := by
  obtain ⟨hn, hs, -⟩ := hΦ
  have h1 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) Φ x := (hs.mdifferentiable (by simp)) x
  have hg : DifferentiableAt ℝ (fun y : E => ‖y‖ ^ 2) (Φ x) :=
    (hasStrictFDerivAt_norm_sq (Φ x)).hasFDerivAt.differentiableAt
  have h2 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y : E => ‖y‖ ^ 2) (Φ x) := hg.mdifferentiableAt
  have hc := mvfderiv_comp_apply x h2 h1 v
  have hconst : (fun y : E => ‖y‖ ^ 2) ∘ Φ = fun _ => (1 : ℝ) := by
    funext y; simp [hn]
  rw [hconst, mvfderiv_const] at hc
  rw [mvfderiv_eq_fderiv] at hc
  have hd : fderiv ℝ (fun y : E => ‖y‖ ^ 2) (Φ x) = (2 : ℕ) • innerSL ℝ (Φ x) :=
    (hasStrictFDerivAt_norm_sq (Φ x)).hasFDerivAt.fderiv
  rw [hd] at hc
  simp at hc
  exact hc

end sphere

section grad

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The differential of an isometric map to the unit sphere has range exactly `(Φ x)^⊥`. -/
lemma range_deriv_eq {Φ : M → 𝔼} (hF : Module.finrank ℝ F = d) (hΦ : IsIsometricSphereMap F Φ)
    (x : M) :
    LinearMap.range (mvfderiv 𝓘(ℝ, F) Φ x : TangentSpace 𝓘(ℝ, F) x →ₗ[ℝ] 𝔼) =
      (ℝ ∙ Φ x)ᗮ := by
  have hinj : Function.Injective (mvfderiv 𝓘(ℝ, F) Φ x) := by
    intro v w hvw
    have h := hΦ.2.2 x (v - w) (v - w)
    rw [map_sub, hvw, sub_self, inner_zero_right] at h
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h)
  have hle : LinearMap.range (mvfderiv 𝓘(ℝ, F) Φ x : TangentSpace 𝓘(ℝ, F) x →ₗ[ℝ] 𝔼) ≤
      (ℝ ∙ Φ x)ᗮ := by
    rintro _ ⟨v, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact inner_Phi_deriv F hΦ x v
  have hfact : Fact (Module.finrank ℝ 𝔼 = d + 1) := ⟨by simp⟩
  have hn : Φ x ≠ 0 := by
    intro h; have := hΦ.1 x; rw [h] at this; simp at this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [Submodule.finrank_orthogonal_span_singleton (n := d) hn]
  have := LinearMap.finrank_range_of_inj
    (f := (mvfderiv 𝓘(ℝ, F) Φ x : TangentSpace 𝓘(ℝ, F) x →ₗ[ℝ] 𝔼)) hinj
  rw [this]
  exact hF

/-- For `f = ⟨a, Φ⟩`: `|∇f|² = |a|² - ⟨a, Φ⟩²` (tangential part of `a`). -/
lemma norm_mgrad_sq {Φ : M → 𝔼} (hF : Module.finrank ℝ F = d) (hΦ : IsIsometricSphereMap F Φ)
    (a : 𝔼) (x : M) :
    ‖mgrad F (fun y => inner ℝ a (Φ y)) x‖ ^ 2 = ‖a‖ ^ 2 - (inner ℝ a (Φ x)) ^ 2 := by
  set D := mvfderiv 𝓘(ℝ, F) Φ x with hD
  set c : ℝ := inner ℝ a (Φ x) with hc
  have hn1 : ‖Φ x‖ = 1 := hΦ.1 x
  have hw : a - c • Φ x ∈ (ℝ ∙ Φ x)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hn1, real_inner_comm]
    simp [hc]
  rw [← range_deriv_eq F hF hΦ x] at hw
  obtain ⟨v₀, hv₀⟩ := hw
  have hv₀' : D v₀ = a - c • Φ x := hv₀
  set u := mgrad F (fun y => inner ℝ a (Φ y)) x with hu
  have hgrad : ∀ v : TangentSpace 𝓘(ℝ, F) x, inner ℝ u v = inner ℝ a (D v) := by
    intro v
    have h1 : inner ℝ u v = mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ a (Φ y)) x v := by
      rw [hu, mgrad, InnerProductSpace.toDual_symm_apply]
    rw [h1]
    exact mvfderiv_comp_clm F Φ hΦ.2.1 (innerSL ℝ a) x v
  have hv : ∀ v : TangentSpace 𝓘(ℝ, F) x, inner ℝ v₀ v = inner ℝ a (D v) := by
    intro v
    rw [hΦ.2.2 x v₀ v, hv₀', inner_sub_left, inner_smul_left, inner_Phi_deriv F hΦ x v]
    simp [hD]
  have huv : u = v₀ := by
    have : inner ℝ (u - v₀) (u - v₀) = 0 := by
      rw [inner_sub_left, hgrad, hv]; simp
    exact sub_eq_zero.mp (inner_self_eq_zero.mp this)
  rw [huv, ← real_inner_self_eq_norm_sq, hΦ.2.2 x v₀ v₀, hv₀', real_inner_self_eq_norm_sq]
  have : ‖a - c • Φ x‖ ^ 2 = ‖a‖ ^ 2 - c ^ 2 := by
    rw [@norm_sub_sq_real, norm_smul, mul_pow, inner_smul_right, hn1, real_inner_comm]
    simp [hc]; rw [real_inner_comm (Φ x) a]; ring
  exact this

end grad

section gap

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable [MeasurableSpace M] [BorelSpace M]

/-- Invariance of `∫ g(Φ)` under a linear isometry, from invariance of the pushforward. -/
lemma integral_comp_iso {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ) {μ : Measure M}
    (hμ : ∀ T : 𝔼 ≃ₗᵢ[ℝ] 𝔼, μ.map (fun x => T (Φ x)) = μ.map Φ) (T : 𝔼 ≃ₗᵢ[ℝ] 𝔼)
    (g : 𝔼 → ℝ) (hg : Continuous g) :
    ∫ x, g (T (Φ x)) ∂μ = ∫ x, g (Φ x) ∂μ := by
  have hc : Continuous Φ := hΦ.2.1.continuous
  have h1 := integral_map (μ := μ) (φ := fun x => T (Φ x)) (f := g)
    (T.continuous.comp hc).aemeasurable hg.aestronglyMeasurable
  have h2 := integral_map (μ := μ) (φ := Φ) (f := g) hc.aemeasurable hg.aestronglyMeasurable
  rw [← h1, ← h2, hμ T]

lemma integrable_coord_sq {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ) (μ : Measure M)
    [IsProbabilityMeasure μ] (i : Fin (d + 1)) :
    Integrable (fun x => (Φ x i) ^ 2) μ := by
  have hc : Continuous Φ := hΦ.2.1.continuous
  refine Integrable.of_bound (C := 1) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have h1 : |Φ x i| ≤ ‖Φ x‖ := by
    simpa using PiLp.norm_apply_le (Φ x) i
  have h2 : |Φ x i| ≤ 1 := h1.trans (hΦ.1 x).le
  rw [Real.norm_eq_abs, abs_pow]
  nlinarith [abs_nonneg (Φ x i)]

/-- Rotation invariance gives `∫ (Φ_0)² = 1/(d+1)` and `∫ Φ_0 = 0`. -/
lemma coord_moments {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ) {μ : Measure M}
    [IsProbabilityMeasure μ]
    (hμ : ∀ T : 𝔼 ≃ₗᵢ[ℝ] 𝔼, μ.map (fun x => T (Φ x)) = μ.map Φ) :
    ∫ x, (Φ x 0) ^ 2 ∂μ = 1 / ((d : ℝ) + 1) ∧ ∫ x, Φ x 0 ∂μ = 0 := by
  have hc : Continuous Φ := hΦ.2.1.continuous
  constructor
  · have hall : ∀ i : Fin (d + 1), ∫ x, (Φ x i) ^ 2 ∂μ = ∫ x, (Φ x 0) ^ 2 ∂μ := by
      intro i
      have := integral_comp_iso F hΦ hμ
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin (d + 1)) i))
        (fun y => (y 0) ^ 2) (by fun_prop)
      simp only [LinearIsometryEquiv.piLpCongrLeft_apply] at this
      simpa using this
    have hsum : ∫ x, ∑ i, (Φ x i) ^ 2 ∂μ = 1 := by
      have : ∀ x, ∑ i, (Φ x i) ^ 2 = 1 := by
        intro x
        have h := hΦ.1 x
        have h2 : ‖Φ x‖ ^ 2 = 1 := by rw [h]; norm_num
        rw [EuclideanSpace.norm_sq_eq] at h2
        simpa using h2
      simp [this]
    rw [integral_finsetSum _ (fun i _ => integrable_coord_sq F hΦ μ i)] at hsum
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    field_simp
    linarith
  · have := integral_comp_iso F hΦ hμ (LinearIsometryEquiv.neg ℝ) (fun y => y 0) (by fun_prop)
    simp only [LinearIsometryEquiv.coe_neg, PiLp.neg_apply, integral_neg] at this
    linarith

/-- **Upper bound `λ₁ ≤ d` on the round `d`-sphere** (model form): if `M` is a compact `d`-dimensional
Riemannian manifold with an isometric smooth map `Φ` into the unit sphere of `ℝ^{d+1}` and `μ` is a
probability measure whose image under `Φ` is invariant under all linear isometries of `ℝ^{d+1}`
(the normalized round measure), then the Poincaré constant is at most `d`; the coordinate function
`x ↦ Φ(x)₀` attains the Rayleigh quotient `d`. -/
theorem sphere_spectralGap_le [CompactSpace M] {Φ : M → 𝔼} (hF : Module.finrank ℝ F = d)
    (hΦ : IsIsometricSphereMap F Φ) {μ : Measure M} [IsProbabilityMeasure μ]
    (hμ : ∀ T : 𝔼 ≃ₗᵢ[ℝ] 𝔼, μ.map (fun x => T (Φ x)) = μ.map Φ) :
    mSpectralGap F μ ≤ d := by
  obtain ⟨hs, hm⟩ := coord_moments F hΦ hμ
  have hc : Continuous Φ := hΦ.2.1.continuous
  set e : 𝔼 := EuclideanSpace.single 0 1 with he
  set f : M → ℝ := fun y => inner ℝ e (Φ y) with hf
  have hfy : ∀ y, f y = Φ y 0 := by
    intro y; simp only [hf, he]; rw [EuclideanSpace.inner_single_left]; simp
  have hfs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f := by
    have : ContDiff ℝ ∞ (fun z : 𝔼 => inner ℝ e z) := contDiff_const.inner ℝ contDiff_id
    exact this.comp_contMDiff hΦ.2.1
  have hvar : variance f μ = 1 / ((d : ℝ) + 1) := by
    rw [variance_of_integral_eq_zero (by
      have : Continuous f := by
        have : f = fun y => (EuclideanSpace.proj (0 : Fin (d + 1)) : 𝔼 →L[ℝ] ℝ) (Φ y) := by
          funext y; rw [hfy]; rfl
        rw [this]; exact (EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp hc
      exact this.aemeasurable) (by simpa [hfy] using hm)]
    simpa [hfy] using hs
  have hpos : 0 < variance f μ := by rw [hvar]; positivity
  have hint : ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ = 1 - 1 / ((d : ℝ) + 1) := by
    have : ∀ x, ‖mgrad F f x‖ ^ 2 = 1 - (Φ x 0) ^ 2 := by
      intro x
      rw [norm_mgrad_sq F hF hΦ e x]
      have h1 : ‖e‖ = 1 := by simp [he]
      have h2 : inner ℝ e (Φ x) = Φ x 0 := hfy x
      rw [h1, h2]; norm_num
    simp only [this]
    rw [integral_sub (integrable_const _) (integrable_coord_sq F hΦ μ 0), hs]
    simp
  have hmem : (1 - 1 / ((d : ℝ) + 1)) / (1 / ((d : ℝ) + 1)) ∈
      {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧
        0 < variance f μ ∧ r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} :=
    ⟨f, hfs, HasCompactSupport.of_compactSpace f, hpos, by rw [hint, hvar]⟩
  have hbdd : BddBelow {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧
      HasCompactSupport f ∧ 0 < variance f μ ∧
      r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} := by
    refine ⟨0, ?_⟩
    rintro r ⟨g, -, -, hg, rfl⟩
    exact div_nonneg (integral_nonneg fun x => by positivity) hg.le
  refine (csInf_le hbdd hmem).trans (le_of_eq ?_)
  field_simp
  ring

section conditional

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- Conditional two-sided bound: if moreover `CD(d-1, ∞)` holds for a constant potential `c` (the Ricci lower bound
`Ric ≥ (d-1) g` of the round sphere, NOT proved here), then `d - 1 ≤ λ₁ ≤ d`.
The lower bound is the project's `mSpectralGap_ge_of_CD`; `λ₁ = d` itself is not proved. -/
theorem sphere_gap_bounds_of_CD [CompactSpace M] {Φ : M → 𝔼} (c : ℝ) (hd : 2 ≤ d)
    (hF : Module.finrank ℝ F = d) (hΦ : IsIsometricSphereMap F Φ) {μ : Measure M}
    [IsProbabilityMeasure μ] (hμ : ∀ T : 𝔼 ≃ₗᵢ[ℝ] 𝔼, μ.map (fun x => T (Φ x)) = μ.map Φ)
    (hvol : IsWeightedVolume F μ (fun _ : M => c)) (hCD : CD F ((d : ℝ) - 1) (fun _ : M => c)) :
    (d : ℝ) - 1 ≤ mSpectralGap F μ ∧ mSpectralGap F μ ≤ d := by
  refine ⟨CutoffRigidity.Paper.mSpectralGap_ge_of_CD F (by omega) contMDiff_const hvol ?_ hCD,
    sphere_spectralGap_le F hF hΦ hμ⟩
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

end conditional

end gap

end CutoffRigidity.Extra
