module

public import CutoffRigidity.Riemann.WitnessGauss
public import CutoffRigidity.Paper.CoreBridge
public import CutoffRigidity.GibbsStationarity
public import CutoffRigidity.CompactBochnerCoercivity

/-! # Temperature (manuscript, Section 4.4)

Bakry-Emery operators of `L_σ = σ²Δ - ∇V·∇` and equivalence of `CD(ρ,∞)` with `Hess V ≥ ρ`.
-/

public section


namespace CutoffRigidity.Paper

open MeasureTheory Set Bundle
open scoped ContDiff ENNReal NNReal Manifold

variable {d : ℕ}

theorem gradient_const_mul' {h : CutCur.Rd d → ℝ} (hh : Differentiable ℝ h) (c : ℝ)
    (x : CutCur.Rd d) : gradient (fun y => c * h y) x = c • gradient h x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left,
    fderiv_const_mul (hh x)]
  simp

theorem laplacian_const_mul {h : CutCur.Rd d → ℝ} (hh : ContDiff ℝ 2 h) (c : ℝ)
    (x : CutCur.Rd d) : CutCur.laplacian (fun y => c * h y) x = c * CutCur.laplacian h x := by
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : fderiv ℝ (fun y => c * h y) = c • fderiv ℝ h := by
    funext y
    rw [fderiv_const_mul (hd y)]
    rfl
  unfold CutCur.laplacian
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_const_smul (hd2 x)]
  simp

theorem gradient_div_const {V : CutCur.Rd d → ℝ} (hV : Differentiable ℝ V) (s : ℝ)
    (x : CutCur.Rd d) : gradient (fun y => V y / s) x = s⁻¹ • gradient V x := by
  have : (fun y => V y / s) = fun y => s⁻¹ * V y := funext fun y => by rw [div_eq_inv_mul]
  rw [this, gradient_const_mul' hV]

theorem hessian_div_const {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V) (s : ℝ)
    (x z : CutCur.Rd d) :
    fderiv ℝ (fderiv ℝ (fun y => V y / s)) x z z = s⁻¹ * fderiv ℝ (fderiv ℝ V) x z z := by
  have hd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : fderiv ℝ (fun y => V y / s) = s⁻¹ • fderiv ℝ V := by
    funext y
    have : (fun y => V y / s) = fun y => s⁻¹ * V y := funext fun y => by rw [div_eq_inv_mul]
    rw [this, fderiv_const_mul (hd y)]
    rfl
  rw [h1, fderiv_const_smul (hd2 x)]
  simp

/-- The Hessian in the coordinate basis, as the second derivative of the coordinate derivatives. -/
theorem coordinateDerivative_coordinateDerivative {f : CutCur.Rd d → ℝ} (hf : ContDiff ℝ 2 f)
    (i j : Fin d) (x : CutCur.Rd d) :
    coordinateDerivative j (coordinateDerivative i f) x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  unfold coordinateDerivative
  rw [fderiv_clm_apply hdf (differentiableAt_const _)]
  simp

theorem gradient_inner_left (z x : CutCur.Rd d) : gradient (fun y : CutCur.Rd d => inner ℝ z y) x = z := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left]
  have : HasFDerivAt (fun y : CutCur.Rd d => inner ℝ z y) (innerSL ℝ z) x := (innerSL ℝ z).hasFDerivAt
  rw [this.fderiv]
  simp

theorem fderiv_fderiv_inner_left (z x : CutCur.Rd d) :
    fderiv ℝ (fderiv ℝ (fun y : CutCur.Rd d => inner ℝ z y)) x = 0 := by
  have : fderiv ℝ (fun y : CutCur.Rd d => inner ℝ z y) = fun _ => innerSL ℝ z := by
    funext y
    exact (innerSL ℝ z).hasFDerivAt.fderiv
  rw [this]
  simp

/-- `CD(ρ,∞)` on flat space (in the Riemannian formulation of the project) is `Hess V ≥ ρ`. -/
theorem cd_euclid_iff {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ ∞ V) (ρ : ℝ) :
    CutCur.CD (CutCur.Rd d) ρ V ↔ ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
  constructor
  · intro h x z
    have hf : ContDiff ℝ ∞ (fun y : CutCur.Rd d => inner ℝ z y) := (innerSL ℝ z).contDiff
    have := h (fun y => inner ℝ z y) (contMDiff_iff_contDiff.2 hf) x
    rw [CutoffRigidity.Riemann.Witness.carre2_rd hf,
      CutoffRigidity.Riemann.Witness.gamma2_euclid hV hf,
      CutoffRigidity.Riemann.Witness.carre_rd, gradient_inner_left,
      real_inner_self_eq_norm_sq] at this
    have h0 : ∑ i : Fin d, ∑ j : Fin d, coordinateDerivative j
        (coordinateDerivative i (fun y : CutCur.Rd d => inner ℝ z y)) x ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [coordinateDerivative_coordinateDerivative (hf.of_le (by norm_cast)), fderiv_fderiv_inner_left]
      simp
    rw [h0] at this
    linarith
  · intro h f hf x
    have hf' : ContDiff ℝ ∞ f := contMDiff_iff_contDiff.1 hf
    rw [CutoffRigidity.Riemann.Witness.carre2_rd hf', CutoffRigidity.Riemann.Witness.gamma2_euclid hV hf',
      CutoffRigidity.Riemann.Witness.carre_rd, real_inner_self_eq_norm_sq]
    have : 0 ≤ ∑ i, ∑ j, coordinateDerivative j (coordinateDerivative i f) x ^ 2 := by positivity
    linarith [h x (gradient f x)]

/-- **Temperature** (manuscript, Section "Temperature"). For `σ > 0` and smooth `V`, with the
generator `L_σ f = σ²Δf - ∇V·∇f`, `Γ(f,g) = σ²⟨∇f,∇g⟩` and `Γ₂(f) = ½ L_σ Γ(f,f) - Γ(f, L_σ f)`:
(i) `Γ(f) = σ²|∇f|²` and `Γ₂(f) = σ⁴ ‖Hess f‖²_HS + σ² Hess V(∇f,∇f)` for smooth `f`;
(ii) the Gibbs measure `e^{-V/σ²}dx` (normalized by `Z_σ`) is invariant for `L_σ`, in the sense
`∫ L_σ f e^{-V/σ²} dx = 0` for every `C²` compactly supported `f`;
(iii) for every `ρ`, `CD(ρ,∞)` of `L_σ` (`ρΓ(f) ≤ Γ₂(f)` for smooth `f`) is equivalent to
`Hess V ≥ ρ I_d` as a quadratic form, a condition free of `σ`. -/
theorem temperature_bakry_emery {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ ∞ V) {σ : ℝ} (hσ : 0 < σ) :
    let L := fun (f : CutCur.Rd d → ℝ) (x : CutCur.Rd d) =>
      σ ^ 2 * CutCur.laplacian f x - inner ℝ (gradient V x) (gradient f x)
    let Γ := fun (f g : CutCur.Rd d → ℝ) (x : CutCur.Rd d) =>
      σ ^ 2 * inner ℝ (gradient f x) (gradient g x)
    let Γ₂ := fun (f : CutCur.Rd d → ℝ) (x : CutCur.Rd d) =>
      L (fun y => Γ f f y) x / 2 - Γ f (L f) x
    (∀ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f → ∀ x,
      Γ f f x = σ ^ 2 * ‖gradient f x‖ ^ 2 ∧
      Γ₂ f x = σ ^ 4 * ∑ i, ∑ j, (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) ^ 2 +
        σ ^ 2 * fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x)) ∧
    (∀ f : CutCur.Rd d → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∫ x, L f x ∂CutCur.gibbs (fun y => V y / σ ^ 2) = 0) ∧
    ∀ ρ : ℝ, (∀ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f → ∀ x, ρ * Γ f f x ≤ Γ₂ f x) ↔
      ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
  intro L Γ Γ₂
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have hV2 : ContDiff ℝ 2 V := hV.of_le (by norm_cast)
  have hVd : Differentiable ℝ V := hV2.differentiable (by norm_num)
  set W : CutCur.Rd d → ℝ := fun y => V y / σ ^ 2 with hW
  have hWs : ContDiff ℝ ∞ W := hV.div_const _
  have hW2 : ContDiff ℝ 2 W := hWs.of_le (by norm_cast)
  have hgW : ∀ x, gradient W x = (σ ^ 2)⁻¹ • gradient V x := gradient_div_const hVd _
  have hL : ∀ g x, L g x = σ ^ 2 * CutCur.generator W g x := by
    intro g x
    simp only [L, CutCur.generator, hgW, inner_smul_left, RCLike.conj_to_real]
    field_simp
  have hΓ : ∀ f g x, Γ f g x = σ ^ 2 * inner ℝ (gradient f x) (gradient g x) := fun _ _ _ => rfl
  have hmain : ∀ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f → ∀ x, Γ₂ f x =
      σ ^ 4 * ∑ i, ∑ j, (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) ^ 2 +
        σ ^ 2 * fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) := by
    intro f hf x
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast)
    have hf3 : ContDiff ℝ 3 f := hf.of_le (by norm_cast)
    have hg : ContDiff ℝ ∞ (gradient f) := CutoffRigidity.Riemann.Witness.contDiff_gradient_rd hf (by simp)
    have hh : ContDiff ℝ ∞ (fun y => ‖gradient f y‖ ^ 2) := hg.norm_sq ℝ
    have hh2 : ContDiff ℝ 2 (fun y => ‖gradient f y‖ ^ 2) := hh.of_le (by norm_cast)
    have hgen : CutCur.generator W f = langevinDifferentialOperator W f :=
      generator_eq_langevinDifferentialOperator W hf2
    have hgen' : CutCur.generator W (fun y => ‖gradient f y‖ ^ 2) =
        langevinDifferentialOperator W (fun y => ‖gradient f y‖ ^ 2) :=
      generator_eq_langevinDifferentialOperator W hh2
    have hkd : Differentiable ℝ (langevinDifferentialOperator W f) :=
      (contDiff_one_langevinDifferentialOperator hW2 hf3).differentiable (by norm_num)
    have e1 : (fun y => Γ f f y) = fun y => σ ^ 2 * ‖gradient f y‖ ^ 2 := by
      funext y; rw [hΓ, real_inner_self_eq_norm_sq]
    have e2 : L f = fun y => σ ^ 2 * langevinDifferentialOperator W f y := by
      funext y; rw [hL, hgen]
    have e3 : L (fun y => σ ^ 2 * ‖gradient f y‖ ^ 2) x =
        σ ^ 2 * (σ ^ 2 * langevinDifferentialOperator W (fun y => ‖gradient f y‖ ^ 2) x) := by
      rw [hL, ← hgen']
      have hlap := laplacian_const_mul hh2 (σ ^ 2) x
      have hgr := gradient_const_mul' (hh.differentiable (by simp)) (σ ^ 2) x
      simp only [CutCur.generator]
      rw [hlap, hgr, inner_smul_right]
      ring
    have e4 : Γ₂ f x = σ ^ 4 * (langevinDifferentialOperator W (fun y => ‖gradient f y‖ ^ 2) x / 2 -
        inner ℝ (gradient f x) (gradient (langevinDifferentialOperator W f) x)) := by
      change L (fun y => Γ f f y) x / 2 - Γ f (L f) x = _
      rw [e1, e3, hΓ, e2, gradient_const_mul' hkd, inner_smul_right]
      ring
    rw [e4, CutoffRigidity.Riemann.Witness.gamma2_euclid hWs hf, hessian_div_const hV2 (σ ^ 2)]
    have hs : ∑ i : Fin d, ∑ j : Fin d, coordinateDerivative j (coordinateDerivative i f) x ^ 2 =
        ∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [coordinateDerivative_coordinateDerivative hf2]
    rw [hs]
    have : σ ^ 4 = σ ^ 2 * σ ^ 2 := by ring
    field_simp
  refine ⟨fun f hf x => ⟨by rw [hΓ, real_inner_self_eq_norm_sq], hmain f hf x⟩, ?_, fun ρ => ?_⟩
  · intro f hf hfc
    have : ∀ x, L f x = σ ^ 2 * langevinDifferentialOperator W f x := fun x => by
      rw [hL, generator_eq_langevinDifferentialOperator W hf]
    simp_rw [this]
    rw [integral_const_mul]
    have h0 := integral_langevinDifferentialOperator_compact_eq_zero hW2 hf hfc
    change σ ^ 2 * ∫ x, langevinDifferentialOperator W f x ∂gibbsMeasure volume W = 0
    rw [h0, mul_zero]
  · constructor
    · intro h x z
      have hf : ContDiff ℝ ∞ (fun y : CutCur.Rd d => inner ℝ z y) := (innerSL ℝ z).contDiff
      have := h _ hf x
      rw [hΓ, hmain _ hf x, gradient_inner_left] at this
      have h0 : ∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fderiv ℝ (fun y : CutCur.Rd d => inner ℝ z y)) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2 = 0 := by
        simp [fderiv_fderiv_inner_left]
      rw [h0] at this
      rw [mul_zero, zero_add, real_inner_self_eq_norm_sq] at this
      have h1 : σ ^ 2 * (ρ * ‖z‖ ^ 2) ≤ σ ^ 2 * fderiv ℝ (fderiv ℝ V) x z z := by
        calc σ ^ 2 * (ρ * ‖z‖ ^ 2) = ρ * (σ ^ 2 * ‖z‖ ^ 2) := by ring
          _ ≤ _ := this
      exact le_of_mul_le_mul_left h1 (by positivity)
    · intro h f hf x
      rw [hΓ, hmain f hf x, real_inner_self_eq_norm_sq]
      have h1 := h x (gradient f x)
      have h2 : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) ^ 2 := by positivity
      have h3 : 0 ≤ σ ^ 4 * ∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg σ)]

/-- The manuscript's remark "using `α = σ²` and `V/σ²` instead of `V`": `L_σ = σ² 𝓛_{V/σ²}`, so
`CD(ρ,∞)` of `L_σ` is `CD(ρ/σ², ∞)` of the unit-temperature generator of the potential `V/σ²`
(in the project's Riemannian formulation on flat space), again equivalent to `Hess V ≥ ρ`.
The smoothness of the standard metric of `ℝ^d` is an instance argument (a proposition). -/
theorem temperature_cd
    [IsContMDiffRiemannianBundle 𝓘(ℝ, CutCur.Rd d) ∞ (CutCur.Rd d)
      (fun x : CutCur.Rd d => TangentSpace 𝓘(ℝ, CutCur.Rd d) x)]
    {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ ∞ V) {σ : ℝ} (hσ : 0 < σ) (ρ : ℝ) :
    CutCur.CD (CutCur.Rd d) (ρ / σ ^ 2) (fun x => V x / σ ^ 2) ↔
      ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
  have hV2 : ContDiff ℝ 2 V := hV.of_le (by norm_cast)
  rw [cd_euclid_iff (hV.div_const _)]
  simp_rw [hessian_div_const hV2]
  have hp : 0 < σ ^ 2 := by positivity
  refine forall_congr' fun x => forall_congr' fun z => ?_
  rw [div_mul_eq_mul_div, ← div_eq_inv_mul, div_le_div_iff_of_pos_right hp]

end CutoffRigidity.Paper
