module

public import CutoffRigidity.Extra.Sphere4

/-! # Sphere, stage 9: coordinate functions are eigenfunctions, `𝓛 φ_a = -d φ_a`

For an isometrically immersed model of `S^d` (`finrank F = d`), `d Φ (∇ φ_a) = a - φ_a Φ` (tangential part
of `a`), `Hess φ_a = -φ_a g`, hence `Δ φ_a = -d φ_a`.
-/

@[expose] public section

open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutCur.WBoch CutoffRigidity.Extra

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "bb" => stdOrthonormalBasis ℝ 𝔼

/-- `d Φ (∇ φ_a) = a - φ_a Φ`. -/
lemma mvfderiv_mgrad_phi (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    (a : 𝔼) (y : M) :
    mvfderiv 𝓘(ℝ, F) Φ y (mgrad F (phi Φ a) y) = a - phi Φ a y • Φ y := by
  set D := mvfderiv 𝓘(ℝ, F) Φ y with hD
  set c : ℝ := inner ℝ a (Φ y) with hc
  have hn1 : ‖Φ y‖ = 1 := hΦ.1 y
  have hw : a - c • Φ y ∈ (ℝ ∙ Φ y)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hn1, real_inner_comm]
    simp [hc]
  rw [← range_deriv_eq F hF hΦ y] at hw
  obtain ⟨v₀, hv₀⟩ := hw
  have hv₀' : D v₀ = a - c • Φ y := hv₀
  set u := mgrad F (phi Φ a) y with hu
  have hgrad : ∀ v : TangentSpace 𝓘(ℝ, F) y, inner ℝ u v = inner ℝ a (D v) := by
    intro v
    have h1 : inner ℝ u v = mvfderiv 𝓘(ℝ, F) (phi Φ a) y v := by
      rw [hu, mgrad, InnerProductSpace.toDual_symm_apply]
    rw [h1, mvfderiv_phi hΦ]
  have hv : ∀ v : TangentSpace 𝓘(ℝ, F) y, inner ℝ v₀ v = inner ℝ a (D v) := by
    intro v
    rw [hΦ.2.2 y v₀ v, hv₀', inner_sub_left, inner_smul_left, inner_Phi_deriv F hΦ y v]
    simp [hD]
  have huv : u = v₀ := by
    have : inner ℝ (u - v₀) (u - v₀) = 0 := by
      rw [inner_sub_left, hgrad, hv]; simp
    exact sub_eq_zero.mp (inner_self_eq_zero.mp this)
  rw [huv, hv₀']
  simp [phi, hc]


/-- **`Hess φ_a = -φ_a g`**. -/
lemma hess_phi (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ) (a : 𝔼)
    {X Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (hX : SmAt F X x) (hZ : SmAt F Z x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F (phi Φ a)) x (X x)) (Z x) =
      - phi Φ a x * inner ℝ (X x) (Z x) := by
  have hG : SmAt F (mgrad F (phi Φ a)) x := CutCur.WReg.contMDiff_mgrad (contMDiff_phi hΦ a) x
  rw [gauss_koszul hΦ hX hG hZ]
  have hfun : ∀ b : Fin (Module.finrank ℝ 𝔼),
      (fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb b)) y (mgrad F (phi Φ a) y)) =
        fun y => inner ℝ (bb b) a - phi Φ a y * phi Φ (bb b) y := by
    intro b; funext y
    rw [mvfderiv_phi hΦ, mvfderiv_mgrad_phi hF hΦ a y, inner_sub_right, inner_smul_right]
    simp [phi]
  have hpa : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (phi Φ a) x :=
    ((contMDiff_phi hΦ a) x).mdifferentiableAt (by simp)
  have hpb : ∀ b : Fin (Module.finrank ℝ 𝔼), MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (phi Φ (bb b)) x :=
    fun b => ((contMDiff_phi hΦ _) x).mdifferentiableAt (by simp)
  have hdd : ∀ b : Fin (Module.finrank ℝ 𝔼), dd F (phi Φ (bb b)) X (mgrad F (phi Φ a)) x =
      -(phi Φ a x * mvfderiv 𝓘(ℝ, F) (phi Φ (bb b)) x (X x) +
        phi Φ (bb b) x * mvfderiv 𝓘(ℝ, F) (phi Φ a) x (X x)) := by
    intro b
    simp only [dd]
    rw [hfun b, show (fun y => inner ℝ (bb b) a - phi Φ a y * phi Φ (bb b) y) =
      (fun _ => inner ℝ (bb b) a) - ((phi Φ a) * (phi Φ (bb b))) from rfl,
      mvfderiv_sub (mdifferentiableAt_const) (hpa.mul (hpb b)), mvfderiv_const,
      mvfderiv_mul hpa (hpb b)]
    simp
  simp only [hdd]
  have S0 := sum_coord_tangent hΦ x (Z x)
  have S1 := (inner_eq_sum hΦ x (Z x) (X x)).symm
  have : ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (Z x) *
      -(phi Φ a x * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (X x) +
        phi Φ (bb i) x * mvfderiv 𝓘(ℝ, F) (phi Φ a) x (X x)) =
      -(phi Φ a x) * ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (Z x) *
        mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (X x) -
      mvfderiv 𝓘(ℝ, F) (phi Φ a) x (X x) *
        ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (Z x) * phi Φ (bb i) x := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, S0, S1, real_inner_comm]
  ring


/-- **`Δ φ_a = -d φ_a`** on the model of `S^d`. -/
theorem mlaplacian_phi (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    (a : 𝔼) (x : M) : mlaplacian F (phi Φ a) x = -(d : ℝ) * phi Φ a x := by
  unfold mlaplacian
  have hterm : ∀ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
      (mgrad F (phi Φ a)) x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) = - phi Φ a x := by
    intro i
    set e := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i with he
    have h := hess_phi hF hΦ a (X := CutCur.mExt F x e) (Z := CutCur.mExt F x e)
      (CutoffRigidity.Paper.mExt_smooth F x e) (CutoffRigidity.Paper.mExt_smooth F x e)
    rw [CutoffRigidity.Paper.mExt_apply_self] at h
    rw [h]
    have : inner ℝ e e = (1 : ℝ) := by simp [he]
    rw [this]; ring
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) = d := hF
  rw [hd]
  ring

/-- `𝓛 φ_a = -d φ_a` for the generator of any constant potential. -/
theorem mgenerator_phi (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    (c : ℝ) (a : 𝔼) (x : M) :
    mgenerator F (fun _ : M => c) (phi Φ a) x = -(d : ℝ) * phi Φ a x := by
  unfold mgenerator
  rw [mlaplacian_phi hF hΦ, mgrad_const]
  simp

end CutoffRigidity.Extra.Sphere
