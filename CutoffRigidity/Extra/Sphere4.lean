module

public import CutoffRigidity.Extra.Sphere3

/-! # Sphere, stage 4: `Ric = (d-1) g` and `CD(d-1, ∞)` for any isometrically immersed model of `S^d`

Statements are for the project's own `mRic` (built from Mathlib's Levi-Civita connection and Lie bracket)
and `CD`; `M` is any manifold (standing instances of `Challenge.lean`, without `IsRiemannianManifold`)
carrying `Φ : M → ℝ^{d+1}` with `|Φ| = 1`, smooth, with `⟪dΦ v, dΦ w⟫ = ⟪v, w⟫` (Item6a's
`IsIsometricSphereMap`) and `dim M = d`.
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

/-- Every tangent vector extends to a globally smooth vector field (a gradient of a coordinate function). -/
lemma exists_global_field {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ) (x : M)
    (u : TangentSpace 𝓘(ℝ, F) x) :
    ∃ G : (y : M) → TangentSpace 𝓘(ℝ, F) y, (∀ y, SmAt F G y) ∧ G x = u := by
  refine ⟨mgrad F (phi Φ (mvfderiv 𝓘(ℝ, F) Φ x u)), fun y => ?_, ?_⟩
  · exact CutCur.WReg.contMDiff_mgrad (contMDiff_phi hΦ _) y
  · apply ext_inner_right ℝ
    intro w
    have h1 : inner ℝ (mgrad F (phi Φ (mvfderiv 𝓘(ℝ, F) Φ x u)) x) w =
        mvfderiv 𝓘(ℝ, F) (phi Φ (mvfderiv 𝓘(ℝ, F) Φ x u)) x w := by
      rw [mgrad, InnerProductSpace.toDual_symm_apply]
    rw [h1, mvfderiv_phi hΦ, hΦ.2.2 x u w]

/-- **`Ric = (d-1) g`** on an isometrically immersed model of the unit sphere `S^d ⊂ ℝ^{d+1}`. -/
theorem sphere_mRic (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    (x : M) (v w : TangentSpace 𝓘(ℝ, F) x) :
    mRic F x v w = ((d : ℝ) - 1) * inner ℝ v w := by
  have hN : NabSmooth F M := nabSmooth
  set b := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) with hb
  obtain ⟨Gv, hGv, hGvx⟩ := exists_global_field hΦ x v
  obtain ⟨Gw, hGw, hGwx⟩ := exists_global_field hΦ x w
  have hterm : ∀ i, inner ℝ (mCurv F (mExt F x (b i)) (mExt F x v) (mExt F x w) x) (b i) =
      inner ℝ w v * inner ℝ (b i) (b i) - inner ℝ w (b i) * inner ℝ (b i) v := by
    intro i
    obtain ⟨Gi, hGi, hGix⟩ := exists_global_field hΦ x (b i)
    have h1 : mCurv F (mExt F x (b i)) (mExt F x v) (mExt F x w) x = curv F Gi Gv Gw x := by
      rw [CutoffRigidity.Paper.mCurv_eq_curv]
      exact CutoffRigidity.Paper.curv_tensor F hN (CutoffRigidity.Paper.mExt_smooth F x _) (hGi x)
        (CutoffRigidity.Paper.mExt_smooth F x _) (hGv x)
        (CutoffRigidity.Paper.mExt_smooth F x _) (hGw x)
        (by rw [CutoffRigidity.Paper.mExt_apply_self, hGix])
        (by rw [CutoffRigidity.Paper.mExt_apply_self, hGvx])
        (by rw [CutoffRigidity.Paper.mExt_apply_self, hGwx])
    rw [h1, ← hGix]
    have := curv_inner hF hΦ hGi hGv hGw (hGi x)
    rw [this, hGix, hGvx, hGwx]
  unfold mRic
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hn : ∑ i, inner ℝ (b i) (b i) = (d : ℝ) := by
    have : ∀ i, inner ℝ (b i) (b i) = (1 : ℝ) := fun i => by simp [hb]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hd : Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) = d := hF
    rw [hd]
  have hp : ∑ i, inner ℝ w (b i) * inner ℝ (b i) v = inner ℝ w v := b.sum_inner_mul_inner w v
  rw [hn, hp, real_inner_comm v w]
  ring


lemma mHess_const (c : ℝ) (x : M) (v w : TangentSpace 𝓘(ℝ, F) x) :
    mHess F (fun _ : M => c) x v w = 0 := by
  have e : mgrad F (fun _ : M => c) = 0 := funext (mgrad_const F c)
  unfold mHess
  rw [e, CovariantDerivative.zero]
  simp

/-- **`CD(d-1, ∞)` on the model of the unit sphere** (for any constant potential, i.e. the unweighted
Laplace-Beltrami operator): the Bakry-Emery condition of the project holds with `ρ = d - 1`. -/
theorem sphere_CD (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    (c : ℝ) : CD F ((d : ℝ) - 1) (fun _ : M => c) := by
  rw [CutoffRigidity.Paper.CD_iff_ricci F (contMDiff_const (c := c))]
  intro x v
  rw [mHess_const, sphere_mRic hF hΦ, real_inner_self_eq_norm_sq]
  simp

/-- `ρ = d - 1` is optimal: for `d ≥ 1`, `CD(ρ, ∞)` fails for every `ρ > d - 1` on the model of the sphere. -/
theorem sphere_not_CD (hF : Module.finrank ℝ F = d) (hd : 1 ≤ d) {Φ : M → 𝔼}
    (hΦ : IsIsometricSphereMap F Φ) (x : M) (c : ℝ) {ρ : ℝ} (hρ : (d : ℝ) - 1 < ρ) :
    ¬ CD F ρ (fun _ : M => c) := by
  intro h
  rw [CutoffRigidity.Paper.CD_iff_ricci F (contMDiff_const (c := c))] at h
  have hpos : 0 < Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) := by
    have : Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) = d := hF
    omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have := h x v
  rw [mHess_const, sphere_mRic hF hΦ, real_inner_self_eq_norm_sq] at this
  have hn : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith

end CutoffRigidity.Extra.Sphere
