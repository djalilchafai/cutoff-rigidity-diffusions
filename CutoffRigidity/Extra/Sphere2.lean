module

public import CutoffRigidity.Extra.Sphere1

/-! # Sphere, stage 2: coordinates of `∇_Y W` -/

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


/-- Tangency: `∑ₐ d φₐ(W) φₐ = 0`. -/
lemma sum_coord_tangent {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ) (y : M) (v : TangentSpace 𝓘(ℝ, F) y) :
    ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y v * phi Φ (bb i) y = 0 := by
  have h := inner_Phi_deriv F hΦ y v
  have e : ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y v * phi Φ (bb i) y =
      inner ℝ (mvfderiv 𝓘(ℝ, F) Φ y v) (Φ y) := by
    rw [← OrthonormalBasis.sum_inner_mul_inner (stdOrthonormalBasis ℝ 𝔼) (mvfderiv 𝓘(ℝ, F) Φ y v) (Φ y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mvfderiv_phi hΦ, phi, real_inner_comm (bb i)]
  rw [e, real_inner_comm]
  exact h


lemma deriv_tangent {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    {Y W : (y : M) → TangentSpace 𝓘(ℝ, F) y} {y : M} (hY : SmAt F Y y) (hW : SmAt F W y) :
    ∑ i, (mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (W y) * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (Y y) +
      phi Φ (bb i) y * dd F (phi Φ (bb i)) Y W y) = 0 := by
  have hA : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ)
      (fun y' => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y' (W y')) y := fun i =>
    mdiffAt_mvfderiv_apply ((contMDiff_phi hΦ _) y) hW
  have hB : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (phi Φ (bb i)) y := fun i =>
    ((contMDiff_phi hΦ _) y).mdifferentiableAt (by simp)
  have hz : (fun y' => ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y' (W y') * phi Φ (bb i) y') =
      fun _ => (0 : ℝ) := by
    funext y'; exact sum_coord_tangent hΦ y' (W y')
  have h := congrArg (fun L => L (Y y)) (congrArg (fun f => mvfderiv 𝓘(ℝ, F) f y) hz)
  simp only [mvfderiv_const, zero_apply] at h
  rw [mvfderiv_sum (Finset.univ) (A := fun i y' =>
      mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y' (W y') * phi Φ (bb i) y')
      (fun i => (hA i).mul (hB i))] at h
  simp only [sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mvfderiv_fun_mul (hA i) (hB i)]
  simp [dd]


/-- Coordinates of `∇_Y W`: `(∇_Y W) φₐ = Y(W φₐ) + ⟪W, Y⟫ φₐ`. -/
lemma nab_coord (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    {Y W : (y : M) → TangentSpace 𝓘(ℝ, F) y} {y : M} (hY : SmAt F Y y) (hW : SmAt F W y)
    (j : Fin (Module.finrank ℝ 𝔼)) :
    mvfderiv 𝓘(ℝ, F) (phi Φ (bb j)) y
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M W y (Y y)) =
      dd F (phi Φ (bb j)) Y W y + inner ℝ (W y) (Y y) * phi Φ (bb j) y := by
  set n := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M W y (Y y) with hn
  set D := mvfderiv 𝓘(ℝ, F) Φ y with hD
  set c : Fin (Module.finrank ℝ 𝔼) → ℝ := fun i => dd F (phi Φ (bb i)) Y W y with hc
  set q : 𝔼 := ∑ i, c i • bb i with hq
  have hq_inner : ∀ a : 𝔼, inner ℝ a q = ∑ i, c i * inner ℝ a (bb i) := by
    intro a; simp [hq, inner_sum, inner_smul_right]
  have h1 : ∀ z : TangentSpace 𝓘(ℝ, F) y, inner ℝ (D n) (D z) = inner ℝ q (D z) := by
    intro z
    have g := gauss_koszul hΦ (X := Y) (Y := W) (Z := CutCur.mExt F y z) hY hW
      (CutoffRigidity.Paper.mExt_smooth F y z)
    rw [CutoffRigidity.Paper.mExt_apply_self] at g
    rw [← hΦ.2.2 y n z, g, real_inner_comm (D z) q, hq_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mvfderiv_phi hΦ, real_inner_comm (bb i)]
    simp only [hc]; ring
  have h2 : D n - q ∈ (ℝ ∙ Φ y) := by
    have hm : D n - q ∈ (LinearMap.range (D : TangentSpace 𝓘(ℝ, F) y →ₗ[ℝ] 𝔼))ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨z, rfl⟩
      rw [inner_sub_right]
      show inner ℝ (D z) (D n) - inner ℝ (D z) q = 0
      have e1 := real_inner_comm (D n) (D z)
      have e2 := real_inner_comm q (D z)
      have := h1 z
      linarith
    rw [range_deriv_eq F hF hΦ y] at hm
    rwa [Submodule.orthogonal_orthogonal] at hm
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h2
  have hort : inner ℝ (Φ y) (D n) = 0 := inner_Phi_deriv F hΦ y n
  have hDn : D n = q + t • Φ y := by rw [ht]; abel
  have hΦn : inner ℝ (Φ y) (Φ y) = 1 := by rw [real_inner_self_eq_norm_sq, hΦ.1 y]; norm_num
  have ht' : t = - ∑ i, c i * phi Φ (bb i) y := by
    rw [hDn, inner_add_right, inner_smul_right, hΦn, hq_inner] at hort
    have : ∑ i, c i * inner ℝ (Φ y) (bb i) = ∑ i, c i * phi Φ (bb i) y := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [phi, real_inner_comm]
    rw [this] at hort
    linarith
  have hdt := deriv_tangent hΦ hY hW
  have hgWY : inner ℝ (W y) (Y y) = ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (W y) *
      mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (Y y) := inner_eq_sum hΦ y _ _
  have hsum : ∑ i, c i * phi Φ (bb i) y = - inner ℝ (W y) (Y y) := by
    rw [hgWY]
    have := hdt
    rw [Finset.sum_add_distrib] at this
    have e : ∑ i, phi Φ (bb i) y * dd F (phi Φ (bb i)) Y W y = ∑ i, c i * phi Φ (bb i) y := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]; ring
    rw [e] at this
    linarith
  have hfin : mvfderiv 𝓘(ℝ, F) (phi Φ (bb j)) y n = inner ℝ (bb j) (D n) := mvfderiv_phi hΦ _ y n
  rw [hfin, hDn, inner_add_right, inner_smul_right, hq_inner, ht', hsum]
  have : ∑ i, c i * inner ℝ (bb j) (bb i) = c j := by
    simp [(bb).inner_eq_ite, Finset.sum_ite_eq]
  rw [this]
  simp only [hc, phi]
  ring

end CutoffRigidity.Extra.Sphere
