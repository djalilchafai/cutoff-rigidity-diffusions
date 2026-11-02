module

public import CutoffRigidity.Extra.Item6a
public import CutoffRigidity.Extra.RicciBochner

/-! # Sphere, stage 1: the Gauss formula for the Levi-Civita connection of an isometrically immersed model

For `M` with an isometric smooth map `Φ : M → E` (Item6a's `IsIsometricSphereMap`, which only uses
`⟪dΦ v, dΦ w⟫ = ⟪v, w⟫`), with `φ_a = ⟪a, Φ⟫` and `a` running over an orthonormal basis of `E`,
the Koszul formula gives `⟪∇_X Y, Z⟫ = ∑ₐ Z(φₐ) · X(Y φₐ)`.
-/

@[expose] public section

open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutCur.WBoch CutoffRigidity.Extra

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The coordinate function `φ_a = ⟪a, Φ⟫`. -/
def phi (Φ : M → E) (a : E) : M → ℝ := fun y => inner ℝ a (Φ y)

/-- `U (V f)` at `x`: the derivative along the vector `U x` of the function `y ↦ d f (V y)`. -/
noncomputable def dd (f : M → ℝ) (U V : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) : ℝ :=
  mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) f y (V y)) x (U x)

variable {F}

lemma contMDiff_phi {Φ : M → E} (hΦ : IsIsometricSphereMap F Φ) (a : E) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (phi Φ a) :=
  (contDiff_const.inner ℝ contDiff_id : ContDiff ℝ ∞ (fun z : E => inner ℝ a z)).comp_contMDiff hΦ.2.1

lemma mvfderiv_phi {Φ : M → E} (hΦ : IsIsometricSphereMap F Φ) (a : E) (x : M)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (phi Φ a) x v = inner ℝ a (mvfderiv 𝓘(ℝ, F) Φ x v) := by
  have := mvfderiv_comp_clm F Φ hΦ.2.1 (innerSL ℝ a) x v
  exact this

/-- Parseval for the pulled back metric. -/
lemma inner_eq_sum {Φ : M → E} (hΦ : IsIsometricSphereMap F Φ) (x : M)
    (v w : TangentSpace 𝓘(ℝ, F) x) :
    inner ℝ v w = ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ ((stdOrthonormalBasis ℝ E) i)) x v *
      mvfderiv 𝓘(ℝ, F) (phi Φ ((stdOrthonormalBasis ℝ E) i)) x w := by
  rw [hΦ.2.2 x v w]
  simp_rw [mvfderiv_phi hΦ]
  rw [← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm]

lemma mvfderiv_sum {ι : Type*} (s : Finset ι) {A : ι → M → ℝ} {x : M}
    (hA : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (A i) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => ∑ i ∈ s, A i y) x = ∑ i ∈ s, mvfderiv 𝓘(ℝ, F) (A i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mvfderiv_const (I := 𝓘(ℝ, F)) (0 : ℝ) (x := x)
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have h2 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, A i y) x := by
      have := MDifferentiableAt.sum (f := A) (t := s) (z := x) (fun i _ => hA i)
      convert this using 1
      ext y; simp
    rw [mvfderiv_fun_add (hA j) h2, ih]


section gauss

variable {Φ : M → E}

local notation "bb" => stdOrthonormalBasis ℝ E

/-- Derivative of the metric pairing of two fields, in terms of the coordinate functions. -/
lemma mvfderiv_inner_fields (hΦ : IsIsometricSphereMap F Φ)
    {U V : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (hU : SmAt F U x) (hV : SmAt F V x)
    (w : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (U y) (V y)) x w =
      ∑ i, (mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (U x) *
          mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (V y)) x w +
        mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) *
          mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (U y)) x w) := by
  have hfun : (fun y => inner ℝ (U y) (V y)) = fun y => ∑ i,
      mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (U y) * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (V y) := by
    funext y; exact inner_eq_sum hΦ y _ _
  have hdU : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ)
      (fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (U y)) x := fun i =>
    mdiffAt_mvfderiv_apply ((contMDiff_phi hΦ _) x) hU
  have hdV : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ)
      (fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (V y)) x := fun i =>
    mdiffAt_mvfderiv_apply ((contMDiff_phi hΦ _) x) hV
  rw [hfun, mvfderiv_sum (Finset.univ) (A := fun i y =>
      mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (U y) * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (V y))
      (fun i => (hdU i).mul (hdV i))]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := mvfderiv_fun_mul (hdU i) (hdV i)
  rw [this]
  simp

lemma inner_mlieBracket_fields (hΦ : IsIsometricSphereMap F Φ)
    {U V W : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (hV : SmAt F V x) (hW : SmAt F W x) :
    inner ℝ (U x) (mlieBracket 𝓘(ℝ, F) V W x) =
      ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (U x) *
        (dd F (phi Φ (bb i)) V W x - dd F (phi Φ (bb i)) W V x) := by
  rw [inner_eq_sum hΦ x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WBoch.mvfderiv_mlieBracket F ((contMDiff_phi hΦ _) x) hV hW]
  rfl

/-- **Gauss formula**: `⟪∇_X Y, Z⟫ = ∑ₐ Z(φₐ) · X(Y φₐ)`. -/
theorem gauss_koszul (hΦ : IsIsometricSphereMap F Φ)
    {X Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hY : SmAt F Y x) (hZ : SmAt F Z x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y x (X x)) (Z x) =
      ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (Z x) * dd F (phi Φ (bb i)) X Y x := by
  rw [CovariantDerivative.leviCivitaConnection_apply_inner 𝓘(ℝ, F) hX.mdiffAt hY.mdiffAt hZ.mdiffAt]
  simp only []
  rw [mvfderiv_inner_fields hΦ hY hZ, mvfderiv_inner_fields hΦ hZ hX, mvfderiv_inner_fields hΦ hX hY,
    inner_mlieBracket_fields hΦ hX hZ, inner_mlieBracket_fields hΦ hY hX,
    inner_mlieBracket_fields hΦ hZ hY]
  simp only [dd]
  rw [div_eq_iff two_ne_zero, Finset.sum_mul]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end gauss

end CutoffRigidity.Extra.Sphere
