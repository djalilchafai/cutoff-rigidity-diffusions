module

public import CutoffRigidity.Extra.Sphere2

/-! # Sphere, stage 3: the curvature of an isometrically immersed model of the unit sphere

`⟪R(X,Y)W, V⟫ = ⟪Y,W⟫⟪X,V⟫ - ⟪X,W⟫⟪Y,V⟫`, hence `Ric = (d-1) g`, for the project's `mCurv`/`mRic`.
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

/-- `y ↦ d f (W y)` is smooth for smooth `f` and smooth `W`. -/
lemma contMDiff_dfun {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f)
    {W : (y : M) → TangentSpace 𝓘(ℝ, F) y} (hW : ∀ y, SmAt F W y) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y => mvfderiv 𝓘(ℝ, F) f y (W y)) := by
  have hT : ContMDiff 𝓘(ℝ, F).tangent 𝓘(ℝ, ℝ).tangent ∞
      (tangentMap 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f) := hf.contMDiff_tangentMap (by simp)
  have hY : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% W) := fun y => hW y
  have hc := (contMDiff_snd_tangentBundle_modelSpace (n := ∞) ℝ 𝓘(ℝ, ℝ)).comp (hT.comp hY)
  refine hc.congr ?_
  intro y
  simp only [Function.comp, tangentMap]
  rfl


lemma mdiff_inner_fields {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    {U V : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (hU : SmAt F U x) (hV : SmAt F V x) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => inner ℝ (U y) (V y)) x := by
  have hfun : (fun y => inner ℝ (U y) (V y)) = fun y => ∑ i,
      mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (U y) * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (V y) := by
    funext y; exact inner_eq_sum hΦ y _ _
  have hdU : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ)
      (fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (U y)) x := fun i =>
    mdiffAt_mvfderiv_apply ((contMDiff_phi hΦ _) x) hU
  have hdV : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ)
      (fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (V y)) x := fun i =>
    mdiffAt_mvfderiv_apply ((contMDiff_phi hΦ _) x) hV
  rw [hfun]
  have := MDifferentiableAt.sum (t := Finset.univ) (z := x)
    (f := fun i y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (U y) *
      mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (V y)) (fun i _ => (hdU i).mul (hdV i))
  convert this using 1
  ext y; simp

variable (F) in
/-- Third derivative `U (Y (W f))` at `x`. -/
noncomputable def ddd (f : M → ℝ) (U Y W : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) : ℝ :=
  mvfderiv 𝓘(ℝ, F) (fun y => dd F f Y W y) x (U x)

/-- The metric pairing against `∇_U (∇_Y W)`. -/
lemma inner_nab_term (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    {U Y W V : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (hU : SmAt F U x)
    (hY : ∀ y, SmAt F Y y) (hW : ∀ y, SmAt F W y) (hV : SmAt F V x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F Y W) x (U x)) (V x) =
      ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) *
        (ddd F (phi Φ (bb i)) U Y W x +
          (inner ℝ (W x) (Y x) * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (U x) +
            phi Φ (bb i) x * mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (W y) (Y y)) x (U x))) := by
  have hN : NabSmooth F M := nabSmooth
  rw [gauss_koszul hΦ hU (hN Y W x (hY x) (hW x)) hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hfun : (fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (nab F Y W y)) =
      fun y => dd F (phi Φ (bb i)) Y W y + inner ℝ (W y) (Y y) * phi Φ (bb i) y := by
    funext y
    exact nab_coord hF hΦ (hY y) (hW y) i
  have hd1 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => dd F (phi Φ (bb i)) Y W y) x :=
    mdiffAt_mvfderiv_apply (((contMDiff_dfun (contMDiff_phi hΦ _) hW) x)) (hY x)
  have hs : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => inner ℝ (W y) (Y y)) x :=
    mdiff_inner_fields hΦ (hW x) (hY x)
  have hp : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (phi Φ (bb i)) x :=
    ((contMDiff_phi hΦ _) x).mdifferentiableAt (by simp)
  simp only [dd]
  rw [hfun, show (fun y => dd F (phi Φ (bb i)) Y W y + inner ℝ (W y) (Y y) * phi Φ (bb i) y) =
      (fun y => dd F (phi Φ (bb i)) Y W y) + ((fun y => inner ℝ (W y) (Y y)) * phi Φ (bb i)) from rfl,
    mvfderiv_add hd1 (hs.mul hp), mvfderiv_mul hs hp]
  simp [ddd, dd]


/-- The metric pairing against `∇_{[X,Y]} W`. -/
lemma inner_lie_term {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    {X Y W V : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : ∀ y, SmAt F X y) (hY : ∀ y, SmAt F Y y) (hW : ∀ y, SmAt F W y) (hV : SmAt F V x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M W x
        (mlieBracket 𝓘(ℝ, F) X Y x)) (V x) =
      ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) *
        (ddd F (phi Φ (bb i)) X Y W x - ddd F (phi Φ (bb i)) Y X W x) := by
  set t := mlieBracket 𝓘(ℝ, F) X Y x with ht
  have g := gauss_koszul hΦ (X := CutCur.mExt F x t) (Y := W) (Z := V)
    (CutoffRigidity.Paper.mExt_smooth F x t) (hW x) hV
  rw [CutoffRigidity.Paper.mExt_apply_self] at g
  rw [g]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h := WBoch.mvfderiv_mlieBracket F (φ := fun y => mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) y (W y))
    (X := X) (Y := Y) (x := x) ((contMDiff_dfun (contMDiff_phi hΦ _) hW) x) (hX x) (hY x)
  simp only [dd, CutoffRigidity.Paper.mExt_apply_self]
  rw [h]
  rfl

/-- **Curvature of the model of the unit sphere**: `⟪R(X,Y)W, V⟫ = ⟪Y,W⟫⟪X,V⟫ - ⟪X,W⟫⟪Y,V⟫`. -/
theorem curv_inner (hF : Module.finrank ℝ F = d) {Φ : M → 𝔼} (hΦ : IsIsometricSphereMap F Φ)
    {X Y W V : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : ∀ y, SmAt F X y) (hY : ∀ y, SmAt F Y y) (hW : ∀ y, SmAt F W y) (hV : SmAt F V x) :
    inner ℝ (curv F X Y W x) (V x) =
      inner ℝ (W x) (Y x) * inner ℝ (V x) (X x) - inner ℝ (W x) (X x) * inner ℝ (V x) (Y x) := by
  unfold curv
  rw [inner_sub_left, inner_sub_left, inner_nab_term hF hΦ (hX x) hY hW hV,
    inner_nab_term hF hΦ (hY x) hX hW hV, inner_lie_term hΦ hX hY hW hV]
  have S0 := sum_coord_tangent hΦ x (V x)
  have S1 := (inner_eq_sum hΦ x (V x) (X x)).symm
  have S2 := (inner_eq_sum hΦ x (V x) (Y x)).symm
  set p := mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (W y) (Y y)) x (X x)
  set r := mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (W y) (X y)) x (Y x)
  have key : ∀ (s1 s2 : ℝ), (∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) *
        (ddd F (phi Φ (bb i)) X Y W x +
          (s1 * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (X x) + phi Φ (bb i) x * p))) -
      (∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) *
        (ddd F (phi Φ (bb i)) Y X W x +
          (s2 * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (Y x) + phi Φ (bb i) x * r))) -
      (∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) *
        (ddd F (phi Φ (bb i)) X Y W x - ddd F (phi Φ (bb i)) Y X W x)) =
      s1 * ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (X x)
      - s2 * ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) * mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (Y x)
      + (p - r) * ∑ i, mvfderiv 𝓘(ℝ, F) (phi Φ (bb i)) x (V x) * phi Φ (bb i) x := by
    intro s1 s2
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key, S1, S2, S0]
  ring

end CutoffRigidity.Extra.Sphere
