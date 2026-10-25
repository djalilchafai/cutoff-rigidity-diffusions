module

public import CutoffRigidity.Riemann.DiffDynkinBounded
public import CutoffRigidity.EuclideanBochner

/-! # Witness: the Riemannian hypotheses are satisfiable on the flat space `ℝ^k` (part 1: geometry)

On `Rd k = EuclideanSpace ℝ (Fin k)` with Mathlib's standard Riemannian structure we show that the
manifold-side objects of `Challenge.lean` (`mgrad`, `mlaplacian`, `mgenerator`, `carre`, `carre2`,
`chartVolumeDensity`, `IsWeightedVolume`) agree with their Euclidean counterparts.
-/

@[expose] public section

open Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Witness

open CutCur CutoffRigidity

/-- Smooth Riemannian metric on `ℝ^k` in the form required by the Challenge (all smoothness
orders), from Mathlib's `riemannianMetricVectorSpace`. -/
instance instIsContMDiffRiemannianBundleRd (k : ℕ) (n : ℕ∞ω) :
    IsContMDiffRiemannianBundle 𝓘(ℝ, Rd k) n (Rd k) (fun x : Rd k => TangentSpace 𝓘(ℝ, Rd k) x) :=
  ⟨(riemannianMetricVectorSpace (Rd k)).inner,
    (riemannianMetricVectorSpace (Rd k)).contMDiff.of_le le_top, fun _ _ _ => rfl⟩

theorem mvfderiv_rd {k : ℕ} (f : Rd k → ℝ) (x : Rd k) : mvfderiv 𝓘(ℝ, Rd k) f x = fderiv ℝ f x := mvfderiv_eq_fderiv

theorem mgrad_rd {k : ℕ} (f : Rd k → ℝ) (x : Rd k) : mgrad (Rd k) f x = gradient f x := by
  unfold mgrad gradient
  rw [mvfderiv_rd]
  rfl

theorem chartAt_rd {k : ℕ} (x : Rd k) : chartAt (Rd k) x = OpenPartialHomeomorph.refl _ := by simp

theorem chartVolumeDensity_rd {k : ℕ} (x₀ : Rd k) (z : Rd k) : chartVolumeDensity (Rd k) x₀ z = 1 := by
  unfold chartVolumeDensity
  have h : ∀ i j : Fin (Module.finrank ℝ (Rd k)), inner ℝ (mfderiv 𝓘(ℝ, Rd k) 𝓘(ℝ, Rd k) (chartAt (Rd k) x₀).symm z (stdOrthonormalBasis ℝ (Rd k) i) :
      TangentSpace 𝓘(ℝ, Rd k) ((chartAt (Rd k) x₀).symm z))
      (mfderiv 𝓘(ℝ, Rd k) 𝓘(ℝ, Rd k) (chartAt (Rd k) x₀).symm z (stdOrthonormalBasis ℝ (Rd k) j)) = if i = j then 1 else 0 := by
    intro i j
    rw [chartAt_rd]
    have hr : ((OpenPartialHomeomorph.refl (Rd k) : OpenPartialHomeomorph _ _) : Rd k → Rd k) = id := rfl
    simp only [OpenPartialHomeomorph.refl_symm]
    rw [hr, mfderiv_id]
    exact (stdOrthonormalBasis ℝ (Rd k)).inner_eq_ite i j
  simp only [h]
  rw [show (Matrix.of fun i j : Fin (Module.finrank ℝ (Rd k)) => if i = j then (1:ℝ) else 0) = 1 from rfl]
  simp

theorem isWeightedVolume_gibbs {k : ℕ} (V : Rd k → ℝ) : IsWeightedVolume (Rd k) (gibbs V) V := by
  intro x₀
  rw [chartAt_rd]
  simp only [chartVolumeDensity_rd, mul_one]
  have : (OpenPartialHomeomorph.refl (Rd k)).source = Set.univ := rfl
  have h2 : (OpenPartialHomeomorph.refl (Rd k)).target = Set.univ := rfl
  rw [this, h2, Measure.restrict_univ, Measure.restrict_univ]
  have hr : ((OpenPartialHomeomorph.refl (Rd k) : OpenPartialHomeomorph _ _) : Rd k → Rd k) = id := rfl
  rw [hr, Measure.map_id]
  rfl

theorem mlieBracket_rd {k : ℕ} (V W : Π y : Rd k, TangentSpace 𝓘(ℝ, Rd k) y) :
    VectorField.mlieBracket 𝓘(ℝ, Rd k) V W = VectorField.lieBracket ℝ V W := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin]
  simp [VectorField.lieBracketWithin_univ]

theorem mdiffAt_rd {k : ℕ} {V : Π y : EuclideanSpace ℝ (Fin k), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) y}
    {x : EuclideanSpace ℝ (Fin k)}
    (h : ContDiffAt ℝ 1 V x) : MDiffAt (T% V) x :=
  ((contMDiffAt_vectorSpace_iff_contDiffAt (𝕜 := ℝ) (E := Rd k) (V := V) (x := x) (n := 1)).2 h).mdifferentiableAt one_ne_zero

theorem inner_cov_rd {k : ℕ} {Y : Π y : Rd k, TangentSpace 𝓘(ℝ, Rd k) y} {x : Rd k}
    (hY : ContDiffAt ℝ 1 Y x) (e : Rd k) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Rd k) (Rd k) Y x e)
      (e : TangentSpace 𝓘(ℝ, Rd k) x) =
      inner ℝ (fderiv ℝ (Y : Rd k → Rd k) x e) e := by
  have hc := mdiffAt_rd (k := k) (V := fun _ => e) (x := x) contDiffAt_const
  have h := CovariantDerivative.leviCivitaConnection_apply_inner (I := 𝓘(ℝ, Rd k)) (M := Rd k) (x := x) hc (mdiffAt_rd hY) hc
  have hYd : DifferentiableAt ℝ (Y : Rd k → Rd k) x := hY.differentiableAt one_ne_zero
  simp only [mvfderiv_rd, mlieBracket_rd, VectorField.lieBracket_eq] at h
  have h1 := fderiv_inner_apply (𝕜 := ℝ) (f := fun x => (Y x : Rd k)) (g := fun _ => e) (x := x) hYd (differentiableAt_const e) e
  have h2 := fderiv_inner_apply (𝕜 := ℝ) (f := fun _ => e) (g := fun x => (Y x : Rd k)) (x := x) (differentiableAt_const e) hYd e
  have h3 := fderiv_inner_apply (𝕜 := ℝ) (f := fun _ => e) (g := fun _ => e) (x := x) (differentiableAt_const e) (differentiableAt_const e) (Y x)
  refine h.trans ?_
  erw [h1, h2, h3]
  simp
  have hc2 : inner ℝ e ((fderiv ℝ (Y : Rd k → Rd k) x) e) = inner ℝ ((fderiv ℝ (Y : Rd k → Rd k) x) e) e := real_inner_comm _ _
  rw [hc2]
  ring

theorem contDiff_gradient_rd {k : ℕ} {n m : WithTop ℕ∞} {f : Rd k → ℝ} (hf : ContDiff ℝ m f)
    (hnm : n + 1 ≤ m) : ContDiff ℝ n (gradient f) := by
  have h1 : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right hnm
  exact (InnerProductSpace.toDual ℝ (Rd k)).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp h1


theorem mlaplacian_rd {k : ℕ} {f : Rd k → ℝ} (hf : ContDiff ℝ 2 f) (x : Rd k) :
    mlaplacian (Rd k) f x = laplacian f x := by
  have hg : ContDiff ℝ 1 (gradient f) := contDiff_gradient_rd hf (by norm_num)
  have hmg : (mgrad (Rd k) f : Π y : Rd k, TangentSpace 𝓘(ℝ, Rd k) y) = gradient f :=
    funext fun y => mgrad_rd f y
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  unfold mlaplacian laplacian
  rw [hmg]
  simp_rw [inner_cov_rd (hg.contDiffAt)]
  set L : Rd k →L[ℝ] Rd k := fderiv ℝ (gradient f) x with hL
  have hB : ∀ z : Rd k, fderiv ℝ (fderiv ℝ f) x z z = inner ℝ (L z) z := fun z =>
    (inner_fderiv_gradient_apply hd).symm
  let LT : TangentSpace 𝓘(ℝ, Rd k) x →L[ℝ] TangentSpace 𝓘(ℝ, Rd k) x := L
  have h1 := LinearMap.trace_eq_sum_inner
    (LT : TangentSpace 𝓘(ℝ, Rd k) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rd k) x)
    (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, Rd k) x))
  have hTr : (LT : TangentSpace 𝓘(ℝ, Rd k) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rd k) x).trace ℝ
      (TangentSpace 𝓘(ℝ, Rd k) x) = (L : Rd k →ₗ[ℝ] Rd k).trace ℝ (Rd k) := rfl
  have h2 := LinearMap.trace_eq_sum_inner (L : Rd k →ₗ[ℝ] Rd k) (EuclideanSpace.basisFun (Fin k) ℝ)
  have e1 : ∑ i, inner ℝ (L ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, Rd k) x)) i))
      ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, Rd k) x)) i) =
      (L : Rd k →ₗ[ℝ] Rd k).trace ℝ (Rd k) := by
    rw [← hTr, h1]
    exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  have e2 : ∑ i, ((fderiv ℝ (fderiv ℝ f) x) (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1) =
      (L : Rd k →ₗ[ℝ] Rd k).trace ℝ (Rd k) := by
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB, real_inner_comm]
    simp
  exact e1.trans e2.symm

end CutoffRigidity.Riemann.Witness
