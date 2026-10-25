module

public import CutoffRigidity.Riemann.WitnessGeometry
public import CutoffRigidity.Paper.CoreBridge

/-! # Witness (part 2): the Bochner identity on flat `ℝ^k`

Pointwise Euclidean identity `Γ₂(f) = ‖D²f‖² + D²V(∇f,∇f)` for smooth `f` and `V`, by a coordinate
computation using the project's coordinate calculus (`EuclideanBochner.lean`).
-/

@[expose] public section

open Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Witness

open CutCur CutoffRigidity

variable {k : ℕ}

theorem coordinateDerivative_sq {h : Rd k → ℝ} (hh : Differentiable ℝ h) (j : Fin k) (x : Rd k) :
    coordinateDerivative j (fun y => h y ^ 2) x = 2 * h x * coordinateDerivative j h x := by
  unfold coordinateDerivative
  rw [fderiv_fun_pow 2 (hh x)]
  simp

theorem coordinateDerivative_sum {ι : Type*} (s : Finset ι) {h : ι → Rd k → ℝ}
    (hh : ∀ i ∈ s, Differentiable ℝ (h i)) (j : Fin k) (x : Rd k) :
    coordinateDerivative j (fun y => ∑ i ∈ s, h i y) x = ∑ i ∈ s, coordinateDerivative j (h i) x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sum (fun i hi => (hh i hi) x)]
  simp

theorem coordinateDerivative_mul {a b : Rd k → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (j : Fin k) (x : Rd k) :
    coordinateDerivative j (fun y => a y * b y) x =
      a x * coordinateDerivative j b x + coordinateDerivative j a x * b x := by
  unfold coordinateDerivative
  rw [fderiv_fun_mul (ha x) (hb x)]
  simp [mul_comm]

theorem coordinateDerivative_const_mul {a : Rd k → ℝ} (c : ℝ) (ha : Differentiable ℝ a)
    (j : Fin k) (x : Rd k) :
    coordinateDerivative j (fun y => c * a y) x = c * coordinateDerivative j a x := by
  unfold coordinateDerivative
  rw [fderiv_const_mul (ha x)]
  simp

/-- `‖∇f‖²` as a sum of squares of coordinate derivatives. -/
theorem norm_gradient_sq_eq_sum (f : Rd k → ℝ) (y : Rd k) :
    ‖gradient f y‖ ^ 2 = ∑ i, coordinateDerivative i f y ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_gradient_eq_sum_fderiv_single]
  exact Finset.sum_congr rfl fun i _ => by unfold coordinateDerivative; ring

theorem contDiff_coordinateDerivative_top {f : Rd k → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin k) :
    ContDiff ℝ ∞ (coordinateDerivative i f) :=
  contDiff_coordinateDerivative (n := ∞) (by simpa using hf) i

theorem coordinateDerivative_norm_gradient_sq {f : Rd k → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin k) :
    coordinateDerivative j (fun y => ‖gradient f y‖ ^ 2) =
      fun y => ∑ i, 2 * coordinateDerivative i f y * coordinateDerivative j (coordinateDerivative i f) y := by
  have hd : ∀ i, Differentiable ℝ (coordinateDerivative i f) := fun i =>
    (contDiff_coordinateDerivative_top hf i).differentiable (by simp)
  have hG : (fun y => ‖gradient f y‖ ^ 2) = fun y => ∑ i, coordinateDerivative i f y ^ 2 :=
    funext (norm_gradient_sq_eq_sum f)
  rw [hG]
  funext y
  rw [coordinateDerivative_sum Finset.univ (h := fun i y => coordinateDerivative i f y ^ 2)
      (fun i _ => by have := hd i; fun_prop)]
  exact Finset.sum_congr rfl fun i _ => coordinateDerivative_sq (hd i) j y

/-- The Laplacian of `‖∇f‖²`. -/
theorem laplacian_norm_gradient_sq {f : Rd k → ℝ} (hf : ContDiff ℝ ∞ f) (x : Rd k) :
    euclideanLaplacian (fun y => ‖gradient f y‖ ^ 2) x =
      ∑ j, ∑ i, 2 * (coordinateDerivative j (coordinateDerivative i f) x ^ 2 +
        coordinateDerivative i f x * coordinateDerivative j (coordinateDerivative j (coordinateDerivative i f)) x) := by
  have hfi : ∀ i, ContDiff ℝ ∞ (coordinateDerivative i f) := contDiff_coordinateDerivative_top hf
  have hfij : ∀ i j, ContDiff ℝ ∞ (coordinateDerivative j (coordinateDerivative i f)) := fun i j =>
    contDiff_coordinateDerivative_top (hfi i) j
  have hd : ∀ i, Differentiable ℝ (coordinateDerivative i f) := fun i =>
    (hfi i).differentiable (by simp)
  have hdd : ∀ i j, Differentiable ℝ (coordinateDerivative j (coordinateDerivative i f)) := fun i j =>
    (hfij i j).differentiable (by simp)
  have hG : (fun y => ‖gradient f y‖ ^ 2) = fun y => ∑ i, coordinateDerivative i f y ^ 2 :=
    funext (norm_gradient_sq_eq_sum f)
  have hdG : ∀ j, coordinateDerivative j (fun y => ‖gradient f y‖ ^ 2) =
      fun y => ∑ i, 2 * coordinateDerivative i f y * coordinateDerivative j (coordinateDerivative i f) y := by
    intro j
    rw [hG]
    funext y
    rw [coordinateDerivative_sum Finset.univ (h := fun i y => coordinateDerivative i f y ^ 2)
      (fun i _ => by have := hd i; fun_prop)]
    exact Finset.sum_congr rfl fun i _ => coordinateDerivative_sq (hd i) j y
  unfold euclideanLaplacian
  change ∑ j, coordinateDerivative j (coordinateDerivative j (fun y => ‖gradient f y‖ ^ 2)) x = _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hdG j, coordinateDerivative_sum Finset.univ
    (h := fun i y => 2 * coordinateDerivative i f y * coordinateDerivative j (coordinateDerivative i f) y)
    (fun i _ => by have := hd i; have := hdd i j; fun_prop)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordinateDerivative_mul ((hd i).const_mul 2) (hdd i j), coordinateDerivative_const_mul 2 (hd i)]
  ring

/-- **Bochner identity on flat space**: `Γ₂(f) = ‖D²f‖² + D²V(∇f,∇f)`. -/
theorem gamma2_euclid {V f : Rd k → ℝ} (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (x : Rd k) :
    langevinDifferentialOperator V (fun y => ‖gradient f y‖ ^ 2) x / 2 -
        inner ℝ (gradient f x) (gradient (langevinDifferentialOperator V f) x) =
      (∑ i, ∑ j, coordinateDerivative j (coordinateDerivative i f) x ^ 2) +
        fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) := by
  have hV2 : ContDiff ℝ 2 V := hV.of_le (by norm_cast)
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by norm_cast)
  rw [langevinDifferentialOperator, laplacian_norm_gradient_sq hf,
    inner_gradient_eq_sum_fderiv_single V, inner_gradient_eq_sum_fderiv_single f,
    hessian_gradient_coordinate_contraction hV2 f x]
  have h1 : ∀ i, fderiv ℝ (langevinDifferentialOperator V f) x (EuclideanSpace.single i 1) =
      ∑ j, coordinateDerivative j (coordinateDerivative j (coordinateDerivative i f)) x -
        ∑ j, coordinateDerivative j V x * coordinateDerivative j (coordinateDerivative i f) x -
        ∑ j, coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f x := by
    intro i
    have := coordinateDerivative_langevin_commutator hV2 hf3 i x
    rw [langevin_eq_coordinate_sum] at this
    exact this
  simp only [h1]
  have h2 : ∀ j, fderiv ℝ (fun y => ‖gradient f y‖ ^ 2) x (EuclideanSpace.single j 1) =
      ∑ i, 2 * coordinateDerivative i f x * coordinateDerivative j (coordinateDerivative i f) x := by
    intro j
    exact congrFun (coordinateDerivative_norm_gradient_sq hf j) x
  simp only [h2]
  have hcd : ∀ (g : Rd k → ℝ) (y : Rd k) (i : Fin k),
      fderiv ℝ g y (EuclideanSpace.single i 1) = coordinateDerivative i g y := fun _ _ _ => rfl
  simp only [hcd]
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib]
  have c1 : (∑ a, ∑ b, 2 * coordinateDerivative a (coordinateDerivative b f) x ^ 2) =
      2 * ∑ i, ∑ j, coordinateDerivative j (coordinateDerivative i f) x ^ 2 := by
    rw [Finset.sum_comm]; simp [Finset.mul_sum]
  have c2 : (∑ a, ∑ b, 2 * (coordinateDerivative b f x *
      coordinateDerivative a (coordinateDerivative a (coordinateDerivative b f)) x)) =
      2 * ∑ a, ∑ i, coordinateDerivative a f x *
        coordinateDerivative i (coordinateDerivative i (coordinateDerivative a f)) x := by
    rw [Finset.sum_comm]; simp [Finset.mul_sum]
  have c3 : (∑ a, ∑ i, coordinateDerivative a V x *
      (2 * coordinateDerivative i f x * coordinateDerivative a (coordinateDerivative i f) x)) =
      2 * ∑ a, ∑ i, coordinateDerivative a f x * (coordinateDerivative i V x *
        coordinateDerivative i (coordinateDerivative a f) x) := by
    rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring
  have c4 : (∑ i, ∑ j, coordinateDerivative i f x * coordinateDerivative i (coordinateDerivative j V) x *
      coordinateDerivative j f x) = ∑ a, ∑ i, coordinateDerivative a f x *
        (coordinateDerivative a (coordinateDerivative i V) x * coordinateDerivative i f x) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring
  linarith [c1, c2, c3, c4]

theorem carre_rd {f g : Rd k → ℝ} (x : Rd k) :
    carre (Rd k) f g x = inner ℝ (gradient f x) (gradient g x) := by
  unfold carre
  rw [mgrad_rd, mgrad_rd]

theorem mgenerator_rd {V f : Rd k → ℝ} (hf : ContDiff ℝ 2 f) (x : Rd k) :
    mgenerator (Rd k) V f x = langevinDifferentialOperator V f x := by
  unfold mgenerator langevinDifferentialOperator
  rw [mlaplacian_rd hf, Paper.laplacian_eq_euclideanLaplacian hf, mgrad_rd, mgrad_rd]

theorem carre2_rd {V f : Rd k → ℝ} (hf : ContDiff ℝ ∞ f) (x : Rd k) :
    carre2 (Rd k) V f x =
      langevinDifferentialOperator V (fun y => ‖gradient f y‖ ^ 2) x / 2 -
        inner ℝ (gradient f x) (gradient (langevinDifferentialOperator V f) x) := by
  have hg : ContDiff ℝ ∞ (gradient f) := contDiff_gradient_rd hf (by simp)
  have hG : ContDiff ℝ 2 (fun y => ‖gradient f y‖ ^ 2) :=
    ((hg.norm_sq ℝ).of_le (by norm_cast))
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast)
  have e1 : carre (Rd k) f f = fun y => ‖gradient f y‖ ^ 2 := by
    funext y
    rw [carre_rd, real_inner_self_eq_norm_sq]
  have e2 : mgenerator (Rd k) V f = langevinDifferentialOperator V f := funext (mgenerator_rd hf2)
  unfold carre2
  rw [e1, mgenerator_rd hG, e2, carre_rd]
