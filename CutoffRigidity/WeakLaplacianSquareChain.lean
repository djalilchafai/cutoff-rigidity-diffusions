module

public import CutoffRigidity.WeakLaplacianC1Tests
public import CutoffRigidity.GibbsLocalizedTranslations

/-! # The actual weak Laplacian square chain at C¹ regularity

Testing the genuine weak equation against fψ is justified by actual H¹
mollification. Classical C¹ integration by parts for f² then proves the
paper's carré-du-champ identity without a C² representative assumption.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem compactSupport_of_eq_zero_off_compact {g : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hg : ∀ x ∉ K, g x = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra h
  exact hx (hg x h)

theorem gradient_square_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x : E) :
    gradient (fun y => f y ^ 2) x = (2 * f x) • gradient f x := by
  have he : (fun y => f y ^ 2) = fun y => f y * f y := by
    funext y
    ring
  rw [he, gradient_cutoff_mul (hf.differentiable (by norm_num)) (hf.differentiable (by norm_num))]
  rw [← add_smul]
  congr 1
  ring

set_option maxHeartbeats 600000 in
/-- Genuine distributional square chain: local L² Δf=F and C¹f imply
Δ(f²)=2fF+2‖∇f‖² on compact C² tests. Global bounds are not needed by
this local argument, so in particular bounded C¹ backward functions apply. -/
theorem weak_laplacian_square_chain {f F : E → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hFloc : ∀ K : Set E, IsCompact K → MemLp F 2 ((volume : Measure E).restrict K))
    (hLap : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, f x ^ 2 * euclideanLaplacian ψ x) =
      ∫ x, (2 * f x * F x + 2 * ‖gradient f x‖ ^ 2) * ψ x := by
  let A (x : E) := f x * inner ℝ (gradient f x) (gradient ψ x)
  let B (x : E) := ψ x * ‖gradient f x‖ ^ 2
  let C (x : E) := F x * (f x * ψ x)
  have hGf := continuous_gradient_of_c1 hf
  have hGψ := continuous_gradient_of_c1 (hψ.of_le (by norm_num))
  have hAcont : Continuous A := hf.continuous.mul (hGf.inner hGψ)
  have hAoff : ∀ x ∉ tsupport ψ, A x = 0 := by
    intro x hx
    have hgψ : gradient ψ x = 0 := gradient_eq_zero_off_closed_support (isClosed_tsupport ψ)
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) hx
    simp only [A, hgψ, inner_zero_right, mul_zero]
  have hA : Integrable A volume := hAcont.integrable_of_hasCompactSupport
    (compactSupport_of_eq_zero_off_compact hψc hAoff)
  have hBcont : Continuous B := hψ.continuous.mul (hGf.norm.pow 2)
  have hBc : HasCompactSupport B := by
    simpa only [B, Pi.mul_def] using hψc.mul_right (f' := fun x => ‖gradient f x‖ ^ 2)
  have hB : Integrable B volume := hBcont.integrable_of_hasCompactSupport hBc
  have hη : ContDiff ℝ 1 (fun x => f x * ψ x) := hf.mul (hψ.of_le (by norm_num))
  have hηc : HasCompactSupport (fun x => f x * ψ x) := by
    simpa only [Pi.mul_def] using hψc.mul_left (f := f)
  have hC : Integrable C volume :=
    locallyL2_mul_compact_continuous_integrable hFloc hη.continuous hηc
  have hE := weak_laplacian_compact_c1_test hf hFloc hLap hη hηc
  have hpoint (x : E) : inner ℝ (gradient f x) (gradient (fun y => f y * ψ y) x) = A x + B x := by
    rw [gradient_cutoff_mul (hf.differentiable (by norm_num)) (hψ.differentiable (by norm_num))]
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, A, B]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_add hA hB] at hE
  change (∫ x, A x) + (∫ x, B x) = -(∫ x, C x) at hE
  have hsq : ContDiff ℝ 1 (fun x => f x ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hf.mul hf
  have hIBP := c1_integral_mul_laplacian_compact_test hsq hψ hψc
  have hsqp (x : E) : inner ℝ (gradient (fun y => f y ^ 2) x) (gradient ψ x) = 2 * A x := by
    rw [gradient_square_of_c1 hf, real_inner_smul_left]
    dsimp only [A]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsqp), integral_const_mul] at hIBP
  have hrhs (x : E) : (2 * f x * F x + 2 * ‖gradient f x‖ ^ 2) * ψ x = 2 * C x + 2 * B x := by
    dsimp only [C, B]
    ring
  rw [hIBP, integral_congr_ae (Filter.Eventually.of_forall hrhs),
    integral_add (hC.const_mul 2) (hB.const_mul 2), integral_const_mul, integral_const_mul]
  linarith only [hE]

theorem weak_laplacian_square_chain_of_continuous_rhs {f F : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hF : Continuous F)
    (hLap : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, f x ^ 2 * euclideanLaplacian ψ x) =
      ∫ x, (2 * f x * F x + 2 * ‖gradient f x‖ ^ 2) * ψ x :=
  weak_laplacian_square_chain hf (fun _K hK => continuous_memLp_two_restrict_compact hF hK)
    hLap ψ hψ hψc

/-- The source weak Langevin carré-du-champ identity, in ordinary-volume
distribution form. The potential drift cancels by the genuine C¹ square
gradient rule, leaving exactly 2fLf+2‖∇f‖² as the generator right-hand side. -/
theorem weak_langevin_square_chain {V f G : E → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hFloc : ∀ K : Set E, IsCompact K →
      MemLp (fun x => G x + inner ℝ (gradient V x) (gradient f x)) 2
        ((volume : Measure E).restrict K))
    (hLap : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
      ∫ x, (G x + inner ℝ (gradient V x) (gradient f x)) * ψ x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, f x ^ 2 * euclideanLaplacian ψ x) =
      ∫ x, ((2 * f x * G x + 2 * ‖gradient f x‖ ^ 2) +
        inner ℝ (gradient V x) (gradient (fun y => f y ^ 2) x)) * ψ x := by
  have he := weak_laplacian_square_chain hf hFloc hLap ψ hψ hψc
  refine he.trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro x
  dsimp only
  rw [gradient_square_of_c1 hf, inner_smul_right]
  ring

end CutoffRigidity
