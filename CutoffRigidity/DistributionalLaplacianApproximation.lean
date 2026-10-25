module

public import CutoffRigidity.EuclideanMollificationStrongLimit
public import CutoffRigidity.GibbsOperatorDomainLocalization

/-! # Strong approximation of actual distributional Laplacians

Smooth convolution preserves the genuine Laplace equation and converges
strongly in L² to its actual source. This supplies the second-order part of
local graph approximation, including for arbitrary actual operator-domain
pairs rather than just eigenvectors.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual smooth Laplacian is in L² because it is the mollified source. -/
theorem mollified_laplacian_memLp {w F : E → ℝ}
    (hw : LocallyIntegrable w volume) (hFm : Measurable F) (hF : MemLp F 2 volume)
    (heq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, w x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    (φ : ContDiffBump (0 : E)) :
    MemLp (euclideanLaplacian (bumpMollification φ w)) 2 volume := by
  have he : euclideanLaplacian (bumpMollification φ w) = bumpMollification φ F := by
    funext x
    exact convolution_laplacian_eq_of_distributional_equation hw
      (φ.contDiff_normed (n := 3)) φ.hasCompactSupport_normed heq x
  rw [he]
  exact (bumpMollification_L2_contraction φ hFm hF).1

/-- The L² class of the genuine differentiated mollification. -/
@[expose] noncomputable def mollifiedLaplacianLp {w F : E → ℝ}
    (hw : LocallyIntegrable w volume) (hFm : Measurable F) (hF : MemLp F 2 volume)
    (heq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, w x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    (φ : ContDiffBump (0 : E)) : E →₂[volume] ℝ :=
  (mollified_laplacian_memLp hw hFm hF heq φ).toLp
    (euclideanLaplacian (bumpMollification φ w))

/-- Strong convergence of actual smooth Laplacians to the genuine weak source. -/
theorem mollifiedLaplacianLp_tendsto {w F : E → ℝ}
    (hw : LocallyIntegrable w volume) (hFm : Measurable F) (hF : MemLp F 2 volume)
    (heq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, w x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => mollifiedLaplacianLp hw hFm hF heq (φ n))
      atTop (𝓝 (hF.toLp F)) := by
  have he (n : ℕ) : mollifiedLaplacianLp hw hFm hF heq (φ n) =
      bumpMollificationLp (φ n) F hFm hF := by
    apply Lp.ext
    filter_upwards [(mollified_laplacian_memLp hw hFm hF heq (φ n)).coeFn_toLp,
      (bumpMollification_L2_contraction (φ n) hFm hF).1.coeFn_toLp] with x hx hy
    change (mollified_laplacian_memLp hw hFm hF heq (φ n)).toLp _ x = _
    rw [hx]
    change _ = (bumpMollification_L2_contraction (φ n) hFm hF).1.toLp _ x
    rw [hy]
    exact convolution_laplacian_eq_of_distributional_equation hw
      ((φ n).contDiff_normed (n := 3)) (φ n).hasCompactSupport_normed heq x
  simp_rw [he]
  exact bumpMollificationLp_tendsto φ hφ F hFm hF

end CutoffRigidity
