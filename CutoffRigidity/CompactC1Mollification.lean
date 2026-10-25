module

public import CutoffRigidity.C1LaplacianTest
public import CutoffRigidity.WeakH1Mollification

/-! # Genuine compact C¹ strong H¹ approximation with one common support -/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped Pointwise

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Compact C¹ tests and their classical gradients are approximated
strongly by actual compact smooth mollifications in Lebesgue L². -/
theorem mollifiedGradientLp_tendsto_of_compact_c1 {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (φ : ℕ → ContDiffBump (0 : E)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => mollifiedGradientLp (φ n) g hg.continuous.locallyIntegrable hgc)
      atTop (𝓝 ((c1_compact_gradient_memLp hg hgc).toLp (gradient g))) := by
  let G := (c1_compact_gradient_memLp hg hgc).toLp (gradient g)
  let H (j : Fin d) := (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp G
  have hw (j : Fin d) (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) :
      (∫ x, g x * coordinateDerivative j ψ x) = -(∫ x, H j x * ψ x) := by
    rw [c1_volume_weak_derivative_compact_test hg (hψ.of_le (by norm_num)) hψc j]
    congr 1
    apply integral_congr_ae
    filter_upwards [(EuclideanSpace.proj j : E →L[ℝ] ℝ).coeFn_compLp G,
      (c1_compact_gradient_memLp hg hgc).coeFn_toLp] with x hp hx
    rw [hp, hx]
    rw [coordinateDerivative, fderiv_single_eq_gradient_coordinate]
    rfl
  have he := mollifiedGradientLp_tendsto_of_weak_derivatives φ hφ
    hg.continuous.locallyIntegrable hgc H hw
  simpa only [H, euclideanL2_assemble_projections, G] using he

/-- At outer radius at most one, every actual smoothing has support in
one fixed compact enlargement of the original support. -/
theorem bumpMollification_eq_zero_off_unit_enlargement (φ : ContDiffBump (0 : E))
    (hφ : φ.rOut ≤ 1) {g : E → ℝ} (x : E)
    (hx : x ∉ Metric.closedBall (0 : E) 1 + tsupport g) : bumpMollification φ g x = 0 := by
  apply bumpMollification_eq_zero_off_add_support φ
    (fun y hy => image_eq_zero_of_notMem_tsupport hy) x
  intro h
  apply hx
  rcases h with ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, Metric.closedBall_subset_closedBall hφ ha, b, hb, rfl⟩

theorem eq_zero_off_unit_support_enlargement {g : E → ℝ} (x : E)
    (hx : x ∉ Metric.closedBall (0 : E) 1 + tsupport g) : g x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hx ⟨0, by simp, x, h, by simp⟩

end CutoffRigidity
