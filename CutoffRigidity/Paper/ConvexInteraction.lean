module

public import CutoffRigidity.Paper.GapUpper
public import CutoffRigidity.Paper.CoreBridge
public import CutoffRigidity.ConvexInteractionTheorem

/-! # Theorem 1.5 (convex interaction) on the statement surface -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

section Coordinates

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem unitDirectionCoordinates_apply (v : E) (hv : ‖v‖ = 1) (x : E) :
    ((unitDirectionCoordinates v hv x).ofLp.1 = inner ℝ v x) ∧
      (((unitDirectionCoordinates v hv x).ofLp.2 : E) = x - inner ℝ v x • v) := by
  set A := unitDirectionCoordinates v hv
  have hx : x = (A x).ofLp.1 • v + ((A x).ofLp.2 : E) := by
    conv_lhs => rw [← A.symm_apply_apply x]
    rw [← unitDirectionCoordinates_symm_apply v hv]
  have horth : inner ℝ v ((A x).ofLp.2 : E) = 0 := by
    have := (A x).ofLp.2.2
    rw [Submodule.mem_orthogonal'] at this
    rw [real_inner_comm]
    exact this v (Submodule.mem_span_singleton_self v)
  have hi : inner ℝ v x = (A x).ofLp.1 := by
    conv_lhs => rw [hx]
    rw [inner_add_right, inner_smul_right, horth, real_inner_self_eq_norm_sq, hv]
    simp
  refine ⟨hi.symm, ?_⟩
  rw [hi]
  nth_rewrite 2 [hx]
  abel

/-- The Gaussian factor of a diagonally invariant normalized Gibbs measure, in the form of
the statement surface. -/
theorem gibbs_gaussian_factor_unit (v : E) (hv : ‖v‖ = 1) (W : E → ℝ) (hW : Measurable W)
    (hinv : ∀ x : E, ∀ t : ℝ, W (x + t • v) = W x) {ρ : ℝ} (hρ : 0 < ρ)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x))) :
    (gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x)).map
        (fun x => (inner ℝ v x, x - inner ℝ v x • v)) =
      (gaussianReal 0 ρ⁻¹.toNNReal).prod
        ((gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x)).map
          (fun x => x - inner ℝ v x • v)) := by
  set μ := gibbsMeasure volume (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x) with hμ
  obtain ⟨ν, hν, hfactor⟩ := normalized_gibbs_unit_direction_factor v hv W hW hinv hρ hprob
  set A := unitDirectionCoordinates v hv
  have hfactor' : μ.map (fun x => (A x).ofLp) = (gaussianReal 0 ρ⁻¹.toNNReal).prod ν := hfactor
  have hAm : Measurable (fun x => (A x).ofLp) := by
    have : Continuous (fun x => (A x).ofLp) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Submodule.span ℝ {v})ᗮ).continuous.comp
        A.continuous
    exact this.measurable
  have hΦ : (fun x : E => (inner ℝ v x, x - inner ℝ v x • v)) =
      (Prod.map id (fun w : (Submodule.span ℝ {v})ᗮ => (w : E))) ∘ (fun x => (A x).ofLp) := by
    funext x
    obtain ⟨h1, h2⟩ := unitDirectionCoordinates_apply v hv x
    exact Prod.ext h1.symm h2.symm
  have hcoe : Measurable (fun w : (Submodule.span ℝ {v})ᗮ => (w : E)) := measurable_subtype_coe
  have hmapΦ : μ.map (fun x : E => (inner ℝ v x, x - inner ℝ v x • v)) =
      (gaussianReal 0 ρ⁻¹.toNNReal).prod (ν.map (fun w : (Submodule.span ℝ {v})ᗮ => (w : E))) := by
    rw [hΦ, ← Measure.map_map (measurable_id.prodMap hcoe) hAm, hfactor']
    have h := Measure.map_prod_map (gaussianReal 0 ρ⁻¹.toNNReal) ν measurable_id hcoe
    rw [Measure.map_id] at h
    exact h.symm
  have hsnd : μ.map (fun x => x - inner ℝ v x • v) =
      ν.map (fun w : (Submodule.span ℝ {v})ᗮ => (w : E)) := by
    have hπ : (fun x : E => x - inner ℝ v x • v) =
        Prod.snd ∘ (fun x : E => (inner ℝ v x, x - inner ℝ v x • v)) := rfl
    have hm : Measurable (fun x : E => (inner ℝ v x, x - inner ℝ v x • v)) := by fun_prop
    rw [hπ, ← Measure.map_map measurable_snd hm, hmapΦ, Measure.map_snd_prod]
    simp
  rw [hmapΦ, hsnd]

end Coordinates

/-- **Theorem 1.5** (convex interaction). -/
theorem convex_interaction {d : ℕ} (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {W : CutCur.Rd d → ℝ}
    (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W)
    (hinv : ∀ x (s : ℝ), W (x + s • CutCur.diagonal d) = W x)
    (hp : IsProbabilityMeasure (CutCur.gibbs fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) :
    let V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + W x
    let u := (Real.sqrt d)⁻¹ • CutCur.diagonal d
    let π := fun x : CutCur.Rd d => x - inner ℝ u x • u
    (CutCur.spectralGap V = ρ ∧ CutCur.IsEigenfunction V ρ (fun x => ∑ i, x i)) ∧
    ((∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) ∧
      (CutCur.gibbs V).map (fun x => (inner ℝ u x, π x)) =
        (gaussianReal 0 ρ⁻¹.toNNReal).prod ((CutCur.gibbs V).map π)) ∧
    CutCur.RigidCurvature V := by
  intro V u π
  have hinv' : ∀ x : CutCur.Rd d, ∀ t : ℝ, W (x + t • diagonalDirection d) = W x := hinv
  obtain ⟨hV, hconc⟩ := convexInteraction_theorem hd hW hconv hρ hinv' hp
  have hdne : diagonalDirection d ≠ 0 := diagonalDirection_ne_zero hd
  have hderiv : ∀ x : CutCur.Rd d, langevinDifferentialOperator V
      (fun y => inner ℝ (diagonalDirection d) y + 0) x =
      -ρ * (inner ℝ (diagonalDirection d) x + 0) := fun x => by
    simpa only [add_zero, inner_diagonalDirection] using
      langevinDifferentialOperator_coordinateSum (hW.differentiable (by norm_num) x) (hinv' x)
  have hgap : CutCur.spectralGap V = ρ :=
    spectralGap_eq_of_affine_eigenfunction hV hp hd ρ hρ hconc.hessian_bound hconc.spectral_gap
      (diagonalDirection d) hdne hderiv
  have hsum : ContDiff ℝ 2 (coordinateSum : CutCur.Rd d → ℝ) := by
    have heq : (coordinateSum : CutCur.Rd d → ℝ) = innerSL ℝ (diagonalDirection d) :=
      funext (fun x => (inner_diagonalDirection x).symm)
    rw [heq]
    exact (innerSL ℝ (diagonalDirection d)).contDiff
  have hmem := coordinateSum_memLp_gibbs (hW.differentiable (by norm_num)) hρ hinv' hp
  refine ⟨⟨hgap, isEigenfunction_iff.mpr ⟨hsum, hmem, fun x => ?_⟩⟩, ⟨hconc.hessian_bound, ?_⟩,
    ⟨hgap ▸ hρ, fun x z => hgap ▸ hconc.hessian_bound x z⟩⟩
  · have := hderiv x
    simp only [add_zero, inner_diagonalDirection] at this
    exact this
  · have hnorm : ‖diagonalDirection d‖ = Real.sqrt d := by
      rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_diagonalDirection]
    have hu : u = unitDiagonalDirection d := by
      simp only [u, unitDiagonalDirection, hnorm]
      rfl
    have hv : ‖unitDiagonalDirection d‖ = 1 := norm_unitDiagonalDirection hd
    have hWinv : ∀ x : CutCur.Rd d, ∀ t : ℝ, W (x + t • unitDiagonalDirection d) = W x := by
      intro x t
      rw [unitDiagonalDirection, smul_smul]
      exact hinv' x _
    have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
    simp only [hu, π, V]
    exact gibbs_gaussian_factor_unit _ hv W (hW.continuous.measurable) hWinv hρ hp'

end CutoffRigidity.Paper
