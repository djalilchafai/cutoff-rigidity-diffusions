module

public import CutoffRigidity.Extra.Sphere15

/-! # Sphere, stage 16: the first eigenspace of `S^d` contains `d + 1 > d` independent eigenfunctions

On the round sphere `λ₁ = d`, the `d + 1` coordinate functions are `L²`-independent smooth eigenfunctions of `-𝓛`
for `λ₁`; the first eigenspace therefore has (algebraic) dimension at least `d + 1 > d = dim S^d`, in contrast with the
conclusion `k₁ ≤ dim M` of the Riemannian theorem under `hgap : λ₁ = ρ`: the hypothesis `hgap` cannot be dropped.
-/

@[expose] public section

open Bundle Filter Set VectorField MeasureTheory
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutoffRigidity CutoffRigidity.Extra

namespace Sph

variable (d : ℕ)

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Fd" => EuclideanSpace ℝ (Fin d)

lemma memLp_phi {μ : Measure (Sph d)} [IsProbabilityMeasure μ] (a : 𝔼) :
    MemLp (phi (val d) a) 2 μ :=
  ((contMDiff_phi (isIsometricSphereMap d) a).continuous).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Every coordinate function is a smooth `L²` eigenfunction of `-𝓛` for `λ₁ = d`. -/
theorem isMEigenfunction_phi (hd : 2 ≤ d) {μ : Measure (Sph d)} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume Fd μ (fun _ => c)) (a : 𝔼) :
    IsMEigenfunction Fd μ (fun _ : Sph d => c) (mSpectralGap Fd μ) (phi (val d) a) := by
  refine ⟨contMDiff_phi (isIsometricSphereMap d) a, memLp_phi d a, fun x => ?_⟩
  rw [gap_eq d hd hμ, mgenerator_phi (finrank_model d) (isIsometricSphereMap d)]

/-- The `d + 1` coordinate eigenfunctions are linearly independent in `L²(μ)`. -/
theorem linearIndependent_coords (hd : 2 ≤ d) {μ : Measure (Sph d)} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume Fd μ (fun _ => c)) :
    LinearIndependent ℝ (fun i : Fin (d + 1) =>
      (memLp_phi d (μ := μ) (EuclideanSpace.single i (1 : ℝ))).toLp) := by
  haveI := CutoffRigidity.Riemann.Diff.isOpenPosMeasure_of_isWeightedVolume Fd
    (contMDiff_const (c := c)) hμ
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  set u : Fin (d + 1) → Lp ℝ 2 μ := fun i =>
    (memLp_phi d (μ := μ) (EuclideanSpace.single i (1 : ℝ))).toLp with hu
  have hae : ∀ᵐ x ∂μ, ∑ i, g i * phi (val d) (EuclideanSpace.single i (1 : ℝ)) x = 0 := by
    have h1 := Lp.coeFn_fun_finsetSum (μ := μ) (p := 2) Finset.univ (fun i => g i • u i)
    have h3 : ∀ᵐ x ∂μ, ∀ i, ((g i • u i : Lp ℝ 2 μ) : Sph d → ℝ) x =
        g i * phi (val d) (EuclideanSpace.single i (1 : ℝ)) x := by
      rw [ae_all_iff]
      intro i
      filter_upwards [Lp.coeFn_smul (g i) (u i),
        (memLp_phi d (μ := μ) (EuclideanSpace.single i (1 : ℝ))).coeFn_toLp] with x hx1 hx2
      rw [hx1]
      simp [hu, hx2]
    have h2 := Lp.coeFn_zero ℝ 2 μ
    have hg' : ∑ i, g i • u i = 0 := hg
    rw [hg'] at h1
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [← Finset.sum_congr rfl fun i _ => hx3 i, ← hx1, hx2]
    rfl
  have hcont : Continuous (fun x : Sph d => ∑ i, g i * phi (val d) (EuclideanSpace.single i (1 : ℝ)) x) :=
    continuous_finset_sum _ fun i _ =>
      continuous_const.mul (contMDiff_phi (isIsometricSphereMap d) _).continuous
  have hall : ∀ x, ∑ i, g i * phi (val d) (EuclideanSpace.single i (1 : ℝ)) x = 0 := by
    have := (Continuous.ae_eq_iff_eq μ hcont continuous_const (g := fun _ => (0 : ℝ))).1
      (by filter_upwards [hae] with x hx using hx)
    intro x; exact congrFun this x
  -- evaluate at the point `e_j`
  let pt : Sph d := ⟨EuclideanSpace.single j 1, by simp⟩
  have := hall pt
  simp only [phi, val, pt] at this
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply] using this

/-- **The first eigenspace of the round sphere contains `d + 1` linearly independent classes**: there are
`d + 1` linearly independent classes in `L²(μ)`, each represented by a smooth eigenfunction of `-𝓛` for
`λ₁ = mSpectralGap`. This statement does not mention `mFirstEigenDim` and does not claim finite-dimensionality or
`k₁ = d + 1`; the consequence for `mFirstEigenDim` is `Sph.k1_fails` (Sphere17). -/
theorem first_eigenspace_large (hd : 2 ≤ d) {μ : Measure (Sph d)} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume Fd μ (fun _ => c)) :
    ∃ u : Fin (d + 1) → (Sph d →₂[μ] ℝ), LinearIndependent ℝ u ∧
      ∀ i, ∃ f, IsMEigenfunction Fd μ (fun _ : Sph d => c) (mSpectralGap Fd μ) f ∧ f =ᵐ[μ] u i :=
  ⟨_, linearIndependent_coords d hd hμ, fun i =>
    ⟨phi (val d) (EuclideanSpace.single i (1 : ℝ)), isMEigenfunction_phi d hd hμ _,
      (memLp_phi d (μ := μ) (EuclideanSpace.single i (1 : ℝ))).coeFn_toLp.symm⟩⟩

end Sph

end CutoffRigidity.Extra.Sphere
