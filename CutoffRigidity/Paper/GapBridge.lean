module

public import CutoffRigidity.Paper.CoreBridge
public import CutoffRigidity.GibbsSpectralPoincare
public import CutoffRigidity.GibbsOperatorCurvatureGap
public import CutoffRigidity.GibbsOperatorAffineRepresentative
public import CutoffRigidity.OperatorWassersteinTheorem

/-! # Bridges from the statement surface to the library: spectral objects

Under the rigid curvature condition `Hess V ≥ λ₁ > 0`, the variational spectral
gap of the statement surface (the optimal Poincaré constant over smooth compactly
supported functions) is the library's operator-theoretic gap: the Poincaré
inequality at the library gap bounds every Rayleigh quotient from below, and the
Bakry–Émery bound of the library gives the converse. Consequently the first
eigenspace, its dimension `k₁` and the function `Λ` agree with the library ones.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ContDiff

variable {d : ℕ}

/-! ### The spectral gap -/

/-- In dimension zero no test function has positive variance, so a positive
spectral gap forces a positive dimension. -/
theorem pos_dim_of_spectralGap_pos {V : CutCur.Rd d → ℝ}
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hgap : 0 < CutCur.spectralGap V) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h0 | h
  · subst h0
    exfalso
    have hempty : {r : ℝ | ∃ f : CutCur.Rd 0 → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        0 < variance f (CutCur.gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) /
          variance f (CutCur.gibbs V)} = ∅ := by
      ext r
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro f _ _ hvar
      have hc : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
      rw [hc, variance_eq_integral aemeasurable_const] at hvar
      simp at hvar
    rw [CutCur.spectralGap, hempty, Real.sInf_empty] at hgap
    exact lt_irrefl _ hgap
  · exact h

/-- The Poincaré inequality at the library gap, in Rayleigh form, for smooth compactly
supported test functions. -/
theorem gibbsSpectralGap_mul_variance_le {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f : CutCur.Rd d → ℝ} (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f) :
    gibbsSpectralGap hV hp * variance f (CutCur.gibbs V) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V := by
  let μ := gibbsMeasure volume V
  let m := ∫ x, f x ∂μ
  have hg := gibbsSpectralGap_pos hV hp hd ρ hρ hHess
  have hP := hasSmoothPoincare_gibbsSpectralGap hV hp hd ρ hρ hHess
  have hfc : Continuous f := hf.continuous
  have hfL : MemLp f 2 μ := hfc.memLp_of_hasCompactSupport hcs
  have hgrad : gradient (fun x => f x - m) = gradient f := by
    funext x
    simp only [gradient, fderiv_sub_const]
  have hgc : Continuous (gradient f) := continuous_gradient_of_c1 (hf.of_le (by simp))
  have hgcs : HasCompactSupport (fun x => ‖gradient f x‖ ^ 2) := by
    have h1 : HasCompactSupport (gradient f) :=
      (hcs.fderiv (𝕜 := ℝ)).comp_left (g := (InnerProductSpace.toDual ℝ (CutCur.Rd d)).symm)
        (map_zero _)
    exact h1.comp_left (g := fun v : CutCur.Rd d => ‖v‖ ^ 2) (by simp)
  have hint : Integrable (fun x => ‖gradient f x‖ ^ 2) μ :=
    (hgc.norm.pow 2).integrable_of_hasCompactSupport hgcs
  have h := hP (fun x => f x - m) (hf.sub contDiff_const) (hfL.sub (memLp_const m))
    (by rw [hgrad]; exact hint)
    (by rw [integral_sub (hfL.integrable one_le_two) (integrable_const m)]; simp [m])
  rw [hgrad] at h
  have hvar : variance f (CutCur.gibbs V) = ∫ x, (f x - m) ^ 2 ∂μ :=
    variance_eq_integral hfc.aemeasurable
  rw [hvar]
  rw [le_div_iff₀ hg] at h
  exact (mul_comm _ _).trans_le h

/-- Under the rigid curvature condition, the variational gap of the statement surface is
the library's operator-theoretic gap. -/
theorem spectralGap_eq_gibbsSpectralGap {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V) :
    CutCur.spectralGap V = gibbsSpectralGap hV hp := by
  obtain ⟨hs, hHess⟩ := hrig
  have hd := pos_dim_of_spectralGap_pos hp hs
  set ρ := CutCur.spectralGap V with hρdef
  set g := gibbsSpectralGap hV hp
  have hge : ρ ≤ g := gibbsSpectralGap_ge_curvature hV hp hd ρ hs hHess
  set R := {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    0 < variance f (CutCur.gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) /
      variance f (CutCur.gibbs V)} with hR
  have hρR : ρ = sInf R := rfl
  have hne : R.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hρR, h, Real.sInf_empty] at hs
    exact lt_irrefl _ hs
  have hle : g ≤ ρ := by
    rw [hρR]
    refine le_csInf hne ?_
    rintro r ⟨f, hf, hcs, hvar, rfl⟩
    exact (le_div_iff₀ hvar).mpr
      (gibbsSpectralGap_mul_variance_le hV hp hd ρ hs hHess hf hcs)
  exact le_antisymm hge hle

/-- Positivity of the dimension under the rigid curvature condition. -/
theorem pos_dim_of_rigidCurvature {V : CutCur.Rd d → ℝ}
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hrig : CutCur.RigidCurvature V) : 0 < d :=
  pos_dim_of_spectralGap_pos hp hrig.1

end CutoffRigidity.Paper
