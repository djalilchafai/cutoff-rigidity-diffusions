module

public import CutoffRigidity.Riemann.DiffPerron0
public import CutoffRigidity.Riemann.DiffForm

/-! # Compactly supported subsolution from a penalized resolvent (workstream PENAL, P3)

`f = θ_ε ∘ v` is a smooth compactly supported subsolution `(λ - 𝓛) f ≤ g`, exactly and pointwise.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur CutoffRigidity.Riemann

/-- A smooth convex nondecreasing cutoff function `θ_ε`. -/
theorem exists_convex_cutoff_fn {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ θ 0 = 0 ∧ (∀ r, r ≤ ε → θ r = 0) ∧
      (∀ r, 0 ≤ deriv θ r ∧ deriv θ r ≤ 1) ∧ (∀ r, 0 ≤ deriv (deriv θ) r) ∧
      (∀ r, r - 2 * ε ≤ θ r) ∧ (∀ r, 0 ≤ r → θ r ≤ r * deriv θ r) := by
  set φ : ℝ → ℝ := fun t => Real.smoothTransition ((t - ε) / ε) with hφ
  have hφc : ContDiff ℝ ∞ φ :=
    Real.smoothTransition.contDiff.comp (((contDiff_id.sub contDiff_const)).div_const ε)
  have hφcont : Continuous φ := hφc.continuous
  have hφ0 : ∀ t, t ≤ ε → φ t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)
  have hφ1 : ∀ t, 2 * ε ≤ t → φ t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith)
  have hφmono : Monotone φ := fun a b hab =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hε.le)
  set θ : ℝ → ℝ := fun r => ∫ t in ε..r, φ t with hθ
  have hder : ∀ r, HasDerivAt θ (φ r) r := fun r => intervalIntegral.integral_hasDerivAt_right (hφcont.intervalIntegrable _ _)
    (hφcont.stronglyMeasurableAtFilter _ _) hφcont.continuousAt
  have hderiv : deriv θ = φ := funext fun r => (hder r).deriv
  have hθs : ContDiff ℝ ∞ θ :=
    contDiff_infty_iff_deriv.2 ⟨fun r => (hder r).differentiableAt, by rw [hderiv]; exact hφc⟩
  have hθ0 : ∀ r, r ≤ ε → θ r = 0 := by
    intro r hr
    simp only [hθ]
    rw [intervalIntegral.integral_symm, neg_eq_zero]
    refine intervalIntegral.integral_zero_ae ?_
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hr] at ht
    exact hφ0 t ht.2
  have hθnn : ∀ r, ε ≤ r → 0 ≤ θ r := by
    intro r hr
    exact intervalIntegral.integral_nonneg hr fun t _ => Real.smoothTransition.nonneg _
  have hθnn' : ∀ r, 0 ≤ θ r := fun r => by
    rcases le_total r ε with h | h
    · rw [hθ0 r h]
    · exact hθnn r h
  refine ⟨θ, hθs, hθ0 0 hε.le, hθ0, ?_, ?_, ?_, ?_⟩
  · intro r; rw [hderiv]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro r; rw [hderiv]; exact hφmono.deriv_nonneg
  · intro r
    rcases le_total r (2 * ε) with h | h
    · linarith [hθnn' r]
    · have h1 : θ r = θ (2 * ε) + ∫ t in (2 * ε)..r, φ t := by
        simp only [hθ]
        rw [intervalIntegral.integral_add_adjacent_intervals]
        · exact hφcont.intervalIntegrable _ _
        · exact hφcont.intervalIntegrable _ _
      have h2 : ∫ t in (2 * ε)..r, φ t = r - 2 * ε := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
        · simp
        · intro t ht
          rw [Set.uIcc_of_le h] at ht
          exact hφ1 t ht.1
      linarith [hθnn' (2 * ε)]
  · intro r hr
    have hh : MonotoneOn (fun r => r * deriv θ r - θ r) (Set.Ici 0) := by
      have hd : ∀ r, HasDerivAt (fun r => r * deriv θ r - θ r)
          (deriv θ r + r * deriv (deriv θ) r - φ r) r := by
        intro r
        have h1 : HasDerivAt (deriv θ) (deriv (deriv θ) r) r := by
          rw [hderiv]
          exact ((hφc.differentiable (by simp)) r).hasDerivAt
        exact (((hasDerivAt_id r).mul h1).sub (hder r)).congr_deriv (by simp)
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
      · exact fun r _ => (hd r).continuousAt.continuousWithinAt
      · exact fun r _ => (hd r).differentiableAt.differentiableWithinAt
      · intro r hr'
        rw [interior_Ici] at hr'
        rw [(hd r).deriv, hderiv]
        have : 0 ≤ deriv φ r := hφmono.deriv_nonneg
        nlinarith [hr'.out.le]
    have := hh (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hr) hr
    have h0 : θ 0 = 0 := hθ0 0 hε.le
    dsimp only at this
    rw [h0, zero_mul, sub_zero] at this
    linarith

section Sub

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- **Compactly supported subsolution** `f = θ_ε ∘ v`: `(λ - 𝓛) f ≤ g` exactly, `f ≥ v - 2ε`. -/
theorem subsolution_of_penalized {V : M → ℝ} {lam : ℝ} (hlam : 0 < lam) {v g κ : M → ℝ}
    (hv : MSmooth F v) (h0 : ∀ x, 0 ≤ v x) (hg : ∀ x, 0 ≤ g x) (hκ : ∀ x, 0 ≤ κ x)
    (hv' : ∀ x, mgenerator F V v x = (lam + κ x) * v x - g x) {ε : ℝ} (hε : 0 < ε)
    {K₀ : Set M} (hK₀ : IsCompact K₀) (hsupp : ∀ x, ε ≤ v x → x ∈ K₀) :
    ∃ f : M → ℝ, f ∈ testSub F M ∧ (∀ y, lam * f y - mgenerator F V f y ≤ g y) ∧
      (∀ y, v y - 2 * ε ≤ f y) := by
  obtain ⟨θ, hθ, hθ0, hθz, hθd, hθdd, hθge, hθle⟩ := exists_convex_cutoff_fn hε
  refine ⟨θ ∘ v, ⟨hθ.contMDiff.comp hv, ?_⟩, fun y => ?_, fun y => hθge (v y)⟩
  · refine HasCompactSupport.intro hK₀ fun x hx => ?_
    apply hθz
    by_contra h
    exact hx (hsupp x (not_le.1 h).le)
  · rw [mgenerator_comp_real F hθ hv y, hv' y]
    have a1 := hθle (v y) (h0 y)
    have a2 := hθdd (v y)
    have a3 := carre_nonneg F v y
    obtain ⟨b1, b2⟩ := hθd (v y)
    have c1 : lam * θ (v y) ≤ lam * (v y * deriv θ (v y)) := mul_le_mul_of_nonneg_left a1 hlam.le
    have c2 : 0 ≤ deriv θ (v y) * (κ y * v y) :=
      mul_nonneg b1 (mul_nonneg (hκ y) (h0 y))
    have c3 : deriv θ (v y) * g y ≤ g y := by nlinarith [hg y]
    have c4 : 0 ≤ deriv (deriv θ) (v y) * carre F v v y := mul_nonneg a2 a3
    simp only [Function.comp]
    nlinarith

end Sub

end CutoffRigidity.Riemann.Diff
