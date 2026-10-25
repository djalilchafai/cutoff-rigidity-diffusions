module

public import CutoffRigidity.Riemann.DiffSobolevRn1
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Calculus of weak derivatives

Linearity, a.e. invariance, uniqueness (global), classical derivatives are weak derivatives,
Leibniz rule with a smooth factor, symmetry of mixed weak derivatives.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integrable_mul_of_locInt {Ω : Set E} {u ψ : E → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ω) : Integrable (fun x => u x * ψ x) volume := by
  have h1 : IntegrableOn u (tsupport ψ) volume := hu.integrableOn_compact_subset hs hc
  have h2 : IntegrableOn (fun x => u x * ψ x) (tsupport ψ) volume :=
    h1.mul_continuousOn hψ.continuousOn hc
  refine h2.integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  have : ψ x = 0 := by
    by_contra h
    exact hx (subset_tsupport _ h)
  simp [this]

theorem IsTest.mono {Ω Ω' : Set E} (h : Ω ⊆ Ω') {φ : E → ℝ} (hφ : IsTest Ω φ) : IsTest Ω' φ :=
  ⟨hφ.1, hφ.2.1, hφ.2.2.trans h⟩

theorem IsTest.mul {Ω : Set E} {φ g : E → ℝ} (hφ : IsTest Ω φ) (hg : ContDiff ℝ ∞ g) :
    IsTest Ω (fun x => g x * φ x) :=
  ⟨hg.mul hφ.1, hφ.2.1.mul_left, (tsupport_mul_subset_right).trans hφ.2.2⟩

theorem IsTest.pd {Ω : Set E} {φ : E → ℝ} (hφ : IsTest Ω φ) (v : E) : IsTest Ω (pd v φ) := by
  refine ⟨?_, ?_, ?_⟩
  · have : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.1.fderiv_right (by simp)
    exact this.clm_apply contDiff_const
  · exact hφ.2.1.fderiv_apply ℝ v
  · exact (tsupport_fderiv_apply_subset ℝ v).trans hφ.2.2

theorem HasWDeriv.mono {Ω Ω' : Set E} {v : E} {u w : E → ℝ} (h : HasWDeriv Ω v u w)
    (hΩ : Ω' ⊆ Ω) : HasWDeriv Ω' v u w :=
  ⟨h.1.mono_set hΩ, h.2.1.mono_set hΩ, fun φ hφ => h.2.2 φ (hφ.mono hΩ)⟩

theorem HasWDeriv.congr_ae {Ω : Set E} {v : E} {u u' w w' : E → ℝ}
    (h : HasWDeriv Ω v u w) (hu : u =ᵐ[volume] u') (hw : w =ᵐ[volume] w') :
    HasWDeriv Ω v u' w' := by
  refine ⟨h.1.congr ?_, h.2.1.congr ?_, fun φ hφ => ?_⟩
  · exact (ae_restrict_of_ae hu)
  · exact (ae_restrict_of_ae hw)
  · have e1 : ∫ x, u' x * pd v φ x = ∫ x, u x * pd v φ x :=
      integral_congr_ae (by filter_upwards [hu] with x hx; rw [hx])
    have e2 : ∫ x, w' x * φ x = ∫ x, w x * φ x :=
      integral_congr_ae (by filter_upwards [hw] with x hx; rw [hx])
    rw [e1, e2]; exact h.2.2 φ hφ

theorem hasWDeriv_congr_left {Ω : Set E} {v : E} {u u' w : E → ℝ} (hu : u =ᵐ[volume] u')
    : HasWDeriv Ω v u w ↔ HasWDeriv Ω v u' w :=
  ⟨fun h => h.congr_ae hu Filter.EventuallyEq.rfl, fun h => h.congr_ae hu.symm Filter.EventuallyEq.rfl⟩

theorem HasWDeriv.add {Ω : Set E} {v : E} {u₁ u₂ w₁ w₂ : E → ℝ} (h₁ : HasWDeriv Ω v u₁ w₁)
    (h₂ : HasWDeriv Ω v u₂ w₂) : HasWDeriv Ω v (u₁ + u₂) (w₁ + w₂) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun φ hφ => ?_⟩
  have hc := @integrable_mul_of_locInt E _ _ _ _ _ Ω
  have hp : IsTest Ω (pd v φ) := hφ.pd v
  have i1 := hc h₁.1 (hp.1.continuous) hp.2.1 hp.2.2
  have i2 := hc h₂.1 (hp.1.continuous) hp.2.1 hp.2.2
  have i3 := hc h₁.2.1 (hφ.1.continuous) hφ.2.1 hφ.2.2
  have i4 := hc h₂.2.1 (hφ.1.continuous) hφ.2.1 hφ.2.2
  have := h₁.2.2 φ hφ
  have := h₂.2.2 φ hφ
  simp only [Pi.add_apply, add_mul]
  rw [integral_add i1 i2, integral_add i3 i4]
  linarith

theorem HasWDeriv.smul {Ω : Set E} {v : E} {u w : E → ℝ} (c : ℝ) (h : HasWDeriv Ω v u w) :
    HasWDeriv Ω v (fun x => c * u x) (fun x => c * w x) := by
  refine ⟨?_, ?_, fun φ hφ => ?_⟩
  · exact h.1.smul c
  · exact h.2.1.smul c
  · have := h.2.2 φ hφ
    simp only [mul_assoc]
    rw [integral_const_mul, integral_const_mul, this]; ring

theorem HasWDeriv.neg {Ω : Set E} {v : E} {u w : E → ℝ} (h : HasWDeriv Ω v u w) :
    HasWDeriv Ω v (fun x => -u x) (fun x => -w x) := by
  have := h.smul (-1)
  simpa using this

theorem HasWDeriv.sub {Ω : Set E} {v : E} {u₁ u₂ w₁ w₂ : E → ℝ} (h₁ : HasWDeriv Ω v u₁ w₁)
    (h₂ : HasWDeriv Ω v u₂ w₂) : HasWDeriv Ω v (u₁ - u₂) (w₁ - w₂) := by
  have := h₁.add h₂.neg
  have e1 : u₁ - u₂ = u₁ + fun x => -u₂ x := by funext x; simp [sub_eq_add_neg]
  have e2 : w₁ - w₂ = w₁ + fun x => -w₂ x := by funext x; simp [sub_eq_add_neg]
  rw [e1, e2]; exact this

/-- Uniqueness of weak derivatives (global). -/
theorem HasWDeriv.unique {v : E} {u w w' : E → ℝ} (h : HasWDeriv Set.univ v u w)
    (h' : HasWDeriv Set.univ v u w') : w =ᵐ[volume] w' := by
  have hw : LocallyIntegrable w volume := locallyIntegrableOn_univ.mp h.2.1
  have hw' : LocallyIntegrable w' volume := locallyIntegrableOn_univ.mp h'.2.1
  refine ae_eq_of_integral_contDiff_smul_eq hw hw' ?_
  intro g hg hc
  have t : IsTest Set.univ g := ⟨hg, hc, Set.subset_univ _⟩
  have e1 := h.2.2 g t
  have e2 := h'.2.2 g t
  simp only [smul_eq_mul]
  have : ∫ x, w x * g x = ∫ x, w' x * g x := by linarith
  simp only [mul_comm (g _)]
  exact this

theorem pd_mul {g φ : E → ℝ} (hg : Differentiable ℝ g) (hφ : Differentiable ℝ φ) (v : E) :
    pd v (fun x => g x * φ x) = fun x => g x * pd v φ x + pd v g x * φ x := by
  funext x
  unfold pd
  rw [fderiv_fun_mul (hg x) (hφ x)]
  simp [mul_comm]

theorem pd_pd_comm {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v v' : E) :
    pd v' (pd v φ) = pd v (pd v' φ) := by
  funext x
  have hd : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have h1 : ∀ (a b : E), pd b (pd a φ) x = fderiv ℝ (fderiv ℝ φ) x b a := by
    intro a b
    unfold pd
    have : HasFDerivAt (fun y => fderiv ℝ φ y a)
        ((ContinuousLinearMap.apply ℝ ℝ a).comp (fderiv ℝ (fderiv ℝ φ) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp x
        ((hd.differentiable (by simp)) x).hasFDerivAt
    rw [this.fderiv]; rfl
  rw [h1, h1]
  exact (ContDiffAt.isSymmSndFDerivAt (x := x) (hφ.contDiffAt) (by simp)) v' v

theorem hasWDeriv_of_contDiff {Ω : Set E} {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
    HasWDeriv Ω v f (pd v f) := by
  have hfd : Continuous (pd v f) := by
    have : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
    exact (this.clm_apply continuous_const)
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn _,
    hfd.locallyIntegrable.locallyIntegrableOn _, fun φ hφ => ?_⟩
  have hp := hφ.pd v
  have i1 : Integrable (fun x => pd v f x * φ x) volume :=
    integrable_mul_of_locInt (hfd.locallyIntegrable.locallyIntegrableOn Set.univ)
      hφ.1.continuous hφ.2.1 (Set.subset_univ _)
  have i2 : Integrable (fun x => f x * pd v φ x) volume :=
    integrable_mul_of_locInt (hf.continuous.locallyIntegrable.locallyIntegrableOn Set.univ)
      hp.1.continuous hp.2.1 (Set.subset_univ _)
  have i3 : Integrable (fun x => f x * φ x) volume :=
    integrable_mul_of_locInt (hf.continuous.locallyIntegrable.locallyIntegrableOn Set.univ)
      hφ.1.continuous hφ.2.1 (Set.subset_univ _)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v)
    (f := f) (g := φ) i1 i2 i3
    (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => (hφ.1.differentiable (by simp)) x)
  exact this

/-- Leibniz rule with a smooth factor. -/
theorem HasWDeriv.mul_smooth {Ω : Set E} (hΩ : IsOpen Ω) {v : E} {u w g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (h : HasWDeriv Ω v u w) :
    HasWDeriv Ω v (fun x => g x * u x) (fun x => g x * w x + pd v g x * u x) := by
  have hgc : Continuous g := hg.continuous
  have hgd : Continuous (pd v g) := by
    have : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
    exact (this.clm_apply continuous_const)
  have hu' : LocallyIntegrableOn (fun x => g x * u x) Ω volume :=
    h.1.continuousOn_mul hgc.continuousOn hΩ.isLocallyClosed
  have hw1 : LocallyIntegrableOn (fun x => g x * w x) Ω volume :=
    h.2.1.continuousOn_mul hgc.continuousOn hΩ.isLocallyClosed
  have hw2 : LocallyIntegrableOn (fun x => pd v g x * u x) Ω volume :=
    h.1.continuousOn_mul hgd.continuousOn hΩ.isLocallyClosed
  refine ⟨hu', hw1.add hw2, fun φ hφ => ?_⟩
  have hp := hφ.pd v
  have hψ := hφ.mul hg
  have e := h.2.2 _ hψ
  rw [pd_mul (hg.differentiable (by simp)) (hφ.1.differentiable (by simp))] at e
  have ia : Integrable (fun x => u x * (g x * pd v φ x)) volume :=
    integrable_mul_of_locInt h.1 (hgc.mul hp.1.continuous) hp.2.1.mul_left
      ((tsupport_mul_subset_right).trans hp.2.2)
  have ib : Integrable (fun x => u x * (pd v g x * φ x)) volume :=
    integrable_mul_of_locInt h.1 (hgd.mul hφ.1.continuous) hφ.2.1.mul_left
      ((tsupport_mul_subset_right).trans hφ.2.2)
  have ic : Integrable (fun x => w x * (g x * φ x)) volume :=
    integrable_mul_of_locInt h.2.1 hψ.1.continuous hψ.2.1 hψ.2.2
  have hsum : ∫ x, u x * (g x * pd v φ x + pd v g x * φ x) =
      (∫ x, u x * (g x * pd v φ x)) + ∫ x, u x * (pd v g x * φ x) := by
    simp only [mul_add]
    exact integral_add ia ib
  rw [hsum] at e
  have lhs : ∫ x, g x * u x * pd v φ x = ∫ x, u x * (g x * pd v φ x) := by
    congr 1; funext x; ring
  have rhs : ∫ x, (g x * w x + pd v g x * u x) * φ x =
      (∫ x, w x * (g x * φ x)) + ∫ x, u x * (pd v g x * φ x) := by
    rw [← integral_add ic ib]; congr 1; funext x; ring
  rw [lhs, rhs]
  linarith

/-- Symmetry of mixed weak derivatives. -/
theorem HasWDeriv.mixed {Ω : Set E} {v v' : E} {u w w' z : E → ℝ} (h : HasWDeriv Ω v u w)
    (h' : HasWDeriv Ω v' u w') (h₃ : HasWDeriv Ω v' w z) : HasWDeriv Ω v w' z := by
  refine ⟨h'.2.1, h₃.2.1, fun φ hφ => ?_⟩
  have a1 := h'.2.2 (pd v φ) (hφ.pd v)
  have a2 := h.2.2 (pd v' φ) (hφ.pd v')
  have a3 := h₃.2.2 φ hφ
  rw [pd_pd_comm hφ.1 v v'] at a1
  linarith

end CutoffRigidity.Riemann.Diff
