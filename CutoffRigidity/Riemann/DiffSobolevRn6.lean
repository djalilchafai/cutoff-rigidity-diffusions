module

public import CutoffRigidity.Riemann.DiffSobolevRn5

/-! # Difference quotients

`dq v h f x = (f (x + h v) - f x) / h`: `L²` bounds, discrete integration by parts, Leibniz
rule, commutation with weak derivatives.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Difference quotient in direction `v` with step `h`. -/
noncomputable def dq (v : E) (h : ℝ) (f : E → ℝ) : E → ℝ := fun x => (f (x + h • v) - f x) / h

theorem memLp_comp_add {f : E → ℝ} (hf : MemLp f 2 volume) (c : E) :
    MemLp (fun x => f (x + c)) 2 volume :=
  hf.comp_measurePreserving (measurePreserving_add_right volume c)

theorem memLp_dq {v : E} {h : ℝ} {f : E → ℝ} (hf : MemLp f 2 volume) :
    MemLp (dq v h f) 2 volume := by
  have := MemLp.const_mul (MemLp.sub (memLp_comp_add hf (h • v)) hf) h⁻¹
  refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
  simp [dq, div_eq_inv_mul]

theorem dq_mul {v : E} {h : ℝ} (hh : h ≠ 0) (a f : E → ℝ) (x : E) :
    dq v h (fun x => a x * f x) x = a (x + h • v) * dq v h f x + dq v h a x * f x := by
  unfold dq
  field_simp
  ring

theorem dq_add {v : E} {h : ℝ} (f g : E → ℝ) : dq v h (f + g) = dq v h f + dq v h g := by
  funext x; unfold dq; simp only [Pi.add_apply]; ring

theorem dq_sub {v : E} {h : ℝ} (f g : E → ℝ) : dq v h (f - g) = dq v h f - dq v h g := by
  funext x; unfold dq; simp only [Pi.sub_apply]; ring

theorem dq_const_mul {v : E} {h : ℝ} (c : ℝ) (f : E → ℝ) :
    dq v h (fun x => c * f x) = fun x => c * dq v h f x := by
  funext x; unfold dq; ring

/-- Discrete integration by parts. -/
theorem integral_mul_dq_neg {v : E} {h : ℝ} (hh : h ≠ 0) {f g : E → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    ∫ x, f x * dq v (-h) g x = -∫ x, dq v h f x * g x := by
  have i1 : Integrable (fun x => f x * g x) volume := hf.integrable_mul hg
  have i2 : Integrable (fun x => f x * g (x + (-h) • v)) volume :=
    hf.integrable_mul (memLp_comp_add hg _)
  have i3 : Integrable (fun x => f (x + h • v) * g x) volume :=
    (memLp_comp_add hf _).integrable_mul hg
  have i4 : Integrable (fun x => f x * g x) volume := i1
  have e : ∫ x, f x * g (x + (-h) • v) = ∫ x, f (x + h • v) * g x := by
    have := integral_add_right_eq_self (μ := volume) (fun x => f x * g (x + (-h) • v)) (h • v)
    rw [← this]
    congr 1; funext x
    simp
  have lhs : ∫ x, f x * dq v (-h) g x = ((∫ x, f x * g (x + (-h) • v)) - ∫ x, f x * g x) / (-h) := by
    rw [← integral_sub i2 i1, ← integral_div]
    congr 1; funext x; unfold dq; ring
  have rhs : ∫ x, dq v h f x * g x = ((∫ x, f (x + h • v) * g x) - ∫ x, f x * g x) / h := by
    rw [← integral_sub i3 i1, ← integral_div]
    congr 1; funext x; unfold dq; ring
  rw [lhs, rhs, e]
  field_simp

theorem dq_eq_mul {v : E} {h : ℝ} (f : E → ℝ) :
    dq v h f = fun x => h⁻¹ * (f (x + h • v) - f x) := by
  funext x; simp [dq, div_eq_inv_mul]

theorem isTest_dq {φ : E → ℝ} (hφ : IsTest Set.univ φ) (v : E) (h : ℝ) :
    IsTest Set.univ (dq v h φ) := by
  rw [dq_eq_mul]
  have h1 : ContDiff ℝ ∞ (fun x => φ (x + h • v)) :=
    hφ.1.comp (contDiff_id.add contDiff_const)
  have h2 : HasCompactSupport (fun x => φ (x + h • v)) :=
    hφ.2.1.comp_homeomorph (Homeomorph.addRight (h • v))
  refine ⟨contDiff_const.mul (h1.sub hφ.1), ?_, Set.subset_univ _⟩
  exact (h2.sub hφ.2.1).mul_left

theorem pd_dq {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v e : E) (h : ℝ) :
    pd v (dq e h φ) = dq e h (pd v φ) := by
  funext x
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have h1 : DifferentiableAt ℝ (fun x => φ (x + h • e)) x :=
    (hd (x + h • e)).comp x (differentiableAt_id.add_const _)
  unfold pd
  have e2 := ((h1.hasFDerivAt.sub (hd x).hasFDerivAt).const_mul h⁻¹)
  have e3 : fderiv ℝ (fun x => h⁻¹ * (φ (x + h • e) - φ x)) x =
      h⁻¹ • (fderiv ℝ (fun x => φ (x + h • e)) x - fderiv ℝ φ x) := e2.fderiv
  rw [dq_eq_mul, e3, fderiv_comp_add_right]
  simp [dq, div_eq_inv_mul, mul_sub]

/-- Difference quotients commute with weak derivatives. -/
theorem hasWDeriv_dq {v e : E} {h : ℝ} (hh : h ≠ 0) {u w : E → ℝ} (hu : MemLp u 2 volume)
    (hw : MemLp w 2 volume) (H : HasWDeriv Set.univ v u w) :
    HasWDeriv Set.univ v (dq e h u) (dq e h w) := by
  refine ⟨(memLp_dq hu).locallyIntegrable (by norm_num) |>.locallyIntegrableOn _,
    (memLp_dq hw).locallyIntegrable (by norm_num) |>.locallyIntegrableOn _, fun φ hφ => ?_⟩
  have hp : IsTest Set.univ (pd v φ) := hφ.pd v
  have hψ : IsTest Set.univ (dq e (-h) φ) := isTest_dq hφ e (-h)
  have mem : ∀ {ψ : E → ℝ}, IsTest Set.univ ψ → MemLp ψ 2 volume := fun hψ =>
    hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have a1 := integral_mul_dq_neg (v := e) hh hu (mem hp)
  have a2 := integral_mul_dq_neg (v := e) hh hw (mem hφ)
  have a3 := H.2.2 _ hψ
  rw [pd_dq hφ.1] at a3
  -- a1 : ∫ u * dq (-h) (pd v φ) = -∫ dq h u * pd v φ
  have e1 : ∫ x, dq e h u x * pd v φ x = -∫ x, u x * dq e (-h) (pd v φ) x := by linarith
  rw [e1]
  have a4 : pd v (dq e (-h) φ) = dq e (-h) (pd v φ) := pd_dq hφ.1 v e (-h)
  have := H.2.2 _ hψ
  rw [a4] at this
  rw [this]
  linarith

end CutoffRigidity.Riemann.Diff
