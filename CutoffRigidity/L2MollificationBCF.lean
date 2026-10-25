module

public import CutoffRigidity.EuclideanMollificationStrongLimit
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Actual smooth mollification as a bounded map into bounded functions

The L² convolution estimate supplies a genuine continuous linear map into
the supremum norm. Consequently strong L² time derivatives can be passed
through spatial smoothing as actual uniform time derivatives.
-/

public section

namespace CutoffRigidity

open MeasureTheory ContinuousLinearMap
open scoped Topology Convolution BoundedContinuousFunction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The genuine smooth convolution represented as a bounded continuous function. -/
@[expose] noncomputable def bumpMollificationBCF (φ : ContDiffBump (0 : E))
    (f : E →₂[volume] ℝ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (bumpMollification φ f)
    (bumpMollification_contDiff φ ((Lp.memLp f).locallyIntegrable (by norm_num))).continuous
    ((‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ *
      ‖(bumpKernel_memLp φ).toLp (φ.normed volume)‖) * ‖f‖)
    (fun x => by
      have hh := bumpMollification_sup_bound φ (Lp.memLp f) x
      simpa only [Lp.toLp_coeFn, Real.norm_eq_abs] using hh)

/-- The actual supremum bound for smooth convolution of an L² class. -/
theorem norm_bumpMollificationBCF_le (φ : ContDiffBump (0 : E)) (f : E →₂[volume] ℝ) :
    ‖bumpMollificationBCF φ f‖ ≤
      (‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ *
        ‖(bumpKernel_memLp φ).toLp (φ.normed volume)‖) * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖bumpMollification φ f x‖ ≤ _
  have hh := bumpMollification_sup_bound φ (Lp.memLp f) x
  simpa only [Lp.toLp_coeFn, Real.norm_eq_abs] using hh

/-- Mollification depends only on the genuine almost-everywhere input. -/
theorem bumpMollification_congr_ae (φ : ContDiffBump (0 : E)) {f g : E → ℝ}
    (hfg : f =ᵐ[volume] g) : bumpMollification φ f = bumpMollification φ g :=
  convolution_congr (lsmul ℝ ℝ) Filter.EventuallyEq.rfl hfg

/-- The linear map is defined on actual L² classes, rather than raw functions. -/
@[expose] noncomputable def bumpMollificationBCFLinear (φ : ContDiffBump (0 : E)) :
    (E →₂[volume] ℝ) →ₗ[ℝ] (E →ᵇ ℝ) where
  toFun := bumpMollificationBCF φ
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    change bumpMollification φ (fun y => (f + g : E →₂[volume] ℝ) y) x = bumpMollification φ f x + bumpMollification φ g x
    rw [bumpMollification_congr_ae φ (Lp.coeFn_add f g)]
    have hf := ConvolutionExists.of_memLp_memLp (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
      (bumpKernel_memLp φ) (Lp.memLp f)
    have hg := ConvolutionExists.of_memLp_memLp (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
      (bumpKernel_memLp φ) (Lp.memLp g)
    change (∫ y, (φ.normed volume y) * (f (x - y) + g (x - y))) = _
    simp_rw [mul_add]
    exact integral_add (hf x) (hg x)
  map_smul' r f := by
    apply BoundedContinuousFunction.ext
    intro x
    change bumpMollification φ (fun y => (r • f : E →₂[volume] ℝ) y) x = r * bumpMollification φ f x
    rw [bumpMollification_congr_ae φ (Lp.coeFn_smul r f)]
    have hh := convolution_smul (L := (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ))
      (μ := (volume : Measure E)) (f := φ.normed volume) (g := fun y => f y) (y := r)
    exact congrFun hh x

/-- Genuine continuous linear smoothing from L² into the supremum norm. -/
@[expose] noncomputable def bumpMollificationBCFCLM (φ : ContDiffBump (0 : E)) :
    (E →₂[volume] ℝ) →L[ℝ] (E →ᵇ ℝ) :=
  (bumpMollificationBCFLinear φ).mkContinuous
    (‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ * ‖(bumpKernel_memLp φ).toLp (φ.normed volume)‖)
    (norm_bumpMollificationBCF_le φ)

/-- True strong L² derivatives become genuine uniform derivatives after smoothing. -/
theorem hasDerivAt_bumpMollificationBCFCLM (φ : ContDiffBump (0 : E))
    {u : ℝ → E →₂[volume] ℝ} {v : E →₂[volume] ℝ} {t : ℝ}
    (hu : HasDerivAt u v t) :
    HasDerivAt (fun s => bumpMollificationBCFCLM φ (u s)) (bumpMollificationBCFCLM φ v) t :=
  (bumpMollificationBCFCLM φ).hasFDerivAt.comp_hasDerivAt t hu

end CutoffRigidity
