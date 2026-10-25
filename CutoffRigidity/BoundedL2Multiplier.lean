module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Actual bounded coefficient multiplication as a continuous L² operator

A measurable scalar coefficient with a genuine finite bound defines a
bounded linear multiplier on scalar or vector L² equivalence classes.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X}

theorem memLp_boundedCoefficient_smul (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : X →₂[μ] F) :
    MemLp (fun x => a x • f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := C) (ha.smul (Lp.aestronglyMeasurable f))
  filter_upwards [hb] with x hx
  change ‖a x • f x‖ ≤ C * ‖f x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

@[expose] noncomputable def boundedCoefficientMulL2 (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : X →₂[μ] F) : X →₂[μ] F :=
  (memLp_boundedCoefficient_smul a ha C hb f).toLp (fun x => a x • f x)

theorem boundedCoefficientMulL2_coeFn (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : X →₂[μ] F) :
    boundedCoefficientMulL2 a ha C hb f =ᵐ[μ] fun x => a x • f x :=
  (memLp_boundedCoefficient_smul a ha C hb f).coeFn_toLp

@[expose] noncomputable def boundedCoefficientMulL2Linear (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) : (X →₂[μ] F) →ₗ[ℝ] (X →₂[μ] F) where
  toFun := boundedCoefficientMulL2 a ha C hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [boundedCoefficientMulL2_coeFn a ha C hb (f + g),
      boundedCoefficientMulL2_coeFn a ha C hb f, boundedCoefficientMulL2_coeFn a ha C hb g,
      Lp.coeFn_add f g, Lp.coeFn_add (boundedCoefficientMulL2 a ha C hb f) (boundedCoefficientMulL2 a ha C hb g)]
      with x hfg hf hg hsum hs
    rw [hfg, hs, Pi.add_apply, hf, hg, hsum, Pi.add_apply, smul_add]
  map_smul' r f := by
    change boundedCoefficientMulL2 a ha C hb (r • f) = r • boundedCoefficientMulL2 a ha C hb f
    apply Lp.ext
    filter_upwards [boundedCoefficientMulL2_coeFn a ha C hb (r • f),
      boundedCoefficientMulL2_coeFn a ha C hb f, Lp.coeFn_smul r f,
      Lp.coeFn_smul r (boundedCoefficientMulL2 a ha C hb f)] with x hrf hf hrs hs
    rw [hrf, hs, Pi.smul_apply, hf, hrs, Pi.smul_apply, smul_smul, smul_smul, mul_comm]

theorem norm_boundedCoefficientMulL2_le (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : X →₂[μ] F) :
    ‖boundedCoefficientMulL2 a ha C hb f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedCoefficientMulL2_coeFn a ha C hb f, hb] with x hx hb
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- The actual bounded continuous linear multiplication operator. -/
@[expose] noncomputable def boundedL2Multiplier (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    (X →₂[μ] F) →L[ℝ] (X →₂[μ] F) :=
  (boundedCoefficientMulL2Linear a ha C hb).mkContinuous C (norm_boundedCoefficientMulL2_le a ha C hb)

theorem boundedL2Multiplier_coeFn (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : X →₂[μ] F) :
    boundedL2Multiplier a ha C hC hb f =ᵐ[μ] fun x => a x • f x :=
  boundedCoefficientMulL2_coeFn a ha C hb f

theorem boundedL2Multiplier_norm_le (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    ‖boundedL2Multiplier (F := F) a ha C hC hb‖ ≤ C := by
  apply (boundedL2Multiplier (F := F) a ha C hC hb).opNorm_le_bound hC
  intro f
  change ‖boundedCoefficientMulL2 a ha C hb f‖ ≤ C * ‖f‖
  exact norm_boundedCoefficientMulL2_le a ha C hb f

end CutoffRigidity
