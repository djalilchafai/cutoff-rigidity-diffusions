module

public import CutoffRigidity.Statements
public import CutoffRigidity.Paper.ProductCondition
public import CutoffRigidity.Extra.Normalization

/-! # Brownian scaling and the SDE-level "Normalization" (manuscript, Section 4.2)

If `X` solves `dX = -∇V dt + √2 dB`, then `X_{c·}` solves `dX = -c ∇V dt + √(2c) dB'` where
`B'_t = B_{ct}/√c` is again a standard Brownian motion.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem isLangevinSolution_iff_sde {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {x₀ : CutCur.Rd d} {X : ℝ≥0 → Ω → CutCur.Rd d} :
    CutCur.IsLangevinSolution V B P x₀ X ↔ CutCur.IsSDESolution V 1 (Real.sqrt 2) B P x₀ X := by
  simp [CutCur.IsLangevinSolution, CutCur.IsSDESolution]

/-- Brownian scaling: `B'_t = B_{ct}/√c` is again a standard Brownian motion. -/
theorem isStdBrownian_scale {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    (hB : CutCur.IsStdBrownian B P) {c : ℝ≥0} (hc : c ≠ 0) :
    CutCur.IsStdBrownian (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P := by
  refine ⟨fun i => ?_, ?_⟩
  · have := (hB.1 i).smul hc
    simpa using this
  · have h := hB.2.comp
      (fun (i : Fin d) (path : ℝ≥0 → ℝ) => fun t : ℝ≥0 => (√(c:ℝ))⁻¹ * path (c * t))
      (fun i => by fun_prop)
    simpa [Function.comp_def] using h

/-- Time change `X^{(c)}_t = X_{ct}` solves `dX = -c a ∇V dt + √c s dB'`, `B'_t = B_{ct}/√c`. -/
theorem isSDESolution_timeChange {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {x₀ : CutCur.Rd d} {X : ℝ≥0 → Ω → CutCur.Rd d} {a s : ℝ}
    (h : CutCur.IsSDESolution V a s B P x₀ X) {c : ℝ≥0} (hc : c ≠ 0) :
    CutCur.IsSDESolution V (c * a) (Real.sqrt c * s) (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P x₀
      (fun t w => X (c * t) w) := by
  filter_upwards [h] with w ⟨hcont, hX⟩
  refine ⟨hcont.comp (by fun_prop), fun t => ?_⟩
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hsq : Real.sqrt c ≠ 0 := by positivity
  rw [hX (c * t)]
  have hint : ∫ r in (0 : ℝ)..((c * t : ℝ≥0) : ℝ), gradient V (X r.toNNReal w) =
      (c : ℝ) • ∫ r in (0 : ℝ)..(t : ℝ), gradient V (X (c * r.toNNReal) w) := by
    have := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (t : ℝ))
      (fun r : ℝ => gradient V (X r.toNNReal w)) hc'
    simp only [mul_zero] at this
    rw [NNReal.coe_mul]
    have h2 : ∫ r in (0 : ℝ)..(t : ℝ), gradient V (X (c * r.toNNReal) w) =
        ∫ r in (0 : ℝ)..(t : ℝ), gradient V (X (((c : ℝ) * r).toNNReal) w) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Real.toNNReal_mul (NNReal.coe_nonneg c), Real.toNNReal_coe]
    rw [h2, this, smul_smul, mul_inv_cancel₀ hc', one_smul]
  rw [hint]
  simp only [smul_smul]
  rw [mul_assoc]
  congr 2
  · rw [mul_comm]
  · field_simp

theorem isSDESolution_congr {V V' : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {x₀ : CutCur.Rd d} {X : ℝ≥0 → Ω → CutCur.Rd d} {a a' s s' : ℝ}
    (h : CutCur.IsSDESolution V a s B P x₀ X)
    (hg : ∀ x, a • gradient V x = a' • gradient V' x) (hs : s = s') :
    CutCur.IsSDESolution V' a' s' B P x₀ X := by
  subst hs
  filter_upwards [h] with w ⟨hc, hX⟩
  refine ⟨hc, fun t => ?_⟩
  rw [hX t, ← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
  simp only [hg]

/-- **Normalization, SDE level** (manuscript, Section "Normalization"): if `X x₀` solves
`dX = -∇V dt + √2 dB`, then for `c > 0` the time-changed `X x₀ (c ·)` solves
`dX = -c ∇V dt + √(2c) dB'` driven by the rescaled Brownian motion `B'_t = B_{ct}/√c`, which is
again a standard Brownian motion. -/
theorem normalization_sde {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X) {c : ℝ}
    (hc : 0 < c) :
    CutCur.IsStdBrownian (fun t w => (Real.sqrt c)⁻¹ • B (c.toNNReal * t) w) P ∧
    ∀ x₀, CutCur.IsSDESolution V c (Real.sqrt (2 * c))
      (fun t w => (Real.sqrt c)⁻¹ • B (c.toNNReal * t) w) P x₀
      (fun t w => X x₀ (c.toNNReal * t) w) := by
  have hc0 : c.toNNReal ≠ 0 := by simpa using hc
  have hcR : ((c.toNNReal : ℝ≥0) : ℝ) = c := Real.coe_toNNReal _ hc.le
  refine ⟨?_, fun x₀ => ?_⟩
  · simpa [hcR] using isStdBrownian_scale hL.2.2.1 hc0
  · have h := isSDESolution_timeChange (isLangevinSolution_iff_sde.mp (hL.2.2.2 x₀)) hc0
    simp only [hcR] at h
    have e : Real.sqrt (2 * c) = Real.sqrt c * Real.sqrt 2 := by
      rw [mul_comm, Real.sqrt_mul hc.le]
    rw [e]
    simpa using h

end CutoffRigidity.Paper
