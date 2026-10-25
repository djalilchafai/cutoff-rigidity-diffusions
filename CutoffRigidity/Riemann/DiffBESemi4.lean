module

public import CutoffRigidity.Riemann.DiffBESemi1
public import CutoffRigidity.Riemann.DiffBESemi2

/-! # Remainder estimates along the semigroup path (workstream BE, part C)

First-order remainders `h⁻¹ (K_{τ₁} g - K_{τ₀} g) + 𝓛 K_{τ₀} g` and their generators are `O(|h|)`
in sup norm, for smooth compactly supported `g`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Path

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} {Kk : ℝ≥0 → Kernel M M}

theorem smooth_semi (hK : KerCanonical F V μ Kk) {g : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) (r : ℝ≥0) : MSmooth F (semi Kk r g) :=
  (hK.smoothing g hg hgc r).1

theorem gen_semi (hK : KerCanonical F V μ Kk) {g : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) (r : ℝ≥0) :
    mgenerator F V (semi Kk r g) = semi Kk r (mgenerator F V g) :=
  (hK.smoothing g hg hgc r).2.1

theorem bdd_semi (hK : KerCanonical F V μ Kk) {g : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ≥0) (x : M), |semi Kk r g x| ≤ C ∧
      |mgenerator F V (semi Kk r g) x| ≤ C := by
  obtain ⟨C, hC⟩ := (hK.smoothing g hg hgc 0).2.2
  exact ⟨max C 0, le_max_right _ _, fun r x => ⟨(hC r x).1.trans (le_max_left _ _),
    (hC r x).2.trans (le_max_left _ _)⟩⟩

/-- Remainder estimates for the path `τ ↦ K_τ g`, in the direction used for `w_s = K_{t-s} f`. -/
theorem remainder_bounds (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {g : M → ℝ}
    (hg : MSmooth F g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ0 τ1 h : ℝ), 0 < τ0 → 0 < τ1 → h ≠ 0 → τ1 - τ0 = -h →
      (∀ y, |h⁻¹ * (semi Kk τ1.toNNReal g y - semi Kk τ0.toNNReal g y) -
          (-1 * mgenerator F V (semi Kk τ0.toNNReal g) y)| ≤ C * |h|) ∧
      (∀ y, |mgenerator F V (fun y => h⁻¹ * (semi Kk τ1.toNNReal g y - semi Kk τ0.toNNReal g y) -
          (-1 * mgenerator F V (semi Kk τ0.toNNReal g) y)) y| ≤ C * |h|) ∧
      (∀ y, |h⁻¹ * (semi Kk τ1.toNNReal g y - semi Kk τ0.toNNReal g y)| ≤ C) ∧
      (∀ y, |mgenerator F V (fun y => h⁻¹ *
          (semi Kk τ1.toNNReal g y - semi Kk τ0.toNNReal g y)) y| ≤ C) := by
  have hLg := msmooth_mgenerator F hV hg
  have hLgc := hasCompactSupport_mgenerator F V hg hgc
  obtain ⟨T, hT0, hT⟩ := semi_taylor F hK hV hg hgc
  obtain ⟨T', hT0', hT'⟩ := semi_taylor F hK hV hLg hLgc
  obtain ⟨C1, hC10, hC1⟩ := semi_lip F hK hV hg hgc
  obtain ⟨C2, hC20, hC2⟩ := semi_lip F hK hV hLg hLgc
  refine ⟨T + T' + C1 + C2, by positivity, fun τ0 τ1 h h0 h1 hh hτ => ?_⟩
  have hw0 := smooth_semi F hK hg hgc τ0.toNNReal
  have hw1 := smooth_semi F hK hg hgc τ1.toNNReal
  have hLw0 : MSmooth F (mgenerator F V (semi Kk τ0.toNNReal g)) := msmooth_mgenerator F hV hw0
  have hD : MSmooth F (fun y => -1 * mgenerator F V (semi Kk τ0.toNNReal g) y) :=
    contMDiff_const.mul hLw0
  have e0 := gen_semi F hK hg hgc τ0.toNNReal
  have e1 := gen_semi F hK hg hgc τ1.toNNReal
  have e00 := gen_semi F hK hLg hLgc τ0.toNNReal
  have hhpos : 0 < |h| := abs_pos.2 hh
  have habs : |τ1 - τ0| = |h| := by rw [hτ, abs_neg]
  have hτ' : τ1 = τ0 - h := by linarith
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · have h1 := hT y τ0 τ1 h0 h1
    rw [e0]
    have : h⁻¹ * (semi Kk τ1.toNNReal g y - semi Kk τ0.toNNReal g y) -
        (-1 * semi Kk τ0.toNNReal (mgenerator F V g) y) =
        h⁻¹ * (semi Kk τ1.toNNReal g y - semi Kk τ0.toNNReal g y -
          (τ1 - τ0) * semi Kk τ0.toNNReal (mgenerator F V g) y) := by
      rw [hτ]; field_simp
    rw [this, abs_mul, abs_inv]
    have h2 : |semi Kk τ1.toNNReal g y - semi Kk τ0.toNNReal g y -
          (τ1 - τ0) * semi Kk τ0.toNNReal (mgenerator F V g) y| ≤ T * |h| ^ 2 := by
      refine h1.trans ?_
      rw [hτ]; simp [sq_abs]
    calc |h|⁻¹ * _ ≤ |h|⁻¹ * (T * |h| ^ 2) := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hhpos.le)
      _ = T * |h| := by field_simp
      _ ≤ _ := by nlinarith [mul_nonneg hT0' hhpos.le, mul_nonneg hC10 hhpos.le,
            mul_nonneg hC20 hhpos.le]
  · rw [mgenerator_dq_sub F h hw1 hw0 hD y]
    rw [mgenerator_const_mul F (-1) hLw0 y, e0, e1, e00]
    have h1 := hT' y τ0 τ1 h0 h1
    have : h⁻¹ * (semi Kk τ1.toNNReal (mgenerator F V g) y - semi Kk τ0.toNNReal (mgenerator F V g) y) -
        -1 * semi Kk τ0.toNNReal (mgenerator F V (mgenerator F V g)) y =
        h⁻¹ * (semi Kk τ1.toNNReal (mgenerator F V g) y - semi Kk τ0.toNNReal (mgenerator F V g) y -
          (τ1 - τ0) * semi Kk τ0.toNNReal (mgenerator F V (mgenerator F V g)) y) := by
      rw [hτ]; field_simp
    rw [this, abs_mul, abs_inv]
    have h2 : |semi Kk τ1.toNNReal (mgenerator F V g) y - semi Kk τ0.toNNReal (mgenerator F V g) y -
          (τ1 - τ0) * semi Kk τ0.toNNReal (mgenerator F V (mgenerator F V g)) y| ≤ T' * |h| ^ 2 := by
      refine h1.trans ?_
      rw [hτ]; simp [sq_abs]
    calc |h|⁻¹ * _ ≤ |h|⁻¹ * (T' * |h| ^ 2) := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hhpos.le)
      _ = T' * |h| := by field_simp
      _ ≤ _ := by nlinarith [mul_nonneg hT0 hhpos.le, mul_nonneg hC10 hhpos.le,
            mul_nonneg hC20 hhpos.le]
  · have := hC1 y τ1 τ0
    rw [abs_mul, abs_inv]
    rw [habs] at this
    calc |h|⁻¹ * |semi Kk τ1.toNNReal g y - semi Kk τ0.toNNReal g y| ≤ |h|⁻¹ * (C1 * |h|) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hhpos.le)
      _ = C1 := by field_simp
      _ ≤ _ := by linarith
  · rw [mgenerator_dq F h hw1 hw0 y, e0, e1]
    have := hC2 y τ1 τ0
    rw [habs] at this
    rw [abs_mul, abs_inv]
    calc |h|⁻¹ * |semi Kk τ1.toNNReal (mgenerator F V g) y - semi Kk τ0.toNNReal (mgenerator F V g) y|
        ≤ |h|⁻¹ * (C2 * |h|) := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hhpos.le)
      _ = C2 := by field_simp
      _ ≤ _ := by linarith

/-- First-order expansion of `s ↦ K_s ζ`, uniformly in `x`. -/
theorem phi_remainder (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {g : M → ℝ}
    (hg : MSmooth F g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s h : ℝ), 0 < s → 0 < s + h → h ≠ 0 → ∀ y,
      |h⁻¹ * (semi Kk (s + h).toNNReal g y - semi Kk s.toNNReal g y) -
        mgenerator F V (semi Kk s.toNNReal g) y| ≤ C * |h| := by
  obtain ⟨T, hT0, hT⟩ := semi_taylor F hK hV hg hgc
  refine ⟨T, hT0, fun s h hs hsh hh y => ?_⟩
  have h1 := hT y s (s + h) hs hsh
  rw [gen_semi F hK hg hgc]
  have hhpos : 0 < |h| := abs_pos.2 hh
  have : h⁻¹ * (semi Kk (s + h).toNNReal g y - semi Kk s.toNNReal g y) -
      semi Kk s.toNNReal (mgenerator F V g) y =
      h⁻¹ * (semi Kk (s + h).toNNReal g y - semi Kk s.toNNReal g y -
        (s + h - s) * semi Kk s.toNNReal (mgenerator F V g) y) := by
    field_simp; ring
  rw [this, abs_mul, abs_inv]
  have h2 : |semi Kk (s + h).toNNReal g y - semi Kk s.toNNReal g y -
      (s + h - s) * semi Kk s.toNNReal (mgenerator F V g) y| ≤ T * |h| ^ 2 := by
    refine h1.trans ?_
    simp [sq_abs]
  calc |h|⁻¹ * _ ≤ |h|⁻¹ * (T * |h| ^ 2) := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hhpos.le)
    _ = T * |h| := by field_simp

end Path

end CutoffRigidity.Riemann.Diff
