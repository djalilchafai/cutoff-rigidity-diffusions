module

public import CutoffRigidity.Paper.SpectralBridge
public import CutoffRigidity.Paper.SeqData
public import CutoffRigidity.Paper.BrownianLinear
public import CutoffRigidity.EigenfunctionC2Rigidity
public import CutoffRigidity.AffineEigenfunctionOrthogonality
public import CutoffRigidity.AffineEigenspace

/-! # Lemma 3.3: the projection on an orthonormal eigenbasis is an Ornstein–Uhlenbeck process -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

/-- **Lemma 3.3** (projection on an orthonormal multi-eigenfunction is an OU process). -/
theorem eigenmap_is_ou_carrier {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin V B P X) (hV : CutCur.RigidCurvature V)
    (T : Fin (CutCur.firstEigenDim V) → CutCur.Rd d → ℝ) (hT : CutCur.IsEigenbasis V T) :
    let ρ := CutCur.spectralGap V
    let Tv := fun x => (WithLp.toLp 2 fun i => T i x : CutCur.Rd (CutCur.firstEigenDim V))
    ∃ β : ℝ≥0 → Ω → CutCur.Rd (CutCur.firstEigenDim V), CutCur.IsStdBrownian β P ∧
      ∀ x₀, ∀ᵐ w ∂P, ∀ t : ℝ≥0,
        Tv (X x₀ t w) = Tv x₀ - ρ • (∫ s in (0 : ℝ)..(t : ℝ), Tv (X x₀ s.toNNReal w)) +
          Real.sqrt (2 * ρ) • β t w := by
  intro ρ Tv
  have hV2 := hL.1
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := gibbs_probability hL.2.1
  have hρ : 0 < ρ := hV.1
  have hHess := hV.2
  -- affine representation of each eigenfunction
  have hTe : ∀ i, ContDiff ℝ 2 (T i) ∧ MemLp (T i) 2 (gibbsMeasure volume V) ∧
      ∀ x, langevinDifferentialOperator V (T i) x = -ρ * T i x :=
    fun i => isEigenfunction_iff.mp (hT.1 i)
  set a : Fin (CutCur.firstEigenDim V) → CutCur.Rd d := fun i => gradient (T i) 0 with ha
  set b : Fin (CutCur.firstEigenDim V) → ℝ := fun i => T i 0 with hb
  have haff : ∀ i x, T i x = b i + inner ℝ (a i) x := fun i x =>
    c2_L2_eigenfunction_is_affine hV2 (hTe i).1 (hTe i).2.1 ρ hρ.le hHess (hTe i).2.2 x
  have hTeq : ∀ i, T i = fun y => inner ℝ (a i) y + b i := fun i =>
    funext fun y => by rw [haff i y, add_comm]
  have heig' : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i) := fun i x => by
    rw [← hTeq i, (hTe i).2.2 x, hTeq i]
  have hrows : ∀ i, a i ∈ affineEigenRows V ρ ∧ b i = affineEigenConstant V ρ (a i) := fun i =>
    (affineEigenRows_iff_eigenfunction V hρ (a i) (b i)).mp (heig' i)
  have hgram := affine_eigenfunction_row_gram V (hV2.differentiable (by norm_num)) a b ρ hρ heig'
    hp' (fun i j => by
      have := hT.2 i j
      rw [hTeq i, hTeq j] at this
      exact this)
  let a' : Fin (CutCur.firstEigenDim V) → Fin d → ℝ := fun j i => (Real.sqrt ρ)⁻¹ * (a j) i
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ.le
  have ha' : ∀ j l, ∑ i, a' j i * a' l i = if j = l then 1 else 0 := by
    intro j l
    have h := hgram j l
    rw [PiLp.inner_apply] at h
    have h' : ∑ i, (a j) i * (a l) i = if j = l then ρ else 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
    have hr : ∑ i, a' j i * a' l i = ρ⁻¹ * ∑ i, (a j) i * (a l) i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [a']
      have : (Real.sqrt ρ)⁻¹ * (Real.sqrt ρ)⁻¹ = ρ⁻¹ := by
        rw [← mul_inv, hsq]
      calc (Real.sqrt ρ)⁻¹ * (a j) i * ((Real.sqrt ρ)⁻¹ * (a l) i)
          = ((Real.sqrt ρ)⁻¹ * (Real.sqrt ρ)⁻¹) * ((a j) i * (a l) i) := by ring
        _ = _ := by rw [this]
    rw [hr, h']
    split_ifs
    · field_simp
    · simp
  refine ⟨fun t w => (WithLp.toLp 2 fun j => ∑ i, a' j i * B t w i : CutCur.Rd (CutCur.firstEigenDim V)),
    isStdBrownian_orthonormal_image hL.2.2.1 a' ha', fun x₀ => ?_⟩
  filter_upwards [hL.2.2.2 x₀] with w hw t
  obtain ⟨hcont, heq⟩ := hw
  have hXc : Continuous (fun s : ℝ => X x₀ s.toNNReal w) := hcont.comp continuous_real_toNNReal
  have hgc : Continuous (gradient V) := continuous_gradient_of_c1 (hV2.of_le (by norm_num))
  have hint : IntervalIntegrable (fun s : ℝ => gradient V (X x₀ s.toNNReal w))
      MeasureTheory.volume 0 (t : ℝ) :=
    (hgc.comp hXc).intervalIntegrable _ _
  ext j
  -- pointwise drift identity
  have hdrift : ∀ y : CutCur.Rd d, inner ℝ (a j) (gradient V y) = ρ * T j y := by
    intro y
    have h1 := (hrows j).1 y
    have h2 : b j = inner ℝ (a j) (gradient V 0) / ρ := (hrows j).2
    rw [inner_sub_right] at h1
    rw [haff j y, h2]
    field_simp
    linarith
  have h3 : inner ℝ (a j) (X x₀ t w) = inner ℝ (a j) x₀ -
      ρ * (∫ s in (0 : ℝ)..(t : ℝ), T j (X x₀ s.toNNReal w)) +
        Real.sqrt 2 * inner ℝ (a j) (B t w) := by
    rw [heq t, inner_add_right, inner_sub_right, inner_smul_right]
    have := (innerSL ℝ (a j)).intervalIntegral_comp_comm hint
    simp only [innerSL_apply_apply] at this
    rw [← this]
    simp only [hdrift]
    rw [intervalIntegral.integral_const_mul]
  have hTint : IntervalIntegrable (fun s : ℝ => Tv (X x₀ s.toNNReal w)) MeasureTheory.volume 0 (t : ℝ) := by
    refine Continuous.intervalIntegrable ?_ _ _
    show Continuous (fun s : ℝ => (WithLp.toLp 2 fun i => T i (X x₀ s.toNNReal w) :
      CutCur.Rd (CutCur.firstEigenDim V)))
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (hTe i).1.continuous.comp hXc)
  have h4 : (∫ s in (0 : ℝ)..(t : ℝ), Tv (X x₀ s.toNNReal w)) j =
      ∫ s in (0 : ℝ)..(t : ℝ), T j (X x₀ s.toNNReal w) := by
    have := (EuclideanSpace.proj (𝕜 := ℝ) j).intervalIntegral_comp_comm hTint
    simpa using this.symm
  show T j (X x₀ t w) = T j x₀ - ρ * (∫ s in (0 : ℝ)..(t : ℝ), Tv (X x₀ s.toNNReal w)) j +
    Real.sqrt (2 * ρ) * ∑ i, a' j i * B t w i
  rw [h4, haff j (X x₀ t w), haff j x₀, h3]
  have h5 : ∑ i, a' j i * B t w i = (Real.sqrt ρ)⁻¹ * inner ℝ (a j) (B t w) := by
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [a']
    simp [mul_comm, mul_left_comm]
  rw [h5, Real.sqrt_mul (by norm_num) ρ]
  have hs : Real.sqrt ρ ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  field_simp
  ring

end CutoffRigidity.Paper
