module

public import CutoffRigidity.ParallelGradientProductDifferential

/-! # The actual zero-level retraction does not increase tangent norms -/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M] [CompleteSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
  (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
  {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
  (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)

local notation "F₀" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))
local notation "J₀" => 𝓘(ℝ, F₀)
local notation "N₀" => {y : M // f y = 0}

/-- The actual zero-level retraction is genuinely `C¹`. -/
theorem contMDiff_unitParallelGradient_zeroProjection (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    let e := unitParallelGradientLevelHomeomorph hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
    ContMDiff I J₀ 1 (fun x ↦ (e.symm x).2) := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  exact (contMDiff_unitParallelGradientLevelHomeomorph_symm hX hpX hf hgrad x₀ hne).snd

/-- The actual retraction's differential has norm at most one, derived from
its actual inverse differential and the proved exact product norm identity. -/
theorem norm_mfderiv_unitParallelGradient_zeroProjection_le (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    let e := unitParallelGradientLevelHomeomorph hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
    ∀ (x : M) (w : TangentSpace I x),
      ‖(mfderiv I J₀ (fun z ↦ (e.symm z).2) x) w‖ ≤ ‖w‖ := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
  let e := unitParallelGradientLevelHomeomorph hX hpX
    (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
  dsimp only
  intro x w
  let p := e.symm x
  let B := mfderiv I (𝓘(ℝ, ℝ).prod J₀) e.symm x
  let D := mfderiv (𝓘(ℝ, ℝ).prod J₀) I e p
  have hinv := ((contMDiff_unitParallelGradientLevelHomeomorph_symm hX hpX hf hgrad x₀ hne) x).mdifferentiableAt one_ne_zero
  have hfor := ((contMDiff_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne) p).mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp x hfor hinv
  have hfun : e ∘ e.symm = id := funext e.apply_symm_apply
  have hid := mfderiv_congr (I := I) (I' := I) (x := x) hfun
  rw [mfderiv_id] at hid
  have hDB : @Eq (E →L[ℝ] E) (D.comp B) (ContinuousLinearMap.id ℝ E) := hchain.symm.trans hid
  have hvec := congrArg (fun L : E →L[ℝ] E ↦ L w) hDB
  change D (B w) = w at hvec
  have hnorm := norm_sq_mfderiv_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne
    p (B w).1 (B w).2
  change (@norm (TangentSpace I (e p))
      (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal (e p)).toNorm (D (B w))) ^ 2 =
    (B w).1 ^ 2 + (@norm (TangentSpace J₀ p.2)
      (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal p.2).toNorm (B w).2) ^ 2 at hnorm
  rw [hvec] at hnorm
  have htransport : @norm (TangentSpace I (e p))
      (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal (e p)).toNorm w = ‖w‖ :=
    congrArg (fun y : M ↦ @norm (TangentSpace I y)
      (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y).toNorm w) (e.apply_symm_apply x)
  rw [htransport] at hnorm
  have hproj : (mfderiv I J₀ (fun z ↦ (e.symm z).2) x) w = (B w).2 := by
    have hc := mfderiv_comp x (mdifferentiableAt_snd (I := 𝓘(ℝ, ℝ)) (I' := J₀)) hinv
    have hv := congrArg
      (fun L : TangentSpace I x →L[ℝ] TangentSpace J₀ p.2 ↦ L w) hc
    convert! hv using 1
    rw [mfderiv_snd]
    rfl
  rw [hproj]
  nlinarith [sq_nonneg (B w).1, norm_nonneg w]

/-- The genuine zero-level retraction fixes every actual zero-level point. -/
theorem unitParallelGradient_zeroProjection_inclusion (x₀ : M) (hne : X x₀ ≠ 0) (y : N₀) :
    ((unitParallelGradientLevelHomeomorph hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne).symm y.val).2 = y := by
  let e := unitParallelGradientLevelHomeomorph hX hpX
    (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
  have hzero : e (0, y) = y.val := completeBoundedFlow_zero
    (hX.const_smul_section (a := ‖X x₀‖⁻¹))
    (unitParallelField_enorm_le_one hX hpX x₀ hne) y.val
  have h := e.symm_apply_apply (0, y)
  rw [hzero] at h
  exact congrArg Prod.snd h

end CutoffRigidity
