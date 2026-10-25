module

public import CutoffRigidity.GradientLevelOrthogonality

/-! # Actual differential of the constructed parallel-gradient product -/

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

/-- The actual product derivative is the sum of its original unit-gradient
time direction and its actual level tangent direction. -/
theorem mfderiv_unitParallelGradientLevelHomeomorph (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    let e := unitParallelGradientLevelHomeomorph hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
    ∀ (p : ℝ × N₀) (r : ℝ) (v : TangentSpace J₀ p.2),
      (mfderiv (𝓘(ℝ, ℝ).prod J₀) I e p) (r, v) =
        r • ((‖X x₀‖⁻¹ • X) (e p)) +
          (mfderiv J₀ I (fun y ↦ e (p.1, y)) p.2) v := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
  let e := unitParallelGradientLevelHomeomorph hX hpX
    (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
  dsimp only
  intro p r v
  have hY := hX.const_smul_section (a := ‖X x₀‖⁻¹)
  have hb := unitParallelField_enorm_le_one hX hpX x₀ hne
  have hc : MDifferentiableAt (𝓘(ℝ, ℝ).prod J₀) I e p :=
    ((contMDiff_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne) p).mdifferentiableAt one_ne_zero
  have htime : mfderiv 𝓘(ℝ, ℝ) I (fun s ↦ e (s, p.2)) p.1 =
      (1 : ℝ →L[ℝ] ℝ).smulRight ((‖X x₀‖⁻¹ • X) (e p)) := by
    have hi := completeBoundedFlow_isMIntegralCurve hY hb p.2.val p.1
    convert! hi.mfderiv using 1
  have hprod := mfderiv_prod_eq_add_comp hc
  have hval := congrArg
    (fun L : TangentSpace (𝓘(ℝ, ℝ).prod J₀) p →L[ℝ] TangentSpace I (e p) ↦ L (r, v)) hprod
  rw [htime] at hval
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, id_eq] at hval
  convert! hval using 1

/-- The actual level tangent part preserves the constructed level norm,
by the proved actual parallel-flow isometry and actual induced inclusion metric. -/
theorem norm_mfderiv_unitParallelGradientLevelHomeomorph_level (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    let e := unitParallelGradientLevelHomeomorph hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
    ∀ (s : ℝ) (y : N₀) (v : TangentSpace J₀ y),
      ‖(mfderiv J₀ I (fun z ↦ e (s, z)) y) v‖ = ‖v‖ := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
  let e := unitParallelGradientLevelHomeomorph hX hpX
    (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
  dsimp only
  intro s y v
  have hY := hX.const_smul_section (a := ‖X x₀‖⁻¹)
  have hb := unitParallelField_enorm_le_one hX hpX x₀ hne
  have hpY (x : M) : CovariantDerivative.leviCivitaConnection I M (‖X x₀‖⁻¹ • X) x = 0 := by
    have hh := (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOn.smul_const
      (‖X x₀‖⁻¹) ((hX.mdifferentiable one_ne_zero) x)
    simpa only [hpX x, smul_zero] using hh
  have hflow := ((contMDiff_completeBoundedFlow_timeSlice hY hb s) y.val).mdifferentiableAt one_ne_zero
  have hinc := ((contMDiff_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne) y).mdifferentiableAt
    (by norm_num)
  have hsp : mfderiv J₀ I (fun z ↦ e (s, z)) y =
      (mfderiv I I (fun z ↦ completeBoundedFlow hY hb z s) y.val).comp
        (mfderiv J₀ I (Subtype.val : N₀ → M) y) := by
    convert! mfderiv_comp y hflow hinc using 1
  have hn := (norm_mfderiv_completeBoundedFlow_eq_of_parallel hY hb hpY y.val
    ((mfderiv J₀ I (Subtype.val : N₀ → M) y) v) s).trans
    (norm_mfderiv_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne y v)
  convert! hn using 1
  exact congrArg norm (congrArg (fun L : TangentSpace J₀ y →L[ℝ] TangentSpace I (e (s, y)) ↦ L v) hsp)

/-- The actual gradient direction is orthogonal to the actual level tangent
part, by differentiating the original exact scalar-coordinate formula. -/
theorem inner_unitParallelGradientLevelHomeomorph_level_eq_zero (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    let e := unitParallelGradientLevelHomeomorph hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
    ∀ (s : ℝ) (y : N₀) (v : TangentSpace J₀ y),
      inner ℝ ((‖X x₀‖⁻¹ • X) (e (s, y)))
        ((mfderiv J₀ I (fun z ↦ e (s, z)) y) v) = 0 := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
  let e := unitParallelGradientLevelHomeomorph hX hpX
    (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
  dsimp only
  intro s y v
  have hsp := (contMDiff_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne).comp
    ((contMDiff_const (c := s)).prodMk contMDiff_id)
  have hsp' : MDifferentiableAt J₀ I (fun z ↦ e (s, z)) y :=
    (hsp y).mdifferentiableAt one_ne_zero
  have hconst : f ∘ (fun z : N₀ ↦ e (s, z)) = fun _ ↦ ‖X x₀‖ * s := by
    funext z
    exact unitParallelGradientLevelHomeomorph_scalar hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne (s, z)
  have hz := inner_gradient_mfderiv_eq_zero_of_constant (I := I) (J := J₀)
    (g := fun z : N₀ ↦ e (s, z)) (z := y)
    ((hf (e (s, y))).mdifferentiableAt (by norm_num)) hsp' X (hgrad (e (s, y))) hconst v
  change inner ℝ ((‖X x₀‖⁻¹ • X) (e (s, y)))
    ((mfderiv J₀ I (fun z ↦ e (s, z)) y) v) = 0
  simp only [Pi.smul_apply, inner_smul_left]
  rw [hz, mul_zero]


include hX hpX in
/-- The original normalized parallel field has norm exactly one everywhere. -/
theorem norm_unitParallelField_eq_one (x₀ : M) (hne : X x₀ ≠ 0) (x : M) :
    ‖(‖X x₀‖⁻¹ • X) x‖ = 1 := by
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  rw [norm_parallel_eq_of_preconnected hX hpX x x₀,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

/-- The actual constructed diffeomorphism preserves the exact product
Riemannian quadratic form: the real direction and the actual induced level
metric have no cross term. No product metric identity is assumed. -/
theorem norm_sq_mfderiv_unitParallelGradientLevelHomeomorph (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    let e := unitParallelGradientLevelHomeomorph hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
    ∀ (p : ℝ × N₀) (r : ℝ) (v : TangentSpace J₀ p.2),
      ‖(mfderiv (𝓘(ℝ, ℝ).prod J₀) I e p) (r, v)‖ ^ 2 = r ^ 2 + ‖v‖ ^ 2 := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
  let e := unitParallelGradientLevelHomeomorph hX hpX
    (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
  dsimp only
  intro p r v
  have hd := mfderiv_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne p r v
  have horth := inner_unitParallelGradientLevelHomeomorph_level_eq_zero hX hpX hf hgrad x₀ hne p.1 p.2 v
  have hunit := norm_unitParallelField_eq_one hX hpX x₀ hne (e p)
  have hspace := norm_mfderiv_unitParallelGradientLevelHomeomorph_level hX hpX hf hgrad x₀ hne p.1 p.2 v
  rw [hd, norm_add_sq_real]
  simp only [inner_smul_left, horth, mul_zero, add_zero]
  rw [norm_smul, hunit, mul_one, hspace, Real.norm_eq_abs, sq_abs]


/-- The actual source product diffeomorphism preserves the complete product
Riemannian bilinear form, by polarization of the proved actual norm identity. -/
theorem inner_mfderiv_unitParallelGradientLevelHomeomorph (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    let e := unitParallelGradientLevelHomeomorph hX hpX
      (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
    ∀ (p : ℝ × N₀) (r s : ℝ) (u v : TangentSpace J₀ p.2),
      inner ℝ ((mfderiv (𝓘(ℝ, ℝ).prod J₀) I e p) (r, u))
        ((mfderiv (𝓘(ℝ, ℝ).prod J₀) I e p) (s, v)) =
          r * s + inner ℝ u v := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
  let e := unitParallelGradientLevelHomeomorph hX hpX
    (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
  dsimp only
  intro p r s u v
  let D := mfderiv (𝓘(ℝ, ℝ).prod J₀) I e p
  have h1 := norm_sq_mfderiv_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne p r u
  have h2 := norm_sq_mfderiv_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne p s v
  have h3 := norm_sq_mfderiv_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne p (r + s) (u + v)
  change ‖D (r, u)‖ ^ 2 = r ^ 2 + ‖u‖ ^ 2 at h1
  change ‖D (s, v)‖ ^ 2 = s ^ 2 + ‖v‖ ^ 2 at h2
  change ‖D (r + s, u + v)‖ ^ 2 = (r + s) ^ 2 + ‖u + v‖ ^ 2 at h3
  have hadd : D (r + s, u + v) = D (r, u) + D (s, v) := D.map_add (r, u) (s, v)
  rw [hadd, norm_add_sq_real, norm_add_sq_real] at h3
  change inner ℝ (D (r, u)) (D (s, v)) = r * s + inner ℝ u v
  nlinarith


end CutoffRigidity
