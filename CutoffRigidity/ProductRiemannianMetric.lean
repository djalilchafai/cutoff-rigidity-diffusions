module

public import CutoffRigidity.SmoothRiemannianPullbackMetric

/-! # The standard product Riemannian metric
The product metric is constructed explicitly as the sum of the original factor
pairings. Its topology compatibility is proved with temporary factor product norms.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J 2 N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun x : N ↦ TangentSpace J x)]

local notation "g₁" => (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x))
local notation "g₂" => (RiemannianBundle.g (E := fun x : N ↦ TangentSpace J x))

/-- The actual product fiber metric is the sum of the actual factor pairings. -/
noncomputable def productRiemannianMetric :
    RiemannianMetric (fun p : M × N ↦ TangentSpace (I.prod J) p) := by
  letI : (p : M × N) → NormedAddCommGroup (TangentSpace (I.prod J) p) :=
    fun p ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I p.1 × TangentSpace J p.2))
  letI : (p : M × N) → NormedSpace ℝ (TangentSpace (I.prod J) p) :=
    fun p ↦ inferInstanceAs (NormedSpace ℝ (TangentSpace I p.1 × TangentSpace J p.2))
  let A := fun p : M × N ↦
    ContinuousLinearMap.fst ℝ (TangentSpace I p.1) (TangentSpace J p.2)
  let B := fun p : M × N ↦
    ContinuousLinearMap.snd ℝ (TangentSpace I p.1) (TangentSpace J p.2)
  refine
    { inner := fun p ↦ ((g₁).inner p.1).bilinearComp (A p) (A p) +
        ((g₂).inner p.2).bilinearComp (B p) (B p)
      symm := ?_
      pos := ?_
      continuousAt := ?_
      isVonNBounded := ?_ }
  · intro p v w
    change (g₁).inner p.1 v.1 w.1 + (g₂).inner p.2 v.2 w.2 =
      (g₁).inner p.1 w.1 v.1 + (g₂).inner p.2 w.2 v.2
    rw [(g₁).symm p.1 v.1 w.1, (g₂).symm p.2 v.2 w.2]
  · intro p v hv
    change 0 < (g₁).inner p.1 v.1 v.1 + (g₂).inner p.2 v.2 v.2
    by_cases hv1 : v.1 = 0
    · have hv2 : v.2 ≠ 0 := by
        intro h
        exact hv (Prod.ext hv1 h)
      simpa only [hv1, map_zero, zero_apply, zero_add] using (g₂).pos p.2 v.2 hv2
    · have h2 : 0 ≤ (g₂).inner p.2 v.2 v.2 := by
        by_cases hv2 : v.2 = 0
        · simp only [hv2, map_zero, zero_apply, le_refl]
        · exact ((g₂).pos p.2 v.2 hv2).le
      exact add_pos_of_pos_of_nonneg ((g₁).pos p.1 v.1 hv1) h2
  · intro p
    change ContinuousAt (fun v : TangentSpace I p.1 × TangentSpace J p.2 ↦
      (g₁).inner p.1 v.1 v.1 + (g₂).inner p.2 v.2 v.2) 0
    fun_prop
  · intro p
    apply (NormedSpace.isVonNBounded_ball ℝ (TangentSpace (I.prod J) p) 1).subset
    intro v hv
    let v₁ : TangentSpace I p.1 := v.1
    let v₂ : TangentSpace J p.2 := v.2
    have h1 : (g₁).inner p.1 v.1 v.1 = ‖v₁‖ ^ 2 := real_inner_self_eq_norm_sq v₁
    have h2 : (g₂).inner p.2 v.2 v.2 = ‖v₂‖ ^ 2 := real_inner_self_eq_norm_sq v₂
    change (g₁).inner p.1 v.1 v.1 + (g₂).inner p.2 v.2 v.2 < 1 at hv
    rw [h1, h2] at hv
    simp only [Metric.mem_ball, dist_zero_right]
    change max ‖v₁‖ ‖v₂‖ < 1
    rw [max_lt_iff]
    constructor <;> nlinarith [norm_nonneg v₁, norm_nonneg v₂, sq_nonneg ‖v₁‖, sq_nonneg ‖v₂‖]

@[instance_reducible] noncomputable def productRiemannianBundle :
    RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
  ⟨productRiemannianMetric (I := I) (J := J) (M := M) (N := N)⟩

/-- The constructed product pairing is exactly the original factor sum. -/
theorem productRiemannianMetric_inner (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    (productRiemannianMetric (I := I) (J := J) (M := M) (N := N)).inner p v w =
      (g₁).inner p.1 v.1 w.1 + (g₂).inner p.2 v.2 w.2 := rfl

/-- The constructed product norm has the actual factor squared-norm formula. -/
theorem norm_sq_productRiemannianBundle :
    letI := productRiemannianBundle (I := I) (J := J) (M := M) (N := N)
    ∀ (p : M × N) (v : TangentSpace (I.prod J) p),
      ‖v‖ ^ 2 =
        (@norm (TangentSpace I p.1)
          (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal p.1).toNorm v.1) ^ 2 +
        (@norm (TangentSpace J p.2)
          (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal p.2).toNorm v.2) ^ 2 := by
  letI := productRiemannianBundle (I := I) (J := J) (M := M) (N := N)
  intro p v
  let v₁ : TangentSpace I p.1 := v.1
  let v₂ : TangentSpace J p.2 := v.2
  have hi : inner ℝ v v = inner ℝ v₁ v₁ + inner ℝ v₂ v₂ := rfl
  simpa only [real_inner_self_eq_norm_sq] using hi

end CutoffRigidity
