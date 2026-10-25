module
public import CutoffRigidity.HopfLax
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Rademacher

/-! # Genuine Hopf–Lax derivatives at differentiability points

Every minimizing quadratic cost touches the actual infimum convolution.
Its spatial and time derivatives therefore identify the true derivatives;
no Hamilton–Jacobi equation is supplied as a premise.
-/
public section
namespace CutoffRigidity
open Set Filter MeasureTheory
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- At an actual differentiability point the actual gradient is determined
by every minimizing point of the quadratic infimum convolution. -/
theorem gradient_hopfLax_of_minimizer {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : ∀ z, |f z| ≤ M) (x y : E)
    (hy : hopfLax t f x = f y+‖x-y‖^2/(2*t))
    (hd : DifferentiableAt ℝ (hopfLax t f) x) :
    gradient (hopfLax t f) x = t⁻¹ • (x-y) := by
  let cost := fun z : E => f y+‖z-y‖^2/(2*t)
  have hCost : HasFDerivAt cost (t⁻¹ • innerSL ℝ (x-y)) x := by
    have hh := (((hasFDerivAt_id x).sub_const y).norm_sq.mul_const ((2*t)⁻¹))
    have hh' := HasFDerivAt.const_add (f y) hh
    convert hh' using 1
    · funext z; dsimp only [cost]; simp only [id_eq]; ring
    · ext z
      simp only [smul_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
      field_simp
      ring
  have hMin : IsLocalMin (fun z => cost z-hopfLax t f z) x := by
    show ∀ᶠ z in 𝓝 x, cost x-hopfLax t f x ≤ cost z-hopfLax t f z
    apply Eventually.of_forall
    intro z
    have hh := hopfLax_le_cost ht (fun w => (abs_le.mp (hf w)).1) z y
    change f y+‖x-y‖^2/(2*t)-hopfLax t f x ≤ _
    rw [hy]
    simpa only [sub_self,cost] using sub_nonneg.mpr hh
  have heq := hMin.hasFDerivAt_eq_zero (hCost.sub hd.hasFDerivAt)
  have hdEq : fderiv ℝ (hopfLax t f) x = t⁻¹ • innerSL ℝ (x-y) := by
    exact (sub_eq_zero.mp heq).symm
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient,hdEq,map_smul]
  rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- At an actual time differentiability point a minimizing cost also
identifies the actual time derivative. -/
theorem deriv_hopfLax_time_of_minimizer {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : ∀ z, |f z| ≤ M) (x y : E)
    (hy : hopfLax t f x = f y+‖x-y‖^2/(2*t))
    (hd : DifferentiableAt ℝ (fun s => hopfLax s f x) t) :
    deriv (fun s => hopfLax s f x) t = -‖x-y‖^2/(2*t^2) := by
  let cost := fun s : ℝ => f y+‖x-y‖^2/(2*s)
  have hCost : HasDerivAt cost (-‖x-y‖^2/(2*t^2)) t := by
    have hh := ((hasDerivAt_id t).inv (ne_of_gt ht)).const_mul (‖x-y‖^2/2)
    have hh' := hh.const_add (f y)
    convert hh' using 1
    · funext s; dsimp only [cost]; simp only [Pi.inv_apply,id_eq]; ring
    · simp only [id_eq]
      field_simp
  have hMin : IsLocalMin (fun s => cost s-hopfLax s f x) t := by
    show ∀ᶠ s in 𝓝 t, cost t-hopfLax t f x ≤ cost s-hopfLax s f x
    filter_upwards [eventually_gt_nhds ht] with s hs
    have hh := hopfLax_le_cost hs (fun z => (abs_le.mp (hf z)).1) x y
    change f y+‖x-y‖^2/(2*t)-hopfLax t f x ≤ _
    rw [hy]
    simpa only [sub_self,cost] using sub_nonneg.mpr hh
  have heq := hMin.hasDerivAt_eq_zero (hCost.sub hd.hasDerivAt)
  linarith

/-- The Hamilton–Jacobi equation follows from the actual minimizing
quadratic costs at every time and spatial differentiability point. -/
theorem hopfLax_hamilton_jacobi_at [ProperSpace E] {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : ∀ z, |f z| ≤ M) (hfc : Continuous f) (x : E)
    (hspace : DifferentiableAt ℝ (hopfLax t f) x)
    (htime : DifferentiableAt ℝ (fun s => hopfLax s f x) t) :
    deriv (fun s => hopfLax s f x) t + ‖gradient (hopfLax t f) x‖^2/2 = 0 := by
  obtain ⟨y,hy⟩ := exists_hopfLax_minimizer ht hf hfc x
  rw [deriv_hopfLax_time_of_minimizer ht hf x y hy htime,
    gradient_hopfLax_of_minimizer ht hf x y hy hspace]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow]
  field_simp
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The actual positive-time curve is differentiable almost everywhere;
this is obtained from the proved local time Lipschitz bound. -/
theorem hopfLax_ae_time_differentiable [ProperSpace E] {a M : ℝ} (ha : 0 < a)
    {f : E → ℝ} (hf : ∀ z, |f z| ≤ M) (hfc : Continuous f) (x : E) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (Ioi a),
      DifferentiableAt ℝ (fun s => hopfLax s f x) t := by
  have hLip := lipschitzOnWith_hopfLax_time ha hf hfc x
  filter_upwards [hLip.ae_differentiableWithinAt measurableSet_Ioi,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t hd ht
  exact hd.differentiableAt (Ioi_mem_nhds ht)

/-- Rademacher applies to the actual spatial Hopf–Lax operator on the
finite-dimensional Euclidean source space. -/
theorem hopfLax_ae_spatial_differentiable {d : ℕ} {t M : ℝ} (ht : 0 ≤ t)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ∀ z, |f z| ≤ M)
    {L : NNReal} (hL : LipschitzWith L f) :
    ∀ᵐ x ∂MeasureTheory.volume, DifferentiableAt ℝ (hopfLax t f) x :=
  (lipschitzWith_hopfLax ht hf hL).ae_differentiableAt

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The actual Hopf–Lax field is locally jointly Lipschitz in time and
space, so Rademacher applies directly to both variables together. -/
theorem exists_lipschitzOnWith_hopfLax_time_space [ProperSpace E] {a M : ℝ} (ha : 0 < a)
    {f : E → ℝ} (hf : ∀ z, |f z| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    ∃ C : NNReal, LipschitzOnWith C (fun p : ℝ×E => hopfLax p.1 f p.2) {p | a < p.1} := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  let Ct : NNReal := ⟨2*M/a,div_nonneg (by positivity) ha.le⟩
  refine ⟨Ct+L,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro p hp q hq
  have htime := (lipschitzOnWith_hopfLax_time ha hf hL.continuous p.2).dist_le_mul p.1 hp q.1 hq
  have hspace := (lipschitzWith_hopfLax (ha.trans hq).le hf hL).dist_le_mul p.2 q.2
  have hfst : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hsnd : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  calc
    _ ≤ dist (hopfLax p.1 f p.2) (hopfLax q.1 f p.2) +
        dist (hopfLax q.1 f p.2) (hopfLax q.1 f q.2) := dist_triangle _ _ _
    _ ≤ (Ct:ℝ)*dist p.1 q.1+(L:ℝ)*dist p.2 q.2 := add_le_add htime hspace
    _ ≤ (Ct:ℝ)*dist p q+(L:ℝ)*dist p q :=
      add_le_add (mul_le_mul_of_nonneg_left hfst Ct.coe_nonneg)
        (mul_le_mul_of_nonneg_left hsnd L.coe_nonneg)
    _ = _ := by simp only [NNReal.coe_add]; ring

/-- The actual Hamilton–Jacobi equation holds almost everywhere in both
time and space, with no equation or differentiability premise. -/
theorem hopfLax_hamilton_jacobi_hasDerivAt_ae {d : ℕ} {a M : ℝ} (ha : 0 < a)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ∀ z, |f z| ≤ M)
    {L : NNReal} (hL : LipschitzWith L f) :
    ∀ᵐ p : ℝ×EuclideanSpace ℝ (Fin d)
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))).restrict {p | a < p.1},
      HasDerivAt (fun s => hopfLax s f p.2) (-‖gradient (hopfLax p.1 f) p.2‖^2/2) p.1 := by
  obtain ⟨C,hLip⟩ := exists_lipschitzOnWith_hopfLax_time_space ha hf hL
  have hopen : IsOpen {p : ℝ×EuclideanSpace ℝ (Fin d) | a < p.1} :=
    isOpen_lt continuous_const continuous_fst
  filter_upwards [hLip.ae_differentiableWithinAt hopen.measurableSet,
    MeasureTheory.ae_restrict_mem hopen.measurableSet] with p hd hp
  have hdiff := hd.differentiableAt (hopen.mem_nhds hp)
  have htime : DifferentiableAt ℝ (fun s => hopfLax s f p.2) p.1 := by
    have hlin : DifferentiableAt ℝ (fun s : ℝ => (s,p.2)) p.1 :=
      differentiableAt_id.prodMk (differentiableAt_const p.2)
    exact hdiff.comp p.1 hlin
  have hspace : DifferentiableAt ℝ (hopfLax p.1 f) p.2 := by
    have hlin : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin d) => (p.1,x)) p.2 :=
      (differentiableAt_const p.1).prodMk differentiableAt_id
    exact hdiff.comp p.2 hlin
  have hHJ := hopfLax_hamilton_jacobi_at (ha.trans hp) hf hL.continuous p.2 hspace htime
  convert htime.hasDerivAt using 1
  linarith

/-- The actual Hamilton–Jacobi equation, as an equality of actual derivatives. -/
theorem hopfLax_hamilton_jacobi_ae {d : ℕ} {a M : ℝ} (ha : 0 < a)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ∀ z, |f z| ≤ M)
    {L : NNReal} (hL : LipschitzWith L f) :
    ∀ᵐ p : ℝ×EuclideanSpace ℝ (Fin d)
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))).restrict {p | a < p.1},
      deriv (fun s => hopfLax s f p.2) p.1 + ‖gradient (hopfLax p.1 f) p.2‖^2/2 = 0 := by
  apply (hopfLax_hamilton_jacobi_hasDerivAt_ae ha hf hL).mono
  intro p hp
  rw [hp.deriv]
  ring

/-- Fubini gives the exact time-a.e., space-a.e. Hamilton–Jacobi input
under every measure absolutely continuous with respect to volume. -/
theorem hopfLax_hamilton_jacobi_ae_of_absolutelyContinuous {d : ℕ} {a M : ℝ}
    (ha : 0 < a) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ∀ z, |f z| ≤ M)
    {L : NNReal} (hL : LipschitzWith L f)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) (hμ : μ ≪ MeasureTheory.volume) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (Ioi a), ∀ᵐ x ∂μ,
      deriv (fun s => hopfLax s f x) t + ‖gradient (hopfLax t f) x‖^2/2 = 0 := by
  have h := hopfLax_hamilton_jacobi_ae ha hf hL
  have hset : {p : ℝ×EuclideanSpace ℝ (Fin d) | a < p.1} =
      (Ioi a) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin d))) := by ext p; simp
  rw [hset,← MeasureTheory.Measure.prod_restrict,MeasureTheory.Measure.restrict_univ] at h
  exact (MeasureTheory.Measure.ae_ae_of_ae_prod h).mono (fun t ht => hμ.ae_le ht)

/-- The true a.e. time derivative under every volume-absolutely-continuous
law, including the Gibbs law, with all differentiability discharged. -/
theorem hopfLax_hasDerivAt_ae_of_absolutelyContinuous {d : ℕ} {a M : ℝ}
    (ha : 0 < a) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ∀ z, |f z| ≤ M)
    {L : NNReal} (hL : LipschitzWith L f)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) (hμ : μ ≪ MeasureTheory.volume) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (Ioi a), ∀ᵐ x ∂μ,
      HasDerivAt (fun s => hopfLax s f x) (-‖gradient (hopfLax t f) x‖^2/2) t := by
  have h := hopfLax_hamilton_jacobi_hasDerivAt_ae ha hf hL
  have hset : {p : ℝ×EuclideanSpace ℝ (Fin d) | a < p.1} =
      (Ioi a) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin d))) := by ext p; simp
  rw [hset,← MeasureTheory.Measure.prod_restrict,MeasureTheory.Measure.restrict_univ] at h
  exact (MeasureTheory.Measure.ae_ae_of_ae_prod h).mono (fun t ht => hμ.ae_le ht)

end CutoffRigidity
