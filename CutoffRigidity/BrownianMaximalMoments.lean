module

public import CutoffRigidity.BrownianIndependence
public import CutoffRigidity.LinearLangevinLaw
public import CutoffRigidity.FiniteDoobL2
public import CutoffRigidity.L2FatouBounds
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Data.Finset.Sort
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.CondVar
public import Mathlib.Algebra.Order.Chebyshev

/-! # Actual Brownian martingales and maximal moments

The Brownian predicates only require a.e. measurable evaluations and a.e.
continuous paths. We first construct a measurable continuous-path version,
indistinguishable from the original process. Its natural filtration is a
true sub-sigma-algebra of the given measurable space. Future/past independence
then proves the actual martingale conditional-expectation equation.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- There is a measurable continuous-path modification equal to the actual
Brownian process simultaneously at all times, outside one null set. -/
theorem exists_measurable_continuous_brownian_version (hB : IsBrownianReal B P) :
    ∃ C : Ω → C(ℝ≥0, ℝ), Measurable C ∧ ∀ᵐ ω ∂P, ∀ t, C ω t = B t ω := by
  classical
  let g : Ω → C(ℝ≥0, ℝ) := fun ω =>
    if h : Continuous (fun t => B t ω) then ⟨fun t => B t ω, h⟩ else 0
  have heval (t : ℝ≥0) : AEMeasurable (fun ω => g ω t) P := by
    apply (hB.aemeasurable t).congr
    filter_upwards [hB.cont] with ω hω
    simp [g, hω]
  have hgm : Measurable (fun ω : NullMeasurableSpace Ω P => g ω) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    exact fun t => (heval t).nullMeasurable.measurable'
  have hgn : AEMeasurable g P := (show NullMeasurable g P from hgm).aemeasurable
  refine ⟨hgn.mk g, hgn.measurable_mk, ?_⟩
  filter_upwards [hgn.ae_eq_mk, hB.cont] with ω hω hcont
  intro t
  rw [← hω]
  simp [g, hcont]

/-- A chosen genuine measurable continuous-path Brownian modification. -/
@[expose] noncomputable def brownianContinuousModification (hB : IsBrownianReal B P) : Ω → C(ℝ≥0, ℝ) :=
  Classical.choose (exists_measurable_continuous_brownian_version hB)

theorem brownianContinuousModification_measurable (hB : IsBrownianReal B P) :
    Measurable (brownianContinuousModification hB) :=
  (Classical.choose_spec (exists_measurable_continuous_brownian_version hB)).1

theorem brownianContinuousModification_eq_ae (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t, brownianContinuousModification hB ω t = B t ω :=
  (Classical.choose_spec (exists_measurable_continuous_brownian_version hB)).2

theorem brownianContinuousModification_eval_stronglyMeasurable
    (hB : IsBrownianReal B P) (t : ℝ≥0) :
    StronglyMeasurable (fun ω => brownianContinuousModification hB ω t) :=
  ((ContinuousMap.measurable_eval t).comp (brownianContinuousModification_measurable hB)).stronglyMeasurable

/-- The modification is itself a genuine Brownian process. -/
theorem brownianContinuousModification_isBrownian (hB : IsBrownianReal B P) :
    IsBrownianReal (fun t ω => brownianContinuousModification hB ω t) P := by
  refine ⟨hB.toIsPreBrownianReal.congr ?_, Filter.Eventually.of_forall (fun ω =>
    (brownianContinuousModification hB ω).continuous)⟩
  intro t
  filter_upwards [brownianContinuousModification_eq_ae hB] with ω hω
  exact (hω t).symm

/-- Future/past independence gives the genuine martingale equation for
any measurable Brownian realization and its actual natural filtration. -/
theorem brownian_martingale_natural (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) : Martingale B (Filtration.natural B hsm) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨Filtration.stronglyAdapted_natural hsm, ?_⟩
  intro s t hst
  have hi : IndepFun (fun ω => B t ω - B s ω)
      (fun ω (u : Iic s) => B u ω) P := by
    have h : IndepFun (fun ω => B (s + (t - s)) ω - B s ω)
        (fun ω (u : Iic s) => B u ω) P := (hB.indepFun_shift s).comp
      (φ := fun f : ℝ≥0 → ℝ => f (t - s)) (ψ := fun f : Iic s → ℝ => f) (measurable_pi_apply _) measurable_id
    simpa only [add_tsub_cancel_of_le hst] using h
  have hm : StronglyMeasurable (fun ω => B t ω - B s ω) := (hsm t).sub (hsm s)
  have hind : Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance)
      (Filtration.natural B hsm s) P := by
    rw [Filtration.natural_eq_comap]
    exact hi
  have hc := condExp_indep_eq hm.measurable.comap_le (Filtration.le _ s)
    (comap_measurable (fun ω => B t ω - B s ω)).stronglyMeasurable hind
  have hzero : (∫ ω, B t ω - B s ω ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s), hB.integral_eval, hB.integral_eval]
    ring
  rw [hzero] at hc
  have hs := condExp_of_stronglyMeasurable (Filtration.le (Filtration.natural B hsm) s)
    (Filtration.stronglyAdapted_natural hsm s) (hB.integrable_eval s)
  have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) (Filtration.natural B hsm s)
  filter_upwards [hc, hsub] with ω hω hsubω
  rw [hs] at hsubω
  have heq : P[fun ω => B t ω - B s ω | Filtration.natural B hsm s] ω =
      P[B t | Filtration.natural B hsm s] ω - B s ω := by
    convert! hsubω using 1
  rw [heq] at hω
  change P[B t | Filtration.natural B hsm s] ω = B s ω
  change P[B t | Filtration.natural B hsm s] ω - B s ω = 0 at hω
  linarith

/-- Every Brownian process admits a genuine natural-filtration martingale
version indistinguishable from the original process. -/
theorem brownianContinuousModification_martingale (hB : IsBrownianReal B P) :
    Martingale (fun t ω => brownianContinuousModification hB ω t)
      (Filtration.natural (fun t ω => brownianContinuousModification hB ω t)
        (brownianContinuousModification_eval_stronglyMeasurable hB)) P :=
  brownian_martingale_natural (brownianContinuousModification_isBrownian hB)
    (brownianContinuousModification_eval_stronglyMeasurable hB)


/-- Absolute value of a measurable Brownian realization is a nonnegative
submartingale in its genuine natural filtration. -/
theorem brownian_abs_submartingale_natural (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    Submartingale (fun t ω => |B t ω|) (Filtration.natural B hsm) P := by
  have hM := brownian_martingale_natural hB hsm
  have h := hM.submartingale.sup hM.neg.submartingale
  have heq : (fun t ω => |B t ω|) = B ⊔ (-B) := by
    funext t ω
    exact abs_eq_max_neg
  rw [heq]
  exact h

/-- Pull a genuine filtration back along a monotone deterministic time map. -/
@[expose] def sampledFiltration {I J : Type*} [Preorder I] [Preorder J]
    (ℱ : Filtration I ‹MeasurableSpace Ω›) (τ : J → I) (hτ : Monotone τ) :
    Filtration J ‹MeasurableSpace Ω› where
  seq j := ℱ (τ j)
  mono' _ _ hij := ℱ.mono (hτ hij)
  le' j := ℱ.le (τ j)

/-- Deterministic increasing sampling preserves the actual submartingale. -/
theorem submartingale_sampled {I J : Type*} [Preorder I] [Preorder J]
    {ℱ : Filtration I ‹MeasurableSpace Ω›} {f : I → Ω → ℝ}
    (hf : Submartingale f ℱ P) (τ : J → I) (hτ : Monotone τ) :
    Submartingale (fun j => f (τ j)) (sampledFiltration ℱ τ hτ) P :=
  ⟨(fun j => hf.stronglyAdapted (τ j)), (fun _ _ hij => hf.ae_le_condExp (hτ hij)),
    (fun j => hf.integrable (τ j))⟩

omit [MeasurableSpace Ω] in
/-- Every earlier sample lies below its recursively defined running maximum. -/
theorem le_finiteRunningMaximum {f : ℕ → Ω → ℝ} {i n : ℕ} (hin : i ≤ n) (ω : Ω) :
    f i ω ≤ finiteRunningMaximum f n ω := by
  induction n with
  | zero =>
    have hi := Nat.le_zero.mp hin
    subst i
    exact le_rfl
  | succ n ih =>
    by_cases hi : i = n + 1
    · subst i
      exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

/-- A finite collection of Brownian times inside `[0,T]` has uniformly
bounded squared maximum, by sorting and the proved finite Doob L² inequality. -/
theorem brownian_finite_max_integral_sq_le (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (S : Finset ℝ≥0) (hS : S.Nonempty)
    (T : ℝ≥0) (hST : ∀ s ∈ S, s ≤ T) :
    (∫ ω, (S.sup' hS (fun s => |B s ω|)) ^ 2 ∂P) ≤ 4 * (T : ℝ) := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hcard : 0 < S.card := Finset.card_pos.mpr hS
  let N := S.card - 1
  let τ : ℕ → ℝ≥0 := fun n => S.orderEmbOfFin rfl
    ⟨min n N, lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hcard (by norm_num))⟩
  have hτ : Monotone τ := by
    intro i j hij
    apply (S.orderEmbOfFin rfl).monotone
    exact min_le_min hij le_rfl
  have hcover : ∀ s ∈ S, ∃ i ≤ N, τ i = s := by
    intro s hs
    let j := (S.orderIsoOfFin rfl).symm ⟨s, hs⟩
    have hj : (j : ℕ) ≤ N := Nat.le_sub_one_of_lt j.isLt
    refine ⟨j, hj, ?_⟩
    change S.orderEmbOfFin rfl ⟨min (j : ℕ) N, _⟩ = s
    have hfin : (⟨min (j : ℕ) N, lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hcard (by norm_num))⟩ : Fin S.card) = j :=
      Fin.ext (min_eq_left hj)
    rw [hfin]
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨s, hs⟩)
  let f : ℕ → Ω → ℝ := fun n ω => |B (τ n) ω|
  have hsub := submartingale_sampled (brownian_abs_submartingale_natural hB hsm) τ hτ
  have hL : ∀ n, MemLp (f n) 2 P := fun n =>
    (hB.isGaussianProcess.hasGaussianLaw_eval (τ n)).memLp_two.abs
  have hn : 0 ≤ f := fun n ω => abs_nonneg _
  have hmax := integral_finiteRunningMaximum_sq_le_four hsub hL hn N
  have hpoint (ω : Ω) : S.sup' hS (fun s => |B s ω|) ≤ finiteRunningMaximum f N ω := by
    apply Finset.sup'_le
    intro s hs
    obtain ⟨i, hi, hτi⟩ := hcover s hs
    have h := le_finiteRunningMaximum (f := f) hi ω
    simpa only [f, hτi] using h
  have hmaxle (n : ℕ) (ω : Ω) : finiteRunningMaximum f n ω ≤ S.sup' hS (fun s => |B s ω|) := by
    induction n with
    | zero => exact Finset.le_sup' (fun s => |B s ω|) (S.orderEmbOfFin_mem rfl _)
    | succ n ih => exact max_le ih (Finset.le_sup' (fun s => |B s ω|) (S.orderEmbOfFin_mem rfl _))
  have heq : (fun ω => S.sup' hS (fun s => |B s ω|)) = finiteRunningMaximum f N :=
    funext (fun ω => le_antisymm (hpoint ω) (hmaxle N ω))
  have hterminal : (∫ ω, f N ω ^ 2 ∂P) ≤ (T : ℝ) := by
    simp only [f, sq_abs]
    rw [integral_sq_brownian hB]
    exact_mod_cast hST (τ N) (S.orderEmbOfFin_mem rfl _)
  rw [show (fun ω => (S.sup' hS (fun s => |B s ω|)) ^ 2) =
    (fun ω => finiteRunningMaximum f N ω ^ 2) from congrArg (fun g => fun ω => (g ω) ^ 2) heq]
  exact hmax.trans (by linarith)


omit [MeasurableSpace Ω] in
/-- An upper bound for every sample bounds the finite running maximum. -/
theorem finiteRunningMaximum_le {f : ℕ → Ω → ℝ} {n : ℕ} {C : ℝ} (ω : Ω)
    (h : ∀ i ≤ n, f i ω ≤ C) : finiteRunningMaximum f n ω ≤ C := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih => exact max_le (ih (fun i hi => h i (hi.trans (Nat.le_succ n)))) (h _ le_rfl)

omit [MeasurableSpace Ω] in
/-- The recursive running maximum is the finite supremum of its entries. -/
theorem finiteRunningMaximum_eq_sup' (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    finiteRunningMaximum f n ω = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun i => f i ω) := by
  apply le_antisymm
  · apply finiteRunningMaximum_le
    intro i hi
    exact Finset.le_sup' (fun i => f i ω) (Finset.mem_range.mpr (by omega))
  · apply Finset.sup'_le
    intro i hi
    exact le_finiteRunningMaximum (by have := Finset.mem_range.mp hi; omega) ω

/-- Dense finite samples recover the actual supremum norm of a continuous
function on a compact space. -/
theorem tendsto_finiteRunningMaximum_dense_norm {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] (q : ℕ → K) (hq : DenseRange q) (f : C(K, ℝ)) :
    Tendsto (fun n => finiteRunningMaximum (fun i (_ : Unit) => |f (q i)|) n ())
      atTop (𝓝 ‖f‖) := by
  let M : ℕ → ℝ := fun n => finiteRunningMaximum (fun i (_ : Unit) => |f (q i)|) n ()
  have hbound (n : ℕ) : M n ≤ ‖f‖ :=
    finiteRunningMaximum_le () (fun i hi => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (q i))
  have hnonneg : 0 ≤ M 0 := abs_nonneg _
  have hb : BddAbove (range M) := ⟨‖f‖, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  have hmono : Monotone M := by
    apply monotone_nat_of_le_succ
    intro n
    exact le_max_left _ _
  have hEq : (⨆ n, M n) = ‖f‖ := by
    apply le_antisymm (ciSup_le hbound)
    apply (f.norm_le (hnonneg.trans (le_ciSup hb 0))).mpr
    intro x
    refine hq.induction_on (p := fun x => ‖f x‖ ≤ ⨆ n, M n) x
      (isClosed_le f.continuous.norm continuous_const) ?_
    intro n
    exact (show ‖f (q n)‖ ≤ M n by
      simpa only [Real.norm_eq_abs] using
        le_finiteRunningMaximum (f := fun i (_ : Unit) => |f (q i)|) (le_refl n) ()).trans (le_ciSup hb n)
  simpa only [hEq] using tendsto_atTop_ciSup hmono hb

/-- The finite-time supremum norm of a genuine measurable continuous-path
Brownian modification; it agrees with the original whole path off one null set. -/
@[expose] noncomputable def brownianMaximum (hB : IsBrownianReal B P) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ‖(brownianContinuousModification hB ω).restrict (Icc 0 T)‖

/-- Actual Brownian finite-time maximal L² estimate. All moments are derived
from the Brownian law, with no supremum-integrability assumption. -/
theorem brownianMaximum_memLp_integral_sq_le (hB : IsBrownianReal B P) (T : ℝ≥0) :
    MemLp (brownianMaximum hB T) 2 P ∧
      (∫ ω, brownianMaximum hB T ω ^ 2 ∂P) ≤ 4 * (T : ℝ) := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  let q := TopologicalSpace.denseSeq (Icc (0 : ℝ≥0) T)
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq _
  let C := brownianContinuousModification hB
  let X : ℕ → Ω → ℝ := fun n ω => |C ω (q n)|
  let M : ℕ → Ω → ℝ := finiteRunningMaximum X
  have hL : ∀ n, MemLp (X n) 2 P := fun n =>
    ((brownianContinuousModification_isBrownian hB).isGaussianProcess.hasGaussianLaw_eval (q n)).memLp_two.abs
  have hM : ∀ n, MemLp (M n) 2 P := finiteRunningMaximum_memLp hL
  have hlim (ω : Ω) : Tendsto (fun n => M n ω) atTop (𝓝 (brownianMaximum hB T ω)) := by
    convert! tendsto_finiteRunningMaximum_dense_norm q hq ((C ω).restrict (Icc 0 T)) using 1
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg₂ max ih rfl
  have hmeas : Measurable (brownianMaximum hB T) := by
    apply measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.mpr hlim)
    have hmeasX : StronglyAdapted
        (Filtration.natural X (fun n =>
          (brownianContinuousModification_eval_stronglyMeasurable hB (q n)).norm)) X :=
      Filtration.stronglyAdapted_natural _
    exact (finiteRunningMaximum_stronglyMeasurable hmeasX n).measurable.mono (Filtration.le _ _) le_rfl
  have hbound (n : ℕ) : (∫ ω, ‖M n ω‖ ^ 2 ∂P) ≤ 4 * (T : ℝ) := by
    let S := (Finset.range (n + 1)).image (fun i => (q i : ℝ≥0))
    have hS : S.Nonempty := Finset.nonempty_range_add_one.image _
    have h := brownian_finite_max_integral_sq_le (brownianContinuousModification_isBrownian hB)
      (brownianContinuousModification_eval_stronglyMeasurable hB) S hS T (fun s hs => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
        exact (q i).property.2)
    have heq (ω : Ω) : S.sup' hS (fun s => |C ω s|) = M n ω := by
      rw [Finset.sup'_image]
      exact (finiteRunningMaximum_eq_sup' X n ω).symm
    change (∫ ω, (S.sup' hS (fun s => |C ω s|)) ^ 2 ∂P) ≤ 4 * (T : ℝ) at h
    simp_rw [heq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have h := memLp_two_and_second_moment_le_of_ae_tendsto hM hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hlim) hbound
  simpa only [Real.norm_eq_abs, sq_abs] using h


/-- The literal supremum of the original scalar Brownian path on `[0,T]`. -/
@[expose] noncomputable def brownianSupAbs (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  sSup ((fun t => |B t ω|) '' Icc 0 T)

/-- On a compact time interval the continuous-map norm is exactly the
literal real supremum of the norms of its evaluations. -/
theorem continuousMap_restrict_norm_eq_sSup {E : Type*} [NormedAddCommGroup E]
    (f : C(ℝ≥0, E)) (T : ℝ≥0) :
    ‖f.restrict (Icc 0 T)‖ = sSup ((fun t => ‖f t‖) '' Icc 0 T) := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  change sSup (range (fun t : Icc (0 : ℝ≥0) T => ‖f t‖)) = _
  congr 1
  ext r
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

/-- The constructed maximum equals the original whole-path supremum outside
one Brownian null set, rather than merely at each fixed time. -/
theorem brownianMaximum_eq_supAbs_ae (hB : IsBrownianReal B P) (T : ℝ≥0) :
    brownianMaximum hB T =ᵐ[P] brownianSupAbs B T := by
  filter_upwards [brownianContinuousModification_eq_ae hB] with ω hω
  rw [brownianMaximum, continuousMap_restrict_norm_eq_sSup]
  simp only [Real.norm_eq_abs, hω, brownianSupAbs]

/-- Actual finite-time Brownian maximal L² bound, stated using the original
process and the literal supremum over every time in the interval. -/
theorem brownianSupAbs_memLp_integral_sq_le (hB : IsBrownianReal B P) (T : ℝ≥0) :
    MemLp (brownianSupAbs B T) 2 P ∧
      (∫ ω, brownianSupAbs B T ω ^ 2 ∂P) ≤ 4 * (T : ℝ) := by
  obtain ⟨hL, hb⟩ := brownianMaximum_memLp_integral_sq_le hB T
  have heq := brownianMaximum_eq_supAbs_ae hB T
  refine ⟨MemLp.ae_eq heq hL, ?_⟩
  have hi := integral_congr_ae (heq.fun_comp (fun x => x ^ 2))
  simp only [Function.comp_def] at hi
  rw [← hi]
  exact hb
/-- Dense finite samples recover the actual supremum norm of a continuous
function on a compact space. -/
theorem tendsto_finiteRunningMaximum_dense_norm_generic {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] {F : Type*} [NormedAddCommGroup F]
    (q : ℕ → K) (hq : DenseRange q) (f : C(K, F)) :
    Tendsto (fun n => finiteRunningMaximum (fun i (_ : Unit) => ‖f (q i)‖) n ())
      atTop (𝓝 ‖f‖) := by
  let M : ℕ → ℝ := fun n => finiteRunningMaximum (fun i (_ : Unit) => ‖f (q i)‖) n ()
  have hbound (n : ℕ) : M n ≤ ‖f‖ :=
    finiteRunningMaximum_le () (fun i hi => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (q i))
  have hnonneg : 0 ≤ M 0 := norm_nonneg _
  have hb : BddAbove (range M) := ⟨‖f‖, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  have hmono : Monotone M := by
    apply monotone_nat_of_le_succ
    intro n
    exact le_max_left _ _
  have hEq : (⨆ n, M n) = ‖f‖ := by
    apply le_antisymm (ciSup_le hbound)
    apply (f.norm_le (hnonneg.trans (le_ciSup hb 0))).mpr
    intro x
    refine hq.induction_on (p := fun x => ‖f x‖ ≤ ⨆ n, M n) x
      (isClosed_le f.continuous.norm continuous_const) ?_
    intro n
    exact (show ‖f (q n)‖ ≤ M n by
      simpa only [Real.norm_eq_abs] using
        le_finiteRunningMaximum (f := fun i (_ : Unit) => ‖f (q i)‖) (le_refl n) ()).trans (le_ciSup hb n)
  simpa only [hEq] using tendsto_atTop_ciSup hmono hb



/-- Every finite list of original Brownian evaluations satisfies the same
maximal bound, without a global measurability premise on the raw realization. -/
theorem brownian_sample_max_integral_sq_le (hB : IsBrownianReal B P)
    (q : ℕ → ℝ≥0) (T : ℝ≥0) (hq : ∀ n, q n ≤ T) (n : ℕ) :
    (∫ ω, finiteRunningMaximum (fun i ω => |B (q i) ω|) n ω ^ 2 ∂P) ≤ 4 * (T : ℝ) := by
  classical
  let C := brownianContinuousModification hB
  let S := (Finset.range (n + 1)).image q
  have hS : S.Nonempty := Finset.nonempty_range_add_one.image q
  have h := brownian_finite_max_integral_sq_le (brownianContinuousModification_isBrownian hB)
    (brownianContinuousModification_eval_stronglyMeasurable hB) S hS T (fun s hs => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      exact hq i)
  have heq (ω : Ω) : S.sup' hS (fun s => |C ω s|) =
      finiteRunningMaximum (fun i ω => |C ω (q i)|) n ω := by
    rw [Finset.sup'_image]
    convert! (finiteRunningMaximum_eq_sup' (fun i ω => |C ω (q i)|) n ω).symm using 1
  change (∫ ω, (S.sup' hS (fun s => |C ω s|)) ^ 2 ∂P) ≤ _ at h
  simp_rw [heq] at h
  have hAE : (fun ω => finiteRunningMaximum (fun i ω => |C ω (q i)|) n ω ^ 2) =ᵐ[P]
      (fun ω => finiteRunningMaximum (fun i ω => |B (q i) ω|) n ω ^ 2) := by
    filter_upwards [brownianContinuousModification_eq_ae hB] with ω hω
    congr 1
    clear h heq hS S
    induction n with
    | zero => exact congrArg abs (hω (q 0))
    | succ n ih => exact congrArg₂ max ih (congrArg abs (hω (q (n + 1))))
  rwa [integral_congr_ae hAE] at h

omit [MeasurableSpace Ω] in
/-- A finite vector maximum is controlled by the sum of the squared
coordinate maxima, giving the dimension rather than its square. -/
theorem finiteRunningMaximum_norm_sq_le_sum {ι : Type*} [Fintype ι]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (n : ℕ) (ω : Ω) :
    finiteRunningMaximum (fun i ω => ‖X i ω‖) n ω ^ 2 ≤
      ∑ j, finiteRunningMaximum (fun i ω => |X i ω j|) n ω ^ 2 := by
  let C := ∑ j, finiteRunningMaximum (fun i ω => |X i ω j|) n ω ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hvalue (i : ℕ) (hi : i ≤ n) : ‖X i ω‖ ^ 2 ≤ C := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j hj
    have h := le_finiteRunningMaximum (f := fun i ω => |X i ω j|) hi ω
    have hn := finiteRunningMaximum_nonneg (f := fun i ω => |X i ω j|)
      (fun _ _ => abs_nonneg _) n ω
    nlinarith [sq_abs (X i ω j), abs_nonneg (X i ω j)]
  have hm : finiteRunningMaximum (fun i ω => ‖X i ω‖) n ω ≤ Real.sqrt C := by
    apply finiteRunningMaximum_le
    intro i hi
    have hv := hvalue i hi
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg (X i ω)]
  have hn := finiteRunningMaximum_nonneg (f := fun i ω => ‖X i ω‖)
    (fun _ _ => norm_nonneg _) n ω
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C]

/-- The literal supremum norm of the original Euclidean Brownian path. -/
@[expose] noncomputable def brownianSupNorm {ι : Type*} [Fintype ι]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (T : ℝ≥0) (ω : Ω) : ℝ :=
  sSup ((fun t => ‖B t ω‖) '' Icc 0 T)

/-- The genuine finite-time Euclidean Brownian maximum has finite second
moment, bounded by four times dimension times time. -/
theorem euclideanBrownianSupNorm_memLp_integral_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} (hB : IsEuclideanBrownian B P) (T : ℝ≥0) :
    MemLp (brownianSupNorm B T) 2 P ∧
      (∫ ω, brownianSupNorm B T ω ^ 2 ∂P) ≤ 4 * Fintype.card ι * (T : ℝ) := by
  classical
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure
  let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  let q := TopologicalSpace.denseSeq (Icc (0 : ℝ≥0) T)
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq _
  let X : ℕ → Ω → EuclideanSpace ℝ ι := fun i ω => B (q i) ω
  let M : ℕ → Ω → ℝ := finiteRunningMaximum (fun i ω => ‖X i ω‖)
  let Mi : ι → ℕ → Ω → ℝ := fun j => finiteRunningMaximum (fun i ω => |X i ω j|)
  have hL : ∀ n, MemLp (fun ω => ‖X n ω‖) 2 P := fun n =>
    (hB.hasLaw_eval (q n)).hasGaussianLaw.memLp_two.norm
  have hM : ∀ n, MemLp (M n) 2 P := finiteRunningMaximum_memLp hL
  have hMi : ∀ j n, MemLp (Mi j n) 2 P := fun j => finiteRunningMaximum_memLp
    (fun n => ((hB.coordinate j).isGaussianProcess.hasGaussianLaw_eval (q n)).memLp_two.abs)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => M n ω) atTop (𝓝 (brownianSupNorm B T ω)) := by
    filter_upwards [hB.continuous_paths] with ω hω
    let f : C(ℝ≥0, EuclideanSpace ℝ ι) := ⟨fun t => B t ω, hω⟩
    have h := tendsto_finiteRunningMaximum_dense_norm_generic q hq (f.restrict (Icc 0 T))
    rw [continuousMap_restrict_norm_eq_sSup] at h
    convert! h using 1
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg₂ max ih rfl
  have hg : AEStronglyMeasurable (brownianSupNorm B T) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hM n).aestronglyMeasurable) hlim
  have hb (n : ℕ) : (∫ ω, ‖M n ω‖ ^ 2 ∂P) ≤ 4 * Fintype.card ι * (T : ℝ) := by
    have hc (j : ι) := brownian_sample_max_integral_sq_le (hB.coordinate j)
      (fun i => (q i : ℝ≥0)) T (fun i => (q i).property.2) n
    have hint : Integrable (fun ω => ∑ j, Mi j n ω ^ 2) P :=
      integrable_finsetSum _ (fun j _ => (hMi j n).integrable_sq)
    calc
      _ = ∫ ω, M n ω ^ 2 ∂P := by simp only [Real.norm_eq_abs, sq_abs]
      _ ≤ ∫ ω, (∑ j, Mi j n ω ^ 2) ∂P := by
        apply integral_mono (hM n).integrable_sq hint
        exact finiteRunningMaximum_norm_sq_le_sum X n
      _ = ∑ j, ∫ ω, Mi j n ω ^ 2 ∂P :=
        integral_finsetSum _ (fun j _ => (hMi j n).integrable_sq)
      _ ≤ ∑ _ : ι, 4 * (T : ℝ) := Finset.sum_le_sum (fun j _ => hc j)
      _ = _ := by simp; ring
  have h := memLp_two_and_second_moment_le_of_ae_tendsto hM hg hlim hb
  simpa only [Real.norm_eq_abs, sq_abs] using h


/-- Squaring an actual square-integrable real martingale gives a genuine
submartingale, by nonnegativity of conditional variance. -/
theorem martingale_square_submartingale {I : Type*} [Preorder I]
    {ℱ : Filtration I ‹MeasurableSpace Ω›} {X : I → Ω → ℝ}
    [IsFiniteMeasure P] (hM : Martingale X ℱ P) (hL : ∀ i, MemLp (X i) 2 P) :
    Submartingale (fun i ω => X i ω ^ 2) ℱ P := by
  refine ⟨(fun i => (hM.stronglyAdapted i).pow 2), ?_, fun i => (hL i).integrable_sq⟩
  intro i j hij
  have h := condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le i) (hL j)
  have hn : 0 ≤ᵐ[P] condVar (ℱ i) (X j) P :=
    condExp_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  filter_upwards [h, hn, hM.condExp_ae_eq hij] with ω hω hnω hmω
  have heq : condVar (ℱ i) (X j) P ω =
      P[fun ω => X j ω ^ 2 | ℱ i] ω - (P[X j | ℱ i] ω) ^ 2 := by
    convert! hω using 1
  rw [heq, hmω] at hnω
  exact sub_nonneg.mp hnω

/-- The actual Brownian square is a genuine nonnegative submartingale. -/
theorem brownian_square_submartingale_natural (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    Submartingale (fun t ω => B t ω ^ 2) (Filtration.natural B hsm) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact martingale_square_submartingale (brownian_martingale_natural hB hsm)
    (fun t => (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)

/-- The Brownian square has genuine L² integrability, from its Gaussian
fourth moment rather than a supremum-moment assumption. -/
theorem brownian_square_memLp_two (hB : IsBrownianReal B P) (t : ℝ≥0) :
    MemLp (fun ω => B t ω ^ 2) 2 P := by
  apply (memLp_two_iff_integrable_sq
    (((hB.aemeasurable t).pow_const 2).aestronglyMeasurable)).mpr
  have h4 : MemLp (B t) (4 : ℝ≥0∞) P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp (by norm_num)
  have hint := h4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  simpa only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs] using hint

/-- A nonnegative continuous-time submartingale has a finite-set maximal
L² bound whenever its second moments up to the terminal time are bounded. -/
theorem submartingale_finite_max_integral_sq_le
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → ℝ} (hX : Submartingale X ℱ P)
    (hXL : ∀ t, MemLp (X t) 2 P) (hXN : 0 ≤ X)
    (S : Finset ℝ≥0) (hS : S.Nonempty) (T : ℝ≥0)
    (hST : ∀ s ∈ S, s ≤ T) {C : ℝ}
    (hterm : ∀ s ≤ T, (∫ ω, X s ω ^ 2 ∂P) ≤ C) :
    (∫ ω, (S.sup' hS (fun s => X s ω)) ^ 2 ∂P) ≤ 4 * C := by
  classical
  have hcard : 0 < S.card := Finset.card_pos.mpr hS
  let N := S.card - 1
  let τ : ℕ → ℝ≥0 := fun n => S.orderEmbOfFin rfl
    ⟨min n N, lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hcard (by norm_num))⟩
  have hτ : Monotone τ := by
    intro i j hij
    apply (S.orderEmbOfFin rfl).monotone
    exact min_le_min hij le_rfl
  have hcover : ∀ s ∈ S, ∃ i ≤ N, τ i = s := by
    intro s hs
    let j := (S.orderIsoOfFin rfl).symm ⟨s, hs⟩
    have hj : (j : ℕ) ≤ N := Nat.le_sub_one_of_lt j.isLt
    refine ⟨j, hj, ?_⟩
    change S.orderEmbOfFin rfl ⟨min (j : ℕ) N, _⟩ = s
    have hfin : (⟨min (j : ℕ) N, lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hcard (by norm_num))⟩ : Fin S.card) = j :=
      Fin.ext (min_eq_left hj)
    rw [hfin]
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨s, hs⟩)
  let f : ℕ → Ω → ℝ := fun n ω => X (τ n) ω
  have hsub := submartingale_sampled hX τ hτ
  have hL : ∀ n, MemLp (f n) 2 P := fun n => hXL (τ n)
  have hn : 0 ≤ f := fun n ω => hXN (τ n) ω
  have hmax := integral_finiteRunningMaximum_sq_le_four hsub hL hn N
  have hpoint (ω : Ω) : S.sup' hS (fun s => X s ω) ≤ finiteRunningMaximum f N ω := by
    apply Finset.sup'_le
    intro s hs
    obtain ⟨i, hi, hτi⟩ := hcover s hs
    have h := le_finiteRunningMaximum (f := f) hi ω
    simpa only [f, hτi] using h
  have hmaxle (n : ℕ) (ω : Ω) : finiteRunningMaximum f n ω ≤ S.sup' hS (fun s => X s ω) := by
    induction n with
    | zero => exact Finset.le_sup' (fun s => X s ω) (S.orderEmbOfFin_mem rfl _)
    | succ n ih => exact max_le ih (Finset.le_sup' (fun s => X s ω) (S.orderEmbOfFin_mem rfl _))
  have heq : (fun ω => S.sup' hS (fun s => X s ω)) = finiteRunningMaximum f N :=
    funext (fun ω => le_antisymm (hpoint ω) (hmaxle N ω))
  have hterminal : (∫ ω, f N ω ^ 2 ∂P) ≤ C :=
    hterm (τ N) (hST (τ N) (S.orderEmbOfFin_mem rfl _))
  rw [show (fun ω => (S.sup' hS (fun s => X s ω)) ^ 2) =
    (fun ω => finiteRunningMaximum f N ω ^ 2) from congrArg (fun g => fun ω => (g ω) ^ 2) heq]
  exact hmax.trans (by linarith)



/-- A fixed actual Gaussian fourth moment; it is a finite real number. -/
@[expose] noncomputable def gaussianFourthMoment : ℝ :=
  ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1

/-- The constant in the fourth-moment bound is the genuine integrable
standard Gaussian fourth power. -/
theorem integrable_fourth_standardGaussian :
    Integrable (fun z : ℝ => z ^ 4) (gaussianReal 0 1) := by
  have hL : MemLp (id : ℝ → ℝ) (4 : ℝ≥0∞) (gaussianReal 0 1) :=
    memLp_id_gaussianReal' _ (by norm_num)
  have h := hL.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  simpa only [id_eq, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs] using h

theorem gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg (fun x => by positivity)

/-- Brownian fourth moments scale quadratically in time, proved using the
actual Gaussian marginal and the actual scaling pushforward. -/
theorem integral_fourth_brownian (hB : IsBrownianReal B P) (t : ℝ≥0) :
    (∫ ω, B t ω ^ 4 ∂P) = (t : ℝ) ^ 2 * gaussianFourthMoment := by
  have hId : HasLaw (fun z : ℝ => z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hscale := gaussianReal_const_mul hId (Real.sqrt (t : ℝ))
  have hvar : NNReal.mk (Real.sqrt (t : ℝ) ^ 2) (sq_nonneg _) * 1 = t := by
    ext
    simp [Real.sq_sqrt t.coe_nonneg]
  rw [mul_zero, hvar] at hscale
  have hs := hscale.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  have hb := (hB.hasLaw_eval t).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  simp only [Function.comp_def] at hs hb
  calc
    _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 t := hb
    _ = ∫ z : ℝ, (Real.sqrt (t : ℝ) * z) ^ 4 ∂gaussianReal 0 1 := hs.symm
    _ = _ := by
      simp_rw [mul_pow]
      rw [integral_const_mul]
      have he : Real.sqrt (t : ℝ) ^ 4 = (t : ℝ) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt t.coe_nonneg]
      rw [he]
      rfl

omit [MeasurableSpace Ω] in
/-- The running maximum of the squares is the square of the running
maximum of absolute values. -/
theorem finiteRunningMaximum_square (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    finiteRunningMaximum (fun i ω => X i ω ^ 2) n ω =
      finiteRunningMaximum (fun i ω => |X i ω|) n ω ^ 2 := by
  induction n with
  | zero => exact (sq_abs _).symm
  | succ n ih =>
    change max _ (X (n + 1) ω ^ 2) = max _ |X (n + 1) ω| ^ 2
    rw [ih]
    have hn := finiteRunningMaximum_nonneg (f := fun i ω => |X i ω|) (fun _ _ => abs_nonneg _) n ω
    rcases le_total (finiteRunningMaximum (fun i ω => |X i ω|) n ω) |X (n + 1) ω| with h | h
    · rw [max_eq_right h, max_eq_right (by nlinarith [sq_abs (X (n + 1) ω), abs_nonneg (X (n + 1) ω)])]
      exact (sq_abs _).symm
    · rw [max_eq_left h, max_eq_left (by nlinarith [sq_abs (X (n + 1) ω), abs_nonneg (X (n + 1) ω)])]


/-- The Brownian squared running maximum has second moment O(T²), derived
from the actual square submartingale and Gaussian marginal scaling. -/
theorem brownianSupAbs_fourth_moment_le (hB : IsBrownianReal B P) (T : ℝ≥0) :
    MemLp (fun ω => brownianSupAbs B T ω ^ 2) 2 P ∧
      (∫ ω, brownianSupAbs B T ω ^ 4 ∂P) ≤ 4 * gaussianFourthMoment * (T : ℝ) ^ 2 := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  let q := TopologicalSpace.denseSeq (Icc (0 : ℝ≥0) T)
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq _
  let C := brownianContinuousModification hB
  have hC := brownianContinuousModification_isBrownian hB
  have hCsm := brownianContinuousModification_eval_stronglyMeasurable hB
  let X : ℕ → Ω → ℝ := fun n ω => C ω (q n) ^ 2
  let M : ℕ → Ω → ℝ := finiteRunningMaximum X
  have hM : ∀ n, MemLp (M n) 2 P := finiteRunningMaximum_memLp
    (fun n => brownian_square_memLp_two hC (q n))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => M n ω) atTop (𝓝 (brownianSupAbs B T ω ^ 2)) := by
    filter_upwards [brownianMaximum_eq_supAbs_ae hB T] with ω hω
    have habs : Tendsto (fun n => finiteRunningMaximum (fun i (_ : Unit) => |C ω (q i)|) n ())
        atTop (𝓝 (brownianMaximum hB T ω)) :=
      tendsto_finiteRunningMaximum_dense_norm q hq ((C ω).restrict (Icc 0 T))
    rw [hω] at habs
    have h := habs.pow 2
    convert! h using 1
    funext n
    rw [show M n ω = finiteRunningMaximum (fun i ω => |C ω (q i)|) n ω ^ 2 from
      finiteRunningMaximum_square (fun i ω => C ω (q i)) n ω]
    congr 1
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg₂ max ih rfl
  have hg := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hM n).aestronglyMeasurable) hlim
  have hb (n : ℕ) : (∫ ω, ‖M n ω‖ ^ 2 ∂P) ≤ 4 * gaussianFourthMoment * (T : ℝ) ^ 2 := by
    let S := (Finset.range (n + 1)).image (fun i => (q i : ℝ≥0))
    have hS : S.Nonempty := Finset.nonempty_range_add_one.image _
    have h := submartingale_finite_max_integral_sq_le (brownian_square_submartingale_natural hC hCsm)
      (brownian_square_memLp_two hC) (fun _ _ => sq_nonneg _) S hS T
      (fun s hs => by obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs; exact (q i).property.2)
      (C := (T : ℝ) ^ 2 * gaussianFourthMoment) (fun s hs => by
        simp only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num]
        rw [integral_fourth_brownian hC]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ s.coe_nonneg (by exact_mod_cast hs) 2) gaussianFourthMoment_nonneg)
    have heq (ω : Ω) : S.sup' hS (fun s => C ω s ^ 2) = M n ω := by
      rw [Finset.sup'_image]
      convert! (finiteRunningMaximum_eq_sup' X n ω).symm using 1
    change (∫ ω, (S.sup' hS (fun s => C ω s ^ 2)) ^ 2 ∂P) ≤ _ at h
    simp_rw [heq] at h
    simpa only [Real.norm_eq_abs, sq_abs, mul_assoc, mul_comm, mul_left_comm] using h
  have h := memLp_two_and_second_moment_le_of_ae_tendsto hM hg hlim hb
  simpa only [Real.norm_eq_abs, sq_abs, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using h


/-- The literal vector supremum is controlled by the coordinate suprema,
proved by taking dense-sample limits of the finite-dimensional inequality. -/
theorem euclideanBrownianSupNorm_sq_le_sum_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} (hB : IsEuclideanBrownian B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, brownianSupNorm B T ω ^ 2 ≤
      ∑ j, brownianSupAbs (fun t ω => B t ω j) T ω ^ 2 := by
  classical
  let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  let q := TopologicalSpace.denseSeq (Icc (0 : ℝ≥0) T)
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq _
  filter_upwards [hB.continuous_paths] with ω hω
  let f : C(ℝ≥0, EuclideanSpace ℝ ι) := ⟨fun t => B t ω, hω⟩
  let X : ℕ → Unit → EuclideanSpace ℝ ι := fun n _ => B (q n) ω
  have hv : Tendsto (fun n => finiteRunningMaximum (fun i (_ : Unit) => ‖X i ()‖) n ())
      atTop (𝓝 (brownianSupNorm B T ω)) := by
    have h := tendsto_finiteRunningMaximum_dense_norm_generic q hq (f.restrict (Icc 0 T))
    rw [continuousMap_restrict_norm_eq_sSup] at h
    exact h
  have hc (j : ι) : Tendsto (fun n => finiteRunningMaximum (fun i (_ : Unit) => |X i () j|) n ())
      atTop (𝓝 (brownianSupAbs (fun t ω => B t ω j) T ω)) := by
    let fj : C(ℝ≥0, ℝ) := ⟨fun t => B t ω j, (EuclideanSpace.proj j).continuous.comp hω⟩
    have h := tendsto_finiteRunningMaximum_dense_norm q hq (fj.restrict (Icc 0 T))
    rw [continuousMap_restrict_norm_eq_sSup] at h
    simp only [Real.norm_eq_abs] at h
    convert! h using 1
  have hs := tendsto_finsetSum Finset.univ (fun j _ => (hc j).pow 2)
  exact le_of_tendsto_of_tendsto (hv.pow 2) hs (Filter.Eventually.of_forall
    (fun n => finiteRunningMaximum_norm_sq_le_sum X n ()))

/-- Actual fourth moment of the Euclidean Brownian supremum is O(T²).
The constant is an explicit genuine standard Gaussian integral. -/
theorem euclideanBrownianSupNorm_fourth_moment_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} (hB : IsEuclideanBrownian B P) (T : ℝ≥0) :
    MemLp (fun ω => brownianSupNorm B T ω ^ 2) 2 P ∧
      (∫ ω, brownianSupNorm B T ω ^ 4 ∂P) ≤
        4 * (Fintype.card ι : ℝ) ^ 2 * gaussianFourthMoment * (T : ℝ) ^ 2 := by
  classical
  let G := brownianSupNorm B T
  let g : ι → Ω → ℝ := fun j => brownianSupAbs (fun t ω => B t ω j) T
  have hcoord (j : ι) := brownianSupAbs_fourth_moment_le (hB.coordinate j) T
  have hG : AEStronglyMeasurable G P :=
    (euclideanBrownianSupNorm_memLp_integral_sq_le hB T).1.aestronglyMeasurable
  have hpoint : ∀ᵐ ω ∂P, G ω ^ 4 ≤ (Fintype.card ι : ℝ) * ∑ j, g j ω ^ 4 := by
    filter_upwards [euclideanBrownianSupNorm_sq_le_sum_ae hB T] with ω hω
    calc
      _ = (G ω ^ 2) ^ 2 := by ring
      _ ≤ (∑ j, g j ω ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hω 2
      _ ≤ _ := by
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => g j ω ^ 2)
        have hp (j : ι) : (g j ω ^ 2) ^ 2 = g j ω ^ 4 := by ring
        simp_rw [hp] at hh
        simpa only [Finset.card_univ] using hh
  have hgi (j : ι) : Integrable (fun ω => g j ω ^ 4) P := by
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using (hcoord j).1.integrable_sq
  have hint : Integrable (fun ω => (Fintype.card ι : ℝ) * ∑ j, g j ω ^ 4) P :=
    (integrable_finsetSum _ (fun j _ => hgi j)).const_mul _
  have hfourMeas : AEStronglyMeasurable (fun ω => G ω ^ 4) P := by
    convert! hG.pow 4 using 1
  have htwoMeas : AEStronglyMeasurable (fun ω => G ω ^ 2) P := by
    convert! hG.pow 2 using 1
  have hfour : Integrable (fun ω => G ω ^ 4) P := by
    apply hint.mono' hfourMeas
    filter_upwards [hpoint] with ω hω
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg (by positivity : 0 ≤ G ω ^ 4)] using hω
  refine ⟨(memLp_two_iff_integrable_sq htwoMeas).mpr ?_, ?_⟩
  · simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hfour
  · calc
      _ ≤ ∫ ω, (Fintype.card ι : ℝ) * ∑ j, g j ω ^ 4 ∂P := integral_mono_ae hfour hint hpoint
      _ = (Fintype.card ι : ℝ) * ∑ j, ∫ ω, g j ω ^ 4 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ (fun j _ => hgi j)]
      _ ≤ (Fintype.card ι : ℝ) * ∑ _ : ι, 4 * gaussianFourthMoment * (T : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun j _ => (hcoord j).2)
      _ = _ := by simp; ring


/-- The bad-noise event has probability O(T²), with no maximal-moment
assumption. This is the localization bound needed for the actual generator. -/
theorem euclideanBrownianSupNorm_tail_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} (hB : IsEuclideanBrownian B P)
    (T : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    P.real {ω | R < brownianSupNorm B T ω} ≤
      (4 * (Fintype.card ι : ℝ) ^ 2 * gaussianFourthMoment * (T : ℝ) ^ 2) / R ^ 4 := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure
  obtain ⟨hL, hb⟩ := euclideanBrownianSupNorm_fourth_moment_le hB T
  have hint : Integrable (fun ω => brownianSupNorm B T ω ^ 4) P := by
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hL.integrable_sq
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => by positivity : ∀ ω, 0 ≤ brownianSupNorm B T ω ^ 4)) hint (R ^ 4)
  have hsubset : {ω | R < brownianSupNorm B T ω} ⊆
      {ω | R ^ 4 ≤ brownianSupNorm B T ω ^ 4} := by
    intro ω hω
    exact pow_le_pow_left₀ hR.le hω.le 4
  have hprob := measureReal_mono (μ := P) hsubset
  apply (le_div_iff₀ (pow_pos hR 4)).mpr
  have hmul := mul_le_mul_of_nonneg_left hprob (pow_nonneg hR.le 4)
  simpa only [mul_comm] using hmul.trans (hm.trans hb)

end CutoffRigidity
