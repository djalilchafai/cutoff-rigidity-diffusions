module
public import CutoffRigidity.Transport
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Regular

/-! # Genuine compact-space transport strong duality

Riesz's positive extension theorem and Riesz–Markov representation construct
an actual coupling from the dual budget. No primal-dual equality is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory Set
open scoped Topology CompactlySupported
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

local instance : IsOrderedAddMonoid C(X×Y,ℝ) where
  add_le_add_left a b h c := fun z => add_le_add_left (h z) (c z)

@[expose] def transportMarginalSum : C(X,ℝ) × C(Y,ℝ) →ₗ[ℝ] C(X×Y,ℝ) where
  toFun p := p.1.comp ⟨Prod.fst,continuous_fst⟩+p.2.comp ⟨Prod.snd,continuous_snd⟩
  map_add' p q := by ext z; simp; ring
  map_smul' r p := by ext z; simp

/-- The positive cone enlarged by the desired cost budget. -/
@[expose] def transportBudgetCone (c : C(X×Y,ℝ)) (K : ℝ) : PointedCone ℝ C(X×Y,ℝ) where
  carrier := {h | ∃ a : ℝ, 0 ≤ a ∧ ∀ z, a*(K-c z) ≤ h z}
  zero_mem' := ⟨0,le_rfl,by simp⟩
  add_mem' := by
    rintro f g ⟨a,ha,hf⟩ ⟨b,hb,hg⟩
    refine ⟨a+b,add_nonneg ha hb,?_⟩
    intro z
    have h1 := hf z
    have h2 := hg z
    change (a+b)*(K-c z) ≤ f z+g z
    nlinarith
  smul_mem' := by
    rintro r f ⟨a,ha,hf⟩
    refine ⟨(r:ℝ)*a,mul_nonneg r.property ha,?_⟩
    intro z
    change ((r:ℝ)*a)*(K-c z) ≤ (r:ℝ)*f z
    nlinarith [mul_le_mul_of_nonneg_left (hf z) r.property]

/-- Integration against the independent product, on continuous functions. -/
@[expose] noncomputable def compactProductIntegral (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : C(X×Y,ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ z, f z ∂μ.prod ν
  map_add' f g := integral_add (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' r f := integral_smul r f

theorem compactProductIntegral_marginalSum (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : C(X,ℝ)) (g : C(Y,ℝ)) :
    compactProductIntegral μ ν (transportMarginalSum (f,g)) =
      (∫ x, f x ∂μ)+(∫ y,g y ∂ν) := by
  change (∫ z : X×Y, f z.1+g z.2 ∂μ.prod ν) = _
  have hfi : Integrable (fun z : X×Y => f z.1) (μ.prod ν) :=
    (f.continuous.comp continuous_fst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable (fun z : X×Y => g z.2) (μ.prod ν) :=
    (g.continuous.comp continuous_snd).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add hfi hgi]
  congr 1
  · have hh := integral_map (μ := μ.prod ν) measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
    simpa using hh.symm
  · have hh := integral_map (μ := μ.prod ν) measurable_snd.aemeasurable g.continuous.aestronglyMeasurable
    simpa using hh.symm

set_option maxHeartbeats 800000 in
/-- The dual budget yields a genuine positive extension preserving all
marginal integrals and satisfying the actual cost budget. -/
theorem exists_positive_transport_functional
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : C(X×Y,ℝ)) (K : ℝ)
    (hDual : ∀ (f : C(X,ℝ)) (g : C(Y,ℝ)),
      (∀ x y, f x+g y ≤ c (x,y)) → (∫ x,f x ∂μ)+(∫ y,g y ∂ν) ≤ K) :
    ∃ L : C(X×Y,ℝ) →ₚ[ℝ] ℝ,
      (∀ f g, L (transportMarginalSum (f,g)) = (∫ x,f x ∂μ)+(∫ y,g y ∂ν)) ∧
      L c ≤ K := by
  let S := (transportMarginalSum (X := X) (Y := Y)).range
  let F : C(X×Y,ℝ) →ₗ.[ℝ] ℝ := ⟨S,(compactProductIntegral μ ν).domRestrict S⟩
  have hPos : ∀ h : F.domain, (h : C(X×Y,ℝ)) ∈ transportBudgetCone c K → 0 ≤ F h := by
    intro h hh
    obtain ⟨a,ha,hh⟩ := hh
    obtain ⟨⟨f,g⟩,hfg⟩ := h.property
    have hF : F h = (∫ x,f x ∂μ)+(∫ y,g y ∂ν) := by
      change compactProductIntegral μ ν h.val = _
      rw [← hfg,compactProductIntegral_marginalSum]
    have hRep (x : X) (y : Y) : h.val (x,y) = f x+g y := by
      rw [← hfg]; rfl
    by_cases ha0 : a = 0
    · apply integral_nonneg
      intro z
      have hh' := hh z
      simpa [ha0] using hh'
    have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let f' : C(X,ℝ) := ContinuousMap.const X K - a⁻¹ • f
    let g' : C(Y,ℝ) := -(a⁻¹ • g)
    have hd : ∀ x y, f' x+g' y ≤ c (x,y) := by
      intro x y
      have hh' := hh (x,y)
      rw [hRep] at hh'
      change K-a⁻¹*f x+ -(a⁻¹*g y) ≤ c (x,y)
      have hinv : 0 < a⁻¹ := inv_pos.mpr hap
      have hm := mul_le_mul_of_nonneg_left hh' hinv.le
      field_simp at hm ⊢
      nlinarith
    have hd' := hDual f' g' hd
    have hf' : (∫ x,f' x ∂μ) = K-a⁻¹*(∫ x,f x ∂μ) := by
      change (∫ x,K-a⁻¹*f x ∂μ) = _
      rw [integral_sub (integrable_const K) ((f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _),integral_const_mul]
      simp
    have hg' : (∫ y,g' y ∂ν) = -(a⁻¹*(∫ y,g y ∂ν)) := by
      change (∫ y,-(a⁻¹*g y) ∂ν) = _
      rw [integral_neg,integral_const_mul]
    rw [hf',hg'] at hd'
    rw [hF]
    have hInv := inv_pos.mpr hap
    nlinarith
  have hDense : ∀ y : C(X×Y,ℝ), ∃ x : F.domain,
      (x : C(X×Y,ℝ))+y ∈ transportBudgetCone c K := by
    intro y
    let p : C(X,ℝ)×C(Y,ℝ) := (ContinuousMap.const X ‖y‖,0)
    refine ⟨⟨transportMarginalSum p,⟨p,rfl⟩⟩,0,le_rfl,?_⟩
    intro z
    change 0*(K-c z) ≤ (transportMarginalSum p) z+y z
    change 0*(K-c z) ≤ ‖y‖+0+y z
    have hy := ContinuousMap.norm_coe_le_norm y z
    have hy' : -‖y‖ ≤ y z := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hy)).1
    linarith
  obtain ⟨L,hEq,hNonneg⟩ := riesz_extension (transportBudgetCone c K) F hPos hDense
  have hLpos (h : C(X×Y,ℝ)) (hh : 0 ≤ h) : 0 ≤ L h := by
    apply hNonneg h
    exact ⟨0,le_rfl,fun z => by simpa using hh z⟩
  let Lp := PositiveLinearMap.mk₀ L hLpos
  have hMarg (f : C(X,ℝ)) (g : C(Y,ℝ)) :
      Lp (transportMarginalSum (f,g)) = (∫ x,f x ∂μ)+(∫ y,g y ∂ν) := by
    have hh := hEq ⟨transportMarginalSum (f,g),⟨(f,g),rfl⟩⟩
    change L (transportMarginalSum (f,g)) = _
    exact hh.trans (compactProductIntegral_marginalSum μ ν f g)
  refine ⟨Lp,hMarg,?_⟩
  have hBudget := hNonneg (ContinuousMap.const (X×Y) K-c) ⟨1,zero_le_one,by intro z; simp⟩
  have hConst : L (ContinuousMap.const (X×Y) K) = K := by
    have hh := hMarg (ContinuousMap.const X K) 0
    have he : transportMarginalSum (ContinuousMap.const X K,0) = ContinuousMap.const (X×Y) K := by ext z; simp [transportMarginalSum]
    rw [he] at hh
    have hh' : Lp (ContinuousMap.const (X×Y) K) = K := by simpa using hh
    convert! hh' using 1
  rw [map_sub,hConst] at hBudget
  change L c ≤ K
  linarith

set_option maxHeartbeats 800000 in
/-- Compact Kantorovich strong duality, in budget form: all actual
continuous dual tests below the cost produce an actual coupling attaining
the budget. The measure is constructed by positive extension and RMK. -/
theorem exists_compact_transport_coupling_of_dual_budget
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.PseudoMetrizableSpace Y]
    (c : C(X×Y,ℝ)) (K : ℝ)
    (hDual : ∀ (f : C(X,ℝ)) (g : C(Y,ℝ)),
      (∀ x y, f x+g y ≤ c (x,y)) → (∫ x,f x ∂μ)+(∫ y,g y ∂ν) ≤ K) :
    ∃ π : Measure (X×Y), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∫ z,c z ∂π) ≤ K := by
  obtain ⟨L,hMarg,hCost⟩ := exists_positive_transport_functional μ ν c K hDual
  let F : C_c(X×Y,ℝ) →ₗ[ℝ] ℝ :=
    { toFun f := L f.toContinuousMap
      map_add' f g := by change L (f.toContinuousMap+g.toContinuousMap) = _; exact map_add L _ _
      map_smul' r f := by change L (r • f.toContinuousMap) = _; exact map_smul L r _ }
  let Λ : C_c(X×Y,ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ F (by
    intro f hf
    exact L.map_nonneg hf)
  let π := RealRMK.rieszMeasure Λ
  have hRep (f : C(X×Y,ℝ)) : (∫ z,f z ∂π) = L f := by
    have hh := RealRMK.integral_rieszMeasure Λ
      (⟨f,HasCompactSupport.of_compactSpace f⟩ : C_c(X×Y,ℝ))
    convert! hh using 1
  have hOne : L (1 : C(X×Y,ℝ)) = 1 := by
    have hh := hMarg (1 : C(X,ℝ)) (0 : C(Y,ℝ))
    have he : transportMarginalSum ((1 : C(X,ℝ)),(0 : C(Y,ℝ))) = 1 := by
      ext z
      simp [transportMarginalSum]
    rw [he] at hh
    simpa using hh
  have hπprob : IsProbabilityMeasure π := by
    apply isProbabilityMeasure_iff_real.mpr
    have hh := hRep 1
    rw [hOne] at hh
    simpa using hh
  let := hπprob
  have hFirst : π.map Prod.fst = μ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := π) (f := fun x => f x) measurable_fst.aemeasurable
      (show AEStronglyMeasurable (fun x => f x) (π.map Prod.fst) from f.continuous.aestronglyMeasurable)]
    let A : C(X×Y,ℝ) := f.toContinuousMap.comp ⟨Prod.fst,continuous_fst⟩
    have he : A = transportMarginalSum (f.toContinuousMap,(0 : C(Y,ℝ))) := by
      ext z
      simp [A,transportMarginalSum]
    have hh := hRep A
    rw [he,hMarg] at hh
    convert! hh using 1
    · apply integral_congr_ae; filter_upwards with z; simp [transportMarginalSum]
    · simp
  have hSecond : π.map Prod.snd = ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := π) (f := fun x => f x) measurable_snd.aemeasurable
      (show AEStronglyMeasurable (fun x => f x) (π.map Prod.snd) from f.continuous.aestronglyMeasurable)]
    let A : C(X×Y,ℝ) := f.toContinuousMap.comp ⟨Prod.snd,continuous_snd⟩
    have he : A = transportMarginalSum ((0 : C(X,ℝ)),f.toContinuousMap) := by
      ext z
      simp [A,transportMarginalSum]
    have hh := hRep A
    rw [he,hMarg] at hh
    convert! hh using 1
    · apply integral_congr_ae; filter_upwards with z; simp [transportMarginalSum]
    · simp
  exact ⟨π,hπprob,hFirst,hSecond,(hRep c).le.trans hCost⟩

end CutoffRigidity
