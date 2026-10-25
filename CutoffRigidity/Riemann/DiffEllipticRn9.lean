module

public import CutoffRigidity.Riemann.DiffEllipticRn8

/-! # Localization of the coefficients
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

/-- The localized coefficient `ψ A + (1-ψ) δ`. -/
noncomputable def locCoeff (ψ : E → ℝ) (A : ι → ι → E → ℝ) (i j : ι) (x : E) : ℝ :=
  ψ x * A i j x + (1 - ψ x) * (if i = j then 1 else 0)

theorem exists_localized_coeff {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {K' : Set E} (hK' : IsCompact K') (hK'Ω : K' ⊆ Ω) (N : ℕ) :
    ∃ (ψ : E → ℝ) (θ Kb : ℝ), IsTest Ω ψ ∧ (∃ V : Set E, IsOpen V ∧ K' ⊆ V ∧ ∀ x ∈ V, ψ x = 1) ∧
      0 < θ ∧ Ell (locCoeff ψ A) θ Kb N ∧
      (∀ i j, IsTest Ω (fun x => ψ x * A i j x)) := by
  obtain ⟨ψ, hψ, ⟨V, hV, hKV, hV1⟩, h01⟩ := exists_cutoff_nhds hK' hΩ hK'Ω
  have hhat : ∀ i j, ContDiff ℝ ∞ (fun x => ψ x * A i j x) := fun i j =>
    contDiff_mul_of_contDiffOn hΩ hψ.1 hψ.2.2 (hAs i j)
  have htest : ∀ i j, IsTest Ω (fun x => ψ x * A i j x) := fun i j =>
    ⟨hhat i j, hψ.2.1.mul_right, tsupport_mul_subset_left.trans hψ.2.2⟩
  obtain ⟨c0, hc0, hell⟩ := exists_uniform_ellipticity
    (fun i j => (hAs i j).continuousOn) hAell hψ.2.1 hψ.2.2
  have hsmooth : ∀ i j, ContDiff ℝ ∞ (locCoeff ψ A i j) := fun i j => by
    unfold locCoeff
    exact (hhat i j).add ((contDiff_const.sub hψ.1).mul contDiff_const)
  have hform : ∀ i j, locCoeff ψ A i j =
      fun x => (if i = j then (1 : ℝ) else 0) + ψ x * (A i j x - (if i = j then 1 else 0)) := by
    intro i j; funext x; unfold locCoeff; ring
  have hfs : ∀ i j, ContDiff ℝ ∞ (fun x => ψ x * (A i j x - (if i = j then (1 : ℝ) else 0))) :=
    fun i j => contDiff_mul_of_contDiffOn hΩ hψ.1 hψ.2.2
      ((hAs i j).sub contDiffOn_const)
  have hfc : ∀ i j, HasCompactSupport
      (fun x => ψ x * (A i j x - (if i = j then (1 : ℝ) else 0))) :=
    fun i j => hψ.2.1.mul_right
  have hB : ∀ i j, ∃ B : ℝ, ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (locCoeff ψ A i j) x‖ ≤ B := by
    intro i j
    rw [hform]
    exact bound_const_add_compact (hfs i j) (hfc i j) _ N
  choose B hB using hB
  set Kb : ℝ := ∑ i, ∑ j, max (B i j) 0 with hKb
  refine ⟨ψ, min 1 c0, Kb, hψ, ⟨V, hV, hKV, hV1⟩, lt_min one_pos hc0, ⟨hsmooth, ?_, ?_, ?_⟩, htest⟩
  · intro i j x
    unfold locCoeff
    by_cases hx : x ∈ tsupport ψ
    · rw [hAsym i j x (hψ.2.2 hx)]
      simp only [eq_comm (a := i) (b := j)]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp [eq_comm (a := i) (b := j)]
  · intro x ξ
    have hq : ∑ i, ∑ j, locCoeff ψ A i j x * ξ j * ξ i =
        ψ x * (∑ i, ∑ j, A i j x * ξ j * ξ i) + (1 - ψ x) * ∑ i, ξ i ^ 2 := by
      unfold locCoeff
      have e : ∀ i j, (ψ x * A i j x + (1 - ψ x) * (if i = j then (1 : ℝ) else 0)) * ξ j * ξ i =
          ψ x * (A i j x * ξ j * ξ i) + (1 - ψ x) * ((if i = j then (1 : ℝ) else 0) * ξ j * ξ i) := by
        intro i j; ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [sq]
    rw [hq]
    have h0 := (h01 x).1
    have h1 := (h01 x).2
    have hS : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    by_cases hx : x ∈ tsupport ψ
    · have h2 := hell x hx ξ
      have hm1 : min 1 c0 ≤ 1 := min_le_left _ _
      have hm2 : min 1 c0 ≤ c0 := min_le_right _ _
      nlinarith [mul_nonneg h0 hS, mul_nonneg (sub_nonneg.2 h1) hS,
        mul_nonneg h0 (sub_nonneg.2 h2), mul_nonneg h0 (mul_nonneg hS (sub_nonneg.2 hm2)),
        mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hS (sub_nonneg.2 hm1))]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      have hm1 : min 1 c0 ≤ 1 := min_le_left _ _
      nlinarith [mul_nonneg hS (sub_nonneg.2 hm1)]
  · intro i j k hk x
    have h1 : B i j ≤ max (B i j) 0 := le_max_left _ _
    have h2 : max (B i j) 0 ≤ Kb := by
      calc max (B i j) 0 ≤ ∑ j', max (B i j') 0 :=
            Finset.single_le_sum (f := fun j' => max (B i j') 0) (fun _ _ => le_max_right _ _)
              (Finset.mem_univ j)
        _ ≤ Kb := Finset.single_le_sum (f := fun i' => ∑ j', max (B i' j') 0)
            (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)
    exact (hB i j k hk x).trans (h1.trans h2)

/-- The local weak equation on `Ω`. -/
def LocEq (Ω : Set E) (A : ι → ι → E → ℝ) (u' : ι → E → ℝ) (F : E → ℝ) : Prop :=
  ∀ φ, IsTest Ω φ → ∑ i, ∑ j, ∫ x, A i j x * u' j x * pd (b i) φ x = ∫ x, F x * φ x

theorem isTest_mul_pd {Ω : Set E} {φ : E → ℝ} (hφ : IsTest Ω φ) {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (v : E) : IsTest Ω (fun x => pd v g x * φ x) :=
  hφ.mul (contDiff_pd hg v)

theorem localized_weakEq_of {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    {u : E → ℝ} {u' : ι → E → ℝ} (hu : LocH1 b Ω u u') {F : E → ℝ} (hF : LocL2 Ω F)
    (heq : LocEq b Ω A u' F) {χ₁ : E → ℝ} (hχ₁ : IsTest Ω χ₁) {ψ : E → ℝ}
    {V : Set E} (hV : IsOpen V) (hKV : tsupport χ₁ ⊆ V) (hV1 : ∀ x ∈ V, ψ x = 1)
    (hAhat : ∀ i j, IsTest Ω (fun x => ψ x * A i j x)) :
    WeakEq b (locCoeff ψ A) (fun x => χ₁ x * u x)
        (fun x => χ₁ x * F x - ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x)
        (fun i x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) := by
  intro φ hφ
  have hw' : ∀ j, HasWDeriv Set.univ (b j) (fun x => χ₁ x * u x)
      (fun x => χ₁ x * u' j x + pd (b j) χ₁ x * u x) :=
    fun j => hasWDeriv_cutoff_mul hΩ (hu.wd j) hχ₁
  have hw'm : ∀ j, MemLp (fun x => χ₁ x * u' j x + pd (b j) χ₁ x * u x) 2 volume :=
    fun j => (memLp_mul_test (hu.l2' j) hχ₁).add (memLp_mul_test hu.l2 (hχ₁.pd (b j)))
  have hwae : ∀ j, wd (b j) (fun x => χ₁ x * u x) =ᵐ[volume]
      fun x => χ₁ x * u' j x + pd (b j) χ₁ x * u x := fun j => (wd_spec (hw' j) (hw'm j)).2.2
  have ha : ∀ i j, MemLp (fun x => ψ x * A i j x * u' j x) 2 volume :=
    fun i j => memLp_mul_test (hu.l2' j) (hAhat i j)
  have hc : ∀ i j, MemLp (fun x => ψ x * A i j x * u x) 2 volume :=
    fun i j => memLp_mul_test hu.l2 (hAhat i j)
  have t1 : ∀ i, IsTest Set.univ (fun x => χ₁ x * pd (b i) φ x) :=
    fun i => (hφ.pd (b i)).mul hχ₁.1
  have t2 : ∀ i, IsTest Set.univ (fun x => pd (b i) χ₁ x * φ x) :=
    fun i => isTest_mul_pd hφ hχ₁.1 (b i)
  have t3 : ∀ i j, IsTest Set.univ (fun x => pd (b j) χ₁ x * pd (b i) φ x) :=
    fun i j => isTest_mul_pd (hφ.pd (b i)) hχ₁.1 (b j)
  have hFm : MemLp (fun x => χ₁ x * F x) 2 volume := memLp_mul_test hF hχ₁
  -- the three families of integrals
  set P : ι → ι → ℝ := fun i j => ∫ x, (ψ x * A i j x * u' j x) * (χ₁ x * pd (b i) φ x) with hP
  set Q : ι → ι → ℝ := fun i j => ∫ x, (ψ x * A i j x * u' j x) * (pd (b i) χ₁ x * φ x) with hQ
  set R : ι → ι → ℝ := fun i j =>
    ∫ x, (ψ x * A i j x * u x) * (pd (b j) χ₁ x * pd (b i) φ x) with hR
  have iP : ∀ i j, Integrable (fun x => (ψ x * A i j x * u' j x) * (χ₁ x * pd (b i) φ x)) volume :=
    fun i j => integrable_mul_test (ha i j) (t1 i)
  have iQ : ∀ i j, Integrable (fun x => (ψ x * A i j x * u' j x) * (pd (b i) χ₁ x * φ x)) volume :=
    fun i j => integrable_mul_test (ha i j) (t2 i)
  have iR : ∀ i j, Integrable
      (fun x => (ψ x * A i j x * u x) * (pd (b j) χ₁ x * pd (b i) φ x)) volume :=
    fun i j => integrable_mul_test (hc i j) (t3 i j)
  -- Step 1
  have S1 : ∀ i j, ∫ x, locCoeff ψ A i j x * wd (b j) (fun x => χ₁ x * u x) x * pd (b i) φ x =
      P i j + R i j := by
    intro i j
    have e1 : ∫ x, locCoeff ψ A i j x * wd (b j) (fun x => χ₁ x * u x) x * pd (b i) φ x =
        ∫ x, ((ψ x * A i j x * u' j x) * (χ₁ x * pd (b i) φ x) +
          (ψ x * A i j x * u x) * (pd (b j) χ₁ x * pd (b i) φ x)) := by
      refine integral_congr_ae ?_
      filter_upwards [hwae j] with x hx
      rw [hx]
      by_cases hxK : x ∈ tsupport χ₁
      · have hψx : ψ x = 1 := hV1 x (hKV hxK)
        simp only [locCoeff, hψx]
        ring
      · have h0 : χ₁ x = 0 := image_eq_zero_of_notMem_tsupport hxK
        have h1 : pd (b j) χ₁ x = 0 := pd_eq_zero_of_notMem hxK _
        simp [h0, h1]
    rw [e1, integral_add (iP i j) (iR i j)]
  -- Step 2
  have hξ : IsTest Ω (fun x => χ₁ x * φ x) :=
    ⟨hχ₁.1.mul hφ.1, hφ.2.1.mul_left, (tsupport_mul_subset_left).trans hχ₁.2.2⟩
  have S2 : ∑ i, ∑ j, (P i j + Q i j) = ∫ x, χ₁ x * F x * φ x := by
    have h := heq _ hξ
    have e : ∀ i j, ∫ x, A i j x * u' j x * pd (b i) (fun x => χ₁ x * φ x) x = P i j + Q i j := by
      intro i j
      have e1 : ∫ x, A i j x * u' j x * pd (b i) (fun x => χ₁ x * φ x) x =
          ∫ x, ((ψ x * A i j x * u' j x) * (χ₁ x * pd (b i) φ x) +
            (ψ x * A i j x * u' j x) * (pd (b i) χ₁ x * φ x)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        beta_reduce
        rw [pd_mul (hχ₁.1.differentiable (by simp)) (hφ.1.differentiable (by simp))]
        by_cases hxK : x ∈ tsupport χ₁
        · have hψx : ψ x = 1 := hV1 x (hKV hxK)
          rw [hψx]; ring
        · have h0 : χ₁ x = 0 := image_eq_zero_of_notMem_tsupport hxK
          have h1 : pd (b i) χ₁ x = 0 := pd_eq_zero_of_notMem hxK _
          simp [h0, h1]
      rw [e1, integral_add (iP i j) (iQ i j)]
    simp only [e] at h
    rw [h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- Step 3
  have T3a : ∫ x, (χ₁ x * F x - ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) * φ x =
      (∫ x, χ₁ x * F x * φ x) - ∑ i, ∑ j, Q i j := by
    have e1 : (fun x => (χ₁ x * F x - ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) * φ x) =
        fun x => χ₁ x * F x * φ x -
          ∑ i, ∑ j, (ψ x * A i j x * u' j x) * (pd (b i) χ₁ x * φ x) := by
      funext x
      rw [sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [e1, integral_sub (integrable_mul_test hFm ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩)
      (integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iQ i j))),
      integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iQ i j))]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => integral_finset_sum _ (fun j _ => iQ i j))
  have T3b : ∀ i, ∫ x, (u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) * pd (b i) φ x =
      ∑ j, R i j := by
    intro i
    have e1 : (fun x => (u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) * pd (b i) φ x) =
        fun x => ∑ j, (ψ x * A i j x * u x) * (pd (b j) χ₁ x * pd (b i) φ x) := by
      funext x
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [e1, integral_finset_sum _ (fun j _ => iR i j)]
  have hφ' : IsTest Set.univ φ := ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
  simp only [S1, T3a, T3b]
  have hS2 := S2
  simp only [Finset.sum_add_distrib] at hS2 ⊢
  linarith

theorem localized_weakEq {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {u : E → ℝ} {u' : ι → E → ℝ} (hu : LocH1 b Ω u u') {F : E → ℝ} (hF : LocL2 Ω F)
    (heq : LocEq b Ω A u' F) {χ₁ : E → ℝ} (hχ₁ : IsTest Ω χ₁) (N : ℕ) :
    ∃ (ψ : E → ℝ) (θ Kb : ℝ) (AR : ι → ι → E → ℝ), IsTest Ω ψ ∧ 0 < θ ∧ Ell AR θ Kb N ∧
      (∀ i j, IsTest Ω (fun x => ψ x * A i j x)) ∧
      WeakEq b AR (fun x => χ₁ x * u x)
        (fun x => χ₁ x * F x - ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x)
        (fun i x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) := by
  obtain ⟨ψ, θ, Kb, hψ, ⟨V, hV, hKV, hV1⟩, hθ, hEll, hAhat⟩ :=
    exists_localized_coeff hΩ hAs hAsym hAell hχ₁.2.1 hχ₁.2.2 N
  exact ⟨ψ, θ, Kb, locCoeff ψ A, hψ, hθ, hEll, hAhat,
    localized_weakEq_of b hΩ hu hF heq hχ₁ hV hKV hV1 hAhat⟩

end CutoffRigidity.Riemann.Diff
