module

public import CutoffRigidity.Riemann.DiffEllipticRn13

/-! # Caccioppoli inequality
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

/-- Uniform sup bound for a finite family of smooth compactly supported functions. -/
theorem exists_sup_bound_family {J : Type*} [Fintype J] {a : J → E → ℝ}
    (ha : ∀ j, ContDiff ℝ ∞ (a j)) (hc : ∀ j, HasCompactSupport (a j)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j x, |a j x| ≤ K := by
  have : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |a j x| ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := exists_iteratedFDeriv_bound (ha j) (hc j) 0
    refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
    have := hB 0 le_rfl x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  choose B hB0 hB using this
  refine ⟨∑ j, B j, Finset.sum_nonneg (fun j _ => hB0 j), fun j x => (hB j x).trans ?_⟩
  exact Finset.single_le_sum (f := B) (fun i _ => hB0 i) (Finset.mem_univ j)

theorem l2_mul_le {a g : E → ℝ} {K : ℝ} (hK : 0 ≤ K) (ha : ∀ x, |a x| ≤ K)
    (hg : MemLp g 2 volume) (hag : MemLp (fun x => a x * g x) 2 volume) :
    l2 (fun x => a x * g x) ≤ K * l2 g :=
  l2_le_of_abs_le hg hag hK (fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ha x) (abs_nonneg _))

theorem memLp_finset_sum' {J : Type*} (s : Finset J) {f : J → E → ℝ}
    (hf : ∀ j ∈ s, MemLp (f j) 2 volume) : MemLp (fun x => ∑ j ∈ s, f j x) 2 volume := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (MemLp.zero : MemLp (fun _ : E => (0 : ℝ)) 2 volume)
  | insert a s ha ih =>
    have := (hf a (Finset.mem_insert_self a s)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
    simp [Finset.sum_insert ha]

/-- The energy identity behind the Caccioppoli inequality. -/
theorem caccioppoli_identity {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {u : E → ℝ} {u' : ι → E → ℝ} (hu : LocH1 b Ω u u') {F : E → ℝ} (hF : LocL2 Ω F)
    (heq : LocEq b Ω A u' F) {χ χ₁ : E → ℝ} (hχ : IsTest Ω χ) (hχ₁ : IsTest Ω χ₁)
    {V₁ : Set E} (hV₁ : IsOpen V₁) (hKV₁ : tsupport χ ⊆ V₁) (hV₁1 : ∀ x ∈ V₁, χ₁ x = 1) :
    ∑ i, ∑ j, ∫ x, A i j x * u' j x * (χ x * χ x * u' i x + pd (b i) (fun y => χ y * χ y) x * u x) =
      ∫ x, F x * (χ x * χ x * u x) := by
  obtain ⟨ψ, θ, Kb, hψ, ⟨V, hV, hKV, hV1⟩, hθ, hEll, hAhat⟩ :=
    exists_localized_coeff hΩ hAs hAsym hAell hχ₁.2.1 hχ₁.2.2 0
  have hWeak := localized_weakEq_of b hΩ hu hF heq hχ₁ hV hKV hV1 hAhat
  set ξ : E → ℝ := fun x => χ x * χ x with hξdef
  have hξ : ContDiff ℝ ∞ ξ := hχ.1.mul hχ.1
  have hξc : HasCompactSupport ξ := hχ.2.1.mul_left
  have hξts : tsupport ξ ⊆ tsupport χ := tsupport_mul_subset_left
  obtain ⟨Kξ, hKξ⟩ := exists_iteratedFDeriv_bound hξ hξc 0
  have hξb : ∀ x, ‖ξ x‖ ≤ Kξ := fun x => by
    simpa using hKξ 0 le_rfl x
  have hdξb : ∀ i, ∃ K : ℝ, ∀ x, ‖pd (b i) ξ x‖ ≤ K := fun i => by
    obtain ⟨K, hK⟩ := exists_iteratedFDeriv_bound (contDiff_pd hξ (b i))
      (hξc.fderiv_apply ℝ (b i)) 0
    exact ⟨K, fun x => by simpa using hK 0 le_rfl x⟩
  choose Kd hKd using hdξb
  have hSob1 : Sob b 1 (fun x => χ₁ x * u x) := hu.locSob b hΩ χ₁ hχ₁
  obtain ⟨hw1m, hwd1⟩ := Sob.one_wd b hSob1
  have hwae : ∀ j, wd (b j) (fun x => χ₁ x * u x) =ᵐ[volume]
      fun x => χ₁ x * u' j x + pd (b j) χ₁ x * u x := fun j =>
    (wd_spec (hasWDeriv_cutoff_mul hΩ (hu.wd j) hχ₁)
      ((memLp_mul_test (hu.l2' j) hχ₁).add (memLp_mul_test hu.l2 (hχ₁.pd (b j))))).2.2
  have hφm : MemLp (fun x => ξ x * (χ₁ x * u x)) 2 volume :=
    memLp_mul_of_bound hξ.continuous hξb hw1m
  have hφs : AESupp (fun x => ξ x * (χ₁ x * u x)) := by
    obtain ⟨R, hR⟩ := exists_norm_bound_of_compactSupport hξc
    exact ⟨R, Filter.Eventually.of_forall fun x hx => by simp [hR x hx]⟩
  have hφ' : ∀ i, HasWDeriv Set.univ (b i) (fun x => ξ x * (χ₁ x * u x))
      (fun x => ξ x * wd (b i) (fun x => χ₁ x * u x) x + pd (b i) ξ x * (χ₁ x * u x)) :=
    fun i => (hwd1 i).1.mul_smooth isOpen_univ hξ
  have hφ'm : ∀ i, MemLp (fun x => ξ x * wd (b i) (fun x => χ₁ x * u x) x +
      pd (b i) ξ x * (χ₁ x * u x)) 2 volume := fun i =>
    (memLp_mul_of_bound hξ.continuous hξb (hwd1 i).2).add
      (memLp_mul_of_bound (contDiff_pd hξ (b i)).continuous (hKd i) hw1m)
  -- `L²` bounds for `F̃`, `G̃`
  have hFm : MemLp (fun x => χ₁ x * F x - ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) 2
      volume := by
    refine (memLp_mul_test hF hχ₁).sub (memLp_finset_sum' _ (fun i _ => memLp_finset_sum' _
      (fun j _ => ?_)))
    exact memLp_mul_test (hu.l2' j) ⟨(hAhat i j).1.mul (contDiff_pd hχ₁.1 _),
      (hAhat i j).2.1.mul_right, tsupport_mul_subset_left.trans (hAhat i j).2.2⟩
  have hGm : ∀ i, MemLp (fun x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) 2 volume := by
    intro i
    have : (fun x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) =
        fun x => ∑ j, ψ x * A i j x * pd (b j) χ₁ x * u x := by
      funext x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]
    refine memLp_finset_sum' _ (fun j _ => ?_)
    exact memLp_mul_test hu.l2 ⟨(hAhat i j).1.mul (contDiff_pd hχ₁.1 _),
      (hAhat i j).2.1.mul_right, tsupport_mul_subset_left.trans (hAhat i j).2.2⟩
  have E1 := WeakEq.extend b hEll hSob1 hFm hGm hWeak hφm hφs hφ' hφ'm
  -- pointwise facts on `tsupport χ`
  have hV1' : ∀ x ∈ tsupport χ, χ₁ x = 1 ∧ (∀ v, pd v χ₁ x = 0) ∧ ψ x = 1 := by
    intro x hx
    refine ⟨hV₁1 x (hKV₁ hx), fun v => pd_eq_zero_of_eventually_one hV₁ hV₁1 (hKV₁ hx) v, ?_⟩
    have : x ∈ tsupport χ₁ := subset_tsupport _ (by simp [hV₁1 x (hKV₁ hx)])
    exact hV1 x (hKV this)
  have hoff : ∀ x, x ∉ tsupport χ → ξ x = 0 ∧ ∀ v, pd v ξ x = 0 := fun x hx =>
    ⟨by simp [hξdef, image_eq_zero_of_notMem_tsupport hx],
      fun v => pd_eq_zero_of_notMem (fun h => hx (hξts h)) v⟩
  have eL : ∀ i j, ∫ x, locCoeff ψ A i j x * wd (b j) (fun x => χ₁ x * u x) x *
      (ξ x * wd (b i) (fun x => χ₁ x * u x) x + pd (b i) ξ x * (χ₁ x * u x)) =
      ∫ x, A i j x * u' j x * (χ x * χ x * u' i x + pd (b i) (fun y => χ y * χ y) x * u x) := by
    intro i j
    refine integral_congr_ae ?_
    filter_upwards [hwae i, hwae j] with x hxi hxj
    by_cases hx : x ∈ tsupport χ
    · obtain ⟨e1, e2, e3⟩ := hV1' x hx
      rw [hxi, hxj, e1, e2, e2]
      simp only [locCoeff, e3, hξdef]
      ring
    · obtain ⟨e1, e2⟩ := hoff x hx
      have e1' : χ x * χ x = 0 := e1
      have e2' : pd (b i) (fun y => χ y * χ y) x = 0 := e2 (b i)
      rw [e1, e2 (b i)]
      simp [e1', e2']
  have eF : ∫ x, (χ₁ x * F x - ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) *
      (ξ x * (χ₁ x * u x)) = ∫ x, F x * (χ x * χ x * u x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport χ
    · obtain ⟨e1, e2, e3⟩ := hV1' x hx
      simp only [e1, e2, hξdef]
      simp
    · obtain ⟨e1, e2⟩ := hoff x hx
      simp [e1, show χ x * χ x = 0 from e1]
  have eG : ∀ i, ∫ x, (u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) *
      (ξ x * wd (b i) (fun x => χ₁ x * u x) x + pd (b i) ξ x * (χ₁ x * u x)) = 0 := by
    intro i
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport χ
    · obtain ⟨e1, e2, e3⟩ := hV1' x hx
      simp [e2]
    · obtain ⟨e1, e2⟩ := hoff x hx
      simp [e1, e2 (b i)]
  simp only [eL, eF, eG, Finset.sum_const_zero, add_zero] at E1
  exact E1

theorem two_sq_bound (p q : ℝ) : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
  nlinarith [sq_nonneg (p - q)]

set_option maxHeartbeats 1600000 in
/-- Caccioppoli inequality (local `H¹` bound in terms of `L²` norms). -/
theorem caccioppoli {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {χ : E → ℝ} (hχ : IsTest Ω χ) :
    ∃ (χ₁ : E → ℝ) (C : ℝ), IsTest Ω χ₁ ∧ 0 ≤ C ∧
      ∀ (u : E → ℝ) (u' : ι → E → ℝ) (F : E → ℝ), LocH1 b Ω u u' → LocL2 Ω F →
        LocEq b Ω A u' F →
        sobSq b 1 (fun x => χ x * u x) ≤
          C * (sobSq b 0 (fun x => χ₁ x * F x) + sobSq b 0 (fun x => χ₁ x * u x)) := by
  obtain ⟨χ₁, hχ₁, ⟨V₁, hV₁, hKV₁, hV₁1⟩, -⟩ := exists_cutoff_nhds hχ.2.1 hΩ hχ.2.2
  obtain ⟨ψ₀, hψ₀, ⟨V₀, hV₀, hKV₀, hV₀1⟩, -⟩ := exists_cutoff_nhds hχ.2.1 hΩ hχ.2.2
  obtain ⟨θ0, hθ0, hell⟩ := exists_uniform_ellipticity (fun i j => (hAs i j).continuousOn)
    hAell hχ.2.1 hχ.2.2
  have hAh : ∀ p : ι × ι, ContDiff ℝ ∞ (fun x => ψ₀ x * A p.1 p.2 x) := fun p =>
    contDiff_mul_of_contDiffOn hΩ hψ₀.1 hψ₀.2.2 (hAs p.1 p.2)
  have hAhc : ∀ p : ι × ι, HasCompactSupport (fun x => ψ₀ x * A p.1 p.2 x) := fun p =>
    hψ₀.2.1.mul_right
  have hAht : ∀ i j, IsTest Ω (fun x => ψ₀ x * A i j x) := fun i j =>
    ⟨hAh (i, j), hAhc (i, j), tsupport_mul_subset_left.trans hψ₀.2.2⟩
  obtain ⟨KA, hKA0, hKA⟩ := exists_sup_bound_family hAh hAhc
  obtain ⟨Kd, hKd0, hKd⟩ := exists_sup_bound_family (a := fun i x => pd (b i) χ x)
    (fun i => contDiff_pd hχ.1 (b i)) (fun i => hχ.2.1.fderiv_apply ℝ (b i))
  obtain ⟨Kχ, hKχ0, hKχ⟩ := exists_sup_bound_family (J := Unit) (a := fun _ => χ)
    (fun _ => hχ.1) (fun _ => hχ.2.1)
  set n := Fintype.card ι with hn
  set C : ℝ := Kχ ^ 2 + 2 * Kχ ^ 2 / θ0 + 8 * (n : ℝ) ^ 4 * KA ^ 2 * Kd ^ 2 / θ0 ^ 2 +
    2 * n * Kd ^ 2 with hC
  refine ⟨χ₁, C, hχ₁, by rw [hC]; positivity, ?_⟩
  intro u u' F hu hF heq
  have hid := caccioppoli_identity b hΩ hAs hAsym hAell hu hF heq hχ hχ₁ hV₁ hKV₁ hV₁1
  have hKχ' : ∀ x, |χ x| ≤ Kχ := fun x => hKχ () x
  set y : ι → E → ℝ := fun j x => χ x * u' j x with hy
  have hym : ∀ j, MemLp (y j) 2 volume := fun j => memLp_mul_test (hu.l2' j) hχ
  set Y : ℝ := ∑ j, ∫ x, y j x ^ 2 with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))
  set s : ℝ := Real.sqrt Y with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Y := Real.sq_sqrt hY0
  have hys : ∀ j, l2 (y j) ≤ s := fun j => Real.sqrt_le_sqrt (by
    have := Finset.single_le_sum (f := fun j => ∫ x, y j x ^ 2)
      (fun j _ => integral_nonneg (fun x => sq_nonneg _)) (Finset.mem_univ j)
    exact this)
  have hCu : MemLp (fun x => χ₁ x * u x) 2 volume := memLp_mul_test hu.l2 hχ₁
  have hCF : MemLp (fun x => χ₁ x * F x) 2 volume := memLp_mul_test hF hχ₁
  set ℓ : ℝ := l2 (fun x => χ₁ x * u x) with hℓ
  set ℓF : ℝ := l2 (fun x => χ₁ x * F x) with hℓF
  have hℓ0 : 0 ≤ ℓ := l2_nonneg _
  have hℓF0 : 0 ≤ ℓF := l2_nonneg _
  have hpt : ∀ x ∈ tsupport χ, χ₁ x = 1 ∧ ψ₀ x = 1 := fun x hx =>
    ⟨hV₁1 x (hKV₁ hx), hV₀1 x (hKV₀ hx)⟩
  have hoff : ∀ x, x ∉ tsupport χ → χ x = 0 ∧ ∀ v, pd v (fun y => χ y * χ y) x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx, fun v => pd_eq_zero_of_notMem
      (fun h => hx (tsupport_mul_subset_left h)) v⟩
  have hpdξ : ∀ i x, pd (b i) (fun y => χ y * χ y) x = 2 * (χ x * pd (b i) χ x) := by
    intro i x
    rw [pd_mul (hχ.1.differentiable (by simp)) (hχ.1.differentiable (by simp))]; ring
  -- the coefficient functions
  set a : ι → ι → E → ℝ := fun i j x => ψ₀ x * A i j x with ha
  have haL : ∀ i j, MemLp (fun x => a i j x * y j x) 2 volume := fun i j =>
    memLp_mul_of_bound (hAh (i, j)).continuous (K := KA) (fun x => by rw [Real.norm_eq_abs]; exact hKA (i, j) x)
      (hym j)
  have hpd2 : ∀ i, MemLp (fun x => 2 * (pd (b i) χ x * (χ₁ x * u x))) 2 volume := fun i =>
    (memLp_mul_of_bound (contDiff_pd hχ.1 (b i)).continuous (K := Kd)
      (fun x => by rw [Real.norm_eq_abs]; exact hKd i x) hCu).const_mul 2
  -- rewriting the identity
  have hLHS : ∀ i j, ∫ x, A i j x * u' j x * (χ x * χ x * u' i x +
      pd (b i) (fun y => χ y * χ y) x * u x) =
      (∫ x, (a i j x * y j x) * y i x) +
        ∫ x, (a i j x * y j x) * (2 * (pd (b i) χ x * (χ₁ x * u x))) := by
    intro i j
    have i1 : Integrable (fun x => (a i j x * y j x) * y i x) volume :=
      (haL i j).integrable_mul (hym i)
    have i2 : Integrable (fun x => (a i j x * y j x) * (2 * (pd (b i) χ x * (χ₁ x * u x))))
        volume := (haL i j).integrable_mul (hpd2 i)
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport χ
    · obtain ⟨e1, e2⟩ := hpt x hx
      simp only [ha, hy, hpdξ, e1, e2]
      ring
    · obtain ⟨e1, e2⟩ := hoff x hx
      have e3 := e2 (b i)
      simp [ha, hy, e1, e3]
  have hRHS : ∫ x, F x * (χ x * χ x * u x) =
      ∫ x, (χ x * (χ₁ x * F x)) * (χ x * (χ₁ x * u x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport χ
    · obtain ⟨e1, e2⟩ := hpt x hx
      simp only [e1]; ring
    · simp [(hoff x hx).1]
  simp only [hLHS, Finset.sum_add_distrib] at hid
  rw [hRHS] at hid
  set T : ℝ := ∑ i, ∑ j, ∫ x, (a i j x * y j x) * y i x with hT
  set Q : ℝ := ∑ i, ∑ j, ∫ x, (a i j x * y j x) * (2 * (pd (b i) χ x * (χ₁ x * u x))) with hQ
  set R : ℝ := ∫ x, (χ x * (χ₁ x * F x)) * (χ x * (χ₁ x * u x)) with hR
  have hTQ : T + Q = R := hid
  -- ellipticity lower bound
  have hTlow : θ0 * Y ≤ T := by
    have iT : ∀ i j, Integrable (fun x => (a i j x * y j x) * y i x) volume := fun i j =>
      (haL i j).integrable_mul (hym i)
    have e1 : T = ∫ x, ∑ i, ∑ j, (a i j x * y j x) * y i x := by
      rw [hT, integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iT i j))]
      exact Finset.sum_congr rfl (fun i _ => (integral_finset_sum _ (fun j _ => iT i j)).symm)
    have e2 : θ0 * Y = ∫ x, θ0 * ∑ i, y i x ^ 2 := by
      rw [integral_const_mul, integral_finset_sum _ (fun i _ => (hym i).integrable_sq)]
    rw [e1, e2]
    refine integral_mono ((integrable_finset_sum _ (fun i _ => (hym i).integrable_sq)).const_mul θ0)
      (integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iT i j)))
      (fun x => ?_)
    by_cases hx : x ∈ tsupport χ
    · obtain ⟨e1, e2⟩ := hpt x hx
      have := hell x hx (fun j => u' j x)
      have h2 : ∑ i, ∑ j, (a i j x * y j x) * y i x =
          χ x ^ 2 * ∑ i, ∑ j, A i j x * u' j x * u' i x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [ha, hy, e2]; ring
      have h3 : ∑ i, y i x ^ 2 = χ x ^ 2 * ∑ i, u' i x ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by simp only [hy]; ring)
      rw [h2, h3]
      have := mul_le_mul_of_nonneg_left this (sq_nonneg (χ x))
      linarith
    · have e1 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hy, e1]
  -- bounds on `Q` and `R`
  have hQb : |Q| ≤ (n : ℝ) ^ 2 * (2 * KA * Kd * ℓ) * s := by
    have hq : ∀ i j, |∫ x, (a i j x * y j x) * (2 * (pd (b i) χ x * (χ₁ x * u x)))| ≤
        KA * s * (2 * Kd * ℓ) := by
      intro i j
      refine (abs_integral_mul_le_l2 (haL i j) (hpd2 i)).trans ?_
      have h1 : l2 (fun x => a i j x * y j x) ≤ KA * s := by
        refine (l2_mul_le hKA0 (fun x => hKA (i, j) x) (hym j) (haL i j)).trans ?_
        exact mul_le_mul_of_nonneg_left (hys j) hKA0
      have h2 : l2 (fun x => 2 * (pd (b i) χ x * (χ₁ x * u x))) ≤ 2 * Kd * ℓ := by
        have := l2_const_mul 2 (fun x => pd (b i) χ x * (χ₁ x * u x))
        rw [this]
        have h3 : l2 (fun x => pd (b i) χ x * (χ₁ x * u x)) ≤ Kd * ℓ :=
          l2_mul_le hKd0 (fun x => hKd i x) hCu
            (memLp_mul_of_bound (contDiff_pd hχ.1 (b i)).continuous (K := Kd)
              (fun x => by rw [Real.norm_eq_abs]; exact hKd i x) hCu)
        rw [abs_of_pos two_pos]
        nlinarith
      exact mul_le_mul h1 h2 (l2_nonneg _) (by positivity)
    calc |Q| ≤ ∑ i, |∑ j, ∫ x, (a i j x * y j x) * (2 * (pd (b i) χ x * (χ₁ x * u x)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |∫ x, (a i j x * y j x) * (2 * (pd (b i) χ x * (χ₁ x * u x)))| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : ι, ∑ _j : ι, KA * s * (2 * Kd * ℓ) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hq i j))
      _ = (n : ℝ) ^ 2 * (2 * KA * Kd * ℓ) * s := by simp [hn]; ring
  have hRb : |R| ≤ Kχ ^ 2 * (ℓF * ℓ) := by
    have h1 : l2 (fun x => χ x * (χ₁ x * F x)) ≤ Kχ * ℓF :=
      l2_mul_le hKχ0 hKχ' hCF (memLp_mul_of_bound hχ.1.continuous (K := Kχ)
        (fun x => by rw [Real.norm_eq_abs]; exact hKχ' x) hCF)
    have h2 : l2 (fun x => χ x * (χ₁ x * u x)) ≤ Kχ * ℓ :=
      l2_mul_le hKχ0 hKχ' hCu (memLp_mul_of_bound hχ.1.continuous (K := Kχ)
        (fun x => by rw [Real.norm_eq_abs]; exact hKχ' x) hCu)
    have hm1 : MemLp (fun x => χ x * (χ₁ x * F x)) 2 volume :=
      memLp_mul_of_bound hχ.1.continuous (K := Kχ)
        (fun x => by rw [Real.norm_eq_abs]; exact hKχ' x) hCF
    have hm2 : MemLp (fun x => χ x * (χ₁ x * u x)) 2 volume :=
      memLp_mul_of_bound hχ.1.continuous (K := Kχ)
        (fun x => by rw [Real.norm_eq_abs]; exact hKχ' x) hCu
    refine (abs_integral_mul_le_l2 hm1 hm2).trans ?_
    calc _ ≤ (Kχ * ℓF) * (Kχ * ℓ) := mul_le_mul h1 h2 (l2_nonneg _) (by positivity)
      _ = Kχ ^ 2 * (ℓF * ℓ) := by ring
  -- the quadratic inequality for `s`
  set γ : ℝ := (n : ℝ) ^ 2 * (2 * KA * Kd * ℓ) with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  set ρ : ℝ := Kχ ^ 2 * (ℓF * ℓ) with hρ
  have h1 : θ0 * s ^ 2 ≤ ρ + γ * s := by
    have hT' : T = R - Q := by linarith
    have : θ0 * s ^ 2 ≤ T := by rw [hs2]; exact hTlow
    have h2 := le_abs_self R
    have h3 := neg_abs_le Q
    have h4 : R - Q ≤ |R| + |Q| := by linarith [le_abs_self R, neg_abs_le Q]
    nlinarith [hRb, hQb, hT', h4]
  have h2 : θ0 ^ 2 * s ^ 2 ≤ 2 * θ0 * ρ + γ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ0.le, sq_nonneg (θ0 * s - γ)]
  set u1 : ℝ := θ0⁻¹ with hu1
  have hu10 : 0 ≤ u1 := by positivity
  have hθu : θ0 * u1 = 1 := by rw [hu1]; field_simp
  have h3 : s ^ 2 ≤ 2 * ρ * u1 + γ ^ 2 * u1 ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 (sq_nonneg u1)
    have e : θ0 ^ 2 * s ^ 2 * u1 ^ 2 = s ^ 2 := by
      have : (θ0 * u1) ^ 2 = 1 := by rw [hθu]; norm_num
      calc θ0 ^ 2 * s ^ 2 * u1 ^ 2 = (θ0 * u1) ^ 2 * s ^ 2 := by ring
        _ = s ^ 2 := by rw [this]; ring
    have e2 : (2 * θ0 * ρ + γ ^ 2) * u1 ^ 2 = 2 * ρ * u1 + γ ^ 2 * u1 ^ 2 := by
      have : θ0 * u1 = 1 := hθu
      calc (2 * θ0 * ρ + γ ^ 2) * u1 ^ 2 = 2 * ρ * (θ0 * u1) * u1 + γ ^ 2 * u1 ^ 2 := by ring
        _ = _ := by rw [this]; ring
    linarith
  -- the Sobolev norm of `χ u`
  have hwχ : ∀ j, HasWDeriv Set.univ (b j) (fun x => χ x * u x)
      (fun x => χ x * u' j x + pd (b j) χ x * u x) := fun j =>
    hasWDeriv_cutoff_mul hΩ (hu.wd j) hχ
  have hpdu : ∀ j, MemLp (fun x => pd (b j) χ x * u x) 2 volume := fun j =>
    memLp_mul_test hu.l2 (hχ.pd (b j))
  have hwχm : ∀ j, MemLp (fun x => χ x * u' j x + pd (b j) χ x * u x) 2 volume := fun j =>
    (hym j).add (hpdu j)
  have e : sobSq b 1 (fun x => χ x * u x) = (∫ x, (χ x * u x) ^ 2) +
      ∑ j, ∫ x, (χ x * u' j x + pd (b j) χ x * u x) ^ 2 :=
    sobSq_succ_eq b (m := 0) (fun j => ⟨hwχ j, hwχm j⟩)
  have hpdl : ∀ j, l2 (fun x => pd (b j) χ x * u x) ≤ Kd * ℓ := by
    intro j
    have e1 : (fun x => pd (b j) χ x * u x) = fun x => pd (b j) χ x * (χ₁ x * u x) := by
      funext x
      by_cases hx : x ∈ tsupport χ
      · rw [(hpt x hx).1]; ring
      · simp [pd_eq_zero_of_notMem hx]
    rw [e1]
    exact l2_mul_le hKd0 (fun x => hKd j x) hCu
      (memLp_mul_of_bound (contDiff_pd hχ.1 (b j)).continuous (K := Kd)
        (fun x => by rw [Real.norm_eq_abs]; exact hKd j x) hCu)
  have hterm : ∀ j, ∫ x, (χ x * u' j x + pd (b j) χ x * u x) ^ 2 ≤
      2 * (∫ x, y j x ^ 2) + 2 * (Kd * ℓ) ^ 2 := by
    intro j
    have h5 := l2_add_le (hym j) (hpdu j)
    have h6 : l2 (fun x => χ x * u' j x + pd (b j) χ x * u x) ≤ l2 (y j) + Kd * ℓ :=
      h5.trans (add_le_add le_rfl (hpdl j))
    have h7 : 0 ≤ l2 (fun x => χ x * u' j x + pd (b j) χ x * u x) := l2_nonneg _
    have h8 := pow_le_pow_left₀ h7 h6 2
    rw [l2_sq] at h8
    have h9 := l2_sq (y j)
    have h10 := two_sq_bound (l2 (y j)) (Kd * ℓ)
    linarith
  have hχu : ∫ x, (χ x * u x) ^ 2 ≤ (Kχ * ℓ) ^ 2 := by
    have e1 : (fun x => χ x * u x) = fun x => χ x * (χ₁ x * u x) := by
      funext x
      by_cases hx : x ∈ tsupport χ
      · rw [(hpt x hx).1]; ring
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have h5 := l2_mul_le hKχ0 hKχ' hCu (memLp_mul_of_bound hχ.1.continuous (K := Kχ)
        (fun x => by rw [Real.norm_eq_abs]; exact hKχ' x) hCu)
    rw [← e1] at h5
    have h6 := pow_le_pow_left₀ (l2_nonneg _) h5 2
    rw [l2_sq] at h6
    exact h6
  have hsum : ∑ j, ∫ x, (χ x * u' j x + pd (b j) χ x * u x) ^ 2 ≤ 2 * Y + 2 * n * (Kd * ℓ) ^ 2 := by
    calc _ ≤ ∑ j, (2 * (∫ x, y j x ^ 2) + 2 * (Kd * ℓ) ^ 2) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = 2 * Y + 2 * n * (Kd * ℓ) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp [hY, hn]; ring
  have hP : sobSq b 0 (fun x => χ₁ x * F x) = ℓF ^ 2 := (l2_sq _).symm
  have hN : sobSq b 0 (fun x => χ₁ x * u x) = ℓ ^ 2 := (l2_sq _).symm
  rw [e, hP, hN]
  have hρle : ρ ≤ Kχ ^ 2 * ((ℓF ^ 2 + ℓ ^ 2) / 2) := by
    rw [hρ]; refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _); nlinarith [sq_nonneg (ℓF - ℓ)]
  have hγ2 : γ ^ 2 = 4 * (n : ℝ) ^ 4 * KA ^ 2 * Kd ^ 2 * ℓ ^ 2 := by rw [hγ]; ring
  have hCeq : C = Kχ ^ 2 + 2 * Kχ ^ 2 * u1 + 8 * (n : ℝ) ^ 4 * KA ^ 2 * Kd ^ 2 * u1 ^ 2 +
      2 * n * Kd ^ 2 := by
    rw [hC, hu1]; field_simp
  rw [hCeq]
  have hY : Y ≤ u1 * Kχ ^ 2 * (ℓF ^ 2 + ℓ ^ 2) +
      4 * (n : ℝ) ^ 4 * KA ^ 2 * Kd ^ 2 * u1 ^ 2 * ℓ ^ 2 := by
    have h5 := mul_le_mul_of_nonneg_left hρle (by positivity : (0 : ℝ) ≤ 2 * u1)
    have h6 : γ ^ 2 * u1 ^ 2 = 4 * (n : ℝ) ^ 4 * KA ^ 2 * Kd ^ 2 * u1 ^ 2 * ℓ ^ 2 := by
      rw [hγ2]; ring
    rw [← hs2]
    nlinarith [h3, h5, h6]
  have hLHS : (∫ x, (χ x * u x) ^ 2) + ∑ j, ∫ x, (χ x * u' j x + pd (b j) χ x * u x) ^ 2 ≤
      Kχ ^ 2 * ℓ ^ 2 + 2 * Y + 2 * n * Kd ^ 2 * ℓ ^ 2 := by
    have : (Kχ * ℓ) ^ 2 = Kχ ^ 2 * ℓ ^ 2 := by ring
    have h7 : 2 * (n : ℝ) * (Kd * ℓ) ^ 2 = 2 * n * Kd ^ 2 * ℓ ^ 2 := by ring
    linarith [hχu, hsum]
  have hnn : 0 ≤ (Kχ ^ 2 + 8 * (n : ℝ) ^ 4 * KA ^ 2 * Kd ^ 2 * u1 ^ 2 + 2 * n * Kd ^ 2) * ℓF ^ 2 := by
    positivity
  nlinarith [hLHS, hY, hnn]

end CutoffRigidity.Riemann.Diff
