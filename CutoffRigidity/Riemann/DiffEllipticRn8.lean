module

public import CutoffRigidity.Riemann.DiffSobolevRn10

/-! # Localization tools: local `H^m`, cutoffs
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- Local `L²` on `Ω`: `L²` on every compact subset. -/
def LocL2 (Ω : Set E) (f : E → ℝ) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K)

/-- Local `H^m` on `Ω`, defined through cutoffs. -/
def LocSob (Ω : Set E) (m : ℕ) (u : E → ℝ) : Prop :=
  ∀ χ : E → ℝ, IsTest Ω χ → Sob b m (fun x => χ x * u x)

theorem contDiff_mul_of_contDiffOn {Ω : Set E} (hΩ : IsOpen Ω) {ψ f : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ω) (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiff ℝ ∞ (fun x => ψ x * f x) := by
  have h1 : ContDiffOn ℝ ∞ (fun x => ψ x * f x) Ω := hψ.contDiffOn.mul hf
  have h2 : ContDiffOn ℝ ∞ (fun x => ψ x * f x) (tsupport ψ)ᶜ := by
    refine (contDiffOn_const (c := (0 : ℝ))).congr (fun x hx => ?_)
    have : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [this]
  refine contDiff_of_contDiffOn_union_of_isOpen h1 h2 ?_ hΩ (isClosed_tsupport ψ).isOpen_compl
  ext x
  by_cases hx : x ∈ tsupport ψ
  · simp [hs hx]
  · simp [hx]

theorem locallyIntegrable_of_support {Ω : Set E} {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {f : E → ℝ} (hf : LocallyIntegrableOn f Ω volume) (h0 : ∀ x ∉ K, f x = 0) :
    Integrable f volume := by
  have := hf.integrableOn_compact_subset hKΩ hK
  exact this.integrable_of_forall_notMem_eq_zero h0

theorem hasWDeriv_univ_of_support {Ω : Set E} (hΩ : IsOpen Ω) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {v : E} {w w' : E → ℝ} (h : HasWDeriv Ω v w w')
    (hw : ∀ x ∉ K, w x = 0) (hw' : ∀ x ∉ K, w' x = 0) : HasWDeriv Set.univ v w w' := by
  have i1 := locallyIntegrable_of_support hK hKΩ h.1 hw
  have i2 := locallyIntegrable_of_support hK hKΩ h.2.1 hw'
  refine ⟨i1.locallyIntegrable.locallyIntegrableOn _, i2.locallyIntegrable.locallyIntegrableOn _,
    fun φ hφ => ?_⟩
  obtain ⟨V, hV, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨χ, hχ, hχc, hχΩ, hχ1, -⟩ := exists_cutoff hVc hΩ hVΩ
  have hψ : IsTest Ω (fun x => χ x * φ x) :=
    ⟨hχ.mul hφ.1, hφ.2.1.mul_left, (tsupport_mul_subset_left).trans hχΩ⟩
  have e := h.2.2 _ hψ
  have hpd : ∀ x ∈ K, pd v (fun x => χ x * φ x) x = pd v φ x := by
    intro x hx
    have : (fun x => χ x * φ x) =ᶠ[nhds x] φ := by
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      rw [hχ1 y (subset_closure hy), one_mul]
    unfold pd; rw [this.fderiv_eq]
  have e1 : ∫ x, w x * pd v (fun x => χ x * φ x) x = ∫ x, w x * pd v φ x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ K
    · simp only [hpd x hx]
    · simp [hw x hx]
  have e2 : ∫ x, w' x * (χ x * φ x) = ∫ x, w' x * φ x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ K
    · simp only [hχ1 x (subset_closure (hKV hx)), one_mul]
    · simp [hw' x hx]
  rw [e1, e2] at e
  exact e

theorem exists_iteratedFDeriv_bound {a : E → ℝ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (m : ℕ) : ∃ Kb : ℝ, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Kb := by
  have : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) k).exists_bound_of_continuous
      (ha.continuous_iteratedFDeriv (by simp))
    exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩
  choose B hB0 hB using this
  refine ⟨∑ k ∈ Finset.range (m + 1), B k, fun k hk x => ?_⟩
  refine (hB k x).trans ?_
  exact Finset.single_le_sum (f := B) (fun i _ => hB0 i) (Finset.mem_range.2 (by omega))

theorem sob_mul_of_locSob {Ω : Set E} (hΩ : IsOpen Ω) {m : ℕ} {f : E → ℝ}
    (hf : LocSob b Ω m f) {a : E → ℝ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ Ω) : Sob b m (fun x => a x * f x) := by
  obtain ⟨χ, hχ, hχc, hχΩ, hχ1, -⟩ := exists_cutoff hc hΩ hs
  obtain ⟨Kb, hKb⟩ := exists_iteratedFDeriv_bound ha hc m
  have h1 := (Sob.mul_smooth b ha hKb (hf χ ⟨hχ, hχc, hχΩ⟩)).1
  refine Sob.congr_ae b h1 (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : a x = 0
  · simp [hx]
  · have := hχ1 x (subset_tsupport _ hx)
    simp [this]

theorem memLp_mul_test {Ω : Set E} {f χ : E → ℝ} (hf : LocL2 Ω f) (hχ : IsTest Ω χ) :
    MemLp (fun x => χ x * f x) 2 volume := by
  have hK : IsCompact (tsupport χ) := hχ.2.1
  have h1 := hf _ hK hχ.2.2
  obtain ⟨c, hc⟩ := hχ.2.1.exists_bound_of_continuous hχ.1.continuous
  have h2 : MemLp (fun x => χ x * f x) 2 (volume.restrict (tsupport χ)) :=
    MemLp.of_le_mul (c := c) h1 (hχ.1.continuous.aestronglyMeasurable.mul h1.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))
  have h3 : (tsupport χ).indicator (fun x => χ x * f x) = fun x => χ x * f x := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · simp [hx]
    · simp [hx, image_eq_zero_of_notMem_tsupport hx]
  have := (memLp_indicator_iff_restrict (μ := volume) (p := 2) hK.measurableSet
    (f := fun x => χ x * f x)).2 h2
  rwa [h3] at this

/-- Local `H¹` data on `Ω`. -/
structure LocH1 (Ω : Set E) (u : E → ℝ) (u' : ι → E → ℝ) : Prop where
  l2 : LocL2 Ω u
  l2' : ∀ j, LocL2 Ω (u' j)
  wd : ∀ j, HasWDeriv Ω (b j) u (u' j)

theorem pd_eq_zero_of_notMem {χ : E → ℝ} {x : E} (hx : x ∉ tsupport χ) (v : E) : pd v χ x = 0 := by
  have : fderiv ℝ χ x = 0 := by
    by_contra h
    exact hx (tsupport_fderiv_subset ℝ (subset_tsupport _ h))
  simp [pd, this]

theorem LocH1.locSob {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} {u' : ι → E → ℝ}
    (h : LocH1 b Ω u u') : LocSob b Ω 1 u := by
  intro χ hχ
  have hmem : MemLp (fun x => χ x * u x) 2 volume := memLp_mul_test h.l2 hχ
  refine ⟨hmem, fun j => ⟨fun x => χ x * u' j x + pd (b j) χ x * u x, ?_, ?_⟩⟩
  · have h1 := (h.wd j).mul_smooth hΩ hχ.1
    refine hasWDeriv_univ_of_support hΩ hχ.2.1 hχ.2.2 h1 (fun x hx => ?_) (fun x hx => ?_)
    · simp [image_eq_zero_of_notMem_tsupport hx]
    · simp [image_eq_zero_of_notMem_tsupport hx, pd_eq_zero_of_notMem hx]
  · exact (memLp_mul_test (h.l2' j) hχ).add (memLp_mul_test h.l2 (hχ.pd (b j)))

theorem hasWDeriv_cutoff_mul {Ω : Set E} (hΩ : IsOpen Ω) {v : E} {u u' χ : E → ℝ}
    (h : HasWDeriv Ω v u u') (hχ : IsTest Ω χ) :
    HasWDeriv Set.univ v (fun x => χ x * u x) (fun x => χ x * u' x + pd v χ x * u x) := by
  have h1 := h.mul_smooth hΩ hχ.1
  refine hasWDeriv_univ_of_support hΩ hχ.2.1 hχ.2.2 h1 (fun x hx => ?_) (fun x hx => ?_)
  · simp [image_eq_zero_of_notMem_tsupport hx]
  · simp [image_eq_zero_of_notMem_tsupport hx, pd_eq_zero_of_notMem hx]

/-- Cutoff equal to `1` on an open neighbourhood of a compact set. -/
theorem exists_cutoff_nhds {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, IsTest U χ ∧ (∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, χ x = 1) ∧
      ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨χ, hχ, hχc, hχU, hχ1, h01⟩ := exists_cutoff hVc hU hVU
  exact ⟨χ, ⟨hχ, hχc, hχU⟩, ⟨V, hV, hKV, fun x hx => hχ1 x (subset_closure hx)⟩, h01⟩

theorem pd_eq_zero_of_eventually_one {χ : E → ℝ} {V : Set E} (hV : IsOpen V)
    (h1 : ∀ x ∈ V, χ x = 1) {x : E} (hx : x ∈ V) (v : E) : pd v χ x = 0 := by
  have : χ =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [hV.mem_nhds hx] with y hy using h1 y hy
  unfold pd
  rw [this.fderiv_eq]; simp

theorem LocSob.deriv {Ω : Set E} (hΩ : IsOpen Ω) {m : ℕ} {u : E → ℝ} {u' : ι → E → ℝ}
    (hu : LocSob b Ω (m + 1) u) (hd : ∀ j, HasWDeriv Ω (b j) u (u' j)) (j : ι) :
    LocSob b Ω m (u' j) := by
  intro χ hχ
  obtain ⟨χ', hχ', ⟨V, hV, hKV, hV1⟩, -⟩ := exists_cutoff_nhds hχ.2.1 hΩ hχ.2.2
  have h1 := hu χ' hχ'
  obtain ⟨-, hw⟩ := (Sob.succ_iff b).1 h1
  have hw1 := hasWDeriv_cutoff_mul hΩ (hd j) hχ'
  have hm := (hw j).2
  have hae : (fun x => χ' x * u' j x + pd (b j) χ' x * u x) =ᵐ[volume]
      wd (b j) (fun x => χ' x * u x) := hw1.unique (hw j).1
  have hm1 : Sob b m (fun x => χ' x * u' j x + pd (b j) χ' x * u x) := hm.congr_ae b hae.symm
  obtain ⟨Kb, hKb⟩ := exists_iteratedFDeriv_bound hχ.1 hχ.2.1 m
  have h2 := (Sob.mul_smooth b hχ.1 hKb hm1).1
  refine Sob.congr_ae b h2 (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport χ
  · have e1 := hV1 x (hKV hx)
    have e2 := pd_eq_zero_of_eventually_one hV hV1 (hKV hx) (b j)
    simp [e1, e2]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem LocSob.mono {Ω : Set E} {m m' : ℕ} (h : m ≤ m') {u : E → ℝ} (hu : LocSob b Ω m' u) :
    LocSob b Ω m u := fun χ hχ => Sob.mono b h (hu χ hχ)

/-- Uniform ellipticity on compact subsets, from pointwise ellipticity and continuity. -/
theorem exists_uniform_ellipticity {Ω : Set E} {A : ι → ι → E → ℝ}
    (hcont : ∀ i j, ContinuousOn (A i j) Ω)
    (hell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ c > 0, ∀ x ∈ K, ∀ ξ : ι → ℝ, c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i := by
  set S : Set (ι → ℝ) := {ξ | ∑ i, ξ i ^ 2 = 1} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset (fun ξ hξ => ?_)
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      have h1 : ξ i ^ 2 ≤ 1 := by
        have := Finset.single_le_sum (f := fun i => ξ i ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ i)
        simp only [hS, Set.mem_setOf_eq] at hξ
        linarith
      exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  set q : E × (ι → ℝ) → ℝ := fun p => ∑ i, ∑ j, A i j p.1 * p.2 j * p.2 i with hq
  rcases (K ×ˢ S).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun x hx ξ => ?_⟩
    by_cases hξ : ∑ i, ξ i ^ 2 = 0
    · have : ∀ i, ξ i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ξ i))).1 hξ i
          (Finset.mem_univ i)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      simp [this]
    · exfalso
      have hpos : 0 < ∑ i, ξ i ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
        (Ne.symm hξ)
      set η : ι → ℝ := (1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ with hη
      have : η ∈ S := by
        simp only [hS, Set.mem_setOf_eq, hη, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
        rw [div_pow, Real.sq_sqrt hpos.le]
        field_simp
      have : (x, η) ∈ K ×ˢ S := ⟨hx, this⟩
      rw [hemp] at this; exact this
  · have hcq : ContinuousOn q (K ×ˢ S) := by
      refine continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ => ?_))
      refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) (by fun_prop)
      exact ((hcont i j).mono hKΩ).comp continuousOn_fst (fun p hp => hp.1)
    obtain ⟨p0, hp0, hmin⟩ := (hK.prod hSc).exists_isMinOn hne hcq
    obtain ⟨c0, hc0, hc0'⟩ := hell p0.1 (hKΩ hp0.1)
    have hqpos : 0 < q p0 := by
      have h := hc0' p0.2
      have h1 : ∑ i, p0.2 i ^ 2 = 1 := hp0.2
      rw [h1, mul_one] at h
      exact lt_of_lt_of_le hc0 h
    refine ⟨q p0, hqpos, fun x hx ξ => ?_⟩
    by_cases hξ : ∑ i, ξ i ^ 2 = 0
    · have : ∀ i, ξ i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ξ i))).1 hξ i
          (Finset.mem_univ i)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      simp [this]
    · have hpos : 0 < ∑ i, ξ i ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
        (Ne.symm hξ)
      set t := Real.sqrt (∑ i, ξ i ^ 2) with ht
      have ht0 : 0 < t := Real.sqrt_pos.2 hpos
      have ht2 : t ^ 2 = ∑ i, ξ i ^ 2 := Real.sq_sqrt hpos.le
      set η : ι → ℝ := (1 / t) • ξ with hη
      have hηS : η ∈ S := by
        simp only [hS, Set.mem_setOf_eq, hη, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
        rw [div_pow, ht2]
        field_simp
      have h1 : q p0 ≤ q (x, η) := hmin ⟨hx, hηS⟩
      have h2 : q (x, ξ) = t ^ 2 * q (x, η) := by
        simp only [hq, hη, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        field_simp
      have : q p0 * ∑ i, ξ i ^ 2 ≤ q (x, ξ) := by
        rw [h2, ← ht2]; nlinarith [sq_nonneg t]
      exact this

theorem bound_const_add_compact {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : ℝ) (N : ℕ) : ∃ B : ℝ, ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (fun x => c + f x) x‖ ≤ B := by
  obtain ⟨Kb, hKb⟩ := exists_iteratedFDeriv_bound hf hc N
  refine ⟨Kb + |c|, fun k hk x => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have h0 := hKb 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at h0
    calc |c + f x| ≤ |c| + |f x| := abs_add_le _ _
      _ ≤ Kb + |c| := by rw [Real.norm_eq_abs] at h0; linarith
  · have e : (fun x => c + f x) = (fun _ : E => c) + f := rfl
    rw [e, iteratedFDeriv_add_apply (contDiff_const.contDiffAt) ((hf.of_le (by simp)).contDiffAt),
      iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hk0)]
    simp only [Pi.zero_apply, zero_add]
    exact (hKb k hk x).trans (by linarith [abs_nonneg c])

end CutoffRigidity.Riemann.Diff
