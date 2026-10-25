module

public import CutoffRigidity.Riemann.DiffInstance2
public import CutoffRigidity.Riemann.DiffRellichChart
public import CutoffRigidity.Riemann.WeightedIBPGlobal
public import CutoffRigidity.L2CompactnessTools

/-! # Compactness of the energy balls in `L²(μ)` (workstream HPOS)

Local Rellich in charts (`DiffRellichChart`) is globalised by a finite cover of the support of a cutoff;
tightness (`tail`) is a hypothesis here and is supplied by `DiffTight` (from LSI).

* `tb_of_finite_control`: abstract gluing lemma for total boundedness;
* `mulBall_totallyBounded`: `{ψ f : E₁(f) ≤ C}` is totally bounded in `L²(μ)` for every test function `ψ`;
* `ball_totallyBounded_of_tail`: tightness gives total boundedness of `{f : E₁(f) ≤ C}`;
* `Qball_totallyBounded_of_tail`: the same for the energy balls of the form domain `Q`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Abstract

/-- Gluing lemma: if `u` is controlled by finitely many totally bounded families `P k`, then `u` is
totally bounded. -/
theorem tb_of_finite_control {ι X : Type*} [PseudoMetricSpace X] {κ : Type*} [Fintype κ]
    (u : ι → X) (P : κ → ι → X) (hP : ∀ k, TotallyBounded (Set.range (P k))) (c : ℝ)
    (hc : ∀ a b, dist (u a) (u b) ≤ c * ∑ k, dist (P k a) (P k b)) :
    TotallyBounded (Set.range u) := by
  classical
  by_cases hι : IsEmpty ι
  · simp [Set.range_eq_empty]
  rw [not_isEmpty_iff] at hι
  obtain ⟨a₀⟩ := hι
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set c' : ℝ := |c| + 1 with hc'
  have hc'pos : 0 < c' := by positivity
  set n : ℝ := (Fintype.card κ : ℝ) with hn
  have hn0 : 0 ≤ n := by positivity
  set δ : ℝ := ε / (2 * c' * (n + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hnet : ∀ k, ∃ t : Set X, t.Finite ∧ Set.range (P k) ⊆ ⋃ y ∈ t, Metric.ball y δ :=
    fun k => Metric.totallyBounded_iff.1 (hP k) δ hδpos
  choose t ht hcov using hnet
  have hsel : ∀ k a, ∃ y ∈ t k, dist (P k a) y < δ := by
    intro k a
    have := hcov k ⟨a, rfl⟩
    simp only [mem_iUnion, Metric.mem_ball] at this
    obtain ⟨y, hy, hd⟩ := this
    exact ⟨y, hy, hd⟩
  choose s hs hsd using hsel
  haveI : ∀ k, Finite (t k) := fun k => (ht k).to_subtype
  let τ : ι → ∀ k, t k := fun a k => ⟨s k a, hs k a⟩
  let rep : (∀ k, t k) → ι := fun σ => if h : ∃ a, τ a = σ then h.choose else a₀
  have hrep : ∀ a, τ (rep (τ a)) = τ a := by
    intro a
    have h : ∃ a', τ a' = τ a := ⟨a, rfl⟩
    have h2 : rep (τ a) = h.choose := by simp [rep, h]
    rw [h2]
    exact h.choose_spec
  refine ⟨Set.range (fun σ => u (rep σ)), Set.finite_range _, ?_⟩
  rintro _ ⟨a, rfl⟩
  simp only [mem_iUnion, Metric.mem_ball, exists_prop]
  refine ⟨u (rep (τ a)), ⟨τ a, rfl⟩, ?_⟩
  have hk : ∀ k, dist (P k a) (P k (rep (τ a))) < 2 * δ := by
    intro k
    have h1 := hsd k a
    have h2 : s k (rep (τ a)) = s k a := by
      have := congrFun (hrep a) k
      exact congrArg Subtype.val this
    have h3 := hsd k (rep (τ a))
    rw [h2] at h3
    calc dist (P k a) (P k (rep (τ a))) ≤ dist (P k a) (s k a) + dist (P k (rep (τ a))) (s k a) := by
          rw [dist_comm (P k (rep (τ a))) (s k a)]; exact dist_triangle _ _ _
      _ < 2 * δ := by linarith
  calc dist (u a) (u (rep (τ a))) ≤ c * ∑ k, dist (P k a) (P k (rep (τ a))) := hc _ _
    _ ≤ c' * ∑ k : κ, (2 * δ) := by
        have hsum : ∑ k, dist (P k a) (P k (rep (τ a))) ≤ ∑ k : κ, (2 * δ) :=
          Finset.sum_le_sum fun k _ => (hk k).le
        have hs0 : 0 ≤ ∑ k, dist (P k a) (P k (rep (τ a))) := Finset.sum_nonneg fun k _ => dist_nonneg
        calc c * ∑ k, dist (P k a) (P k (rep (τ a))) ≤ |c| * ∑ k, dist (P k a) (P k (rep (τ a))) :=
              mul_le_mul_of_nonneg_right (le_abs_self c) hs0
          _ ≤ c' * ∑ k : κ, (2 * δ) := mul_le_mul (by simp [hc']) hsum hs0 hc'pos.le
    _ < ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : c' * (n * (2 * δ)) < ε := by
          have e : c' * (n * (2 * δ)) = ε * (n / (n + 1)) := by
            simp only [hδ]; field_simp
          rw [e]
          have : n / (n + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
          nlinarith
        simpa [hn] using this

end Abstract

section Ball

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- `E₁(f) = ∫ Γ f dμ + ∫ f² dμ` for a test function. -/
noncomputable def E1 (μ : Measure M) (f : testSub F M) : ℝ :=
  ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ + ∫ x, (f : M → ℝ) x ^ 2 ∂μ

/-- Product of two test functions. -/
noncomputable def mulT (θ f : testSub F M) : testSub F M :=
  ⟨fun x => (θ : M → ℝ) x * (f : M → ℝ) x, θ.2.1.mul f.2.1, by
    simpa [Pi.mul_def] using θ.2.2.mul_right (f' := (f : M → ℝ))⟩

theorem mulT_apply (θ f : testSub F M) (x : M) :
    (mulT F θ f : M → ℝ) x = (θ : M → ℝ) x * (f : M → ℝ) x := rfl

theorem norm_testToL2_sq (g : testSub F M) :
    ‖testToL2 F μ g‖ ^ 2 = ∫ x, (g : M → ℝ) x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_testToL2]
  simp [sq]

theorem dist_testToL2_sq (g g' : testSub F M) :
    dist (testToL2 F μ g) (testToL2 F μ g') ^ 2 =
      ∫ x, ((g : M → ℝ) x - (g' : M → ℝ) x) ^ 2 ∂μ := by
  rw [dist_eq_norm, ← map_sub, norm_testToL2_sq]
  rfl

/-- Pointwise control of a function supported in `K` by finitely many cutoffs covering `K`. -/
theorem sq_le_sum_cutoffs {κ : Type*} [Fintype κ] (b : κ → M → ℝ) (hb : ∀ k y, 0 ≤ b k y)
    {m : ℝ} (hm : 0 < m) (K : Set M) (hK : ∀ y ∈ K, m ≤ ∑ k, b k y) (a : M → ℝ)
    (ha : ∀ y, y ∉ K → a y = 0) (y : M) :
    a y ^ 2 ≤ (Fintype.card κ / m ^ 2) * ∑ k, (b k y * a y) ^ 2 := by
  by_cases hy : y ∈ K
  · have h1 : m ^ 2 ≤ (∑ k, b k y) ^ 2 := by
      have := hK y hy
      nlinarith
    have h2 : (∑ k, b k y) ^ 2 ≤ Fintype.card κ * ∑ k, b k y ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := fun k => b k y)
    have h3 : ∑ k, (b k y * a y) ^ 2 = (∑ k, b k y ^ 2) * a y ^ 2 := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [h3, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : m ^ 2 * a y ^ 2 ≤ Fintype.card κ * ((∑ k, b k y ^ 2) * a y ^ 2) :=
      calc m ^ 2 * a y ^ 2 ≤ (∑ k, b k y) ^ 2 * a y ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ ≤ (Fintype.card κ * ∑ k, b k y ^ 2) * a y ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = _ := by ring
    nlinarith [this]
  · rw [ha y hy]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Finset.sum_const_zero, mul_zero, le_refl]

include hV hμ in
/-- Totally boundedness of `{ψ f : E₁ f ≤ C}`. -/
theorem mulBall_totallyBounded (ψ : testSub F M) (C : ℝ) :
    TotallyBounded (Set.range (fun f : {f : testSub F M // E1 F μ f ≤ C} =>
      testToL2 F μ (mulT F ψ f))) := by
  classical
  have hK : IsCompact (tsupport (ψ : M → ℝ)) := ψ.2.2
  choose b hb1 hb2 hb3 hb4 hb5 using exists_bump (F := F) (M := M)
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | 0 < b x y})
    (fun x _ => (isOpen_lt continuous_const (hb1 x).continuous).mem_nhds (hb4 x))
  set Ψ : M → ℝ := fun y => ∑ x ∈ t, b x y with hΨ
  have hΨc : Continuous Ψ := continuous_finsetSum _ fun x _ => (hb1 x).continuous
  have hΨpos : ∀ y ∈ tsupport (ψ : M → ℝ), 0 < Ψ y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (hcov hy)
    exact lt_of_lt_of_le hxy (Finset.single_le_sum (f := fun x => b x y) (fun z _ => hb3 z y) hx)
  obtain ⟨m, hm, hmle⟩ := hK.exists_forall_le' (a := 0) hΨc.continuousOn hΨpos
  let χ : t → testSub F M := fun k => ⟨b k.1, hb1 k.1, hb2 k.1⟩
  let u : {f : testSub F M // E1 F μ f ≤ C} → (M →₂[μ] ℝ) := fun f => testToL2 F μ (mulT F ψ f)
  let P : t → {f : testSub F M // E1 F μ f ≤ C} → (M →₂[μ] ℝ) :=
    fun k f => testToL2 F μ (mulT F (mulT F (χ k) ψ) f)
  have hP : ∀ k, TotallyBounded (Set.range (P k)) := by
    intro k
    refine (chart_local_totallyBounded F hV hμ k.1 (mulT F (χ k) ψ) ?_ C).subset ?_
    · exact tsupport_mul_subset_left.trans (hb5 k.1)
    · rintro _ ⟨f, rfl⟩
      exact ⟨f.1, mulT F (mulT F (χ k) ψ) f.1, fun x => rfl, f.2, rfl⟩
  have hcard : 0 ≤ (Fintype.card t : ℝ) := by positivity
  refine tb_of_finite_control u P hP (Real.sqrt (Fintype.card t) / m) ?_
  intro f f'
  set d : t → ℝ := fun k => dist (P k f) (P k f') with hd
  have hd0 : ∀ k, 0 ≤ d k := fun k => dist_nonneg
  have hsq : dist (u f) (u f') ^ 2 ≤ (Fintype.card t / m ^ 2) * ∑ k, d k ^ 2 := by
    rw [dist_testToL2_sq]
    have hpt : ∀ y, ((mulT F ψ f : M → ℝ) y - (mulT F ψ f' : M → ℝ) y) ^ 2 ≤
        (Fintype.card t / m ^ 2) * ∑ k : t, ((b k.1 y) * ((ψ : M → ℝ) y * ((f.1 : M → ℝ) y - (f'.1 : M → ℝ) y))) ^ 2 := by
      intro y
      have := sq_le_sum_cutoffs (fun k : t => b k.1) (fun k y => hb3 k.1 y) hm
        (tsupport (ψ : M → ℝ)) (fun y hy => by
          rw [Finset.sum_coe_sort t (fun x => b x y)]
          exact hmle y hy)
        (fun y => (ψ : M → ℝ) y * ((f.1 : M → ℝ) y - (f'.1 : M → ℝ) y))
        (fun y hy => by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]) y
      simpa [mulT_apply, mul_sub] using this
    have hint : ∀ k : t, d k ^ 2 = ∫ x, ((b k.1 x) * ((ψ : M → ℝ) x * ((f.1 : M → ℝ) x - (f'.1 : M → ℝ) x))) ^ 2 ∂μ := by
      intro k
      simp only [hd, P]
      rw [dist_testToL2_sq]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mulT_apply, χ]; ring_nf
    have hI : ∀ k : t, Integrable (fun x => ((b k.1 x) * ((ψ : M → ℝ) x * ((f.1 : M → ℝ) x - (f'.1 : M → ℝ) x))) ^ 2) μ := by
      intro k
      have h1 : Continuous (fun x => ((b k.1 x) * ((ψ : M → ℝ) x * ((f.1 : M → ℝ) x - (f'.1 : M → ℝ) x))) ^ 2) :=
        ((hb1 k.1).continuous.mul (ψ.2.1.continuous.mul (f.1.2.1.continuous.sub f'.1.2.1.continuous))).pow 2
      refine h1.integrable_of_hasCompactSupport ?_
      have := ((hb2 k.1).mul_right (f' := fun x => (ψ : M → ℝ) x * ((f.1 : M → ℝ) x - (f'.1 : M → ℝ) x))).comp_left
        (g := fun z : ℝ => z ^ 2) (by simp)
      simpa [Function.comp_def, Pi.mul_def] using this
    calc _ ≤ ∫ x, (Fintype.card t / m ^ 2) * ∑ k : t, ((b k.1 x) * ((ψ : M → ℝ) x * ((f.1 : M → ℝ) x - (f'.1 : M → ℝ) x))) ^ 2 ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) ?_ (Eventually.of_forall hpt)
          exact (integrable_finsetSum _ fun k _ => hI k).const_mul _
      _ = _ := by
          rw [integral_const_mul, integral_finsetSum _ fun k _ => hI k]
          simp only [hint]
  have hsum : ∑ k, d k ^ 2 ≤ (∑ k, d k) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc d k ^ 2 = d k * d k := sq _
      _ ≤ ∑ j, d k * d j := Finset.single_le_sum (f := fun j => d k * d j)
          (fun j _ => mul_nonneg (hd0 k) (hd0 j)) (Finset.mem_univ k)
  have hS : 0 ≤ ∑ k, d k := Finset.sum_nonneg fun k _ => hd0 k
  have hfin : dist (u f) (u f') ^ 2 ≤ (Real.sqrt (Fintype.card t) / m * ∑ k, d k) ^ 2 := by
    calc _ ≤ _ := hsq
      _ ≤ (Fintype.card t / m ^ 2) * (∑ k, d k) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by
          rw [mul_pow, div_pow, Real.sq_sqrt hcard]
  exact (sq_le_sq₀ dist_nonneg (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hm.le) hS)).1 hfin

/-- Smooth compactly supported cutoff equal to `1` on a compact set. -/
theorem exists_cutoff_one_on {K : Set M} (hK : IsCompact K) :
    ∃ ψ : testSub F M, (∀ x, 0 ≤ (ψ : M → ℝ) x ∧ (ψ : M → ℝ) x ≤ 1) ∧ ∀ x ∈ K, (ψ : M → ℝ) x = 1 := by
  haveI := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  obtain ⟨K', hK', hsub⟩ := exists_compact_superset hK
  obtain ⟨f, hf, hrange, hsupp, h1⟩ := exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, F) (n := (⊤ : ℕ∞))
    (isOpen_interior (s := K')) hK.isClosed hsub
  refine ⟨⟨f, hf, ?_⟩, fun x => hrange ⟨x, rfl⟩, fun x hx => (h1 x).1 hx⟩
  refine IsCompact.of_isClosed_subset hK' (isClosed_tsupport _) ?_
  rw [tsupport, hsupp]
  exact closure_minimal interior_subset hK'.isClosed

include hV hμ in
/-- Tightness implies total boundedness of the energy balls of test functions. -/
theorem ball_totallyBounded_of_tail
    (htail : ∀ C ε : ℝ, 0 < ε → ∃ K : Set M, IsCompact K ∧ ∀ f : testSub F M, E1 F μ f ≤ C →
      ∫ x in Kᶜ, (f : M → ℝ) x ^ 2 ∂μ ≤ ε) (C : ℝ) :
    TotallyBounded (Set.range (fun f : {f : testSub F M // E1 F μ f ≤ C} => testToL2 F μ f)) := by
  apply totallyBounded_of_uniform_precompact_approximation
  intro ε hε
  obtain ⟨K, hK, hKt⟩ := htail C (ε ^ 2 / 2) (by positivity)
  obtain ⟨ψ, hψ01, hψK⟩ := exists_cutoff_one_on F hK
  refine ⟨Set.range (fun f : {f : testSub F M // E1 F μ f ≤ C} => testToL2 F μ (mulT F ψ f)),
    mulBall_totallyBounded F hV hμ ψ C, ?_⟩
  rintro _ ⟨f, rfl⟩
  refine ⟨_, ⟨f, rfl⟩, ?_⟩
  have hd := dist_testToL2_sq (F := F) (μ := μ) f.1 (mulT F ψ f.1)
  have hle : ∫ x, ((f.1 : M → ℝ) x - (mulT F ψ f.1 : M → ℝ) x) ^ 2 ∂μ ≤
      ∫ x in Kᶜ, (f.1 : M → ℝ) x ^ 2 ∂μ := by
    rw [← integral_indicator hK.isClosed.measurableSet.compl]
    have hcont : Continuous (fun x => ((f.1 : M → ℝ) x) ^ 2) := (f.1.2.1.continuous).pow 2
    have hint : Integrable (fun x => ((f.1 : M → ℝ) x - (mulT F ψ f.1 : M → ℝ) x) ^ 2) μ := by
      refine (Continuous.integrable_of_hasCompactSupport ?_ ?_)
      · exact ((f.1.2.1.continuous).sub (mulT F ψ f.1).2.1.continuous).pow 2
      · exact (((f.1).2.2.sub (mulT F ψ f.1).2.2)).comp_left (g := fun z : ℝ => z ^ 2) (by simp)
    have hint2 : Integrable (Kᶜ.indicator (fun x => ((f.1 : M → ℝ) x) ^ 2)) μ := by
      refine (hcont.integrable_of_hasCompactSupport ?_).indicator hK.isClosed.measurableSet.compl
      exact f.1.2.2.comp_left (g := fun z : ℝ => z ^ 2) (by simp)
    refine integral_mono hint hint2 fun x => ?_
    by_cases hx : x ∈ K
    · have h1 := hψK x hx
      simp [mulT_apply, h1, hx]
    · simp only [Set.indicator_of_mem (Set.mem_compl hx), mulT_apply]
      obtain ⟨h0, h1⟩ := hψ01 x
      nlinarith [sq_nonneg ((f.1 : M → ℝ) x), mul_nonneg h0 (sq_nonneg ((f.1 : M → ℝ) x)),
        mul_nonneg (sub_nonneg.2 h1) (sq_nonneg ((f.1 : M → ℝ) x)),
        mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1)) (sq_nonneg ((f.1 : M → ℝ) x))]
  have h2 := hKt f.1 f.2
  have : dist (testToL2 F μ f.1) (testToL2 F μ (mulT F ψ f.1)) ^ 2 < ε ^ 2 := by
    rw [hd]; nlinarith [sq_pos_of_pos hε]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this

include hV hμ in
/-- Tightness implies total boundedness of the energy balls of the form domain `Q`. -/
theorem Qball_totallyBounded_of_tail
    (htail : ∀ C ε : ℝ, 0 < ε → ∃ K : Set M, IsCompact K ∧ ∀ f : testSub F M, E1 F μ f ≤ C →
      ∫ x in Kᶜ, (f : M → ℝ) x ^ 2 ∂μ ≤ ε) (C : ℝ) :
    TotallyBounded {u : M →₂[μ] ℝ | u ∈ (diffT F hV hμ).Q ∧
      (diffT F hV hμ).E u u + ‖u‖ ^ 2 ≤ C} := by
  have hb := (ball_totallyBounded_of_tail F hV hμ htail (C + 1)).closure
  refine hb.subset ?_
  rintro u ⟨hu, huC⟩
  obtain ⟨f, hf, hfc⟩ := ((diffT F hV hμ).mem_Q u).1 hu
  have hE := (diffT F hV hμ).E_lim f f u u hf hfc hf hfc
  have hn : Tendsto (fun n => ‖(f n : M →₂[μ] ℝ)‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2)) := (hf.norm).pow 2
  have hev : ∀ᶠ n in atTop, (diffFormData F hV hμ).en (f n) (f n) + ‖(f n : M →₂[μ] ℝ)‖ ^ 2 < C + 1 :=
    (hE.add hn).eventually (gt_mem_nhds (by linarith))
  refine mem_closure_of_tendsto hf (hev.mono fun n hn => ?_)
  obtain ⟨a, ha⟩ := (f n).2
  have hfa : f n = ⟨testToL2 F μ a, a, rfl⟩ := Subtype.ext ha.symm
  refine ⟨⟨a, ?_⟩, ha⟩
  have h1 := en_diffFormData F hV hμ a a
  rw [← hfa] at h1
  rw [← ha, norm_testToL2_sq] at hn
  unfold E1
  linarith

end Ball

end CutoffRigidity.Riemann.Diff
