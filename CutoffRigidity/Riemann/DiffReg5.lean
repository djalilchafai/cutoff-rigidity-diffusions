module

public import CutoffRigidity.Riemann.DiffReg4
public import CutoffRigidity.Riemann.DiffEllipticRn17

/-! # Interior sup estimate, part 1: the `ℝⁿ` level (workstream KER-REG)

Conversion of the chart weak equation into REGn's `WCoeff`/`WSol`, weak gradient of smooth functions,
and the sup estimate `sup_estimate_Rn` for smooth solutions of `-div(ϱ a ∇u) + lam ϱ u = 0`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

section Rn

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- `WCoeff` for the coordinate coefficients of a chart. -/
theorem wcoeff_chart
    {Ω : Set F} (hΩ : IsOpen Ω) {a : F → F →L[ℝ] F} {ϱ : F → ℝ}
    (ha : ContDiffOn ℝ ∞ a Ω) (hϱ : ContDiffOn ℝ ∞ ϱ Ω)
    (hsym : ∀ x ∈ Ω, ∀ v w : F, inner ℝ (a x v) w = inner ℝ v (a x w))
    (hell : ∀ x ∈ Ω, ∃ c > 0, ∀ v : F, c * ‖v‖ ^ 2 ≤ inner ℝ (a x v) v)
    (hpos : ∀ x ∈ Ω, 0 < ϱ x)  :
    WCoeff Ω (fun i j x => inner ℝ (a x ((stdOrthonormalBasis ℝ F) j)) ((stdOrthonormalBasis ℝ F) i)) ϱ := by
  classical
  set b := stdOrthonormalBasis ℝ F with hb
  set A : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F) → F → ℝ :=
    fun i j x => inner ℝ (a x (b j)) (b i) with hA
  -- : Fin (Module.finrank ℝ F) → F → ℝ := fun j x => inner ℝ (Du x) (b j) with hu'
  have hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω := fun i j =>
    (ha.clm_apply contDiffOn_const).inner ℝ contDiffOn_const
  have hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x := by
    intro i j x hx
    simp only [hA]
    rw [hsym x hx (b j) (b i), real_inner_comm]
  have hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : Fin (Module.finrank ℝ F) → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i := by
    intro x hx
    obtain ⟨c, hc, hcv⟩ := hell x hx
    refine ⟨c, hc, fun ξ => ?_⟩
    set v : F := ∑ j, ξ j • b j with hv
    have hbv : ∀ i, inner ℝ (b i) v = ξ i := by
      intro i
      rw [hv, inner_sum]
      simp [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    have h1 : ‖v‖ ^ 2 = ∑ i, ξ i ^ 2 := by
      rw [← b.sum_sq_norm_inner_right v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbv i, Real.norm_eq_abs, sq_abs]
    have h2 : inner ℝ (a x v) v = ∑ i, ∑ j, A i j x * ξ j * ξ i := by
      have e1 : a x v = ∑ j, ξ j • a x (b j) := by
        rw [hv, map_sum]; simp [map_smul]
      rw [e1, sum_inner, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hv, inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [inner_smul_left, inner_smul_right, hA, conj_trivial]
      ring
    rw [← h1, ← h2]
    exact hcv v
  exact ⟨hΩ, hAs, hAsym, hAell, hϱ, hpos⟩

/-- The chart weak equation as `WSol`. -/
theorem wsol_chart
    {Ω : Set F} (hΩ : IsOpen Ω) {a : F → F →L[ℝ] F} {ϱ : F → ℝ}
    (ha : ContDiffOn ℝ ∞ a Ω) (hϱ : ContDiffOn ℝ ∞ ϱ Ω)
    (hsym : ∀ x ∈ Ω, ∀ v w : F, inner ℝ (a x v) w = inner ℝ v (a x w))
    (hell : ∀ x ∈ Ω, ∃ c > 0, ∀ v : F, c * ‖v‖ ^ 2 ≤ inner ℝ (a x v) v)
    (hpos : ∀ x ∈ Ω, 0 < ϱ x)
    {lam : ℝ} {u g : F → ℝ} {Du : F → F} (hg : ContDiffOn ℝ ∞ g Ω)
    (hwg : IsWeakGradOn F Ω u Du)
    (hweak : ∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∫ x in Ω, (inner ℝ (a x (Du x)) (gradient ψ x) + lam * u x * ψ x) * ϱ x =
        ∫ x in Ω, g x * ψ x * ϱ x) :
    WSol (stdOrthonormalBasis ℝ F) Ω (fun i j x => inner ℝ (a x ((stdOrthonormalBasis ℝ F) j)) ((stdOrthonormalBasis ℝ F) i)) ϱ lam u (fun j x => inner ℝ (Du x) ((stdOrthonormalBasis ℝ F) j)) g := by
  classical
  set b := stdOrthonormalBasis ℝ F with hb
  set A : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F) → F → ℝ :=
    fun i j x => inner ℝ (a x (b j)) (b i) with hA
  set u' : Fin (Module.finrank ℝ F) → F → ℝ := fun j x => inner ℝ (Du x) (b j) with hu'
  have hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω := fun i j =>
    (ha.clm_apply contDiffOn_const).inner ℝ contDiffOn_const
  have hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x := by
    intro i j x hx
    simp only [hA]
    rw [hsym x hx (b j) (b i), real_inner_comm]
  have hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : Fin (Module.finrank ℝ F) → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i := by
    intro x hx
    obtain ⟨c, hc, hcv⟩ := hell x hx
    refine ⟨c, hc, fun ξ => ?_⟩
    set v : F := ∑ j, ξ j • b j with hv
    have hbv : ∀ i, inner ℝ (b i) v = ξ i := by
      intro i
      rw [hv, inner_sum]
      simp [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    have h1 : ‖v‖ ^ 2 = ∑ i, ξ i ^ 2 := by
      rw [← b.sum_sq_norm_inner_right v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbv i, Real.norm_eq_abs, sq_abs]
    have h2 : inner ℝ (a x v) v = ∑ i, ∑ j, A i j x * ξ j * ξ i := by
      have e1 : a x v = ∑ j, ξ j • a x (b j) := by
        rw [hv, map_sum]; simp [map_smul]
      rw [e1, sum_inner, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hv, inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [inner_smul_left, inner_smul_right, hA, conj_trivial]
      ring
    rw [← h1, ← h2]
    exact hcv v
  -- local `H¹`
  have hl2' : ∀ j, ∀ K : Set F, IsCompact K → K ⊆ Ω → MemLp (u' j) 2 (volume.restrict K) := by
    intro j K hK hKΩ
    refine (hwg.memLp_Du K hK hKΩ).mono ?_ ?_
    · exact ((hwg.memLp_Du K hK hKΩ).aestronglyMeasurable.inner aestronglyMeasurable_const)
    · refine Filter.Eventually.of_forall fun x => ?_
      simp only [hu']
      calc ‖inner ℝ (Du x) (b j)‖ ≤ ‖Du x‖ * ‖b j‖ := norm_inner_le_norm _ _
        _ = ‖Du x‖ := by simp
  have hH1 : LocH1 b Ω u u' :=
    ⟨hwg.memLp_u, hl2', fun j =>
      ⟨locallyIntegrableOn_of_locL2 F hΩ hwg.memLp_u, locallyIntegrableOn_of_locL2 F hΩ (hl2' j),
        fun φ hφ => by simpa [pd, hu'] using hwg.weak φ hφ.1 hφ.2.1 hφ.2.2 (b j)⟩⟩
  refine ⟨hH1, hg, ?_⟩
  intro φ hφ
  have hψij : ∀ i j, IsTest Ω (fun x => pd (b i) φ x * (A i j x * ϱ x)) := by
    intro i j
    have h0 := hφ.pd (b i)
    exact ⟨contDiff_mul_of_contDiffOn hΩ h0.1 h0.2.2 ((hAs i j).mul hϱ), h0.2.1.mul_right,
      tsupport_mul_subset_left.trans h0.2.2⟩
  have hint : ∀ i j, Integrable (fun x => A i j x * u' j x * pd (b i) φ x * ϱ x) volume := by
    intro i j
    have := integrable_mul_test_loc (hl2' j) (hψij i j) hΩ
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hint2 : Integrable (fun x => u x * φ x * ϱ x) volume := by
    have hψ : IsTest Ω (fun x => φ x * ϱ x) :=
      ⟨contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 hϱ, hφ.2.1.mul_right,
        tsupport_mul_subset_left.trans hφ.2.2⟩
    refine (integrable_mul_test_loc hwg.memLp_u hψ hΩ).congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- pointwise identity
  have hpt : ∀ x, (inner ℝ (a x (Du x)) (gradient φ x) + lam * u x * φ x) * ϱ x =
      (∑ i, ∑ j, A i j x * u' j x * pd (b i) φ x * ϱ x) + lam * (u x * φ x * ϱ x) := by
    intro x
    have h1 := inner_expand F b (a x) (Du x) (gradient φ x)
    have h2 : ∀ i, inner ℝ (gradient φ x) (b i) = pd (b i) φ x := by
      intro i
      simp only [pd, gradient, InnerProductSpace.toDual_symm_apply]
    simp only [h2] at h1
    rw [add_mul, h1, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    · ring
  have hΩ0 : ∀ x, x ∉ Ω → (inner ℝ (a x (Du x)) (gradient φ x) + lam * u x * φ x) * ϱ x = 0 := by
    intro x hx
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
    have hev := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hφ.2.2 h))
    have : fderiv ℝ φ x = 0 := by rw [hev.fderiv_eq]; simp
    simp [gradient, this, hφx]
  have hΩ1 : ∀ x, x ∉ Ω → g x * φ x * ϱ x = 0 := by
    intro x hx
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
    simp [hφx]
  have h := hweak φ hφ.1 hφ.2.1 hφ.2.2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hΩ0,
    setIntegral_eq_integral_of_forall_compl_eq_zero hΩ1] at h
  rw [← h]
  simp only [hpt]
  rw [integral_add (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j)
    (hint2.const_mul lam), integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hint i j]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]

/-- A function smooth on `Ω` has the classical gradient as weak gradient. -/
theorem weakGrad_of_smooth {Ω : Set F} (hΩ : IsOpen Ω) {u : F → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) :
    IsWeakGradOn F Ω u (gradient u) := by
  have hcont : ContinuousOn (gradient u) Ω := by
    have h1 : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hΩ (by simp)
    exact (InnerProductSpace.toDual ℝ F).symm.continuous.comp_continuousOn h1
  refine ⟨fun K hK hKΩ => locL2_of_continuousOn hu.continuousOn K hK hKΩ, ?_, ?_⟩
  · intro K hK hKΩ
    have hfK : ContinuousOn (gradient u) K := hcont.mono hKΩ
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfK
    haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    refine MemLp.of_bound (hfK.aestronglyMeasurable hK.measurableSet) C ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx using hC x hx
  · intro ψ hψ hψc hψT w
    obtain ⟨χ, hχ, ⟨V, hV, hKV, hV1⟩, -⟩ := exists_cutoff_nhds hψc hΩ hψT
    have hf : ContDiff ℝ ∞ (fun x => χ x * u x) := contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 hu
    have hw := (hasWDeriv_of_contDiff (Ω := Ω) (hf.of_le (by simp)) w).2.2 ψ ⟨hψ, hψc, hψT⟩
    have e1 : ∫ z, u z * fderiv ℝ ψ z w = ∫ x, χ x * u x * pd w ψ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ tsupport ψ
      · simp [pd, hV1 x (hKV hx)]
      · simp [pd_eq_zero_of_notMem hx, pd]
        have := pd_eq_zero_of_notMem hx w
        simp [pd] at this
        simp [this]
    have e2 : ∫ x, pd w (fun x => χ x * u x) x * ψ x = ∫ z, inner ℝ (gradient u z) w * ψ z := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ tsupport ψ
      · have hev : (fun x => χ x * u x) =ᶠ[nhds x] u := by
          filter_upwards [hV.mem_nhds (hKV hx)] with y hy
          simp [hV1 y hy]
        have : pd w (fun x => χ x * u x) x = inner ℝ (gradient u x) w := by
          simp only [pd, hev.fderiv_eq, gradient, InnerProductSpace.toDual_symm_apply]
        show pd w (fun x => χ x * u x) x * ψ x = _
        rw [this]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    rw [e1, ← e2]
    exact hw

theorem sobSq_zero_fun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (k : ℕ) : sobSq b k (fun _ => (0 : ℝ)) = 0 := by
  induction k with
  | zero => simp [sobSq]
  | succ k ih =>
    have hz : ∀ i, wd (b i) (fun _ => (0 : ℝ)) =ᵐ[volume] fun _ => (0 : ℝ) := fun i => by
      have hpd : pd (b i) (fun _ : E => (0 : ℝ)) = fun _ => 0 := by funext x; simp [pd]
      have hd := hasWDeriv_of_contDiff (E := E) (Ω := Set.univ) (f := fun _ : E => (0 : ℝ))
        (contDiff_const (c := (0 : ℝ))) (b i)
      rw [hpd] at hd
      have hm : MemLp (fun _ : E => (0 : ℝ)) 2 volume := by
        simpa using (MemLp.zero : MemLp (0 : E → ℝ) 2 volume)
      exact (wd_spec hd hm).2.2
    show (∫ x, (0 : ℝ) ^ 2) + ∑ i, sobSq b k (wd (b i) (fun _ => (0 : ℝ))) = 0
    simp only [sobSq_congr_ae b (hz _), ih]
    simp

/-- **Sup estimate in a chart.** -/
theorem sup_estimate_Rn
    {Ω : Set F} (hΩ : IsOpen Ω) {a : F → F →L[ℝ] F} {ϱ : F → ℝ}
    (ha : ContDiffOn ℝ ∞ a Ω) (hϱ : ContDiffOn ℝ ∞ ϱ Ω)
    (hsym : ∀ x ∈ Ω, ∀ v w : F, inner ℝ (a x v) w = inner ℝ v (a x w))
    (hell : ∀ x ∈ Ω, ∃ c > 0, ∀ v : F, c * ‖v‖ ^ 2 ≤ inner ℝ (a x v) v)
    (hpos : ∀ x ∈ Ω, 0 < ϱ x) (lam : ℝ) {χ : F → ℝ} (hχ : IsTest Ω χ) :
    ∃ (χ' : F → ℝ) (C : ℝ), IsTest Ω χ' ∧ 0 ≤ C ∧
      ∀ ũ : F → ℝ, ContDiffOn ℝ ∞ ũ Ω →
        (∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
          ∫ x in Ω, (inner ℝ (a x (gradient ũ x)) (gradient ψ x) + lam * ũ x * ψ x) * ϱ x = 0) →
        ∀ z, χ z = 1 → ũ z ^ 2 ≤ C * ∫ x, (χ' x * ũ x) ^ 2 := by
  classical
  have hc := wcoeff_chart F hΩ ha hϱ hsym hell hpos
  obtain ⟨χ', C, hχ', hC0, hC⟩ := interior_sup_estimate (stdOrthonormalBasis ℝ F) hc lam
    (j := 0) (m := Module.finrank ℝ F + 1) (by omega) hχ
  refine ⟨χ', C, hχ', hC0, fun ũ hũ hw z hz => ?_⟩
  have hwg := weakGrad_of_smooth F hΩ hũ
  have hs := wsol_chart F hΩ ha hϱ hsym hell hpos (lam := lam) (g := fun _ => 0)
    contDiffOn_const hwg (fun ψ hψ hψc hψT => by simpa using hw ψ hψ hψc hψT)
  obtain ⟨gχ, hg1, hg2, hg3⟩ := hC ũ _ (fun _ => 0) hs
  have h3 := hg3 z 0 le_rfl
  have hzero : (fun x => χ' x * (fun _ : F => (0 : ℝ)) x) = fun _ => 0 := by
    funext x; simp
  rw [hzero, sobSq_zero_fun, zero_add] at h3
  have hχu : Continuous (fun x => χ x * ũ x) :=
    (contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 hũ).continuous
  have heq : gχ = fun x => χ x * ũ x :=
    (Continuous.ae_eq_iff_eq volume hg1.continuous hχu).1 hg2
  have h4 : gχ z = ũ z := by rw [heq]; simp [hz]
  rw [norm_iteratedFDeriv_zero, h4, Real.norm_eq_abs, sq_abs] at h3
  exact h3

end Rn

end CutoffRigidity.Riemann.Diff
