module

public import CutoffRigidity.Riemann.DiffRegSmooth

/-! # Regularity bootstrap, part 3: smooth potentials (workstream KER-REG)

`weak_solution_locSob_step_pot`, `regularity_step_Rn_pot`: the REG steps of `DiffReg1` with the
constant `lam` replaced by a smooth potential `ℓ`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

section RnStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

/-- **Gain of two derivatives for `-div(ϱ A ∇u) + ℓ ϱ u = ϱ g`** with `g ∈ H^m_loc` and smooth potential `ℓ`. -/
theorem weak_solution_locSob_step_pot {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {ϱ : E → ℝ} (hϱ : ContDiffOn ℝ ∞ ϱ Ω) (hϱpos : ∀ x ∈ Ω, 0 < ϱ x) {ℓ : E → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ Ω)
    {g : E → ℝ} (hg : LocL2 Ω g) {u : E → ℝ} {u' : ι → E → ℝ}
    (hu : LocH1 b Ω u u')
    (hweak : ∀ φ, IsTest Ω φ →
      (∑ i, ∑ j, ∫ x, A i j x * u' j x * pd (b i) φ x * ϱ x) + ∫ x, ℓ x * u x * φ x * ϱ x =
        ∫ x, g x * φ x * ϱ x)
    (m : ℕ) (hgm : LocSob b Ω m g) : LocSob b Ω (m + 2) u := by
  set At : ι → ι → E → ℝ := fun i j x => ϱ x * A i j x with hAt
  have hAts : ∀ i j, ContDiffOn ℝ ∞ (At i j) Ω := fun i j => hϱ.mul (hAs i j)
  have hAtsym : ∀ i j, ∀ x ∈ Ω, At i j x = At j i x := fun i j x hx => by
    simp only [hAt, hAsym i j x hx]
  have hAtell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, At i j x * ξ j * ξ i := by
    intro x hx
    obtain ⟨c, hc, hell⟩ := hAell x hx
    refine ⟨ϱ x * c, mul_pos (hϱpos x hx) hc, fun ξ => ?_⟩
    have := mul_le_mul_of_nonneg_left (hell ξ) (hϱpos x hx).le
    calc ϱ x * c * ∑ i, ξ i ^ 2 = ϱ x * (c * ∑ i, ξ i ^ 2) := by ring
      _ ≤ ϱ x * ∑ i, ∑ j, A i j x * ξ j * ξ i := this
      _ = _ := by
        simp only [hAt, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
  set F : E → ℝ := fun x => ϱ x * g x - (ℓ x * ϱ x) * u x with hFdef
  have hF : LocL2 Ω F := by
    intro K hK hKΩ
    exact ((locL2_mul hg hϱ.continuousOn) K hK hKΩ).sub
      ((locL2_mul hu.l2 (hℓ.continuousOn.mul hϱ.continuousOn)) K hK hKΩ)
  have heq : LocEq b Ω At u' F := by
    intro φ hφ
    have h := hweak φ hφ
    have hψ : IsTest Ω (fun x => φ x * ϱ x) :=
      ⟨contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 hϱ, hφ.2.1.mul_right,
        tsupport_mul_subset_left.trans hφ.2.2⟩
    have I1 : Integrable (fun x => g x * φ x * ϱ x) volume := by
      refine (integrable_mul_test_loc hg hψ hΩ).congr (Filter.Eventually.of_forall fun x => ?_)
      ring
    have hψ2 : IsTest Ω (fun x => φ x * (ℓ x * ϱ x)) :=
      ⟨contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 (hℓ.mul hϱ), hφ.2.1.mul_right,
        tsupport_mul_subset_left.trans hφ.2.2⟩
    have I2 : Integrable (fun x => ℓ x * u x * φ x * ϱ x) volume := by
      refine (integrable_mul_test_loc hu.l2 hψ2 hΩ).congr (Filter.Eventually.of_forall fun x => ?_)
      ring
    have e1 : ∫ x, F x * φ x = (∫ x, g x * φ x * ϱ x) - ∫ x, ℓ x * u x * φ x * ϱ x := by
      rw [← integral_sub I1 I2]
      congr 1; funext x; simp only [hFdef]; ring
    rw [e1]
    have e2 : ∀ i j, ∫ x, At i j x * u' j x * pd (b i) φ x =
        ∫ x, A i j x * u' j x * pd (b i) φ x * ϱ x := by
      intro i j; congr 1; funext x; simp only [hAt]; ring
    simp only [e2]
    linarith
  have hFreg : ∀ k, k ≤ m → LocSob b Ω (k + 1) u → LocSob b Ω k F := by
    intro k hk hum χ hχ
    have hs2 : ContDiff ℝ ∞ (fun x => χ x * ϱ x) :=
      contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 hϱ
    have hs3 : ContDiff ℝ ∞ (fun x => χ x * (ℓ x * ϱ x)) :=
      contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 (hℓ.mul hϱ)
    have S1 := sob_mul_of_locSob b hΩ (hgm.mono b hk) hs2 hχ.2.1.mul_right
      (tsupport_mul_subset_left.trans hχ.2.2)
    have S2 := sob_mul_of_locSob b hΩ hum hs3 hχ.2.1.mul_right
      (tsupport_mul_subset_left.trans hχ.2.2)
    have S2' := Sob.mono b (Nat.le_succ k) S2
    have S4 := (Sob.sub b S1 S2').1
    refine Sob.congr_ae b S4 (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFdef]; ring
  have key : ∀ k, k ≤ m + 1 → LocSob b Ω (k + 1) u := by
    intro k
    induction k with
    | zero => intro _; exact hu.locSob b hΩ
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      exact locSob_step b hΩ hAts hAtsym hAtell hu hF heq k ih' (hFreg k (by omega) ih')
  exact key (m + 1) le_rfl

end RnStep

section Bridge

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Regularity step in `F` (chart form, smooth potential)**: `-div(ϱ a ∇u) + ℓ ϱ u = ϱ g` with `g ∈ H^m_loc` gives
`u ∈ H^{m+2}_loc`, where `LocSob` is taken in the standard orthonormal basis. -/
theorem regularity_step_Rn_pot {Ω : Set F} (hΩ : IsOpen Ω) {a : F → F →L[ℝ] F} {ϱ : F → ℝ} {ℓ : F → ℝ}
    (hℓ : ContDiffOn ℝ ∞ ℓ Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hϱ : ContDiffOn ℝ ∞ ϱ Ω)
    (hsym : ∀ x ∈ Ω, ∀ v w : F, inner ℝ (a x v) w = inner ℝ v (a x w))
    (hell : ∀ x ∈ Ω, ∃ c > 0, ∀ v : F, c * ‖v‖ ^ 2 ≤ inner ℝ (a x v) v)
    (hpos : ∀ x ∈ Ω, 0 < ϱ x) {u g : F → ℝ} {Du : F → F} (hg : LocL2 Ω g)
    (hwg : IsWeakGradOn F Ω u Du)
    (hweak : ∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∫ x in Ω, (inner ℝ (a x (Du x)) (gradient ψ x) + ℓ x * u x * ψ x) * ϱ x =
        ∫ x in Ω, g x * ψ x * ϱ x) (m : ℕ)
    (hgm : LocSob (stdOrthonormalBasis ℝ F) Ω m g) :
    LocSob (stdOrthonormalBasis ℝ F) Ω (m + 2) u := by
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
  refine weak_solution_locSob_step_pot b hΩ (A := A) hAs hAsym hAell hϱ hpos hℓ hg hH1 ?_ m hgm
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
  have hint2 : Integrable (fun x => ℓ x * u x * φ x * ϱ x) volume := by
    have hψ : IsTest Ω (fun x => φ x * (ℓ x * ϱ x)) :=
      ⟨contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 (hℓ.mul hϱ), hφ.2.1.mul_right,
        tsupport_mul_subset_left.trans hφ.2.2⟩
    refine (integrable_mul_test_loc hwg.memLp_u hψ hΩ).congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- pointwise identity
  have hpt : ∀ x, (inner ℝ (a x (Du x)) (gradient φ x) + ℓ x * u x * φ x) * ϱ x =
      (∑ i, ∑ j, A i j x * u' j x * pd (b i) φ x * ϱ x) + ℓ x * u x * φ x * ϱ x := by
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
  have hΩ0 : ∀ x, x ∉ Ω → (inner ℝ (a x (Du x)) (gradient φ x) + ℓ x * u x * φ x) * ϱ x = 0 := by
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
    hint2, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hint i j]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]

end Bridge

end CutoffRigidity.Riemann.Diff
