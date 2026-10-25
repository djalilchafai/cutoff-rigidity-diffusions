module

public import CutoffRigidity.Riemann.DiffEllipticRn3

/-! # Cutoff functions, supports of weak derivatives
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- Smooth cutoff function: `1` on a compact set `K`, with compact support inside the open set
`U ⊇ K`, values in `[0,1]`. -/
theorem exists_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ x ∈ K, χ x = 1) ∧
      ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨f, hf, hr, hs, ht⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    hV.isClosed_compl hK.isClosed (Set.disjoint_compl_left_iff_subset.2 hKV)
  have hsupp : Function.support f ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx ((hs x).1 hxV)
  have hts : tsupport f ⊆ closure V := closure_mono hsupp
  refine ⟨f, hf, ?_, hts.trans hVU, fun x hx => (ht x).1 hx, fun x => ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact hVc (hsupp.trans subset_closure)
  · have := hr (Set.mem_range_self x)
    exact this

theorem aesupp_of_hasWDeriv {v : E} {w w' : E → ℝ} (hs : AESupp w)
    (h : HasWDeriv Set.univ v w w') : AESupp w' := by
  obtain ⟨R, hR⟩ := hs
  refine ⟨R, ?_⟩
  have hw' : LocallyIntegrable w' volume := locallyIntegrableOn_univ.mp h.2.1
  set U : Set E := {x | R < ‖x‖} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_norm
  let Kn : ℕ → Set E := fun n => {x | R + 1 / ((n : ℝ) + 1) ≤ ‖x‖ ∧ ‖x‖ ≤ n}
  have hKc : ∀ n, IsCompact (Kn n) := by
    intro n
    refine (isCompact_closedBall (0 : E) n).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro x hx; simpa using hx.2
  have hKU : ∀ n, Kn n ⊆ U := by
    intro n x hx
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    show R < ‖x‖
    linarith [hx.1]
  have hn : ∀ n, ∀ᵐ x ∂(volume : Measure E), x ∈ Kn n → w' x = 0 := by
    intro n
    obtain ⟨χ, hχ, hχc, hχU, hχ1, -⟩ := exists_cutoff (hKc n) hUo (hKU n)
    have h0 : ∀ᵐ x ∂(volume : Measure E), χ x * w' x = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (f := fun x => χ x * w' x) ?_ ?_
      · exact locallyIntegrableOn_univ.1 ((locallyIntegrableOn_univ.2 hw').continuousOn_mul
          hχ.continuous.continuousOn isOpen_univ.isLocallyClosed)
      · intro g hg hgc
        have ht : IsTest Set.univ (fun x => g x * χ x) :=
          ⟨hg.mul hχ, hgc.mul_right, Set.subset_univ _⟩
        have e1 := h.2.2 _ ht
        have hz : ∫ x, w x * pd v (fun x => g x * χ x) x = 0 := by
          refine integral_eq_zero_of_ae ?_
          filter_upwards [hR] with x hx
          by_cases hp : pd v (fun x => g x * χ x) x = 0
          · simp [hp]
          · have h1 : x ∈ tsupport (pd v (fun x => g x * χ x)) := subset_tsupport _ hp
            have h2 := (ht.pd v).2.2 h1
            have h3 : x ∈ tsupport (fun x => g x * χ x) :=
              (tsupport_fderiv_apply_subset ℝ v) h1
            have h4 : x ∈ tsupport χ := tsupport_mul_subset_right h3
            have h5 : R < ‖x‖ := hχU h4
            simp [hx h5]
        rw [hz] at e1
        simp only [smul_eq_mul]
        have : ∫ x, w' x * (g x * χ x) = 0 := by linarith
        rw [← this]
        congr 1; funext x; ring
    filter_upwards [h0] with x hx hxK
    have := hχ1 x hxK
    rw [this, one_mul] at hx
    exact hx
  have hall : ∀ᵐ x ∂(volume : Measure E), ∀ n, x ∈ Kn n → w' x = 0 := ae_all_iff.2 hn
  filter_upwards [hall] with x hx hRx
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ ‖x‖ - R ∧ ‖x‖ ≤ n := by
    obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt (sub_pos.2 hRx)
    obtain ⟨n2, hn2⟩ := exists_nat_ge ‖x‖
    refine ⟨max n1 n2, ?_, ?_⟩
    · refine le_trans ?_ hn1.le
      apply one_div_le_one_div_of_le (by positivity)
      have : (n1 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_left _ _
      linarith
    · refine hn2.trans ?_
      exact_mod_cast le_max_right _ _
  exact hx n ⟨by linarith, hn2⟩

end CutoffRigidity.Riemann.Diff
