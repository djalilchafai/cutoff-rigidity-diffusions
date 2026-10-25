module

public import CutoffRigidity.Riemann.DiffKuwApprox1

/-! # Sharp global smoothing: `SharpApprox` -/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Lip2

variable {X : Type*} [EMetricSpace X]

/-- Monotonicity of `locLip` with respect to inclusion of balls (the ball with the larger
centre/radius pair has the larger best Lipschitz constant). -/
theorem locLip_le_of_ball_subset (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) {p x : X} {ε₁ ε₂ : ℝ}
    (h : ∀ w, edist p w < ENNReal.ofReal ε₁ → edist x w < ENNReal.ofReal ε₂) :
    locLip ψ p ε₁ ≤ locLip ψ x ε₂ := by
  refine le_csInf (lipSet_nonempty hfin hψ x ε₂) fun c hc => csInf_le (lipSet_bddBelow ψ p ε₁) ?_
  exact ⟨hc.1, fun w w' hw hw' => hc.2 w w' (h w hw) (h w' hw')⟩

end Lip2

section Sharp2

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]

include F

theorem sharpApprox_aux [SigmaCompactSpace M] (hfin : ∀ x y : M, edist x y ≠ ⊤)
    {ψ : M → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ g : M → ℝ, MSmooth F g ∧ (∀ x, |g x - ψ x| ≤ ε) ∧
      ∀ x, ‖mgrad F g x‖ ≤ (1 + η) * locLip ψ x ε + η := by
  have := isContinuousRiemannianBundle_tangent (F := F) (M := M)
  set r : ℝ := Real.sqrt (1 + η) with hrdef
  have hr2 : r ^ 2 = 1 + η := Real.sq_sqrt (by linarith)
  have hr : 1 < r := by
    by_contra h
    push Not at h
    nlinarith [Real.sqrt_nonneg (1 + η)]
  set θ : ℝ := η / (2 * (1 + η)) with hθdef
  have hθ : 0 < θ := by positivity
  have hθη : (1 + η) * θ = η / 2 := by
    simp only [hθdef]; field_simp
  set cc : M → ℝ := fun p => locLip ψ p (ε / 2) + θ with hcc
  have hcc0 : ∀ p, 0 ≤ cc p := fun p => by
    have := locLip_nonneg ψ p (ε / 2)
    simp only [hcc]; linarith
  set S : M → Set M := fun p => {w | edist p w < ENNReal.ofReal (ε / 2)} with hSdef
  have hSo : ∀ p, IsOpen (S p) := fun p =>
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hpS : ∀ p, p ∈ S p := fun p => by
    simp only [hSdef, mem_setOf_eq, edist_self]
    exact ENNReal.ofReal_pos.2 (by linarith)
  have hSL : ∀ p, ∀ w ∈ S p, ∀ w' ∈ S p, |ψ w - ψ w'| ≤ cc p * dd w w' := fun p w hw w' hw' =>
    abs_sub_le_of_locLip_lt hfin hψ (c := cc p) (by simp only [hcc]; linarith) hw hw'
  have hloc0 := fun p => sharp_local_smooth F hfin hψ.continuous (hSo p) (hcc0 p) hr (hSL p) p
    (hpS p)
  choose V hVo hpV hVS hK hloc using hloc0
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (ι := M) 𝓘(ℝ, F)
    isClosed_univ V hVo (fun x _ => mem_iUnion.2 ⟨x, hpV x⟩)
  have hts : ∀ i, IsCompact (tsupport (ρ i)) := fun i => by
    obtain ⟨K, hKc, hKV⟩ := hK i
    exact hKc.of_isClosed_subset (isClosed_tsupport _) ((hρ i).trans hKV)
  have hC : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport (ρ i), ‖mgrad F (ρ i) x‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (hts i).exists_bound_of_continuousOn
      (f := fun x => ‖mgrad F (ρ i) x‖)
      (continuous_norm_mgrad F (ρ i).contMDiff).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx => by
      have := hC x hx
      rw [norm_norm] at this
      exact this.trans (le_max_left _ _)⟩
  choose C hC0 hCb using hC
  have hcount : Countable {i : M // (Function.support (ρ i)).Nonempty} := by
    have hlf := (ρ.locallyFinite).comp_injective
      (Subtype.val_injective (p := fun i : M => (Function.support (ρ i)).Nonempty))
    exact (Set.countable_univ_iff.1 (hlf.countable_univ (fun i => i.2)))
  classical
  obtain ⟨nn, hnn⟩ := hcount.exists_injective_nat
  let n : M → ℕ := fun i => if h : (Function.support (ρ i)).Nonempty then nn ⟨i, h⟩ else 0
  have hn_inj : ∀ i j, (Function.support (ρ i)).Nonempty → (Function.support (ρ j)).Nonempty →
      n i = n j → i = j := by
    intro i j hi hj hij
    have e1 : n i = nn ⟨i, hi⟩ := by simp only [n]; exact dif_pos hi
    have e2 : n j = nn ⟨j, hj⟩ := by simp only [n]; exact dif_pos hj
    rw [e1, e2] at hij
    exact congrArg Subtype.val (hnn hij)
  set a : M → ℝ := fun i => η / 2 * (1 / 2 : ℝ) ^ (n i + 1) with hadef
  have hapos : ∀ i, 0 < a i := fun i => by simp only [hadef]; positivity
  set δ : M → ℝ := fun i => min ε (a i / (C i + 1)) with hδ
  have hδpos : ∀ i, 0 < δ i := fun i => by
    have := hC0 i
    have := hapos i
    simp only [hδ]; exact lt_min hε (by positivity)
  have hδle : ∀ i, δ i ≤ ε := fun i => min_le_left _ _
  have hδC : ∀ i, δ i * C i ≤ a i := fun i => by
    have h0 := hC0 i
    have h1 := hapos i
    calc δ i * C i ≤ a i / (C i + 1) * C i :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) h0
      _ ≤ a i := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  choose g hgs hgv hgd using fun i => hloc i (δ i) (hδpos i)
  set ψ' : M → ℝ := fun x => ∑ᶠ i, ρ i x * g i x with hψ'
  have hψsm : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ ψ' := by
    have := ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (g := g) (fun i x hx => hgs i x (hρ i hx))
    simpa [smul_eq_mul] using this
  have hmemS : ∀ x₀ i, ρ i x₀ ≠ 0 → i ∈ ρ.fintsupport x₀ := fun x₀ i hi =>
    (ρ.mem_fintsupport_iff x₀ i).2 (subset_tsupport _ hi)
  have hloc' : ∀ x₀, ∀ᶠ y in 𝓝 x₀, ∀ i, ρ i y ≠ 0 → i ∈ ρ.fintsupport x₀ := by
    intro x₀
    filter_upwards [ρ.eventually_fintsupport_subset x₀] with y hy i hi
    exact hy (hmemS y i hi)
  have hψeq : ∀ x₀ y, (∀ i, ρ i y ≠ 0 → i ∈ ρ.fintsupport x₀) →
      ψ' y = ∑ i ∈ ρ.fintsupport x₀, ρ i y * g i y := by
    intro x₀ y hy
    exact finsum_eq_sum_of_support_subset _ (fun i hi => hy i (left_ne_zero_of_mul hi))
  have hsum1 : ∀ x₀ y, (∀ i, ρ i y ≠ 0 → i ∈ ρ.fintsupport x₀) →
      ∑ i ∈ ρ.fintsupport x₀, ρ i y = 1 := by
    intro x₀ y hy
    rw [← finsum_eq_sum_of_support_subset (s := ρ.fintsupport x₀) _ (fun i hi => hy i hi)]
    exact ρ.sum_eq_one (mem_univ y)
  refine ⟨ψ', hψsm, ?_, ?_⟩
  · intro x₀
    set S' := ρ.fintsupport x₀ with hSdef'
    have hS : ∀ i, ρ i x₀ ≠ 0 → i ∈ S' := hmemS x₀
    have h1 := hsum1 x₀ x₀ hS
    rw [hψeq x₀ x₀ hS]
    have e : ∑ i ∈ S', ρ i x₀ * g i x₀ - ψ x₀ = ∑ i ∈ S', ρ i x₀ * (g i x₀ - ψ x₀) := by
      rw [Finset.sum_congr rfl (fun i _ => mul_sub (ρ i x₀) (g i x₀) (ψ x₀)),
        Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rw [e]
    calc |∑ i ∈ S', ρ i x₀ * (g i x₀ - ψ x₀)|
        ≤ ∑ i ∈ S', |ρ i x₀ * (g i x₀ - ψ x₀)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S', ρ i x₀ * ε := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (ρ.nonneg i x₀)]
        have hxV : x₀ ∈ V i := hρ i ((ρ.mem_fintsupport_iff x₀ i).1 hi)
        exact mul_le_mul_of_nonneg_left
          ((hgv i x₀ hxV).trans (hδle i)) (ρ.nonneg i x₀)
      _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
  · intro x₀
    set S' := ρ.fintsupport x₀ with hSdef'
    set l := locLip ψ x₀ ε with hl
    have hl0 : 0 ≤ l := locLip_nonneg ψ x₀ ε
    have hev := hloc' x₀
    have hxS : ∀ i ∈ S', x₀ ∈ tsupport (ρ i) := fun i hi => (ρ.mem_fintsupport_iff x₀ i).1 hi
    have hdρ : ∀ i, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (ρ i) x₀ := fun i =>
      ((ρ i).contMDiff.mdifferentiable (by simp)) x₀
    have hdg : ∀ i ∈ S', MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (g i) x₀ := fun i hi =>
      (hgs i x₀ (hρ i (hxS i hi))).mdifferentiableAt (by simp)
    have hψφ : ψ' =ᶠ[𝓝 x₀] fun y => ∑ i ∈ S', ρ i y * g i y := by
      filter_upwards [hev] with y hy using hψeq x₀ y hy
    have h1ev : (fun y => ∑ i ∈ S', ρ i y) =ᶠ[𝓝 x₀] fun _ => (1 : ℝ) := by
      filter_upwards [hev] with y hy using hsum1 x₀ y hy
    have hd1 : ∑ i ∈ S', mvfderiv 𝓘(ℝ, F) (ρ i) x₀ = 0 := by
      rw [← mvfderiv_finset_sum F S' (fun i => ρ i) (fun i _ => hdρ i),
        mvfderiv_congr_ev F h1ev, mvfderiv_const]
    have hdψ : mvfderiv 𝓘(ℝ, F) ψ' x₀ =
        ∑ i ∈ S', (ρ i x₀ • mvfderiv 𝓘(ℝ, F) (g i) x₀ + g i x₀ • mvfderiv 𝓘(ℝ, F) (ρ i) x₀) := by
      rw [mvfderiv_congr_ev F hψφ,
        mvfderiv_finset_sum F S' (fun i y => ρ i y * g i y) (fun i hi => (hdρ i).mul (hdg i hi))]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      exact mvfderiv_fun_mul (hdρ i) (hdg i hi)
    apply norm_mgrad_le_of F (by positivity)
    intro v
    have hv1 : ∑ i ∈ S', mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v = 0 := by
      have := congrArg (fun L => L v) hd1
      simpa [sum_apply] using this
    have hdψv : mvfderiv 𝓘(ℝ, F) ψ' x₀ v = ∑ i ∈ S', ρ i x₀ * mvfderiv 𝓘(ℝ, F) (g i) x₀ v +
        ∑ i ∈ S', (g i x₀ - ψ x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v := by
      rw [hdψ, sum_apply]
      have : ∑ i ∈ S', (g i x₀ - ψ x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v =
          ∑ i ∈ S', g i x₀ * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v -
            ψ x₀ * ∑ i ∈ S', mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, hv1, mul_zero, sub_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp)
    have hsum1' : ∑ i ∈ S', ρ i x₀ = 1 := hsum1 x₀ x₀ (hmemS x₀)
    have hne : ∀ i ∈ S', (Function.support (ρ i)).Nonempty := fun i hi => by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have := hxS i hi
      simp [tsupport, h] at this
    have hinj : Set.InjOn n (S' : Set M) := fun i hi j hj hij =>
      hn_inj i j (hne i hi) (hne j hj) hij
    have hgeo : ∑ i ∈ S', (1 / 2 : ℝ) ^ (n i + 1) ≤ 1 := by
      rw [← Finset.sum_image (f := fun k => (1 / 2 : ℝ) ^ (k + 1)) hinj]
      exact CutCur.sum_half_pow_succ_le _
    -- comparison of local Lipschitz constants
    have hcmp : ∀ i ∈ S', cc i ≤ l + θ := by
      intro i hi
      have hxV : x₀ ∈ V i := hρ i (hxS i hi)
      have hxS' : edist i x₀ < ENNReal.ofReal (ε / 2) := hVS i hxV
      have : locLip ψ i (ε / 2) ≤ locLip ψ x₀ ε := by
        refine locLip_le_of_ball_subset hfin hψ fun w hw => ?_
        calc edist x₀ w ≤ edist x₀ i + edist i w := edist_triangle _ _ _
          _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
              rw [edist_comm x₀ i]
              exact ENNReal.add_lt_add hxS' hw
          _ = ENNReal.ofReal ε := by
              rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
      simp only [hcc]; linarith
    have hA : |∑ i ∈ S', ρ i x₀ * mvfderiv 𝓘(ℝ, F) (g i) x₀ v| ≤ (1 + η) * (l + θ) * ‖v‖ := by
      calc _ ≤ ∑ i ∈ S', |ρ i x₀ * mvfderiv 𝓘(ℝ, F) (g i) x₀ v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ S', ρ i x₀ * ((1 + η) * (l + θ) * ‖v‖) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_of_nonneg (ρ.nonneg i x₀)]
          refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg i x₀)
          refine (hgd i x₀ (hρ i (hxS i hi)) v).trans ?_
          rw [hr2]
          have := hcmp i hi
          gcongr
        _ = (1 + η) * (l + θ) * ‖v‖ := by rw [← Finset.sum_mul, hsum1', one_mul]
    have hB : |∑ i ∈ S', (g i x₀ - ψ x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v| ≤ η / 2 * ‖v‖ := by
      calc _ ≤ ∑ i ∈ S', |(g i x₀ - ψ x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ S', η / 2 * ((1 / 2 : ℝ) ^ (n i + 1)) * ‖v‖ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          have h1 : |g i x₀ - ψ x₀| ≤ δ i := hgv i x₀ (hρ i (hxS i hi))
          have h2 : |mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v| ≤ C i * ‖v‖ :=
            (abs_mvfderiv_le_norm_mgrad F (ρ i) x₀ v).trans
              (mul_le_mul_of_nonneg_right (hCb i x₀ (hxS i hi)) (norm_nonneg _))
          calc |g i x₀ - ψ x₀| * |mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v|
              ≤ δ i * (C i * ‖v‖) :=
                mul_le_mul h1 h2 (abs_nonneg _) (hδpos i).le
            _ = (δ i * C i) * ‖v‖ := by ring
            _ ≤ a i * ‖v‖ :=
                mul_le_mul_of_nonneg_right (hδC i) (norm_nonneg _)
        _ = η / 2 * (∑ i ∈ S', (1 / 2 : ℝ) ^ (n i + 1)) * ‖v‖ := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ ≤ η / 2 * 1 * ‖v‖ := by
            gcongr
        _ = η / 2 * ‖v‖ := by ring
    rw [hdψv]
    have key : (1 + η) * (l + θ) + η / 2 = (1 + η) * l + η := by
      have : (1 + η) * (l + θ) = (1 + η) * l + (1 + η) * θ := by ring
      rw [this, hθη]; ring
    calc _ ≤ |∑ i ∈ S', ρ i x₀ * mvfderiv 𝓘(ℝ, F) (g i) x₀ v| +
          |∑ i ∈ S', (g i x₀ - ψ x₀) * mvfderiv 𝓘(ℝ, F) (ρ i) x₀ v| := abs_add_le _ _
      _ ≤ (1 + η) * (l + θ) * ‖v‖ + η / 2 * ‖v‖ := add_le_add hA hB
      _ = ((1 + η) * l + η) * ‖v‖ := by rw [← add_mul, key]

/-- **Sharp smooth approximation of Lipschitz functions.** -/
theorem sharpApprox [ConnectedSpace M] [CompleteSpace M] : SharpApprox F M := by
  intro ψ L hψ ε η hε hη
  haveI := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  exact sharpApprox_aux F (edist_ne_top_of_connected F) hψ hε hη

end Sharp2

end CutoffRigidity.Riemann.Diff
