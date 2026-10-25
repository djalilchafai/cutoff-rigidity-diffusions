module

public import CutoffRigidity.Riemann.DiffEllipticRn15

/-! # The interior estimate (quantitative)
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

/-- Domination of a cutoff norm by a larger cutoff norm. -/
theorem exists_dom_const {Ω : Set E} {a : E → ℝ} (ha : IsTest Ω a) (m : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (χ' f : E → ℝ), (∀ x ∈ tsupport a, χ' x = 1) →
      Sob b m (fun x => χ' x * f x) →
      Sob b m (fun x => a x * f x) ∧
        sobSq b m (fun x => a x * f x) ≤ c * sobSq b m (fun x => χ' x * f x) := by
  obtain ⟨c, hc0, hc⟩ := exists_mul_const b ha.1 ha.2.1 m
  refine ⟨c, hc0, fun χ' f h1 hf => ?_⟩
  have e : (fun x => a x * f x) = fun x => a x * (χ' x * f x) := by
    funext x
    by_cases hx : x ∈ tsupport a
    · rw [h1 x hx]; ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [e]
  exact hc _ hf

/-- The cutoff norm of the right-hand side is controlled by cutoff norms of `g` and `u`. -/
theorem rhs_bound {Ω : Set E} {A : ι → ι → E → ℝ} {ϱ : E → ℝ} (hc : WCoeff Ω A ϱ) (lam : ℝ)
    {χ₁ χ_a : E → ℝ} (hχ₁ : IsTest Ω χ₁) (hχa : IsTest Ω χ_a)
    (h1 : ∀ x ∈ tsupport χ₁, χ_a x = 1) (m : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (u : E → ℝ) (u' : ι → E → ℝ) (g : E → ℝ),
      WSol b Ω A ϱ lam u u' g →
      sobSq b m (fun x => χ₁ x * wRHS ϱ lam g u x) ≤
        c * (sobSq b m (fun x => χ_a x * g x) + sobSq b m (fun x => χ_a x * u x)) := by
  have hΩ := hc.open_
  have hat : IsTest Ω (fun x => χ₁ x * ϱ x) :=
    ⟨contDiff_mul_of_contDiffOn hΩ hχ₁.1 hχ₁.2.2 hc.rho_smooth, hχ₁.2.1.mul_right,
      tsupport_mul_subset_left.trans hχ₁.2.2⟩
  have hts : tsupport (fun x => χ₁ x * ϱ x) ⊆ tsupport χ₁ := tsupport_mul_subset_left
  obtain ⟨ca, hca0, hca⟩ := exists_dom_const b hat m
  refine ⟨2 * ca * (1 + lam ^ 2), by positivity, fun u u' g hs => ?_⟩
  have hSg : Sob b m (fun x => χ_a x * g x) := locSob_of_contDiffOn b hΩ hs.g_smooth m χ_a hχa
  have hSu : Sob b m (fun x => χ_a x * u x) := hs.locSob_all b hc m χ_a hχa
  obtain ⟨g1, g2⟩ := hca χ_a g (fun x hx => h1 x (hts hx)) hSg
  obtain ⟨u1, u2⟩ := hca χ_a u (fun x hx => h1 x (hts hx)) hSu
  obtain ⟨s1, s2⟩ := Sob.smul b lam u1
  obtain ⟨d1, d2⟩ := Sob.sub b g1 s1
  have e : (fun x => χ₁ x * wRHS ϱ lam g u x) =
      fun x => (χ₁ x * ϱ x) * g x - lam * ((χ₁ x * ϱ x) * u x) := by
    funext x; simp only [wRHS]; ring
  rw [e]
  refine d2.trans ?_
  rw [s2]
  have n1 := sobSq_nonneg b m (fun x => χ_a x * g x)
  have n2 := sobSq_nonneg b m (fun x => χ_a x * u x)
  have n3 : 0 ≤ lam ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left g2 (by norm_num : (0:ℝ) ≤ 2),
    mul_le_mul_of_nonneg_left u2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) n3), mul_nonneg hca0 n1,
    mul_nonneg hca0 n2, mul_nonneg (mul_nonneg hca0 n3) n2]

/-- **Interior estimate** (cutoff form): for every cutoff `χ` and every order `k` there are a
cutoff `χ'` and a constant `C`, independent of the solution, such that
`‖χ u‖²_{H^k} ≤ C (‖χ' g‖²_{H^{k-2}} + ‖χ' u‖²_{L²})`. -/
theorem interior_estimate {Ω : Set E} {A : ι → ι → E → ℝ} {ϱ : E → ℝ} (hc : WCoeff Ω A ϱ)
    (lam : ℝ) : ∀ k : ℕ, ∀ χ : E → ℝ, IsTest Ω χ → ∃ (χ' : E → ℝ) (C : ℝ), IsTest Ω χ' ∧
      0 ≤ C ∧ ∀ (u : E → ℝ) (u' : ι → E → ℝ) (g : E → ℝ), WSol b Ω A ϱ lam u u' g →
        sobSq b k (fun x => χ x * u x) ≤
          C * (sobSq b (k - 2) (fun x => χ' x * g x) + sobSq b 0 (fun x => χ' x * u x)) := by
  have hΩ := hc.open_
  obtain ⟨hw1, hw2, hw3⟩ := hc.weighted
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro χ hχ
    rcases k with _ | _ | m
    · -- k = 0
      obtain ⟨χ₁, hχ₁, ⟨V, hV, hKV, hV1⟩, -⟩ := exists_cutoff_nhds hχ.2.1 hΩ hχ.2.2
      obtain ⟨c, hc0, hcd⟩ := exists_dom_const b hχ 0
      refine ⟨χ₁, c, hχ₁, hc0, fun u u' g hs => ?_⟩
      have hS : Sob b 0 (fun x => χ₁ x * u x) := hs.locSob_all b hc 0 χ₁ hχ₁
      have h1 := (hcd χ₁ u (fun x hx => hV1 x (hKV hx)) hS).2
      have h2 := sobSq_nonneg b (0 - 2) (fun x => χ₁ x * g x)
      have h3 := sobSq_nonneg b 0 (fun x => χ₁ x * u x)
      simp only [Nat.zero_sub] at h2 ⊢
      nlinarith [mul_nonneg hc0 h2]
    · -- k = 1 (Caccioppoli)
      obtain ⟨χ₁, C₀, hχ₁, hC₀, hcac⟩ := caccioppoli b hΩ hw1 hw2 hw3 hχ
      obtain ⟨χ₂, hχ₂, ⟨V, hV, hKV, hV1⟩, -⟩ := exists_cutoff_nhds hχ₁.2.1 hΩ hχ₁.2.2
      have hb2 : ∀ x ∈ tsupport χ₁, χ₂ x = 1 := fun x hx => hV1 x (hKV hx)
      obtain ⟨c, hc0, hcr⟩ := rhs_bound b hc lam hχ₁ hχ₂ hb2 0
      obtain ⟨c₁, hc10, hcd⟩ := exists_dom_const b hχ₁ 0
      refine ⟨χ₂, C₀ * (c + c₁), hχ₂, by positivity, fun u u' g hs => ?_⟩
      have h1 := hcac u u' (wRHS ϱ lam g u) hs.h1 (hs.locL2_rhs b hc) (hs.locEq b hc)
      have h2 := hcr u u' g hs
      have hS : Sob b 0 (fun x => χ₂ x * u x) := hs.locSob_all b hc 0 χ₂ hχ₂
      have h3 := (hcd χ₂ u hb2 hS).2
      have h4 := sobSq_nonneg b 0 (fun x => χ₂ x * g x)
      have h5 := sobSq_nonneg b 0 (fun x => χ₂ x * u x)
      have e : (1 : ℕ) - 2 = 0 := rfl
      rw [e]
      have h6 : sobSq b 0 (fun x => χ₁ x * wRHS ϱ lam g u x) + sobSq b 0 (fun x => χ₁ x * u x) ≤
          (c + c₁) * (sobSq b 0 (fun x => χ₂ x * g x) + sobSq b 0 (fun x => χ₂ x * u x)) := by
        nlinarith [mul_nonneg hc0 h4, mul_nonneg hc10 h4, mul_nonneg hc0 h5, mul_nonneg hc10 h5]
      calc sobSq b 1 (fun x => χ x * u x) ≤
          C₀ * (sobSq b 0 (fun x => χ₁ x * wRHS ϱ lam g u x) + sobSq b 0 (fun x => χ₁ x * u x)) := h1
        _ ≤ C₀ * ((c + c₁) * (sobSq b 0 (fun x => χ₂ x * g x) + sobSq b 0 (fun x => χ₂ x * u x))) :=
            mul_le_mul_of_nonneg_left h6 hC₀
        _ = _ := by ring
    · -- k = m + 2
      obtain ⟨χ₁, χ₂, C₁, hχ₁, hχ₂, hC₁, hstep⟩ := interior_step b hΩ hw1 hw2 hw3 m hχ
      obtain ⟨χ₃, C₂, hχ₃, hC₂, hIH₂⟩ := ih (m + 1) (by omega) χ₂ hχ₂
      obtain ⟨χa, hχa, ⟨Va, hVa, hKVa, hVa1⟩, -⟩ := exists_cutoff_nhds hχ₁.2.1 hΩ hχ₁.2.2
      have hba : ∀ x ∈ tsupport χ₁, χa x = 1 := fun x hx => hVa1 x (hKVa hx)
      obtain ⟨c, hc0, hcr⟩ := rhs_bound b hc lam hχ₁ hχa hba m
      obtain ⟨χ₅, C₃, hχ₅, hC₃, hIH₃⟩ := ih m (by omega) χa hχa
      have hK : IsCompact (tsupport χ₃ ∪ tsupport χa ∪ tsupport χ₅) :=
        (hχ₃.2.1.union hχa.2.1).union hχ₅.2.1
      have hKΩ : tsupport χ₃ ∪ tsupport χa ∪ tsupport χ₅ ⊆ Ω :=
        Set.union_subset (Set.union_subset hχ₃.2.2 hχa.2.2) hχ₅.2.2
      obtain ⟨χ', hχ', ⟨V, hV, hKV, hV1⟩, -⟩ := exists_cutoff_nhds hK hΩ hKΩ
      have h3 : ∀ x ∈ tsupport χ₃, χ' x = 1 := fun x hx =>
        hV1 x (hKV (Or.inl (Or.inl hx)))
      have ha' : ∀ x ∈ tsupport χa, χ' x = 1 := fun x hx =>
        hV1 x (hKV (Or.inl (Or.inr hx)))
      have h5 : ∀ x ∈ tsupport χ₅, χ' x = 1 := fun x hx => hV1 x (hKV (Or.inr hx))
      obtain ⟨d3g, hd3g0, hd3g⟩ := exists_dom_const b hχ₃ (m + 1 - 2)
      obtain ⟨d3u, hd3u0, hd3u⟩ := exists_dom_const b hχ₃ 0
      obtain ⟨dag, hdag0, hdag⟩ := exists_dom_const b hχa m
      obtain ⟨d5g, hd5g0, hd5g⟩ := exists_dom_const b hχ₅ (m - 2)
      obtain ⟨d5u, hd5u0, hd5u⟩ := exists_dom_const b hχ₅ 0
      set Cfin : ℝ := C₁ * (c * dag + c * C₃ * d5g + c * C₃ * d5u + C₂ * d3g + C₂ * d3u) with hCfin
      refine ⟨χ', Cfin, hχ', by rw [hCfin]; positivity, fun u u' g hs => ?_⟩
      have hSg : ∀ L, Sob b L (fun x => χ' x * g x) := fun L =>
        locSob_of_contDiffOn b hΩ hs.g_smooth L χ' hχ'
      have hSu : ∀ L, Sob b L (fun x => χ' x * u x) := fun L => hs.locSob_all b hc L χ' hχ'
      have h0 := hstep u u' (wRHS ϱ lam g u) hs.h1 (hs.locL2_rhs b hc) (hs.locEq b hc)
        (hs.locSob_all b hc (m + 1)) (hs.rhs_regular b hc m (hs.locSob_all b hc (m + 1)))
      have hB := hIH₂ u u' g hs
      have hA := hcr u u' g hs
      have hA2 := hIH₃ u u' g hs
      set G := sobSq b m (fun x => χ' x * g x) with hG
      set U := sobSq b 0 (fun x => χ' x * u x) with hU
      have hG0 : 0 ≤ G := sobSq_nonneg b _ _
      have hU0 : 0 ≤ U := sobSq_nonneg b _ _
      have e1 : sobSq b (m + 1 - 2) (fun x => χ₃ x * g x) ≤ d3g * G :=
        ((hd3g χ' g h3 (hSg _)).2).trans (mul_le_mul_of_nonneg_left
          (sobSq_mono b (by omega) _) hd3g0)
      have e2 : sobSq b 0 (fun x => χ₃ x * u x) ≤ d3u * U :=
        (hd3u χ' u h3 (hSu _)).2
      have e3 : sobSq b m (fun x => χa x * g x) ≤ dag * G :=
        (hdag χ' g ha' (hSg _)).2
      have e4 : sobSq b (m - 2) (fun x => χ₅ x * g x) ≤ d5g * G :=
        ((hd5g χ' g h5 (hSg _)).2).trans (mul_le_mul_of_nonneg_left
          (sobSq_mono b (by omega) _) hd5g0)
      have e5 : sobSq b 0 (fun x => χ₅ x * u x) ≤ d5u * U :=
        (hd5u χ' u h5 (hSu _)).2
      have hA2' : sobSq b m (fun x => χa x * u x) ≤ C₃ * (d5g * G + d5u * U) :=
        hA2.trans (mul_le_mul_of_nonneg_left (add_le_add e4 e5) hC₃)
      have hA' : sobSq b m (fun x => χ₁ x * wRHS ϱ lam g u x) ≤
          c * (dag * G + C₃ * (d5g * G + d5u * U)) :=
        hA.trans (mul_le_mul_of_nonneg_left (add_le_add e3 hA2') hc0)
      have hB' : sobSq b (m + 1) (fun x => χ₂ x * u x) ≤ C₂ * (d3g * G + d3u * U) :=
        hB.trans (mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC₂)
      have hfin : sobSq b (m + 2) (fun x => χ x * u x) ≤
          C₁ * (c * (dag * G + C₃ * (d5g * G + d5u * U)) + C₂ * (d3g * G + d3u * U)) :=
        h0.trans (mul_le_mul_of_nonneg_left (add_le_add hA' hB') hC₁)
      have e : m + 1 + 1 - 2 = m := by omega
      rw [e]
      have hnn : 0 ≤ C₁ * ((c * C₃ * d5u + C₂ * d3u) * G + (c * dag + c * C₃ * d5g + C₂ * d3g) * U) := by
        positivity
      have e6 : m + 1 + 1 = m + 2 := rfl
      rw [e6]
      rw [hCfin]
      nlinarith [hfin, hnn]

end CutoffRigidity.Riemann.Diff
