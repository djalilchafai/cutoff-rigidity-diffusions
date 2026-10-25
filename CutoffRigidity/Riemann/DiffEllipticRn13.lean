module

public import CutoffRigidity.Riemann.DiffEllipticRn12

/-! # Quantitative interior estimate: the one-step estimate
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

/-- Multiplication by a smooth compactly supported function is bounded on `H^m`. -/
theorem exists_mul_const {a : E → ℝ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (m : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ f : E → ℝ, Sob b m f →
      Sob b m (fun x => a x * f x) ∧ sobSq b m (fun x => a x * f x) ≤ c * sobSq b m f := by
  obtain ⟨Kb, hKb⟩ := exists_iteratedFDeriv_bound ha hc m
  exact ⟨mulConst (Fintype.card ι) Kb m, mulConst_nonneg _ _ _,
    fun f hf => Sob.mul_smooth b ha hKb hf⟩

theorem sobSq_sum_le {J : Type*} (m : ℕ) (s : Finset J) (f : J → E → ℝ)
    (hf : ∀ j ∈ s, Sob b m (f j)) :
    sobSq b m (fun x => ∑ j ∈ s, f j x) ≤ 2 ^ s.card * ∑ j ∈ s, sobSq b m (f j) :=
  (Sob.sum b m s f hf).2

/-- A uniform constant for finitely many smooth compactly supported functions. -/
theorem exists_mul_const_family {J : Type*} [Fintype J] {a : J → E → ℝ}
    (ha : ∀ j, ContDiff ℝ ∞ (a j)) (hc : ∀ j, HasCompactSupport (a j)) (m : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ j, ∀ f : E → ℝ, Sob b m f →
      Sob b m (fun x => a j x * f x) ∧ sobSq b m (fun x => a j x * f x) ≤ c * sobSq b m f := by
  have : ∀ j, ∃ c : ℝ, 0 ≤ c ∧ ∀ f : E → ℝ, Sob b m f →
      Sob b m (fun x => a j x * f x) ∧ sobSq b m (fun x => a j x * f x) ≤ c * sobSq b m f :=
    fun j => exists_mul_const b (ha j) (hc j) m
  choose c hc0 hcb using this
  refine ⟨∑ j, c j, Finset.sum_nonneg (fun j _ => hc0 j), fun j f hf => ⟨(hcb j f hf).1, ?_⟩⟩
  refine (hcb j f hf).2.trans ?_
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := c) (fun i _ => hc0 i) (Finset.mem_univ j)) (sobSq_nonneg b m f)

/-- One-step interior estimate with constant independent of the solution. -/
theorem interior_step {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    (m : ℕ) {χ : E → ℝ} (hχ : IsTest Ω χ) :
    ∃ (χ₁ χ₂ : E → ℝ) (C : ℝ), IsTest Ω χ₁ ∧ IsTest Ω χ₂ ∧ 0 ≤ C ∧
      ∀ (u : E → ℝ) (u' : ι → E → ℝ) (F : E → ℝ), LocH1 b Ω u u' → LocL2 Ω F →
        LocEq b Ω A u' F → LocSob b Ω (m + 1) u → LocSob b Ω m F →
        sobSq b (m + 2) (fun x => χ x * u x) ≤
          C * (sobSq b m (fun x => χ₁ x * F x) + sobSq b (m + 1) (fun x => χ₂ x * u x)) := by
  obtain ⟨χ₁, hχ₁, ⟨V₁, hV₁, hKV₁, hV₁1⟩, -⟩ := exists_cutoff_nhds hχ.2.1 hΩ hχ.2.2
  obtain ⟨ψ, θ, Kb, hψ, ⟨V, hV, hKV, hV1⟩, hθ, hEll, hAhat⟩ :=
    exists_localized_coeff hΩ hAs hAsym hAell hχ₁.2.1 hχ₁.2.2 (m + 1)
  obtain ⟨χ₂, hχ₂, ⟨V₂, hV₂, hKV₂, hV₂1⟩, -⟩ := exists_cutoff_nhds hχ₁.2.1 hΩ hχ₁.2.2
  obtain ⟨Cg, hCg0, hCg⟩ := global_regularity b θ Kb hθ m
  set n := Fintype.card ι with hn
  -- the coefficient families
  have hasm : ∀ p : ι × ι, ContDiff ℝ ∞ (fun x => ψ x * A p.1 p.2 x * pd (b p.1) χ₁ x) := fun p =>
    (hAhat p.1 p.2).1.mul (contDiff_pd hχ₁.1 _)
  have hacs : ∀ p : ι × ι, HasCompactSupport (fun x => ψ x * A p.1 p.2 x * pd (b p.1) χ₁ x) :=
    fun p => (hAhat p.1 p.2).2.1.mul_right
  have hbsm : ∀ p : ι × ι, ContDiff ℝ ∞ (fun x => ψ x * A p.1 p.2 x * pd (b p.2) χ₁ x) := fun p =>
    (hAhat p.1 p.2).1.mul (contDiff_pd hχ₁.1 _)
  have hbcs : ∀ p : ι × ι, HasCompactSupport (fun x => ψ x * A p.1 p.2 x * pd (b p.2) χ₁ x) :=
    fun p => (hAhat p.1 p.2).2.1.mul_right
  obtain ⟨ca, hca0, hca⟩ := exists_mul_const_family b hasm hacs m
  obtain ⟨cb, hcb0, hcb⟩ := exists_mul_const_family b hbsm hbcs (m + 1)
  obtain ⟨c1, hc10, hc1⟩ := exists_mul_const b hχ₁.1 hχ₁.2.1 1
  obtain ⟨c0, hc00, hc0⟩ := exists_mul_const b hχ.1 hχ.2.1 (m + 2)
  set K1 : ℝ := 2 + 2 * ((2 : ℝ) ^ n * n) ^ 2 * ca + (n : ℝ) ^ 2 * 2 ^ n * cb + c1 with hK1
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  refine ⟨χ₁, χ₂, c0 * Cg * K1, hχ₁, hχ₂, by positivity, ?_⟩
  intro u u' F hu hF heq hum hFm
  set X := sobSq b (m + 1) (fun x => χ₂ x * u x) with hX
  set S := sobSq b m (fun x => χ₁ x * F x) with hS
  have hX0 : 0 ≤ X := sobSq_nonneg b _ _
  have hS0 : 0 ≤ S := sobSq_nonneg b _ _
  have hu2 : Sob b (m + 1) (fun x => χ₂ x * u x) := hum χ₂ hχ₂
  have hu2' := (Sob.succ_iff b).1 hu2
  have hfj : ∀ j, Sob b m (wd (b j) (fun x => χ₂ x * u x)) := fun j => (hu2'.2 j).2
  have hfjb : ∀ j, sobSq b m (wd (b j) (fun x => χ₂ x * u x)) ≤ X := fun j =>
    sobSq_wd_le b m _ j
  have hwae2 : ∀ j, wd (b j) (fun x => χ₂ x * u x) =ᵐ[volume]
      fun x => χ₂ x * u' j x + pd (b j) χ₂ x * u x := fun j =>
    (wd_spec (hasWDeriv_cutoff_mul hΩ (hu.wd j) hχ₂)
      ((memLp_mul_test (hu.l2' j) hχ₂).add (memLp_mul_test hu.l2 (hχ₂.pd (b j))))).2.2
  have hchi2 : ∀ x ∈ tsupport χ₁, χ₂ x = 1 ∧ ∀ v, pd v χ₂ x = 0 := fun x hx =>
    ⟨hV₂1 x (hKV₂ hx), fun v => pd_eq_zero_of_eventually_one hV₂ hV₂1 (hKV₂ hx) v⟩
  -- the terms `a_ij u'_j`
  have hterm : ∀ i j, Sob b m (fun x => ψ x * A i j x * pd (b i) χ₁ x * u' j x) ∧
      sobSq b m (fun x => ψ x * A i j x * pd (b i) χ₁ x * u' j x) ≤ ca * X := by
    intro i j
    obtain ⟨h1, h2⟩ := hca (i, j) _ (hfj j)
    have hae : (fun x => ψ x * A i j x * pd (b i) χ₁ x * u' j x) =ᵐ[volume]
        fun x => ψ x * A i j x * pd (b i) χ₁ x * wd (b j) (fun x => χ₂ x * u x) x := by
      filter_upwards [hwae2 j] with x hx
      by_cases hx1 : x ∈ tsupport χ₁
      · obtain ⟨e1, e2⟩ := hchi2 x hx1
        rw [hx, e1, e2]; ring
      · simp [pd_eq_zero_of_notMem hx1]
    refine ⟨Sob.congr_ae b h1 hae.symm, ?_⟩
    rw [sobSq_congr_ae b hae]
    exact h2.trans (mul_le_mul_of_nonneg_left (hfjb j) hca0)
  have hsumj : ∀ i, Sob b m (fun x => ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) ∧
      sobSq b m (fun x => ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) ≤
        2 ^ n * ((n : ℝ) * (ca * X)) := by
    intro i
    obtain ⟨h1, h2⟩ := Sob.sum b m Finset.univ
      (fun j x => ψ x * A i j x * pd (b i) χ₁ x * u' j x) (fun j _ => (hterm i j).1)
    refine ⟨h1, h2.trans ?_⟩
    rw [Finset.card_univ, ← hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ j, sobSq b m (fun x => ψ x * A i j x * pd (b i) χ₁ x * u' j x)
        ≤ ∑ _j : ι, ca * X := Finset.sum_le_sum (fun j _ => (hterm i j).2)
      _ = (n : ℝ) * (ca * X) := by simp [hn]
  have hsumi : Sob b m (fun x => ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) ∧
      sobSq b m (fun x => ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) ≤
        ((2 : ℝ) ^ n * n) ^ 2 * (ca * X) := by
    obtain ⟨h1, h2⟩ := Sob.sum b m Finset.univ
      (fun i x => ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) (fun i _ => (hsumj i).1)
    refine ⟨h1, h2.trans ?_⟩
    rw [Finset.card_univ, ← hn]
    calc (2 : ℝ) ^ n * ∑ i, sobSq b m (fun x => ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x)
        ≤ 2 ^ n * ∑ _i : ι, 2 ^ n * ((n : ℝ) * (ca * X)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hsumj i).2)) (by positivity)
      _ = ((2 : ℝ) ^ n * n) ^ 2 * (ca * X) := by simp [hn]; ring
  have hFt := Sob.sub b (hFm χ₁ hχ₁) hsumi.1
  -- the terms of `G̃`
  have hGt : ∀ i, Sob b (m + 1) (fun x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) ∧
      sobSq b (m + 1) (fun x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) ≤
        2 ^ n * ((n : ℝ) * (cb * X)) := by
    intro i
    have hb1 : ∀ j, Sob b (m + 1) (fun x => ψ x * A i j x * pd (b j) χ₁ x * (χ₂ x * u x)) ∧
        sobSq b (m + 1) (fun x => ψ x * A i j x * pd (b j) χ₁ x * (χ₂ x * u x)) ≤ cb * X :=
      fun j => ⟨(hcb (i, j) _ hu2).1, (hcb (i, j) _ hu2).2⟩
    obtain ⟨h1, h2⟩ := Sob.sum b (m + 1) Finset.univ
      (fun j x => ψ x * A i j x * pd (b j) χ₁ x * (χ₂ x * u x)) (fun j _ => (hb1 j).1)
    have he : (fun x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) =
        fun x => ∑ j, ψ x * A i j x * pd (b j) χ₁ x * (χ₂ x * u x) := by
      funext x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hx1 : x ∈ tsupport χ₁
      · rw [(hchi2 x hx1).1]; ring
      · simp [pd_eq_zero_of_notMem hx1]
    rw [he]
    refine ⟨h1, h2.trans ?_⟩
    rw [Finset.card_univ, ← hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ j, sobSq b (m + 1) (fun x => ψ x * A i j x * pd (b j) χ₁ x * (χ₂ x * u x))
        ≤ ∑ _j : ι, cb * X := Finset.sum_le_sum (fun j _ => (hb1 j).2)
      _ = (n : ℝ) * (cb * X) := by simp [hn]
  -- the localized function
  have hweq : (fun x => χ₁ x * u x) = fun x => χ₁ x * (χ₂ x * u x) := by
    funext x
    by_cases hx1 : x ∈ tsupport χ₁
    · rw [(hchi2 x hx1).1]; ring
    · simp [image_eq_zero_of_notMem_tsupport hx1]
  have hu21 : Sob b 1 (fun x => χ₂ x * u x) := Sob.mono b (by omega) hu2
  have hw1 : Sob b 1 (fun x => χ₁ x * u x) ∧
      sobSq b 1 (fun x => χ₁ x * u x) ≤ c1 * X := by
    rw [hweq]
    obtain ⟨h1, h2⟩ := hc1 _ hu21
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left
      (sobSq_mono b (by omega : 1 ≤ m + 1) _) hc10)⟩
  have hWeak := localized_weakEq_of b hΩ hu hF heq hχ₁ hV hKV hV1 hAhat
  obtain ⟨hsob, hbound⟩ := hCg (locCoeff ψ A) hEll (fun x => χ₁ x * u x) _ _ hw1.1
    (aesupp_of_testMul hχ₁) hFt.1 (fun i => (hGt i).1) hWeak
  -- the final chain
  have hFb : sobSq b m (fun x => χ₁ x * F x - ∑ i, ∑ j, ψ x * A i j x * pd (b i) χ₁ x * u' j x) ≤
      2 * (S + ((2 : ℝ) ^ n * n) ^ 2 * (ca * X)) :=
    hFt.2.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsumi.2) (by norm_num))
  have hGsum : ∑ i, sobSq b (m + 1) (fun x => u x * ∑ j, ψ x * A i j x * pd (b j) χ₁ x) ≤
      (n : ℝ) ^ 2 * 2 ^ n * (cb * X) := by
    calc _ ≤ ∑ _i : ι, 2 ^ n * ((n : ℝ) * (cb * X)) := Finset.sum_le_sum (fun i _ => (hGt i).2)
      _ = _ := by simp [hn]; ring
  have hw2 : sobSq b (m + 2) (fun x => χ₁ x * u x) ≤ Cg * (K1 * (S + X)) := by
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hCg0)
    have hq1 : 0 ≤ ((2 : ℝ) ^ n * n) ^ 2 * ca := by positivity
    have hq2 : 0 ≤ (n : ℝ) ^ 2 * 2 ^ n * cb := by positivity
    nlinarith [mul_nonneg hq1 hX0, mul_nonneg hq2 hX0, mul_nonneg hc10 hX0, hw1.2, hFb, hGsum]
  have hc0w := hc0 _ hsob
  have hfin : (fun x => χ x * u x) = fun x => χ x * (χ₁ x * u x) := by
    funext x
    by_cases hx1 : x ∈ tsupport χ
    · rw [hV₁1 x (hKV₁ hx1)]; ring
    · simp [image_eq_zero_of_notMem_tsupport hx1]
  rw [hfin]
  calc sobSq b (m + 2) (fun x => χ x * (χ₁ x * u x)) ≤ c0 * sobSq b (m + 2) (fun x => χ₁ x * u x) :=
        hc0w.2
    _ ≤ c0 * (Cg * (K1 * (S + X))) := mul_le_mul_of_nonneg_left hw2 hc00
    _ = c0 * Cg * K1 * (S + X) := by ring

end CutoffRigidity.Riemann.Diff
