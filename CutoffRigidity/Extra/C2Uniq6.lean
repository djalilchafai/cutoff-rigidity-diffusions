module

public import CutoffRigidity.Extra.C2Uniq5

/-! # `C²` uniqueness, stage 5: two-sided comparison and limits -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open Bundle
open scoped ENNReal NNReal ContDiff Manifold

namespace C2U

variable {d : ℕ}

section Close

variable {V W g : Rd d → ℝ} {P : ℝ≥0 → Kernel (Rd d) (Rd d)} {w : ℝ≥0 → Rd d → ℝ} {K G C : ℝ}
  {χ : Rd d → ℝ}

theorem integrableOn_exp_mul_w (hb : IsBackward W g w K G C) {lam : ℝ} (hlam : 0 < lam) (x : Rd d) :
    IntegrableOn (fun s : ℝ => Real.exp (-lam * s) * w s.toNNReal x) (Ioi (0 : ℝ)) := by
  refine ((integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0).const_mul K).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (hb.cont x)).aestronglyMeasurable
    ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun σ _ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (by rw [abs_of_nonneg (hb.nonneg _ _)]; exact hb.le _ _) (Real.exp_pos _).le

/-- Two-sided comparison of `U_λ g(x)` with the Laplace transform of the backward family. -/
theorem resU_close
    (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 2 V) (hW : ContDiff ℝ ∞ W)
    (hb : IsBackward W g w K G C)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    {A R δ : ℝ} (hgrad : ∀ y, ‖gradient χ y‖ ≤ A / R) (hlap : ∀ y, |laplacian χ y| ≤ A / R ^ 2)
    (hVχ : ∀ y, inner ℝ (gradient V y) (gradient χ y) ≤ A / R)
    (hδ : ∀ y, χ y ≠ 0 → ‖gradient V y - gradient W y‖ ≤ δ) (hδ0 : 0 ≤ δ)
    (hA1 : 0 ≤ A / R) (hA2 : 0 ≤ A / R ^ 2)
    (hχg : ∀ y, χ y * g y = g y) (x : Rd d) (hχx : χ x = 1)
    {lam : ℝ} (hlam : 0 < lam) :
    |(∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * w s.toNNReal x) - resU P lam g x| ≤
      (δ * G + K * (A / R ^ 2) + 2 * (A / R) * G + K * (A / R)) / lam ^ 2 := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_cast)
  have hχ0 : Continuous χ := hχ.continuous
  set Err : ℝ := δ * G + K * (A / R ^ 2) + 2 * (A / R) * G + K * (A / R) with hErr
  have hK0 : 0 ≤ K := (hb.nonneg 0 0).trans (hb.le 0 0)
  have hfun : (fun y => χ y * g y) = g := funext hχg
  -- upper bound
  have up := core_upper hP hV hW hb hχ hχc hχ01 hgrad hlap hVχ hδ hδ0 hA1 hA2 hlam x
  rw [hχx, one_mul, hfun] at up
  -- lower bound via `K - w`
  have hb' := hb.const_sub (c := K) le_rfl
  have lo := core_upper hP hV hW hb' hχ hχc hχ01 hgrad hlap hVχ hδ hδ0 hA1 hA2 hlam x
  rw [hχx, one_mul] at lo
  set r : ℝ := ∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * w s.toNNReal x with hr
  have hr' : (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * (K - w s.toNNReal x)) = K / lam - r := by
    have : ∀ s : ℝ, Real.exp (-lam * s) * (K - w s.toNNReal x) =
        Real.exp (-lam * s) * K - Real.exp (-lam * s) * w s.toNNReal x := fun s => by ring
    simp_rw [this]
    rw [integral_sub (integrableOn_exp_mul_const lam K hlam) (integrableOn_exp_mul_w hb hlam x),
      integral_exp_mul_const lam K hlam]
  beta_reduce at lo
  rw [hr'] at lo
  have hsplit : resU P lam (fun y => χ y * (K - g y)) x =
      resU P lam (fun y => χ y * K) x - resU P lam g x := by
    have := resU_add hP hV1 (h1 := fun y => χ y * K) (h2 := fun y => -1 * g y)
      (hχ0.mul continuous_const) (hχc.mul_right) (continuous_const.mul hg.continuous)
      (hgc.mul_left (f := fun _ => -1)) hlam x
    have h4 := resU_smul (P := P) (-1) g lam x
    have e : (fun y => χ y * (K - g y)) = fun y => χ y * K + -1 * g y := by
      funext y
      have := hχg y
      nlinarith
    rw [e, this, h4]; ring
  have hmass : resU P lam (fun y => χ y * K) x ≤ K / lam := by
    refine resU_le hP hV1 (hχ0.mul continuous_const) hχc.mul_right (fun y => ?_) hlam x
    calc χ y * K ≤ 1 * K := mul_le_mul_of_nonneg_right (hχ01 y).2 hK0
      _ = K := one_mul K
  rw [hsplit] at lo
  rw [abs_le]
  constructor
  · linarith
  · linarith

end Close

section Assembly

variable {V : Rd d → ℝ}

/-- Convexity gives `⟨∇V(y), y⟩ ≥ ⟨∇V(0), y⟩`. -/
theorem inner_gradient_monotone (hV : ContDiff ℝ 1 V) (hc : ConvexOn ℝ univ V) (y : Rd d) :
    inner ℝ (gradient V 0) y ≤ inner ℝ (gradient V y) y := by
  let f : ℝ → ℝ := fun t => V (t • y)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => s • y) y t := by
    simpa using (hasDerivAt_id t).smul_const y
  have hfd (t : ℝ) : HasDerivAt f (fderiv ℝ V (t • y) y) t :=
    (hV.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hconvf : ConvexOn ℝ univ f := by
    have h := hc.comp_affineMap (AffineMap.lineMap (0 : Rd d) y)
    have e : (V ∘ ⇑(AffineMap.lineMap (0 : Rd d) y)) = f := by
      funext t; simp [f, AffineMap.lineMap_apply]
    rw [e] at h
    simpa using h
  have hm : Monotone (deriv f) :=
    fun s t hst => (hconvf.monotoneOn_deriv (fun t _ => (hfd t).differentiableAt))
      (mem_univ s) (mem_univ t) hst
  have h01 := hm (zero_le_one : (0 : ℝ) ≤ 1)
  rw [(hfd 0).deriv, (hfd 1).deriv] at h01
  simp only [zero_smul, one_smul] at h01
  rw [real_inner_comm, inner_gradient_left, real_inner_comm, inner_gradient_left]
  exact h01

theorem gradient_lower (hV : ContDiff ℝ 1 V) (hc : ConvexOn ℝ univ V) (y : Rd d) :
    -(‖gradient V 0‖ * ‖y‖) ≤ inner ℝ (gradient V y) y := by
  have h1 := inner_gradient_monotone hV hc y
  have h2 := abs_real_inner_le_norm (gradient V 0) y
  have h3 := neg_abs_le (inner ℝ (gradient V 0) y)
  linarith


theorem exists_support_radius {g : Rd d → ℝ} (hgc : HasCompactSupport g) :
    ∃ Rg : ℝ, ∀ y, Rg < ‖y‖ → g y = 0 := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.exists_norm_le
  exact ⟨R, fun y hy => by
    by_contra hne
    exact absurd (hR y (subset_tsupport _ hne)) (not_le.2 hy)⟩

/-- **Resolvent uniqueness** for nonnegative `C_c^∞` data: two Euclidean diffusion semigroups of a
convex `C²` potential have the same resolvent. -/
theorem resU_eq_of_nonneg {P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V)
    (h₁ : IsEuclideanDiffusion V P₁) (h₂ : IsEuclideanDiffusion V P₂)
    {lam : ℝ} (hlam : 0 < lam) {g : Rd d → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hg0 : ∀ y, 0 ≤ g y) (x : Rd d) :
    resU P₁ lam g x = resU P₂ lam g x := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_cast)
  obtain ⟨K, hK⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hK' : ∀ y, g y ≤ max K 0 := fun y => by
    have := hK y
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  set K₀ := max K 0 with hK₀
  have hK0 : 0 ≤ K₀ := le_max_right _ _
  obtain ⟨G, hG0, hG⟩ := exists_gradient_bound hg hgc
  obtain ⟨Rg, hRg⟩ := exists_support_radius hgc
  set a := ‖gradient V 0‖ with ha
  obtain ⟨A, hA0, hAc⟩ := exists_cutoff V a (norm_nonneg _) (gradient_lower hV1 hc)
  -- it suffices to show `|u₁ - u₂| ≤ ε` for all `ε > 0`
  refine eq_of_abs_sub_le_all fun ε hε => ?_
  -- choice of `R`
  set M : ℝ := max 1 (max ‖x‖ Rg) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMx : ‖x‖ ≤ M := (le_max_left ‖x‖ Rg).trans (le_max_right _ _)
  have hMg : Rg ≤ M := (le_max_right ‖x‖ Rg).trans (le_max_right _ _)
  set T : ℝ := 4 * (2 * K₀ * A + 2 * A * G) / (lam ^ 2 * ε) with hT
  set R : ℝ := max M T with hR
  have hMR : M ≤ R := le_max_left _ _
  have hR1 : 1 ≤ R := hM1.trans hMR
  have hR0 : 0 < R := by linarith
  have hRx : ‖x‖ ≤ R := hMx.trans hMR
  have hRg' : Rg ≤ R := hMg.trans hMR
  have hRbig : 4 * (2 * K₀ * A + 2 * A * G) / (lam ^ 2 * ε) ≤ R := le_max_right _ _
  obtain ⟨χ, hχ, hχc, hχ01, hχ1, hχ0, hχgrad, hχlap, hχV⟩ := hAc R hR1
  -- smallness of the `R`-dependent error
  have hsmallR : K₀ * (A / R ^ 2) + 2 * (A / R) * G + K₀ * (A / R) ≤ lam ^ 2 * ε / 4 := by
    have h1 : K₀ * (A / R ^ 2) ≤ K₀ * (A / R) := by
      have : A / R ^ 2 ≤ A / R := by
        apply div_le_div_of_nonneg_left hA0 hR0
        nlinarith
      exact mul_le_mul_of_nonneg_left this hK0
    have h2 : K₀ * (A / R ^ 2) + 2 * (A / R) * G + K₀ * (A / R) ≤ (2 * K₀ * A + 2 * A * G) / R := by
      have : (2 * K₀ * A + 2 * A * G) / R = 2 * K₀ * (A / R) + 2 * (A / R) * G := by
        field_simp
      rw [this]; linarith
    refine h2.trans ?_
    rw [div_le_iff₀ hR0]
    have h3 := hRbig
    rw [div_le_iff₀ (by positivity)] at h3
    nlinarith
  -- choice of `δ` and `n`
  set δ : ℝ := lam ^ 2 * ε / (4 * (G + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := Wm_grad_close hV (2 * R) δ hδpos
  have hδG : δ * G ≤ lam ^ 2 * ε / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg lam) hε.le) hG0]
  -- the backward family
  obtain ⟨w, C, hb⟩ := exists_backward hV hc hg hgc hg0 hK' hG N
  have hW : ContDiff ℝ ∞ (Wm V N) := Wm_contDiff hV N
  have hδ' : ∀ y, χ y ≠ 0 → ‖gradient V y - gradient (Wm V N) y‖ ≤ δ := by
    intro y hy
    have hy2 : ‖y‖ ≤ 2 * R := by
      by_contra hcon
      exact hy (hχ0 y (le_of_lt (not_le.1 hcon)))
    rw [norm_sub_rev]
    exact hN N le_rfl y hy2
  have hχg : ∀ y, χ y * g y = g y := by
    intro y
    by_cases hy : g y = 0
    · simp [hy]
    · have : ‖y‖ ≤ R := by
        by_contra hcon
        exact hy (hRg y (lt_of_le_of_lt hRg' (not_le.1 hcon)))
      rw [hχ1 y this, one_mul]
  have hA1 : 0 ≤ A / R := by positivity
  have hA2 : 0 ≤ A / R ^ 2 := by positivity
  have c₁ := resU_close h₁ hV hW hb hg hgc hχ hχc hχ01 hχgrad hχlap hχV hδ' hδpos.le hA1 hA2 hχg x
    (hχ1 x hRx) hlam
  have c₂ := resU_close h₂ hV hW hb hg hgc hχ hχc hχ01 hχgrad hχlap hχV hδ' hδpos.le hA1 hA2 hχg x
    (hχ1 x hRx) hlam
  set Err := δ * G + K₀ * (A / R ^ 2) + 2 * (A / R) * G + K₀ * (A / R) with hErr
  have hErr' : Err / lam ^ 2 ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : Err ≤ lam ^ 2 * ε / 2 := by
      have e : Err = δ * G + (K₀ * (A / R ^ 2) + 2 * (A / R) * G + K₀ * (A / R)) := by
        rw [hErr]; ring
      rw [e]; linarith
    nlinarith
  calc |resU P₁ lam g x - resU P₂ lam g x|
      = |((∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * w s.toNNReal x) - resU P₂ lam g x) -
          ((∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * w s.toNNReal x) - resU P₁ lam g x)| := by
        congr 1; ring
    _ ≤ |(∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * w s.toNNReal x) - resU P₂ lam g x| +
          |(∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * w s.toNNReal x) - resU P₁ lam g x| :=
        abs_sub _ _
    _ ≤ Err / lam ^ 2 + Err / lam ^ 2 := add_le_add c₂ c₁
    _ ≤ ε := by linarith


/-- Resolvent uniqueness for arbitrary real `C_c^∞` data (bump trick). -/
theorem resU_eq {P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V)
    (h₁ : IsEuclideanDiffusion V P₁) (h₂ : IsEuclideanDiffusion V P₂)
    {lam : ℝ} (hlam : 0 < lam) {g : Rd d → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : Rd d) :
    resU P₁ lam g x = resU P₂ lam g x := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_cast)
  obtain ⟨K, hK⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hK' : ∀ y, |g y| ≤ max K 0 := fun y => by
    have := hK y
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set C := max K 0 with hCdef
  obtain ⟨Rg, hRg⟩ := exists_support_radius hgc
  let ψ : ContDiffBump (0 : Rd d) := ⟨max Rg 0 + 1, max Rg 0 + 2, by positivity, by linarith⟩
  have hψ1 : ∀ y : Rd d, ‖y‖ ≤ max Rg 0 + 1 → ψ y = 1 := fun y hy =>
    ψ.one_of_mem_closedBall (by simpa [ψ] using hy)
  have hψs : ContDiff ℝ ∞ (fun y => ψ y) := ψ.contDiff
  have hψc : HasCompactSupport (fun y => ψ y) := ψ.hasCompactSupport
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => ψ.nonneg
  have hgψ : ∀ y, 0 ≤ g y + C * ψ y := by
    intro y
    by_cases hy : g y = 0
    · rw [hy, zero_add]; exact mul_nonneg (le_max_right _ _) (hψ0 y)
    · have : ‖y‖ ≤ max Rg 0 + 1 := by
        by_contra hcon
        exact hy (hRg y (lt_of_le_of_lt (le_max_left _ _) (by linarith [not_le.1 hcon])))
      rw [hψ1 y this]
      have := (abs_le.1 (hK' y)).1
      linarith
  have hs : ContDiff ℝ ∞ (fun y => g y + C * ψ y) := hg.add (contDiff_const.mul hψs)
  have hcs : HasCompactSupport (fun y => g y + C * ψ y) := hgc.add (hψc.mul_left (f := fun _ => C))
  have e1 := resU_eq_of_nonneg hV hc h₁ h₂ hlam hs hcs hgψ x
  have e2 := resU_eq_of_nonneg hV hc h₁ h₂ hlam hψs hψc hψ0 x
  have split : ∀ P : ℝ≥0 → Kernel (Rd d) (Rd d), IsEuclideanDiffusion V P →
      resU P lam (fun y => g y + C * ψ y) x = resU P lam g x + C * resU P lam (fun y => ψ y) x := by
    intro P hP
    have := resU_add hP hV1 (h1 := g) (h2 := fun y => C * ψ y) hg.continuous hgc
      (continuous_const.mul hψs.continuous)
      (by exact hψc.mul_left (f := fun _ => C)) hlam x
    rw [this, resU_smul]
  have s1 := split P₁ h₁
  have s2 := split P₂ h₂
  rw [e2] at s1
  linarith

end Assembly

end C2U

end CutCur
