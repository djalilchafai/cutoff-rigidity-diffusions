module

public import CutoffRigidity.Riemann.TransportMain

/-! # Lower bound for `W₂(ν, μ)` from two moments of `ν` (Tier C, lemma C1)

If the Euclidean coordinate `p` of the splitting has, under a probability measure `ν`, the mean
`e^{-ρt} p x₀` and the second moment `e^{-2ρt}‖p x₀‖² + (k/ρ)(1-e^{-2ρt})`, then
`ρ e^{-2ρt}‖p x₀‖² + k (1-√(1-e^{-2ρt}))² ≤ ρ W₂²(ν, μ)`.  No Gaussian (Mehler) law of `ν` is
needed: only the two moments, through a Cauchy-Schwarz bound on every coupling.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace CutoffRigidity.Riemann

section Aux

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

theorem integrable_inner_of_sq (π : Measure Ω) [IsFiniteMeasure π]
    {u v : Ω → EuclideanSpace ℝ (Fin k)} (hu : Measurable u) (hv : Measurable v)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) π) (hv2 : Integrable (fun ω => ‖v ω‖ ^ 2) π) :
    Integrable (fun ω => ⟪u ω, v ω⟫) π := by
  refine ((hu2.add hv2).div_const 2).mono' (by fun_prop) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  calc |⟪u ω, v ω⟫| ≤ ‖u ω‖ * ‖v ω‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖u ω‖ ^ 2 + ‖v ω‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖u ω‖ - ‖v ω‖)]

theorem integrable_sq_const (π : Measure Ω) [IsFiniteMeasure π] (a : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun _ : Ω => ‖a‖ ^ 2) π := integrable_const _

/-- Cauchy-Schwarz lower bound for a coupling of two `ℝ^k`-valued random variables. -/
theorem lower_aux (π : Measure Ω) [IsProbabilityMeasure π]
    (X Z : Ω → EuclideanSpace ℝ (Fin k)) (hX : Measurable X) (hZ : Measurable Z)
    (m : EuclideanSpace ℝ (Fin k)) (C B : ℝ)
    (hX1 : ∀ a, ∫ ω, ⟪a, X ω⟫ ∂π = ⟪a, m⟫)
    (hX2i : Integrable (fun ω => ‖X ω‖ ^ 2) π) (hX2 : ∫ ω, ‖X ω‖ ^ 2 ∂π = ‖m‖ ^ 2 + C)
    (hZ1 : ∀ a, ∫ ω, ⟪a, Z ω⟫ ∂π = 0)
    (hZ2i : Integrable (fun ω => ‖Z ω‖ ^ 2) π) (hZ2 : ∫ ω, ‖Z ω‖ ^ 2 ∂π = B) :
    ‖m‖ ^ 2 + C + B - 2 * Real.sqrt (C * B) ≤ ∫ ω, ‖X ω - Z ω‖ ^ 2 ∂π := by
  have hmc : Measurable (fun _ : Ω => m) := measurable_const
  have i2 : Integrable (fun ω => ⟪m, X ω⟫) π :=
    integrable_inner_of_sq π hmc hX (integrable_const _) hX2i
  have i3 : Integrable (fun ω => ⟪X ω, Z ω⟫) π := integrable_inner_of_sq π hX hZ hX2i hZ2i
  have i4 : Integrable (fun ω => ⟪m, Z ω⟫) π :=
    integrable_inner_of_sq π hmc hZ (integrable_const _) hZ2i
  have hI := hX1 m
  have hI' : ∫ ω, ⟪m, X ω⟫ ∂π = ‖m‖ ^ 2 := by rw [hX1 m, real_inner_self_eq_norm_sq]
  have hJ : ∫ ω, ⟪m, Z ω⟫ ∂π = 0 := hZ1 m
  set I := ∫ ω, ⟪X ω, Z ω⟫ ∂π with hIdef
  -- expansion of the cost
  have hcost : ∫ ω, ‖X ω - Z ω‖ ^ 2 ∂π = ‖m‖ ^ 2 + C - 2 * I + B := by
    have e : ∀ ω, ‖X ω - Z ω‖ ^ 2 = ‖X ω‖ ^ 2 - 2 * ⟪X ω, Z ω⟫ + ‖Z ω‖ ^ 2 := fun ω => by
      rw [@norm_sub_sq_real]
    simp_rw [e]
    have h1 : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * ⟪X ω, Z ω⟫) π := hX2i.sub (i3.const_mul 2)
    rw [integral_add h1 hZ2i, integral_sub hX2i (i3.const_mul 2),
      integral_const_mul, hX2, hZ2]
  -- the variance of `X`
  have hvar : ∫ ω, ‖X ω - m‖ ^ 2 ∂π = C := by
    have e : ∀ ω, ‖X ω - m‖ ^ 2 = ‖X ω‖ ^ 2 - 2 * ⟪m, X ω⟫ + ‖m‖ ^ 2 := fun ω => by
      rw [@norm_sub_sq_real, real_inner_comm]
    simp_rw [e]
    have h1 : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * ⟪m, X ω⟫) π := hX2i.sub (i2.const_mul 2)
    rw [integral_add h1 (integrable_const _),
      integral_sub hX2i (i2.const_mul 2), integral_const_mul, hX2, hI']
    simp
    ring
  have hcross : ∫ ω, ⟪X ω - m, Z ω⟫ ∂π = I := by
    have e : ∀ ω, ⟪X ω - m, Z ω⟫ = ⟪X ω, Z ω⟫ - ⟪m, Z ω⟫ := fun ω => inner_sub_left _ _ _
    simp_rw [e]
    rw [integral_sub i3 i4, hJ, sub_zero]
  -- discriminant
  have hq : ∀ l : ℝ, 0 ≤ C * (l * l) + (-2 * I) * l + B := by
    intro l
    have hu2 : Integrable (fun ω => ‖X ω - m‖ ^ 2) π := by
      have e : ∀ ω, ‖X ω - m‖ ^ 2 = ‖X ω‖ ^ 2 - 2 * ⟪m, X ω⟫ + ‖m‖ ^ 2 := fun ω => by
        rw [@norm_sub_sq_real, real_inner_comm]
      simp_rw [e]
      exact (hX2i.sub (i2.const_mul 2)).add (integrable_const _)
    have i5 : Integrable (fun ω => ⟪X ω - m, Z ω⟫) π := by
      have e : ∀ ω, ⟪X ω - m, Z ω⟫ = ⟪X ω, Z ω⟫ - ⟪m, Z ω⟫ := fun ω => inner_sub_left _ _ _
      simp_rw [e]
      exact i3.sub i4
    have e : ∀ ω, ‖l • (X ω - m) - Z ω‖ ^ 2 =
        l ^ 2 * ‖X ω - m‖ ^ 2 - 2 * l * ⟪X ω - m, Z ω⟫ + ‖Z ω‖ ^ 2 := fun ω => by
      rw [@norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_left]
      simp only [conj_trivial]
      ring
    have h0 : 0 ≤ ∫ ω, ‖l • (X ω - m) - Z ω‖ ^ 2 ∂π :=
      integral_nonneg fun ω => sq_nonneg _
    simp_rw [e] at h0
    have h1 : Integrable (fun ω => l ^ 2 * ‖X ω - m‖ ^ 2 - 2 * l * ⟪X ω - m, Z ω⟫) π :=
      (hu2.const_mul _).sub (i5.const_mul _)
    rw [integral_add h1 hZ2i,
      integral_sub (hu2.const_mul _) (i5.const_mul _), integral_const_mul, integral_const_mul,
      hvar, hcross, hZ2] at h0
    nlinarith [h0]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hI2 : I ^ 2 ≤ C * B := by nlinarith [hd]
  have hIle : I ≤ Real.sqrt (C * B) := (le_abs_self I).trans (Real.abs_le_sqrt hI2)
  rw [hcost]
  linarith

end Aux

section Split

variable {M N : Type*} [PseudoEMetricSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [PseudoEMetricSpace N] [MeasurableSpace N] {k : ℕ} {ρ : ℝ} {μ : Measure M}

namespace SplitData

variable (D : SplitData M N k ρ μ)

/-- Gaussian moments of the Euclidean coordinate under the equilibrium measure. -/
theorem proj_moments (hρ : 0 < ρ) :
    (∀ a : EuclideanSpace ℝ (Fin k), ∫ y, ⟪a, D.proj y⟫ ∂μ = 0) ∧
    Integrable (fun y => ‖D.proj y‖ ^ 2) μ ∧ ∫ y, ‖D.proj y‖ ^ 2 ∂μ = k / ρ := by
  have hS : (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (inv_nonneg.mpr hρ.le)
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
    (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) with hγ
  have hmap := D.map_proj_eq
  have hpm : AEMeasurable D.proj μ := D.measurable_proj.aemeasurable
  have hid : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x) γ := IsGaussian.integrable_id
  have hm2 : MemLp id 2 γ := IsGaussian.memLp_two_id
  have hint2 : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2) γ := by
    have := hm2.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have : ∫ y, ⟪a, D.proj y⟫ ∂μ = ∫ x, ⟪a, x⟫ ∂(μ.map D.proj) := by
      rw [integral_map hpm (by fun_prop)]
    rw [this, hmap, integral_inner hid, hγ, integral_id_multivariateGaussian]
    simp
  · have := (integrable_map_measure (f := D.proj)
      (g := fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2) (by fun_prop) hpm).1
      (by rw [hmap]; exact hint2)
    exact this
  · have : ∫ y, ‖D.proj y‖ ^ 2 ∂μ = ∫ x, ‖x‖ ^ 2 ∂(μ.map D.proj) := by
      rw [integral_map hpm (by fun_prop)]
    rw [this, hmap]
    have hcoord : ∀ i : Fin k, ∫ x, x i ^ 2 ∂γ = ρ⁻¹ := by
      intro i
      have hL : MemLp (fun x : EuclideanSpace ℝ (Fin k) => x i) 2 γ :=
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).comp_memLp' hm2
      have h3 : ∫ x, x i ∂γ = 0 := by
        have := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).integral_comp_comm hid
        simpa [hγ] using this
      have h1 := variance_of_integral_eq_zero hL.aemeasurable h3
      have h2 := variance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin k))) hS i
      rw [h2] at h1
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
      simpa using h1.symm
    have e : ∀ x : EuclideanSpace ℝ (Fin k), ‖x‖ ^ 2 = ∑ i, x i ^ 2 := fun x => by
      rw [EuclideanSpace.norm_sq_eq]; simp
    simp_rw [e]
    have hint_i : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        Integrable (fun x : EuclideanSpace ℝ (Fin k) => x i ^ 2) γ := fun i _ => by
      have hL : MemLp (fun x : EuclideanSpace ℝ (Fin k) => x i) 2 γ :=
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).comp_memLp' hm2
      simpa using hL.integrable_sq
    rw [integral_finsetSum _ hint_i]
    simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- **Lower bound for one law from two moments** (Tier C, lemma C1): if the Euclidean coordinate has
under `ν` the mean `e^{-ρt} p x₀` and second moment `e^{-2ρt}‖p x₀‖² + (k/ρ)(1-e^{-2ρt})`, then
`ρ e^{-2ρt}‖p x₀‖² + k (1-√(1-e^{-2ρt}))² ≤ ρ W₂²(ν, μ)`. -/
theorem lower_of_moments [IsProbabilityMeasure μ] (hρ : 0 < ρ) {t : ℝ} (ht : 0 ≤ t) (x₀ : M)
    (ν : Measure M) [IsProbabilityMeasure ν]
    (h1 : ∀ a : EuclideanSpace ℝ (Fin k),
      ∫ y, ⟪a, D.proj y⟫ ∂ν = Real.exp (-ρ * t) * ⟪a, D.proj x₀⟫)
    (h2i : Integrable (fun y => ‖D.proj y‖ ^ 2) ν)
    (h2 : ∫ y, ‖D.proj y‖ ^ 2 ∂ν =
      Real.exp (-2 * ρ * t) * ‖D.proj x₀‖ ^ 2 + k / ρ * (1 - Real.exp (-2 * ρ * t))) :
    ENNReal.ofReal (ρ * (Real.exp (-2 * ρ * t) * ‖D.proj x₀‖ ^ 2) +
        k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
      ENNReal.ofReal ρ * CutCur.wasserstein2 ν μ ^ 2 := by
  obtain ⟨hμ1, hμ2i, hμ2⟩ := D.proj_moments hρ
  rw [wasserstein2_sq_eq_cost2]
  have hne0 : ENNReal.ofReal ρ ≠ 0 := by simpa using hρ
  have hneT : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold cost2
  rw [ENNReal.mul_iInf_of_ne hne0 hneT]
  refine le_iInf fun π => ?_
  rw [ENNReal.mul_iInf_of_ne hne0 hneT]
  refine le_iInf fun hπ => ?_
  have hpm := D.measurable_proj
  have hπp : IsProbabilityMeasure π := by
    refine ⟨?_⟩
    have := congrArg (fun m => m univ) hπ.1
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
      measure_univ] at this
    exact this
  set q := Real.exp (-2 * ρ * t) with hq
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  set s := Real.sqrt (1 - q) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hkρ : 0 ≤ (k : ℝ) / ρ := by positivity
  set X : M × M → EuclideanSpace ℝ (Fin k) := fun z => D.proj z.1 with hX
  set Z : M × M → EuclideanSpace ℝ (Fin k) := fun z => D.proj z.2 with hZ
  have hXm : Measurable X := hpm.comp measurable_fst
  have hZm : Measurable Z := hpm.comp measurable_snd
  have e1 : ∀ (g : EuclideanSpace ℝ (Fin k) → ℝ), Measurable g →
      ∫ z, g (X z) ∂π = ∫ y, g (D.proj y) ∂ν := fun g hg => by
    have := integral_map (μ := π) (φ := Prod.fst) measurable_fst.aemeasurable
      (f := fun y => g (D.proj y)) (hg.comp hpm).aestronglyMeasurable
    rw [hπ.1] at this
    exact this.symm
  have e2 : ∀ (g : EuclideanSpace ℝ (Fin k) → ℝ), Measurable g →
      ∫ z, g (Z z) ∂π = ∫ y, g (D.proj y) ∂μ := fun g hg => by
    have := integral_map (μ := π) (φ := Prod.snd) measurable_snd.aemeasurable
      (f := fun y => g (D.proj y)) (hg.comp hpm).aestronglyMeasurable
    rw [hπ.2] at this
    exact this.symm
  have i1 : ∀ (g : EuclideanSpace ℝ (Fin k) → ℝ), Measurable g →
      Integrable (fun y => g (D.proj y)) ν → Integrable (fun z => g (X z)) π := fun g hg h => by
    have : Integrable (fun y => g (D.proj y)) (π.map Prod.fst) := by rw [hπ.1]; exact h
    exact (integrable_map_measure (hg.comp hpm).aestronglyMeasurable
      measurable_fst.aemeasurable).1 this
  have i2 : ∀ (g : EuclideanSpace ℝ (Fin k) → ℝ), Measurable g →
      Integrable (fun y => g (D.proj y)) μ → Integrable (fun z => g (Z z)) π := fun g hg h => by
    have : Integrable (fun y => g (D.proj y)) (π.map Prod.snd) := by rw [hπ.2]; exact h
    exact (integrable_map_measure (hg.comp hpm).aestronglyMeasurable
      measurable_snd.aemeasurable).1 this
  have hsq : Measurable (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2) := by fun_prop
  have key := lower_aux π X Z hXm hZm (Real.exp (-ρ * t) • D.proj x₀) (k / ρ * (1 - q)) (k / ρ)
    (fun a => by
      rw [e1 (fun x => ⟪a, x⟫) (by fun_prop), h1 a, inner_smul_right])
    (i1 _ hsq h2i)
    (by
      rw [e1 _ hsq, h2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have : Real.exp (-ρ * t) ^ 2 = q := by
        rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [this])
    (fun a => by rw [e2 (fun x => ⟪a, x⟫) (by fun_prop), hμ1 a])
    (i2 _ hsq hμ2i)
    (by rw [e2 _ hsq, hμ2])
  -- algebra
  have hCB : Real.sqrt (k / ρ * (1 - q) * (k / ρ)) = k / ρ * s := by
    rw [show k / ρ * (1 - q) * (k / ρ) = (k / ρ * s) ^ 2 by rw [mul_pow, hs2]; ring]
    exact Real.sqrt_sq (mul_nonneg hkρ hs0)
  rw [hCB, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at key
  have hE : Real.exp (-ρ * t) ^ 2 = q := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hE] at key
  -- integrability of the cost
  have hcostm : Measurable (fun z : M × M => ‖X z - Z z‖ ^ 2) := by fun_prop
  have hint : Integrable (fun z : M × M => ‖X z - Z z‖ ^ 2) π := by
    have hX2 := i1 _ hsq h2i
    have hZ2 := i2 _ hsq hμ2i
    refine ((hX2.add hZ2).const_mul 2).mono' hcostm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖X z - Z z‖))]
    show ‖X z - Z z‖ ^ 2 ≤ 2 * (‖X z‖ ^ 2 + ‖Z z‖ ^ 2)
    have := norm_sub_le (X z) (Z z)
    nlinarith [sq_nonneg (‖X z‖ - ‖Z z‖), norm_nonneg (X z), norm_nonneg (Z z),
      norm_nonneg (X z - Z z)]
  have hle : ∫⁻ z, ENNReal.ofReal (‖X z - Z z‖ ^ 2) ∂π ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := by
    refine lintegral_mono fun z => ?_
    have h := D.edist_proj_le z.1 z.2
    calc ENNReal.ofReal (‖X z - Z z‖ ^ 2) = edist (D.proj z.1) (D.proj z.2) ^ 2 := by
          rw [edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ edist z.1 z.2 ^ 2 := pow_le_pow_left' h 2
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => sq_nonneg _)] at hle
  calc ENNReal.ofReal (ρ * (q * ‖D.proj x₀‖ ^ 2) + k * (1 - s) ^ 2)
      ≤ ENNReal.ofReal (ρ * ∫ z, ‖X z - Z z‖ ^ 2 ∂π) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hρ' : ρ * (k / ρ) = k := by field_simp
        have : k * (1 - s) ^ 2 = ρ * (k / ρ * (1 - s) ^ 2) := by field_simp
        rw [this, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hρ.le
        nlinarith [key, hs2]
    _ = ENNReal.ofReal ρ * ENNReal.ofReal (∫ z, ‖X z - Z z‖ ^ 2 ∂π) :=
        ENNReal.ofReal_mul hρ.le
    _ ≤ ENNReal.ofReal ρ * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := by gcongr

end SplitData

end Split

section Upper

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]

/-- **Upper bound from the Dirac contraction** (Tier C, lemma C2): a pointwise bound
`W₂²(P x, μ) ≤ q ∫ d(x,·)² dμ` gives the same bound for the supremum over any set. -/
theorem upper_iSup_dirac (P : Kernel M M) {μ : Measure M} {q : ℝ≥0∞}
    (h : ∀ x, CutCur.wasserstein2 (P x) μ ^ 2 ≤ q * ∫⁻ y, edist x y ^ 2 ∂μ) (S : Set M) :
    ⨆ x₀ ∈ S, CutCur.wasserstein2 (P x₀) μ ^ 2 ≤ q * ⨆ x₀ ∈ S, ∫⁻ y, edist x₀ y ^ 2 ∂μ := by
  refine iSup₂_le fun x₀ hx₀ => (h x₀).trans ?_
  gcongr
  exact le_iSup₂ (f := fun x₀ (_ : x₀ ∈ S) => ∫⁻ y, edist x₀ y ^ 2 ∂μ) x₀ hx₀

end Upper

end CutoffRigidity.Riemann
