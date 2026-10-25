module

public import CutoffRigidity.Riemann.DiffKantorovichProper1
public import CutoffRigidity.Riemann.TransportW2
public import CutoffRigidity.CompactLipschitzTransportDuality

/-! # Kantorovich duality on a proper metric space, part 2: extension of compact dual pairs

For the truncated cost `cR R x y = (min (dist x y) R)^2` (bounded, Lipschitz in each variable),
a dual pair `(f, g)` of continuous functions on a compact set `A ⊆ X` with `f x + g y ≤ cR R x y`
on `A × A` is extended, by two `cR`-transforms, to a pair of bounded Lipschitz functions
`(F, G)` on `X` with `F x + G y ≤ dist x y ^ 2`, `f ≤ F`, `g ≤ G` on `A`, and oscillation at most
`R^2` relative to a base point of `A`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CutoffRigidity.Riemann

section

variable {X : Type*} [MetricSpace X]

/-- The truncated quadratic cost. -/
noncomputable def cR (R : ℝ) (x y : X) : ℝ := (min (dist x y) R) ^ 2

theorem cR_nonneg (R : ℝ) (x y : X) : 0 ≤ cR R x y := sq_nonneg _

theorem cR_le_sq (R : ℝ) (hR : 0 ≤ R) (x y : X) : cR R x y ≤ dist x y ^ 2 := by
  unfold cR
  exact pow_le_pow_left₀ (le_min dist_nonneg hR) (min_le_left _ _) 2

theorem cR_le_R_sq (R : ℝ) (hR : 0 ≤ R) (x y : X) : cR R x y ≤ R ^ 2 := by
  unfold cR
  exact pow_le_pow_left₀ (le_min dist_nonneg hR) (min_le_right _ _) 2

theorem cR_self (R : ℝ) (hR : 0 ≤ R) (x : X) : cR R x x = 0 := by simp [cR, hR]

theorem cR_comm (R : ℝ) (x y : X) : cR R x y = cR R y x := by simp [cR, dist_comm]

theorem continuous_cR (R : ℝ) : Continuous (fun z : X × X => cR R z.1 z.2) := by
  unfold cR; fun_prop

/-- `cR` is `2R`-Lipschitz in its second variable. -/
theorem cR_le_add (R : ℝ) (hR : 0 ≤ R) (x y y' : X) :
    cR R x y ≤ cR R x y' + 2 * R * dist y y' := by
  unfold cR
  have h1 : |min (dist x y) R - min (dist x y') R| ≤ dist y y' := by
    have := (LipschitzWith.id.min_const R).dist_le_mul (dist x y) (dist x y')
    simp only [NNReal.coe_one, one_mul, id_eq] at this
    rw [← Real.dist_eq]
    exact this.trans (dist_dist_dist_le_right x y y')
  set a := min (dist x y) R
  set b := min (dist x y') R
  have ha0 : 0 ≤ a := le_min dist_nonneg hR
  have hb0 : 0 ≤ b := le_min dist_nonneg hR
  have haR : a ≤ R := min_le_right _ _
  have hbR : b ≤ R := min_le_right _ _
  have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  have h2 : (a - b) * (a + b) ≤ |a - b| * (2 * R) := by
    calc (a - b) * (a + b) ≤ |(a - b) * (a + b)| := le_abs_self _
      _ = |a - b| * (a + b) := by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ a + b by linarith)]
      _ ≤ |a - b| * (2 * R) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 2 * R)]

theorem lipschitz_iInf {ι : Type*} [Nonempty ι] {α : Type*} [PseudoMetricSpace α]
    (u : ι → α → ℝ) (K : ℝ≥0) (hu : ∀ i x y, u i x ≤ u i y + K * dist x y)
    (hb : ∀ x, BddBelow (range fun i => u i x)) :
    LipschitzWith K (fun x => ⨅ i, u i x) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  have : (⨅ i, u i x) - K * dist x y ≤ ⨅ i, u i y := by
    refine le_ciInf fun i => ?_
    have := (ciInf_le (hb x) i).trans (hu i x y)
    have h2 := hu i y x
    rw [sub_le_iff_le_add]
    exact this
  linarith

/-- Extension of a compact dual pair to a pair of bounded Lipschitz functions on `X`. -/
theorem exists_extension_pair (R : ℝ) (hR : 0 ≤ R) (A : Set X) (hA : IsCompact A) (x₀ : X)
    (hx₀ : x₀ ∈ A) (f g : C(A, ℝ)) (hfg : ∀ x y : A, f x + g y ≤ cR R (x : X) (y : X)) :
    ∃ (F G : X →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L F ∧ LipschitzWith J G ∧
      (∀ x y, F x + G y ≤ dist x y ^ 2) ∧ (∀ a : A, f a ≤ F a) ∧ (∀ a : A, g a ≤ G a) ∧
      (∀ x, F x₀ ≤ F x + R ^ 2) ∧ (∀ y, G x₀ ≤ G y + R ^ 2) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  haveI : Nonempty A := ⟨⟨x₀, hx₀⟩⟩
  haveI : Nonempty X := ⟨x₀⟩
  set M : ℝ := ‖f‖ with hM
  have hf : ∀ a : A, |f a| ≤ M := fun a => by
    simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f a
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  set K : ℝ≥0 := ⟨2 * R, by positivity⟩ with hK
  have hKc : (K : ℝ) = 2 * R := rfl
  let Gf : X → ℝ := fun y => ⨅ a : A, (cR R (a : X) y - f a)
  have hGb : ∀ y, BddBelow (range fun a : A => cR R (a : X) y - f a) := fun y =>
    ⟨-M, by rintro _ ⟨a, rfl⟩; have := cR_nonneg R (a : X) y; have := (abs_le.mp (hf a)).2; simp only; linarith⟩
  have hGlow : ∀ y, -M ≤ Gf y := fun y => le_ciInf fun a => by
    have := cR_nonneg R (a : X) y; have := (abs_le.mp (hf a)).2; linarith
  have hGup : ∀ y, Gf y ≤ R ^ 2 + M := fun y => by
    have h1 := ciInf_le (hGb y) ⟨x₀, hx₀⟩
    have h2 := cR_le_R_sq R hR x₀ y
    have h3 := (abs_le.mp (hf ⟨x₀, hx₀⟩)).1
    simp only at h1
    linarith
  have hGlip : LipschitzWith K Gf := by
    refine lipschitz_iInf (fun (a : A) y => cR R (a : X) y - f a) K ?_ hGb
    intro a y y'
    have := cR_le_add R hR (a : X) y y'
    simp only [hKc]
    linarith
  let Ff : X → ℝ := fun x => ⨅ y : X, (cR R x y - Gf y)
  have hFb : ∀ x, BddBelow (range fun y : X => cR R x y - Gf y) := fun x =>
    ⟨-(R ^ 2 + M), by rintro _ ⟨y, rfl⟩; have := cR_nonneg R x y; have := hGup y; simp only; linarith⟩
  have hFlow : ∀ x, -(R ^ 2 + M) ≤ Ff x := fun x => le_ciInf fun y => by
    have := cR_nonneg R x y; have := hGup y; linarith
  have hFup : ∀ x, Ff x ≤ M := fun x => by
    have h1 := ciInf_le (hFb x) x
    have := hGlow x
    simp only [cR_self R hR] at h1
    linarith
  have hFlip : LipschitzWith K Ff := by
    refine lipschitz_iInf (fun (y : X) x => cR R x y - Gf y) K ?_ hFb
    intro y x x'
    have := cR_le_add R hR y x x'
    rw [cR_comm R y x, cR_comm R y x'] at this
    simp only [hKc]
    linarith
  have hGb' : ∀ y, ‖Gf y‖ ≤ R ^ 2 + M := fun y => by
    rw [Real.norm_eq_abs, abs_le]; have := hGlow y; have := hGup y
    have : 0 ≤ M := norm_nonneg _
    constructor <;> linarith
  have hFb' : ∀ x, ‖Ff x‖ ≤ R ^ 2 + M := fun x => by
    rw [Real.norm_eq_abs, abs_le]; have := hFlow x; have := hFup x
    have : 0 ≤ M := norm_nonneg _
    constructor <;> linarith
  let F : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup Ff hFlip.continuous _ hFb'
  let G : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup Gf hGlip.continuous _ hGb'
  have hFx : ∀ x, F x = Ff x := fun x => rfl
  have hGx : ∀ x, G x = Gf x := fun x => rfl
  refine ⟨F, G, K, K, hFlip, hGlip, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [hFx, hGx]
    have h1 := ciInf_le (hFb x) y
    have := cR_le_sq R hR x y
    linarith
  · intro a
    rw [hFx]
    refine le_ciInf fun y => ?_
    have := ciInf_le (hGb y) a
    show f a ≤ cR R (a : X) y - Gf y
    linarith
  · intro a
    rw [hGx]
    refine le_ciInf fun b => ?_
    have := hfg b a
    show g a ≤ cR R (b : X) (a : X) - f b
    linarith
  · intro x
    rw [hFx, hFx]
    have : Ff x₀ - R ^ 2 ≤ Ff x := by
      refine le_ciInf fun y => ?_
      have h1 := ciInf_le (hFb x₀) y
      have := cR_le_R_sq R hR x₀ y
      have := cR_nonneg R x y
      linarith
    linarith
  · intro y
    rw [hGx, hGx]
    have : Gf x₀ - R ^ 2 ≤ Gf y := by
      refine le_ciInf fun a => ?_
      have h1 := ciInf_le (hGb x₀) a
      have := cR_le_R_sq R hR (a : X) x₀
      have := cR_nonneg R (a : X) y
      linarith
    linarith

end

section Coupling

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

open scoped Classical in
/-- The truncation sending the complement of `A` to the base point `x₀`. -/
noncomputable def truncTo (A : Set X) (x₀ : X) : X → X := A.piecewise id (fun _ => x₀)

theorem measurable_truncTo {A : Set X} (hA : MeasurableSet A) (x₀ : X) :
    Measurable (truncTo A x₀) := Measurable.piecewise hA measurable_id measurable_const

theorem truncTo_mem {A : Set X} {x₀ : X} (hx₀ : x₀ ∈ A) (x : X) : truncTo A x₀ x ∈ A := by
  classical
  unfold truncTo
  by_cases h : x ∈ A
  · simpa [Set.piecewise_eq_of_mem _ _ _ h] using h
  · simpa [Set.piecewise_eq_of_notMem _ _ _ h] using hx₀

theorem truncTo_of_mem {A : Set X} {x₀ x : X} (h : x ∈ A) : truncTo A x₀ x = x := by
  classical
  simp [truncTo, Set.piecewise_eq_of_mem _ _ _ h]

theorem truncTo_of_notMem {A : Set X} {x₀ x : X} (h : x ∉ A) : truncTo A x₀ x = x₀ := by
  classical
  simp [truncTo, Set.piecewise_eq_of_notMem _ _ _ h]

set_option maxHeartbeats 1600000 in
/-- Truncated coupling: the compact strong duality on a compact set `A`, fed by the extension of
dual pairs, produces a coupling of the truncated laws whose truncated cost is controlled by the
budget `K` plus the tails of `μ` and `ν` outside `A`. -/
theorem exists_trunc_coupling (R : ℝ) (hR : 0 ≤ R) (A : Set X) (hA : IsCompact A) (x₀ : X)
    (hx₀ : x₀ ∈ A) (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (K : ℝ)
    (hDual : ∀ (f g : X →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x + g y ≤ dist x y ^ 2) → ∫ x, f x ∂μ + ∫ y, g y ∂ν ≤ K) :
    ∃ π : Measure (X × X), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ.map (truncTo A x₀) ∧ π.map Prod.snd = ν.map (truncTo A x₀) ∧
      ∫⁻ z, ENNReal.ofReal (cR R z.1 z.2) ∂π ≤
        ENNReal.ofReal (K + R ^ 2 * (μ.real Aᶜ + ν.real Aᶜ)) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hTm := measurable_truncTo hAm x₀
  let T : X → A := fun x => ⟨truncTo A x₀ x, truncTo_mem hx₀ x⟩
  have hT : Measurable T := hTm.subtype_mk
  let μn : Measure A := μ.map T
  let νn : Measure A := ν.map T
  haveI : IsProbabilityMeasure μn := inferInstance
  haveI : IsProbabilityMeasure νn := inferInstance
  let c : C(A × A, ℝ) := ⟨fun z => cR R (z.1 : X) (z.2 : X), by
    have := continuous_cR (X := X) R
    fun_prop⟩
  -- pointwise inequality and its integrated form
  have bound : ∀ (h : C(A, ℝ)) (H : X →ᵇ ℝ) (ρ : Measure X) [IsProbabilityMeasure ρ],
      (∀ a : A, h a ≤ H a) → (∀ x, H x₀ ≤ H x + R ^ 2) →
      ∫ a, h a ∂(ρ.map T) ≤ ∫ x, H x ∂ρ + R ^ 2 * ρ.real Aᶜ := by
    intro h H ρ _ hH hH0
    have hint : ∫ a, h a ∂(ρ.map T) = ∫ x, h (T x) ∂ρ :=
      integral_map hT.aemeasurable h.continuous.aestronglyMeasurable
    rw [hint]
    have hi1 : Integrable (fun x => h (T x)) ρ := by
      refine Integrable.of_bound (C := ‖h‖) ((h.continuous.measurable.comp hT).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      simpa using ContinuousMap.norm_coe_le_norm h (T x)
    have hi2 : Integrable (fun x => H x + Aᶜ.indicator (fun _ => R ^ 2) x) ρ :=
      (H.integrable ρ).add ((integrable_const (R ^ 2)).indicator hAm.compl)
    have hle : ∫ x, h (T x) ∂ρ ≤ ∫ x, (H x + Aᶜ.indicator (fun _ => R ^ 2) x) ∂ρ := by
      refine integral_mono hi1 hi2 fun x => ?_
      by_cases hx : x ∈ A
      · have : T x = ⟨x, hx⟩ := Subtype.ext (truncTo_of_mem hx)
        simp only [this, Set.indicator_of_notMem (show x ∉ Aᶜ by simpa using hx), add_zero]
        exact hH ⟨x, hx⟩
      · have : T x = ⟨x₀, hx₀⟩ := Subtype.ext (truncTo_of_notMem hx)
        simp only [this, Set.indicator_of_mem (show x ∈ Aᶜ from hx)]
        have := hH ⟨x₀, hx₀⟩
        have := hH0 x
        simp only at *
        linarith
    refine hle.trans (le_of_eq ?_)
    rw [integral_add (H.integrable ρ) ((integrable_const (R ^ 2)).indicator hAm.compl),
      integral_indicator_const _ hAm.compl]
    simp [Measure.real, mul_comm]
  have hd : ∀ (f g : C(A, ℝ)), (∀ x y, f x + g y ≤ c (x, y)) →
      ∫ x, f x ∂μn + ∫ y, g y ∂νn ≤ K + R ^ 2 * (μ.real Aᶜ + ν.real Aᶜ) := by
    intro f g hfg
    obtain ⟨F, G, L, J, hL, hJ, hFG, hf, hg, hF0, hG0⟩ :=
      exists_extension_pair R hR A hA x₀ hx₀ f g hfg
    have h1 := bound f F μ hf hF0
    have h2 := bound g G ν hg hG0
    have h3 := hDual F G L J hL hJ hFG
    change ∫ a, f a ∂(μ.map T) + ∫ a, g a ∂(ν.map T) ≤ _
    nlinarith
  obtain ⟨π, hπ, hF, hS, hC⟩ := exists_compact_transport_coupling_of_dual_budget μn νn c _ hd
  let ι : A × A → X × X := fun z => ((z.1 : X), (z.2 : X))
  have hι : Continuous ι := by fun_prop
  haveI := hπ
  refine ⟨π.map ι, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hι.measurable]
    have he : (Prod.fst ∘ ι) = (Subtype.val ∘ Prod.fst) := rfl
    rw [he, ← Measure.map_map measurable_subtype_coe measurable_fst, hF,
      Measure.map_map measurable_subtype_coe hT]
    rfl
  · rw [Measure.map_map measurable_snd hι.measurable]
    have he : (Prod.snd ∘ ι) = (Subtype.val ∘ Prod.snd) := rfl
    rw [he, ← Measure.map_map measurable_subtype_coe measurable_snd, hS,
      Measure.map_map measurable_subtype_coe hT]
    rfl
  · have hm : Measurable fun z : X × X => ENNReal.ofReal (cR R z.1 z.2) :=
      ENNReal.measurable_ofReal.comp (continuous_cR R).measurable
    rw [lintegral_map hm hι.measurable]
    have he : ∫⁻ z : A × A, ENNReal.ofReal (cR R (ι z).1 (ι z).2) ∂π =
        ENNReal.ofReal (∫ z, c z ∂π) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (c.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (Eventually.of_forall fun z => cR_nonneg R _ _)]
      rfl
    rw [he]
    exact ENNReal.ofReal_le_ofReal hC

end Coupling

end CutoffRigidity.Riemann
