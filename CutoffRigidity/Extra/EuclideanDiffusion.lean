module

public import CutoffRigidity.Statements
public import CutoffRigidity.Paper.CarrierDefs
public import CutoffRigidity.Riemann.DiffFinal
public import CutoffRigidity.Riemann.WitnessMain
public import CutoffRigidity.Paper.CoreBridge
public import CutoffRigidity.Paper.ExistsBrownian
public import CutoffRigidity.LangevinDynkin

/-! # Brownian-free Euclidean Langevin setting

Bridge lemmas for the Challenge definitions (`IsEuclideanDiffusion`, `IsEuclideanLangevin`, `worstK`, `mixingTimeK`,
`mixingTimeW2K`, `mixingTimeKLK`, `IsRigidSequenceK`, now in `Challenge`/`CutoffRigidity.Statements`) replacing the Brownian carrier
`(Ω, B, P, X)` of `IsLangevin` by transition kernels `Pt`: equivalence with the Riemannian
`IsDiffusionSemigroup` on flat `ℝ^d`, the library `langevinKernel` as a witness, uniqueness for
`C^∞` potentials, non-vacuity, and the transfer lemmas producing a Brownian carrier whose
Langevin process has the prescribed transition kernels.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Manifold

end CutCur

namespace CutCur

open CutoffRigidity CutoffRigidity.Riemann
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Manifold

theorem generator_eq_langevinOp {d : ℕ} {V f : Rd d → ℝ} (hf : ContDiff ℝ 2 f) (x : Rd d) :
    generator V f x = langevinDifferentialOperator V f x := by
  unfold generator langevinDifferentialOperator
  rw [Paper.laplacian_eq_euclideanLaplacian hf]

/-- Flat `ℝ^d` in the Riemannian framework: `IsEuclideanDiffusion` is `IsDiffusionSemigroup`. -/
theorem isEuclideanDiffusion_iff {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} :
    IsEuclideanDiffusion V Pt ↔ IsDiffusionSemigroup (Rd d) V Pt := by
  have key : ∀ f : Rd d → ℝ, ContDiff ℝ ∞ f → ∀ y, mgenerator (Rd d) V f y = generator V f y := by
    intro f hf y
    rw [Riemann.Witness.mgenerator_rd (hf.of_le (by norm_cast)),
      generator_eq_langevinOp (hf.of_le (by norm_cast))]
  unfold IsEuclideanDiffusion IsDiffusionSemigroup
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h f hf hfc x t
    have := h f ((contMDiff_iff_contDiff).1 hf) hfc x t
    simpa [key f ((contMDiff_iff_contDiff).1 hf)] using this
  · intro h f hf hfc x t
    have := h f (contMDiff_iff_contDiff.2 hf) hfc x t
    simpa [key f hf] using this

/-- The project's Brownian-driven Langevin kernel is a Euclidean diffusion semigroup
(`C²` potential with `Hess V ≥ rate ≥ 0`). -/
theorem isEuclideanDiffusion_langevinKernel {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : Rd d, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    IsEuclideanDiffusion V (langevinKernel V B P) := by
  refine ⟨fun t => langevinKernel_isMarkovKernel hB hV rate hrate hHess t, fun s t => ?_, ?_⟩
  · exact (langevinKernel_comp hB hV rate hrate hHess s t).symm
  · intro f hf hfc x t
    have h := langevinKernel_dynkin_identity hB hV (hf.of_le (by norm_cast)) hfc rate hrate hHess x
      (T := (t : ℝ)) t.2
    simp only [Real.toNNReal_coe] at h
    rw [h]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [generator_eq_langevinOp (hf.of_le (by norm_cast))]

/-- Uniqueness of Euclidean diffusion semigroups for `C^∞` potentials with probability Gibbs
measure (Riemannian `bridge_final` on flat space). -/
theorem isEuclideanDiffusion_unique {d : ℕ} {V : Rd d → ℝ} (hV : ContDiff ℝ ∞ V)
    (hp : IsProbabilityMeasure (gibbs V))
    {P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d)} (h₁ : IsEuclideanDiffusion V P₁)
    (h₂ : IsEuclideanDiffusion V P₂) : ∀ t x, P₁ t x = P₂ t x := by
  have hV' : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) ∞ V := contMDiff_iff_contDiff.2 hV
  have hμ := Riemann.Witness.isWeightedVolume_gibbs V
  intro t x
  rw [Diff.bridge_final (Rd d) hV' hμ (isEuclideanDiffusion_iff.1 h₁) t x,
    Diff.bridge_final (Rd d) hV' hμ (isEuclideanDiffusion_iff.1 h₂) t x]

/-- Uniqueness, `IsEuclideanLangevin` form. -/
theorem isEuclideanLangevin_unique {d : ℕ} {V : Rd d → ℝ} {P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h₁ : IsEuclideanLangevin V P₁) (h₂ : IsEuclideanLangevin V P₂) : ∀ t x, P₁ t x = P₂ t x :=
  isEuclideanDiffusion_unique h₁.1 h₁.2.1 h₁.2.2 h₂.2.2

/-- An abstract Euclidean diffusion is the library Langevin kernel (smooth convex potential, any
Brownian carrier). -/
theorem isEuclideanDiffusion_eq_langevinKernel {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : Rd d → ℝ} (hV : ContDiff ℝ ∞ V) (hp : IsProbabilityMeasure (gibbs V))
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : Rd d, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hP : IsEuclideanDiffusion V Pt) (t : ℝ≥0) (x : Rd d) :
    Pt t x = langevinKernel V B P t x :=
  isEuclideanDiffusion_unique hV hp hP
    (isEuclideanDiffusion_langevinKernel hB (hV.of_le (by norm_cast)) rate hrate hHess) t x

/-- Non-vacuity: for a smooth convex potential with probability Gibbs measure there is a Euclidean
Langevin semigroup. -/
theorem exists_euclideanLangevin {d : ℕ} {V : Rd d → ℝ} (hV : ContDiff ℝ ∞ V)
    (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbs V)) :
    ∃ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsEuclideanLangevin V Pt := by
  obtain ⟨Ω, hΩ, P, B, hP, hB⟩ := Paper.exists_stdBrownian d
  have hH : ∀ x z : Rd d, (0 : ℝ) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z; simpa using hHess x z
  exact ⟨langevinKernel V B P, hV, hp,
    isEuclideanDiffusion_langevinKernel (Paper.isStdBrownian_iff.1 hB) (hV.of_le (by norm_cast))
      0 le_rfl hH⟩

/-- Non-vacuity without any convexity assumption: the canonical Riemannian kernel `Kk` on flat
space. -/
theorem exists_euclideanLangevin_of_smooth {d : ℕ} {V : Rd d → ℝ} (hV : ContDiff ℝ ∞ V)
    (hp : IsProbabilityMeasure (gibbs V)) :
    ∃ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsEuclideanLangevin V Pt := by
  have hV' : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) ∞ V := contMDiff_iff_contDiff.2 hV
  have hμ := Riemann.Witness.isWeightedVolume_gibbs V
  exact ⟨Diff.Kk (Rd d) hV' hμ, hV, hp,
    isEuclideanDiffusion_iff.2 (Diff.isDiffusionSemigroup_Kk (Rd d) hV' hμ)⟩

/-- **Transfer lemma.** For a smooth convex potential with a Euclidean Langevin semigroup `Pt`, there
are a probability space with a standard Brownian motion `B` and a family `X` of solutions of the
Langevin SDE (`IsLangevin V B P X`) whose one-time laws are the kernels `Pt`. -/
theorem exists_isLangevin_of_isEuclideanLangevin {d : ℕ} {V : Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt)
    (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω)
      (X : Rd d → ℝ≥0 → Ω → Rd d),
      IsProbabilityMeasure P ∧ IsLangevin V B P X ∧ ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀ := by
  obtain ⟨Ω, hΩ, P, B, hP, hB⟩ := Paper.exists_stdBrownian d
  have hB' : IsEuclideanBrownian B P := Paper.isStdBrownian_iff.1 hB
  have hV2 : ContDiff ℝ 2 V := hL.1.of_le (by norm_cast)
  have hH : ∀ x z : Rd d, (0 : ℝ) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z; simpa using hHess x z
  refine ⟨Ω, hΩ, B, P, fun x₀ => langevinProcess V B x₀, hP, ⟨hV2, hL.2.1, hB, fun x₀ => ?_⟩,
    fun t x₀ => ?_⟩
  · exact Paper.isLangevinSolution_langevinProcess hB' hV2 0 le_rfl hH x₀
  · exact (langevinKernel_apply_eq_process_law hB' hV2 0 le_rfl hH t x₀).symm.trans
      (isEuclideanDiffusion_eq_langevinKernel hB' hL.1 hL.2.1 0 le_rfl hH hL.2.2 t x₀).symm

/-- Convexity of a rigid potential: `Hess V ≥ gap ≥ 0`. -/
theorem RigidCurvature.hess_nonneg {d : ℕ} {V : Rd d → ℝ} (h : RigidCurvature V) :
    ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z := fun x z =>
  le_trans (mul_nonneg h.1.le (sq_nonneg _)) (h.2 x z)

/-- Transfer lemma for the rigid setting (convexity is implied by `RigidCurvature`). -/
theorem exists_isLangevin_of_rigid {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hL : IsEuclideanLangevin V Pt) (hR : RigidCurvature V) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω)
      (X : Rd d → ℝ≥0 → Ω → Rd d),
      IsProbabilityMeasure P ∧ IsLangevin V B P X ∧ ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀ :=
  exists_isLangevin_of_isEuclideanLangevin hL hR.hess_nonneg

/-- Transfer lemma for sequences: carriers `Ω n` chosen dimension by dimension. The conclusion
`IsRigidSequence V B P X` is the hypothesis of every sequence theorem of the Challenge, and the
laws are the given kernels in every positive dimension. -/
theorem exists_isRigidSequence_of_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt) :
    ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n)) (B : ∀ n, ℝ≥0 → Ω n → Rd n)
      (P : ∀ n, Measure (Ω n)) (X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n),
      (∀ n, 0 < n → IsProbabilityMeasure (P n)) ∧ IsRigidSequence V B P X ∧
        ∀ n, 0 < n → ∀ (t : ℝ≥0) (x₀ : Rd n), (P n).map (X n x₀ t) = Pt n t x₀ := by
  classical
  have hn : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd n) (P : Measure Ω)
      (X : Rd n → ℝ≥0 → Ω → Rd n), 0 < n → (IsProbabilityMeasure P ∧
        IsLangevin (V n) B P X ∧ ∀ (t : ℝ≥0) (x₀ : Rd n), P.map (X x₀ t) = Pt n t x₀) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨Ω, hΩ, B, P, X, h1⟩ := exists_isLangevin_of_rigid (h.1 n hn).1 (h.1 n hn).2
      exact ⟨Ω, hΩ, B, P, X, fun _ => h1⟩
    · exact ⟨Unit, inferInstance, fun _ _ => 0, 0, fun _ _ _ => 0, fun h' => absurd h' hn⟩
  choose Ω hΩ B P X hX using hn
  exact ⟨Ω, hΩ, B, P, X, fun n hn => (hX n hn).1,
    ⟨fun n hn => ⟨(hX n hn).2.1, (h.1 n hn).2⟩, h.2⟩, fun n hn => (hX n hn).2.2⟩

/-- `worst` of the carrier equals `worstK` of the kernels when the laws agree. -/
theorem worst_eq_worstK {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {X : Rd d → ℝ≥0 → Ω → Rd d} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀) (S : Set (Rd d))
    (δ : Measure (Rd d) → ℝ≥0∞) (t : ℝ) : worst P X S δ t = worstK Pt S δ t := by
  simp only [worst, worstK, h]

theorem mixingTime_eq_mixingTimeK {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {X : Rd d → ℝ≥0 → Ω → Rd d} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀) (μ : Measure (Rd d))
    (S : Set (Rd d)) (η : ℝ) : mixingTime P X μ S η = mixingTimeK Pt μ S η := by
  simp only [mixingTime, mixingTimeK, worst_eq_worstK h]

theorem mixingTimeW2_eq_mixingTimeW2K {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {X : Rd d → ℝ≥0 → Ω → Rd d} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀) (μ : Measure (Rd d))
    (S : Set (Rd d)) (η : ℝ) : mixingTimeW2 P X μ S η = mixingTimeW2K Pt μ S η := by
  simp only [mixingTimeW2, mixingTimeW2K, worst_eq_worstK h]

theorem mixingTimeKL_eq_mixingTimeKLK {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {X : Rd d → ℝ≥0 → Ω → Rd d} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀) (μ : Measure (Rd d))
    (S : Set (Rd d)) (η : ℝ) : mixingTimeKL P X μ S η = mixingTimeKLK Pt μ S η := by
  simp only [mixingTimeKL, mixingTimeKLK, worst_eq_worstK h]

/-- Sequence version of `worst_eq_worstK`: profiles agree eventually (positive dimensions). -/
theorem eventually_worst_eq_worstK {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : ∀ n, 0 < n → ∀ (t : ℝ≥0) (x₀ : Rd n), (P n).map (X n x₀ t) = Pt n t x₀)
    (S : ∀ n, Set (Rd n)) (δ : ∀ n, Measure (Rd n) → ℝ≥0∞) :
    ∀ᶠ n in atTop, (fun t => worst (P n) (X n) (S n) (δ n) t) =
      fun t => worstK (Pt n) (S n) (δ n) t := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  funext t
  exact worst_eq_worstK (h n hn) _ _ _

/-- Cutoff transfers from profiles that agree eventually (positive dimensions). -/
theorem hasCutoff_congr_eventually {p q : ℕ → ℝ → ℝ≥0∞} {t : ℕ → ℝ} {b a : ℝ≥0∞}
    (h : ∀ᶠ n in atTop, p n = q n) (hp : HasCutoff p t b a) : HasCutoff q t b a := by
  intro ε h0 h1
  obtain ⟨u, v⟩ := hp ε h0 h1
  exact ⟨u.congr' (by filter_upwards [h] with n hn; rw [hn]),
    v.congr' (by filter_upwards [h] with n hn; rw [hn])⟩

end CutCur
