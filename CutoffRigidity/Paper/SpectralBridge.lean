module

public import CutoffRigidity.Paper.GapBridge
public import CutoffRigidity.GibbsSpectralPoincare
public import CutoffRigidity.GibbsOperatorCurvatureGap
public import CutoffRigidity.GibbsOperatorAffineRepresentative
public import CutoffRigidity.OperatorWassersteinTheorem

/-! # Bridges from the statement surface to the library: spectral objects

Under the rigid curvature condition `Hess V ≥ λ₁ > 0`, the variational spectral
gap of the statement surface (the optimal Poincaré constant over smooth compactly
supported functions) is the library's operator-theoretic gap: the Poincaré
inequality at the library gap bounds every Rayleigh quotient from below, and the
Bakry–Émery bound of the library gives the converse. Consequently the first
eigenspace, its dimension `k₁` and the function `Λ` agree with the library ones.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ContDiff

variable {d : ℕ}

/-! ### The first eigenspace -/

/-- The first eigenspace of the statement surface is the library's classical `L²`
eigenspace at the variational gap (no assumption needed). -/
theorem firstEigenspace_eq_classicalL2Eigenspace (V : CutCur.Rd d → ℝ) :
    CutCur.firstEigenspace V = classicalL2Eigenspace V (CutCur.spectralGap V) := by
  apply le_antisymm
  · rw [CutCur.firstEigenspace]
    refine Submodule.span_le.mpr ?_
    rintro u ⟨f, hf, hae⟩
    obtain ⟨hf2, -, he⟩ := isEigenfunction_iff.mp hf
    exact ⟨f, hf2, he, hae⟩
  · rintro u ⟨f, hf2, he, hae⟩
    exact Submodule.subset_span
      ⟨f, isEigenfunction_iff.mpr ⟨hf2, (Lp.memLp u).ae_eq hae.symm, he⟩, hae⟩

/-- Under the rigid curvature condition the first eigenspace is the library's first
eigenspace of the self-adjoint Gibbs operator. -/
theorem firstEigenspace_eq_gibbsFirstEigenspace {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V) :
    CutCur.firstEigenspace V = gibbsFirstEigenspace hV hp := by
  rw [firstEigenspace_eq_classicalL2Eigenspace, gibbsFirstEigenspace,
    ← spectralGap_eq_gibbsSpectralGap hV hp hrig,
    gibbsOperatorEigenspace_eq_classicalL2Eigenspace hV hp _ hrig.1 hrig.2]

/-- `k₁` is the dimension of the library's first operator eigenspace. -/
theorem firstEigenDim_eq {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V) :
    CutCur.firstEigenDim V = Module.finrank ℝ (gibbsFirstEigenspace hV hp) := by
  rw [CutCur.firstEigenDim, firstEigenspace_eq_gibbsFirstEigenspace hV hp hrig]
  rfl

/-- `1 ≤ k₁ ≤ d` under the rigid curvature condition. -/
theorem one_le_firstEigenDim {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V) :
    1 ≤ CutCur.firstEigenDim V := by
  rw [firstEigenDim_eq hV hp hrig]
  exact firstEigenspace_finrank_pos hV hp (pos_dim_of_rigidCurvature hp hrig) _ hrig.1 hrig.2
    (spectralGap_eq_gibbsSpectralGap hV hp hrig).symm

theorem firstEigenDim_le {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V) :
    CutCur.firstEigenDim V ≤ d := by
  rw [firstEigenDim_eq hV hp hrig]
  exact firstEigenspace_finrank_le hV hp _ hrig.1 hrig.2
    (spectralGap_eq_gibbsSpectralGap hV hp hrig).symm

/-! ### The function `Λ` -/

theorem integral_mul_eq_inner {V f g : CutCur.Rd d → ℝ} (hf : MemLp f 2 (gibbsMeasure volume V))
    (hg : MemLp g 2 (gibbsMeasure volume V)) :
    ∫ x, f x * g x ∂gibbsMeasure volume V = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy, Real.inner_apply, mul_comm]

/-- Every orthonormal eigenbasis of the statement surface computes the library's
evaluation-norm `Λ`. -/
theorem sum_sq_eq_firstEigenLambdaPoint {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V)
    (f : Fin (CutCur.firstEigenDim V) → CutCur.Rd d → ℝ) (hf : CutCur.IsEigenbasis V f)
    (x₀ : CutCur.Rd d) :
    ∑ i, f i x₀ ^ 2 = firstEigenLambdaPoint hV hp (CutCur.spectralGap V) hrig.1 hrig.2
      (spectralGap_eq_gibbsSpectralGap hV hp hrig).symm x₀ := by
  set ρ := CutCur.spectralGap V
  have hG := (spectralGap_eq_gibbsSpectralGap hV hp hrig).symm
  have hk := firstEigenDim_eq hV hp hrig
  let := firstEigenspace_finiteDimensional hV hp ρ hrig.1 hrig.2 hG
  set W := gibbsFirstEigenspace hV hp
  have hW : ∀ u : CutCur.Rd d →₂[gibbsMeasure volume V] ℝ,
      u ∈ W ↔ u ∈ classicalL2Eigenspace V ρ := by
    intro u
    change u ∈ gibbsOperatorEigenspace hV hp (gibbsSpectralGap hV hp) ↔ _
    rw [hG, gibbsOperatorEigenspace_eq_classicalL2Eigenspace hV hp ρ hrig.1 hrig.2]
  obtain ⟨hfe, hon⟩ := hf
  let v : Fin (CutCur.firstEigenDim V) → W := fun i =>
    ⟨(hfe i).2.1.toLp (f i), (hW _).mpr ⟨f i, (hfe i).1,
      (isEigenfunction_iff.mp (hfe i)).2.2, (hfe i).2.1.coeFn_toLp.symm⟩⟩
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ ((hfe i).2.1.toLp (f i)) ((hfe j).2.1.toLp (f j)) = _
    exact (integral_mul_eq_inner (V := V) (hfe i).2.1 (hfe j).2.1).symm.trans (hon i j)
  have hpos : 0 < CutCur.firstEigenDim V := one_le_firstEigenDim hV hp hrig
  let := Fin.pos_iff_nonempty.mp hpos
  let bb := basisOfOrthonormalOfCardEqFinrank hv (by simpa using hk)
  let b := OrthonormalBasis.mk hv (by
    rw [← coe_basisOfOrthonormalOfCardEqFinrank hv (by simpa using hk)]
    exact bb.span_eq.ge)
  rw [firstEigenLambdaPoint_eq_basis_sum hV hp ρ hrig.1 hrig.2 hG b x₀]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : b i = v i := by rw [OrthonormalBasis.coe_mk]
  have hu : f i = firstEigenRepresentative hV hp ρ hrig.1 hrig.2 hG (b i) := by
    apply operatorEigenRepresentative_unique hV hp ρ hrig.1 hrig.2 _ (hfe i).1.continuous
    rw [hb]
    exact (hfe i).2.1.coeFn_toLp.symm
  rw [← hu, sq_abs]

theorem firstEigenRepresentative_spec' {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (u : gibbsFirstEigenspace hV hp) :
    ContDiff ℝ 2 (firstEigenRepresentative hV hp ρ hρ hHess hgap u) ∧
    (∀ x, langevinDifferentialOperator V (firstEigenRepresentative hV hp ρ hρ hHess hgap u) x =
      -ρ * firstEigenRepresentative hV hp ρ hρ hHess hgap u x) ∧
    firstEigenRepresentative hV hp ρ hρ hHess hgap u =ᵐ[gibbsMeasure volume V]
      (u : CutCur.Rd d →₂[gibbsMeasure volume V] ℝ) := by
  subst hgap
  exact operatorEigenRepresentative_spec hV hp _ hρ hHess _

/-- An orthonormal eigenbasis of the statement surface exists. -/
theorem exists_isEigenbasis {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V) :
    ∃ f, CutCur.IsEigenbasis V f := by
  have hG := (spectralGap_eq_gibbsSpectralGap hV hp hrig).symm
  have hk := firstEigenDim_eq hV hp hrig
  have hrep : ∃ rep : gibbsFirstEigenspace hV hp → CutCur.Rd d → ℝ, ∀ u : gibbsFirstEigenspace hV hp,
      CutCur.IsEigenfunction V (CutCur.spectralGap V) (rep u) ∧
      rep u =ᵐ[gibbsMeasure volume V] (u : CutCur.Rd d →₂[gibbsMeasure volume V] ℝ) := by
    refine ⟨firstEigenRepresentative hV hp _ hrig.1 hrig.2 hG, fun u => ?_⟩
    obtain ⟨h2, he, hae⟩ := firstEigenRepresentative_spec' hV hp _ hrig.1 hrig.2 hG u
    exact ⟨isEigenfunction_iff.mpr ⟨h2, (Lp.memLp _).ae_eq hae.symm, he⟩, hae⟩
  obtain ⟨rep, hrep⟩ := hrep
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin (CutCur.firstEigenDim V)) ℝ (gibbsFirstEigenspace hV hp)) :=
    ⟨(firstEigenOrthonormalBasis hV hp _ hrig.1 hrig.2 hG).reindex (finCongr hk.symm)⟩
  refine ⟨fun i => rep (b i), fun i => (hrep (b i)).1, fun i j => ?_⟩
  have hi : MemLp (rep (b i)) 2 (gibbsMeasure volume V) := (hrep (b i)).1.2.1
  have hj : MemLp (rep (b j)) 2 (gibbsMeasure volume V) := (hrep (b j)).1.2.1
  have h1 : hi.toLp (rep (b i)) = (b i : CutCur.Rd d →₂[gibbsMeasure volume V] ℝ) :=
    Lp.ext (hi.coeFn_toLp.trans (hrep (b i)).2)
  have h2 : hj.toLp (rep (b j)) = (b j : CutCur.Rd d →₂[gibbsMeasure volume V] ℝ) :=
    Lp.ext (hj.coeFn_toLp.trans (hrep (b j)).2)
  have key : ∫ x, rep (b i) x * rep (b j) x ∂gibbsMeasure volume V =
      inner ℝ (b i : CutCur.Rd d →₂[gibbsMeasure volume V] ℝ) (b j) := by
    rw [integral_mul_eq_inner hi hj, h1, h2]
  refine key.trans ?_
  exact orthonormal_iff_ite.mp b.orthonormal i j

/-- `Λ(x₀)` is the library's evaluation-norm `Λ` on the first eigenspace. -/
theorem eigenLambda_eq {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V)
    (x₀ : CutCur.Rd d) :
    CutCur.eigenLambda V x₀ = ENNReal.ofReal (firstEigenLambdaPoint hV hp (CutCur.spectralGap V)
      hrig.1 hrig.2 (spectralGap_eq_gibbsSpectralGap hV hp hrig).symm x₀) := by
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => ?_
    rw [sum_sq_eq_firstEigenLambdaPoint hV hp hrig f hf x₀]
  · obtain ⟨f, hf⟩ := exists_isEigenbasis hV hp hrig
    rw [← sum_sq_eq_firstEigenLambdaPoint hV hp hrig f hf x₀]
    exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)

/-- Every orthonormal eigenbasis attains the supremum defining `Λ`. -/
theorem eigenLambda_eq_sum {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hrig : CutCur.RigidCurvature V)
    (f : Fin (CutCur.firstEigenDim V) → CutCur.Rd d → ℝ) (hf : CutCur.IsEigenbasis V f)
    (x₀ : CutCur.Rd d) : CutCur.eigenLambda V x₀ = ENNReal.ofReal (∑ i, f i x₀ ^ 2) := by
  rw [eigenLambda_eq hV hp hrig, sum_sq_eq_firstEigenLambdaPoint hV hp hrig f hf x₀]

end CutoffRigidity.Paper
