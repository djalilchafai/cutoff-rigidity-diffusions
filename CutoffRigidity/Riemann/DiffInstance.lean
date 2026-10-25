module

public import CutoffRigidity.Riemann.DiffChart6
public import CutoffRigidity.Riemann.DiffFrBridge

/-! # Instantiation of the DIR results with the Friedrichs construction of FR (workstream DIR)

`diffFR F hV hμ : FormData (M →₂[μ] ℝ)` is FR's `FormData` of `A = -𝓛` on `C_c^∞(M) ⊂ L²(μ)`
(same data as `diffFormData`).  We obtain, for the actual Friedrichs resolvent `R_λ = (diffFR).resolvent λ`
and semigroup `T_t = (diffFR).semigroup t`:

* `diff_resolvent_nonneg`, `diff_resolvent_le_one`: Beurling-Deny (positivity, `λ R_λ 1 = 1` sub-Markov);
* `diff_semigroup_nonneg`, `diff_semigroup_le_one`: `T_t` preserves `0 ≤ u` and `u ≤ 1`;
* `diff_oneL2_mem_Q`: `1 ∈ Q`, `E(1,1) = 0`; `diff_semigroup_one : T_t 1 = 1`;
* `diff_resolvent_smooth`: smoothness of `R_λ g` for smooth `g` (given REGn's regularity).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Instance

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- FR's `FormData` of `A = -𝓛` on `C_c^∞(M) ⊂ L²(μ)`. -/
noncomputable def diffFR : FormData (M →₂[μ] ℝ) where
  D := (diffFormData F hV hμ).D
  dense := (diffFormData F hV hμ).dense
  A := (diffFormData F hV hμ).A
  symm := (diffFormData F hV hμ).symm
  nonneg := (diffFormData F hV hμ).nonneg

theorem diffFR_toDir : (diffFR F hV hμ).toDir = diffFormData F hV hμ := rfl

/-- The Friedrichs form of `-𝓛`, as a `DirFriedrichs` for `diffFormData`. -/
noncomputable def diffT : DirFriedrichs (diffFormData F hV hμ) :=
  (diffFR F hV hμ).toDirFriedrichs

theorem diff_dirResolvent {lam : ℝ} (hlam : 0 < lam) :
    DirResolvent (diffT F hV hμ) lam ((diffFR F hV hμ).resolvent lam) :=
  (diffFR F hV hμ).toDirResolvent hlam

/-- **Beurling-Deny**: the Friedrichs resolvent of `-𝓛` preserves positivity. -/
theorem diff_resolvent_nonneg {lam : ℝ} (hlam : 0 < lam) (g : M →₂[μ] ℝ) (hg : 0 ≤ᵐ[μ] g) :
    0 ≤ᵐ[μ] (diffFR F hV hμ).resolvent lam g :=
  resolvent_nonneg F hV hμ (diffT F hV hμ) hlam (diff_dirResolvent F hV hμ hlam) g hg

/-- **Sub-Markov**: `g ≤ 1` implies `λ R_λ g ≤ 1`. -/
theorem diff_resolvent_le_one {lam : ℝ} (hlam : 0 < lam) (g : M →₂[μ] ℝ)
    (hg : g ≤ᵐ[μ] fun _ => (1 : ℝ)) :
    ∀ᵐ x ∂μ, lam * ((diffFR F hV hμ).resolvent lam g) x ≤ 1 :=
  resolvent_le_one F hV hμ (diffT F hV hμ) hlam (diff_dirResolvent F hV hμ hlam) g hg

theorem diff_oneL2_mem_Q : oneL2 μ ∈ (diffFR F hV hμ).Q := by
  have := (one_mem_Q F hV hμ (diffT F hV hμ)).1
  exact this

theorem diff_resolvent_one {lam : ℝ} (hlam : 0 < lam) :
    (diffFR F hV hμ).resolvent lam (oneL2 μ) = lam⁻¹ • oneL2 μ :=
  resolvent_one F hV hμ (diffT F hV hμ) hlam (diff_dirResolvent F hV hμ hlam)

/-- The semigroup preserves nonnegativity. -/
theorem diff_semigroup_nonneg (t : ℝ≥0) (u : M →₂[μ] ℝ) (hu : 0 ≤ᵐ[μ] u) :
    0 ≤ᵐ[μ] (diffFR F hV hμ).semigroup t u := by
  have hC : IsClosed (Set.Ici (0 : M →₂[μ] ℝ)) := isClosed_Ici
  have := (diffFR F hV hμ).semigroup_mapsTo (Set.Ici 0) hC (fun lam hlam x hx => by
    have hx' : 0 ≤ᵐ[μ] x := (Lp.coeFn_nonneg x).2 hx
    have h1 := diff_resolvent_nonneg F hV hμ hlam x hx'
    have h2 : 0 ≤ᵐ[μ] (lam • (diffFR F hV hμ).resolvent lam) x := by
      filter_upwards [h1, Lp.coeFn_smul lam ((diffFR F hV hμ).resolvent lam x)] with y hy hy2
      simp only [smul_apply] at hy2 ⊢
      rw [hy2, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hlam.le hy
    exact (Lp.coeFn_nonneg _).1 h2) t ((Lp.coeFn_nonneg u).1 hu)
  exact (Lp.coeFn_nonneg _).2 this

/-- The semigroup preserves `u ≤ 1`. -/
theorem diff_semigroup_le_one (t : ℝ≥0) (u : M →₂[μ] ℝ) (hu : u ≤ᵐ[μ] fun _ => (1 : ℝ)) :
    (diffFR F hV hμ).semigroup t u ≤ᵐ[μ] fun _ => (1 : ℝ) := by
  have hC : IsClosed (Set.Iic (oneL2 μ : M →₂[μ] ℝ)) := isClosed_Iic
  have hle : ∀ v : M →₂[μ] ℝ, v ≤ oneL2 μ ↔ v ≤ᵐ[μ] fun _ => (1 : ℝ) := fun v => by
    rw [← Lp.coeFn_le]
    exact ⟨fun h => h.trans (coeFn_oneL2 μ).le, fun h => h.trans (coeFn_oneL2 μ).symm.le⟩
  have := (diffFR F hV hμ).semigroup_mapsTo (Set.Iic (oneL2 μ)) hC (fun lam hlam x hx => by
    have hx' : x ≤ᵐ[μ] fun _ => (1 : ℝ) := (hle x).1 hx
    have h1 := diff_resolvent_le_one F hV hμ hlam x hx'
    refine (hle _).2 ?_
    filter_upwards [h1, Lp.coeFn_smul lam ((diffFR F hV hμ).resolvent lam x)] with y hy hy2
    simp only [smul_apply] at hy2 ⊢
    rw [hy2, Pi.smul_apply, smul_eq_mul]
    exact hy) t ((hle u).2 hu)
  exact (hle _).1 this

/-- Conservativity: `T_t 1 = 1`. -/
theorem diff_semigroup_one (t : ℝ≥0) : (diffFR F hV hμ).semigroup t (oneL2 μ) = oneL2 μ := by
  have h := diff_resolvent_one F hV hμ one_pos
  rw [inv_one, one_smul] at h
  have h2 := (diffFR F hV hμ).semigroup_eigen (c := 0) le_rfl (u := oneL2 μ) (by
    rw [← (diffFR F hV hμ).resolvent_one, h]; simp) t
  simpa using h2

/-- **Smoothness of the Friedrichs resolvent on smooth functions**, given interior elliptic
regularity in `F` (workstream REGn): `R_λ g` has a smooth representative if `g` has one. -/
theorem diff_resolvent_smooth (REG : EllipticRegularityRn F) {lam : ℝ} (hlam : 0 < lam)
    (g : M →₂[μ] ℝ) (g' : M → ℝ) (hg' : MSmooth F g') (hgg' : (g : M → ℝ) =ᵐ[μ] g') :
    ∃ ū : M → ℝ, MSmooth F ū ∧ ((diffFR F hV hμ).resolvent lam g : M → ℝ) =ᵐ[μ] ū := by
  have hR := diff_dirResolvent F hV hμ hlam
  exact Q_smooth_of_weak_eq F hV hμ (diffT F hV hμ) REG (hR.mem g) g g' hg' hgg'
    (hR.weak g)

theorem inner_oneL2 (u : M →₂[μ] ℝ) : inner ℝ u (oneL2 μ) = ∫ x, (u : M → ℝ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_oneL2 μ] with x hx
  rw [hx]; simp

/-- Invariance of `μ`: `∫ T_t u dμ = ∫ u dμ`. -/
theorem diff_semigroup_integral (t : ℝ≥0) (u : M →₂[μ] ℝ) :
    ∫ x, ((diffFR F hV hμ).semigroup t u : M → ℝ) x ∂μ = ∫ x, (u : M → ℝ) x ∂μ := by
  have hT := (diffFR F hV hμ).semigroup_isSelfAdjoint t
  have h : inner ℝ ((diffFR F hV hμ).semigroup t u) (oneL2 μ) =
      inner ℝ u ((diffFR F hV hμ).semigroup t (oneL2 μ)) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT u (oneL2 μ)
  rw [← inner_oneL2, ← inner_oneL2, h, diff_semigroup_one]

end Instance

end CutoffRigidity.Riemann.Diff
