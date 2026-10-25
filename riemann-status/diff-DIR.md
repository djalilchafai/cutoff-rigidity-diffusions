# diff-DIR: manifold-side form facts (workstream DIR of DIFFUSION_PLAN)

Status: DONE (all deliverables of the brief, plus the instantiation with FR and REGn).  All files compile with `lake build`,
no `sorry`, no `axiom`, no `native_decide`; `#print axioms` of all main theorems = `[propext, Classical.choice, Quot.sound]`.
Namespace `CutoffRigidity.Riemann.Diff`.  Last module (imports everything): `CutoffRigidity.Riemann.DiffInstance2`.
No file outside my own `Diff{Markov,Form,Chart,Instance}*.lean` was touched (lead: add these 15 modules to `CutoffRigidity.lean`,
or just `DiffInstance2`).

| file | lines | content |
|---|---|---|
| `DiffMarkov.lean` | 486 | generic Hilbert-space Friedrichs form theory (structures mirroring FR), closedness, Beurling-Deny argument |
| `DiffForm.lean` | 178 | `testSub`, `testToL2`, `testGen`, Green formula, normal contractions |
| `DiffForm1.lean` | 102 | density of test functions in `L²(μ)` |
| `DiffForm2.lean` | 82 | `diffFormData : DirFormData (M →₂[μ] ℝ)` |
| `DiffMarkov1.lean` | 204 | `liftLp`, `resolvent_posPreserving` (Beurling-Deny) |
| `DiffMarkov2.lean` | 213 | `one_mem_Q`, `resolvent_one`, `resolvent_le_one` |
| `DiffChart.lean` | 318 | chart coefficients `a = chartCoeff`, `ρ = chartRho`: smoothness, symmetry, ellipticity; chart formula for `Γ` and `∫Γ(u,v)dμ` |
| `DiffChart1.lean` | 155 | change of variables (`lintegral_chart`), weight `κ = ρ/(‖G‖+1)`, measure `ν = κ dz` |
| `DiffChart2.lean` | 168 | `L²(ν)` control of coordinate gradient by the energy |
| `DiffChart3.lean` | 356 | `L²(ν)`-limit of gradients of an energy-Cauchy sequence, energy pairing in a chart |
| `DiffChart4.lean` | 291 | IBP in the chart, weak gradient identity |
| `DiffChart5.lean` | 435 | `IsChartWeakGrad`, `Q_chart_weak`, `chart_weak_equation` |
| `DiffChart6.lean` | 160 | glueing: `Q_smooth_of_weak_eq` (given `EllipticRegularityRn F`) |
| `DiffInstance.lean` | 131 | instantiation with FR's `FormData`, `R_λ`, `T_t` |
| `DiffInstance2.lean` | 194 | `ellipticRegularityRn` from REGn's `weak_solution_smooth`; unconditional smoothness results |

## Interface with FR / REGn
* FR (`DiffFrBridge`): `diffFR F hV hμ : FormData (M →₂[μ] ℝ)` has the same data as `diffFormData`; `diffT := (diffFR ..).toDirFriedrichs`;
  `diff_dirResolvent : DirResolvent (diffT ..) lam ((diffFR ..).resolvent lam)`.  `Q` of `diffT` is FR's `S.Q`, `E` is FR's `S.Eext`.
* REGn: `ellipticRegularityRn F : EllipticRegularityRn F` proved from `weak_solution_smooth` with coefficients `A i j x = ⟪a x (b j), b i⟫`,
  `b = stdOrthonormalBasis`.  `EllipticRegularityRn` allows any real `lam` (REGn's theorem has no sign condition), so eigenfunctions are covered.

## Main declarations (exact statements; standing hypotheses `F` finite-dim inner product space, `M` connected complete Riemannian
manifold `[IsRiemannianManifold 𝓘(ℝ,F) M] [ConnectedSpace M] [CompleteSpace M]`, `hV : MSmooth F V`, `[IsFiniteMeasure μ]`, `hμ : IsWeightedVolume F μ V`)

### Generic (DiffMarkov)
* `structure DirFormData H` (D dense submodule, `A : D →ₗ H`, symmetric, nonneg); `structure DirFriedrichs S` (`Q`, `E`,
  `mem_Q : u ∈ Q ↔ ∃ f : ℕ → D, f → u ∧ EnCauchy f`, `E_lim`); `structure DirResolvent T lam R : Prop` (`R g ∈ Q`, `E (R g) φ + lam ⟪R g,φ⟫ = ⟪g,φ⟫`).
* `DirFriedrichs`: `Q` subspace, `E` bilinear symmetric nonneg, `E_coe`, `E_eq_zero_of_self`;
  `closed_of_bounded : (∀ n, en (w n) (w n) ≤ C) → w n → w' → w' ∈ Q ∧ E w' w' ≤ C` (lower semicontinuity, Banach-Saks via convex hulls);
  `contraction_mem` (Lipschitz `Tm` with `Tm D ⊆ D`, energy non-increasing on `D` ⟹ `Tm Q ⊆ Q`, `E(Tu) ≤ E u`);
  `fixed_of_comparison` (variational Beurling-Deny).

### Test functions and form (DiffForm*)
* `testSub F M : Submodule ℝ (M → ℝ)` smooth compactly supported; `testToL2 F μ : testSub F M →ₗ[ℝ] (M →₂[μ] ℝ)`; `testToL2_injective F hV hμ`;
  `testGen F hV` (`𝓛`); `inner_testGen : ⟪testToL2 f, -testToL2 (testGen g)⟫ = ∫ Γ(f,g) dμ`.
* `dense_test : DenseRange (testToL2 F μ)` (`[IsFiniteMeasure μ]`, no `hμ` needed).
* `diffFormData F hV hμ : DirFormData (M →₂[μ] ℝ)`; `en_diffFormData : en (toL2 a) (toL2 b) = ∫ carre a b dμ`.
* `normalContraction_stable θ (hθ : ContDiff ℝ ∞ θ) (h0 : θ 0 = 0) (h1 : ∀ s, |deriv θ s| ≤ 1) f (hf : f ∈ testSub F M) :
  θ ∘ f ∈ testSub F M ∧ ∀ x, carre F (θ ∘ f) (θ ∘ f) x ≤ carre F f f x` (and `normalContraction_stable'` with `L²`).

### Markov properties (DiffMarkov1/2, generic in `T : DirFriedrichs (diffFormData F hV hμ)`, `R`, `DirResolvent T lam R`)
* `resolvent_posPreserving`/`resolvent_nonneg : 0 < lam → 0 ≤ᵐ g → 0 ≤ᵐ R g`.
* `one_mem_Q : oneL2 μ ∈ T.Q ∧ T.E (oneL2 μ) (oneL2 μ) = 0` (Gaffney cutoffs); `E_one_left`; `resolvent_one : R 1 = lam⁻¹ • 1`;
  `resolvent_le_one : g ≤ᵐ 1 → ∀ᵐ x, lam * R g x ≤ 1`.

### Chart transfer (DiffChart*)
* `chartCoeff F x₀ z : F →L[ℝ] F` (inverse metric), `contDiffOn_chartCoeff` (`C^∞` on the chart target), `chartCoeff_symm`
  (symmetric), `exists_chartCoeff_elliptic` (pointwise `∃ c>0, c‖v‖² ≤ ⟪a v,v⟫`); `chartRho F V x₀ z = e^{-V∘φ⁻¹} √det g`,
  `contDiffOn_chartRho`, `chartRho_pos`; `carre_chart_formula : Γ(u,v)(φ⁻¹z) = ⟪∇(u∘φ⁻¹) z, a(z) ∇(v∘φ⁻¹) z⟫`;
  `integral_carre_chart`; `chart_map_eq : (μ|source).map φ = (vol|target).withDensity ρ`; `lintegral_chart`, `integral_chart_comp`.
* `structure IsChartWeakGrad F V x₀ u Du : Prop` (`ũ = u∘φ⁻¹, Du ∈ L²(ν)` and `∫ ũ ∂_wψ = -∫ ⟪Du,w⟫ ψ` for `ψ ∈ C_c^∞(target)`);
  `memLp_restrict_of_nu` (`L²(ν) ⊆ L²_loc(dz)`).
* **`Q_chart_weak (T) (hu : u ∈ T.Q) : ∃ Du, IsChartWeakGrad F V x₀ u Du ∧ ∀ b : testSub F M, tsupport b ⊆ source →
  T.E u (testToL2 b) = ∫ z in target, ρ z * ⟪∇(b∘φ⁻¹) z, a z (Du z)⟫`**.
* **`chart_weak_equation (T) (hu : u ∈ T.Q) (g) (g') (hg'm : Measurable g') (hgg' : g =ᵐ g') (hweak : ∀ φ ∈ T.Q, T.E u φ + lam ⟪u,φ⟫ = ⟪g,φ⟫) :
  ∃ Du, IsChartWeakGrad .. ∧ ∀ ψ ∈ C_c^∞(target), ∫_T (⟪a Du, ∇ψ⟫ + lam ũ ψ) ρ = ∫_T g̃ ψ ρ`** (`g̃ = g'∘φ⁻¹`; `g'` any measurable
  representative, so right-hand sides that are only `L²`/`H^m_loc` are allowed, which is what the bootstrap of REG-manifold needs).
* `EllipticRegularityRn F` (Prop, interior regularity in `F`), **`Q_smooth_of_weak_eq (REG) (hu : u ∈ T.Q) (hweak) (g' smooth) : ∃ ū, MSmooth F ū ∧ u =ᵐ ū`**.

### Instantiation (DiffInstance*)
* `diffFR`, `diffT`, `diff_dirResolvent`, `diff_resolvent_nonneg`, `diff_resolvent_le_one`, `diff_oneL2_mem_Q`, `diff_resolvent_one`,
  `diff_semigroup_nonneg`, `diff_semigroup_le_one` (`T_t` preserves `0 ≤ u` and `u ≤ 1`, via FR's `semigroup_mapsTo`),
  `diff_semigroup_one : T_t 1 = 1`, `diff_semigroup_integral : ∫ T_t u dμ = ∫ u dμ`.
* **`ellipticRegularityRn F : EllipticRegularityRn F`** (from REGn), `diff_resolvent_smooth'` (`R_λ g` has a smooth representative if `g` has one),
  **`diff_eigen_smooth`** (`u ∈ Q`, `E(u,φ) = c⟪u,φ⟫ ∀ φ ∈ Q` ⟹ smooth representative; this is the regularity needed for the attainment of the gap).

## Remarks / limits
* `diffFormData` needs the standing Riemannian hypotheses only for `dense_test` (σ-compactness/properness).  `μ` need not be a probability
  measure, only finite.
* Smoothness of `T_t u` (A5 (ii), `t > 0`) is NOT proved here: it needs iterating regularity along `D(A_F^k)` with a right-hand side that is only
  `H^m_loc`; `chart_weak_equation` is stated for arbitrary `L²` right-hand sides (arbitrary measurable representative) for that purpose, but
  REGn's final theorem `weak_solution_smooth` takes smooth `g`; for the bootstrap one would use REGn's `LocSob`-level step lemmas.
  For `R_λ g` with `g` smooth and for weak eigenfunctions (`lam = -c`, `g = 0`, the `lam·u` term is inside REGn's theorem) the chain is complete.
* Nothing in this workstream assumes closability, completeness, compactness or smoothness of the constructed objects: closability is FR's
  (`E_lim` field proved in `FormData.toDirFriedrichs`), lower semicontinuity (`closed_of_bounded`) is proved here from the sequence definition.
