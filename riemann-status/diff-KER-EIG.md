# diff-KER-EIG: pointwise PDE from weak equation, and eigenfunction identity in L2

Status: DONE. `lake build CutoffRigidity.Riemann.DiffEigen` succeeds; no sorry/axiom/native_decide;
`#print axioms` of every declaration below = `[propext, Classical.choice, Quot.sound]`.
Namespace `CutoffRigidity.Riemann.Diff`. Standing setting as in DiffInstance2 (`hV : MSmooth F V`, `[IsFiniteMeasure μ]`, `hμ : IsWeightedVolume F μ V`).
Only new files; nothing existing edited.

| file | lines |
|---|---|
| `DiffEig1.lean` | 273 |
| `DiffEig2.lean` | 326 |
| `DiffEigen.lean` | 10 (imports both) |

## DiffEig1
* `inner_testToL2_right (u) (h : testSub F M) : ⟪u, testToL2 F μ h⟫ = ∫ u * h dμ`.
* `E_testFun_eq (hu : u ∈ (diffT F hV hμ).Q) (f : testSub F M) : (diffT ..).E u (testToL2 F μ f) = -∫ x, u x * mgenerator F V f x ∂μ`.
* `green_test (hū : MSmooth F ū) (f : testSub F M) : ∫ ū * 𝓛f dμ = ∫ f * 𝓛ū dμ` (ū need not be compactly supported; proof by Gaffney cutoffs + dominated convergence from `weightedIBP_of_isWeightedVolume`).
* `not_pos_of_integral_test`, `fundamental_lemma [μ.IsOpenPosMeasure] (hh : Continuous h) (hz : ∀ f : testSub F M, ∫ h * f dμ = 0) (x) : h x = 0`.
* **`pointwise_of_weak {lam} {uL gL : M →₂[μ] ℝ} {ū g' : M → ℝ} (hū : MSmooth F ū) (hg' : MSmooth F g') (huū : uL =ᵐ ū) (hgg' : gL =ᵐ g') (hu : uL ∈ (diffT F hV hμ).Q) (hweak : ∀ φ ∈ (diffT ..).Q, E uL φ + lam * ⟪uL, φ⟫ = ⟪gL, φ⟫) : ∀ x, lam * ū x - mgenerator F V ū x = g' x`.**
  (Deviation: `ḡ` renamed `g'`, the combining macron is not an identifier character.)

## DiffEig2
* Generic: `DirFriedrichs.E_sq_le : E u v ^ 2 ≤ E u u * E v v` (Cauchy-Schwarz on `Q`); `DirFriedrichs.E_eq_of_dense : u ∈ Q → (∀ g : S.D, E u g = c ⟪u,g⟫) → ∀ φ ∈ Q, E u φ = c ⟪u,φ⟫`.
* `caccioppoli'`: Caccioppoli for an eigenfunction with eigenvalue of any sign (bound `2(|ρ|+2)‖f‖²`), copy of `CutCur.caccioppoli` without `0 ≤ ρ`.
* `mem_Q_of_eigen (hū : MSmooth F ū) (hu2 : MemLp ū 2 μ) (hL : ∀ x, 𝓛ū x = -c ū x) : hu2.toLp ū ∈ (diffT F hV hμ).Q` (Gaffney, `closed_of_bounded`).
* `weak_eigen_of_smooth` (same hypotheses): `∀ φ ∈ Q, E (toLp ū) φ = c ⟪toLp ū, φ⟫`.
* **`eigen_semigroup {c : ℝ} {u : M → ℝ} (hū : MSmooth F u) (hu2 : MemLp u 2 μ) (hL : ∀ x, mgenerator F V u x = -c * u x) : ∃ uL : M →₂[μ] ℝ, (uL : M → ℝ) =ᵐ[μ] u ∧ ∀ t : ℝ≥0, (diffFR F hV hμ).semigroup t uL = Real.exp (-c * t) • uL`.**
  If `c < 0` the weak equation with `φ = uL` forces `uL = 0` (so no continuity/full-support argument is needed); if `c ≥ 0` use `R_eigen_of_weak` and `semigroup_eigen`.
