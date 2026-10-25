# diff-FR: generic Friedrichs resolvent and `cfc` semigroup (workstream FR)

Status: DONE (all deliverables of the brief, plus extras).  All files compile with `lake build`, no `sorry`,
no `axiom`, no `native_decide`; `#print axioms` of all main theorems = `[propext, Classical.choice, Quot.sound]`.
Namespace `CutoffRigidity.Riemann.Diff` (complexification/functional calculus in `...Diff.Cx`).
No file outside the `Diff*` files of this workstream was touched.

## Files (build order)
| file | lines | content |
|---|---|---|
| `DiffFrComplex.lean` | ~540 | complexification `Cx H`, `cx`, real functional calculus `Cx.rcfc` |
| `DiffFriedrichs.lean` | ~290 | `FormData`, energy completion `K`, `ι`, `Q`, `E`, `R`, closability |
| `DiffCfcSemigroup.lean` | ~530 | `hfun`, `cfcSemigroup`, `resolventLam`, Euler limit (Dini), eigen, invariance |
| `DiffFrDeriv.lean` | ~370 | density of `ran R`, strong continuity, derivative, Duhamel formula |
| `DiffFrPow.lean` | ~90 | smoothing `T_t = R^k B` |
| `DiffFrResolvent.lean` | ~350 | `R_λ` for all λ>0, brief's `exists_resolvent`, weak characterisation, `A_F`, semigroup API |
| `DiffFrBridge.lean` | ~190 | instance of DIR's `DirFormData/DirFriedrichs/DirResolvent` |

## Design notes / deviations from the brief (types only)
* Mathlib's `cfc` needs a *complex* C*-algebra, the brief's `H` is real.  `DiffFrComplex` builds the complexification
  `Cx H = WithLp 2 (H × H)` (`ℂ`-inner-product space, complete) and the real operator calculus
  `rcfc (f : ℝ → ℝ) (R : H →L[ℝ] H) : H →L[ℝ] H` with `cx (rcfc f R) = cfc f (cx R)`
  (the cfc lies in the closed star-subalgebra of operators commuting with conjugation: `Mathlib cfc_mem`).
* The hypotheses `IsSelfAdjoint R`, `0 ≤ R`, `R ≤ 1` are packaged as `Cx.UnitOp R` (self-adjoint, `0 ≤ ⟪Rx,x⟫ ≤ ⟪x,x⟫`), which
  is equivalent (no order instance on real operators needed).
* `FormData.Q` is `LinearMap.range ι ⊆ H` (a `Submodule`), `FormData.E : Q → Q → ℝ`, `E u v = ⟪ι⁻¹u,ι⁻¹v⟫_K - ⟪u,v⟫`;
  the sequence description required by the brief/DIR is `FormData.mem_Q_seq` and `FormData.tendsto_en` (bridge file).
* The resolvent for general λ is `resolventLam R λ = rcfc (r ↦ r/(1+(λ-1)r)) R` with `R = R_1` the completion resolvent.
* `hinj` is needed only for strong continuity at 0 / derivative statements (density of `ran R`), NOT for the Euler limit.

## Main declarations (exact statements)

### DiffFriedrichs
* `structure FormData H` : `D : Submodule ℝ H`, `dense`, `A : D →ₗ[ℝ] H`, `symm : ⟪A f, g⟫ = ⟪f, A g⟫`, `nonneg : 0 ≤ ⟪A f, f⟫`.
* `FormData.K S` (completion of `D` for `⟪f,g⟫+⟪Af,g⟫`), `S.ι : S.K →L[ℝ] H` (contraction), `ι_coe`, `norm_ι_le`,
  `ι_injective` (closability), `inner_coe_left : ⟪g,x⟫_K = ⟪g + A g, ι x⟫`.
* `S.Q : Submodule ℝ H := range ι`, `S.qEquiv : K ≃ₗ[ℝ] Q`, `S.E1 u v = ⟪ι⁻¹u,ι⁻¹v⟫`, `S.E u v = E1 u v - ⟪u,v⟫`,
  `E_emb : E f g = ⟪A f, g⟫` on `D`, `E_nonneg`, `limit_mem_Q` (closedness in energy).
* `S.R := ι ∘ ι†`, `R_isSelfAdjoint`, `R_nonneg`, `R_le_one`, `norm_R_le : ‖R‖ ≤ 1`, `R_injective`, `R_mem_Q`,
  `R_resolvent : R (f + A f) = f` (`f ∈ D`), `E1_R : E1 (R g) φ = ⟪g, φ⟫`, `E_R : E (R g) φ + ⟪R g, φ⟫ = ⟪g, φ⟫`.

### DiffFrComplex (generic, `H` real Hilbert, `UnitOp R`)
`rcfc_id/const/one/add/sub/mul/smul/pow/congr`, `norm_rcfc_le : (∀ x∈[0,1], |f x| ≤ c) → ‖rcfc f R‖ ≤ c`,
`isSelfAdjoint_rcfc`, `commute_rcfc`, `rcfc_inner_nonneg`, `UnitOp.spectrum_subset : spec(cx R) ⊆ [0,1]`.

### DiffCfcSemigroup (`hR : UnitOp R`)
* `hfun t r = if t = 0 then 1 else if 0 < r then exp(-t (1/r - 1)) else 0` (continuous: `continuous_hfun`),
  `cfcSemigroup R t := rcfc (hfun t) R`.
* `cfcSemigroup_zero : T 0 = 1`, `cfcSemigroup_add : T (s+t) = T s * T t`, `norm_cfcSemigroup_le_one`,
  `cfcSemigroup_isSelfAdjoint`, `cfcSemigroup_comm`, `cfcSemigroup_inner_nonneg`, `norm_cfcSemigroup_apply_le`.
* `resolventLam R lam := rcfc (r ↦ r/(1+(lam-1) r)) R`; `resolventLam_one : = R`, `norm_resolventLam_le : ‖R_λ‖ ≤ 1/λ`,
  `resolventLam_sub : R_a - R_b = (b-a) • (R_a * R_b)`, `resolventLam_mul : R_λ * ((λ-1) • R + 1) = R`.
* `eulerOp R t n := (((n+1)/t) • resolventLam R ((n+1)/t))^(n+1)`;
  `tendsto_eulerOp (t ≠ 0) : Tendsto (fun n => eulerOp R t n) atTop (𝓝 (cfcSemigroup R t))` (NORM convergence, Dini,
  monotonicity of `(1+x/m)^m` by Bernoulli: `pow_one_add_div_le`).
* `cfcSemigroup_mapsTo (C closed) (hres : ∀ λ>0, ∀ x∈C, (λ • R_λ) x ∈ C) : T t x ∈ C` (positivity / order-interval preservation).
* `resolventLam_apply_eigen`, `cfcSemigroup_eigen (hc : 0 ≤ c) (hu : R u = (1+c)⁻¹ • u) : T t u = exp(-c t) • u`.

### DiffFrDeriv (`hR : UnitOp R`, `hinj : Injective R`)
* `norm_cfcSemigroup_mul_sub_le : ‖T s * R - R‖ ≤ s`; `denseRange_of_injective : Dense (range R)`.
* `continuous_cfcSemigroup_apply : Continuous (fun t : ℝ≥0 => T t u)` (strong continuity on `[0,∞)`).
* `hasDerivAt_cfcSemigroup_mul (ht : 0 < t) : HasDerivAt (s ↦ T s.toNNReal * R) (-(T t.toNNReal * (1 - R))) t` (OPERATOR NORM).
* `hasDerivAt_cfcSemigroup_apply (ht : 0 < t) g : HasDerivAt (s ↦ T s.toNNReal (R g)) (-(T t.toNNReal (g - R g))) t`.
* `cfcSemigroup_integral : T t (R g) - R g = -∫ s in 0..t, T s.toNNReal (g - R g)`.
  (The right derivative at `0` is covered through the integral form + strong continuity; not stated separately.)

### DiffFrPow
* `cfcSemigroup_eq_pow_mul (t ≠ 0) k : T t = R ^ k * rcfc (psiFun t k) R` (`psiFun t k r = h_t(r) r^{-k}` continuous).

### DiffFrResolvent (`S : FormData H`)
* `S.resolvent lam := resolventLam S.R lam`, `S.semigroup t := cfcSemigroup S.R t`.
* **`FormData.exists_resolvent (hlam : 0 < lam) : ∃ R (hQ : ∀ g, R g ∈ S.Q), IsSelfAdjoint R ∧ (∀ u, 0 ≤ ⟪R u,u⟫) ∧ Injective R ∧
  (∀ f : S.D, R (lam • f + S.A f) = f) ∧ (∀ g (φ : S.Q), S.E ⟨R g, hQ g⟩ φ + lam * ⟪R g, φ⟫ = ⟪g, φ⟫) ∧ ‖R‖ ≤ 1/lam`.**
  Components: `resolvent_isSelfAdjoint`, `resolvent_inner_nonneg`, `resolvent_injective`, `resolvent_mem_Q`, `resolvent_apply_D`, `E_resolvent`,
  `norm_resolvent_le`, `resolvent_sub` (resolvent identity).
* Weak characterisation (Riesz uniqueness): `eq_R_of_weak (u ∈ Q) (∀ φ∈Q, E1 u φ = ⟪g,φ⟫) : u = R g`;
  `eq_resolvent_of_weak (λ>0) (u∈Q) (∀ φ, E u φ + λ⟪u,φ⟫ = ⟪g,φ⟫) : u = R_λ g`;
  `R_eigen_of_weak (1+c ≠ 0) (u∈Q) (∀ φ, E u φ = c ⟪u,φ⟫) : R u = (1+c)⁻¹ • u`   (use for eigenfunction identification, A7).
* Generator: `domAF = range R`, `AF : domAF →ₗ H` with `AF_R : AF (R g) = g - R g`, `D_subset_domAF`, `AF_extends : AF f = A f` for `f ∈ D`.
* Semigroup API: `semigroup_zero/add`, `norm_semigroup_le`, `semigroup_isSelfAdjoint`, `continuous_semigroup_apply`, `tendsto_euler`,
  `semigroup_eigen`, `semigroup_mapsTo`, `hasDerivAt_semigroup`, `semigroup_integral`, `semigroup_integral_D :
  T t f - f = -∫₀ᵗ T s (A f) ds` (`f ∈ D`; with `A = -𝓛` this is the Dynkin formula in `L²`), `semigroup_eq_pow_mul`, `semigroup_apply_mem_Q`.

### DiffFrBridge (for DIR; imports `DiffMarkov`)
* `FormData.toDir : DirFormData H` (same data), `mem_Q_seq : u ∈ S.Q ↔ ∃ f : ℕ → D, f → u in H ∧ EnCauchy f`,
  `tendsto_en : en (f n) (g n) → S.Eext u v`, `toDirFriedrichs : DirFriedrichs S.toDir` (Q = `S.Q`, E = `S.Eext`),
  `toDirResolvent (hlam) : DirResolvent S.toDirFriedrichs lam (S.resolvent lam)`.

## Open items / remarks
* None for the brief.  Not done (not asked): right-derivative statement at `t = 0` as a `HasDerivWithinAt` (the integral formula
  `semigroup_integral` and `continuous_semigroup_apply` give what Dynkin needs); positivity of `T_t` as an operator order statement
  is given as `cfcSemigroup_inner_nonneg` and via `semigroup_mapsTo` for cones (the caller supplies `hres` from Beurling-Deny).
* Consumers (DIR/REG/KER) need: `S := diffFormData` as a `FormData` (DIR currently builds `DirFormData`; `FormData` has the same fields, so
  `⟨D, dense, A, symm, nonneg⟩` transports), then use `S.toDirFriedrichs`/`S.semigroup`.
