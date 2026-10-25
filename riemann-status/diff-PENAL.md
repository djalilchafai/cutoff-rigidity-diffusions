# diff-PENAL: penalized resolvent, energy maximum principle, barrier, compactly supported subsolution (P1-P3 of CO_PLAN)

Status: DONE, fully checked. Last module (imports everything): `CutoffRigidity.Riemann.DiffPenalMain`.
No sorry/axiom/native_decide; `#print axioms` of every theorem below = `[propext, Classical.choice, Quot.sound]`.
Namespace `CutoffRigidity.Riemann.Diff`. Standing hypotheses as `DiffInstance` (F, M complete connected Riemannian,
`hV : MSmooth F V`, `[IsFiniteMeasure μ]`, `hμ : IsWeightedVolume F μ V`; `F` explicit). No existing file edited.
Elliptic regularity with potential is NOT a hypothesis: KER-REG delivered `Q_smooth_of_weak_eq_pot` (DiffRegPot), used directly.

| file | lines | content |
|---|---|---|
| DiffPerron0 | 83 | chain rule `mgenerator_comp_real` |
| DiffPenal | 358 | P1: penalized resolvent (contraction on `R_{lam+B}`), positivity, comparisons, energy |
| DiffPenal1 | 80 | `penalized_smooth`, `continuous_le_of_ae_le` |
| DiffPerron1 | 333 | `exists_smooth_proper`, `energy_max_principle` (+ `Gfun`, `energy_step`) |
| DiffPerronBarrier | 366 | `barrier_decay` (+ `barrier_supersolution`, `barrierProfile`) |
| DiffPerron2 | 139 | `exists_convex_cutoff_fn`, `subsolution_of_penalized` |
| DiffPenalMain | 105 | `potOK_penal`, `penalized_perron` (assembly of P1+P2+P3, the input of P4) |

Note: `DiffPerron0` imports `EigenLinear`, NOT `DiffDynkinBounded` (that module and `DiffForm2` both define `Diff.carre_comm`, so they cannot be imported together; not touched).
Naming deviation: `mgenerator_comp_real` is in `DiffPerron0` (not `DiffPerron1`) so that P2 and P3 can be built in parallel.

## P1 (DiffPenal, DiffPenal1)
* `def PotOK F κ B := MSmooth F κ ∧ ∀ x, 0 ≤ κ x ∧ κ x ≤ B`; `potMul hκ : H →L[ℝ] H` (via `boundedL2Multiplier`, bound `max B 0`),
  `potMul_coeFn : potMul hκ u =ᵐ κ * u`, `inner_potMul : ⟪potMul hκ u, φ⟫ = ∫ κ u φ dμ`.
* `structure IsPenal hV hμ lam κ g v : Prop` : `mem : v ∈ (diffT F hV hμ).Q`, `weak : ∀ φ ∈ Q, E v φ + lam * ⟪v,φ⟫ + ∫ x, κ x * v x * φ x ∂μ = ⟪g,φ⟫`
  (same form as KER's `Q_smooth_of_weak_eq_pot`; `H = M →₂[μ] ℝ`).
* `IsPenal.sub`, `IsPenal.zero`, `IsPenal.unique (hlam) (hκ) : IsPenal g v → IsPenal g v' → v = v'` (coercivity).
* `penalized_exists (hlam) (hκ : PotOK F κ B) g : ∃ v, IsPenal hV hμ lam κ g v` (fixed point of `v ↦ R_{lam+max B 0}(g + (Bp - κ) v)`, a contraction of constant `Bp/(lam+Bp)`; `penalized_exists_aux` also gives positivity).
* `penalized_nonneg : IsPenal g v → 0 ≤ᵐ g → 0 ≤ᵐ v`; `penalized_mono : IsPenal g v → IsPenal g' v' → g ≤ᵐ g' → v ≤ᵐ v'`;
  `penalized_anti (hκ hκ') (hle : ∀ x, κ x ≤ κ' x) (hg : 0 ≤ᵐ g) : IsPenal κ g v → IsPenal κ' g v' → v' ≤ᵐ v`;
  `isPenal_resolvent : IsPenal lam 0 g (R_lam g)`; `penalized_le_resolvent (hg : 0 ≤ᵐ g) : IsPenal κ g v → v ≤ᵐ R_lam g`;
  `penalized_le_const (hc : 0 ≤ c) (hg : g ≤ᵐ c) : IsPenal κ g v → v ≤ᵐ c / lam` (compares with the constant, `E(1,.)=0`);
  `penalized_energy_eq`, `penalized_energy : E v v + lam * ‖v‖^2 ≤ ⟪g, v⟫`.
* `penalized_smooth (hκ : PotOK F κ B) (hg' : MSmooth F g') (hgg' : g =ᵐ g') (h : IsPenal hV hμ lam κ g v) :
   ∃ v', MSmooth F v' ∧ v =ᵐ v' ∧ ∀ x, mgenerator F V v' x = (lam + κ x) * v' x - g' x`.
* `continuous_le_of_ae_le : f ≤ᵐ g → (∀ x, f x ≤ g x)` for continuous `f g`.

## P2
* `mgenerator_comp_real {θ} (hθ : ContDiff ℝ ∞ θ) (hf : MSmooth F f) x : mgenerator F V (θ ∘ f) x = deriv θ (f x) * mgenerator F V f x + deriv (deriv θ) (f x) * carre F f f x`.
* `exists_smooth_proper : ∃ ζ, MSmooth F ζ ∧ (∀ x, 0 ≤ ζ x) ∧ ∀ c, IsCompact {x | ζ x ≤ c}`.
* `energy_max_principle F hV hμ (hw : MSmooth F w) (hb : ∃ C, ∀ x, |w x| ≤ C) (hlam : 0 < lam) (hκ : ∀ x, 0 ≤ κ x)
   (h : ∀ x, 0 < w x → (lam + κ x) * w x ≤ mgenerator F V w x) : ∀ x, w x ≤ 0` (Gaffney cutoffs, `G(s) = exp(-1/s)`).
* `barrier_decay F hV hμ (hζ : MSmooth F ζ) (hζc : ∀ c, IsCompact {x | ζ x ≤ c}) (hlam) (Cg a : ℝ) (hε : 0 < ε) :
   ∃ K₀, ∀ K ≥ K₀, ∀ g v, MSmooth F v → (∀ x, 0 ≤ g x ∧ g x ≤ Cg) → (∀ x, g x ≠ 0 → ζ x < a) → (∀ x, 0 ≤ v x ∧ v x ≤ Cg / lam) →
   (∀ x, mgenerator F V v x = (lam + K * Real.smoothTransition (ζ x - a)) * v x - g x) → ∀ x, a + 2 ≤ ζ x → v x ≤ ε`
  (`K₀` independent of `g, v`; explicit `K₀ = s²B²G + sB(Λ+G)`, `s = max Cg 0/(lam ε)`; barrier `exp(-s S(ζ-a-1))`, `S = smoothTransition`).

## P3
* `exists_convex_cutoff_fn (hε : 0 < ε) : ∃ θ, ContDiff ℝ ∞ θ ∧ θ 0 = 0 ∧ (∀ r ≤ ε, θ r = 0) ∧ (∀ r, 0 ≤ θ' r ≤ 1) ∧ (∀ r, 0 ≤ θ'' r) ∧ (∀ r, r - 2ε ≤ θ r) ∧ (∀ r ≥ 0, θ r ≤ r θ' r)`.
* `subsolution_of_penalized F (hlam) (hv : MSmooth F v) (h0 : ∀ x, 0 ≤ v x) (hg : ∀ x, 0 ≤ g x) (hκ : ∀ x, 0 ≤ κ x)
   (hv' : ∀ x, mgenerator F V v x = (lam + κ x) * v x - g x) (hε) (hK₀ : IsCompact K₀) (hsupp : ∀ x, ε ≤ v x → x ∈ K₀) :
   ∃ f, f ∈ testSub F M ∧ (∀ y, lam * f y - mgenerator F V f y ≤ g y) ∧ (∀ y, v y - 2 * ε ≤ f y)`.

## Interface for P4 (DiffPenalMain): all conclusions proved, nothing assumed
* `potOK_penal F hζ a (hK : 0 ≤ K) : PotOK F (fun x => K * Real.smoothTransition (ζ x - a)) K`.
* `penalized_perron F hV hμ (hζ : MSmooth F ζ) (hζc : ∀ c, IsCompact {x | ζ x ≤ c}) (hlam) (hg : MSmooth F g) (hgc : HasCompactSupport g)
   (hg0 : ∀ x, 0 ≤ g x) (hga : ∀ x, g x ≠ 0 → ζ x < a) (hε : 0 < ε) :
   ∃ K₀, ∀ K, K₀ ≤ K → 0 ≤ K → ∃ (v : H) (v' : M → ℝ), IsPenal hV hμ lam (K θ₀(ζ - a)) (testToL2 F μ ⟨g,hg,hgc⟩) v ∧ MSmooth F v' ∧ v =ᵐ v' ∧
   (∀ x, 0 ≤ v' x ∧ v' x ≤ max C0 0 / lam) ∧ (∀ x, mgenerator F V v' x = (lam + K θ₀(ζ x - a)) * v' x - g x) ∧
   (∀ x, a + 2 ≤ ζ x → v' x ≤ ε/2) ∧ ∃ f ∈ testSub F M, (∀ y, lam * f y - mgenerator F V f y ≤ g y) ∧ ∀ y, v' y - 2 * ε ≤ f y`
  (`C0` = a sup bound of `|g|` from `testSub_bounded`). By `IsPenal.unique` the `v` is THE penalized resolvent `v_{a,K}`.
* For P4's limits use: `penalized_anti` (monotone in `K`), `penalized_le_resolvent`, `penalized_energy` (`E v v ≤ ⟪g,v⟫`), `IsPenal.weak` against
  `φ` with `κ φ = 0` (supp φ ⊂ {ζ < a}), `eq_resolvent_of_weak'` (Eext form of `eq_resolvent_of_weak`, DiffPenal).

## Honest remarks
* Statement adaptations: `PotOK` unchanged but the bound used is `max B 0` (so no `0 ≤ B` needed); `penalized_*` are phrased through `IsPenal` (B-free) rather than `mulL2`;
  `energy_max_principle`/`barrier_decay` carry explicit `F hV hμ`; `barrier_decay` is slightly stronger than the plan (g not assumed smooth, `K₀` uniform in `g, v`).
* The barrier uses `ε ≤ v` ⇒ `ζ < a+2` via `barrier_decay` at `ε/2` (assembly) to get a strict inclusion.
