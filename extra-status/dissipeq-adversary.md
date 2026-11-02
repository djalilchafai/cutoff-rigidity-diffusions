# DissipEq adversary report (R3): ACCEPT

Files inspected cold: CutoffRigidity/Extra/DissipEq1..5.lean (974 lines). Scratch files (outside repo): scratchpad/adv/Ax.lean, scratchpad/adv/Wit.lean.

## Verdict: ACCEPT (no repair needed)

### (1) Mathematics of the short route: no flaw found
- `sub_le_integral_of_rdrop` (Riemann sums): H s - H t <= int I from H r <= H(r+u) + u I r, I antitone, nonneg on [s,inf). Telescoping with step delta, right-endpoint comparison I(F(i+1)) delta <= int over [F i, F(i+1)] (antitone), plus the extra delta*I s boundary term, tends to 0. Correct (the left-endpoint bound is the reverse-drop; the right-endpoint is the antitone integral lower bound; the error term delta*I(s) is what makes it work).
- `defect_lsc`: integrand J = K(klFun f) - klFun(K f) is a.e. >= 0 (Jensen, `defect_nonneg`, via convexOn_klFun, per-y integrability from `ae_integrable_kernel`). Identity H(f) - H(Kf) = int J dmu holds in the REAL setting under explicit hypotheses hk (klFun f integrable) and hi, using invariance K∘μ = μ (`integral_defect`), so no infinite-entropy issue: H(f0) finite is a hypothesis (hk0 comes from `hfin`), approximants' entropies are finite (bounded klFun on core densities `hkn`, compact support + constant). The ENNReal passage uses ofReal of integral = lintegral of ofReal (nonneg a.e.). Pointwise liminf: Fatou under K y for K(klFun f_n) -> K(klFun f0) needs f_n -> f0 K y-a.e. for mu-a.e. y (`ae_ae_kernel`, fine since K∘μ=μ), and klFun(K f_n y) -> klFun(K f0 y) via L¹-contraction giving a.e.-convergent subsequence of K f_n (`exists_subseq_ae`, joint subsequence extraction is correct). `ofReal_sub_le_liminf` handles liminf(a_n - b_n) with b_n -> b0 (epsilon argument, correct). Then Fatou in y. This is the correct statement (lsc of the DROP, not of H).
- `exists_core_fisher_approx`: c_n+g_n in L¹(mu) -> density f0, mass 1, I(q_n) <= ofReal b_n, ofReal b_n -> I(nu). This is the graph-closure statement (square-root density R in domain of the closed gradient, approximated in graph norm by compact C² functions f_n, q_n = (f_n² + eps_n)/(‖f_n‖² + eps_n)); b_n = 4/den * ‖grad f_n‖² -> 4‖D‖² = I(nu) (uses `relativeFisherInformation_eq_closed_energy`). Proof only uses ν ≪ μ and I(ν) ≠ ⊤. Note it needs Hess >= rho (via `relativeFisherInformation_regularized_compact_square_le`), which is available.
- `class_rdrop`: core-class integrated dissipation (already proved `langevin_dissipation_core`) at s=0, I(q P_r) <= I(q) for r>0 (Fisher decay with exp(-2 rho r) <= 1 and rho>0), so H(q) <= H(qP_u) + u I(q). `lawAt_zero` used. Correct.
- `reverse_drop`: combines the above; limsup bound is enough because ofReal b_n -> I(nu) (limit). No Hamilton-type gradient estimate is needed: the hidden difficulty of "H(λ) - H(λP_u) <= u I(λ)" for non-core λ is fully absorbed by the lsc of the drop plus Fisher-sense approximation. I see no gap.
- `langevin_dissipation_le`: H(mu_r) finite for all r>=0 (from `drop_ennreal` + hfin), I(mu_r) finite for r>0 (same lemma, using H drop >= r*... ), I antitone from `relativeFisherInformation_langevinKernel_antitone`, reverse drop applied at ν := mu_r with semigroup identity (comp_assoc and langevinKernel_comp). Interval-integral/lintegral conversion uses finiteness of I on Ioc s t (s>0) and ofReal_integral_eq_lintegral_ofReal. Correct. Equality = le_antisymm with existing `langevin_dissipation_ge`.
- `K` and `K'` kernel forms: time shift by `a` (hat: ν.bind(Pt u) = (ν.bind(Pt a)).bind(Pt(u-a))) and change of variables on Ioc; fine.

### (2) Lean-level fidelity and vacuity
- Final statements use `CutCur.fisherInfo V`, `klDiv` (InformationTheory), `CutCur.gibbs V`, `IsEuclideanLangevin`, `lintegral over Ioc (s:ℝ) t` with `r.toNNReal`, exactly the Challenge's `langevin_dissipation_ge_K'` / `langevin_dissipation_dirac_K` forms with `=` instead of `≤` (same hypotheses: hL, hρ>0, hHess, hfin at a<s, a<s<t; Dirac: 0<s<t). Hypotheses are NOT stronger than the existing Challenge statements and equal to the manuscript's use of eq:HI (hρ, Hess >= rho are the paper's setting).
- Normalization check (paper): generator Δ - ∇V·∇, I = 4∫|∇√h|²dμ. For OU V = rho|x|²/2 (d=1), mu_t = N(m e^{-rho t}, (1-q)/rho), q=e^{-2 rho t}: H = (1/2)[-q - log(1-q) + rho m² q]; dH/dt = -[rho q²/(1-q) + rho² m² q] = -I(mu_t) which matches the Challenge's `ou_fisher_information` value rho d e^{-4 rho t}/(1-e^{-2 rho t}) + rho² e^{-2 rho t}|x0|². So H(s)-H(t) = ∫_s^t I with factor 1: normalization correct.
- Non-vacuity: scratch theorem `witness` (scratchpad/adv/Wit.lean) instantiates the Dirac theorem for the Gaussian potential `gaussPot k rho` (any k, rho>0) with a Euclidean Langevin semigroup from `exists_euclideanLangevin`, and proves in addition that both sides are NOT trivially ⊤: H(P_s x0) ≠ ⊤ (via `klDiv_langevinKernel_ne_top`) and the lintegral ≠ ⊤. `#print axioms witness`: propext, Classical.choice, Quot.sound only. The K' theorem is the engine of the Dirac one, so it is instantiated too (Dirac, a = s/2). Dirac: H(δ|μ)=⊤ but H at positive time is finite, so no ⊤ = ⊤ degeneracy.
- ENNReal equality: both sides finite in the witness; in general both can be finite or both ⊤ only if hfin fails, which is excluded.

### (3) set_option / expose
- `set_option backward.isDefEq.respectTransparency false` appears in DissipEq5 only; it is an elaboration option already used in ~10 library files; cannot affect the kernel-checked statement; harmless.
- `@[expose] noncomputable def kavg` in a `public section` of a `module` file: only controls module visibility of the definition body; harmless. `kavg` is an auxiliary (not in a Challenge statement).
- Style warnings only (haveI linter).

### (4) Build and audit
- `lake build CutoffRigidity.Extra.DissipEq5`: success (linter warnings only).
- grep of sorry/axiom/native_decide/#print/#eval/admit in DissipEq*.lean: none.
- `#print axioms` on every declaration of the five files (21 declarations incl. `kavg`): all [propext, Classical.choice, Quot.sound].

### Minor remarks (no action required)
- DissipEq1..5 are not yet imported by CutoffRigidity.lean (expected; the lead integrates). `DissipEq5` imports Dissip4, DissipEq1, DissipEq4 (transitively Dissip2, DissipEq2/3).
- Unused-variable nothing important; `exists_subseq_ae` contains a dummy `hmeas` (harmless, can be deleted).

## Compact Challenge entry (REPLACES `langevin_dissipation_ge_K'` and `langevin_dissipation_dirac_K`)

```lean
/-- **Integrated de Bruijn identity** (eq. HI), under `Hess V ≥ ρ I`, `ρ > 0`, kernel form, `μ_r = ν.bind (Pt r)`: if `H(μ_a | μ) < ∞` for some `a < s`, then `∫_s^t I(μ_r) dr + H(μ_t) = H(μ_s)` for `s < t`. -/
theorem langevin_dissipation_eq_K' {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ) (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] {a s t : ℝ≥0}
    (hfin : InformationTheory.klDiv (ν.bind (Pt a)) (gibbs V) ≠ ⊤) (has : a < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, fisherInfo V (ν.bind (Pt r.toNNReal))) + InformationTheory.klDiv (ν.bind (Pt t)) (gibbs V) =
      InformationTheory.klDiv (ν.bind (Pt s)) (gibbs V) := by
  sorry

/-- **Integrated de Bruijn identity for a Dirac initial law** (`H(δ|μ)=∞`): for `0 < s < t`, `∫_s^t I(Pᵣ(x₀,·)) dr + H(Pₜ(x₀,·)) = H(Pₛ(x₀,·))`. -/
theorem langevin_dissipation_eq_dirac_K {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ) (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : Rd d) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, fisherInfo V (Pt r.toNNReal x₀)) + InformationTheory.klDiv (Pt t x₀) (gibbs V) =
      InformationTheory.klDiv (Pt s x₀) (gibbs V) := by
  sorry
```
Solution proofs: `exact DissipEq.langevin_dissipation_eq_K' hL hρ hHess ν hfin has hst` and `exact DissipEq.langevin_dissipation_eq_dirac_K hL hρ hHess x₀ hs hst` (statement order identical to the existing ones, and the argument lists match the Challenge variables after namespacing `CutCur`). Note both new theorems are in `CutoffRigidity.DissipEq` with `CutCur.Rd d`, `CutCur.gibbs`, `CutCur.fisherInfo`.
Dependants of the old `≤` versions (if any, e.g. in Solution/Statements/comparator.json/formalization.yaml) must be renamed; the `≤` consequences follow from `le_of_eq`/`.ge`. Also the docstring "equality is not claimed" in the Challenge should be dropped. Net saving: about 0 lines (two statements replaced by two), the docstring of the first gets shorter by one line.
