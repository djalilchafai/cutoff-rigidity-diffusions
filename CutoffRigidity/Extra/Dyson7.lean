module

public import CutoffRigidity.Extra.Dyson6

/-! # Dyson--OU on the Weyl chamber: the static statement (manuscript L315-335)

`V(x) = (ρ/2)|x|² + ∑_{i<j} h(x_i - x_j)`, `h(t) = -β log t` for `t > 0`, `+∞` otherwise, `β ≥ 0`.
The invariant law is `e^{-V(x)} dx` on the open convex Weyl chamber `{x_1 > ⋯ > x_d}` (zero outside),
normalised to a probability measure `dysonProb d ρ β`.

NOT covered: the Dyson--OU process itself (SDE with reflection / collisions, its Markov semigroup,
its generator being the Friedrichs/Neumann extension of `Δ - ∇V·∇`), and the identification of
the spectral gap with the infimum of Rayleigh quotients over `C_c^∞` (cutoff argument); the optimal
constant is stated on the bounded Lipschitz smooth test functions, exactly as `optimalPI` in the
whole-space case.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace CutoffRigidity.Dyson

variable {d : ℕ}

/-- Optimal Poincaré constant of the Dyson--OU law: the infimum of the `C ≥ 0` with
`Var_μ f ≤ C ∫|∇f|² dμ` for all (bounded, Lipschitz, smooth) test functions `f`
(same definition as `CutCur.optimalPI` for the whole-space Gibbs measure). -/
noncomputable def optimalPIDyson (d : ℕ) (ρ β : ℝ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ f : CutCur.Rd d → ℝ, CutCur.IsTestFunction f →
    variance f (dysonProb d ρ β) ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β}

theorem optimalPIDyson_eq (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    optimalPIDyson d ρ β = ρ⁻¹ := by
  refine IsLeast.csInf_eq ⟨⟨inv_nonneg.mpr hρ.le, fun f hf => dyson_poincare hd hρ hβ hf⟩, ?_⟩
  rintro C ⟨hC0, hC⟩
  exact inv_le_of_poincare hd hρ hβ hC0 hC

/-- **Dyson--OU on the Weyl chamber: static statement.**
For `ρ > 0`, `β ≥ 0`, `d ≥ 1`, with `V(x) = ρ|x|²/2 - β ∑_{i<j} log (x_i - x_j)` on the chamber
`C = {x_1 > ⋯ > x_d}`, `μ = e^{-V} 1_C dx` and `μ̂ = μ/μ(ℝ^d)`:
1. `μ` is a finite nonzero measure and `μ̂` a probability measure;
2. `C` is open and convex and `V - ρ|x|²/2` is convex on `C`;
3. `L h = -ρ h` pointwise on `C`, for `h(x) = x_1 + ⋯ + x_d` and `L = Δ - ∇V·∇`;
4. weak Neumann form: `∫ ⟨∇h, ∇φ⟩ dμ̂ = ρ ∫ h φ dμ̂` for every test function `φ`
   (no boundary term on the walls of the chamber);
5. Poincaré inequality with constant `1/ρ` for all test functions;
6. the optimal Poincaré constant is exactly `1/ρ`, `h ∈ L²(μ̂)` is non-constant and attains equality:
   `Var_μ̂ h = (1/ρ) ∫ |∇h|² dμ̂` (the optimal Poincaré constant over bounded smooth Lipschitz test functions is `1/ρ`, with `h` extremal). -/
theorem dyson_ou_static (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    let μ := dysonMeasure d ρ β
    let μ' := dysonProb d ρ β
    let h := fun x : CutCur.Rd d => ∑ i, x i
    (IsFiniteMeasure μ ∧ 0 < μ Set.univ ∧ IsProbabilityMeasure μ') ∧
    (IsOpen (chamber d) ∧ Convex ℝ (chamber d) ∧
      ConvexOn ℝ (chamber d) fun x => dysonV d ρ β x - ρ / 2 * ‖x‖ ^ 2) ∧
    (∀ x ∈ chamber d, CutCur.generator (dysonV d ρ β) h x = -ρ * h x) ∧
    (∀ φ : CutCur.Rd d → ℝ, CutCur.IsTestFunction φ →
      ∫ x, inner ℝ (gradient h x) (gradient φ x) ∂μ' = ρ * ∫ x, h x * φ x ∂μ') ∧
    (∀ f : CutCur.Rd d → ℝ, CutCur.IsTestFunction f →
      variance f μ' ≤ ρ⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂μ') ∧
    (optimalPIDyson d ρ β = ρ⁻¹ ∧ MemLp h 2 μ' ∧ 0 < variance h μ' ∧
      variance h μ' = optimalPIDyson d ρ β * ∫ x, ‖gradient h x‖ ^ 2 ∂μ') := by
  intro μ μ' h
  have hp := isProbabilityMeasure_dysonProb hd hρ hβ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨⟨dysonMeasure_finite hρ hβ, dysonMeasure_pos ρ β nonempty_chamber, hp⟩,
    ⟨isOpen_chamber, convex_chamber, dysonV_rho_convex hβ ρ⟩,
    fun x hx => dyson_generator_sum ρ β hx,
    fun φ hφ => dyson_neumann hd hρ hβ hφ,
    fun f hf => dyson_poincare hd hρ hβ hf, ?_⟩
  have hv := hsum_variance hd hρ hβ
  refine ⟨optimalPIDyson_eq hd hρ hβ, hsum_memLp hd hρ hβ, ?_, ?_⟩
  · have : (h : CutCur.Rd d → ℝ) = hsum d := rfl
    rw [this, hv]; positivity
  · have : (h : CutCur.Rd d → ℝ) = hsum d := rfl
    have e : ∫ x, ‖gradient h x‖ ^ 2 ∂μ' = d := by
      simp only [this, gradient_hsum_sq]; simp
    rw [e, optimalPIDyson_eq hd hρ hβ, this, hv]
    field_simp

end CutoffRigidity.Dyson
