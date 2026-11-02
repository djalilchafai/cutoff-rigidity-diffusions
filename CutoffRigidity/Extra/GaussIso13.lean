module

public import CutoffRigidity.Extra.GaussIso12

/-! # Gaussian isoperimetric inequality, functional (Bobkov) form: final statement

For `μ = e^{-V} dx` with `V = ρ|x|²/2 + c` (the equality case `Hess V = ρ I` of the manuscript's `CD(ρ,∞)`),
and `f : ℝ^d → [0,1]` an `IsTestFunction`,
`I(∫ f dμ) ≤ ∫ √(I(f)² + ρ⁻¹ |∇f|²) dμ`, where `I = φ ∘ Φ⁻¹` is the Gaussian isoperimetric profile.
For `ρ = 1` this is Bobkov's inequality; applied to (approximations of) indicators it is the Gaussian
isoperimetric inequality `μ⁺(A) ≥ I(μ(A))` (Sudakov–Tsirelson, Borell). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ContDiff

namespace CutoffRigidity.GaussIso

lemma gaussianIsoProfile_eq (u : ℝ) : CutCur.gaussianIsoProfile u = gI u := by
  unfold CutCur.gaussianIsoProfile gI
  by_cases h : u ∈ Ioo (0:ℝ) 1
  · rw [if_pos ⟨h.1, h.2⟩, if_pos h]
    have hset : {x : ℝ | u ≤ cdf (gaussianReal 0 1) x} = Ici (gQ u) := by
      ext x
      simp only [mem_setOf_eq, mem_Ici]
      show u ≤ gΦ x ↔ _
      constructor
      · intro hx
        by_contra hlt
        rw [not_le] at hlt
        have := strictMono_gΦ hlt
        rw [gΦ_gQ h] at this
        linarith
      · intro hx
        have := strictMono_gΦ.monotone hx
        rwa [gΦ_gQ h] at this
    rw [hset, csInf_Ici]
    rfl
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2⟩), if_neg h]

end CutoffRigidity.GaussIso

namespace CutoffRigidity.GaussIso

open CutCur

/-- **Gaussian isoperimetric inequality, functional (Bobkov) form.**
Let `ρ > 0`, `V(x) = ρ|x|²/2 + c` with `e^{-V}dx` a probability measure (so `μ = N(0, ρ⁻¹ I_d)`), and
`f : ℝ^d → [0,1]` smooth, bounded and Lipschitz (`IsTestFunction`). Then
`I(∫ f dμ) ≤ ∫ √(I(f)² + ρ⁻¹ ‖∇f‖²) dμ`. -/
theorem gaussian_isoperimetric_functional {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {V : Rd d → ℝ}
    (hV : ∃ c : ℝ, ∀ x, V x = ρ / 2 * ‖x‖ ^ 2 + c) (hp : IsProbabilityMeasure (gibbs V))
    {f : Rd d → ℝ} (hf : IsTestFunction f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gaussianIsoProfile (∫ x, f x ∂gibbs V) ≤
      ∫ x, Real.sqrt (gaussianIsoProfile (f x) ^ 2 + ρ⁻¹ * ‖gradient f x‖ ^ 2) ∂gibbs V := by
  obtain ⟨c, hc⟩ := hV
  have hVe : V = fun x => ρ / 2 * ‖x‖ ^ 2 + c := funext hc
  subst hVe
  have hg : gibbs (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) = gaussρ d ρ :=
    gibbs_quadratic_eq_gaussρ hρ c hp
  obtain ⟨hsm, -, L, hL⟩ := hf
  rw [hg]
  simp only [gaussianIsoProfile_eq]
  exact gaussρ_bobkov hρ (hsm.of_le (by simp)) hL h01


/-- Non-vacuity: with `c = (d/2) log (2π/ρ)` the Gibbs measure of `ρ|x|²/2 + c` is a probability measure. -/
theorem gibbs_quadratic_isProb {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    IsProbabilityMeasure (gibbs fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 +
      (d : ℝ) / 2 * Real.log (2 * Real.pi / ρ)) := by
  set c : ℝ := (d : ℝ) / 2 * Real.log (2 * Real.pi / ρ) with hc
  have h0 := charFun_gibbs_quadratic (d := d) hρ c 0
  rw [charFun_zero] at h0
  have hpos : 0 < 2 * Real.pi / ρ := by positivity
  have hK : (Complex.exp (-(c : ℂ)) * (Real.pi / (((ρ / 2 : ℝ)) : ℂ)) ^ ((d : ℂ) / 2)) = 1 := by
    have e1 : (Real.pi : ℂ) / (((ρ / 2 : ℝ)) : ℂ) = ((2 * Real.pi / ρ : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e1, show ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpos.le, Real.rpow_def_of_pos hpos, hc]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
    have : -((d : ℝ) / 2 * Real.log (2 * Real.pi / ρ)) + Real.log (2 * Real.pi / ρ) * ((d : ℝ) / 2) = 0 := by ring
    rw [this]; simp
  rw [hK] at h0
  simp at h0
  have hfin : gibbs (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Set.univ ≠ ⊤ := by
    intro h
    rw [Measure.real, h] at h0
    simp at h0
  constructor
  rw [Measure.real] at h0
  have := ENNReal.ofReal_toReal hfin
  rw [← this]
  have h1 : (gibbs (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Set.univ).toReal = 1 := by exact_mod_cast h0
  rw [h1]; simp

end CutoffRigidity.GaussIso
