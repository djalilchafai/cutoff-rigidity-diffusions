module

public import CutoffRigidity.Statements
public import CutoffRigidity.Paper.CoreBridge
public import CutoffRigidity.Paper.ConvexInteraction
public import CutoffRigidity.ConvexInteractionCurvature
public import CutoffRigidity.ConvexInteractionTheorem

/-! # Dyson--OU potential on the Weyl chamber: static facts (manuscript L315-335)

`V(x) = (ρ/2)|x|² + W(x)`, `W(x) = ∑_{i<j} h(x_i - x_j)`, `h(t) = -β log t` for `t > 0` and `+∞` otherwise.
The convention `+∞` outside the open convex chamber `{x_1 > ... > x_d}` is encoded by restricting the
Lebesgue measure to the chamber: `dysonMeasure = e^{-V} dx` on the chamber and `0` outside.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace CutoffRigidity.Dyson

variable {d : ℕ}

/-- The open convex Weyl chamber `{x : x_1 > x_2 > ... > x_d}`. -/
def chamber (d : ℕ) : Set (CutCur.Rd d) := {x | ∀ i j : Fin d, i < j → x j < x i}

/-- Dyson--OU potential `V(x) = (ρ/2)|x|² - β ∑_{i<j} log(x_i - x_j)`; the value off the chamber
is irrelevant (the true `V` is `+∞` there), only values on `chamber d` are used. -/
noncomputable def dysonV (d : ℕ) (ρ β : ℝ) (x : CutCur.Rd d) : ℝ :=
  ρ / 2 * ‖x‖ ^ 2 + ∑ i, ∑ j with i < j, (-β * Real.log (x i - x j))

/-- The interaction `W(x) = ∑_{i<j} h(x_i - x_j)` with `h = -β log` (on the chamber). -/
noncomputable def dysonW (d : ℕ) (β : ℝ) (x : CutCur.Rd d) : ℝ :=
  ∑ i, ∑ j with i < j, (-β * Real.log (x i - x j))

theorem dysonV_eq (ρ β : ℝ) (x : CutCur.Rd d) : dysonV d ρ β x = ρ / 2 * ‖x‖ ^ 2 + dysonW d β x := rfl

/-- The (unnormalised) Dyson--OU Gibbs measure `e^{-V(x)} 1_{chamber} dx`. -/
noncomputable def dysonMeasure (d : ℕ) (ρ β : ℝ) : Measure (CutCur.Rd d) :=
  (volume.restrict (chamber d)).withDensity fun x => ENNReal.ofReal (Real.exp (-dysonV d ρ β x))

theorem isOpen_chamber : IsOpen (chamber d) := by
  have : chamber d = ⋂ i : Fin d, ⋂ j : Fin d, ⋂ (_ : i < j), {x : CutCur.Rd d | x j < x i} := by
    ext x; simp [chamber]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_lt (by fun_prop) (by fun_prop)

theorem convex_chamber : Convex ℝ (chamber d) := by
  intro x hx y hy a b ha hb hab i j hij
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have h1 := hx i j hij
  have h2 := hy i j hij
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this; simpa using h2
  · nlinarith [mul_pos ha' (sub_pos.2 h1), mul_nonneg hb (sub_pos.2 h2).le]

theorem nonempty_chamber : (chamber d).Nonempty := by
  refine ⟨WithLp.toLp 2 fun i : Fin d => -(i : ℝ), fun i j hij => ?_⟩
  simp only
  have : (i : ℝ) < j := by exact_mod_cast hij
  linarith


/-- `x ↦ -β log (x_i - x_j)` is convex on the chamber (for `β ≥ 0`, `i < j`). -/
theorem convexOn_neg_log_pair {β : ℝ} (hβ : 0 ≤ β) (i j : Fin d) (hij : i < j) :
    ConvexOn ℝ (chamber d) fun x : CutCur.Rd d => -β * Real.log (x i - x j) := by
  let L : CutCur.Rd d →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i -
        LinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).comp
        (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap
  have h0 : ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun t => -β * Real.log t := by
    have := (strictConcaveOn_log_Ioi.concaveOn.smul hβ).neg
    convert this using 1
    ext t; simp
  have h1 := h0.comp_linearMap L
  refine h1.subset ?_ convex_chamber
  intro x hx
  have := hx j i
  have h2 := hx i j hij
  simp only [Set.mem_preimage, Set.mem_Ioi, L, LinearMap.comp_apply, LinearMap.sub_apply]
  simp [LinearMap.proj_apply]
  linarith


theorem convexOn_dysonW {β : ℝ} (hβ : 0 ≤ β) : ConvexOn ℝ (chamber d) (dysonW d β) := by
  classical
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → CutCur.Rd d → ℝ),
      (∀ i ∈ s, ConvexOn ℝ (chamber d) (f i)) →
      ConvexOn ℝ (chamber d) (fun x => ∑ i ∈ s, f i x) := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) convex_chamber
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))
  unfold dysonW
  refine hsum _ _ fun i _ => hsum _ _ fun j hj => ?_
  exact convexOn_neg_log_pair hβ i j (by simpa using hj)

/-- `ρ`-convexity of `V` on the chamber: `V - (ρ/2)|x|²` is convex there. -/
theorem dysonV_rho_convex {β : ℝ} (hβ : 0 ≤ β) (ρ : ℝ) :
    ConvexOn ℝ (chamber d) fun x => dysonV d ρ β x - ρ / 2 * ‖x‖ ^ 2 := by
  simpa [dysonV_eq] using convexOn_dysonW (d := d) hβ

theorem dysonW_translation (β : ℝ) (x : CutCur.Rd d) (u : ℝ) :
    dysonW d β (x + u • CutCur.diagonal d) = dysonW d β x := by
  unfold dysonW
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [CutCur.diagonal]

theorem differentiableAt_dysonW {β : ℝ} {x : CutCur.Rd d} (hx : x ∈ chamber d) :
    DifferentiableAt ℝ (dysonW d β) x := by
  unfold dysonW
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j hj => ?_
  have hij : i < j := by simpa using hj
  have hpos : x i - x j ≠ 0 := (sub_pos.2 (hx i j hij)).ne'
  have hd : DifferentiableAt ℝ (fun y : CutCur.Rd d => y i - y j) x := by fun_prop
  exact (hd.log hpos).const_mul _

/-- **Eigenfunction identity (pointwise).** On the chamber, `L (∑ x_i) = -ρ ∑ x_i` for
`L = Δ - ∇V·∇`: the singular terms `∑_{j≠i} 1/(x_i - x_j)` cancel by antisymmetry (here via
translation invariance of `W` along `(1,...,1)`). -/
theorem dyson_generator_sum (ρ β : ℝ) {x : CutCur.Rd d} (hx : x ∈ chamber d) :
    CutCur.generator (dysonV d ρ β) (fun y => ∑ i, y i) x = -ρ * ∑ i, x i := by
  have hsum : ContDiff ℝ 2 (CutoffRigidity.coordinateSum : CutCur.Rd d → ℝ) := by
    have heq : (CutoffRigidity.coordinateSum : CutCur.Rd d → ℝ) =
        innerSL ℝ (CutoffRigidity.diagonalDirection d) :=
      funext (fun x => (CutoffRigidity.inner_diagonalDirection x).symm)
    rw [heq]
    exact (innerSL ℝ (CutoffRigidity.diagonalDirection d)).contDiff
  have e1 : (fun y : CutCur.Rd d => ∑ i, y i) = CutoffRigidity.coordinateSum := rfl
  rw [e1, CutoffRigidity.Paper.generator_eq_langevinDifferentialOperator _ hsum]
  have hinv : ∀ u : ℝ, dysonW d β (x + u • CutoffRigidity.diagonalDirection d) = dysonW d β x :=
    fun u => dysonW_translation β x u
  have := CutoffRigidity.langevinDifferentialOperator_coordinateSum (ρ := ρ)
    (differentiableAt_dysonW (β := β) hx) hinv
  exact this

end CutoffRigidity.Dyson
