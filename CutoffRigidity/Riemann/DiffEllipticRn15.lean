module

public import CutoffRigidity.Riemann.DiffEllipticRn14

/-! # Weighted equation `-div(ϱ A ∇u) + λ ϱ u = ϱ g`: reduction to the unweighted problem
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

/-- Hypotheses on the coefficients of the weighted equation. -/
structure WCoeff (Ω : Set E) (A : ι → ι → E → ℝ) (ϱ : E → ℝ) : Prop where
  open_ : IsOpen Ω
  smooth : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω
  symm : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x
  elliptic : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ, c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i
  rho_smooth : ContDiffOn ℝ ∞ ϱ Ω
  rho_pos : ∀ x ∈ Ω, 0 < ϱ x

/-- `u` is a weak solution of `-div(ϱ A ∇u) + lam ϱ u = ϱ g` on `Ω`. -/
structure WSol (Ω : Set E) (A : ι → ι → E → ℝ) (ϱ : E → ℝ) (lam : ℝ) (u : E → ℝ)
    (u' : ι → E → ℝ) (g : E → ℝ) : Prop where
  h1 : LocH1 b Ω u u'
  g_smooth : ContDiffOn ℝ ∞ g Ω
  weak : ∀ φ, IsTest Ω φ →
    (∑ i, ∑ j, ∫ x, A i j x * u' j x * pd (b i) φ x * ϱ x) + lam * ∫ x, u x * φ x * ϱ x =
      ∫ x, g x * φ x * ϱ x

/-- The right-hand side after absorbing the weight. -/
def wRHS (ϱ : E → ℝ) (lam : ℝ) (g u : E → ℝ) : E → ℝ := fun x => ϱ x * g x - lam * (ϱ x * u x)

theorem WCoeff.weighted {Ω : Set E} {A : ι → ι → E → ℝ} {ϱ : E → ℝ} (hc : WCoeff Ω A ϱ) :
    (∀ i j, ContDiffOn ℝ ∞ (fun x => ϱ x * A i j x) Ω) ∧
    (∀ i j, ∀ x ∈ Ω, ϱ x * A i j x = ϱ x * A j i x) ∧
    (∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (ϱ x * A i j x) * ξ j * ξ i) := by
  refine ⟨fun i j => hc.rho_smooth.mul (hc.smooth i j),
    fun i j x hx => by rw [hc.symm i j x hx], ?_⟩
  intro x hx
  obtain ⟨c, hc0, hell⟩ := hc.elliptic x hx
  refine ⟨ϱ x * c, mul_pos (hc.rho_pos x hx) hc0, fun ξ => ?_⟩
  have := mul_le_mul_of_nonneg_left (hell ξ) (hc.rho_pos x hx).le
  calc ϱ x * c * ∑ i, ξ i ^ 2 = ϱ x * (c * ∑ i, ξ i ^ 2) := by ring
    _ ≤ ϱ x * ∑ i, ∑ j, A i j x * ξ j * ξ i := this
    _ = _ := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring

theorem WSol.locL2_rhs {Ω : Set E} {A : ι → ι → E → ℝ} {ϱ : E → ℝ} {lam : ℝ} {u : E → ℝ}
    {u' : ι → E → ℝ} {g : E → ℝ} (hc : WCoeff Ω A ϱ) (hs : WSol b Ω A ϱ lam u u' g) :
    LocL2 Ω (wRHS ϱ lam g u) := by
  intro K hK hKΩ
  exact ((locL2_of_continuousOn (hc.rho_smooth.continuousOn.mul hs.g_smooth.continuousOn)) K hK hKΩ).sub
    (((locL2_mul hs.h1.l2 hc.rho_smooth.continuousOn) K hK hKΩ).const_mul lam)

theorem WSol.locEq {Ω : Set E} {A : ι → ι → E → ℝ} {ϱ : E → ℝ} {lam : ℝ} {u : E → ℝ}
    {u' : ι → E → ℝ} {g : E → ℝ} (hc : WCoeff Ω A ϱ) (hs : WSol b Ω A ϱ lam u u' g) :
    LocEq b Ω (fun i j x => ϱ x * A i j x) u' (wRHS ϱ lam g u) := by
  have hΩ := hc.open_
  intro φ hφ
  have h := hs.weak φ hφ
  have I1 : Integrable (fun x => g x * φ x * ϱ x) volume := by
    have hs' := contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 (hc.rho_smooth.mul hs.g_smooth)
    refine (hs'.continuous.integrable_of_hasCompactSupport (hφ.2.1.mul_right)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    ring
  have I2 : Integrable (fun x => u x * φ x * ϱ x) volume := by
    have hψ : IsTest Ω (fun x => φ x * ϱ x) :=
      ⟨contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 hc.rho_smooth, hφ.2.1.mul_right,
        tsupport_mul_subset_left.trans hφ.2.2⟩
    refine (integrable_mul_test_loc hs.h1.l2 hψ hΩ).congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e1 : ∫ x, wRHS ϱ lam g u x * φ x =
      (∫ x, g x * φ x * ϱ x) - lam * ∫ x, u x * φ x * ϱ x := by
    rw [← integral_const_mul, ← integral_sub I1 (I2.const_mul lam)]
    congr 1; funext x; simp only [wRHS]; ring
  rw [e1]
  have e2 : ∀ i j, ∫ x, (ϱ x * A i j x) * u' j x * pd (b i) φ x =
      ∫ x, A i j x * u' j x * pd (b i) φ x * ϱ x := by
    intro i j; congr 1; funext x; ring
  simp only [e2]
  linarith

theorem WSol.rhs_regular {Ω : Set E} {A : ι → ι → E → ℝ} {ϱ : E → ℝ} {lam : ℝ} {u : E → ℝ}
    {u' : ι → E → ℝ} {g : E → ℝ} (hc : WCoeff Ω A ϱ) (hs : WSol b Ω A ϱ lam u u' g)
    (m : ℕ) (hum : LocSob b Ω (m + 1) u) : LocSob b Ω m (wRHS ϱ lam g u) := by
  have hΩ := hc.open_
  intro χ hχ
  have hs1 : ContDiff ℝ ∞ (fun x => χ x * (ϱ x * g x)) :=
    contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 (hc.rho_smooth.mul hs.g_smooth)
  have S1 := (Sob.of_smooth b m hs1 hχ.2.1.mul_right).1
  have hs2 : ContDiff ℝ ∞ (fun x => χ x * ϱ x) :=
    contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 hc.rho_smooth
  have S2 := sob_mul_of_locSob b hΩ hum hs2 hχ.2.1.mul_right
    (tsupport_mul_subset_left.trans hχ.2.2)
  have S2' := Sob.mono b (Nat.le_succ m) S2
  have S3 := (Sob.smul b lam S2').1
  have S4 := (Sob.sub b S1 S3).1
  refine Sob.congr_ae b S4 (Filter.Eventually.of_forall fun x => ?_)
  simp only [wRHS]; ring

theorem WSol.locSob_all {Ω : Set E} {A : ι → ι → E → ℝ} {ϱ : E → ℝ} {lam : ℝ} {u : E → ℝ}
    {u' : ι → E → ℝ} {g : E → ℝ} (hc : WCoeff Ω A ϱ) (hs : WSol b Ω A ϱ lam u u' g) :
    ∀ m, LocSob b Ω m u := by
  obtain ⟨h1, h2, h3⟩ := hc.weighted
  have := Diff.locSob_all b hc.open_ h1 (fun i j x hx => h2 i j x hx) h3 hs.h1 (hs.locL2_rhs b hc)
    (hs.locEq b hc) (fun m hm => hs.rhs_regular b hc m hm)
  exact fun m => (this m).mono b (Nat.le_succ m)

/-- Smooth functions are locally in every `H^m`. -/
theorem locSob_of_contDiffOn {Ω : Set E} (hΩ : IsOpen Ω) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g Ω)
    (m : ℕ) : LocSob b Ω m g := by
  intro χ hχ
  exact (Sob.of_smooth b m (contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 hg) hχ.2.1.mul_right).1

end CutoffRigidity.Riemann.Diff
