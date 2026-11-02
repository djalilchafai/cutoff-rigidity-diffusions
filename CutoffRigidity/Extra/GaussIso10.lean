module

public import CutoffRigidity.Extra.GaussIso9

/-! # Tensorisation (stage 5b): Bobkov's inequality for the Gaussian on `Fin n → ℝ` -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

lemma sqrt_add_sum_sq_le {ι : Type*} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (b : ι → ℝ) :
    Real.sqrt (a ^ 2 + ∑ i, b i ^ 2) ≤ a + ∑ i, |b i| := by
  apply Real.sqrt_le_iff.2
  have hS : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨by positivity, ?_⟩
  have h1 : ∑ i, b i ^ 2 ≤ (∑ i, |b i|) ^ 2 := by
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |b i|)
      (fun i _ => abs_nonneg _)
    simpa [sq_abs] using this
  nlinarith [mul_nonneg ha hS]

lemma continuous_gI_comp {α : Type*} [TopologicalSpace α] {h : α → ℝ} (hc : Continuous h)
    (hr : ∀ x, 0 ≤ h x ∧ h x ≤ 1) : Continuous fun x => gI (h x) :=
  continuousOn_gI.comp_continuous hc fun x => hr x

/-- The integrand of Bobkov's inequality on `ℝⁿ`. -/
noncomputable def Ntot {n : ℕ} (f : (Fin n → ℝ) → ℝ) (d : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (gI (f x) ^ 2 + ∑ i, d i x ^ 2)

lemma PC.continuous_Ntot {n : ℕ} {f : (Fin n → ℝ) → ℝ} {d : Fin n → (Fin n → ℝ) → ℝ} (P : PC n f d) :
    Continuous (Ntot f d) := by
  unfold Ntot
  have := continuous_gI_comp P.cont P.rng
  have h2 : Continuous fun x => ∑ i, d i x ^ 2 := continuous_finsetSum _ fun i _ => (P.dcont i).pow 2
  exact Real.continuous_sqrt.comp ((this.pow 2).add h2)

lemma PC.bdd_Ntot {n : ℕ} {f : (Fin n → ℝ) → ℝ} {d : Fin n → (Fin n → ℝ) → ℝ} (P : PC n f d) :
    ∃ C, ∀ x, |Ntot f d x| ≤ C := by
  choose C hC using P.dbdd
  refine ⟨gφ 0 + ∑ i, C i, fun x => ?_⟩
  unfold Ntot
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  refine (sqrt_add_sum_sq_le _ (gI_nonneg _) _).trans ?_
  exact add_le_add (gI_le _) (Finset.sum_le_sum fun i _ => hC i x)

lemma PC.integrable_Ntot {n : ℕ} {f : (Fin n → ℝ) → ℝ} {d : Fin n → (Fin n → ℝ) → ℝ} (P : PC n f d) :
    Integrable (Ntot f d) (γn n) := by
  obtain ⟨C, hC⟩ := P.bdd_Ntot
  exact Integrable.mono' (integrable_const C) P.continuous_Ntot.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hC x)

/-- Marginal integrals of bounded continuous functions are continuous. -/
lemma continuous_marg_int {n : ℕ} {G : (Fin (n + 1) → ℝ) → ℝ} (hG : Continuous G) {C : ℝ}
    (hb : ∀ x, |G x| ≤ C) : Continuous fun x' : Fin n → ℝ => ∫ t, G (Fin.cons t x') ∂γ1 := by
  have c1 : ∀ x', Continuous fun t : ℝ => (Fin.cons t x' : Fin (n + 1) → ℝ) := fun x' => by
    refine continuous_pi fun i => ?_
    induction i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; exact continuous_id
    | succ j => simp only [Fin.cons_succ]; exact continuous_const
  have c2 : ∀ t : ℝ, Continuous fun x' : Fin n → ℝ => (Fin.cons t x' : Fin (n + 1) → ℝ) := fun t => by
    refine continuous_pi fun i => ?_
    induction i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; exact continuous_const
    | succ j => simp only [Fin.cons_succ]; exact continuous_apply j
  refine continuous_of_dominated (bound := fun _ => C) (fun x' => ?_) (fun x' => ?_) (integrable_const C) ?_
  · exact (hG.comp (c1 x')).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by simpa using hb _
  · exact Eventually.of_forall fun t => hG.comp (c2 t)


section step
variable {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} {d : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ}
  (P : PC (n + 1) f d)
include P

/-- Pointwise (in `x'`) tensorisation step: Bobkov in the first variable + Minkowski. -/
lemma PC.step_pointwise (x' : Fin n → ℝ) :
    Ntot (marg f) (margd d) x' ≤ ∫ t, Ntot f d (Fin.cons t x') ∂γ1 := by
  set F : ℝ → ℝ := fun t => f (Fin.cons t x') with hF
  set D0 : ℝ → ℝ := fun t => d 0 (Fin.cons t x') with hD0
  set W : Fin n → ℝ → ℝ := fun j t => d j.succ (Fin.cons t x') with hW
  have hFbc : BC F := PC.slice_bc P x'
  have hD0bc : BC D0 := PC.slice_bc0 P x'
  have h1d := bobkov_C1 (PC.slice_deriv0 P x') hFbc hD0bc (fun t => P.rng _)
  set u : ℝ → ℝ := fun t => Real.sqrt (gI (F t) ^ 2 + D0 t ^ 2) with hu
  have hcons := PC.cons_cont P x'
  have huc : Continuous u := by
    have := continuous_gI_comp (P.cont.comp hcons) (fun t => P.rng _)
    exact Real.continuous_sqrt.comp ((this.pow 2).add (hD0bc.cont.pow 2))
  have hub : ∃ C, ∀ t, |u t| ≤ C := by
    obtain ⟨C, hC⟩ := hD0bc.bdd
    refine ⟨gφ 0 + C, fun t => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have := sqrt_add_sum_sq_le (ι := Unit) (gI (F t)) (gI_nonneg _) (fun _ => D0 t)
    simp only [Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul] at this
    exact this.trans (add_le_add (gI_le _) (hC t))
  have hui : Integrable u γ1 := by
    obtain ⟨C, hC⟩ := hub
    exact Integrable.mono' (integrable_const C) huc.aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa using hC t)
  have hWbc : ∀ j, BC (W j) := fun j => by
    obtain ⟨C, hC⟩ := P.dbdd j.succ
    exact ⟨(P.dcont j.succ).comp hcons, C, fun t => hC _⟩
  let v : Fin (n + 1) → ℝ → ℝ := fun i => Fin.cases u (fun j => W j) i
  have hv : ∀ i, Integrable (v i) γ1 := by
    intro i
    induction i using Fin.cases with
    | zero => simpa [v] using hui
    | succ j => simpa [v] using (hWbc j).integrable_g
  have hsq : ∀ t, ∑ i, v i t ^ 2 = u t ^ 2 + ∑ j, W j t ^ 2 := by
    intro t
    rw [Fin.sum_univ_succ]
    simp [v]
  have hu2 : ∀ t, u t ^ 2 = gI (F t) ^ 2 + D0 t ^ 2 := fun t =>
    Real.sq_sqrt (by positivity)
  have hNt : ∀ t, Ntot f d (Fin.cons t x') = Real.sqrt (∑ i, v i t ^ 2) := by
    intro t
    unfold Ntot
    rw [hsq, hu2, Fin.sum_univ_succ]
    congr 1
    show _ = gI (F t) ^ 2 + D0 t ^ 2 + ∑ j, W j t ^ 2
    ring
  have hS : Integrable (fun t => Real.sqrt (∑ i, v i t ^ 2)) γ1 := by
    obtain ⟨C, hC⟩ := P.bdd_Ntot
    have e : (fun t => Real.sqrt (∑ i, v i t ^ 2)) = fun t => Ntot f d (Fin.cons t x') :=
      funext fun t => (hNt t).symm
    rw [e]
    refine Integrable.mono' (integrable_const C)
      (P.continuous_Ntot.comp hcons).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    simpa using hC (Fin.cons t x')
  have hmink := minkowski (ν := γ1) v hv hS
  have hint0 : ∫ t, v 0 t ∂γ1 = ∫ t, u t ∂γ1 := rfl
  have hlhs : ∑ i, (∫ t, v i t ∂γ1) ^ 2 = (∫ t, u t ∂γ1) ^ 2 + ∑ j, (margd d j x') ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp [v, margd]
    rfl
  have hmain : Ntot (marg f) (margd d) x' ≤ Real.sqrt (∑ i, (∫ t, v i t ∂γ1) ^ 2) := by
    rw [hlhs]
    unfold Ntot
    apply Real.sqrt_le_sqrt
    have hge : gI (marg f x') ≤ ∫ t, u t ∂γ1 := h1d
    have := gI_nonneg (marg f x')
    nlinarith
  refine hmain.trans (hmink.trans (le_of_eq ?_))
  congr 1
  funext t
  rw [hNt]

end step

/-- **Bobkov's inequality for the standard Gaussian on `ℝⁿ`** (coordinate-wise `C¹` form). -/
theorem bobkov_pc : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ) (d : Fin n → (Fin n → ℝ) → ℝ), PC n f d →
    gI (∫ x, f x ∂γn n) ≤ ∫ x, Ntot f d x ∂γn n := by
  intro n
  induction n with
  | zero =>
    intro f d P
    have h0 : γn 0 = Measure.dirac (fun i => isEmptyElim i) := Measure.pi_of_empty _
    rw [h0, integral_dirac, integral_dirac]
    simp [Ntot, Real.sqrt_sq (gI_nonneg _)]
  | succ n ih =>
    intro f d P
    have hg := PC.marginal P
    have ih' := ih _ _ hg
    have hfi : Integrable f (γn (n + 1)) := by
      exact Integrable.mono' (integrable_const 1) P.cont.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          have := P.rng x; rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
    have hA : ∫ x, f x ∂γn (n + 1) = ∫ x', marg f x' ∂γn n := integral_γn_succ hfi
    have hNi : Integrable (Ntot f d) (γn (n + 1)) := P.integrable_Ntot
    have hB : ∫ x, Ntot f d x ∂γn (n + 1) = ∫ x', ∫ t, Ntot f d (Fin.cons t x') ∂γ1 ∂γn n :=
      integral_γn_succ hNi
    rw [hA, hB]
    refine ih'.trans ?_
    refine integral_mono hg.integrable_Ntot ?_ (fun x' => PC.step_pointwise P x')
    obtain ⟨C, hC⟩ := P.bdd_Ntot
    have hcont := continuous_marg_int P.continuous_Ntot hC
    exact Integrable.mono' (integrable_const C) hcont.aestronglyMeasurable (Eventually.of_forall fun x' => by
      have := norm_integral_le_of_norm_le_const (μ := γ1) (f := fun t => Ntot f d (Fin.cons t x')) (C := C)
        (Eventually.of_forall fun t => by simpa using hC _)
      simpa using this)

end CutoffRigidity.GaussIso
