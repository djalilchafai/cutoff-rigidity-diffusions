module

public import CutoffRigidity.Extra.Dyson2

/-! # Passage to the limit `ε → 0`: Dyson--OU chamber measure -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace CutoffRigidity.Dyson

variable {d : ℕ}

theorem norm_coord_le (x : CutCur.Rd d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  simpa using this

theorem abs_sub_coord_le (x : CutCur.Rd d) (i j : Fin d) : |x i - x j| ≤ 2 * ‖x‖ :=
  (abs_sub _ _).trans (by linarith [norm_coord_le x i, norm_coord_le x j])

/-- Uniform polynomial-Gaussian majorant for the regularised densities. -/
theorem Dens_bound {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : CutCur.Rd d) :
    (1 + ‖x‖) ^ 2 * Dens d ρ β ε x ≤
      Real.exp ((2 + 2 * (β * d * d)) ^ 2 / ρ) * Real.exp (-(ρ / 4) * ‖x‖ ^ 2) := by
  set r := ‖x‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg x
  set B := (2 * r + 1) ^ β with hB
  have hB1 : 1 ≤ B := Real.one_le_rpow (by linarith) hβ
  have hfac : ∀ i j : Fin d, qe ε β (x i - x j) ≤ B := fun i j => by
    refine (qe_le hε hε1 hβ _).trans (Real.rpow_le_rpow (by positivity) ?_ hβ)
    linarith [abs_sub_coord_le x i j]
  have hprod : (∏ i, ∏ j with i < j, qe ε β (x i - x j)) ≤ B ^ (d * d) := by
    calc (∏ i, ∏ j with i < j, qe ε β (x i - x j)) ≤ ∏ _i : Fin d, B ^ d := by
          refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => qe_nonneg hε _ _) fun i _ => ?_
          calc (∏ j with i < j, qe ε β (x i - x j)) ≤ ∏ _j ∈ Finset.univ.filter (fun j : Fin d => i < j), B :=
                Finset.prod_le_prod₀ (fun j _ => qe_nonneg hε _ _) fun j _ => hfac i j
            _ = B ^ (Finset.univ.filter (fun j : Fin d => i < j)).card := Finset.prod_const _
            _ ≤ B ^ d := pow_le_pow_right₀ hB1 (by
                calc _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
                  _ = d := by simp)
      _ = B ^ (d * d) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hBexp : B ^ (d * d) ≤ Real.exp (2 * r * (β * d * d)) := by
    have h1 : 2 * r + 1 ≤ Real.exp (2 * r) := by linarith [Real.add_one_le_exp (2 * r)]
    have h2 : B ≤ Real.exp (2 * r * β) := by
      calc B ≤ (Real.exp (2 * r)) ^ β := Real.rpow_le_rpow (by positivity) h1 hβ
        _ = Real.exp (2 * r * β) := (Real.exp_mul _ _).symm
    calc B ^ (d * d) ≤ (Real.exp (2 * r * β)) ^ (d * d) := pow_le_pow_left₀ (by positivity) h2 _
      _ = Real.exp (2 * r * (β * d * d)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hpoly : (1 + r) ^ 2 ≤ Real.exp (2 * r) := by
    have h1 : 1 + r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
    calc (1 + r) ^ 2 ≤ (Real.exp r) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      _ = Real.exp (2 * r) := by rw [← Real.exp_nat_mul]; congr 1
  unfold Dens
  have hg : 0 ≤ Real.exp (-(ρ / 2) * r ^ 2) := (Real.exp_pos _).le
  calc (1 + r) ^ 2 * (Real.exp (-(ρ / 2) * r ^ 2) * ∏ i, ∏ j with i < j, qe ε β (x i - x j))
      ≤ Real.exp (2 * r) * (Real.exp (-(ρ / 2) * r ^ 2) * Real.exp (2 * r * (β * d * d))) := by
        exact mul_le_mul hpoly (mul_le_mul_of_nonneg_left (hprod.trans hBexp) hg) (mul_nonneg hg (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => qe_nonneg hε _ _))
          (Real.exp_pos _).le
    _ = Real.exp (-(ρ / 2) * r ^ 2 + (2 + 2 * (β * d * d)) * r) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        set c := 2 + 2 * (β * d * d)
        have : 0 ≤ (ρ * r / 2 - c) ^ 2 / ρ := by positivity
        have e : (ρ * r / 2 - c) ^ 2 / ρ = ρ * r ^ 2 / 4 - c * r + c ^ 2 / ρ := by
          field_simp; ring
        nlinarith


/-- The limit density `e^{-ρ|x|²/2} ∏_{i<j} (x_i-x_j)^β 1_{chamber}`. -/
noncomputable def Dlim (d : ℕ) (ρ β : ℝ) : CutCur.Rd d → ℝ :=
  (chamber d).indicator fun x => Real.exp (-(ρ / 2) * ‖x‖ ^ 2) * ∏ i, ∏ j with i < j, (x i - x j) ^ β

theorem continuous_qe {ε : ℝ} (hε : 0 < ε) {β : ℝ} (hβ : 0 ≤ β) : Continuous (qe ε β) := by
  unfold qe
  have h1 : Continuous fun t : ℝ => ε * sp (t / ε) :=
    continuous_const.mul ((contDiff_sp.continuous).comp (continuous_id.div_const ε))
  refine (h1.rpow_const fun _ => Or.inr hβ).div (by fun_prop) fun t => by positivity

theorem continuous_Dens {ε : ℝ} (hε : 0 < ε) {β : ℝ} (hβ : 0 ≤ β) (ρ : ℝ) :
    Continuous (Dens d ρ β ε) := by
  unfold Dens
  refine (by fun_prop : Continuous fun x : CutCur.Rd d => Real.exp (-(ρ / 2) * ‖x‖ ^ 2)).mul ?_
  refine continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => ?_
  exact (continuous_qe hε hβ).comp (by fun_prop)

theorem measurable_Dlim (ρ β : ℝ) : Measurable (Dlim d ρ β) := by
  unfold Dlim
  refine Measurable.indicator ?_ isOpen_chamber.measurableSet
  refine (by fun_prop : Measurable fun x : CutCur.Rd d => Real.exp (-(ρ / 2) * ‖x‖ ^ 2)).mul ?_
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  exact (by fun_prop : Measurable fun x : CutCur.Rd d => x i - x j).pow_const _

/-- Pointwise limit of the regularised weights at points without ties. -/
theorem tendsto_Dens {ρ β : ℝ} (hβ : 0 ≤ β) {x : CutCur.Rd d} (hx : ∀ i j : Fin d, i ≠ j → x i ≠ x j) :
    Tendsto (fun ε => Dens d ρ β ε x) (𝓝[>] 0) (𝓝 (Dlim d ρ β x)) := by
  let ql : ℝ → ℝ := fun t => if 0 < t then t ^ β else 0
  have hq : ∀ t : ℝ, t ≠ 0 → Tendsto (fun ε => qe ε β t) (𝓝[>] 0) (𝓝 (ql t)) := by
    intro t ht
    rcases lt_or_gt_of_ne ht with h | h
    · simpa [ql, not_lt.2 h.le] using tendsto_qe_neg h hβ
    · simpa [ql, h] using tendsto_qe_pos h β
  have hlim : Tendsto (fun ε => Dens d ρ β ε x) (𝓝[>] 0)
      (𝓝 (Real.exp (-(ρ / 2) * ‖x‖ ^ 2) * ∏ i, ∏ j with i < j, ql (x i - x j))) := by
    refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun i _ => tendsto_finsetProd _ fun j hj => ?_)
    have hij : i < j := by simpa using hj
    exact hq _ (sub_ne_zero.2 (hx i j hij.ne))
  convert hlim using 2
  unfold Dlim
  by_cases hc : x ∈ chamber d
  · rw [Set.indicator_of_mem hc]
    congr 1
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := by simpa using hj
    simp [ql, sub_pos.2 (hc i j hij)]
  · rw [Set.indicator_of_notMem hc]
    simp only [chamber, Set.mem_ofPred_eq, not_forall] at hc
    obtain ⟨i, j, hij, hnot⟩ := hc
    have hlt : x i < x j := lt_of_le_of_ne (not_lt.1 hnot) (hx i j hij.ne)
    rw [mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (i := j) (by simpa using hij) (by simp [ql, hlt.le])))]


theorem volume_ties_null (d : ℕ) :
    volume {x : CutCur.Rd d | ¬ ∀ i j : Fin d, i ≠ j → x i ≠ x j} = 0 := by
  have : {x : CutCur.Rd d | ¬ ∀ i j : Fin d, i ≠ j → x i ≠ x j} =
      ⋃ i : Fin d, ⋃ j : Fin d, ⋃ (_ : i ≠ j), {x : CutCur.Rd d | x i = x j} := by
    ext x; simp
  rw [this]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  let L : CutCur.Rd d →ₗ[ℝ] ℝ :=
    ((EuclideanSpace.proj i : CutCur.Rd d →L[ℝ] ℝ) - EuclideanSpace.proj j).toLinearMap
  have hset : {x : CutCur.Rd d | x i = x j} = (LinearMap.ker L : Set (CutCur.Rd d)) := by
    ext x; simp [L, sub_eq_zero]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  have hmem : (EuclideanSpace.single i (1 : ℝ) : CutCur.Rd d) ∈ LinearMap.ker L := by
    rw [htop]; trivial
  simp [L, LinearMap.mem_ker, hij] at hmem

/-- Dominated convergence for the regularised weights. -/
theorem tendsto_integral_Dens {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
    {F : CutCur.Rd d → ℝ} (hFm : Measurable F) {M : ℝ} (hF : ∀ x, |F x| ≤ M * (1 + ‖x‖) ^ 2) :
    Tendsto (fun ε => ∫ x, Dens d ρ β ε x * F x) (𝓝[>] 0) (𝓝 (∫ x, Dlim d ρ β x * F x)) := by
  have hM : 0 ≤ M := by
    have := hF 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at this
    exact (abs_nonneg _).trans this
  set K := Real.exp ((2 + 2 * (β * d * d)) ^ 2 / ρ) with hK
  have hint : Integrable (fun x : CutCur.Rd d => (M * K) * Real.exp (-(ρ / 4) * ‖x‖ ^ 2)) volume :=
    (integrable_exp_neg_mul_norm_sq (ι := Fin d) (ρ / 4) (by linarith)).const_mul _
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (M * K) * Real.exp (-(ρ / 4) * ‖x‖ ^ 2))
    ?_ ?_ hint ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (continuous_Dens hε hβ ρ).aestronglyMeasurable.mul hFm.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
    refine Eventually.of_forall fun x => ?_
    have hD0 : 0 ≤ Dens d ρ β ε x :=
      mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ =>
        qe_nonneg hε.1 _ _)
    have hb := Dens_bound hρ hβ hε.1 hε.2.le x
    rw [norm_mul, Real.norm_of_nonneg hD0, Real.norm_eq_abs]
    calc Dens d ρ β ε x * |F x| ≤ Dens d ρ β ε x * (M * (1 + ‖x‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (hF x) hD0
      _ = M * ((1 + ‖x‖) ^ 2 * Dens d ρ β ε x) := by ring
      _ ≤ M * (K * Real.exp (-(ρ / 4) * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_left hb hM
      _ = _ := by ring
  · have hnull := volume_ties_null d
    have hae := (measure_eq_zero_iff_ae_notMem.1 hnull)
    filter_upwards [hae] with x hx
    have hx' : ∀ i j : Fin d, i ≠ j → x i ≠ x j := by
      by_contra h; exact hx h
    exact (tendsto_Dens hβ hx').mul_const (F x)

end CutoffRigidity.Dyson
