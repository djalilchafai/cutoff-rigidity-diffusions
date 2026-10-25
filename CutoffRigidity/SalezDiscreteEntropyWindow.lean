module
public import CutoffRigidity.LangevinEntropyDrop
public import CutoffRigidity.SalezGeometricPartition

/-! # The reciprocal-entropy window argument from genuine finite differences

The written reciprocal integration can be implemented with geometric time
partitions. Downward entropy jumps are harmless; no classical derivative
or unproved transition-density smoothness is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology

theorem reciprocal_increment_ge_of_quadratic_drop
    {A B c e r : ℝ} (hc : 0 < c) (hcB : c ≤ B) (hBA : B ≤ A)
    (he : 0 ≤ e) (hr : 0 ≤ r)
    (hdrop : e * r / 2 * B ^ 2 ≤ A-B) :
    e*r/2 - e*r/(2*c)*(A-B) ≤ B⁻¹ - A⁻¹ := by
  have hB : 0 < B := hc.trans_le hcB
  have hA : 0 < A := hB.trans_le hBA
  have hgap : 0 ≤ A-B := sub_nonneg.mpr hBA
  have hratio : 1 - (A-B)/c ≤ B/A := by
    have hfrac : (A-B)/A ≤ (A-B)/c := div_le_div_of_nonneg_left hgap hc (hcB.trans hBA)
    have hid : B/A = 1 - (A-B)/A := by field_simp; ring
    rw [hid]
    linarith
  have hstep : (e*r/2)*(B/A) ≤ B⁻¹-A⁻¹ := by
    have hh := div_le_div_of_nonneg_right hdrop (mul_pos hA hB).le
    convert! hh using 1 <;> field_simp
  calc
    _ = (e*r/2)*(1-(A-B)/c) := by ring
    _ ≤ (e*r/2)*(B/A) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ _ := hstep

set_option maxHeartbeats 800000 in
theorem entropy_reciprocal_partition_bound
    (H I : ℝ → ℝ) {a b eps : ℝ} (ha : 0 < a) (hab : a < b) (heps : 0 < eps)
    (hH : AntitoneOn H (Icc a b))
    (hDrop : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t → (t-s)*I t ≤ H s-H t)
    (hVar : ∀ t ∈ Icc a b, 1/eps < H t → (eps*H t-1)^2 ≤ 2*t*I t)
    (hLarge : 1/eps < H b)
    (N : ℕ) (grid : ℕ → ℝ) (h0 : grid 0 = a) (hN : grid N = b)
    (hGrid : ∀ j ≤ N, grid j ∈ Icc a b)
    (hStep : ∀ j < N, grid j < grid (j+1))
    (r : ℝ) (hr : 0 ≤ r) (hRatio : ∀ j < N, (grid (j+1)-grid j)/grid (j+1) = r) :
    eps/2*((N : ℝ)*r) - eps*r/(2*(eps*H b-1))*((eps*H a-1)-(eps*H b-1)) ≤
      (eps*H b-1)⁻¹-(eps*H a-1)⁻¹ := by
  let A := fun j => eps*H (grid j)-1
  have hc : 0 < eps*H b-1 := by
    have hh := (div_lt_iff₀ heps).mp hLarge
    nlinarith
  have hAj (j : ℕ) (hj : j ≤ N) : eps*H b-1 ≤ A j := by
    have hh := hH (hGrid j hj) ⟨hab.le,le_rfl⟩ (hGrid j hj).2
    dsimp only [A]
    nlinarith
  have hInc (j : ℕ) (hj : j < N) :
      eps*r/2-eps*r/(2*(eps*H b-1))*(A j-A (j+1)) ≤ (A (j+1))⁻¹-(A j)⁻¹ := by
    have hj0 := hGrid j hj.le
    have hj1 := hGrid (j+1) (by omega)
    have hst := hStep j hj
    have htpos : 0 < grid (j+1) := ha.trans_le hj1.1
    have hOrd : A (j+1) ≤ A j := by
      have hh := hH hj0 hj1 hst.le
      dsimp only [A]
      nlinarith
    have hLargeJ : 1/eps < H (grid (j+1)) := hLarge.trans_le (hH hj1 ⟨hab.le,le_rfl⟩ hj1.2)
    have hVarJ := hVar (grid (j+1)) hj1 hLargeJ
    have hDropJ := hDrop (grid j) hj0 (grid (j+1)) hj1 hst
    have hQuad : eps*r/2*(A (j+1))^2 ≤ A j-A (j+1) := by
      calc
        _ ≤ eps*r/2*(2*grid (j+1)*I (grid (j+1))) :=
          mul_le_mul_of_nonneg_left hVarJ (by positivity)
        _ = eps*((grid (j+1)-grid j)*I (grid (j+1))) := by
          rw [← hRatio j hj]
          field_simp
        _ ≤ eps*(H (grid j)-H (grid (j+1))) := mul_le_mul_of_nonneg_left hDropJ heps.le
        _ = _ := by dsimp only [A]; ring
    exact reciprocal_increment_ge_of_quadratic_drop hc (hAj (j+1) (by omega)) hOrd heps.le hr hQuad
  have hSum := Finset.sum_le_sum (s := Finset.range N) (fun j hj => hInc j (Finset.mem_range.mp hj))
  have hTel : (∑ j ∈ Finset.range N, ((A (j+1))⁻¹-(A j)⁻¹)) = (A N)⁻¹-(A 0)⁻¹ := by
    exact Finset.sum_range_sub (fun j => (A j)⁻¹) N
  have hATel : (∑ j ∈ Finset.range N, (A j-A (j+1))) = A 0-A N := by
    calc
      _ = -(∑ j ∈ Finset.range N, (A (j+1)-A j)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        abel
      _ = A 0-A N := by rw [Finset.sum_range_sub]; abel
  rw [hTel,Finset.sum_sub_distrib,Finset.sum_const] at hSum
  have he : (∑ j ∈ Finset.range N, eps*r/(2*(eps*H b-1))*(A j-A (j+1))) =
      eps*r/(2*(eps*H b-1))*(A 0-A N) := by
    rw [← Finset.mul_sum,hATel]
  rw [he] at hSum
  dsimp only [A] at hSum
  rw [h0,hN] at hSum
  convert! hSum using 1 <;> simp only [Finset.card_range,nsmul_eq_mul] <;> ring

/-- The exact reciprocal-entropy window constant, derived from actual
finite-difference dissipation. No continuity or derivative of H is assumed. -/
theorem salez_entropy_window_of_drop
    (H I : ℝ → ℝ) {a b eps : ℝ} (ha : 0 < a) (hab : a < b) (heps : 0 < eps)
    (hH : AntitoneOn H (Icc a b))
    (hDrop : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t → (t-s)*I t ≤ H s-H t)
    (hVar : ∀ t ∈ Icc a b, 1/eps < H t → (eps*H t-1)^2 ≤ 2*t*I t) :
    H b ≤ 1/eps+2/(eps^2*Real.log (b/a)) := by
  have hL : 0 < Real.log (b/a) := Real.log_pos ((one_lt_div ha).mpr hab)
  by_cases hsmall : H b ≤ 1/eps
  · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  have hLarge : 1/eps < H b := lt_of_not_ge hsmall
  have hb : 0 < eps*H b-1 := by
    have hh := (div_lt_iff₀ heps).mp hLarge
    nlinarith
  have hpart (n : ℕ) := entropy_reciprocal_partition_bound H I ha hab heps hH hDrop hVar hLarge
    (n+1) (salezGeometricTime a b n) (salezGeometricTime_zero a b n)
    (salezGeometricTime_terminal ha hab n)
    (fun j hj => salezGeometricTime_mem_Icc ha hab n j hj)
    (fun j _ => salezGeometricTime_strictMono ha hab n (Nat.lt_succ_self j))
    (salezGeometricRatio (Real.log (b/a)) n) (salezGeometricRatio_pos hL n).le
    (fun j _ => salezGeometricTime_increment_ratio ha n j)
  have hlim : Tendsto (fun n : ℕ =>
      eps/2*((n+1 : ℕ) : ℝ)*salezGeometricRatio (Real.log (b/a)) n -
        eps*salezGeometricRatio (Real.log (b/a)) n/(2*(eps*H b-1))*
          ((eps*H a-1)-(eps*H b-1))) atTop (𝓝 (eps/2*Real.log (b/a))) := by
    have h1 := (salezGeometricRatio_scaled_tendsto hL).const_mul (eps/2)
    have h2 := (((salezGeometricRatio_tendsto_zero (Real.log (b/a))).const_mul eps).div_const
      (2*(eps*H b-1))).mul_const ((eps*H a-1)-(eps*H b-1))
    convert! h1.sub h2 using 1
    · ext n; push_cast; ring
    · simp
  have hbound : eps/2*Real.log (b/a) ≤ (eps*H b-1)⁻¹-(eps*H a-1)⁻¹ := by
    apply le_of_tendsto hlim
    exact Eventually.of_forall fun n => by convert! hpart n using 1 <;> ring
  have hHa : H b ≤ H a := hH ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab.le
  have hAa : 0 < eps*H a-1 := lt_of_lt_of_le hb (by nlinarith)
  have hF : eps/2*Real.log (b/a) ≤ (eps*H b-1)⁻¹ :=
    hbound.trans (sub_le_self _ (inv_nonneg.mpr hAa.le))
  have hmul : (eps/2*Real.log (b/a))*(eps*H b-1) ≤ 1 := by
    exact (le_div_iff₀ hb).mp (by simpa only [one_div] using hF)
  have hAb : eps*H b-1 ≤ 2/(eps*Real.log (b/a)) := by
    apply (le_div_iff₀ (mul_pos heps hL)).mpr
    nlinarith
  calc
    H b ≤ (1+2/(eps*Real.log (b/a)))/eps := by
      apply (le_div_iff₀ heps).mpr
      nlinarith
    _ = 1/eps+2/(eps^2*Real.log (b/a)) := by field_simp

end CutoffRigidity
