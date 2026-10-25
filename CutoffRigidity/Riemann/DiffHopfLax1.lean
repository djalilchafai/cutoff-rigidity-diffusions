module

public import CutoffRigidity.Riemann.DiffKuwPre

/-! # Hopf-Lax inf-convolution on a proper (closed balls compact) metric space, part 1

`hlQ h r y = inf_z (h z + dd y z ^ 2 / (2 r))`: attainment, bounds, monotonicity and Lipschitz
dependence in `r`, Lipschitz dependence in `y`.
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CutoffRigidity.Riemann.Diff

section HL

variable {X : Type*} [EMetricSpace X]

theorem continuous_dd (hfin : ∀ x y : X, edist x y ≠ ⊤) :
    Continuous (fun p : X × X => dd p.1 p.2) := by
  have h1 : Continuous fun p : X × X => edist p.1 p.2 := continuous_edist
  exact ENNReal.continuousOn_toReal.comp_continuous h1 (fun p => hfin _ _)

theorem continuous_dd_left (hfin : ∀ x y : X, edist x y ≠ ⊤) (y : X) :
    Continuous (fun z : X => dd y z) :=
  (continuous_dd hfin).comp (continuous_const.prodMk continuous_id)

/-- The Hopf-Lax inf-convolution `Q_r h (y) = inf_z (h z + d(y,z)^2/(2r))`. -/
noncomputable def hlQ (h : X → ℝ) (r : ℝ) (y : X) : ℝ := ⨅ z : X, (h z + dd y z ^ 2 / (2 * r))

variable {h : X → ℝ} {Λ : ℝ≥0} {B r : ℝ}

theorem hlQ_bddBelow (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y : X) :
    BddBelow (range fun z => h z + dd y z ^ 2 / (2 * r)) := by
  refine ⟨-B, ?_⟩
  rintro _ ⟨z, rfl⟩
  have h1 := neg_abs_le (h z)
  have h2 := hb z
  have h3 : 0 ≤ dd y z ^ 2 / (2 * r) := by positivity
  simp only
  linarith

theorem hlQ_le (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y z : X) :
    hlQ h r y ≤ h z + dd y z ^ 2 / (2 * r) :=
  ciInf_le (hlQ_bddBelow hb hr y) z

theorem le_hlQ {c : ℝ} (y : X) (hc : ∀ z, c ≤ h z + dd y z ^ 2 / (2 * r)) : c ≤ hlQ h r y := by
  have : Nonempty X := ⟨y⟩
  exact le_ciInf hc

theorem hlQ_le_self (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y : X) : hlQ h r y ≤ h y := by
  have := hlQ_le hb hr y y
  simpa [dd_self] using this

theorem opt_dist_le (hfin : ∀ x y : X, edist x y ≠ ⊤) (hh : LipschitzWith Λ h)
    (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) {y z : X}
    (hz : hlQ h r y = h z + dd y z ^ 2 / (2 * r)) : dd y z ≤ 2 * r * Λ := by
  have h1 := hlQ_le_self hb hr y
  have h2 := abs_sub_le_of_lipschitz hfin hh y z
  have h3 := (abs_le.1 h2).2
  have hd0 := dd_nonneg y z
  have h4 : dd y z ^ 2 / (2 * r) ≤ Λ * dd y z := by linarith
  rw [div_le_iff₀ (by positivity)] at h4
  by_contra hc
  push Not at hc
  have hΛ : (0 : ℝ) ≤ Λ := Λ.2
  have hd : 0 < dd y z := lt_of_le_of_lt (by positivity) hc
  nlinarith

theorem exists_opt (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y : X) :
    ∃ z, hlQ h r y = h z + dd y z ^ 2 / (2 * r) ∧ dd y z ≤ 2 * r * Λ := by
  have hΛ : (0 : ℝ) ≤ Λ := Λ.2
  set K : Set X := {z : X | dd y z ≤ 2 * r * Λ} with hKdef
  have hK : IsCompact K := hcpt y (2 * r * Λ)
  have hyK : y ∈ K := by
    simp only [hKdef, mem_ofPred_eq, dd_self]; positivity
  have hcont : Continuous fun z => h z + dd y z ^ 2 / (2 * r) :=
    hh.continuous.add (((continuous_dd_left hfin y).pow 2).div_const _)
  obtain ⟨z, hzK, hzmin⟩ := hK.exists_isMinOn ⟨y, hyK⟩ hcont.continuousOn
  have hyz := isMinOn_iff.1 hzmin y hyK
  have hall : ∀ w, h z + dd y z ^ 2 / (2 * r) ≤ h w + dd y w ^ 2 / (2 * r) := by
    intro w
    by_cases hw : w ∈ K
    · exact isMinOn_iff.1 hzmin w hw
    · have hw' : 2 * r * Λ < dd y w := not_le.1 hw
      have h1 := (abs_le.1 (abs_sub_le_of_lipschitz hfin hh y w)).2
      have h2 : Λ * dd y w ≤ dd y w ^ 2 / (2 * r) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith [dd_nonneg y w]
      simp only [dd_self] at hyz
      simp at hyz
      linarith
  have heq : hlQ h r y = h z + dd y z ^ 2 / (2 * r) :=
    le_antisymm (hlQ_le hb hr y z) (le_hlQ y hall)
  exact ⟨z, heq, hzK⟩

theorem self_sub_le (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y : X) :
    h y - r * Λ ^ 2 / 2 ≤ hlQ h r y := by
  obtain ⟨z, hz, -⟩ := exists_opt hfin hcpt hh hb hr y
  have h1 := (abs_le.1 (abs_sub_le_of_lipschitz hfin hh y z)).2
  have h2 : dd y z ^ 2 / (2 * r) - Λ * dd y z + r * Λ ^ 2 / 2
      = (dd y z - r * Λ) ^ 2 / (2 * r) := by field_simp; ring
  have h3 : 0 ≤ (dd y z - r * Λ) ^ 2 / (2 * r) := by positivity
  linarith

theorem abs_hlQ_le (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y : X) : |hlQ h r y| ≤ B := by
  rw [abs_le]
  refine ⟨le_hlQ y fun z => ?_, (hlQ_le_self hb hr y).trans (abs_le.1 (hb y)).2⟩
  have h1 := neg_abs_le (h z)
  have h2 := hb z
  have h3 : 0 ≤ dd y z ^ 2 / (2 * r) := by positivity
  linarith

theorem hlQ_anti (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) {s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (y : X) :
    hlQ h s y ≤ hlQ h r y := by
  have hs : 0 < s := hr.trans_le hrs
  obtain ⟨z, hz, -⟩ := exists_opt hfin hcpt hh hb hr y
  have h1 := hlQ_le hb hs y z
  have h2 : dd y z ^ 2 / (2 * s) ≤ dd y z ^ 2 / (2 * r) := by gcongr
  linarith

theorem hlQ_sub_le_time (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) {s : ℝ} (hs : 0 < s) (hsr : s ≤ r) (y : X) :
    hlQ h s y - hlQ h r y ≤ 2 * (Λ : ℝ) ^ 2 * (r / s) * (r - s) := by
  have hr : 0 < r := hs.trans_le hsr
  obtain ⟨z, hz, hd⟩ := exists_opt hfin hcpt hh hb hr y
  have h1 := hlQ_le hb hs y z
  have h0 := dd_nonneg y z
  have e : dd y z ^ 2 / (2 * s) - dd y z ^ 2 / (2 * r) = dd y z ^ 2 * (r - s) / (2 * r * s) := by
    field_simp
  have h2 : dd y z ^ 2 ≤ (2 * r * Λ) ^ 2 := pow_le_pow_left₀ h0 hd 2
  have h3 : dd y z ^ 2 * (r - s) / (2 * r * s) ≤ (2 * r * Λ) ^ 2 * (r - s) / (2 * r * s) := by
    gcongr
  have e2 : (2 * r * (Λ : ℝ)) ^ 2 * (r - s) / (2 * r * s) = 2 * (Λ : ℝ) ^ 2 * (r / s) * (r - s) := by
    field_simp
  linarith

/-- Time-Lipschitz bound (constant depends only on `Λ`, `R`, `r₀`). -/
theorem abs_hlQ_sub_le (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) {r0 s R : ℝ} (hr0 : 0 < r0) (hs : r0 ≤ s)
    (hr : r0 ≤ r) (hR : r ≤ R) (y : X) :
    |hlQ h r y - hlQ h s y| ≤ 4 * (Λ : ℝ) ^ 2 * (R / r0) * |r - s| := by
  have hr' : 0 < r := hr0.trans_le hr
  have hs' : 0 < s := hr0.trans_le hs
  have hq : 1 ≤ R / r0 := by rw [le_div_iff₀ hr0]; linarith
  have hΛ2 : 0 ≤ (Λ : ℝ) ^ 2 := by positivity
  rcases le_total s r with hsr | hrs
  · have h1 := hlQ_anti hfin hcpt hh hb hs' hsr y
    have h2 := hlQ_sub_le_time hfin hcpt hh hb hs' hsr y
    have hR0 : 0 ≤ R := by linarith
    have h3 : r / s ≤ R / r0 := by gcongr
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    have : 2 * (Λ : ℝ) ^ 2 * (r / s) * (r - s) ≤ 4 * (Λ : ℝ) ^ 2 * (R / r0) * (r - s) := by
      have : 0 ≤ r - s := by linarith
      nlinarith [mul_nonneg hΛ2 this]
    linarith
  · have h1 := hlQ_anti hfin hcpt hh hb hr' hrs y
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    have hrs0 : 0 ≤ s - r := by linarith
    by_cases hs2 : s ≤ 2 * R
    · have h2 := hlQ_sub_le_time hfin hcpt hh hb hr' hrs y
      have h3 : s / r ≤ 2 * (R / r0) := by
        have hR0 : 0 ≤ R := by linarith
        rw [← mul_div_assoc]; gcongr
      have : 2 * (Λ : ℝ) ^ 2 * (s / r) * (s - r) ≤ 4 * (Λ : ℝ) ^ 2 * (R / r0) * (s - r) := by
        nlinarith [mul_nonneg hΛ2 hrs0]
      linarith
    · push Not at hs2
      have h2 := hlQ_le_self hb hr' y
      have h3 := self_sub_le hfin hcpt hh hb hs' y
      have : (Λ : ℝ) ^ 2 * s / 2 ≤ (Λ : ℝ) ^ 2 * (s - r) := by nlinarith
      have : (Λ : ℝ) ^ 2 * (s - r) ≤ 4 * (Λ : ℝ) ^ 2 * (R / r0) * (s - r) := by
        nlinarith [mul_nonneg hΛ2 hrs0]
      nlinarith

theorem lipschitzWith_of_abs_le (hfin : ∀ x y : X, edist x y ≠ ⊤) {f : X → ℝ} {C : ℝ≥0}
    (h : ∀ x y, |f x - f y| ≤ C * dd x y) : LipschitzWith C f := by
  refine fun x y => ?_
  rw [edist_dist, Real.dist_eq, edist_eq_ofReal_dd hfin, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  exact ENNReal.ofReal_le_ofReal (h x y)

theorem hlQ_sub_le_pt (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) {y y' z : X}
    (hz : hlQ h r y' = h z + dd y' z ^ 2 / (2 * r))
    (hfin : ∀ x y : X, edist x y ≠ ⊤) :
    hlQ h r y - hlQ h r y' ≤ dd y y' * (2 * dd y' z + dd y y') / (2 * r) := by
  have h1 := hlQ_le hb hr y z
  have h0 := dd_nonneg y z
  have h0' := dd_nonneg y' z
  have hδ := dd_nonneg y y'
  have ht := dd_triangle hfin y y' z
  have h2 : dd y z ^ 2 ≤ (dd y y' + dd y' z) ^ 2 := pow_le_pow_left₀ h0 ht 2
  have h3 : dd y z ^ 2 / (2 * r) - dd y' z ^ 2 / (2 * r)
      ≤ dd y y' * (2 * dd y' z + dd y y') / (2 * r) := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  linarith

theorem hlQ_sub_le_C (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y y' : X) :
    hlQ h r y - hlQ h r y' ≤ (2 * Λ + 1 / (2 * r) + 2 * B) * dd y y' := by
  have hΛ : (0 : ℝ) ≤ Λ := Λ.2
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb y)
  have hδ := dd_nonneg y y'
  have hr1 : 0 ≤ 1 / (2 * r) := by positivity
  by_cases hd : dd y y' ≤ 1
  · obtain ⟨z, hz, hz2⟩ := exists_opt hfin hcpt hh hb hr y'
    have h1 := hlQ_sub_le_pt hb hr hz hfin (y := y)
    have h2 : (2 * dd y' z + dd y y') / (2 * r) ≤ 2 * Λ + 1 / (2 * r) := by
      rw [div_le_iff₀ (by positivity)]
      have e : (2 * (Λ : ℝ) + 1 / (2 * r)) * (2 * r) = 4 * r * Λ + 1 := by field_simp; ring
      rw [e]; nlinarith
    have h3 : dd y y' * (2 * dd y' z + dd y y') / (2 * r)
        = dd y y' * ((2 * dd y' z + dd y y') / (2 * r)) := by ring
    have h4 : dd y y' * ((2 * dd y' z + dd y y') / (2 * r)) ≤ dd y y' * (2 * Λ + 1 / (2 * r)) :=
      mul_le_mul_of_nonneg_left h2 hδ
    nlinarith
  · push Not at hd
    have h1 := abs_hlQ_le hb hr y
    have h2 := abs_hlQ_le hb hr y'
    rw [abs_le] at h1 h2
    have : 0 ≤ 2 * (Λ : ℝ) + 1 / (2 * r) := by positivity
    nlinarith

/-- **(HL5)** `Q_r h` is Lipschitz. -/
theorem lipschitzWith_hlQ (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) :
    ∃ C : ℝ≥0, LipschitzWith C (hlQ h r) := by
  have hΛ : (0 : ℝ) ≤ Λ := Λ.2
  set C1 : ℝ := 2 * Λ + 1 / (2 * r) + 2 * |B| with hC1
  have hC1nn : 0 ≤ C1 := by positivity
  refine ⟨⟨C1, hC1nn⟩, lipschitzWith_of_abs_le hfin fun y y' => ?_⟩
  show |hlQ h r y - hlQ h r y'| ≤ C1 * dd y y'
  rw [abs_le]
  have hle : (2 * (Λ : ℝ) + 1 / (2 * r) + 2 * B) * dd y y' ≤ C1 * dd y y' :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self B]) (dd_nonneg _ _)
  have hle' : (2 * (Λ : ℝ) + 1 / (2 * r) + 2 * B) * dd y' y ≤ C1 * dd y y' := by
    rw [dd_comm y' y]; exact hle
  have a1 := hlQ_sub_le_C hfin hcpt hh hb hr y y'
  have a2 := hlQ_sub_le_C hfin hcpt hh hb hr y' y
  constructor <;> linarith

theorem continuous_hlQ (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) : Continuous (hlQ h r) :=
  (lipschitzWith_hlQ hfin hcpt hh hb hr).choose_spec.continuous

end HL

end CutoffRigidity.Riemann.Diff
