module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Actual compact-time closed hitting construction

The terminal cap is included explicitly. A hit by the horizon is kept
separate from the tautological fact that the capped time is at most T.
-/
public section
namespace CutoffRigidity
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E]

@[expose] def cappedClosedHitSet (X : NNReal → E) (R : ℝ) (T : NNReal) : Set NNReal :=
  {t | t = T ∨ t ≤ T ∧ R ≤ ‖X t‖}

@[expose] noncomputable def cappedClosedHitTime (X : NNReal → E) (R : ℝ) (T : NNReal) : NNReal :=
  sInf (cappedClosedHitSet X R T)

theorem cappedClosedHitSet_nonempty (X : NNReal → E) (R : ℝ) (T : NNReal) :
    (cappedClosedHitSet X R T).Nonempty := ⟨T, Or.inl rfl⟩

theorem isClosed_cappedClosedHitSet {X : NNReal → E} (hX : Continuous X) (R : ℝ) (T : NNReal) :
    IsClosed (cappedClosedHitSet X R T) :=
  isClosed_singleton.union (isClosed_Iic.inter (isClosed_Ici.preimage hX.norm))

theorem cappedClosedHitTime_mem {X : NNReal → E} (hX : Continuous X) (R : ℝ) (T : NNReal) :
    cappedClosedHitTime X R T ∈ cappedClosedHitSet X R T :=
  (isClosed_cappedClosedHitSet hX R T).csInf_mem (cappedClosedHitSet_nonempty X R T)
    ⟨0, fun _ _ => zero_le⟩

theorem cappedClosedHitTime_le_horizon (X : NNReal → E) (R : ℝ) (T : NNReal) :
    cappedClosedHitTime X R T ≤ T :=
  csInf_le ⟨0, fun _ _ => zero_le⟩ (Or.inl rfl)

theorem cappedClosedHitTime_le_iff {X : NNReal → E} (hX : Continuous X) (R : ℝ) (T s : NNReal) :
    cappedClosedHitTime X R T ≤ s ↔ T ≤ s ∨ ∃ r : NNReal, r ≤ s ∧ r ≤ T ∧ R ≤ ‖X r‖ := by
  constructor
  · intro hs
    rcases cappedClosedHitTime_mem hX R T with ht | ⟨ht, hh⟩
    · exact Or.inl (ht ▸ hs)
    · exact Or.inr ⟨_, hs, ht, hh⟩
  · rintro (hs | ⟨r, hrs, hrT, hr⟩)
    · exact (cappedClosedHitTime_le_horizon X R T).trans hs
    · have hb : BddBelow (cappedClosedHitSet X R T) := ⟨0, fun _ _ => zero_le⟩
      exact (csInf_le hb (show r ∈ cappedClosedHitSet X R T from Or.inr ⟨hrT, hr⟩)).trans hrs

theorem norm_lt_before_cappedClosedHitTime
    (X : NNReal → E) (R : ℝ) (T t : NNReal) (ht : t < cappedClosedHitTime X R T) : ‖X t‖ < R := by
  by_contra hh
  have hmem : t ∈ cappedClosedHitSet X R T :=
    Or.inr ⟨(ht.le.trans (cappedClosedHitTime_le_horizon X R T)), le_of_not_gt hh⟩
  exact (not_le.mpr ht) (csInf_le ⟨0, fun _ _ => zero_le⟩ hmem)

/-- At the capped time continuity preserves the closed localization ball,
provided the initial point was inside it. -/
theorem norm_le_at_cappedClosedHitTime {X : NNReal → E} (hX : Continuous X)
    (R : ℝ) (T : NNReal) (hinit : ‖X 0‖ ≤ R) :
    ‖X (cappedClosedHitTime X R T)‖ ≤ R := by
  let τ := cappedClosedHitTime X R T
  by_cases ht : τ = 0
  · change ‖X τ‖ ≤ R
    rw [ht]
    exact hinit
  · have hpos : 0 < τ := lt_of_le_of_ne (zero_le) (Ne.symm ht)
    have hsub : Ioo 0 τ ⊆ {t | ‖X t‖ ≤ R} := by
      intro t ht
      exact (norm_lt_before_cappedClosedHitTime X R T t ht.2).le
    have hclosed : IsClosed {t | ‖X t‖ ≤ R} := isClosed_Iic.preimage hX.norm
    have hmem : τ ∈ closure (Ioo 0 τ) := by
      rw [closure_Ioo hpos.ne]
      exact ⟨hpos.le, le_rfl⟩
    exact closure_minimal hsub hclosed hmem

theorem cappedClosedHitTime_lt_implies_hit {X : NNReal → E} (hX : Continuous X)
    (R : ℝ) (T : NNReal) (ht : cappedClosedHitTime X R T < T) :
    ∃ r : NNReal, r ≤ T ∧ R ≤ ‖X r‖ := by
  rcases cappedClosedHitTime_mem hX R T with he | ⟨hrT, hr⟩
  · exact False.elim (ht.ne he)
  · exact ⟨_, hrT, hr⟩

end CutoffRigidity
