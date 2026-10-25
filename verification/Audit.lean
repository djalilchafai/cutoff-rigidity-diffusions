module

import CutoffRigidity
import Lean.Util.CollectAxioms

/-! Kernel axiom audit for the supporting results, not paper-level endpoints. -/

/-- info: 'CutoffRigidity.decay_at_criticalTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.decay_at_criticalTime
/-- info: 'CutoffRigidity.dimension_decay_at_criticalTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.dimension_decay_at_criticalTime
/-- info: 'CutoffRigidity.power_after_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.power_after_cutoff
/-- info: 'CutoffRigidity.power_before_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.power_before_cutoff
/-- info: 'CutoffRigidity.upper_bound_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.upper_bound_transfer
/-- info: 'CutoffRigidity.lower_bound_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.lower_bound_transfer
/-- info: 'CutoffRigidity.exponential_upper_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.exponential_upper_cutoff
/-- info: 'CutoffRigidity.exponential_lower_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.exponential_lower_cutoff
/-- info: 'CutoffRigidity.criticalTime_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.criticalTime_scale
/-- info: 'CutoffRigidity.curvature_time_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.curvature_time_product
/-- info: 'CutoffRigidity.dimension_eventually_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.dimension_eventually_ge_one
/-- info: 'CutoffRigidity.shrinking_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.shrinking_time
/-- info: 'CutoffRigidity.diverging_curvature_time_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.diverging_curvature_time_product
/-- info: 'CutoffRigidity.product_condition_does_not_force_time_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.product_condition_does_not_force_time_divergence

/-- info: 'CutoffRigidity.time_diverges_of_bounded_curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.time_diverges_of_bounded_curvature

/-- info: 'CutoffRigidity.gaussian_variance_correction_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.gaussian_variance_correction_le

/-- info: 'CutoffRigidity.ouW2Squared_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.ouW2Squared_bounds

/-- info: 'CutoffRigidity.ouFisher_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.ouFisher_lower

/-- info: 'CutoffRigidity.ouW2Squared_three_quarters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.ouW2Squared_three_quarters

/-- info: 'CutoffRigidity.ouFisher_five_quarters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CutoffRigidity.ouFisher_five_quarters

/- Check every declaration in the project namespace, including definitions
and intermediate results added after the individually guarded checks above. -/
run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if (`CutoffRigidity).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless (#[`propext, `Classical.choice, `Quot.sound]).contains ax do
          throwError "{name} depends on forbidden axiom {ax}"
