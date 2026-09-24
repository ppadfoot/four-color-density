import Audit41
set_option pp.all true in
#check Audit41.published_statement
#print axioms Audit41.published_statement
#print axioms Conjecture41.periodic_density
#print axioms Conjecture41.exists_torusTriangulation
#print axioms Conjecture41.PeriodicConfig.area_identity
#print axioms Conjecture41.PeriodicConfig.euler_identity
#print axioms Conjecture41.DeloneSet.exists_mem_delCell

namespace AuditNegativeControl
axiom injectedFalse : False
theorem poisoned : False := injectedFalse
/-- info: 'AuditNegativeControl.poisoned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poisoned
end AuditNegativeControl

namespace AuditNegativeControl
theorem admitted : False := by sorry
/-- info: 'AuditNegativeControl.admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admitted
end AuditNegativeControl
