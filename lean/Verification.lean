import Conjecture41
import Audit41

/-! Final statement and transitive-axiom checks. A mismatch makes the build fail. -/

#check Audit41.published_statement

/-- info: 'Audit41.published_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Audit41.published_statement

#print axioms Audit41.published_statement

#check Conjecture41.conjecture_4_1

/-- info: 'Conjecture41.conjecture_4_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Conjecture41.conjecture_4_1

#print axioms Conjecture41.conjecture_4_1

#check Conjecture41.conjecture_4_1_limsup

/-- info: 'Conjecture41.conjecture_4_1_limsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Conjecture41.conjecture_4_1_limsup

#print axioms Conjecture41.conjecture_4_1_limsup

