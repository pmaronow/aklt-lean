import AKLT.Gen.Bellman.Main

/-! Complete declaration-type and kernel-axiom audit of the hand-written API. -/

set_option format.width 100

#check AKLT.Gen.Bellman.System

#check AKLT.Gen.Bellman.System.step

#check AKLT.Gen.Bellman.System.step_mono
#print axioms AKLT.Gen.Bellman.System.step_mono

#check AKLT.Gen.Bellman.System.step_zero
#print axioms AKLT.Gen.Bellman.System.step_zero

#check AKLT.Gen.Bellman.System.step_add
#print axioms AKLT.Gen.Bellman.System.step_add

#check AKLT.Gen.Bellman.System.step_sum
#print axioms AKLT.Gen.Bellman.System.step_sum

#check AKLT.Gen.Bellman.System.exact

#check AKLT.Gen.Bellman.System.horizon

#check AKLT.Gen.Bellman.System.horizon_eq_sum
#print axioms AKLT.Gen.Bellman.System.horizon_eq_sum

#check AKLT.Gen.Bellman.System.total

#check AKLT.Gen.Bellman.System.total_eq_iSup_horizon
#print axioms AKLT.Gen.Bellman.System.total_eq_iSup_horizon

#check AKLT.Gen.Bellman.System.horizon_le
#print axioms AKLT.Gen.Bellman.System.horizon_le

#check AKLT.Gen.Bellman.System.total_le
#print axioms AKLT.Gen.Bellman.System.total_le

#check AKLT.Gen.Bellman.System.total_ne_top
#print axioms AKLT.Gen.Bellman.System.total_ne_top

#check AKLT.Gen.Bellman.System.kill

#check AKLT.Gen.Bellman.System.kill_step
#print axioms AKLT.Gen.Bellman.System.kill_step

#check AKLT.Gen.Bellman.System.reward

#check AKLT.Gen.Bellman.System.supersolution_of_stopping
#print axioms AKLT.Gen.Bellman.System.supersolution_of_stopping

#check AKLT.Gen.Bellman.System.stopped_total_le
#print axioms AKLT.Gen.Bellman.System.stopped_total_le

#check AKLT.Gen.Bellman.System.Words

#check AKLT.Gen.Bellman.System.pathWeight

#check AKLT.Gen.Bellman.System.exact_eq_tsum_paths
#print axioms AKLT.Gen.Bellman.System.exact_eq_tsum_paths

#check AKLT.Gen.Bellman.System.total_eq_tsum_paths
#print axioms AKLT.Gen.Bellman.System.total_eq_tsum_paths

#check AKLT.Gen.Bellman.System.stopped_pathWeight_succ
#print axioms AKLT.Gen.Bellman.System.stopped_pathWeight_succ

#check AKLT.Gen.Bellman.System.FirstHit

#check AKLT.Gen.Bellman.System.stopped_pathWeight_eq
#print axioms AKLT.Gen.Bellman.System.stopped_pathWeight_eq

#check AKLT.Gen.Bellman.System.stopped_total_eq_tsum_firstHit
#print axioms AKLT.Gen.Bellman.System.stopped_total_eq_tsum_firstHit

#check AKLT.Gen.Bellman.patch

#check AKLT.Gen.Bellman.patch_eq_inside
#print axioms AKLT.Gen.Bellman.patch_eq_inside

#check AKLT.Gen.Bellman.patch_eq_outside
#print axioms AKLT.Gen.Bellman.patch_eq_outside

#check AKLT.Gen.Bellman.patch_le_cap
#print axioms AKLT.Gen.Bellman.patch_le_cap

#check AKLT.Gen.Bellman.patch_ne_top
#print axioms AKLT.Gen.Bellman.patch_ne_top

#check AKLT.Gen.Bellman.patch_step_le_free
#print axioms AKLT.Gen.Bellman.patch_step_le_free

#check AKLT.Gen.Bellman.local_global
#print axioms AKLT.Gen.Bellman.local_global

#check AKLT.Gen.Bellman.local_global_total_le
#print axioms AKLT.Gen.Bellman.local_global_total_le

#check AKLT.Gen.Bellman.prefix_domination
#print axioms AKLT.Gen.Bellman.prefix_domination

#check AKLT.Gen.Bellman.Automaton

#check AKLT.Gen.Bellman.Automaton.project

#check AKLT.Gen.Bellman.Automaton.Compatible

#check AKLT.Gen.Bellman.Automaton.quotient

#check AKLT.Gen.Bellman.Automaton.quotient_compatible
#print axioms AKLT.Gen.Bellman.Automaton.quotient_compatible

#check AKLT.Gen.Bellman.Automaton.quotientCoeff

#check AKLT.Gen.Bellman.Automaton.quotientCoeff_compatible
#print axioms AKLT.Gen.Bellman.Automaton.quotientCoeff_compatible

#check AKLT.Gen.Bellman.Automaton.arrivalCoeff

#check AKLT.Gen.Bellman.Automaton.arrivalCoeff_compatible
#print axioms AKLT.Gen.Bellman.Automaton.arrivalCoeff_compatible

#check AKLT.Gen.Bellman.Automaton.edgeValue

#check AKLT.Gen.Bellman.Automaton.backward

#check AKLT.Gen.Bellman.Automaton.system

#check AKLT.Gen.Bellman.Automaton.system_step
#print axioms AKLT.Gen.Bellman.Automaton.system_step

#check AKLT.Gen.Bellman.Automaton.edgeValue_pullback
#print axioms AKLT.Gen.Bellman.Automaton.edgeValue_pullback

#check AKLT.Gen.Bellman.Automaton.backward_pullback
#print axioms AKLT.Gen.Bellman.Automaton.backward_pullback

#check AKLT.Gen.Bellman.Automaton.stopped

#check AKLT.Gen.Bellman.Automaton.stopped_eq_horizon
#print axioms AKLT.Gen.Bellman.Automaton.stopped_eq_horizon

#check AKLT.Gen.Bellman.Automaton.stopped_pullback
#print axioms AKLT.Gen.Bellman.Automaton.stopped_pullback

#check AKLT.Gen.Bellman.Automaton.stopped_iSup_pullback
#print axioms AKLT.Gen.Bellman.Automaton.stopped_iSup_pullback

#check AKLT.Gen.Bellman.Automaton.stopped_total_pullback
#print axioms AKLT.Gen.Bellman.Automaton.stopped_total_pullback

#check AKLT.Gen.Bellman.moment

#check AKLT.Gen.Bellman.moment_step_le
#print axioms AKLT.Gen.Bellman.moment_step_le

#check AKLT.Gen.Bellman.moment_growth
#print axioms AKLT.Gen.Bellman.moment_growth

#check AKLT.Gen.Bellman.mass_growth
#print axioms AKLT.Gen.Bellman.mass_growth

#check AKLT.Gen.Bellman.minWitness

#check AKLT.Gen.Bellman.maxWitness

#check AKLT.Gen.Bellman.minWitness_le
#print axioms AKLT.Gen.Bellman.minWitness_le

#check AKLT.Gen.Bellman.le_maxWitness
#print axioms AKLT.Gen.Bellman.le_maxWitness

#check AKLT.Gen.Bellman.minWitness_pos
#print axioms AKLT.Gen.Bellman.minWitness_pos

#check AKLT.Gen.Bellman.positive_vector_growth
#print axioms AKLT.Gen.Bellman.positive_vector_growth

#check AKLT.Gen.Bellman.walkSum

#check AKLT.Gen.Bellman.walkSum_le
#print axioms AKLT.Gen.Bellman.walkSum_le

#check AKLT.Gen.Bellman.all_length_path_bound
#print axioms AKLT.Gen.Bellman.all_length_path_bound

#check AKLT.Gen.Bellman.growthConstant

#check AKLT.Gen.Bellman.alm_of_constant
#print axioms AKLT.Gen.Bellman.alm_of_constant

#check AKLT.Gen.Bellman.alm
#print axioms AKLT.Gen.Bellman.alm

#check AKLT.Gen.Bellman.scaled_row_sound
#print axioms AKLT.Gen.Bellman.scaled_row_sound

#check AKLT.Gen.Bellman.scaled_ennreal_row_sound
#print axioms AKLT.Gen.Bellman.scaled_ennreal_row_sound

/-! Compiler-generated public declarations are audited as well. -/

#check AKLT.Gen.Bellman.Automaton.casesOn
#print axioms AKLT.Gen.Bellman.Automaton.casesOn

#check AKLT.Gen.Bellman.Automaton.ctorIdx
#print axioms AKLT.Gen.Bellman.Automaton.ctorIdx

#check AKLT.Gen.Bellman.Automaton.mk
#print axioms AKLT.Gen.Bellman.Automaton.mk

#check AKLT.Gen.Bellman.Automaton.mk.inj
#print axioms AKLT.Gen.Bellman.Automaton.mk.inj

#check AKLT.Gen.Bellman.Automaton.mk.injEq
#print axioms AKLT.Gen.Bellman.Automaton.mk.injEq

#check AKLT.Gen.Bellman.Automaton.mk.noConfusion
#print axioms AKLT.Gen.Bellman.Automaton.mk.noConfusion

#check AKLT.Gen.Bellman.Automaton.mk.sizeOf_spec
#print axioms AKLT.Gen.Bellman.Automaton.mk.sizeOf_spec

#check AKLT.Gen.Bellman.Automaton.noConfusion
#print axioms AKLT.Gen.Bellman.Automaton.noConfusion

#check AKLT.Gen.Bellman.Automaton.noConfusionType
#print axioms AKLT.Gen.Bellman.Automaton.noConfusionType

#check AKLT.Gen.Bellman.Automaton.rec
#print axioms AKLT.Gen.Bellman.Automaton.rec

#check AKLT.Gen.Bellman.Automaton.recOn
#print axioms AKLT.Gen.Bellman.Automaton.recOn

#check AKLT.Gen.Bellman.Automaton.stopped.eq_def
#print axioms AKLT.Gen.Bellman.Automaton.stopped.eq_def

#check AKLT.Gen.Bellman.Automaton.trans
#print axioms AKLT.Gen.Bellman.Automaton.trans

#check AKLT.Gen.Bellman.System.FirstHit.eq_def
#print axioms AKLT.Gen.Bellman.System.FirstHit.eq_def

#check AKLT.Gen.Bellman.System.Words.eq_def
#print axioms AKLT.Gen.Bellman.System.Words.eq_def

#check AKLT.Gen.Bellman.System.casesOn
#print axioms AKLT.Gen.Bellman.System.casesOn

#check AKLT.Gen.Bellman.System.ctorIdx
#print axioms AKLT.Gen.Bellman.System.ctorIdx

#check AKLT.Gen.Bellman.System.exact.eq_def
#print axioms AKLT.Gen.Bellman.System.exact.eq_def

#check AKLT.Gen.Bellman.System.horizon.eq_def
#print axioms AKLT.Gen.Bellman.System.horizon.eq_def

#check AKLT.Gen.Bellman.System.mk
#print axioms AKLT.Gen.Bellman.System.mk

#check AKLT.Gen.Bellman.System.mk.inj
#print axioms AKLT.Gen.Bellman.System.mk.inj

#check AKLT.Gen.Bellman.System.mk.injEq
#print axioms AKLT.Gen.Bellman.System.mk.injEq

#check AKLT.Gen.Bellman.System.mk.noConfusion
#print axioms AKLT.Gen.Bellman.System.mk.noConfusion

#check AKLT.Gen.Bellman.System.mk.sizeOf_spec
#print axioms AKLT.Gen.Bellman.System.mk.sizeOf_spec

#check AKLT.Gen.Bellman.System.next
#print axioms AKLT.Gen.Bellman.System.next

#check AKLT.Gen.Bellman.System.noConfusion
#print axioms AKLT.Gen.Bellman.System.noConfusion

#check AKLT.Gen.Bellman.System.noConfusionType
#print axioms AKLT.Gen.Bellman.System.noConfusionType

#check AKLT.Gen.Bellman.System.pathWeight.eq_def
#print axioms AKLT.Gen.Bellman.System.pathWeight.eq_def

#check AKLT.Gen.Bellman.System.rec
#print axioms AKLT.Gen.Bellman.System.rec

#check AKLT.Gen.Bellman.System.recOn
#print axioms AKLT.Gen.Bellman.System.recOn

#check AKLT.Gen.Bellman.System.weight
#print axioms AKLT.Gen.Bellman.System.weight

#check AKLT.Gen.Bellman.maxWitness.congr_simp
#print axioms AKLT.Gen.Bellman.maxWitness.congr_simp

#check AKLT.Gen.Bellman.minWitness.congr_simp
#print axioms AKLT.Gen.Bellman.minWitness.congr_simp

#check AKLT.Gen.Bellman.walkSum.eq_def
#print axioms AKLT.Gen.Bellman.walkSum.eq_def

