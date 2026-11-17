module

import all Handwritten
import all Regression.Solution
import Lean.Elab.Print

#print axioms AKLT.Challenge.b_nonzero
#print axioms AKLT.Final.main_of_inputs
#print axioms AKLT.Final.main_of_certificates
#print axioms AKLTPalomar.h1_iff
#print axioms AKLTPalomar.h3_iff
#print axioms AKLTPalomar.main_iff
#print axioms AKLTPalomar.aklt_gap_of_inputs
#print axioms RegenSamples.H1.checked
#print axioms RegenSamples.H1.packed_reduces
#print axioms RegenSamples.H1Consumer.packed_reduces_again
#print axioms RegenSamples.H1Consumer.lowerTriangular
#print axioms RegenSamples.H1Consumer.literal_reduces
#print axioms RegenSamples.H3.checked
#print axioms RegenSamples.H3.walk_step
#print axioms RegenSamples.H3Consumer.component_bound
#print axioms RegenSamples.H3Consumer.literal_reduces

-- Inspect every available first-party constant, including hidden proof signatures.
-- This command only checks the environment and logs the result.
run_elab do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for modInfo in env.header.modules, data in env.header.moduleData do
    if [`AKLT, `CertData, `RegenSamples, `Regression].any (·.isPrefixOf modInfo.module) then
      for name in data.constNames do
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless [`propext, `Classical.choice, `Quot.sound].contains ax do
            Lean.throwError "Forbidden axiom {ax} in {name}"
        count := count + 1
  unless 0 < count do
    Lean.throwError "The first-party audit selected no declarations"
  Lean.logInfo m!"FIRST_PARTY_AXIOM_AUDIT_PASS: {count} constants"

-- Inventory available declaration bodies for the regeneration interface.
run_elab do
  let env ← Lean.getEnv
  for modInfo in env.header.modules, data in env.header.moduleData do
    if [`AKLT, `CertData].any (·.isPrefixOf modInfo.module) then
      for name in data.constNames, info in data.constants do
        let kind := if info.isTheorem then "theorem" else if info.isDefinition then "definition" else "signature"
        Lean.logInfo m!"PORT_DECL|{modInfo.module}|{name}|{kind}|{info.hasValue}"
