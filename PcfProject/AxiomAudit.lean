import PcfProject.PcfTransitiveApplications

/-!
# Public theorem axiom audit

These commands audit every public result listed in `TROPHIES.md`.  Keeping the
checks in one default-built module preserves the trust boundary without
interleaving hundreds of diagnostic messages with the mathematical source.

The audit records only the axioms used by each proof term.  Statements,
hypotheses, and explanatory comments remain beside the proofs in their
defining modules.
-/

namespace PcfProject

#print axioms two_power_alephOmega_lt_alephOmega4
#print axioms targetConditionalStatement_of_strongLimit
#print axioms alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit
#print axioms exists_pcf_transitive_successorDirected_generators_of_successorDoublePower
#print axioms successorAlephLocalLemma2410ExactUpperBounds
#print axioms exists_omegaOneClubGuessingAtAlephThree
#print axioms targetAlephOmega_power_aleph0_le_maxPcf_of_strongLimit_of_lt_alephOmega4
#print axioms canonicalGeneratorSystemOfTwoPowerBelowCoordinates
#print axioms AllUltrafiltersPrincipal.pcf_below_alephOmega4

end PcfProject
