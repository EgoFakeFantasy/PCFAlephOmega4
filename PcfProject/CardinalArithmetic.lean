import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Target cardinals and theorem statement

This module fixes the standard notation used by the proof.  It also records
the elementary order and singularity facts consumed downstream.  The actual
PCF theorem is proved in `PcfTransitiveApplications`; no structural PCF
hypothesis is introduced here.
-/

namespace PcfProject

universe u

noncomputable section

open scoped Cardinal

/-!
`targetIndexOmega4` is the ordinal usually written `omega_4`, represented in
Mathlib as the initial ordinal of the fourth infinite cardinal.
-/

/-- The ordinal index `omega` used in `aleph_omega`. -/
abbrev targetIndexOmega : Ordinal.{u} :=
  Ordinal.omega0

/-- The initial ordinal `omega_4`, used as the index of the target bound. -/
abbrev targetIndexOmega4 : Ordinal.{u} :=
  (Cardinal.aleph (4 : Ordinal)).ord

/-- The singular cardinal `aleph_omega` whose power set is bounded below. -/
abbrev targetAlephOmega : Cardinal.{u} :=
  Cardinal.aleph targetIndexOmega

/-- The target upper bound `aleph_(omega_4)`. -/
abbrev targetAlephOmega4 : Cardinal.{u} :=
  Cardinal.aleph targetIndexOmega4

/-- The final inequality `2^(aleph_omega) < aleph_(omega_4)`. -/
def targetUpperBoundStatement : Prop :=
  (2 : Cardinal.{u}) ^ targetAlephOmega < targetAlephOmega4

/-- The final inequality under the explicit strong-limit hypothesis used by the proof. -/
def targetConditionalStatement : Prop :=
  Cardinal.IsStrongLimit targetAlephOmega.{u} ->
    targetUpperBoundStatement.{u}


theorem targetAlephOmega_aleph0_le :
    Cardinal.aleph0 <= targetAlephOmega := by
  exact Cardinal.aleph0_le_aleph Ordinal.omega0

theorem targetAlephOmega_lt_targetAlephOmega4 :
    targetAlephOmega.{u} < targetAlephOmega4 := by
  rw [Cardinal.aleph_lt_aleph, Cardinal.omega0_lt_ord,
    Cardinal.aleph0_lt_aleph]
  simp

theorem targetAlephOmega_isSingular :
    Cardinal.IsSingular targetAlephOmega := by
  simpa [targetAlephOmega, targetIndexOmega] using
    Cardinal.isSingular_aleph_omega0

theorem targetAlephOmega_not_isRegular :
    Not (Cardinal.IsRegular targetAlephOmega) :=
  targetAlephOmega_isSingular.not_isRegular


end

end PcfProject
