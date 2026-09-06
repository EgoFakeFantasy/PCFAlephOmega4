import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Stage 1: Mathlib cardinal target statements

Field provenance table:

- A. Mathlib native: `Cardinal`, `Ordinal`, `Cardinal.aleph`,
  `Ordinal.omega0`, `Cardinal.ord`, cardinal exponentiation `(^)`,
  `Cardinal.IsRegular`, `Cardinal.IsSingular`, `Cardinal.IsStrongLimit`,
  and `Cardinal.lt_power_cof_ord`.
- B. Project-proved in this file:
  `targetAlephOmega_aleph0_le`,
  `targetAlephOmega_lt_targetAlephOmega4`,
  `targetAlephOmega_isSingular`,
  `targetAlephOmega_not_isRegular`,
  `exists_strictUpperBound_below_targetIndexOmega4_of_orderType_omega_one`,
  `not_isSuccPrelimit_of_regular_aleph_below_targetIndexOmega4`,
  `targetAlephOmega_konig_lower_bound`.
- C. Target definitions:
  `targetUpperBoundStatement` and `targetConditionalStatement` state the
  intended PCF target. Their proof is completed downstream by
  `targetConditionalStatement_of_strongLimit` and
  `two_power_alephOmega_lt_alephOmega4` in
  `PcfProject.PcfTransitiveApplications`.

No new project `structure` is introduced in this file, so the vacuity test for
new structures is not applicable.
-/

namespace PcfProject

universe u

noncomputable section

open scoped Cardinal

/-!
`targetIndexOmega4` is the ordinal usually written `omega_4`, represented in
Mathlib as the initial ordinal of the fourth infinite cardinal.
-/

abbrev targetIndexOmega : Ordinal.{u} :=
  Ordinal.omega0

abbrev targetIndexOmega4 : Ordinal.{u} :=
  (Cardinal.aleph (4 : Ordinal)).ord

abbrev targetAlephOmega : Cardinal.{u} :=
  Cardinal.aleph targetIndexOmega

abbrev targetAlephOmega4 : Cardinal.{u} :=
  Cardinal.aleph targetIndexOmega4

-- The target proposition, proved in `PcfTransitiveApplications`.
def targetUpperBoundStatement : Prop :=
  (2 : Cardinal.{u}) ^ targetAlephOmega < targetAlephOmega4

-- The standard strong-limit form of Shelah's bound, proved downstream.
def targetConditionalStatement : Prop :=
  Cardinal.IsStrongLimit targetAlephOmega.{u} ->
    targetUpperBoundStatement.{u}

/-! The remaining ambient input is best stated independently of the PCF
    representation.  It is the strict countable-power estimate below
    `aleph_(omega_4)`, required only under the strong-limit premise.  This is
    an explicit mathematical hypothesis, not a project axiom and not a
    theorem supplied by ordinary cardinal arithmetic. -/
def AmbientPowerBoundHypothesis : Prop :=
  Cardinal.IsStrongLimit targetAlephOmega.{u} ->
    (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
      Cardinal.lift.{u + 1} targetAlephOmega4.{u}

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

theorem targetAlephOmega_cof :
    targetAlephOmega.ord.cof = Cardinal.aleph0 := by
  simpa [targetAlephOmega, targetIndexOmega] using
    (Ordinal.cof_toType targetAlephOmega.ord).trans Ordinal.cof_omega0

#print axioms targetAlephOmega_cof

/-! Since `aleph_4` is regular and `aleph_1 < aleph_4`, every set of
ordinal indices of order type `omega_1` lying below `omega_4` has a strict
upper bound which still lies below `omega_4`.  This is the target-specific
ordinal boundedness step used before applying PCF no-holes. -/
theorem exists_strictUpperBound_below_targetIndexOmega4_of_orderType_omega_one
    {X : Set (Ordinal.{u})}
    (hX : X ⊆ Set.Iio targetIndexOmega4.{u})
    (hType : Ordinal.type ((· < ·) : X -> X -> Prop) =
      Ordinal.omega.{u + 1} 1) :
    ∃ i, i < targetIndexOmega4.{u} ∧ ∀ x, x ∈ X -> x < i := by
  have hCardX : #X = Cardinal.aleph (1 : Ordinal.{u + 1}) := by
    have hCard := congrArg Ordinal.card hType
    simpa only [Ordinal.card_type, Ordinal.card_omega] using hCard
  have hAleph14 :
      Cardinal.aleph (1 : Ordinal.{u + 1}) <
        Cardinal.lift.{u + 1} (Cardinal.aleph (4 : Ordinal.{u})) := by
    rw [Cardinal.lift_aleph, Cardinal.aleph_lt_aleph]
    simp
  have hRegular4 : Cardinal.IsRegular
      (Cardinal.aleph (4 : Ordinal.{u})) := by
    simpa using
      Cardinal.isRegular_aleph_add_one (3 : Ordinal.{u})
  have hCof : (Ordinal.lift.{u + 1} targetIndexOmega4.{u}).cof =
      Cardinal.lift.{u + 1} (Cardinal.aleph (4 : Ordinal.{u})) := by
    rw [← Ordinal.lift_cof.{u, u + 1}, hRegular4.cof_ord]
  have hSmall : #X <
      (Ordinal.lift.{u + 1} targetIndexOmega4.{u}).cof := by
    rw [hCof, hCardX]
    exact hAleph14
  let i := sSup ((fun x : Ordinal.{u} => x + 1) '' X)
  have hi : i < targetIndexOmega4.{u} :=
    Ordinal.sSup_add_one_lt_of_lt_cof hSmall (fun x hx => hX hx)
  refine ⟨i, hi, ?_⟩
  intro x hx
  exact (lt_add_one x).trans_le
    (le_csSup
      ⟨targetIndexOmega4.{u}, by
        rintro _ ⟨y, hy, rfl⟩
        exact ((Cardinal.isSuccLimit_ord hRegular4.aleph0_le).add_one_lt
          (hX hy)).le⟩
      (Set.mem_image_of_mem (fun y : Ordinal.{u} => y + 1) hx))

#print axioms
  exists_strictUpperBound_below_targetIndexOmega4_of_orderType_omega_one

/-! A positive aleph index below `omega_4` cannot be a limit when its aleph
is regular.  Indeed, a hypothetical limit index has cardinality below
`aleph_4`, while it is above every finite ordinal; hence its cofinality is
strictly below its own aleph, making that aleph singular. -/
theorem not_isSuccPrelimit_of_regular_aleph_below_targetIndexOmega4
    {delta : Ordinal.{u}}
    (hPos : 0 < delta)
    (hDelta : delta < targetIndexOmega4.{u})
    (hRegular : Cardinal.IsRegular (Cardinal.aleph delta)) :
    ¬ Order.IsSuccPrelimit delta := by
  intro hPrelimit
  have hLimit : Order.IsSuccLimit delta :=
    Ordinal.isSuccLimit_iff.mpr ⟨hPos.ne', hPrelimit⟩
  have hCardDelta :
      delta.card < Cardinal.aleph (4 : Ordinal.{u}) :=
    Cardinal.lt_ord.mp hDelta
  have hCof4 : delta.cof < Cardinal.aleph (4 : Ordinal.{u}) :=
    (Ordinal.cof_le_card delta).trans_lt hCardDelta
  have hFourDelta : Cardinal.aleph (4 : Ordinal.{u}) <
      Cardinal.aleph delta := by
    apply Cardinal.aleph_lt_aleph.mpr
    exact Ordinal.natCast_lt_of_isSuccLimit hLimit 4
  have hSingular : Cardinal.IsSingular (Cardinal.aleph delta) :=
    Cardinal.isSingular_aleph_iff.mpr
      ⟨hLimit, hCof4.trans hFourDelta⟩
  exact hRegular.not_isSingular hSingular

#print axioms
  not_isSuccPrelimit_of_regular_aleph_below_targetIndexOmega4

theorem targetAlephOmega_konig_lower_bound :
    targetAlephOmega <
      targetAlephOmega ^ targetAlephOmega.ord.cof :=
  Cardinal.lt_power_cof_ord targetAlephOmega_aleph0_le

theorem targetAlephOmega_konig_lower_bound_aleph0 :
    targetAlephOmega < targetAlephOmega ^ Cardinal.aleph0 := by
  simpa only [targetAlephOmega_cof] using
    targetAlephOmega_konig_lower_bound

#print axioms targetAlephOmega_konig_lower_bound_aleph0

end

end PcfProject
