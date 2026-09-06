import PcfProject.PrincipalPcf
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Stage 8: Continuum-control hypothesis interfaces

This file connects an explicit PCF witness above the continuum at
`aleph_omega` to the target upper-bound statement.

The field `continuum_le_witness` is an external mathematical hypothesis. The
theorems below combine it with either the Stage 7 countable PCF interfaces or
the proved principal-ultrafilter PCF bound. The
`...from_mathlib_countable` theorem uses the canonical subtype-cardinality
definition `CountableCardSet`.
The concentrated indexed-union adapter keeps both component bounds and the
ultrafilter concentration premise explicit; it is not a general countable
union result.
The countable-PCF indexed-union assembly likewise keeps the component
structural packages, side conditions, concentration, and continuum witnesses
visible. Its finite-support specialization uses a supported component witness
and the finite-support componentwise bound without finite `CardinalIndex`
instances.
For a finite index type, the finite-cover concentration theorem discharges
only the concentration premise; the component continuum witnesses and all
countable-PCF inputs remain explicit in the resulting target theorem.
-/

namespace PcfProject

universe u v w x

open Cardinal Set Order

noncomputable abbrev ContinuumAtAlephOmega : Cardinal.{u} :=
  (2 : Cardinal.{u}) ^ targetAlephOmega

/-! The continuum at `aleph_omega` dominates the ordinary continuum. This is
the elementary cardinal-arithmetic link between the PCF target and the usual
notation `2 ^ aleph0`; it does not provide the PCF upper bound itself. -/
theorem two_power_aleph0_le_continuumAtAlephOmega :
    (2 : Cardinal.{u}) ^ Cardinal.aleph0 <= ContinuumAtAlephOmega := by
  exact Cardinal.power_le_power_left two_ne_zero targetAlephOmega_aleph0_le

#print axioms two_power_aleph0_le_continuumAtAlephOmega

/-! The countable-exponent power of `aleph_omega` is bounded by the power
    appearing in `ContinuumAtAlephOmega`. This is only cardinal arithmetic:
    the exponent is enlarged from `aleph0` to `aleph_omega`, and the latter
    self-power is identified with the two-power by Cantor arithmetic. It does
    not identify the two cardinals and does not supply the PCF continuum
    bridge. -/
theorem targetAlephOmega_power_aleph0_le_continuumAtAlephOmega :
    targetAlephOmega.{u} ^ Cardinal.aleph0 <= ContinuumAtAlephOmega := by
  calc
    targetAlephOmega.{u} ^ Cardinal.aleph0 <=
        targetAlephOmega.{u} ^ targetAlephOmega.{u} :=
      Cardinal.power_le_power_left
        (by exact (show targetAlephOmega.{u} ≠ 0 from
          (Cardinal.aleph0_pos.trans_le targetAlephOmega_aleph0_le).ne'))
        targetAlephOmega_aleph0_le
    _ = (2 : Cardinal.{u}) ^ targetAlephOmega := by
      exact Cardinal.power_self_eq targetAlephOmega_aleph0_le
    _ = ContinuumAtAlephOmega := rfl

#print axioms targetAlephOmega_power_aleph0_le_continuumAtAlephOmega

/-! A strong-limit coding lemma for the continuum at `aleph_omega`.  Choose a
    cofinal subset of the canonical well-order of `aleph_omega`.  Each initial
    segment has a powerset of cardinality below `aleph_omega`, so a subset of
    the whole ordinal is determined by its traces on the countably cofinal
    family of initial segments.  This is a genuine cardinal-arithmetic proof;
    it does not use any PCF structural theorem. -/
theorem continuumAtAlephOmega_le_targetAlephOmega_power_aleph0_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    ContinuumAtAlephOmega.{u} <=
      targetAlephOmega.{u} ^ Cardinal.aleph0 := by
  let α := targetAlephOmega.ord.ToType
  obtain ⟨s, hsCof, hsCard⟩ := Order.exists_cof_eq α
  have hα : #α = targetAlephOmega := by
    change #(targetAlephOmega.ord.ToType) = targetAlephOmega
    simp [Cardinal.mk_ord_toType]
  have hcof : #s = Cardinal.aleph0 := by
    rw [hsCard]
    change Order.cof α = Cardinal.aleph0
    simpa [α, targetAlephOmega, targetIndexOmega] using
      (Ordinal.cof_toType targetAlephOmega.ord).trans Ordinal.cof_omega0
  let B : s → Type u := fun i => Set (Set.Iic (i : α))
  have hB : ∀ i : s, #(B i) ≤ targetAlephOmega := by
    intro i
    have hOrder : (#α).ord = Ordinal.type (· < · : α → α → Prop) := by
      rw [hα]
      exact (Ordinal.type_toType targetAlephOmega.ord).symm
    have hα0 : Cardinal.aleph0 ≤ #α := by
      rw [hα]
      exact targetAlephOmega_aleph0_le
    have hIic : #(Set.Iic (i : α)) < #α :=
      Cardinal.mk_Iic_lt (i : α) hOrder hα0
    calc
      #(B i) = 2 ^ #(Set.Iic (i : α)) := by
        simp [B, Cardinal.mk_set]
      _ ≤ targetAlephOmega := by
        exact (hStrongLimit.isStrongPrelimit
          (by simpa [hα] using hIic)).le
  let code : Set α → ((i : s) → B i) := fun X i =>
    {y : Set.Iic (i : α) | (y : α) ∈ X}
  have hCode : Function.Injective code := by
    intro X Y hXY
    apply Set.ext
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := hsCof x
      let i' : s := ⟨i, hi⟩
      let y : Set.Iic (i : α) := ⟨x, hxi⟩
      have hy : y ∈ code X i' := by
        change x ∈ X
        exact hx
      have hpoint : code X i' = code Y i' := congrFun hXY i'
      rw [hpoint] at hy
      change x ∈ Y at hy
      exact hy
    · intro hx
      obtain ⟨i, hi, hxi⟩ := hsCof x
      let i' : s := ⟨i, hi⟩
      let y : Set.Iic (i : α) := ⟨x, hxi⟩
      have hy : y ∈ code Y i' := by
        change x ∈ Y
        exact hx
      have hpoint : code X i' = code Y i' := congrFun hXY i'
      rw [← hpoint] at hy
      change x ∈ X at hy
      exact hy
  have hCodeCard : #(Set α) ≤ #((i : s) → B i) :=
    Cardinal.mk_le_of_injective hCode
  have hPi : #((i : s) → B i) ≤ targetAlephOmega ^ #s := by
    rw [Cardinal.mk_pi]
    exact (Cardinal.prod_le_prod _ _ hB).trans_eq
      (Cardinal.prod_const' s targetAlephOmega)
  have hSet : #(Set α) = (2 : Cardinal.{u}) ^ targetAlephOmega := by
    simpa [Cardinal.mk_set, hα]
  have hLeft : (2 : Cardinal.{u}) ^ targetAlephOmega ≤ #(Set α) := hSet.ge
  calc
    (2 : Cardinal.{u}) ^ targetAlephOmega ≤ #(Set α) := hLeft
    _ ≤ #((i : s) → B i) := hCodeCard
    _ ≤ targetAlephOmega ^ #s := hPi
    _ = targetAlephOmega ^ Cardinal.aleph0 := by rw [hcof]

#print axioms continuumAtAlephOmega_le_targetAlephOmega_power_aleph0_of_strongLimit

/-! The preceding two inequalities identify the two powers under the
    strong-limit hypothesis.  Keeping this as a named equality avoids
    repeating the arithmetic sandwich in final-assembly arguments. -/
theorem continuumAtAlephOmega_eq_targetAlephOmega_power_aleph0_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    ContinuumAtAlephOmega.{u} =
      targetAlephOmega.{u} ^ Cardinal.aleph0 := by
  exact le_antisymm
    (continuumAtAlephOmega_le_targetAlephOmega_power_aleph0_of_strongLimit
      hStrongLimit)
    targetAlephOmega_power_aleph0_le_continuumAtAlephOmega

#print axioms continuumAtAlephOmega_eq_targetAlephOmega_power_aleph0_of_strongLimit

/-! Under the strong-limit premise, the two possible formulations of the
    continuum lower bridge are definitionally different but propositionally
    equivalent.  Naming this equivalence keeps later PCF consumers from
    silently reversing the ambient-product inequality. -/
theorem continuumAtAlephOmega_le_iff_targetAlephOmega_power_aleph0_le_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    {theta : Cardinal.{u}} :
    ContinuumAtAlephOmega.{u} <= theta <->
      targetAlephOmega.{u} ^ Cardinal.aleph0 <= theta := by
  rw [continuumAtAlephOmega_eq_targetAlephOmega_power_aleph0_of_strongLimit
    hStrongLimit]

#print axioms
  continuumAtAlephOmega_le_iff_targetAlephOmega_power_aleph0_le_of_strongLimit

/-! The ambient countable-power inequality is a necessary consequence of the
    final target bound. This records the exact arithmetic direction available
    without any PCF theorem. -/
theorem targetUpperBoundStatement_implies_alephOmega_power_aleph0_lt
    (hTarget : targetUpperBoundStatement.{u}) :
    (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
      Cardinal.lift.{u + 1} targetAlephOmega4.{u} := by
  have hTarget' :
      ContinuumAtAlephOmega.{u} < targetAlephOmega4.{u} := by
    change (2 : Cardinal.{u}) ^ targetAlephOmega < targetAlephOmega4
    exact hTarget
  have hUnlifted : targetAlephOmega.{u} ^ Cardinal.aleph0 <
      targetAlephOmega4.{u} :=
    targetAlephOmega_power_aleph0_le_continuumAtAlephOmega.trans_lt hTarget'
  calc
    (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 =
        Cardinal.lift.{u + 1} (targetAlephOmega.{u} ^ Cardinal.aleph0) := by
      rw [Cardinal.lift_power]
      simp only [Cardinal.lift_aleph0]
    _ < Cardinal.lift.{u + 1} targetAlephOmega4.{u} :=
      Cardinal.lift_lt.mpr hUnlifted

#print axioms targetUpperBoundStatement_implies_alephOmega_power_aleph0_lt

/-! The converse arithmetic reduction becomes available under the explicit
    comparison from the continuum at `aleph_omega` to the countable ambient
    power.  This comparison is deliberately a premise: strong limit alone
    does not identify these two powers. -/
theorem targetUpperBoundStatement_of_alephOmega_power_lt_of_continuum_le_power
    (hPower :
      (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
        Cardinal.lift.{u + 1} targetAlephOmega4.{u})
    (hContinuumLePower :
      ContinuumAtAlephOmega.{u} <=
        targetAlephOmega.{u} ^ Cardinal.aleph0) :
    targetUpperBoundStatement.{u} := by
  have hPowerLift :
      Cardinal.lift.{u + 1} (targetAlephOmega.{u} ^ Cardinal.aleph0) <
        Cardinal.lift.{u + 1} targetAlephOmega4.{u} := by
    rw [Cardinal.lift_power]
    simpa only [Cardinal.lift_aleph0] using hPower
  have hPower' :
      targetAlephOmega.{u} ^ Cardinal.aleph0 < targetAlephOmega4.{u} := by
    exact (Cardinal.lift_lt).mp hPowerLift
  have hContinuum : ContinuumAtAlephOmega.{u} < targetAlephOmega4.{u} :=
    hContinuumLePower.trans_lt hPower'
  change ContinuumAtAlephOmega.{u} < targetAlephOmega4.{u}
  exact hContinuum

#print axioms targetUpperBoundStatement_of_alephOmega_power_lt_of_continuum_le_power

theorem targetConditionalStatement_of_alephOmega_power_lt_of_strongLimit_continuum_le_power
    (hPower :
      (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
        Cardinal.lift.{u + 1} targetAlephOmega4.{u})
    (hContinuumLePower :
      Cardinal.IsStrongLimit targetAlephOmega.{u} ->
        ContinuumAtAlephOmega.{u} <=
          targetAlephOmega.{u} ^ Cardinal.aleph0) :
    targetConditionalStatement.{u} := by
  intro hStrongLimit
  exact targetUpperBoundStatement_of_alephOmega_power_lt_of_continuum_le_power
    hPower (hContinuumLePower hStrongLimit)

#print axioms targetConditionalStatement_of_alephOmega_power_lt_of_strongLimit_continuum_le_power

/-! The preceding coding theorem discharges the continuum comparison under the
    strong-limit premise.  Consequently the conditional final statement needs
    only the remaining strict ambient power inequality. -/
theorem targetConditionalStatement_of_alephOmega_power_lt_of_strongLimit
    (hPower :
      (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
        Cardinal.lift.{u + 1} targetAlephOmega4.{u}) :
    targetConditionalStatement.{u} := by
  intro hStrongLimit
  exact targetUpperBoundStatement_of_alephOmega_power_lt_of_continuum_le_power
    hPower
    (continuumAtAlephOmega_le_targetAlephOmega_power_aleph0_of_strongLimit
      hStrongLimit)

#print axioms targetConditionalStatement_of_alephOmega_power_lt_of_strongLimit

/-! Under the strong-limit premise, the conditional target is equivalent to
    the strict ambient countable-power inequality.  The forward direction is
    the necessary arithmetic reduction, while the reverse direction uses the
    genuine strong-limit coding theorem above. -/
theorem targetConditionalStatement_iff_alephOmega_power_lt_of_strongLimit :
    targetConditionalStatement.{u} <->
      (Cardinal.IsStrongLimit targetAlephOmega.{u} ->
        (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
          Cardinal.lift.{u + 1} targetAlephOmega4.{u}) := by
  constructor
  · intro hTarget hStrongLimit
    exact targetUpperBoundStatement_implies_alephOmega_power_aleph0_lt
      (hTarget hStrongLimit)
  · intro hPower hStrongLimit
    exact targetUpperBoundStatement_of_alephOmega_power_lt_of_continuum_le_power
      (hPower hStrongLimit)
      (continuumAtAlephOmega_le_targetAlephOmega_power_aleph0_of_strongLimit
        hStrongLimit)

#print axioms targetConditionalStatement_iff_alephOmega_power_lt_of_strongLimit

/-! Under a supplied strong-limit hypothesis, the lifted ambient inequality
    has the literal unlifted form in the original cardinal universe. -/
theorem targetUpperBoundStatement_iff_alephOmega_power_aleph0_lt_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    targetUpperBoundStatement.{u} <->
      targetAlephOmega.{u} ^ Cardinal.aleph0 < targetAlephOmega4.{u} := by
  have hEq : ContinuumAtAlephOmega.{u} =
      targetAlephOmega.{u} ^ Cardinal.aleph0 :=
    continuumAtAlephOmega_eq_targetAlephOmega_power_aleph0_of_strongLimit
      hStrongLimit
  constructor
  · intro hTarget
    change ContinuumAtAlephOmega.{u} < targetAlephOmega4.{u} at hTarget
    rw [hEq] at hTarget
    exact hTarget
  · intro hPower
    change ContinuumAtAlephOmega.{u} < targetAlephOmega4.{u}
    rw [hEq]
    exact hPower

#print axioms targetUpperBoundStatement_iff_alephOmega_power_aleph0_lt_of_strongLimit

/-! The corresponding conditional target is equivalent to the same unlifted
    arithmetic statement. This is a normal-form reduction; the strict power
    inequality remains an explicit mathematical input. -/
theorem targetConditionalStatement_iff_alephOmega_power_aleph0_lt_of_strongLimit_unlifted :
    targetConditionalStatement.{u} <->
      (Cardinal.IsStrongLimit targetAlephOmega.{u} ->
        targetAlephOmega.{u} ^ Cardinal.aleph0 < targetAlephOmega4.{u}) := by
  constructor
  · intro hTarget hStrongLimit
    exact (targetUpperBoundStatement_iff_alephOmega_power_aleph0_lt_of_strongLimit
      hStrongLimit).mp (hTarget hStrongLimit)
  · intro hPower hStrongLimit
    exact (targetUpperBoundStatement_iff_alephOmega_power_aleph0_lt_of_strongLimit
      hStrongLimit).mpr (hPower hStrongLimit)

#print axioms
  targetConditionalStatement_iff_alephOmega_power_aleph0_lt_of_strongLimit_unlifted

/-! The lifted formulation used by the quotient/product estimates is exactly
    the ambient-power hypothesis from `CardinalArithmetic`.  Keeping this
    equivalence named makes the final interface independent of whether a
    caller works with lifted or unlifted cardinals. -/
theorem targetConditionalStatement_iff_ambientPowerBoundHypothesis :
    targetConditionalStatement.{u} <-> AmbientPowerBoundHypothesis.{u} := by
  exact targetConditionalStatement_iff_alephOmega_power_lt_of_strongLimit

#print axioms targetConditionalStatement_iff_ambientPowerBoundHypothesis

theorem ambientPowerBoundHypothesis_of_targetConditionalStatement
    (hTarget : targetConditionalStatement.{u}) :
    AmbientPowerBoundHypothesis.{u} :=
  (targetConditionalStatement_iff_ambientPowerBoundHypothesis).mp hTarget

#print axioms ambientPowerBoundHypothesis_of_targetConditionalStatement

theorem targetConditionalStatement_of_ambientPowerBoundHypothesis
    (hPower : AmbientPowerBoundHypothesis.{u}) :
    targetConditionalStatement.{u} :=
  (targetConditionalStatement_iff_ambientPowerBoundHypothesis).mpr hPower

#print axioms targetConditionalStatement_of_ambientPowerBoundHypothesis

/-! The two difficult arithmetic comparisons may themselves be supplied only
    under the strong-limit premise. This is the fully conditional form of the
    preceding reduction. Neither implication field is inferred here: the
    statement merely keeps the two arithmetic inputs synchronized at the same
    strong-limit hypothesis. -/
theorem targetConditionalStatement_of_strongLimit_power_lt_of_strongLimit_continuum_le_power
    (hPower : Cardinal.IsStrongLimit targetAlephOmega.{u} ->
      (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
        Cardinal.lift.{u + 1} targetAlephOmega4.{u})
    (hContinuumLePower : Cardinal.IsStrongLimit targetAlephOmega.{u} ->
      ContinuumAtAlephOmega.{u} <=
        targetAlephOmega.{u} ^ Cardinal.aleph0) :
    targetConditionalStatement.{u} := by
  intro hStrongLimit
  exact targetUpperBoundStatement_of_alephOmega_power_lt_of_continuum_le_power
    (hPower hStrongLimit)
    (hContinuumLePower hStrongLimit)

#print axioms targetConditionalStatement_of_strongLimit_power_lt_of_strongLimit_continuum_le_power

/-! Under the strong-limit premise, the ordinary continuum is strictly below
    `aleph_omega`. This is the elementary cardinal-arithmetic part of the
    conditional PCF route; it does not identify `2 ^ aleph_omega` with the
    ordinary continuum and does not provide the PCF continuum bridge. -/
theorem two_power_aleph0_lt_targetAlephOmega_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    (2 : Cardinal.{u}) ^ Cardinal.aleph0 < targetAlephOmega := by
  apply hStrongLimit.isStrongPrelimit
  simpa only [targetAlephOmega, targetIndexOmega] using
    (Cardinal.aleph0_lt_aleph.mpr Ordinal.omega0_pos)

#print axioms two_power_aleph0_lt_targetAlephOmega_of_strongLimit

/-! Cantor's theorem gives the unconditional lower edge of the PCF
    continuum bridge. Any witness bounding `ContinuumAtAlephOmega` must lie
    strictly above `aleph_omega`. -/
theorem targetAlephOmega_lt_continuumAtAlephOmega :
    targetAlephOmega < ContinuumAtAlephOmega := by
  exact Cardinal.cantor targetAlephOmega

#print axioms targetAlephOmega_lt_continuumAtAlephOmega

structure PcfControlsContinuum
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) where
  boundWitness : Cardinal.{u}
  witness_mem_pcf : R.pcf A boundWitness
  continuum_le_witness : ContinuumAtAlephOmega <= boundWitness

namespace PcfControlsContinuum

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}

theorem targetAlephOmega_lt_boundWitness
    (H : PcfControlsContinuum R A) :
    targetAlephOmega < H.boundWitness := by
  exact targetAlephOmega_lt_continuumAtAlephOmega.trans_le
    H.continuum_le_witness

noncomputable def finsetUnion
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hNonempty : s.Nonempty)
    (H : forall i, PcfControlsContinuum cardinalProductRepresentation (A i)) :
    PcfControlsContinuum cardinalProductRepresentation
      (FinsetUnionCardSet s A) := by
  classical
  let values : Finset (Cardinal.{u}) :=
    s.image (fun i => (H i).boundWitness)
  have hValues : values.Nonempty := by
    rw [show values = s.image (fun i => (H i).boundWitness) by rfl]
    exact Finset.image_nonempty.mpr hNonempty
  let boundWitness : Cardinal.{u} := values.max' hValues
  refine {
    boundWitness := boundWitness
    witness_mem_pcf := ?_
    continuum_le_witness := ?_
  }
  · rw [cardinalProductRepresentation_pcf_finsetUnion s A hRegulars]
    have hBoundMem : boundWitness ∈ values := Finset.max'_mem values hValues
    obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hBoundMem
    exact ⟨i, hi, by
      simpa [boundWitness, values, hEq] using (H i).witness_mem_pcf⟩
  · obtain ⟨i, hi⟩ := hNonempty
    exact (H i).continuum_le_witness.trans (by
      simpa [boundWitness] using
        Finset.le_max' values (H i).boundWitness
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩))

theorem continuum_bound
    (H : PcfControlsContinuum R A)
    (hPcfBound : PcfBelowAlephOmega4 R A) :
    targetUpperBoundStatement.{u} := by
  have hWitnessLt : H.boundWitness < targetAlephOmega4 :=
    hPcfBound H.boundWitness H.witness_mem_pcf
  change ContinuumAtAlephOmega < targetAlephOmega4
  exact lt_of_le_of_lt H.continuum_le_witness hWitnessLt

theorem continuum_bound_of_finsetUnion
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hNonempty : s.Nonempty)
    (H : forall i, PcfControlsContinuum cardinalProductRepresentation (A i))
    (hBounds : forall i, i ∈ s ->
      PcfBelowAlephOmega4 cardinalProductRepresentation (A i)) :
    targetUpperBoundStatement.{u} :=
  (finsetUnion s A hRegulars hNonempty H).continuum_bound
    ((cardinalProductRepresentation_pcf_below_alephOmega4_finsetUnion_iff
      s A hRegulars).mpr hBounds)

/-! A concentrated indexed union has the analogous conditional continuum
assembly. The nonempty index supplies one component witness; the explicit
concentration hypothesis and component PCF bounds control the whole union.
This is not a countable-union theorem without those hypotheses. -/
theorem continuum_bound_of_iUnion_concentration
    {I : Type v}
    (A : I -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hNonempty : Nonempty I)
    (H : forall i,
      PcfControlsContinuum cardinalProductRepresentation (A i))
    (hConcentration : CanonicalIUnionConcentration A)
    (hBounds : forall i,
      PcfBelowAlephOmega4 cardinalProductRepresentation (A i)) :
    targetUpperBoundStatement.{u} := by
  classical
  let i0 : I := Classical.choice hNonempty
  let HUnion :
      PcfControlsContinuum cardinalProductRepresentation (iUnionCardSet A) :=
    { boundWitness := (H i0).boundWitness
      witness_mem_pcf := by
        exact cardinalProductRepresentation_pcf_mono
          (by
            intro theta hTheta
            exact ⟨i0, hTheta⟩)
          (setOfRegulars_iUnion_of_forall A hRegulars)
          _
          (H i0).witness_mem_pcf
      continuum_le_witness := (H i0).continuum_le_witness }
  exact HUnion.continuum_bound
    (cardinalProductRepresentation_pcf_below_alephOmega4_of_iUnion_concentration
      A hRegulars hConcentration hBounds)

theorem continuum_bound_from_mathlib_countable_iUnion_concentration
    {I : Type v}
    (A : I -> CardSet.{u})
    (Hcount : MathlibCountablePcfBoundHypothesis
      cardinalProductRepresentation.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hNonempty : Nonempty I)
    (Hcontinuum : forall i,
      PcfControlsContinuum cardinalProductRepresentation (A i))
    (hConcentration : CanonicalIUnionConcentration A)
    (hStructural : forall i,
      PcfStructuralHypotheses cardinalProductRepresentation.{u} (A i))
    (hCountable : forall i, CountableCardSet (A i))
    (hProgressive : forall i, ProgressiveCardSet (A i))
    (hBelow : forall i, BelowAlephOmega (A i)) :
    targetUpperBoundStatement.{u} := by
  classical
  let i0 : I := Classical.choice hNonempty
  let HUnion :
      PcfControlsContinuum cardinalProductRepresentation (iUnionCardSet A) :=
    { boundWitness := (Hcontinuum i0).boundWitness
      witness_mem_pcf := by
        exact cardinalProductRepresentation_pcf_mono
          (by
            intro theta hTheta
            exact ⟨i0, hTheta⟩)
          (setOfRegulars_iUnion_of_forall A hRegulars)
          _
          (Hcontinuum i0).witness_mem_pcf
      continuum_le_witness := (Hcontinuum i0).continuum_le_witness }
  exact HUnion.continuum_bound
    (MathlibCountablePcfBoundHypothesis.pcf_below_alephOmega4_of_iUnion_concentration
      Hcount
      A
      hConcentration
      hStructural
      hCountable
      hProgressive
      hRegulars
      hBelow)

/-! For a finite nonempty index type, the finite-cover theorem supplies the
concentration needed by the indexed-union continuum assembly. Component
continuum witnesses and every countable-PCF side condition remain explicit. -/
theorem continuum_bound_from_mathlib_countable_finite_index_iUnion
    {I : Type v}
    [Finite I]
    (A : I -> CardSet.{u})
    (Hcount : MathlibCountablePcfBoundHypothesis
      cardinalProductRepresentation.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hNonempty : Nonempty I)
    (Hcontinuum : forall i,
      PcfControlsContinuum cardinalProductRepresentation (A i))
    (hStructural : forall i,
      PcfStructuralHypotheses cardinalProductRepresentation.{u} (A i))
    (hCountable : forall i, CountableCardSet (A i))
    (hProgressive : forall i, ProgressiveCardSet (A i))
    (hBelow : forall i, BelowAlephOmega (A i)) :
    targetUpperBoundStatement.{u} :=
  continuum_bound_from_mathlib_countable_iUnion_concentration
    A
    Hcount
    hRegulars
    hNonempty
    Hcontinuum
    (canonicalIUnionConcentration_of_finite_index A)
    hStructural
    hCountable
    hProgressive
    hBelow

/-! The finite-support form supplies concentration and the component bounds
without requiring finite `CardinalIndex` instances. A supported component
provides the continuum witness that is lifted to the indexed union. -/
theorem continuum_bound_from_mathlib_countable_finite_support_iUnion
    {I : Type v}
    (s : Finset I)
    (A : I -> CardSet.{u})
    (Hcount : MathlibCountablePcfBoundHypothesis
      cardinalProductRepresentation.{u})
    (hNonempty : s.Nonempty)
    (Hcontinuum : forall i, Membership.mem s i ->
      PcfControlsContinuum cardinalProductRepresentation (A i))
    (hOutside : forall i, Not (Membership.mem s i) ->
      forall theta, Not (A i theta))
    (hStructural : forall i, Membership.mem s i ->
      PcfStructuralHypotheses cardinalProductRepresentation.{u} (A i))
    (hCountable : forall i, Membership.mem s i -> CountableCardSet (A i))
    (hProgressive : forall i, Membership.mem s i -> ProgressiveCardSet (A i))
    (hRegulars : forall i, Membership.mem s i -> SetOfRegulars (A i))
    (hBelow : forall i, Membership.mem s i -> BelowAlephOmega (A i)) :
    targetUpperBoundStatement.{u} := by
  classical
  have hRegularsAll : forall i, SetOfRegulars (A i) := by
    intro i theta hTheta
    by_cases hi : Membership.mem s i
    · exact hRegulars i hi theta hTheta
    · exact False.elim ((hOutside i hi theta) hTheta)
  obtain ⟨i0, hi0⟩ := hNonempty
  let HUnion :
      PcfControlsContinuum cardinalProductRepresentation (iUnionCardSet A) :=
    { boundWitness := (Hcontinuum i0 hi0).boundWitness
      witness_mem_pcf := by
        exact cardinalProductRepresentation_pcf_mono
          (by
            intro theta hTheta
            exact ⟨i0, hTheta⟩)
          (setOfRegulars_iUnion_of_forall A hRegularsAll)
          _
          (Hcontinuum i0 hi0).witness_mem_pcf
      continuum_le_witness := (Hcontinuum i0 hi0).continuum_le_witness }
  exact HUnion.continuum_bound
    (Hcount.pcf_below_alephOmega4_of_finite_support
      s A hOutside hStructural hCountable hProgressive hRegulars hBelow)

noncomputable def finsetUnion_of_forall
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hNonempty : s.Nonempty)
    (H : forall i, i ∈ s ->
      PcfControlsContinuum cardinalProductRepresentation (A i)) :
    PcfControlsContinuum cardinalProductRepresentation
      (FinsetUnionCardSet s A) := by
  classical
  let κ := {i : ι // i ∈ s}
  letI : Nonempty κ := by
    obtain ⟨i, hi⟩ := hNonempty
    exact ⟨⟨i, hi⟩⟩
  letI : Fintype κ := Fintype.ofFinite κ
  let Hκ : forall i : κ,
      PcfControlsContinuum cardinalProductRepresentation (A i.1) := by
    intro i
    exact H i.1 i.2
  let HUnion := finsetUnion
    (Finset.univ : Finset κ)
    (fun i => A i.1)
    (fun i => hRegulars i.1)
    Finset.univ_nonempty
    Hκ
  have hSetEq :
      FinsetUnionCardSet (Finset.univ : Finset κ) (fun i => A i.1) =
        FinsetUnionCardSet s A := by
    funext theta
    apply propext
    constructor
    · rintro ⟨i, _hi, hAi⟩
      exact ⟨i.1, i.2, hAi⟩
    · rintro ⟨i, hi, hAi⟩
      exact ⟨⟨i, hi⟩, Finset.mem_univ _, hAi⟩
  rw [hSetEq] at HUnion
  exact HUnion

theorem continuum_bound_of_finsetUnion_of_forall
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hNonempty : s.Nonempty)
    (H : forall i, i ∈ s ->
      PcfControlsContinuum cardinalProductRepresentation (A i))
    (hBounds : forall i, i ∈ s ->
      PcfBelowAlephOmega4 cardinalProductRepresentation (A i)) :
    targetUpperBoundStatement.{u} :=
  (finsetUnion_of_forall s A hRegulars hNonempty H).continuum_bound
    ((cardinalProductRepresentation_pcf_below_alephOmega4_finsetUnion_iff
      s A hRegulars).mpr hBounds)

theorem continuum_bound_from_countable
    (H : PcfControlsContinuum R A)
    (Hcount : CountablePcfBoundHypothesis R)
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : Hcount.Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    targetUpperBoundStatement.{u} :=
  H.continuum_bound
    (Hcount.pcf_below_alephOmega4
      Hstruct
      hCountable
      hProgressive
      hRegulars
      hBelow)

theorem continuum_bound_from_mathlib_countable
    (H : PcfControlsContinuum R A)
    (Hcount : MathlibCountablePcfBoundHypothesis R)
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : CountableCardSet A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    targetUpperBoundStatement.{u} :=
  H.continuum_bound
    (Hcount.pcf_below_alephOmega4
      Hstruct
      hCountable
      hProgressive
      hRegulars
      hBelow)

theorem continuum_bound_from_mathlib_countable_of_aleph0_lt
    (H : PcfControlsContinuum R A)
    (Hcount : MathlibCountablePcfBoundHypothesis R)
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : CountableCardSet A)
    (hUncountable :
      forall theta, A theta -> Cardinal.aleph0 < theta)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    targetUpperBoundStatement.{u} :=
  H.continuum_bound
    (Hcount.pcf_below_alephOmega4_of_aleph0_lt
      Hstruct
      hCountable
      hUncountable
      hRegulars
      hBelow)

/-- Principalization supplies the needed PCF bound directly, so a continuum
control witness yields the target upper bound without a countable-PCF
hypothesis, structural maximum, countability, or progressiveness. -/
theorem continuum_bound_of_principalUltrafilters
    (H : PcfControlsContinuum cardinalProductRepresentation A)
    (hRegulars : SetOfRegulars A)
    (hPrincipal : PrincipalUltrafiltersOn A)
    (hBelow : BelowAlephOmega A) :
    targetUpperBoundStatement.{u} :=
  H.continuum_bound
    (cardinalProductRepresentation_pcf_below_alephOmega4_of_principalUltrafilters
      hRegulars hPrincipal hBelow)

end PcfControlsContinuum

end PcfProject
