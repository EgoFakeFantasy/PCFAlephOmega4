import PcfProject.Generators
import PcfProject.CanonicalPcf
import Mathlib.Data.Set.FiniteExhaustion

/-!
# Countable PCF sets and finite filtrations

This module develops the set-theoretic bookkeeping used to reduce a countable
PCF problem to bounded finite layers.  It proves preservation of countability,
progressiveness, regularity, and bounds under the subset, finite-union, and
tail operations used later in the `aleph_omega` argument.

For a countable indexed union, the owner map and its pushed-forward ideal
separate the principal case from the genuinely nonprincipal one.  In the
nonprincipal case the same true-cofinality witness restricts to every strict
tail.  No equality between the PCF of an arbitrary infinite union and the
union of its component PCFs is asserted.

Only the concrete countability, regularity, boundedness, and tail lemmas used
by later modules are retained; no abstract filtration certificate or general
countable-PCF stitching principle is assumed here.
-/

namespace PcfProject

universe u v w x

def BoundedBy
    (A : CardSet.{u})
    (bound : Cardinal.{u}) : Prop :=
  forall theta, A theta -> theta < bound

def PcfBoundedBy
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u})
    (bound : Cardinal.{u}) : Prop :=
  forall theta, R.pcf A theta -> theta < bound

def BelowAlephOmega
    (A : CardSet.{u}) : Prop :=
  BoundedBy A targetAlephOmega

def PcfBelowAlephOmega4
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) : Prop :=
  PcfBoundedBy R A targetAlephOmega4

def CountableCardSet
    (A : CardSet.{u}) : Prop :=
  Cardinal.mk { theta : Cardinal.{u} // A theta } <= Cardinal.aleph0

theorem countableCardSet_iff_countable
    {A : CardSet.{u}} :
    CountableCardSet A <->
      Countable { theta : Cardinal.{u} // A theta } :=
  Cardinal.mk_le_aleph0_iff

/-! A countable cardinal set has a canonical coordinate index small in the
cardinal universe.  This is the universe bridge needed by the concrete
quotient-to-scale construction; it does not assert any PCF upper bound. -/
theorem cardinalIndex_small_of_countableCardSet
    {A : CardSet.{u}}
    (hCountable : CountableCardSet A) :
    Small.{u} (CardinalIndex A) := by
  letI : Countable (CardinalIndex A) :=
    countableCardSet_iff_countable.mp hCountable
  exact Countable.toSmall _

#print axioms cardinalIndex_small_of_countableCardSet

theorem countableCardSet_iff_set_countable
    {A : CardSet.{u}} :
    CountableCardSet A <->
      Set.Countable { theta : Cardinal.{u} | A theta } := by
  exact Cardinal.mk_le_aleph0_iff.trans Set.countable_coe_iff

def iUnionCardSet
    {I : Type v}
    (A : I -> CardSet.{u}) : CardSet.{u} :=
  fun theta => exists i, A i theta

theorem countableCardSet_iUnion
    {I : Type v}
    [Countable I]
    (A : I -> CardSet.{u})
    (hCountable : forall i, CountableCardSet (A i)) :
    CountableCardSet (iUnionCardSet A) := by
  rw [countableCardSet_iff_set_countable]
  have hSets : forall i : I,
      ({theta : Cardinal.{u} | A i theta}).Countable := by
    intro i
    exact (countableCardSet_iff_set_countable.mp (hCountable i))
  have hSet :
      {theta : Cardinal.{u} | iUnionCardSet A theta} =
        ⋃ i, {theta : Cardinal.{u} | A i theta} := by
    ext theta
    simp [iUnionCardSet]
  rw [hSet]
  exact Set.countable_iUnion hSets

theorem countableCardSet_singleton
    (theta : Cardinal.{u}) :
    CountableCardSet (singletonCardSet theta) := by
  rw [countableCardSet_iff_set_countable]
  simp [singletonCardSet]

/-! A countable set of coordinates below `aleph_omega` has a genuine ambient
    product bound.  This is only a cardinality estimate for the concrete
    canonical product: it does not identify `pcf A` with the whole product
    and does not use the general countable-PCF theorem. -/
theorem cardinalProductRepresentation_pcf_theta_le_power_of_countable_below_alephOmega
    {A : CardSet.{u}}
    (hCountable : CountableCardSet A)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta) :
    exists J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual /\
      Cardinal.lift.{u + 1} theta <=
        (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 := by
  obtain ⟨J, hUltra, hBound⟩ :=
    cardinalProductRepresentation_pcf_theta_le_power_of_coordinate_bound
      (A := A) (theta := theta) (K := targetAlephOmega) hPcf
      (by
        intro i
        exact Cardinal.lift_le.mpr
          (hBelow i.1 i.property).le)
  have hExponent :
      Cardinal.lift.{u} (Cardinal.mk (CardinalIndex A)) <=
        Cardinal.aleph0 := by
    calc
      Cardinal.lift.{u} (Cardinal.mk (CardinalIndex A)) <=
          Cardinal.lift.{u} Cardinal.aleph0 :=
        Cardinal.lift_le.mpr hCountable
      _ = Cardinal.aleph0 := Cardinal.lift_aleph0
  have hBase :
      Cardinal.lift.{u + 1} targetAlephOmega.{u} ≠ 0 := by
    intro hZero
    have hTargetZero : targetAlephOmega.{u} = 0 :=
      Cardinal.lift_eq_zero.mp hZero
    have hTargetPos : 0 < targetAlephOmega.{u} :=
      Cardinal.aleph0_pos.trans_le targetAlephOmega_aleph0_le
    exact hTargetPos.ne.symm hTargetZero
  have hPower :
      (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^
          Cardinal.lift.{u} (Cardinal.mk (CardinalIndex A)) <=
        (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 := by
    exact Cardinal.power_le_power_left hBase hExponent
  exact ⟨J, hUltra, hBound.trans hPower⟩

#print axioms cardinalProductRepresentation_pcf_theta_le_power_of_countable_below_alephOmega

theorem setOfRegulars_iUnion_of_forall
    {I : Type v}
    (A : I -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i)) :
    SetOfRegulars (iUnionCardSet A) := by
  intro theta hTheta
  obtain ⟨i, hTheta⟩ := hTheta
  exact hRegulars i theta hTheta

/-! Choose one component containing each coordinate of the indexed union.
The choice fibers form an actual partition of the union index, even when the
original component sets overlap. -/
noncomputable def iUnionCardSetOwner
    {I : Type v}
    (A : I -> CardSet.{u})
    (k : CardinalIndex (iUnionCardSet A)) : I :=
  Classical.choose k.property

theorem iUnionCardSetOwner_mem
    {I : Type v}
    (A : I -> CardSet.{u})
    (k : CardinalIndex (iUnionCardSet A)) :
    A (iUnionCardSetOwner A k) k.1 :=
  Classical.choose_spec k.property

/-! Push the union ultrafilter-dual ideal to the family index along the owner
map. A principal index ideal is the easy concentration branch; a nonprincipal
index ideal is the genuine infinite-family remainder. -/
noncomputable def canonicalIUnionIndexIdeal
    {I : Type v}
    (A : I -> CardSet.{u})
    (J : Ideal (CardinalIndex (iUnionCardSet A))) : Ideal I :=
  J.pushforward (iUnionCardSetOwner A)

theorem canonicalIUnionIndexIdeal_isUltrafilterDual
    {I : Type v}
    (A : I -> CardSet.{u})
    {J : Ideal (CardinalIndex (iUnionCardSet A))}
    (hUltra : J.IsUltrafilterDual) :
    (canonicalIUnionIndexIdeal A J).IsUltrafilterDual := by
  exact hUltra.pushforward (iUnionCardSetOwner A)

theorem canonicalIUnion_eventually_component_of_indexIdeal_eq_excludePoint
    {I : Type v}
    (A : I -> CardSet.{u})
    {J : Ideal (CardinalIndex (iUnionCardSet A))}
    (hUltra : J.IsUltrafilterDual)
    {i0 : I}
    (hPrincipal :
      canonicalIUnionIndexIdeal A J = Ideal.excludePoint i0) :
    J.Eventually (fun k => A i0 k.1) := by
  have hOwner :
      J.Eventually (fun k => iUnionCardSetOwner A k = i0) := by
    apply (hUltra.pushforward_eq_excludePoint_iff_eventually_eq
      (iUnionCardSetOwner A) i0).mp
    exact hPrincipal
  exact J.eventually_mono hOwner (by
    intro k hk
    have hMem := iUnionCardSetOwner_mem A k
    simpa only [hk] using hMem)


/-! 对核心尾部论证，只需所有者指标最终越过任意自然数这一直接结论。 -/
/-! For a `Nat`-indexed family, the owner map is unbounded modulo every union
ideal whose pushed-forward index ideal is nonprincipal. -/
theorem canonicalIUnion_eventually_nat_lt_owner_of_nonprincipal_indexIdeal
    (A : Nat -> CardSet.{u})
    {J : Ideal (CardinalIndex (iUnionCardSet A))}
    (hUltra : J.IsUltrafilterDual)
    (hNonprincipal : forall i,
      Not (canonicalIUnionIndexIdeal A J = Ideal.excludePoint i))
    (n : Nat) :
    J.Eventually (fun k => n < iUnionCardSetOwner A k) := by
  have hIndexEventually :
      (canonicalIUnionIndexIdeal A J).Eventually (fun i => n < i) :=
    (canonicalIUnionIndexIdeal_isUltrafilterDual A hUltra)
      |>.eventually_nat_lt_of_forall_ne_excludePoint hNonprincipal n
  change
    (J.pushforward (iUnionCardSetOwner A)).Eventually
      (fun i => n < i) at hIndexEventually
  exact (Ideal.pushforward_eventually_iff
    J (iUnionCardSetOwner A) _).mp hIndexEventually


/-! 以下定义严格尾并，并记录它与全并集之间的直接关系。 -/
/-! The strict tail union of a `Nat`-indexed cardinal-set family. -/
def natTailIUnionCardSet
    (A : Nat -> CardSet.{u})
    (n : Nat) : CardSet.{u} :=
  fun theta => exists m, n < m /\ A m theta

theorem natTailIUnionCardSet_subset_iUnionCardSet
    (A : Nat -> CardSet.{u})
    (n : Nat) :
    SubsetOf (natTailIUnionCardSet A n) (iUnionCardSet A) := by
  intro theta hTheta
  obtain ⟨m, _hnm, hAm⟩ := hTheta
  exact ⟨m, hAm⟩

theorem natTailIUnionCardSet_setOfRegulars
    (A : Nat -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (n : Nat) :
    SetOfRegulars (natTailIUnionCardSet A n) := by
  intro theta hTheta
  obtain ⟨m, _hnm, hAm⟩ := hTheta
  exact hRegulars m theta hAm

theorem natTailIUnionCardSet_subset_of_le
    (A : Nat -> CardSet.{u})
    {n m : Nat}
    (hnm : n <= m) :
    SubsetOf (natTailIUnionCardSet A m)
      (natTailIUnionCardSet A n) := by
  intro theta hTheta
  obtain ⟨k, hmk, hAk⟩ := hTheta
  exact ⟨k, lt_of_le_of_lt hnm hmk, hAk⟩

theorem natTailIUnionCardSet_eq_finsetUnion_Icc_union_tail
    (A : Nat -> CardSet.{u})
    {n m : Nat}
    (hnm : n <= m) :
    natTailIUnionCardSet A n =
      unionCardSet
        (finsetUnionCardSet
          ((Finset.range (m + 1)).filter (fun k => n < k)) A)
        (natTailIUnionCardSet A m) := by
  classical
  funext theta
  apply propext
  constructor
  · rintro ⟨k, hnk, hAk⟩
    by_cases hkm : k <= m
    · exact Or.inl ⟨k, by
        rw [Finset.mem_filter]
        exact ⟨by
          rw [Finset.mem_range]
          exact Nat.lt_succ_iff.mpr hkm, hnk⟩, hAk⟩
    · exact Or.inr ⟨k, Nat.lt_of_not_ge hkm, hAk⟩
  · intro hUnion
    cases hUnion with
    | inl hFinite =>
        obtain ⟨k, hk, hAk⟩ := hFinite
        have hnk : n < k := by
          exact (Finset.mem_filter.mp hk).2
        exact ⟨k, hnk, hAk⟩
    | inr hTail =>
        obtain ⟨k, hmk, hAk⟩ := hTail
        exact ⟨k, lt_of_le_of_lt hnm hmk, hAk⟩

theorem cardinalProductRepresentation_pcf_natTail_eq_finiteDifference_union_tail
    (A : Nat -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    {n m : Nat}
    (hnm : n <= m) :
    cardinalProductRepresentation.pcf (natTailIUnionCardSet A n) =
      unionCardSet
        (finsetUnionCardSet
          ((Finset.range (m + 1)).filter (fun k => n < k))
          (fun i => cardinalProductRepresentation.pcf (A i)))
        (cardinalProductRepresentation.pcf (natTailIUnionCardSet A m)) := by
  rw [natTailIUnionCardSet_eq_finsetUnion_Icc_union_tail A hnm]
  rw [cardinalProductRepresentation_pcf_union
    (finsetUnionCardSet_regulars hRegulars)
    (natTailIUnionCardSet_setOfRegulars A hRegulars m)]
  rw [cardinalProductRepresentation_pcf_finsetUnion
    ((Finset.range (m + 1)).filter (fun k => n < k)) A hRegulars]

theorem cardinalProductRepresentation_pcf_natTail_mono
    (A : Nat -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    {n m : Nat}
    (hnm : n <= m) :
    SubsetOf
      (cardinalProductRepresentation.pcf (natTailIUnionCardSet A m))
      (cardinalProductRepresentation.pcf (natTailIUnionCardSet A n)) := by
  intro theta hTheta
  exact cardinalProductRepresentation_pcf_mono
    (natTailIUnionCardSet_subset_of_le A hnm)
    (natTailIUnionCardSet_setOfRegulars A hRegulars n)
    theta
    hTheta

/-! A nonprincipal index witness is eventually contained in every strict
tail union. -/
theorem canonicalIUnion_eventually_mem_natTail_of_nonprincipal_indexIdeal
    (A : Nat -> CardSet.{u})
    {J : Ideal (CardinalIndex (iUnionCardSet A))}
    (hUltra : J.IsUltrafilterDual)
    (hNonprincipal : forall i,
      Not (canonicalIUnionIndexIdeal A J = Ideal.excludePoint i))
    (n : Nat) :
    J.Eventually (fun k => natTailIUnionCardSet A n k.1) := by
  exact J.eventually_mono
    (canonicalIUnion_eventually_nat_lt_owner_of_nonprincipal_indexIdeal
      A hUltra hNonprincipal n)
    (by
      intro k hOwner
      exact ⟨iUnionCardSetOwner A k, hOwner,
        iUnionCardSetOwner_mem A k⟩)


/-! 给定的非主推前理想可把同一 pcf 见证限制到每个严格尾部；无需额外选择包装。 -/

/-! A concrete PCF witness whose index pushforward is nonprincipal descends
to every strict tail union. The same true-cofinality witness is restricted
along the eventual tail inclusion; no tail PCF bound is assumed. -/
theorem cardinalProductRepresentation_mem_pcf_natTail_of_nonprincipal_indexIdeal
    (A : Nat -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    (J : Ideal (CardinalIndex (iUnionCardSet A)))
    (hUltra : J.IsUltrafilterDual)
    (hTcf : HasTrueCofinality
      (cardinalProductFrame (iUnionCardSet A) J)
      (cardinalScaleLength theta))
    (hNonprincipal : forall i,
      Not (canonicalIUnionIndexIdeal A J = Ideal.excludePoint i))
    (n : Nat) :
    cardinalProductRepresentation.pcf (natTailIUnionCardSet A n) theta :=
  cardinalProductRepresentation_mem_pcf_of_eventually_mem
    (natTailIUnionCardSet_subset_iUnionCardSet A n)
    (setOfRegulars_iUnion_of_forall A hRegulars)
    hRegular
    J
    hUltra
    hTcf
    (canonicalIUnion_eventually_mem_natTail_of_nonprincipal_indexIdeal
      A hUltra hNonprincipal n)

/-! A single nonprincipal union witness therefore represents the same PCF
cardinal on every strict tail.  This quantified form is the interface used by
the later maximum argument. -/
theorem cardinalProductRepresentation_mem_pcf_all_natTails_of_nonprincipal_indexIdeal
    (A : Nat -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    (J : Ideal (CardinalIndex (iUnionCardSet A)))
    (hUltra : J.IsUltrafilterDual)
    (hTcf : HasTrueCofinality
      (cardinalProductFrame (iUnionCardSet A) J)
      (cardinalScaleLength theta))
    (hNonprincipal : forall i,
      Not (canonicalIUnionIndexIdeal A J = Ideal.excludePoint i)) :
    forall n,
      cardinalProductRepresentation.pcf (natTailIUnionCardSet A n) theta := by
  intro n
  exact cardinalProductRepresentation_mem_pcf_natTail_of_nonprincipal_indexIdeal
    A hRegulars hRegular J hUltra hTcf hNonprincipal n

theorem BoundedBy_iUnion_iff
    {I : Type v}
    (A : I -> CardSet.{u})
    (bound : Cardinal.{u}) :
    BoundedBy (iUnionCardSet A) bound <->
      forall i, BoundedBy (A i) bound := by
  constructor
  · intro h i theta hTheta
    exact h theta ⟨i, hTheta⟩
  · intro h theta hTheta
    obtain ⟨i, hTheta⟩ := hTheta
    exact h i theta hTheta

theorem BelowAlephOmega_iUnion_iff
    {I : Type v}
    (A : I -> CardSet.{u}) :
    BelowAlephOmega (iUnionCardSet A) <->
      forall i, BelowAlephOmega (A i) :=
  BoundedBy_iUnion_iff A targetAlephOmega

theorem natTailIUnionCardSet_eq_iUnion_subtype
    (A : Nat -> CardSet.{u})
    (n : Nat) :
    natTailIUnionCardSet A n =
      iUnionCardSet (fun m : {m : Nat // n < m} => A m.1) := by
  funext theta
  apply propext
  constructor
  · rintro ⟨m, hnm, hTheta⟩
    exact ⟨⟨m, hnm⟩, hTheta⟩
  · rintro ⟨m, hTheta⟩
    exact ⟨m.1, m.2, hTheta⟩

theorem natTailIUnionCardSet_countable
    (A : Nat -> CardSet.{u})
    (hCountable : forall i, CountableCardSet (A i))
    (n : Nat) :
    CountableCardSet (natTailIUnionCardSet A n) := by
  rw [natTailIUnionCardSet_eq_iUnion_subtype]
  apply countableCardSet_iUnion
  intro m
  exact hCountable m.1

theorem natTailIUnionCardSet_belowAlephOmega
    (A : Nat -> CardSet.{u})
    (hBelow : forall i, BelowAlephOmega (A i))
    (n : Nat) :
    BelowAlephOmega (natTailIUnionCardSet A n) := by
  rw [natTailIUnionCardSet_eq_iUnion_subtype]
  apply (BelowAlephOmega_iUnion_iff _).mpr
  intro m
  exact hBelow m.1

end PcfProject
