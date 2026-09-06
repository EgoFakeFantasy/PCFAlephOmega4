import PcfProject.Generators
import PcfProject.CanonicalPcf
import Mathlib.Data.Set.FiniteExhaustion

/-!
# Stage 7: Countable PCF bound hypothesis interfaces

This file states the countable PCF bound and related max-pcf consequences as
explicit hypotheses over the Mathlib-cardinal Stage 5/6 interfaces.

It does not prove Shelah's countable PCF theorem. The names use `Hypothesis`
rather than `Theorem` on purpose: callers must supply the hard mathematical
bound before the projection lemmas in this file can be used. The legacy
interfaces allow a caller-supplied countability predicate; the
`MathlibCountablePcfBoundHypothesis` interface fixes countability to the
cardinality of the subtype of members. Both interfaces explicitly require
`ProgressiveCardSet A`; this standard PCF input is not silently inferred from
countability alone. The module also proves subset transfer for the routine
countability, progressiveness, regularity, and boundedness side conditions;
these transfers do not prove the reverse PCF inclusion.
The module also records an explicit `CanonicalIUnionConcentration` premise.
Under it, the canonical PCF of an indexed union is proved equal to the union
of the component PCF sets, and component `aleph_(omega_4)` bounds transfer to
the union. This premise is automatic for the finite partition argument but
is not supplied for arbitrary infinite unions.
For the general indexed case, `iUnionCardSetOwner` assigns each union
coordinate to one containing component and `canonicalIUnionIndexIdeal`
pushes the product ideal to the family index. The principal pushforward branch
is proved to concentrate; the exact remaining obligation is the explicitly
named nonprincipal-index concentration condition. In that nonprincipal branch,
the union ideal is proved to eventually avoid any finite set of owner fibers;
for `Nat`-indexed families the owner is consequently unbounded modulo the
union ideal. A concrete nonprincipal product/tcf witness is then restricted to
every strict tail union, proving PCF membership on each tail.
The tail sets are regular under componentwise regularity, are reverse-nested,
and their canonical PCF sets are reverse-monotone.
The componentwise closure of the supplied Mathlib countable-PCF hypothesis is
also explicit: it applies the hypothesis to every component before using the
union equality. Its finite-support specialization does not require finite
`CardinalIndex` instances: it invokes the supplied bound on support components
and uses explicit outside-support emptiness for the remaining components.
The same finite-support layer can combine already supplied component maximum
witnesses into a union maximum, again without finite `CardinalIndex` premises.
For arbitrary concentrated indexed unions, the analogous maximum constructor
requires an explicit greatest-component condition, and the accompanying iff
theorem proves that this condition is also necessary when all component
maxima are supplied.
The weaker dominating-component iff criterion does not require maxima for the
other components.
It is also connected pointwise to the canonical below/at-most filtration:
the union has a critical jump at a threshold exactly when that threshold is a
dominating component maximum.
For a genuinely finite index type, concentration is proved automatically by
the finite-cover ultrafilter argument; the corresponding PCF union and
critical-threshold corollaries do not require a separately supplied
concentration premise. The finite-index maximum criterion has the same
scope and still exposes the local maximum and domination conditions. The
componentwise supplied countable-PCF bound also transfers to the finite
indexed union without a separate concentration input.
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

theorem BoundedBy_of_subset
    {A B : CardSet.{u}}
    {bound : Cardinal.{u}}
    (hBA : SubsetOf B A)
    (hBounded : BoundedBy A bound) :
    BoundedBy B bound := by
  intro theta hTheta
  exact hBounded theta (hBA theta hTheta)

theorem BelowAlephOmega_of_subset
    {A B : CardSet.{u}}
    (hBA : SubsetOf B A)
    (hBelow : BelowAlephOmega A) :
    BelowAlephOmega B :=
  BoundedBy_of_subset hBA hBelow

def PcfBelowAlephOmega4
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) : Prop :=
  PcfBoundedBy R A targetAlephOmega4

/-! A four-step finite-generator certificate is a direct local route to a
    uniform PCF bound.  The certificate itself carries the nontrivial
    coverage assertion; the lemmas below only perform the bound extraction.
    This is useful for recording the exact output of a future Shelah-style
    generator argument without confusing that output with the argument that
    constructs the certificate. -/

theorem pcf_below_alephOmega4_of_finiteGeneratorClosureCertificate
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    {G : GeneratorSystem R A}
    {theta : Cardinal.{u}}
    (C : GeneratorSystem.FiniteGeneratorClosureCertificate G theta)
    (hTheta : theta < targetAlephOmega4) :
    PcfBelowAlephOmega4 R A := by
  intro beta hBeta
  exact C.pcf_lt_of_closure_bound hTheta beta hBeta

theorem pcf_below_alephOmega4_of_forall_finiteGeneratorClosureCertificates
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (hCertificate : forall beta, R.pcf A beta ->
      exists G : GeneratorSystem R A,
        exists theta : Cardinal.{u},
          theta < targetAlephOmega4 /\
          exists C : GeneratorSystem.FiniteGeneratorClosureCertificate
            G theta,
            R.pcf A theta) :
    PcfBelowAlephOmega4 R A := by
  intro beta hBeta
  obtain ⟨G, theta, hTheta, C, hPcfTheta⟩ :=
    hCertificate beta hBeta
  exact (C.pcf_le hBeta).trans_lt hTheta

/-! A fixed generator system is enough for the pointwise certificate route.
    This is the form closest to the usual PCF closure argument: once one
    supplies, for each displayed PCF value, a finite closure threshold below
    `aleph_(omega_4)`, the uniform PCF bound follows.  The generator system and
    the closure witnesses are both explicit inputs. -/
theorem pcf_below_alephOmega4_of_fixed_generator_finiteGeneratorClosureCertificates
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (G : GeneratorSystem R A)
    (hCertificate : forall beta, R.pcf A beta ->
      exists theta : Cardinal.{u},
        theta < targetAlephOmega4 /\
        Nonempty (GeneratorSystem.FiniteGeneratorClosureCertificate G theta)) :
    PcfBelowAlephOmega4 R A := by
  intro beta hBeta
  obtain ⟨theta, hTheta, hC⟩ := hCertificate beta hBeta
  obtain ⟨C⟩ := hC
  exact (C.pcf_le hBeta).trans_lt hTheta

#print axioms
  pcf_below_alephOmega4_of_fixed_generator_finiteGeneratorClosureCertificates

/-! With a fixed generator system, the certificate interface has an exact
    threshold formulation.  The certificate threshold is a non-strict bound
    for the whole PCF set, so the statement deliberately asks for one such
    threshold below the displayed strict bound.  This makes the remaining
    maximum/threshold issue explicit instead of deriving it from a merely
    pointwise strict bound. -/
theorem GeneratorSystem.exists_strict_finiteGeneratorClosureCertificate_iff_exists_pcf_bound_below
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (G : GeneratorSystem R A)
    {bound : Cardinal.{u}} :
    (exists theta : Cardinal.{u},
      theta < bound /\
      Nonempty (GeneratorSystem.FiniteGeneratorClosureCertificate G theta)) <->
      (exists theta : Cardinal.{u},
        theta < bound /\
        forall beta, R.pcf A beta -> beta <= theta) := by
  constructor
  · rintro ⟨theta, hTheta, hCertificate⟩
    refine ⟨theta, hTheta, ?_⟩
    exact (GeneratorSystem.FiniteGeneratorClosureCertificate.exists_iff_pcf_bounded
      G).mp hCertificate
  · rintro ⟨theta, hTheta, hBound⟩
    refine ⟨theta, hTheta, ?_⟩
    exact (GeneratorSystem.FiniteGeneratorClosureCertificate.exists_iff_pcf_bounded
      G).mpr hBound

#print axioms
  GeneratorSystem.exists_strict_finiteGeneratorClosureCertificate_iff_exists_pcf_bound_below

/-! The preceding pointwise certificate route can be packaged as the exact
    PCF-bound statement expected by a countable-PCF consumer.  The ordinary
    countability, progressiveness, regularity, and boundedness premises remain
    explicit so this adapter cannot be mistaken for the general countable-PCF
    theorem. -/

def FiniteGeneratorClosureBoundStatement
    (R : PcfRepresentation.{u, v, w, x})
    (Countable : CardSet.{u} -> Prop) : Prop :=
  forall {A : CardSet.{u}},
    Countable A ->
    ProgressiveCardSet A ->
    SetOfRegulars A ->
    BelowAlephOmega A ->
    (forall beta, R.pcf A beta ->
      exists G : GeneratorSystem R A,
        exists theta : Cardinal.{u},
          theta < targetAlephOmega4 /\
          exists C : GeneratorSystem.FiniteGeneratorClosureCertificate
            G theta,
            R.pcf A theta)

theorem pcf_below_alephOmega4_of_finiteGeneratorClosureBoundStatement
    {R : PcfRepresentation.{u, v, w, x}}
    {Countable : CardSet.{u} -> Prop}
    (hBound : FiniteGeneratorClosureBoundStatement R Countable)
    {A : CardSet.{u}}
    (hCountable : Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 R A := by
  intro beta hBeta
  obtain ⟨G, theta, hTheta, C, hPcfTheta⟩ :=
    hBound hCountable hProgressive hRegulars hBelow beta hBeta
  exact (C.pcf_le hBeta).trans_lt hTheta

theorem pcf_below_alephOmega4_of_mathlib_finiteGeneratorClosureBoundStatement
    {R : PcfRepresentation.{u, v, w, x}}
    (hBound : FiniteGeneratorClosureBoundStatement R CountableCardSet)
    {A : CardSet.{u}}
    (hCountable : CountableCardSet A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 R A :=
  pcf_below_alephOmega4_of_finiteGeneratorClosureBoundStatement
    hBound hCountable hProgressive hRegulars hBelow

theorem PcfStructuralHypotheses.pcf_below_alephOmega4_iff_maxPcf_lt
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A) :
    PcfBelowAlephOmega4 R A <->
      Hstruct.maxPcf.theta < targetAlephOmega4 := by
  constructor
  · intro hBound
    exact hBound Hstruct.maxPcf.theta Hstruct.maxPcf.mem_pcf
  · intro hMaxLt theta hTheta
    exact lt_of_le_of_lt (Hstruct.maxPcf.bounds hTheta) hMaxLt

theorem cardinalProductRepresentation_pcf_below_alephOmega4_finsetUnion_iff
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i)) :
    PcfBelowAlephOmega4 cardinalProductRepresentation
        (FinsetUnionCardSet s A) <->
      forall i, i ∈ s ->
        PcfBelowAlephOmega4 cardinalProductRepresentation (A i) := by
  exact cardinalProductRepresentation_pcf_finsetUnion_bounded_iff
    s A hRegulars targetAlephOmega4

theorem BoundedBy_finsetUnion_iff
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (bound : Cardinal.{u}) :
    BoundedBy (FinsetUnionCardSet s A) bound <->
      forall i, i ∈ s -> BoundedBy (A i) bound := by
  classical
  constructor
  · intro h i hi theta hTheta
    exact h theta ⟨i, hi, hTheta⟩
  · intro h theta hTheta
    obtain ⟨i, hi, hTheta⟩ := hTheta
    exact h i hi theta hTheta

theorem BelowAlephOmega_finsetUnion_iff
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u}) :
    BelowAlephOmega (FinsetUnionCardSet s A) <->
      forall i, i ∈ s -> BelowAlephOmega (A i) :=
  BoundedBy_finsetUnion_iff s A targetAlephOmega

theorem cardinalProductRepresentation_hasMaxPcf_finsetUnion_of_forall_nonempty
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hMax : forall i, i ∈ s ->
      HasMaxPcf cardinalProductRepresentation (A i)) :
    s.Nonempty ->
      HasMaxPcf cardinalProductRepresentation (FinsetUnionCardSet s A) := by
  intro hNonempty
  exact cardinalProductRepresentation_hasMaxPcf_finsetUnion_of_forall
    s A hRegulars hNonempty hMax

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

/-! On an infinite countable set of uncountable regular cardinals, the Zorn
nonprincipal ultrafilter quotient has a genuine scale and therefore realizes
a regular canonical PCF value above `aleph0`.  This is scale existence only,
not the countable-PCF upper theorem. -/
theorem cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_aleph0_of_countableCardSet
    {A : CardSet.{u}}
    [Infinite (CardinalIndex A)]
    (hCountable : CountableCardSet A)
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta) :
    exists theta : Cardinal.{u},
      exists J : Ideal (CardinalIndex A),
        Cardinal.IsRegular theta /\
          J.IsUltrafilterDual /\
          (forall i, Not (J = Ideal.excludePoint i)) /\
          HasTrueCofinality
            (cardinalProductFrame A J)
            (cardinalScaleLength theta) /\
          cardinalProductRepresentation.pcf A theta /\
          Cardinal.aleph0 < theta := by
  exact
    cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_aleph0_of_small_cardinalIndex
      hRegulars
      (cardinalIndex_small_of_countableCardSet hCountable)
      hAleph0

#print axioms
  cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_aleph0_of_countableCardSet

theorem countableCardSet_iff_set_countable
    {A : CardSet.{u}} :
    CountableCardSet A <->
      Set.Countable { theta : Cardinal.{u} | A theta } := by
  exact Cardinal.mk_le_aleph0_iff.trans Set.countable_coe_iff

theorem countableCardSet_mono
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hB : CountableCardSet B) :
    CountableCardSet A :=
  (Cardinal.mk_subtype_mono hAB).trans hB

theorem countableProgressiveRegularBelow_of_subset
    {A B : CardSet.{u}}
    (hBA : SubsetOf B A)
    (hCountable : CountableCardSet A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    CountableCardSet B /\
      ProgressiveCardSet B /\
      SetOfRegulars B /\
      BelowAlephOmega B := by
  exact ⟨countableCardSet_mono hBA hCountable,
    progressiveCardSet_of_subset hBA hProgressive,
    setOfRegulars_of_subset hBA hRegulars,
    BelowAlephOmega_of_subset hBA hBelow⟩

theorem countableCardSet_empty :
    CountableCardSet emptyCardSet := by
  rw [countableCardSet_iff_set_countable]
  simpa [emptyCardSet] using
    (Set.countable_empty : (Set (Cardinal.{u})).Countable)

theorem countableCardSet_union
    {A B : CardSet.{u}}
    (hA : CountableCardSet A)
    (hB : CountableCardSet B) :
    CountableCardSet (UnionCardSet A B) := by
  rw [countableCardSet_iff_set_countable] at hA hB ⊢
  have hUnion :
      Set.Countable
        ({theta : Cardinal.{u} | A theta} ∪
          {theta : Cardinal.{u} | B theta}) :=
    hA.union hB
  have hSet :
      {theta : Cardinal.{u} | UnionCardSet A B theta} =
        {theta : Cardinal.{u} | A theta} ∪
          {theta : Cardinal.{u} | B theta} := by
    ext theta
    simp [UnionCardSet]
  rw [hSet]
  exact hUnion

theorem countableCardSet_finsetUnion_iff
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u}) :
    CountableCardSet (FinsetUnionCardSet s A) <->
      forall i, i ∈ s -> CountableCardSet (A i) := by
  classical
  constructor
  · intro h i hi
    exact countableCardSet_mono
      (by
        intro theta hTheta
        exact ⟨i, hi, hTheta⟩)
      h
  · intro h
    induction s using Finset.induction_on with
    | empty =>
        rw [finsetUnionCardSet_empty]
        exact countableCardSet_empty
    | @insert i s hi ih =>
        rw [finsetUnionCardSet_insert]
        apply countableCardSet_union
        · exact h i (Finset.mem_insert_self i s)
        · apply ih
          intro j hj
          exact h j (Finset.mem_insert_of_mem hj)

def iUnionCardSet
    {I : Type v}
    (A : I -> CardSet.{u}) : CardSet.{u} :=
  fun theta => exists i, A i theta

theorem iUnionCardSet_eq_finsetUnion_of_forall_not_mem
    {I : Type v}
    (s : Finset I)
    (A : I -> CardSet.{u})
    (hOutside : forall i, i ∉ s ->
      forall theta, Not (A i theta)) :
    iUnionCardSet A = FinsetUnionCardSet s A := by
  funext theta
  apply propext
  constructor
  · intro hTheta
    obtain ⟨i, hAi⟩ := hTheta
    by_cases hi : i ∈ s
    · exact ⟨i, hi, hAi⟩
    · exact False.elim ((hOutside i hi theta) hAi)
  · intro hTheta
    obtain ⟨i, hi, hAi⟩ := hTheta
    exact ⟨i, hAi⟩

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

theorem countableCardSet_iUnion_iff
    {I : Type v}
    [Countable I]
    (A : I -> CardSet.{u}) :
    CountableCardSet (iUnionCardSet A) <->
      forall i, CountableCardSet (A i) := by
  constructor
  · intro hCountable i
    apply countableCardSet_mono (A := A i) (B := iUnionCardSet A) ?_ hCountable
    intro theta hTheta
    exact ⟨i, hTheta⟩
  · exact countableCardSet_iUnion A

theorem countableCardSet_iUnion_of_finite_support_iff
    {I : Type v}
    (s : Finset I)
    (A : I -> CardSet.{u})
    (hOutside : forall i, i ∉ s ->
      forall theta, Not (A i theta)) :
    CountableCardSet (iUnionCardSet A) <->
      forall i, i ∈ s -> CountableCardSet (A i) := by
  rw [iUnionCardSet_eq_finsetUnion_of_forall_not_mem s A hOutside]
  exact countableCardSet_finsetUnion_iff s A

theorem countableCardSet_singleton
    (theta : Cardinal.{u}) :
    CountableCardSet (singletonCardSet theta) := by
  rw [countableCardSet_iff_set_countable]
  simpa [singletonCardSet] using
    (Set.countable_singleton theta :
      ({theta : Cardinal.{u} | theta = theta}).Countable)

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

/-! The preceding ambient estimate yields a uniform `aleph_(omega_4)` bound
    under the displayed strict power inequality.  The power inequality remains
    explicit; this theorem is not the general countable-PCF upper theorem. -/
theorem cardinalProductRepresentation_pcf_below_targetAlephOmega4_of_countable_below_alephOmega_of_power_lt
    {A : CardSet.{u}}
    (hCountable : CountableCardSet A)
    (hBelow : BelowAlephOmega A)
    (hPower :
      (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
        Cardinal.lift.{u + 1} targetAlephOmega4.{u}) :
    PcfBelowAlephOmega4 cardinalProductRepresentation.{u} A := by
  intro theta hPcf
  obtain ⟨_J, _hUltra, hAmbient⟩ :=
    cardinalProductRepresentation_pcf_theta_le_power_of_countable_below_alephOmega
      hCountable hBelow hPcf
  apply (Cardinal.lift_lt).mp
  exact hAmbient.trans_lt hPower

#print axioms cardinalProductRepresentation_pcf_below_targetAlephOmega4_of_countable_below_alephOmega_of_power_lt

theorem setOfRegulars_iUnion_of_forall
    {I : Type v}
    (A : I -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i)) :
    SetOfRegulars (iUnionCardSet A) := by
  intro theta hTheta
  obtain ⟨i, hTheta⟩ := hTheta
  exact hRegulars i theta hTheta

/-! An explicit concentration hypothesis for an indexed union. For every
canonical ultrafilter-dual ideal on the union of the component cardinal sets,
the hypothesis names a component on which the ideal is eventually
concentrated. Finite unions obtain this property from ultrafilter dichotomy;
an arbitrary infinite union does not. -/
def CanonicalIUnionConcentration
    {I : Type v}
    (A : I -> CardSet.{u}) : Prop :=
  forall J : Ideal (CardinalIndex (iUnionCardSet A)),
    J.IsUltrafilterDual ->
      exists i, J.Eventually (fun k => A i k.1)

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

/-! For singleton fibres, an infinite total union has an explicit
nonprincipal owner-index witness. The Zorn construction supplies a
nonprincipal ideal on the union index; injectivity of the owner map prevents
its pushforward from becoming principal. This constructs only the ideal-level
obstruction, not a scale or a PCF membership witness. -/
theorem exists_nonprincipal_indexIdeal_of_infinite_cardinalIndex_of_subsingleton
    {I : Type v}
    (A : I -> CardSet.{u})
    [Infinite (CardinalIndex (iUnionCardSet A))]
    (hSubsingleton : forall i theta beta,
      A i theta -> A i beta -> theta = beta) :
    exists J : Ideal (CardinalIndex (iUnionCardSet A)),
      J.IsUltrafilterDual /\
        forall i,
          Not (canonicalIUnionIndexIdeal A J = Ideal.excludePoint i) := by
  classical
  have hOwnerInjective :
      Function.Injective (iUnionCardSetOwner A) := by
    intro k l hkl
    apply Subtype.ext
    have hk := iUnionCardSetOwner_mem A k
    have hl := iUnionCardSetOwner_mem A l
    have hl' : A (iUnionCardSetOwner A k) l.1 := by
      rw [hkl]
      exact hl
    exact hSubsingleton (iUnionCardSetOwner A k) k.1 l.1 hk hl'
  obtain ⟨J, hUltra, hNonprincipal⟩ :=
    exists_nonprincipal_ultrafilterDual_ideal
      (I := CardinalIndex (iUnionCardSet A))
  refine ⟨J, hUltra, ?_⟩
  intro i hPrincipal
  change J.pushforward (iUnionCardSetOwner A) = Ideal.excludePoint i at hPrincipal
  obtain ⟨k0, hJPrincipal⟩ :=
    hUltra.isProper.exists_eq_excludePoint_of_pushforward_eq_excludePoint
      hOwnerInjective hPrincipal
  exact hNonprincipal k0 hJPrincipal

#print axioms exists_nonprincipal_indexIdeal_of_infinite_cardinalIndex_of_subsingleton

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
      UnionCardSet
        (FinsetUnionCardSet
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
      UnionCardSet
        (FinsetUnionCardSet
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

theorem canonicalIUnionConcentration_of_finite_support
    {I : Type v}
    (s : Finset I)
    (A : I -> CardSet.{u})
    (hOutside : forall i, Not (Membership.mem s i) ->
      forall theta, Not (A i theta)) :
    CanonicalIUnionConcentration A := by
  intro J hUltra
  have hCover : J.Eventually
      (fun k => exists i, Membership.mem s i /\ A i k.1) := by
    apply J.eventually_of_forall
    intro k
    obtain ⟨i, hAi⟩ := k.property
    by_cases hi : Membership.mem s i
    · exact ⟨i, hi, hAi⟩
    · exact False.elim ((hOutside i hi k.1) hAi)
  obtain ⟨i, hi, hEventually⟩ :=
    hUltra.exists_eventually_of_finset_cover s hCover
  exact ⟨i, hEventually⟩

/-! A genuinely finite index type supplies concentration without a separate
support set. The universal finite family covers every coordinate of the
indexed union, so an ultrafilter-dual ideal is eventually concentrated on one
component. -/
theorem canonicalIUnionConcentration_of_finite_index
    {I : Type v}
    [Finite I]
    (A : I -> CardSet.{u}) :
    CanonicalIUnionConcentration A := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  intro J hUltra
  have hCover : J.Eventually
      (fun k => exists i, Membership.mem (Finset.univ : Finset I) i /\
        A i k.1) := by
    apply J.eventually_of_forall
    intro k
    obtain ⟨i, hAi⟩ := k.property
    exact ⟨i, Finset.mem_univ i, hAi⟩
  obtain ⟨i, _hi, hEventually⟩ :=
    hUltra.exists_eventually_of_finset_cover
      (Finset.univ : Finset I) hCover
  exact ⟨i, hEventually⟩

/-! Under concentration, the canonical PCF of an indexed union is exactly the
indexed union of the component PCF sets. The reverse inclusion is ordinary
canonical monotonicity; the forward inclusion descends the actual product
ideal and true-cofinality witness to the concentrated component. -/
theorem cardinalProductRepresentation_pcf_iUnion_eq_iUnion_pcf_of_concentration
    {I : Type v}
    (A : I -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hConcentration : CanonicalIUnionConcentration A) :
    cardinalProductRepresentation.pcf (iUnionCardSet A) =
      iUnionCardSet (fun i => cardinalProductRepresentation.pcf (A i)) := by
  funext theta
  apply propext
  constructor
  case h.a.mp =>
    intro hTheta
    obtain ⟨hRegular, J, hUltra, hTcf⟩ :=
      (cardinalProductRepresentation_mem_pcf_iff
        (A := iUnionCardSet A) (theta := theta)).mp hTheta
    obtain ⟨i, hEventually⟩ := hConcentration J hUltra
    have hComponent :
        cardinalProductRepresentation.pcf (A i) theta :=
      cardinalProductRepresentation_mem_pcf_of_eventually_mem
        (A := A i)
        (B := iUnionCardSet A)
        (by
          intro beta hBeta
          exact ⟨i, hBeta⟩)
        (setOfRegulars_iUnion_of_forall A hRegulars)
        hRegular J hUltra hTcf hEventually
    exact ⟨i, hComponent⟩
  case h.a.mpr =>
    intro hTheta
    obtain ⟨i, hTheta⟩ := hTheta
    exact cardinalProductRepresentation_pcf_mono
      (by
        intro beta hBeta
        exact ⟨i, hBeta⟩)
      (setOfRegulars_iUnion_of_forall A hRegulars)
      theta hTheta


/-! 集中性把并集上的 pcf 元素送回某个分量，因此逐分量上界可直接传递到整个并集。 -/
theorem cardinalProductRepresentation_pcf_below_alephOmega4_of_iUnion_concentration
    {I : Type v}
    (A : I -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hConcentration : CanonicalIUnionConcentration A)
    (hBounds : forall i,
      PcfBelowAlephOmega4 cardinalProductRepresentation (A i)) :
    PcfBelowAlephOmega4 cardinalProductRepresentation (iUnionCardSet A) := by
  intro theta hTheta
  rw [cardinalProductRepresentation_pcf_iUnion_eq_iUnion_pcf_of_concentration
    A hRegulars hConcentration] at hTheta
  obtain ⟨i, hTheta⟩ := hTheta
  exact hBounds i theta hTheta

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

theorem progressiveCardSet_iUnion_of_countable_of_aleph0_lt
    {I : Type v}
    [Countable I]
    (A : I -> CardSet.{u})
    (hCountable : forall i, CountableCardSet (A i))
    (hUncountable : forall i, forall theta, A i theta ->
      Cardinal.aleph0 < theta) :
    ProgressiveCardSet (iUnionCardSet A) := by
  intro theta hTheta
  obtain ⟨i, hTheta⟩ := hTheta
  apply (countableCardSet_iUnion A hCountable).trans_lt
  have hLift :
      Cardinal.lift.{u + 1} Cardinal.aleph0 <
        Cardinal.lift.{u + 1} theta :=
    Cardinal.lift_lt.mpr (hUncountable i theta hTheta)
  simpa only [Cardinal.lift_aleph0] using hLift

theorem progressiveCardSet_of_countable_of_aleph0_lt
    {A : CardSet.{u}}
    (hCountable : CountableCardSet A)
    (hUncountable : forall theta, A theta -> Cardinal.aleph0 < theta) :
    ProgressiveCardSet A := by
  intro theta hTheta
  apply hCountable.trans_lt
  have hLift :
      Cardinal.lift.{u + 1} Cardinal.aleph0 <
        Cardinal.lift.{u + 1} theta :=
    Cardinal.lift_lt.mpr (hUncountable theta hTheta)
  simpa only [Cardinal.lift_aleph0] using hLift

theorem progressiveCardSet_finsetUnion_of_countable_of_aleph0_lt
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hCountable : forall i, i ∈ s -> CountableCardSet (A i))
    (hUncountable : forall i, i ∈ s ->
      forall theta, A i theta -> Cardinal.aleph0 < theta) :
    ProgressiveCardSet (FinsetUnionCardSet s A) := by
  apply progressiveCardSet_of_countable_of_aleph0_lt
    ((countableCardSet_finsetUnion_iff s A).mpr hCountable)
  intro theta hTheta
  obtain ⟨i, hi, hAi⟩ := hTheta
  exact hUncountable i hi theta hAi

theorem progressiveCardSet_iUnion_of_finite_support_of_countable_of_aleph0_lt
    {I : Type v}
    (s : Finset I)
    (A : I -> CardSet.{u})
    (hCountable : forall i, i ∈ s -> CountableCardSet (A i))
    (hUncountable : forall i, i ∈ s ->
      forall theta, A i theta -> Cardinal.aleph0 < theta)
    (hOutside : forall i, i ∉ s ->
      forall theta, Not (A i theta)) :
    ProgressiveCardSet (iUnionCardSet A) := by
  rw [iUnionCardSet_eq_finsetUnion_of_forall_not_mem s A hOutside]
  exact progressiveCardSet_finsetUnion_of_countable_of_aleph0_lt
    s A hCountable hUncountable

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

theorem natTailIUnionCardSet_eq_iUnion_shift
    (A : Nat -> CardSet.{u})
    (n : Nat) :
    natTailIUnionCardSet A n =
      iUnionCardSet (fun k : Nat => A (n + 1 + k)) := by
  funext theta
  apply propext
  constructor
  · rintro ⟨m, hnm, hTheta⟩
    have hExists : exists k, m = n + 1 + k := by
      exact Nat.exists_eq_add_of_le (Nat.succ_le_iff.mp hnm)
    obtain ⟨k, hk⟩ := hExists
    refine ⟨k, ?_⟩
    change A (n + 1 + k) theta
    simpa only [hk] using hTheta
  · rintro ⟨k, hTheta⟩
    refine ⟨n + 1 + k, ?_, hTheta⟩
    omega

#print axioms natTailIUnionCardSet_eq_iUnion_shift

theorem natTailIUnionCardSet_countable
    (A : Nat -> CardSet.{u})
    (hCountable : forall i, CountableCardSet (A i))
    (n : Nat) :
    CountableCardSet (natTailIUnionCardSet A n) := by
  rw [natTailIUnionCardSet_eq_iUnion_subtype]
  apply countableCardSet_iUnion
  intro m
  exact hCountable m.1

theorem natTailIUnionCardSet_progressive_of_countable_of_aleph0_lt
    (A : Nat -> CardSet.{u})
    (hCountable : forall i, CountableCardSet (A i))
    (hUncountable : forall i, forall theta, A i theta ->
      Cardinal.aleph0 < theta)
    (n : Nat) :
    ProgressiveCardSet (natTailIUnionCardSet A n) := by
  rw [natTailIUnionCardSet_eq_iUnion_subtype]
  apply progressiveCardSet_iUnion_of_countable_of_aleph0_lt
  · intro m
    exact hCountable m.1
  · intro m theta hTheta
    exact hUncountable m.1 theta hTheta

theorem natTailIUnionCardSet_belowAlephOmega
    (A : Nat -> CardSet.{u})
    (hBelow : forall i, BelowAlephOmega (A i))
    (n : Nat) :
    BelowAlephOmega (natTailIUnionCardSet A n) := by
  rw [natTailIUnionCardSet_eq_iUnion_subtype]
  apply (BelowAlephOmega_iUnion_iff _).mpr
  intro m
  exact hBelow m.1

/-! A countable filtration is the set-theoretic skeleton used in the usual
countable-PCF argument.  The cover and monotonicity fields are kept separate
from the PCF stitching field below: the former are elementary closure data,
whereas the latter is the substantive assertion that a global PCF witness is
already visible on one stage. -/
structure CountableCardSetFiltration
    (A : CardSet.{u}) where
  layer : Nat -> CardSet.{u}
  layer_subset : forall n, SubsetOf (layer n) A
  layer_mono : forall {n m}, n <= m -> SubsetOf (layer n) (layer m)
  covered : forall theta, A theta -> exists n, layer n theta
  layer_countable : forall n, CountableCardSet (layer n)
  layer_progressive : forall n, ProgressiveCardSet (layer n)
  layer_aleph0_lt : forall n, forall theta, layer n theta ->
    Cardinal.aleph0 < theta
  layer_regulars : forall n, SetOfRegulars (layer n)
  layer_below : forall n, BelowAlephOmega (layer n)

namespace CountableCardSetFiltration

variable {A : CardSet.{u}}

theorem layer_subset_of_mem
    (F : CountableCardSetFiltration A)
    {n : Nat} {theta : Cardinal.{u}}
    (hTheta : F.layer n theta) :
    A theta :=
  F.layer_subset n theta hTheta

theorem layer_subset_of_le
    (F : CountableCardSetFiltration A)
    {n m : Nat}
    (hnm : n <= m) :
    SubsetOf (F.layer n) (F.layer m) :=
  F.layer_mono hnm

theorem layer_mem_of_mem
    (F : CountableCardSetFiltration A)
    {theta : Cardinal.{u}}
    (hTheta : A theta) :
    exists n, F.layer n theta :=
  F.covered theta hTheta

theorem eq_iUnion_layer
    (F : CountableCardSetFiltration A) :
    iUnionCardSet F.layer = A := by
  funext theta
  apply propext
  constructor
  · intro hTheta
    obtain ⟨n, hTheta⟩ := hTheta
    exact F.layer_subset n theta hTheta
  · intro hTheta
    exact F.covered theta hTheta

theorem countable
    (F : CountableCardSetFiltration A) :
    CountableCardSet A := by
  rw [← F.eq_iUnion_layer]
  exact countableCardSet_iUnion F.layer F.layer_countable

theorem progressive
    (F : CountableCardSetFiltration A) :
    ProgressiveCardSet A := by
  rw [← F.eq_iUnion_layer]
  apply progressiveCardSet_iUnion_of_countable_of_aleph0_lt
  · exact F.layer_countable
  · intro n theta hTheta
    exact F.layer_aleph0_lt n theta hTheta

theorem regulars
    (F : CountableCardSetFiltration A) :
    SetOfRegulars A := by
  rw [← F.eq_iUnion_layer]
  exact setOfRegulars_iUnion_of_forall F.layer F.layer_regulars

theorem below
    (F : CountableCardSetFiltration A) :
    BelowAlephOmega A := by
  rw [← F.eq_iUnion_layer]
  exact (BelowAlephOmega_iUnion_iff F.layer).mpr F.layer_below

end CountableCardSetFiltration

/-! A finite-generator localization witness for a countable filtration.  The
localizer says that each global PCF value is visible on one layer, together
with a finite generator-closure certificate for that layer.  The certificate
is the local bound-producing object; the localization field remains separate
so this definition does not assert the countable-PCF theorem. -/
def CountableFiniteGeneratorClosureLocalization
    (R : PcfRepresentation.{u, v, w, x})
    {A : CardSet.{u}}
    (F : CountableCardSetFiltration A) : Prop :=
  forall {beta}, R.pcf A beta ->
    exists n : Nat,
      exists G : GeneratorSystem R (F.layer n),
      exists theta : Cardinal.{u},
        theta < targetAlephOmega4 /\
        exists C : GeneratorSystem.FiniteGeneratorClosureCertificate G theta,
          R.pcf (F.layer n) beta

theorem pcf_below_alephOmega4_of_countableFiniteGeneratorClosureLocalization
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (F : CountableCardSetFiltration A)
    (hLocalize : CountableFiniteGeneratorClosureLocalization R F) :
    PcfBelowAlephOmega4 R A := by
  intro beta hBeta
  obtain ⟨n, G, theta, hTheta, C, hLayerBeta⟩ :=
    hLocalize hBeta
  exact (C.pcf_le hLayerBeta).trans_lt hTheta

/-! The localizer can be assembled from two independent PCF-specific steps:
stitching a global witness to a layer and supplying a finite closure
certificate for every PCF value on that layer. -/
theorem countableFiniteGeneratorClosureLocalization_of_stitching_of_layer_certificates
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (F : CountableCardSetFiltration A)
    (hStitched : forall {beta}, R.pcf A beta ->
      exists n, R.pcf (F.layer n) beta)
    (hCertificate : forall n beta, R.pcf (F.layer n) beta ->
      exists G : GeneratorSystem R (F.layer n),
        exists theta : Cardinal.{u},
          theta < targetAlephOmega4 /\
          exists C : GeneratorSystem.FiniteGeneratorClosureCertificate G theta,
            R.pcf (F.layer n) beta) :
    CountableFiniteGeneratorClosureLocalization R F := by
  intro beta hBeta
  obtain ⟨n, hLayerBeta⟩ := hStitched hBeta
  obtain ⟨G, theta, hTheta, C, hCertificateBeta⟩ :=
    hCertificate n beta hLayerBeta
  exact ⟨n, G, theta, hTheta, C, hCertificateBeta⟩

#print axioms
  pcf_below_alephOmega4_of_countableFiniteGeneratorClosureLocalization
#print axioms
  countableFiniteGeneratorClosureLocalization_of_stitching_of_layer_certificates

/-! The two PCF-specific parts of the countable argument are now recorded as
a single local output contract.  The filtration is the elementary countable
layering, `pcf_stitched` is the second-representation/localization assertion,
and `layer_certificate` is the finite-generator closure assertion on one
layer.  The latter two fields are intentionally separate: neither follows
from the set-theoretic finite exhaustion alone. -/
structure CountableFiniteGeneratorClosureOutput
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) where
  filtration : CountableCardSetFiltration A
  pcf_stitched : forall {beta}, R.pcf A beta ->
    exists n, R.pcf (filtration.layer n) beta
  layer_certificate : forall n beta, R.pcf (filtration.layer n) beta ->
    exists G : GeneratorSystem R (filtration.layer n),
      exists theta : Cardinal.{u},
        theta < targetAlephOmega4 /\
        exists C : GeneratorSystem.FiniteGeneratorClosureCertificate G theta,
          R.pcf (filtration.layer n) beta

namespace CountableFiniteGeneratorClosureOutput

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}

theorem to_localization
    (O : CountableFiniteGeneratorClosureOutput R A) :
    CountableFiniteGeneratorClosureLocalization R O.filtration :=
  countableFiniteGeneratorClosureLocalization_of_stitching_of_layer_certificates
    O.filtration O.pcf_stitched O.layer_certificate

theorem pcf_below_alephOmega4
    (O : CountableFiniteGeneratorClosureOutput R A) :
    PcfBelowAlephOmega4 R A :=
  pcf_below_alephOmega4_of_countableFiniteGeneratorClosureLocalization
    O.filtration O.to_localization

end CountableFiniteGeneratorClosureOutput

/-! This is the global form of the preceding output contract.  It is the
exact countable-PCF input needed by the Stage 7 bound interface.  In
particular, it does not claim that every countable set admits such an output;
that existence is the substantive Shelah theorem still to be supplied. -/
def CountableFiniteGeneratorClosureOutputStatement
    (R : PcfRepresentation.{u, v, w, x}) : Prop :=
  forall {A : CardSet.{u}},
    CountableCardSet A ->
    ProgressiveCardSet A ->
    SetOfRegulars A ->
    BelowAlephOmega A ->
    Nonempty (CountableFiniteGeneratorClosureOutput R A)

#print axioms CountableFiniteGeneratorClosureOutput.to_localization
#print axioms CountableFiniteGeneratorClosureOutput.pcf_below_alephOmega4


/-! 核心证明只要求过滤本身携带逐层结构、逐层上界和全局 pcf 拼接，不依赖某个特定枚举构造。 -/
structure CountablePcfFiltration
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) extends CountableCardSetFiltration A where
  layer_structural : forall n,
    PcfStructuralHypotheses R (toCountableCardSetFiltration.layer n)
  layer_pcf_bound : forall n,
    PcfBelowAlephOmega4 R (toCountableCardSetFiltration.layer n)
  pcf_stitched : forall {theta},
    R.pcf A theta ->
      exists n, R.pcf (toCountableCardSetFiltration.layer n) theta

namespace CountablePcfFiltration

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}

theorem countableCardSet
    (F : CountablePcfFiltration R A) :
    CountableCardSet A :=
  F.toCountableCardSetFiltration.countable

theorem progressiveCardSet
    (F : CountablePcfFiltration R A) :
    ProgressiveCardSet A :=
  F.toCountableCardSetFiltration.progressive

theorem setOfRegulars
    (F : CountablePcfFiltration R A) :
    SetOfRegulars A :=
  F.toCountableCardSetFiltration.regulars

theorem belowAlephOmega
    (F : CountablePcfFiltration R A) :
    BelowAlephOmega A :=
  F.toCountableCardSetFiltration.below

theorem pcf_below_alephOmega4
    (F : CountablePcfFiltration R A) :
    PcfBelowAlephOmega4 R A := by
  intro theta hTheta
  obtain ⟨n, hTheta⟩ := F.pcf_stitched hTheta
  exact F.layer_pcf_bound n theta hTheta

end CountablePcfFiltration

/-! For the canonical representation, the stitching field has a useful
    extensional form. The forward implication is exactly the PCF-specific
    stitching input; the converse is canonical monotonicity along the layer
    inclusions. -/
theorem cardinalCountablePcfFiltration_pcf_mem_iff
    {A : CardSet.{u}}
    (F : CountablePcfFiltration cardinalProductRepresentation.{u} A)
    {theta : Cardinal.{u}} :
    cardinalProductRepresentation.pcf A theta <->
      exists n, cardinalProductRepresentation.pcf
        (F.toCountableCardSetFiltration.layer n) theta := by
  constructor
  · exact F.pcf_stitched
  · rintro ⟨n, hTheta⟩
    exact cardinalProductRepresentation_pcf_mono
      (F.toCountableCardSetFiltration.layer_subset n)
      F.toCountableCardSetFiltration.regulars
      theta hTheta

#print axioms cardinalCountablePcfFiltration_pcf_mem_iff

theorem cardinalCountablePcfFiltration_pcf_eq_iUnion_layer_pcf
    {A : CardSet.{u}}
    (F : CountablePcfFiltration cardinalProductRepresentation.{u} A) :
    cardinalProductRepresentation.pcf A =
      iUnionCardSet (fun n : Nat =>
        cardinalProductRepresentation.pcf
          (F.toCountableCardSetFiltration.layer n)) := by
  funext theta
  apply propext
  rw [cardinalCountablePcfFiltration_pcf_mem_iff F]
  rfl

#print axioms cardinalCountablePcfFiltration_pcf_eq_iUnion_layer_pcf

/-! A fully assembled countable filtration also gives the finite-generator
output contract.  This direction is deliberately a representation bridge:
the filtration already contains the layer structural packages, the layer
PCF bounds, and the stitching field.  The certificate is made with
`FiniteGeneratorClosureCertificate.of_pcf_bounded`, so it records exactly the
existing layer bound rather than claiming a new finite-support theorem. -/
noncomputable def CountablePcfFiltration.toCountableFiniteGeneratorClosureOutput
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (F : CountablePcfFiltration R A) :
    CountableFiniteGeneratorClosureOutput R A where
  filtration := F.toCountableCardSetFiltration
  pcf_stitched := F.pcf_stitched
  layer_certificate := by
    intro n beta hBeta
    let M : MaxPcfWitness R (F.toCountableCardSetFiltration.layer n) :=
      (F.layer_structural n).maxPcf
    have hM : M.theta < targetAlephOmega4 :=
      F.layer_pcf_bound n M.theta M.mem_pcf
    let C : GeneratorSystem.FiniteGeneratorClosureCertificate
        (F.layer_structural n).generators M.theta :=
      GeneratorSystem.FiniteGeneratorClosureCertificate.of_pcf_bounded
        (F.layer_structural n).generators
        (fun beta hBeta => M.bounds (beta := beta) hBeta)
    exact ⟨(F.layer_structural n).generators, M.theta, hM, C, hBeta⟩

#print axioms
  CountablePcfFiltration.toCountableFiniteGeneratorClosureOutput

#print axioms CountableCardSetFiltration.countable
#print axioms CountableCardSetFiltration.progressive
#print axioms CountableCardSetFiltration.regulars
#print axioms CountableCardSetFiltration.below
#print axioms CountablePcfFiltration.pcf_below_alephOmega4

def CountablePcfBoundStatement
    (R : PcfRepresentation.{u, v, w, x})
    (Countable : CardSet.{u} -> Prop) : Prop :=
  forall {A : CardSet.{u}},
    PcfStructuralHypotheses R A ->
    Countable A ->
    ProgressiveCardSet A ->
    SetOfRegulars A ->
    BelowAlephOmega A ->
    PcfBelowAlephOmega4 R A

def MathlibCountablePcfBoundStatement
    (R : PcfRepresentation.{u, v, w, x}) : Prop :=
  CountablePcfBoundStatement R CountableCardSet

structure CountablePcfBoundHypothesis
    (R : PcfRepresentation.{u, v, w, x}) where
  Countable : CardSet.{u} -> Prop
  bound_from_structural : CountablePcfBoundStatement R Countable

structure MathlibCountablePcfBoundHypothesis
    (R : PcfRepresentation.{u, v, w, x}) where
  bound_from_structural : MathlibCountablePcfBoundStatement R

/-! The ambient strict-power estimate is already enough to build the
    countable-PCF upper-bound interface for the canonical representation. The
    construction deliberately ignores the structural fields: the direct
    product-cardinality estimate bounds every displayed PCF value. This is a
    dependency reduction, not a proof of the ambient estimate itself. -/
def mathlibCountablePcfBoundHypothesis_of_alephOmega_power_lt
    (hPower :
      (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^ Cardinal.aleph0 <
        Cardinal.lift.{u + 1} targetAlephOmega4.{u}) :
    MathlibCountablePcfBoundHypothesis cardinalProductRepresentation.{u} where
  bound_from_structural := by
    intro A _hStructural hCountable _hProgressive _hRegulars hBelow
    exact cardinalProductRepresentation_pcf_below_targetAlephOmega4_of_countable_below_alephOmega_of_power_lt
      hCountable hBelow hPower

#print axioms mathlibCountablePcfBoundHypothesis_of_alephOmega_power_lt

/-! The finite-generator route can be converted into the ordinary Stage 7
    hypothesis interface. The conversion is a genuine bound extraction: the
    supplied closure statement is applied to each displayed PCF value, and
    the certificate's ideal-smallness argument supplies the strict target
    bound. No structural field is manufactured by this definition. -/
def mathlibCountablePcfBoundHypothesis_of_finiteGeneratorClosureBound
    {R : PcfRepresentation.{u, v, w, x}}
    (hBound : FiniteGeneratorClosureBoundStatement R CountableCardSet) :
    MathlibCountablePcfBoundHypothesis R where
  bound_from_structural := by
    intro A _hStructural hCountable hProgressive hRegulars hBelow
    exact pcf_below_alephOmega4_of_mathlib_finiteGeneratorClosureBoundStatement
      hBound hCountable hProgressive hRegulars hBelow

#print axioms
  mathlibCountablePcfBoundHypothesis_of_finiteGeneratorClosureBound

/-! The global output contract can now be consumed directly by Stage 7.  The
conversion uses the proved localizer-to-bound theorem; it does not create a
structural package or assert the existence of the output for arbitrary
countable sets. -/
def mathlibCountablePcfBoundHypothesis_of_countableFiniteGeneratorClosureOutput
    (hOutput : CountableFiniteGeneratorClosureOutputStatement
      cardinalProductRepresentation.{u}) :
    MathlibCountablePcfBoundHypothesis
      cardinalProductRepresentation.{u} where
  bound_from_structural := by
    intro A _hStructural hCountable hProgressive hRegulars hBelow
    obtain ⟨O⟩ := hOutput hCountable hProgressive hRegulars hBelow
    exact O.pcf_below_alephOmega4

#print axioms
  mathlibCountablePcfBoundHypothesis_of_countableFiniteGeneratorClosureOutput

structure MaxPcfBoundHypothesis
    (R : PcfRepresentation.{u, v, w, x}) where
  Countable : CardSet.{u} -> Prop
  bound_max_from_structural :
    forall {A : CardSet.{u}},
      (Hstruct : PcfStructuralHypotheses R A) ->
      Countable A ->
      ProgressiveCardSet A ->
      SetOfRegulars A ->
      BelowAlephOmega A ->
      Hstruct.maxPcf.theta < targetAlephOmega4

structure MaxPcfWitnessBoundHypothesis
    (R : PcfRepresentation.{u, v, w, x}) where
  Countable : CardSet.{u} -> Prop
  bound_max_witness :
    forall {A : CardSet.{u}},
      (M : MaxPcfWitness R A) ->
      Countable A ->
      SetOfRegulars A ->
      BelowAlephOmega A ->
      M.theta < targetAlephOmega4

/-! A supplied Mathlib countable-PCF bound applies to every tail containing a
concrete nonprincipal witness. The componentwise countability,
progressiveness, regularity, and below-`aleph_omega` assumptions are used to
build the corresponding tail side conditions; the tail structural hypothesis
and the nonprincipal witness remain explicit. -/
theorem MathlibCountablePcfBoundHypothesis.bound_nonprincipal_natTail_witness
    (H : MathlibCountablePcfBoundHypothesis
      cardinalProductRepresentation.{u})
    (A : Nat -> CardSet.{u})
    (hCountable : forall i, CountableCardSet (A i))
    (hUncountable : forall i, forall theta, A i theta ->
      Cardinal.aleph0 < theta)
    (hRegulars : forall i, SetOfRegulars (A i))
    (hBelow : forall i, BelowAlephOmega (A i))
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    (J : Ideal (CardinalIndex (iUnionCardSet A)))
    (hUltra : J.IsUltrafilterDual)
    (hTcf : HasTrueCofinality
      (cardinalProductFrame (iUnionCardSet A) J)
      (cardinalScaleLength theta))
    (hNonprincipal : forall i,
      Not (canonicalIUnionIndexIdeal A J = Ideal.excludePoint i))
    (hStructural : forall n : Nat,
      PcfStructuralHypotheses cardinalProductRepresentation.{u}
        (natTailIUnionCardSet A n)) :
    forall n : Nat,
      cardinalProductRepresentation.pcf (natTailIUnionCardSet A n) theta /\
        theta < targetAlephOmega4 := by
  intro n
  have hTail :
      cardinalProductRepresentation.pcf (natTailIUnionCardSet A n) theta :=
    cardinalProductRepresentation_mem_pcf_natTail_of_nonprincipal_indexIdeal
      A hRegulars hRegular J hUltra hTcf hNonprincipal n
  refine ⟨hTail, ?_⟩
  exact H.bound_from_structural
    (hStructural n)
    (natTailIUnionCardSet_countable A hCountable n)
    (natTailIUnionCardSet_progressive_of_countable_of_aleph0_lt
      A hCountable hUncountable n)
    (natTailIUnionCardSet_setOfRegulars A hRegulars n)
    (natTailIUnionCardSet_belowAlephOmega A hBelow n)
    theta
    hTail

namespace CountablePcfBoundHypothesis

variable {R : PcfRepresentation.{u, v, w, x}}

theorem as_statement
    (H : CountablePcfBoundHypothesis R) :
    CountablePcfBoundStatement R H.Countable :=
  H.bound_from_structural

theorem pcf_below_alephOmega4
    (H : CountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : H.Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 R A :=
  H.bound_from_structural Hstruct hCountable hProgressive hRegulars hBelow

theorem bound_member
    (H : CountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : H.Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    theta < targetAlephOmega4 :=
  H.bound_from_structural
    Hstruct hCountable hProgressive hRegulars hBelow theta hTheta

theorem bound_max_witness_from_structural
    (H : CountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (M : MaxPcfWitness R A)
    (hCountable : H.Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    M.theta < targetAlephOmega4 :=
  H.bound_member
    Hstruct
    hCountable
    hProgressive
    hRegulars
    hBelow
    M.mem_pcf

def toMaxPcfBoundHypothesis
    (H : CountablePcfBoundHypothesis R) :
    MaxPcfBoundHypothesis R where
  Countable := H.Countable
  bound_max_from_structural := by
    intro A Hstruct hCountable hProgressive hRegulars hBelow
    exact H.bound_member
      Hstruct
      hCountable
      hProgressive
      hRegulars
      hBelow
      Hstruct.maxPcf.mem_pcf

end CountablePcfBoundHypothesis

namespace MathlibCountablePcfBoundHypothesis

variable {R : PcfRepresentation.{u, v, w, x}}

theorem as_statement
    (H : MathlibCountablePcfBoundHypothesis R) :
    MathlibCountablePcfBoundStatement R :=
  H.bound_from_structural

def toCountablePcfBoundHypothesis
    (H : MathlibCountablePcfBoundHypothesis R) :
    CountablePcfBoundHypothesis R where
  Countable := CountableCardSet
  bound_from_structural := H.bound_from_structural

theorem pcf_below_alephOmega4
    (H : MathlibCountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : CountableCardSet A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 R A :=
  H.bound_from_structural Hstruct hCountable hProgressive hRegulars hBelow

/-! The canonical indexed-union closure of the supplied Mathlib countable-PCF
bound. Each component invokes the same explicit hypothesis; concentration and
the canonical PCF union equality then assemble the union bound. -/
theorem pcf_below_alephOmega4_of_iUnion_concentration
    {I : Type v}
    (H : MathlibCountablePcfBoundHypothesis
      cardinalProductRepresentation.{u})
    (A : I -> CardSet.{u})
    (hConcentration : CanonicalIUnionConcentration A)
    (hStructural : forall i,
      PcfStructuralHypotheses cardinalProductRepresentation.{u} (A i))
    (hCountable : forall i, CountableCardSet (A i))
    (hProgressive : forall i, ProgressiveCardSet (A i))
    (hRegulars : forall i, SetOfRegulars (A i))
    (hBelow : forall i, BelowAlephOmega (A i)) :
    PcfBelowAlephOmega4 cardinalProductRepresentation.{u} (iUnionCardSet A) := by
  apply cardinalProductRepresentation_pcf_below_alephOmega4_of_iUnion_concentration
    A
    hRegulars
    hConcentration
  intro i
  exact H.pcf_below_alephOmega4
    (hStructural i)
    (hCountable i)
    (hProgressive i)
    (hRegulars i)
    (hBelow i)

/-! A finite index type discharges the concentration premise internally. The
countable-PCF bound itself remains the supplied Mathlib hypothesis, applied to
each component with all structural side conditions visible. -/
theorem pcf_below_alephOmega4_of_finite_index
    {I : Type v}
    [Finite I]
    (H : MathlibCountablePcfBoundHypothesis
      cardinalProductRepresentation.{u})
    (A : I -> CardSet.{u})
    (hStructural : forall i,
      PcfStructuralHypotheses cardinalProductRepresentation.{u} (A i))
    (hCountable : forall i, CountableCardSet (A i))
    (hProgressive : forall i, ProgressiveCardSet (A i))
    (hRegulars : forall i, SetOfRegulars (A i))
    (hBelow : forall i, BelowAlephOmega (A i)) :
    PcfBelowAlephOmega4 cardinalProductRepresentation.{u}
      (iUnionCardSet A) :=
  H.pcf_below_alephOmega4_of_iUnion_concentration
    A
    (canonicalIUnionConcentration_of_finite_index A)
    hStructural
    hCountable
    hProgressive
    hRegulars
    hBelow

/-! A finite-support specialization of the componentwise Mathlib bound.
It does not require finite `CardinalIndex` instances: support components use the
supplied Mathlib bound, while outside-support components have empty PCF by the
explicit emptiness premise. -/
theorem pcf_below_alephOmega4_of_finite_support
    {I : Type v}
    (H : MathlibCountablePcfBoundHypothesis
      cardinalProductRepresentation.{u})
    (s : Finset I)
    (A : I -> CardSet.{u})
    (hOutside : forall i, Not (Membership.mem s i) ->
      forall theta, Not (A i theta))
    (hStructural : forall i, Membership.mem s i ->
      PcfStructuralHypotheses cardinalProductRepresentation.{u} (A i))
    (hCountable : forall i, Membership.mem s i -> CountableCardSet (A i))
    (hProgressive : forall i, Membership.mem s i -> ProgressiveCardSet (A i))
    (hRegulars : forall i, Membership.mem s i -> SetOfRegulars (A i))
    (hBelow : forall i, Membership.mem s i -> BelowAlephOmega (A i)) :
    PcfBelowAlephOmega4 cardinalProductRepresentation.{u} (iUnionCardSet A) := by
  have hRegularsAll : forall i, SetOfRegulars (A i) := by
    intro i theta hTheta
    by_cases hi : Membership.mem s i
    · exact hRegulars i hi theta hTheta
    · exact False.elim ((hOutside i hi theta) hTheta)
  apply cardinalProductRepresentation_pcf_below_alephOmega4_of_iUnion_concentration
    A hRegularsAll
    (canonicalIUnionConcentration_of_finite_support s A hOutside)
  intro i
  by_cases hi : Membership.mem s i
  · exact H.pcf_below_alephOmega4
      (hStructural i hi)
      (hCountable i hi)
      (hProgressive i hi)
      (hRegulars i hi)
      (hBelow i hi)
  · intro theta hTheta
    obtain ⟨beta, hBeta⟩ :=
      cardinalProductRepresentation_nonempty_of_mem_pcf hTheta
    exact False.elim ((hOutside i hi beta) hBeta)

theorem pcf_below_alephOmega4_of_pcf_subset
    (H : MathlibCountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R (R.pcf A))
    (hSubset : SubsetOf (R.pcf A) A)
    (hCountable : CountableCardSet A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 R (R.pcf A) := by
  obtain ⟨hCountablePcf, hProgressivePcf, hRegularsPcf, hBelowPcf⟩ :=
    countableProgressiveRegularBelow_of_subset
      hSubset hCountable hProgressive hRegulars hBelow
  exact H.pcf_below_alephOmega4
    Hstruct hCountablePcf hProgressivePcf hRegularsPcf hBelowPcf

/-! A fixed-point equality transports the bound obtained on `pcf A` back to
the original parameter set. The equality remains an explicit PCF premise. -/
theorem pcf_below_alephOmega4_of_pcf_eq
    (H : MathlibCountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R (R.pcf A))
    (hEq : R.pcf A = A)
    (hCountable : CountableCardSet A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 R A := by
  have hSubset : SubsetOf (R.pcf A) A := by
    intro theta hTheta
    rw [hEq] at hTheta
    exact hTheta
  have hBound : PcfBelowAlephOmega4 R (R.pcf A) :=
    H.pcf_below_alephOmega4_of_pcf_subset
      Hstruct hSubset hCountable hProgressive hRegulars hBelow
  rw [hEq] at hBound
  exact hBound

theorem pcf_below_alephOmega4_of_aleph0_lt
    (H : MathlibCountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : CountableCardSet A)
    (hUncountable :
      forall theta, A theta -> Cardinal.aleph0 < theta)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 R A :=
  H.pcf_below_alephOmega4
    Hstruct
    hCountable
    (progressiveCardSet_of_countable_of_aleph0_lt
      hCountable hUncountable)
    hRegulars
    hBelow

theorem bound_member
    (H : MathlibCountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : CountableCardSet A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    theta < targetAlephOmega4 :=
  H.bound_from_structural
    Hstruct hCountable hProgressive hRegulars hBelow theta hTheta

theorem bound_member_of_aleph0_lt
    (H : MathlibCountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : CountableCardSet A)
    (hUncountable :
      forall theta, A theta -> Cardinal.aleph0 < theta)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    theta < targetAlephOmega4 :=
  H.bound_member
    Hstruct
    hCountable
    (progressiveCardSet_of_countable_of_aleph0_lt
      hCountable hUncountable)
    hRegulars
    hBelow
    hTheta

theorem bound_max_witness_from_structural
    (H : MathlibCountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (M : MaxPcfWitness R A)
    (hCountable : CountableCardSet A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    M.theta < targetAlephOmega4 :=
  H.bound_member
    Hstruct hCountable hProgressive hRegulars hBelow M.mem_pcf

theorem bound_max_witness_from_structural_of_aleph0_lt
    (H : MathlibCountablePcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (M : MaxPcfWitness R A)
    (hCountable : CountableCardSet A)
    (hUncountable :
      forall theta, A theta -> Cardinal.aleph0 < theta)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    M.theta < targetAlephOmega4 :=
  H.bound_member_of_aleph0_lt
    Hstruct
    hCountable
    hUncountable
    hRegulars
    hBelow
    M.mem_pcf

def toMaxPcfBoundHypothesis
    (H : MathlibCountablePcfBoundHypothesis R) :
    MaxPcfBoundHypothesis R :=
  H.toCountablePcfBoundHypothesis.toMaxPcfBoundHypothesis

end MathlibCountablePcfBoundHypothesis

theorem bound_member_from_countable_pcf_statement
    {R : PcfRepresentation.{u, v, w, x}}
    {Countable : CardSet.{u} -> Prop}
    (hBound : CountablePcfBoundStatement R Countable)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    theta < targetAlephOmega4 :=
  hBound Hstruct hCountable hProgressive hRegulars hBelow theta hTheta

theorem bound_max_witness_from_countable_pcf_statement
    {R : PcfRepresentation.{u, v, w, x}}
    {Countable : CardSet.{u} -> Prop}
    (hBound : CountablePcfBoundStatement R Countable)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (M : MaxPcfWitness R A)
    (hCountable : Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    M.theta < targetAlephOmega4 :=
  bound_member_from_countable_pcf_statement
    hBound
    Hstruct
    hCountable
    hProgressive
    hRegulars
    hBelow
    M.mem_pcf

namespace MaxPcfBoundHypothesis

variable {R : PcfRepresentation.{u, v, w, x}}

theorem bound_max
    (H : MaxPcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : H.Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    Hstruct.maxPcf.theta < targetAlephOmega4 :=
  H.bound_max_from_structural Hstruct hCountable hProgressive hRegulars hBelow

theorem bound_member
    (H : MaxPcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : H.Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    theta < targetAlephOmega4 :=
  lt_of_le_of_lt
    (Hstruct.maxPcf.bounds hTheta)
    (H.bound_max Hstruct hCountable hProgressive hRegulars hBelow)

theorem pcf_below_alephOmega4
    (H : MaxPcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (hCountable : H.Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    PcfBelowAlephOmega4 R A :=
  (Hstruct.pcf_below_alephOmega4_iff_maxPcf_lt).mpr
    (H.bound_max Hstruct hCountable hProgressive hRegulars hBelow)

theorem bound_max_witness_from_structural
    (H : MaxPcfBoundHypothesis R)
    {A : CardSet.{u}}
    (Hstruct : PcfStructuralHypotheses R A)
    (M : MaxPcfWitness R A)
    (hCountable : H.Countable A)
    (hProgressive : ProgressiveCardSet A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    M.theta < targetAlephOmega4 := by
  rw [M.theta_eq Hstruct.maxPcf]
  exact H.bound_max Hstruct hCountable hProgressive hRegulars hBelow

end MaxPcfBoundHypothesis

namespace MaxPcfWitnessBoundHypothesis

variable {R : PcfRepresentation.{u, v, w, x}}

theorem bound_max_witness_apply
    (H : MaxPcfWitnessBoundHypothesis R)
    {A : CardSet.{u}}
    (M : MaxPcfWitness R A)
    (hCountable : H.Countable A)
    (hRegulars : SetOfRegulars A)
    (hBelow : BelowAlephOmega A) :
    M.theta < targetAlephOmega4 :=
  H.bound_max_witness M hCountable hRegulars hBelow

end MaxPcfWitnessBoundHypothesis

end PcfProject
