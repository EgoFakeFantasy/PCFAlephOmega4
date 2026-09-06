import PcfProject.CountableBound

/-!
# Stage 8: Cofinal core interfaces

This file records the regular, below-`aleph_omega`, and cofinality conditions
on a set of cardinals using the Mathlib-cardinal interfaces from earlier
stages. It also proves that cofinality below `aleph_omega` forces an infinite
cardinal index by constructing a strictly increasing natural sequence.
-/

namespace PcfProject

universe u v

def CofinalBelow
    (A : CardSet.{u})
    (bound : Cardinal.{u}) : Prop :=
  forall gamma, gamma < bound ->
    exists theta, A theta /\ gamma < theta /\ theta < bound

def CofinalInAlephOmega
    (A : CardSet.{u}) : Prop :=
  CofinalBelow A targetAlephOmega

/-! A cofinal set below `aleph_omega` cannot have a finite cardinal index.
The proof constructs a strictly increasing sequence by repeatedly applying
the cofinality witness above the previous value. -/
theorem infinite_cardinalIndex_of_cofinalInAlephOmega
    {A : CardSet.{u}}
    (hCofinal : CofinalInAlephOmega A) :
    Infinite (CardinalIndex A) := by
  classical
  let S := {i : CardinalIndex A // i.1 < targetAlephOmega}
  have hZero : (0 : Cardinal.{u}) < targetAlephOmega :=
    Cardinal.aleph0_pos.trans_le targetAlephOmega_aleph0_le
  let zero : S := by
    have h := hCofinal 0 hZero
    exact ⟨⟨Classical.choose h, (Classical.choose_spec h).1⟩,
      (Classical.choose_spec h).2.2⟩
  let next : S -> S := fun i => by
    have h := hCofinal i.1.1 i.2
    exact ⟨⟨Classical.choose h, (Classical.choose_spec h).1⟩,
      (Classical.choose_spec h).2.2⟩
  have hNext : forall i : S, i.1.1 < (next i).1.1 := by
    intro i
    change i.1.1 < Classical.choose (hCofinal i.1.1 i.2)
    exact (Classical.choose_spec (hCofinal i.1.1 i.2)).2.1
  let f : Nat -> S := fun n => Nat.rec zero (fun _ i => next i) n
  have hStep : forall n : Nat, (f n).1.1 < (f (n + 1)).1.1 := by
    intro n
    change (f n).1.1 < (next (f n)).1.1
    exact hNext (f n)
  have hLess : forall n m : Nat, n < m -> (f n).1.1 < (f m).1.1 := by
    intro n m
    induction m generalizing n with
    | zero =>
        intro hnm
        exact False.elim ((Nat.not_lt_zero n) hnm)
    | succ m ih =>
        intro hnm
        have hle : n <= m := Nat.le_of_lt_succ hnm
        rcases Nat.eq_or_lt_of_le hle with hEq | hlt
        · subst n
          simpa [Nat.succ_eq_add_one] using hStep m
        · exact (ih n hlt).trans (by
            simpa [Nat.succ_eq_add_one] using hStep m)
  let g : Nat -> CardinalIndex A := fun n => (f n).1
  apply Infinite.of_injective g
  intro m n hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hVal : (g m).1 < (g n).1 := hLess m n hlt
    exact (ne_of_lt hVal) (congrArg Subtype.val hmn)
  · have hVal : (g n).1 < (g m).1 := hLess n m hgt
    exact (ne_of_lt hVal) (congrArg Subtype.val hmn).symm

#print axioms infinite_cardinalIndex_of_cofinalInAlephOmega

theorem cofinalBelow_union_iff
    {A B : CardSet.{u}}
    {bound : Cardinal.{u}} :
    CofinalBelow (UnionCardSet A B) bound <->
      CofinalBelow A bound \/ CofinalBelow B bound := by
  classical
  constructor
  · intro hUnion
    by_cases hA : CofinalBelow A bound
    · exact Or.inl hA
    · right
      have hNoA :
          exists gamma, gamma < bound /\
            Not (exists theta, A theta /\ gamma < theta /\ theta < bound) := by
        by_contra hNoA
        apply hA
        intro gamma hGamma
        by_contra hNoWitness
        exact hNoA ⟨gamma, hGamma, hNoWitness⟩
      obtain ⟨gammaA, hGammaA, hNoA⟩ := hNoA
      intro gamma hGamma
      have hMaxBound : max gamma gammaA < bound :=
        max_lt hGamma hGammaA
      obtain ⟨theta, hTheta, hMaxLt, hThetaBound⟩ :=
        hUnion (max gamma gammaA) hMaxBound
      cases hTheta with
      | inl hATheta =>
          exact False.elim (hNoA ⟨theta, hATheta,
            lt_of_le_of_lt (le_max_right _ _) hMaxLt, hThetaBound⟩)
      | inr hBTheta =>
          exact ⟨theta, hBTheta,
            lt_of_le_of_lt (le_max_left _ _) hMaxLt, hThetaBound⟩
  · intro hUnion
    cases hUnion with
    | inl hA =>
        intro gamma hGamma
        obtain ⟨theta, hTheta, hGammaLt, hThetaBound⟩ :=
          hA gamma hGamma
        exact ⟨theta, Or.inl hTheta, hGammaLt, hThetaBound⟩
    | inr hB =>
        intro gamma hGamma
        obtain ⟨theta, hTheta, hGammaLt, hThetaBound⟩ :=
          hB gamma hGamma
        exact ⟨theta, Or.inr hTheta, hGammaLt, hThetaBound⟩

theorem cofinalBelow_finsetUnion_iff
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (bound : Cardinal.{u})
    (hBoundPos : 0 < bound) :
    CofinalBelow (FinsetUnionCardSet s A) bound <->
      exists i, i ∈ s /\ CofinalBelow (A i) bound := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [finsetUnionCardSet_empty]
      constructor
      · intro hCofinal
        obtain ⟨theta, hFalse, _hLt, _hBound⟩ :=
          hCofinal 0 hBoundPos
        exact False.elim hFalse
      · rintro ⟨i, hi, _hCofinal⟩
        simp at hi
  | @insert i s hi ih =>
      rw [finsetUnionCardSet_insert, cofinalBelow_union_iff, ih]
      simp [Finset.mem_insert]

theorem cofinalInAlephOmega_finsetUnion_iff
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u}) :
    CofinalInAlephOmega (FinsetUnionCardSet s A) <->
      exists i, i ∈ s /\ CofinalInAlephOmega (A i) := by
  change CofinalBelow (FinsetUnionCardSet s A) targetAlephOmega <-> _
  exact cofinalBelow_finsetUnion_iff s A targetAlephOmega
    (Cardinal.aleph0_pos.trans_le targetAlephOmega_aleph0_le)

structure AlephOmegaCore
    (A : CardSet.{u}) where
  regulars : SetOfRegulars A
  belowAlephOmega : BelowAlephOmega A
  cofinalInAlephOmega : CofinalInAlephOmega A

theorem cofinalBelow_iUnion_iff
    {I : Type v}
    (A : I -> CardSet.{u})
    (bound : Cardinal.{u}) :
    CofinalBelow (iUnionCardSet A) bound <->
      forall gamma, gamma < bound ->
        exists i, exists theta,
          A i theta /\ gamma < theta /\ theta < bound := by
  constructor
  · intro h gamma hGamma
    obtain ⟨theta, hTheta, hGammaLt, hThetaBound⟩ :=
      h gamma hGamma
    obtain ⟨i, hAi⟩ := hTheta
    exact ⟨i, theta, hAi, hGammaLt, hThetaBound⟩
  · intro h gamma hGamma
    obtain ⟨i, theta, hAi, hGammaLt, hThetaBound⟩ :=
      h gamma hGamma
    exact ⟨theta, ⟨i, hAi⟩, hGammaLt, hThetaBound⟩

theorem cofinalInAlephOmega_iUnion_iff
    {I : Type v}
    (A : I -> CardSet.{u}) :
    CofinalInAlephOmega (iUnionCardSet A) <->
      forall gamma, gamma < targetAlephOmega ->
        exists i, exists theta,
          A i theta /\ gamma < theta /\ theta < targetAlephOmega := by
  change CofinalBelow (iUnionCardSet A) targetAlephOmega <-> _
  exact cofinalBelow_iUnion_iff A targetAlephOmega

def natPrefixIUnionCardSet
    (A : Nat -> CardSet.{u})
    (n : Nat) : CardSet.{u} :=
  fun theta => exists m, m <= n /\ A m theta

theorem natPrefixIUnionCardSet_eq_finsetUnion_range
    (A : Nat -> CardSet.{u})
    (n : Nat) :
    natPrefixIUnionCardSet A n =
      FinsetUnionCardSet (Finset.range (n + 1)) A := by
  funext theta
  apply propext
  constructor
  · rintro ⟨m, hmn, hAm⟩
    exact ⟨m, by
      simpa only [Finset.mem_range] using (Nat.lt_succ_iff.mpr hmn), hAm⟩
  · rintro ⟨m, hmRange, hAm⟩
    have hmLt : m < n + 1 := by
      simpa only [Finset.mem_range] using hmRange
    exact ⟨m, Nat.lt_succ_iff.mp hmLt, hAm⟩

theorem natPrefixIUnionCardSet_cofinalInAlephOmega_iff
    (A : Nat -> CardSet.{u})
    (n : Nat) :
    CofinalInAlephOmega (natPrefixIUnionCardSet A n) <->
      exists m, m <= n /\ CofinalInAlephOmega (A m) := by
  rw [natPrefixIUnionCardSet_eq_finsetUnion_range]
  simpa only [Finset.mem_range, Nat.lt_succ_iff]
    using (cofinalInAlephOmega_finsetUnion_iff
      (Finset.range (n + 1)) A)

theorem iUnionCardSet_eq_union_natPrefix_natTail
    (A : Nat -> CardSet.{u})
    (n : Nat) :
    iUnionCardSet A =
      UnionCardSet (natPrefixIUnionCardSet A n)
        (natTailIUnionCardSet A n) := by
  funext theta
  apply propext
  constructor
  · rintro ⟨m, hAm⟩
    by_cases hmn : m <= n
    · exact Or.inl ⟨m, hmn, hAm⟩
    · exact Or.inr ⟨m, Nat.lt_of_not_ge hmn, hAm⟩
  · intro hUnion
    cases hUnion with
    | inl hPrefix =>
        obtain ⟨m, _hmn, hAm⟩ := hPrefix
        exact ⟨m, hAm⟩
    | inr hTail =>
        obtain ⟨m, _hnm, hAm⟩ := hTail
        exact ⟨m, hAm⟩

theorem iUnionCardSet_cofinalInAlephOmega_iff_natPrefix_or_natTail
    (A : Nat -> CardSet.{u})
    (n : Nat) :
    CofinalInAlephOmega (iUnionCardSet A) <->
      CofinalInAlephOmega (natPrefixIUnionCardSet A n) \/
        CofinalInAlephOmega (natTailIUnionCardSet A n) := by
  rw [iUnionCardSet_eq_union_natPrefix_natTail]
  exact cofinalBelow_union_iff

theorem natTailIUnionCardSet_cofinalInAlephOmega_of_iUnion_cofinal_of_no_prefix_component
    (A : Nat -> CardSet.{u})
    (n : Nat)
    (hUnion : CofinalInAlephOmega (iUnionCardSet A))
    (hNoPrefix : forall m, m <= n ->
      Not (CofinalInAlephOmega (A m))) :
    CofinalInAlephOmega (natTailIUnionCardSet A n) := by
  have hPrefix :
      Not (CofinalInAlephOmega (natPrefixIUnionCardSet A n)) := by
    intro hCofinal
    obtain ⟨m, hmn, hComponent⟩ :=
      (natPrefixIUnionCardSet_cofinalInAlephOmega_iff A n).mp hCofinal
    exact hNoPrefix m hmn hComponent
  exact (iUnionCardSet_cofinalInAlephOmega_iff_natPrefix_or_natTail
    A n).mp hUnion |>.resolve_left hPrefix

theorem natTailIUnionCardSet_alephOmegaCore_of_cofinal
    (A : Nat -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hBelow : forall i, BelowAlephOmega (A i))
    (n : Nat)
    (hCofinal : CofinalInAlephOmega (natTailIUnionCardSet A n)) :
    AlephOmegaCore (natTailIUnionCardSet A n) := by
  refine {
    regulars := ?_
    belowAlephOmega := ?_
    cofinalInAlephOmega := hCofinal
  }
  · exact natTailIUnionCardSet_setOfRegulars A hRegulars n
  · exact natTailIUnionCardSet_belowAlephOmega A hBelow n

/-! The standard `aleph_omega` core consists exactly of the successor alephs
`aleph_(n+1)`.  The following lemmas prove its countability, regularity,
boundedness, and cofinality directly. -/
def alephSuccSet : CardSet.{u} :=
  fun theta =>
    exists n : Nat,
      theta = Cardinal.aleph ((n : Ordinal.{u}) + 1)

/-! Below `aleph_omega`, the uncountable regular cardinals are exactly the
    successor alephs used by the standard countable PCF core. -/
theorem alephSuccSet_of_aleph0_lt_of_lt_targetAlephOmega
    {theta : Cardinal.{u}}
    (hAleph0 : Cardinal.aleph0 < theta)
    (hBelow : theta < targetAlephOmega) :
    alephSuccSet theta := by
  obtain ⟨o, hTheta⟩ := Cardinal.mem_range_aleph_iff.mpr hAleph0.le
  have hOrd : o < Ordinal.omega0 := by
    apply (Cardinal.aleph_lt_aleph).mp
    simpa only [targetAlephOmega, targetIndexOmega] using
      (show Cardinal.aleph o < targetAlephOmega from hTheta ▸ hBelow)
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hOrd
  have hnZero : n ≠ 0 := by
    intro hn0
    subst n
    have hEq : theta = Cardinal.aleph0 := by
      rw [← hTheta, hn]
      simp
    exact (ne_of_gt hAleph0) hEq
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnZero
  refine ⟨m, ?_⟩
  rw [← hTheta, hn]
  simp [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]

theorem alephSuccSet_eq_iUnion_singleton :
    alephSuccSet.{u} =
      iUnionCardSet
        (fun n : Nat =>
          singletonCardSet (Cardinal.aleph ((n : Ordinal.{u}) + 1))) := by
  funext theta
  simp [alephSuccSet, iUnionCardSet, singletonCardSet]

theorem alephSuccSet_countable :
    CountableCardSet alephSuccSet.{u} := by
  rw [alephSuccSet_eq_iUnion_singleton]
  exact countableCardSet_iUnion _ (fun n =>
    countableCardSet_singleton
      (Cardinal.aleph ((n : Ordinal.{u}) + 1)))

theorem alephSuccSet_aleph0_lt :
    forall theta, alephSuccSet.{u} theta -> Cardinal.aleph0 < theta := by
  intro theta hTheta
  obtain ⟨n, rfl⟩ := hTheta
  exact Cardinal.aleph0_lt_aleph.mpr
    ((zero_le : (0 : Ordinal.{u}) <= (n : Ordinal.{u})).trans_lt
      (lt_add_one _))

#print axioms alephSuccSet_aleph0_lt

theorem alephSuccSet_regulars :
    SetOfRegulars alephSuccSet.{u} := by
  intro theta hTheta
  obtain ⟨n, rfl⟩ := hTheta
  exact Cardinal.isRegular_aleph_add_one (n : Ordinal.{u})

theorem alephSuccSet_belowAlephOmega :
    BelowAlephOmega alephSuccSet.{u} := by
  intro theta hTheta
  obtain ⟨n, rfl⟩ := hTheta
  rw [Cardinal.aleph_lt_aleph]
  simpa only [Nat.cast_add, Nat.cast_one] using
    Ordinal.natCast_lt_omega0 (n + 1)

theorem alephSuccSet_cofinalInAlephOmega :
    CofinalInAlephOmega alephSuccSet.{u} := by
  rw [alephSuccSet_eq_iUnion_singleton]
  apply (cofinalInAlephOmega_iUnion_iff _).mpr
  intro gamma hGamma
  have hLimit :
      targetAlephOmega.{u} =
        ⨆ a : Set.Iio (Ordinal.omega0 : Ordinal.{u}), Cardinal.aleph a.1 := by
    simpa [targetAlephOmega, targetIndexOmega] using
      (Cardinal.aleph_limit Ordinal.isSuccLimit_omega0)
  rw [hLimit] at hGamma
  obtain ⟨a, ha⟩ := exists_lt_of_lt_ciSup' hGamma
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp a.2
  rw [hn] at ha
  refine ⟨n, Cardinal.aleph ((n : Ordinal.{u}) + 1), rfl, ?_, ?_⟩
  · exact ha.trans (Cardinal.aleph_lt_aleph.mpr (lt_add_one _))
  · exact alephSuccSet_belowAlephOmega _ ⟨n, rfl⟩

theorem alephSuccSet_tail_cofinalInAlephOmega
    (n : Nat) :
    CofinalInAlephOmega
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) := by
  apply natTailIUnionCardSet_cofinalInAlephOmega_of_iUnion_cofinal_of_no_prefix_component
    (fun m : Nat =>
      singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1)))
    n
  · rw [← alephSuccSet_eq_iUnion_singleton]
    exact alephSuccSet_cofinalInAlephOmega
  · intro m _hmn hCofinal
    have hBelow :
        Cardinal.aleph ((m : Ordinal.{u}) + 1) < targetAlephOmega :=
      alephSuccSet_belowAlephOmega _ ⟨m, rfl⟩
    obtain ⟨theta, hTheta, hGammaLt, _hThetaBound⟩ :=
      hCofinal
        (Cardinal.aleph ((m : Ordinal.{u}) + 1))
        hBelow
    have hEq :
        theta = Cardinal.aleph ((m : Ordinal.{u}) + 1) := by
      simpa [singletonCardSet] using hTheta
    exact (lt_irrefl _)
      (hEq ▸ hGammaLt)

theorem alephSuccSet_tail_alephOmegaCore
    (n : Nat) :
    AlephOmegaCore
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) := by
  refine natTailIUnionCardSet_alephOmegaCore_of_cofinal
    (fun m : Nat =>
      singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1)))
    ?_ ?_ n ?_
  · intro m theta hTheta
    rw [hTheta]
    exact Cardinal.isRegular_aleph_add_one (m : Ordinal.{u})
  · intro m theta hTheta
    rw [hTheta]
    exact alephSuccSet_belowAlephOmega _ ⟨m, rfl⟩
  · exact alephSuccSet_tail_cofinalInAlephOmega n

theorem alephSuccSet_tail_countable
    (n : Nat) :
    CountableCardSet
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) := by
  exact natTailIUnionCardSet_countable
    (fun m : Nat =>
      singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1)))
    (fun _ => countableCardSet_singleton _)
    n

/-! Canonical-product form of the finite pointwise-cover lemma.  A single
    raw family that is cofinal in every ultrafilter quotient has the property
    that every product function is pointwise covered by finitely many family
    members.  This is the compactness step used to pass from quotient
    cofinalities to a pointwise cofinal family in the proof of the
    `aleph_(omega_4)` bound. -/
theorem cardinalProductFrame_exists_finset_pointwise_cover_of_forall_ultrafilterDual_isCofinalFamily
    {A : CardSet.{u}}
    {J0 : Ideal (CardinalIndex A)}
    {K : Type v}
    (d : K -> ProductElement (cardinalProductFrame A J0))
    (hCofinal : forall J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual ->
        (cardinalProductFrame A J).IsCofinalFamily d) :
    forall g : ProductElement (cardinalProductFrame A J0),
      exists s : Finset K,
        forall i, exists k, k ∈ s /\
          (cardinalProductFrame A J0).le i (g i) (d k i) := by
  intro g
  obtain ⟨s, hs⟩ :=
    ReducedProductFrame.exists_finset_pointwise_cover_of_forall_ultrafilterDual_isCofinalFamily
      (cardinalProductFrame A J0) d hCofinal g
  refine ⟨s, ?_⟩
  intro i
  exact hs i

#print axioms
  cardinalProductFrame_exists_finset_pointwise_cover_of_forall_ultrafilterDual_isCofinalFamily

end PcfProject
