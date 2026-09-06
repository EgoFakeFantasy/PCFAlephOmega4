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

structure RegularBelowAlephOmegaCore
    (A : CardSet.{u}) where
  regulars : SetOfRegulars A
  belowAlephOmega : BelowAlephOmega A

structure AlephOmegaCore
    (A : CardSet.{u}) where
  regulars : SetOfRegulars A
  belowAlephOmega : BelowAlephOmega A
  cofinalInAlephOmega : CofinalInAlephOmega A

theorem regularBelowAlephOmegaCore_iUnion_of_forall
    {I : Type v}
    (A : I -> CardSet.{u})
    (hCore : forall i, RegularBelowAlephOmegaCore (A i)) :
    RegularBelowAlephOmegaCore (iUnionCardSet A) := by
  refine {
    regulars := ?_
    belowAlephOmega := ?_
  }
  · exact setOfRegulars_iUnion_of_forall A (fun i => (hCore i).regulars)
  · exact (BelowAlephOmega_iUnion_iff A).mpr
      (fun i => (hCore i).belowAlephOmega)

theorem alephOmegaCore_iUnion_of_regularBelow_of_cofinal
    {I : Type v}
    (A : I -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hBelow : forall i, BelowAlephOmega (A i))
    (i0 : I)
    (hCofinal : CofinalInAlephOmega (A i0)) :
    AlephOmegaCore (iUnionCardSet A) := by
  refine {
    regulars := ?_
    belowAlephOmega := ?_
    cofinalInAlephOmega := ?_
  }
  · exact setOfRegulars_iUnion_of_forall A hRegulars
  · exact (BelowAlephOmega_iUnion_iff A).mpr hBelow
  · intro gamma hGamma
    obtain ⟨theta, hTheta, hGammaLt, hThetaBound⟩ :=
      hCofinal gamma hGamma
    exact ⟨theta, ⟨i0, hTheta⟩, hGammaLt, hThetaBound⟩

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

/-! The finite-prefix construction is the elementary filtration attached to a
`Nat`-indexed family.  The PCF-specific stitching assertion is deliberately
not part of this construction; this object records only the countable,
progressive, regular, and bounded set-theoretic data. -/
noncomputable def natPrefixCountableCardSetFiltration
    (A : Nat -> CardSet.{u})
    (hCountable : forall m, CountableCardSet (A m))
    (hUncountable : forall m, forall theta, A m theta ->
      Cardinal.aleph0 < theta)
    (hRegulars : forall m, SetOfRegulars (A m))
    (hBelow : forall m, BelowAlephOmega (A m)) :
    CountableCardSetFiltration (iUnionCardSet A) where
  layer := natPrefixIUnionCardSet A
  layer_subset := by
    intro n theta hTheta
    obtain ⟨m, _hmn, hAm⟩ := hTheta
    exact ⟨m, hAm⟩
  layer_mono := by
    intro n m hnm theta hTheta
    obtain ⟨k, hk, hAk⟩ := hTheta
    exact ⟨k, le_trans hk hnm, hAk⟩
  covered := by
    intro theta hTheta
    obtain ⟨m, hAm⟩ := hTheta
    exact ⟨m, ⟨m, le_rfl, hAm⟩⟩
  layer_countable := by
    intro n
    rw [natPrefixIUnionCardSet_eq_finsetUnion_range]
    apply (countableCardSet_finsetUnion_iff
      (Finset.range (n + 1)) A).mpr
    intro m hm
    exact hCountable m
  layer_progressive := by
    intro n
    rw [natPrefixIUnionCardSet_eq_finsetUnion_range]
    apply progressiveCardSet_finsetUnion_of_countable_of_aleph0_lt
      (Finset.range (n + 1)) A
    · intro m hm
      exact hCountable m
    · intro m hm
      exact hUncountable m
  layer_aleph0_lt := by
    intro n theta hTheta
    obtain ⟨m, _hmn, hAm⟩ := hTheta
    exact hUncountable m theta hAm
  layer_regulars := by
    intro n theta hTheta
    obtain ⟨m, _hmn, hAm⟩ := hTheta
    exact hRegulars m theta hAm
  layer_below := by
    intro n theta hTheta
    obtain ⟨m, _hmn, hAm⟩ := hTheta
    exact hBelow m theta hAm

#print axioms natPrefixCountableCardSetFiltration

/-! The same elementary filtration can be based at any strict natural tail.
The shift is useful because it keeps the layer index type equal to `Nat`, while
the PCF-specific stitching assertion remains deliberately absent. -/
noncomputable def natTailCountableCardSetFiltration
    (A : Nat -> CardSet.{u})
    (hCountable : forall m, CountableCardSet (A m))
    (hUncountable : forall m, forall theta, A m theta ->
      Cardinal.aleph0 < theta)
    (hRegulars : forall m, SetOfRegulars (A m))
    (hBelow : forall m, BelowAlephOmega (A m))
    (n : Nat) :
    CountableCardSetFiltration (natTailIUnionCardSet A n) := by
  rw [natTailIUnionCardSet_eq_iUnion_shift A n]
  exact natPrefixCountableCardSetFiltration
    (fun k : Nat => A (n + 1 + k))
    (fun k => hCountable (n + 1 + k))
    (by
      intro k theta hTheta
      exact hUncountable (n + 1 + k) theta hTheta)
    (fun k => hRegulars (n + 1 + k))
    (fun k => hBelow (n + 1 + k))

#print axioms natTailCountableCardSetFiltration

/-! For the standard successor-aleph family, the finite prefix and strict
tail are complementary on the actual union index type.  The singleton
components are disjoint because `Cardinal.aleph` is strictly increasing. -/
theorem alephSuccSet_natTail_not_iff_natPrefix
    (n : Nat)
    (k : CardinalIndex
      (iUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))))) :
    Not (natTailIUnionCardSet
      (fun m : Nat =>
        singletonCardSet
          (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n k.1) <->
      natPrefixIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n k.1 := by
  obtain ⟨m, hm⟩ := k.2
  have hOwner :
      k.1 = Cardinal.aleph ((m : Ordinal.{u}) + 1) := by
    simpa [singletonCardSet] using hm
  constructor
  · intro hNotTail
    by_cases hmn : m <= n
    · refine ⟨m, hmn, ?_⟩
      simpa [singletonCardSet] using hOwner
    · exfalso
      apply hNotTail
      refine ⟨m, Nat.lt_of_not_ge hmn, ?_⟩
      simpa [singletonCardSet] using hOwner
  · rintro ⟨i, hin, hi⟩
    intro hTail
    obtain ⟨j, hnj, hj⟩ := hTail
    have hij : i < j := lt_of_le_of_lt hin hnj
    have hPrefix :
        k.1 = Cardinal.aleph ((i : Ordinal.{u}) + 1) := by
      simpa [singletonCardSet] using hi
    have hTail :
        k.1 = Cardinal.aleph ((j : Ordinal.{u}) + 1) := by
      simpa [singletonCardSet] using hj
    have hCardEq :
        Cardinal.aleph ((i : Ordinal.{u}) + 1) =
          Cardinal.aleph ((j : Ordinal.{u}) + 1) :=
      hPrefix.symm.trans hTail
    have hCardLt :
        Cardinal.aleph ((i : Ordinal.{u}) + 1) <
          Cardinal.aleph ((j : Ordinal.{u}) + 1) := by
      apply Cardinal.aleph_lt_aleph.mpr
      exact_mod_cast (Nat.add_lt_add_right hij 1)
    exact (lt_irrefl _) (hCardEq ▸ hCardLt)

theorem alephSuccSet_natTail_eventually_iff_natPrefix_small
    {J : Ideal
      (CardinalIndex
        (iUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1)))))}
    (n : Nat) :
    J.Eventually
        (fun k =>
          natTailIUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n k.1) <->
      J.Small
        (fun k =>
          natPrefixIUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n k.1) := by
  change J.Small
      (fun k => Not (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n k.1)) <-> _
  have hPred :
      (fun k : CardinalIndex
          (iUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1)))) =>
        Not (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n k.1)) =
        (fun k : CardinalIndex
          (iUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1)))) =>
          natPrefixIUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n k.1) := by
    funext k
    apply propext
    exact alephSuccSet_natTail_not_iff_natPrefix n k
  rw [hPred]

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

theorem natTailIUnionCardSet_cofinalInAlephOmega_iff
    (A : Nat -> CardSet.{u})
    (n : Nat) :
    CofinalInAlephOmega (natTailIUnionCardSet A n) <->
      forall gamma, gamma < targetAlephOmega ->
        exists m, n < m /\ exists theta,
          A m theta /\ gamma < theta /\ theta < targetAlephOmega := by
  change CofinalBelow (natTailIUnionCardSet A n) targetAlephOmega <-> _
  constructor
  · intro hCofinal gamma hGamma
    obtain ⟨theta, hTheta, hGammaLt, hThetaBound⟩ :=
      hCofinal gamma hGamma
    obtain ⟨m, hnm, hAm⟩ := hTheta
    exact ⟨m, hnm, theta, hAm, hGammaLt, hThetaBound⟩
  · intro hCofinal gamma hGamma
    obtain ⟨m, hnm, theta, hAm, hGammaLt, hThetaBound⟩ :=
      hCofinal gamma hGamma
    exact ⟨theta, ⟨m, hnm, hAm⟩, hGammaLt, hThetaBound⟩

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

theorem alephOmegaCore_iUnion_natPrefix_or_natTail
    (A : Nat -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i))
    (hBelow : forall i, BelowAlephOmega (A i))
    (C : AlephOmegaCore (iUnionCardSet A))
    (n : Nat) :
    (exists m, m <= n /\ CofinalInAlephOmega (A m)) \/
      AlephOmegaCore (natTailIUnionCardSet A n) := by
  have hD :=
    (iUnionCardSet_cofinalInAlephOmega_iff_natPrefix_or_natTail
      A n).mp C.cofinalInAlephOmega
  cases hD with
  | inl hPrefix =>
      exact Or.inl
        ((natPrefixIUnionCardSet_cofinalInAlephOmega_iff A n).mp hPrefix)
  | inr hTail =>
      exact Or.inr
        (natTailIUnionCardSet_alephOmegaCore_of_cofinal
          A hRegulars hBelow n hTail)

theorem regularBelowAlephOmegaCore_iUnion_iff
    {I : Type v}
    (A : I -> CardSet.{u}) :
    RegularBelowAlephOmegaCore (iUnionCardSet A) <->
      forall i, RegularBelowAlephOmegaCore (A i) := by
  constructor
  · intro hCore i
    refine {
      regulars := ?_
      belowAlephOmega := ?_
    }
    · intro theta hTheta
      exact hCore.regulars theta ⟨i, hTheta⟩
    · intro theta hTheta
      exact hCore.belowAlephOmega theta ⟨i, hTheta⟩
  · intro hCore
    exact regularBelowAlephOmegaCore_iUnion_of_forall A hCore

theorem alephOmegaCore_iUnion_iff
    {I : Type v}
    (A : I -> CardSet.{u}) :
    AlephOmegaCore (iUnionCardSet A) <->
      (forall i, RegularBelowAlephOmegaCore (A i)) /\
        CofinalInAlephOmega (iUnionCardSet A) := by
  constructor
  · intro hCore
    refine ⟨(regularBelowAlephOmegaCore_iUnion_iff A).mp {
      regulars := hCore.regulars
      belowAlephOmega := hCore.belowAlephOmega
    }, hCore.cofinalInAlephOmega⟩
  · rintro ⟨hCore, hCofinal⟩
    refine {
      regulars := ?_
      belowAlephOmega := ?_
      cofinalInAlephOmega := hCofinal
    }
    · exact setOfRegulars_iUnion_of_forall A
        (fun i => (hCore i).regulars)
    · exact (BelowAlephOmega_iUnion_iff A).mpr
        (fun i => (hCore i).belowAlephOmega)

/-!
The standard core used at `aleph_omega` consists of the successor
alephs `aleph_(n+1)`. Unlike the abstract core structures above, all of its
elementary properties are proved here.
-/

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

theorem alephSuccSet_progressive :
  ProgressiveCardSet alephSuccSet.{u} := by
  apply progressiveCardSet_of_countable_of_aleph0_lt alephSuccSet_countable
  exact alephSuccSet_aleph0_lt

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

/-! The standard successor-aleph core has the elementary prefix filtration
    supplied by `natPrefixCountableCardSetFiltration`.  This is the complete
    set-theoretic part of the countable-PCF setup; it deliberately does not
    assert that PCF witnesses stitch to a finite prefix. -/
noncomputable def alephSuccSet_countableCardSetFiltration :
    CountableCardSetFiltration alephSuccSet.{u} := by
  rw [alephSuccSet_eq_iUnion_singleton]
  exact natPrefixCountableCardSetFiltration
    (fun n : Nat =>
      singletonCardSet (Cardinal.aleph ((n : Ordinal.{u}) + 1)))
    (fun _ => countableCardSet_singleton _)
    (by
      intro n theta hTheta
      rw [hTheta]
      exact Cardinal.aleph0_lt_aleph.mpr
        ((zero_le : (0 : Ordinal.{u}) <= (n : Ordinal.{u})).trans_lt
          (lt_add_one _)))
    (by
      intro n theta hTheta
      rw [hTheta]
      exact Cardinal.isRegular_aleph_add_one (n : Ordinal.{u}))
    (by
      intro n theta hTheta
      rw [hTheta]
      exact alephSuccSet_belowAlephOmega _ ⟨n, rfl⟩)

#print axioms alephSuccSet_countableCardSetFiltration

def alephSuccCore : AlephOmegaCore alephSuccSet.{u} where
  regulars := alephSuccSet_regulars
  belowAlephOmega := alephSuccSet_belowAlephOmega
  cofinalInAlephOmega := alephSuccSet_cofinalInAlephOmega

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

theorem alephSuccSet_tail_not_exists_greatest
    (n : Nat) :
    Not (exists theta,
      IsGreatest
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
        theta) := by
  rintro ⟨theta, hGreatest⟩
  obtain ⟨m, hmn, hTheta⟩ := hGreatest.1
  have hEq : theta = Cardinal.aleph ((m : Ordinal.{u}) + 1) := by
    simpa [singletonCardSet] using hTheta
  have hNextMem :
      natTailIUnionCardSet
        (fun k : Nat =>
          singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) n
        (Cardinal.aleph (((m + 1 : Nat) : Ordinal.{u}) + 1)) := by
    exact ⟨m + 1, lt_trans hmn (Nat.lt_succ_self m), rfl⟩
  have hLt :
      theta < Cardinal.aleph (((m + 1 : Nat) : Ordinal.{u}) + 1) := by
    rw [hEq]
    apply Cardinal.aleph_lt_aleph.mpr
    simpa only [Nat.cast_add, Nat.cast_one] using
      (lt_add_one ((m : Ordinal.{u}) + 1))
  exact (not_lt_of_ge (hGreatest.2 hNextMem)) hLt

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

theorem alephSuccSet_tail_progressive
    (n : Nat) :
    ProgressiveCardSet
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) := by
  apply natTailIUnionCardSet_progressive_of_countable_of_aleph0_lt
    (fun m : Nat =>
      singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1)))
    (fun _ => countableCardSet_singleton _)
    ?_
    n
  intro m theta hTheta
  rw [hTheta]
  exact Cardinal.aleph0_lt_aleph.mpr
    ((zero_le : (0 : Ordinal.{u}) <= (m : Ordinal.{u})).trans_lt
      (lt_add_one _))

/-! The strict-tail analogue of the elementary countable filtration.  As in
the full-core construction, this packages only the set-theoretic skeleton;
the PCF-specific assertion that a value of the union is already visible in a
finite layer remains a separate hypothesis. -/
noncomputable def alephSuccSet_tail_countableCardSetFiltration
    (n : Nat) :
    CountableCardSetFiltration
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) := by
  exact natTailCountableCardSetFiltration
    (fun m : Nat =>
      singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1)))
    (fun _ => countableCardSet_singleton _)
    (by
      intro m theta hTheta
      rw [hTheta]
      exact Cardinal.aleph0_lt_aleph.mpr
        ((zero_le : (0 : Ordinal.{u}) <= (m : Ordinal.{u})).trans_lt
          (lt_add_one _)))
    (by
      intro m theta hTheta
      rw [hTheta]
      exact Cardinal.isRegular_aleph_add_one (m : Ordinal.{u}))
    (by
      intro m theta hTheta
      rw [hTheta]
      exact alephSuccSet_belowAlephOmega _ ⟨m, rfl⟩)
    n

#print axioms alephSuccSet_tail_countableCardSetFiltration

theorem regularBelowAlephOmegaCore_finsetUnion_of_forall
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hRegulars : forall i, i ∈ s -> SetOfRegulars (A i))
    (hBelow : forall i, i ∈ s -> BelowAlephOmega (A i)) :
    RegularBelowAlephOmegaCore (FinsetUnionCardSet s A) := by
  refine {
    regulars := ?_
    belowAlephOmega := ?_
  }
  · intro theta hTheta
    obtain ⟨i, hi, hAi⟩ := hTheta
    exact hRegulars i hi theta hAi
  · intro theta hTheta
    obtain ⟨i, hi, hAi⟩ := hTheta
    exact hBelow i hi theta hAi

theorem alephOmegaCore_finsetUnion_of_forall
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hNonempty : s.Nonempty)
    (hCore : forall i, i ∈ s -> AlephOmegaCore (A i)) :
    AlephOmegaCore (FinsetUnionCardSet s A) := by
  refine {
    regulars := ?_
    belowAlephOmega := ?_
    cofinalInAlephOmega := ?_
  }
  · intro theta hTheta
    obtain ⟨i, hi, hAi⟩ := hTheta
    exact (hCore i hi).regulars theta hAi
  · intro theta hTheta
    obtain ⟨i, hi, hAi⟩ := hTheta
    exact (hCore i hi).belowAlephOmega theta hAi
  · intro gamma hGamma
    obtain ⟨i, hi⟩ := hNonempty
    obtain ⟨theta, hTheta, hGammaLt, hThetaBound⟩ :=
      (hCore i hi).cofinalInAlephOmega gamma hGamma
    exact ⟨theta, ⟨i, hi, hTheta⟩, hGammaLt, hThetaBound⟩

theorem regularBelowAlephOmegaCore_finsetUnion_iff
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u}) :
    RegularBelowAlephOmegaCore (FinsetUnionCardSet s A) <->
      forall i, i ∈ s -> RegularBelowAlephOmegaCore (A i) := by
  constructor
  · intro C i hi
    refine {
      regulars := ?_
      belowAlephOmega := ?_
    }
    · intro theta hTheta
      exact C.regulars theta ⟨i, hi, hTheta⟩
    · intro theta hTheta
      exact C.belowAlephOmega theta ⟨i, hi, hTheta⟩
  · intro hCore
    exact regularBelowAlephOmegaCore_finsetUnion_of_forall
      s A
      (fun i hi => (hCore i hi).regulars)
      (fun i hi => (hCore i hi).belowAlephOmega)

theorem alephOmegaCore_finsetUnion_iff
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u}) :
    AlephOmegaCore (FinsetUnionCardSet s A) <->
      (forall i, i ∈ s -> RegularBelowAlephOmegaCore (A i)) /\
        (exists i, i ∈ s /\ CofinalInAlephOmega (A i)) := by
  constructor
  · intro C
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (regularBelowAlephOmegaCore_finsetUnion_iff s A).mp
        ({
          regulars := C.regulars
          belowAlephOmega := C.belowAlephOmega
        } : RegularBelowAlephOmegaCore (FinsetUnionCardSet s A)) i hi
    · exact (cofinalInAlephOmega_finsetUnion_iff s A).mp
        C.cofinalInAlephOmega
  · rintro ⟨hCore, ⟨i, hi, hCofinal⟩⟩
    refine {
      regulars := ?_
      belowAlephOmega := ?_
      cofinalInAlephOmega := ?_
    }
    · intro theta hTheta
      obtain ⟨j, hj, hAj⟩ := hTheta
      exact (hCore j hj).regulars theta hAj
    · intro theta hTheta
      obtain ⟨j, hj, hAj⟩ := hTheta
      exact (hCore j hj).belowAlephOmega theta hAj
    · intro gamma hGamma
      obtain ⟨theta, hTheta, hGammaLt, hThetaBound⟩ :=
        hCofinal gamma hGamma
      exact ⟨theta, ⟨i, hi, hTheta⟩, hGammaLt, hThetaBound⟩

namespace RegularBelowAlephOmegaCore

variable {A : CardSet.{u}}

theorem regular_of_mem
    (C : RegularBelowAlephOmegaCore A)
    {theta : Cardinal.{u}}
    (hTheta : A theta) :
    Cardinal.IsRegular theta :=
  C.regulars theta hTheta

theorem below_of_mem
    (C : RegularBelowAlephOmegaCore A)
    {theta : Cardinal.{u}}
    (hTheta : A theta) :
    theta < targetAlephOmega :=
  C.belowAlephOmega theta hTheta

end RegularBelowAlephOmegaCore

namespace AlephOmegaCore

variable {A : CardSet.{u}}

def toRegularBelow
    (C : AlephOmegaCore A) :
    RegularBelowAlephOmegaCore A where
  regulars := C.regulars
  belowAlephOmega := C.belowAlephOmega

theorem regular_of_mem
    (C : AlephOmegaCore A)
    {theta : Cardinal.{u}}
    (hTheta : A theta) :
    Cardinal.IsRegular theta :=
  C.regulars theta hTheta

theorem below_of_mem
    (C : AlephOmegaCore A)
    {theta : Cardinal.{u}}
    (hTheta : A theta) :
    theta < targetAlephOmega :=
  C.belowAlephOmega theta hTheta

theorem exists_between
    (C : AlephOmegaCore A)
    {gamma : Cardinal.{u}}
    (hGamma : gamma < targetAlephOmega) :
    exists theta, A theta /\ gamma < theta /\ theta < targetAlephOmega :=
  C.cofinalInAlephOmega gamma hGamma

end AlephOmegaCore

/-! Every initial segment of an uncountable cardinal set below
`aleph_omega` has finite canonical index.  The point is that every such
coordinate is one of the finitely many successor alephs below a fixed
successor aleph above the bound. -/
theorem finite_cardinalIndex_le_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {kappa : Cardinal.{u}}
    (hKappa : kappa < targetAlephOmega) :
    Finite {i : CardinalIndex A // i.1 <= kappa} := by
  classical
  obtain ⟨eta, hEta, hKappaEta, _hEtaBelow⟩ :=
    alephSuccSet_cofinalInAlephOmega kappa hKappa
  obtain ⟨q, hEtaEq⟩ := hEta
  let indexOf : {i : CardinalIndex A // i.1 <= kappa} -> Nat := fun i =>
    Classical.choose
      (alephSuccSet_of_aleph0_lt_of_lt_targetAlephOmega
        (hAleph0 i.1.1 i.1.2) (hBelow i.1.1 i.1.2))
  have hIndexEq : forall i : {i : CardinalIndex A // i.1 <= kappa},
      i.1.1 = Cardinal.aleph ((indexOf i : Ordinal.{u}) + 1) := by
    intro i
    exact Classical.choose_spec
      (alephSuccSet_of_aleph0_lt_of_lt_targetAlephOmega
        (hAleph0 i.1.1 i.1.2) (hBelow i.1.1 i.1.2))
  let f : {i : CardinalIndex A // i.1 <= kappa} -> Fin q := fun i => by
    refine ⟨indexOf i, ?_⟩
    have hCardLt :
        Cardinal.aleph ((indexOf i : Ordinal.{u}) + 1) <
          Cardinal.aleph ((q : Ordinal.{u}) + 1) := by
      calc
        Cardinal.aleph ((indexOf i : Ordinal.{u}) + 1) = i.1.1 :=
          (hIndexEq i).symm
        _ <= kappa := i.2
        _ < eta := hKappaEta
        _ = Cardinal.aleph ((q : Ordinal.{u}) + 1) := hEtaEq
    have hOrdLt :
        (indexOf i : Ordinal.{u}) + 1 < (q : Ordinal.{u}) + 1 :=
      Cardinal.aleph_lt_aleph.mp hCardLt
    apply Nat.lt_of_succ_lt_succ
    simpa only [Nat.succ_eq_add_one] using (by
      exact_mod_cast hOrdLt : indexOf i + 1 < q + 1)
  apply Finite.of_injective f
  intro i j hEq
  apply Subtype.ext
  apply Subtype.ext
  have hIndex : indexOf i = indexOf j := congrArg Fin.val hEq
  calc
    i.1.1 = Cardinal.aleph ((indexOf i : Ordinal.{u}) + 1) := hIndexEq i
    _ = Cardinal.aleph ((indexOf j : Ordinal.{u}) + 1) := by rw [hIndex]
    _ = j.1.1 := (hIndexEq j).symm

#print axioms finite_cardinalIndex_le_of_aleph0_lt_of_belowAlephOmega

/-! On an uncountable core below `aleph_omega`, every family of size below
    `aleph_omega` can be defeated after choosing a suitable nonprincipal
    ultrafilter-dual ideal.  Only finitely many coordinates fail to exceed the
    family's cardinality, by the preceding initial-segment theorem. -/
theorem
    cardinalProductFrame_exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily_of_mk_lt_targetAlephOmega
    {A : CardSet.{u}}
    [Infinite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {ι : Type u}
    (hFamily : Cardinal.mk ι < targetAlephOmega)
    (d : ι -> ProductElement
      (cardinalProductFrame A (Ideal.finiteSet (CardinalIndex A)))) :
    exists J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual /\
        (forall i, Not (J = Ideal.excludePoint i)) /\
        Not ((cardinalProductFrame A J).IsCofinalFamily d) := by
  let B : CardinalIndex A -> Prop := fun i => Cardinal.mk ι < i.1
  have hFiniteException :
      Set.Finite {i : CardinalIndex A | Not (B i)} := by
    simpa only [B, not_lt] using
      Set.finite_coe_iff.mp
        (finite_cardinalIndex_le_of_aleph0_lt_of_belowAlephOmega
          hAleph0 hBelow hFamily)
  exact
    cardinalProductFrame_exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily_of_mk_lt_off_finite
      hRegulars (B := B) (fun i hi => hi) hFiniteException d

#print axioms
  cardinalProductFrame_exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily_of_mk_lt_targetAlephOmega

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

/-! The preceding family-dependent ideal construction has a useful uniform
    consequence.  If one fixed family is cofinal modulo every nonprincipal
    ultrafilter-dual ideal on the core, then its index has cardinality at
    least `aleph_omega`.  The family is written over the finite-set frame only
    to choose a common product type; changing the ideal changes the eventual
    order but not the underlying dependent product. -/
theorem targetAlephOmega_le_mk_of_forall_nonprincipal_ultrafilterDual_isCofinalFamily
    {A : CardSet.{u}}
    [Infinite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {ι : Type u}
    (d : ι -> ProductElement
      (cardinalProductFrame A (Ideal.finiteSet (CardinalIndex A))))
    (hUniform : forall J : Ideal (CardinalIndex A),
      J.IsUltrafilterDual ->
      (forall i, Not (J = Ideal.excludePoint i)) ->
      (cardinalProductFrame A J).IsCofinalFamily d) :
    targetAlephOmega <= Cardinal.mk ι := by
  by_contra hNotLe
  have hFamily : Cardinal.mk ι < targetAlephOmega := lt_of_not_ge hNotLe
  obtain ⟨J, hUltra, hNonprincipal, hNotCofinal⟩ :=
    cardinalProductFrame_exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily_of_mk_lt_targetAlephOmega
      hRegulars hAleph0 hBelow hFamily d
  exact hNotCofinal (hUniform J hUltra hNonprincipal)

#print axioms
  targetAlephOmega_le_mk_of_forall_nonprincipal_ultrafilterDual_isCofinalFamily

/-! On the canonical successor-aleph core, all side conditions of the uniform
    obstruction are theorems.  Thus no family of size below `aleph_omega` can
    be cofinal simultaneously for every nonprincipal ultrafilter quotient. -/
theorem alephSuccSet_targetAlephOmega_le_mk_of_forall_nonprincipal_ultrafilterDual_isCofinalFamily
    {ι : Type u}
    (d : ι -> ProductElement
      (cardinalProductFrame alephSuccSet.{u}
        (Ideal.finiteSet (CardinalIndex alephSuccSet.{u}))))
    (hUniform : forall J : Ideal (CardinalIndex alephSuccSet.{u}),
      J.IsUltrafilterDual ->
      (forall i, Not (J = Ideal.excludePoint i)) ->
      (cardinalProductFrame alephSuccSet.{u} J).IsCofinalFamily d) :
    targetAlephOmega <= Cardinal.mk ι := by
  letI : Infinite (CardinalIndex alephSuccSet.{u}) :=
    infinite_cardinalIndex_of_cofinalInAlephOmega
      alephSuccSet_cofinalInAlephOmega
  exact
    targetAlephOmega_le_mk_of_forall_nonprincipal_ultrafilterDual_isCofinalFamily
      alephSuccSet_regulars alephSuccSet_aleph0_lt
      alephSuccSet_belowAlephOmega d hUniform

#print axioms
  alephSuccSet_targetAlephOmega_le_mk_of_forall_nonprincipal_ultrafilterDual_isCofinalFamily

/-! Among cardinal sets with only uncountable members below `aleph_omega`,
infinite canonical index is exactly cofinality in `aleph_omega`: a bounded
such set has finite index by the preceding successor-aleph argument. -/
theorem cofinalInAlephOmega_iff_infinite_cardinalIndex_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A) :
    CofinalInAlephOmega A <-> Infinite (CardinalIndex A) := by
  constructor
  · exact infinite_cardinalIndex_of_cofinalInAlephOmega
  · intro hInfinite
    letI : Infinite (CardinalIndex A) := hInfinite
    classical
    by_contra hNotCofinal
    have hBounded : exists gamma, gamma < targetAlephOmega /\
        Not (exists theta, A theta /\ gamma < theta /\ theta < targetAlephOmega) := by
      apply Classical.byContradiction
      intro hNoBounded
      apply hNotCofinal
      intro gamma hGamma
      apply Classical.byContradiction
      intro hNoWitness
      apply hNoBounded
      exact ⟨gamma, hGamma, hNoWitness⟩
    obtain ⟨gamma, hGamma, hNoWitness⟩ := hBounded
    have hAllLe : forall i : CardinalIndex A, i.1 <= gamma := by
      intro i
      by_contra hNotLe
      have hGt : gamma < i.1 := lt_of_not_ge hNotLe
      exact hNoWitness ⟨i.1, i.2, hGt, hBelow i.1 i.2⟩
    let S := {i : CardinalIndex A // i.1 <= gamma}
    letI : Finite S :=
      finite_cardinalIndex_le_of_aleph0_lt_of_belowAlephOmega
        hAleph0 hBelow hGamma
    let f : CardinalIndex A -> S := fun i => ⟨i, hAllLe i⟩
    have hFinite : Finite (CardinalIndex A) :=
      Finite.of_injective f (by
        intro i j hEq
        simpa only [f] using congrArg Subtype.val hEq)
    letI : Finite (CardinalIndex A) := hFinite
    exact not_finite (CardinalIndex A)

#print axioms
  cofinalInAlephOmega_iff_infinite_cardinalIndex_of_aleph0_lt_of_belowAlephOmega

/-! A nonprincipal ultrafilter-dual ideal on an uncountable cardinal set
below `aleph_omega` eventually avoids every bounded initial segment.  The
finite-initial-segment theorem above supplies the finite set to avoid. -/
theorem nonprincipal_eventually_coordinate_gt_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual)
    (hNonprincipal : forall i, Not (J = Ideal.excludePoint i))
    {kappa : Cardinal.{u}}
    (hKappa : kappa < targetAlephOmega) :
    exists B : CardinalIndex A -> Prop,
      J.Eventually B /\
        forall i, B i -> kappa < i.1 := by
  classical
  let S := {i : CardinalIndex A // i.1 <= kappa}
  letI : Finite S :=
    finite_cardinalIndex_le_of_aleph0_lt_of_belowAlephOmega
      hAleph0 hBelow hKappa
  letI : Fintype S := Fintype.ofFinite S
  let s : Finset (CardinalIndex A) := Finset.univ.image (fun i : S => i.1)
  have hAvoid : J.Eventually (fun i => Not (Membership.mem s i)) :=
    hUltra.eventually_not_mem_finset_of_forall_ne_excludePoint
      hNonprincipal s
  refine ⟨fun i => Not (Membership.mem s i), hAvoid, ?_⟩
  intro i hi
  apply lt_of_not_ge
  intro hLe
  apply hi
  exact Finset.mem_image.mpr
    ⟨⟨i, hLe⟩, Finset.mem_univ _, rfl⟩

#print axioms
  nonprincipal_eventually_coordinate_gt_of_aleph0_lt_of_belowAlephOmega

/-! The preceding finite-initial-segment argument gives the full
`aleph_omega` quotient-cofinality lower bound for every nonprincipal product
on an uncountable set of regular cardinals below `aleph_omega`. -/
theorem cardinalProductQuotient_lift_le_cof_of_nonprincipal_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual)
    (hNonprincipal : forall i, Not (J = Ideal.excludePoint i)) :
    Cardinal.lift.{u + 1} targetAlephOmega.{u} <=
      Order.cof (CardinalProductQuotient A J) := by
  apply cardinalProductQuotient_lift_le_cof_of_regulars_of_eventually_unbounded
    hRegulars
  · intro kappa hKappa
    exact nonprincipal_eventually_coordinate_gt_of_aleph0_lt_of_belowAlephOmega
      hAleph0 hBelow hUltra hNonprincipal hKappa
  · exact hUltra.isProper

#print axioms
  cardinalProductQuotient_lift_le_cof_of_nonprincipal_of_aleph0_lt_of_belowAlephOmega

/-! Any supplied canonical-length scale on a nonprincipal ultrafilter-dual
product over an uncountable regular core below `aleph_omega` is strictly
longer than `aleph_omega`. This is the direct scale form of eventual
coordinate unboundedness and does not construct the scale. -/
theorem cardinalProductFrame_nonprincipal_scale_gt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall beta, A beta -> Cardinal.aleph0 < beta)
    (hBelow : BelowAlephOmega A)
    (hUltra : J.IsUltrafilterDual)
    (hNonprincipal : forall i, Not (J = Ideal.excludePoint i))
    (hRegular : Cardinal.IsRegular theta)
    (hScale : HasScaleWitness
      (cardinalProductFrame A J)
      (cardinalScaleLength theta)) :
    targetAlephOmega < theta := by
  exact cardinalProductFrame_cardinalScaleLength_gt_of_eventually_unbounded_of_not_isRegular
    hRegulars hUltra.isProper hScale
    (by
      intro kappa hKappa
      exact nonprincipal_eventually_coordinate_gt_of_aleph0_lt_of_belowAlephOmega
        hAleph0 hBelow hUltra hNonprincipal hKappa)
    targetAlephOmega_not_isRegular hRegular

#print axioms
  cardinalProductFrame_nonprincipal_scale_gt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega

/-! On a small canonical index, the preceding quotient lower bound constructs
an actual regular true-cofinality scale above `aleph_omega`; it is not merely
an order-cofinality statement. -/
theorem cardinalProductFrame_exists_trueCofinality_gt_targetAlephOmega_of_small_cardinalIndex
    {A : CardSet.{u}}
    {J : Ideal (CardinalIndex A)}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hUltra : J.IsUltrafilterDual)
    (hNonprincipal : forall i, Not (J = Ideal.excludePoint i)) :
    exists theta : Cardinal.{u},
      Cardinal.IsRegular theta /\
        HasTrueCofinality
          (cardinalProductFrame A J)
          (cardinalScaleLength theta) /\
        targetAlephOmega < theta := by
  exact cardinalProductFrame_exists_trueCofinality_gt_of_small_cardinalIndex
    hRegulars hUltra hSmall targetAlephOmega_aleph0_le
    targetAlephOmega_not_isRegular
    (cardinalProductQuotient_lift_le_cof_of_nonprincipal_of_aleph0_lt_of_belowAlephOmega
      hRegulars hAleph0 hBelow hUltra hNonprincipal)

#print axioms
  cardinalProductFrame_exists_trueCofinality_gt_targetAlephOmega_of_small_cardinalIndex

/-! An infinite small canonical index supports a Zorn-constructed
nonprincipal ideal.  For uncountable coordinates below `aleph_omega`, its
eventual diagonal lower bound turns that ideal into a real canonical PCF value
strictly above `aleph_omega`. -/
theorem cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_small_cardinalIndex
    {A : CardSet.{u}}
    [Infinite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    (hSmall : Small.{u} (CardinalIndex A)) :
    exists theta : Cardinal.{u},
      exists J : Ideal (CardinalIndex A),
        Cardinal.IsRegular theta /\
          J.IsUltrafilterDual /\
          (forall i, Not (J = Ideal.excludePoint i)) /\
          HasTrueCofinality
            (cardinalProductFrame A J)
            (cardinalScaleLength theta) /\
          cardinalProductRepresentation.pcf A theta /\
          targetAlephOmega < theta := by
  obtain ⟨J, hUltra, hNonprincipal⟩ :=
    exists_nonprincipal_ultrafilterDual_ideal (I := CardinalIndex A)
  obtain ⟨theta, hRegular, hTcf, hThetaGt⟩ :=
    cardinalProductFrame_exists_trueCofinality_gt_targetAlephOmega_of_small_cardinalIndex
      hRegulars hAleph0 hBelow hSmall hUltra hNonprincipal
  exact ⟨theta, J, hRegular, hUltra, hNonprincipal, hTcf,
    cardinalProductRepresentation_mem_pcf_iff.mpr
      ⟨hRegular, J, hUltra, hTcf⟩,
    hThetaGt⟩

#print axioms
  cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_small_cardinalIndex

/-! Countability supplies the small-index premise in the preceding
infinite-index construction.  No cofinality assumption is needed for this
Zorn-to-scale existence theorem. -/
theorem cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_countableCardSet
    {A : CardSet.{u}}
    [Infinite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    (hCountable : CountableCardSet A) :
    exists theta : Cardinal.{u},
      exists J : Ideal (CardinalIndex A),
        Cardinal.IsRegular theta /\
          J.IsUltrafilterDual /\
          (forall i, Not (J = Ideal.excludePoint i)) /\
          HasTrueCofinality
            (cardinalProductFrame A J)
            (cardinalScaleLength theta) /\
          cardinalProductRepresentation.pcf A theta /\
          targetAlephOmega < theta := by
  exact
    cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_small_cardinalIndex
      hRegulars hAleph0 hBelow
      (cardinalIndex_small_of_countableCardSet hCountable)

#print axioms
  cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_countableCardSet

/-! The PCF witness supplied by the infinite small-index construction lies
outside the original coordinate set, because every original coordinate is
strictly below `aleph_omega`. -/
theorem cardinalProductRepresentation_exists_nonprincipal_pcf_mem_not_mem_gt_targetAlephOmega_of_small_cardinalIndex
    {A : CardSet.{u}}
    [Infinite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    (hSmall : Small.{u} (CardinalIndex A)) :
    exists theta : Cardinal.{u},
      exists J : Ideal (CardinalIndex A),
        Cardinal.IsRegular theta /\
          J.IsUltrafilterDual /\
          (forall i, Not (J = Ideal.excludePoint i)) /\
          HasTrueCofinality
            (cardinalProductFrame A J)
            (cardinalScaleLength theta) /\
          cardinalProductRepresentation.pcf A theta /\
          Not (A theta) /\
          targetAlephOmega < theta := by
  obtain ⟨theta, J, hRegular, hUltra, hNonprincipal, hTcf, hPcf, hThetaGt⟩ :=
    cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_small_cardinalIndex
      hRegulars hAleph0 hBelow hSmall
  refine ⟨theta, J, hRegular, hUltra, hNonprincipal, hTcf, hPcf, ?_, hThetaGt⟩
  intro hMem
  exact (hBelow theta hMem).not_gt hThetaGt

#print axioms
  cardinalProductRepresentation_exists_nonprincipal_pcf_mem_not_mem_gt_targetAlephOmega_of_small_cardinalIndex

/-! A cofinal core has an infinite canonical index.  Together with an
explicit small-index witness, the preceding theorem therefore supplies a
nonprincipal canonical PCF value strictly above `aleph_omega`. -/
theorem cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_small_cardinalIndex_of_cofinalInAlephOmega
    {A : CardSet.{u}}
    (C : AlephOmegaCore A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hSmall : Small.{u} (CardinalIndex A)) :
    exists theta : Cardinal.{u},
      exists J : Ideal (CardinalIndex A),
        Cardinal.IsRegular theta /\
          J.IsUltrafilterDual /\
          (forall i, Not (J = Ideal.excludePoint i)) /\
          HasTrueCofinality
            (cardinalProductFrame A J)
            (cardinalScaleLength theta) /\
          cardinalProductRepresentation.pcf A theta /\
          targetAlephOmega < theta := by
  letI : Infinite (CardinalIndex A) :=
    infinite_cardinalIndex_of_cofinalInAlephOmega C.cofinalInAlephOmega
  exact
    cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_small_cardinalIndex
      C.regulars hAleph0 C.belowAlephOmega hSmall

#print axioms
  cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_small_cardinalIndex_of_cofinalInAlephOmega

/-! Countability supplies the small-index premise required by the preceding
Zorn-to-scale construction. -/
theorem cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_countableCardSet_of_cofinalInAlephOmega
    {A : CardSet.{u}}
    (C : AlephOmegaCore A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hCountable : CountableCardSet A) :
    exists theta : Cardinal.{u},
      exists J : Ideal (CardinalIndex A),
        Cardinal.IsRegular theta /\
          J.IsUltrafilterDual /\
          (forall i, Not (J = Ideal.excludePoint i)) /\
          HasTrueCofinality
            (cardinalProductFrame A J)
            (cardinalScaleLength theta) /\
          cardinalProductRepresentation.pcf A theta /\
          targetAlephOmega < theta := by
  letI : Infinite (CardinalIndex A) :=
    infinite_cardinalIndex_of_cofinalInAlephOmega C.cofinalInAlephOmega
  exact
    cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_countableCardSet
      C.regulars hAleph0 C.belowAlephOmega hCountable

#print axioms
  cardinalProductRepresentation_exists_nonprincipal_pcf_mem_gt_targetAlephOmega_of_countableCardSet_of_cofinalInAlephOmega

/-! Every non-generator canonical PCF value of an uncountable regular core
below `aleph_omega` lies strictly above `aleph_omega`.  The PCF witness is
first shown nonprincipal by the principal-product computation, then the
finite-initial-segment diagonal lower bound applies to that same witness. -/
theorem cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_of_not_mem_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta)
    (hNotMem : Not (A theta)) :
    targetAlephOmega < theta := by
  obtain ⟨J, hUltra, hTcf, hNonprincipal⟩ :=
    cardinalProductRepresentation_mem_pcf_not_mem_has_nonprincipal_ideal
      hRegulars hPcf hNotMem
  exact cardinalProductFrame_nonprincipal_scale_gt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
    hRegulars hAleph0 hBelow hUltra hNonprincipal
    (cardinalProductRepresentation.mem_pcf_regular hPcf)
    hTcf.hasScaleWitness

#print axioms
  cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_of_not_mem_of_aleph0_lt_of_belowAlephOmega

/-! For an uncountable regular cardinal set below `aleph_omega`, the
canonical PCF spectrum has no value at `aleph_omega`: a value is either an
original coordinate below that bound or is strictly above it. -/
theorem cardinalProductRepresentation_mem_pcf_lt_or_gt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta) :
    theta < targetAlephOmega \/ targetAlephOmega < theta := by
  by_cases hMem : A theta
  · exact Or.inl (hBelow theta hMem)
  · exact Or.inr
      (cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_of_not_mem_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow hPcf hMem)

#print axioms
  cardinalProductRepresentation_mem_pcf_lt_or_gt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega

/-! On an uncountable regular core below `aleph_omega`, the part of the
canonical PCF spectrum strictly below `aleph_omega` is exactly the original
coordinate set. -/
theorem cardinalProductRepresentation_mem_pcf_lt_targetAlephOmega_iff_mem_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}} :
    cardinalProductRepresentation.pcf A theta /\ targetAlephOmega > theta <-> A theta := by
  constructor
  · rintro ⟨hPcf, hThetaLt⟩
    by_contra hNotMem
    have hThetaGt :=
      cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_of_not_mem_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow hPcf hNotMem
    exact (not_lt_of_ge hThetaGt.le) hThetaLt
  · intro hMem
    exact ⟨cardinalProductRepresentation_mem_pcf_of_mem hRegulars hMem,
      hBelow theta hMem⟩

#print axioms
  cardinalProductRepresentation_mem_pcf_lt_targetAlephOmega_iff_mem_of_aleph0_lt_of_belowAlephOmega

/-! The non-generator spectrum above `aleph_omega` is exactly the branch
represented by a nonprincipal ultrafilter-dual product with a genuine
true-cofinality scale.  This is a classification of displayed witnesses, not
a scale-existence theorem for arbitrary ideals. -/
theorem cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_iff_exists_nonprincipal_trueCofinality_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}} :
    cardinalProductRepresentation.pcf A theta /\ targetAlephOmega < theta <->
      Cardinal.IsRegular theta /\
        exists J : Ideal (CardinalIndex A),
          J.IsUltrafilterDual /\
            (forall i, Not (J = Ideal.excludePoint i)) /\
            HasTrueCofinality
              (cardinalProductFrame A J)
              (cardinalScaleLength theta) := by
  constructor
  · rintro ⟨hPcf, hThetaGt⟩
    have hNotMem : Not (A theta) := by
      intro hMem
      exact (hBelow theta hMem).not_gt hThetaGt
    obtain ⟨J, hUltra, hTcf, hNonprincipal⟩ :=
      cardinalProductRepresentation_mem_pcf_not_mem_has_nonprincipal_ideal
        hRegulars hPcf hNotMem
    exact ⟨cardinalProductRepresentation.mem_pcf_regular hPcf,
      J, hUltra, hNonprincipal, hTcf⟩
  · rintro ⟨hRegular, J, hUltra, hNonprincipal, hTcf⟩
    refine ⟨cardinalProductRepresentation_mem_pcf_iff.mpr
      ⟨hRegular, J, hUltra, hTcf⟩, ?_⟩
    exact cardinalProductFrame_nonprincipal_scale_gt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
      hRegulars hAleph0 hBelow hUltra hNonprincipal hRegular
      hTcf.hasScaleWitness

#print axioms
  cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_iff_exists_nonprincipal_trueCofinality_of_aleph0_lt_of_belowAlephOmega

/-! The preceding high-spectrum classification can be stated with a scale
witness instead of true cofinality.  For a regular represented length, the
canonical product proves the required true-cofinality lower bound from that
scale, so this is still an exact witness classification. -/
theorem cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_iff_exists_nonprincipal_scale_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A)
    {theta : Cardinal.{u}} :
    cardinalProductRepresentation.pcf A theta /\ targetAlephOmega < theta <->
      Cardinal.IsRegular theta /\
        exists J : Ideal (CardinalIndex A),
          J.IsUltrafilterDual /\
            (forall i, Not (J = Ideal.excludePoint i)) /\
            HasScaleWitness
              (cardinalProductFrame A J)
              (cardinalScaleLength theta) := by
  constructor
  · rintro ⟨hPcf, hThetaGt⟩
    obtain ⟨hRegular, J, hUltra, hNonprincipal, hTcf⟩ :=
      (cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_iff_exists_nonprincipal_trueCofinality_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow).mp ⟨hPcf, hThetaGt⟩
    exact ⟨hRegular, J, hUltra, hNonprincipal, hTcf.hasScaleWitness⟩
  · rintro ⟨hRegular, J, hUltra, hNonprincipal, hScale⟩
    obtain ⟨s⟩ := hScale
    exact
      (cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_iff_exists_nonprincipal_trueCofinality_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow).mpr
        ⟨hRegular, J, hUltra, hNonprincipal,
          cardinalScaleLength_hasTrueCofinality hRegular s⟩

#print axioms
  cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_iff_exists_nonprincipal_scale_of_aleph0_lt_of_belowAlephOmega

/-! For an uncountable regular core below `aleph_omega`, the canonical PCF
set is a fixed point precisely when every displayed PCF value lies below
`aleph_omega`.  This is a spectrum criterion; it does not assert a general
upper bound on arbitrary non-fixed-point spectra. -/
theorem cardinalProductRepresentation_pcf_eq_iff_forall_mem_lt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A) :
    cardinalProductRepresentation.pcf A = A <->
      forall theta, cardinalProductRepresentation.pcf A theta ->
        theta < targetAlephOmega := by
  constructor
  · intro hEq theta hPcf
    rw [hEq] at hPcf
    exact hBelow theta hPcf
  · intro hBound
    apply cardinalProductRepresentation_pcf_eq_of_pcf_subset hRegulars
    intro theta hPcf
    exact
      (cardinalProductRepresentation_mem_pcf_lt_targetAlephOmega_iff_mem_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow).mp
        ⟨hPcf, hBound theta hPcf⟩

#print axioms
  cardinalProductRepresentation_pcf_eq_iff_forall_mem_lt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega

/-! Equivalently, the fixed-point condition is the absence of a
nonprincipal scale. On this bounded uncountable core, the preceding diagonal
argument proves that every such scale is automatically above `aleph_omega`,
so the inequality need not be repeated in the existential statement. -/
theorem cardinalProductRepresentation_pcf_eq_iff_not_exists_nonprincipal_scale_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A) :
    cardinalProductRepresentation.pcf A = A <->
      Not (exists theta : Cardinal.{u},
        Cardinal.IsRegular theta /\
          exists J : Ideal (CardinalIndex A),
            J.IsUltrafilterDual /\
              (forall i, Not (J = Ideal.excludePoint i)) /\
              HasScaleWitness
                (cardinalProductFrame A J)
                (cardinalScaleLength theta)) := by
  constructor
  · intro hEq hScale
    obtain ⟨theta, hRegular, J, hUltra, hNonprincipal, hWitness⟩ := hScale
    have hHigh :=
      (cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_iff_exists_nonprincipal_scale_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow).mpr
        ⟨hRegular, J, hUltra, hNonprincipal, hWitness⟩
    have hThetaLt :=
      (cardinalProductRepresentation_pcf_eq_iff_forall_mem_lt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow).mp hEq theta hHigh.1
    exact (not_lt_of_ge hHigh.2.le) hThetaLt
  · intro hNoScale
    apply
      (cardinalProductRepresentation_pcf_eq_iff_forall_mem_lt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow).mpr
    intro theta hPcf
    rcases
        cardinalProductRepresentation_mem_pcf_lt_or_gt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
          hRegulars hAleph0 hBelow hPcf with hThetaLt | hThetaGt
    · exact hThetaLt
    · apply False.elim
      apply hNoScale
      refine ⟨theta, ?_⟩
      exact
        (cardinalProductRepresentation_mem_pcf_gt_targetAlephOmega_iff_exists_nonprincipal_scale_of_aleph0_lt_of_belowAlephOmega
          hRegulars hAleph0 hBelow).mp ⟨hPcf, hThetaGt⟩

#print axioms
  cardinalProductRepresentation_pcf_eq_iff_not_exists_nonprincipal_scale_of_aleph0_lt_of_belowAlephOmega

/-! The singular cardinal `aleph_omega` itself cannot be a canonical PCF
value of a regular core whose coordinates are all uncountable and below it.
The result is a spectrum-gap statement, not an upper bound on the values
above that gap. -/
theorem cardinalProductRepresentation_not_mem_pcf_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (hBelow : BelowAlephOmega A) :
    Not (cardinalProductRepresentation.pcf A targetAlephOmega) := by
  intro hPcf
  rcases
      cardinalProductRepresentation_mem_pcf_lt_or_gt_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega
        hRegulars hAleph0 hBelow hPcf with hLt | hGt
  · exact (lt_irrefl targetAlephOmega) hLt
  · exact (lt_irrefl targetAlephOmega) hGt

#print axioms
  cardinalProductRepresentation_not_mem_pcf_targetAlephOmega_of_aleph0_lt_of_belowAlephOmega

end PcfProject
