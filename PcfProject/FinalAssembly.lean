import PcfProject.CofinalCore
import PcfProject.FinitePcf

/-!
# Finite and concentrated PCF assembly

This file assembles the preceding explicit hypotheses into the target
conditional statement. It does not prove Shelah's PCF theorem unconditionally:
the reduction from strong limit at `aleph_omega` to a continuum-bounding
max-pcf witness remains an explicit field.
The finite-support componentwise route can additionally combine supplied
component structural packages into a union maximum before applying the
explicit continuum comparison; it remains conditional.
The general concentrated indexed-union route has the same shape, with an
explicit greatest-component premise controlling the cross-component maximum.
The dominating-component adapter isolates that maximum construction from the
structural inputs still required by the countable-PCF bound.
-/

namespace PcfProject

universe u v w x

/-! 以下仅保留核心路径实际调用的终端语义段。 -/

theorem alephSuccSet_tail_maxPcf_witness_has_full_witness_and_all_tail_eventuality
    (n : Nat)
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) theta) :
    exists J : Ideal
        (CardinalIndex
          (iUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1))))),
      J.IsUltrafilterDual /\
        HasTrueCofinality
          (cardinalProductFrame
            (iUnionCardSet
              (fun m : Nat =>
                singletonCardSet
                  (Cardinal.aleph ((m : Ordinal.{u}) + 1)))) J)
          (cardinalScaleLength theta) /\
        (forall i,
          Not (canonicalIUnionIndexIdeal
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1))) J =
            Ideal.excludePoint i)) /\
        (forall m : Nat,
          J.Eventually
            (fun k =>
              natTailIUnionCardSet
                (fun i : Nat =>
                  singletonCardSet
                    (Cardinal.aleph ((i : Ordinal.{u}) + 1))) m k.1)) /\
        (forall m : Nat,
          cardinalProductRepresentation.pcf
            (natTailIUnionCardSet
              (fun k : Nat =>
                singletonCardSet
                  (Cardinal.aleph ((k : Ordinal.{u}) + 1))) m) theta) := by
  let A : Nat -> CardSet.{u} := fun k =>
    singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))
  have hRegulars : forall k, SetOfRegulars (A k) := by
    intro k beta hBeta
    change beta = Cardinal.aleph ((k : Ordinal.{u}) + 1) at hBeta
    rw [hBeta]
    exact Cardinal.isRegular_aleph_add_one (k : Ordinal.{u})
  have hFullMem :
      cardinalProductRepresentation.pcf (iUnionCardSet A) theta := by
    exact cardinalProductRepresentation_pcf_mono
      (natTailIUnionCardSet_subset_iUnionCardSet A n)
      (setOfRegulars_iUnion_of_forall A hRegulars)
      theta
      (by simpa [A] using hMax.1)
  obtain ⟨hRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := iUnionCardSet A) (theta := theta)).mp hFullMem
  have hNonprincipal : forall i,
      Not (canonicalIUnionIndexIdeal A J = Ideal.excludePoint i) := by
    intro i hPrincipal
    have hEventually : J.Eventually (fun k => A i k.1) :=
      canonicalIUnion_eventually_component_of_indexIdeal_eq_excludePoint
        A hUltra hPrincipal
    have hComponentPcf : cardinalProductRepresentation.pcf (A i) theta :=
      cardinalProductRepresentation_mem_pcf_of_eventually_mem
        (A := A i) (B := iUnionCardSet A)
        (by
          intro beta hBeta
          exact ⟨i, hBeta⟩)
        (setOfRegulars_iUnion_of_forall A hRegulars)
        hRegular J hUltra hTcf hEventually
    have hThetaEq :
        theta = Cardinal.aleph ((i : Ordinal.{u}) + 1) := by
      apply (cardinalProductRepresentation_mem_pcf_singleton_iff
        (Cardinal.isRegular_aleph_add_one (i : Ordinal.{u}))).mp
      simpa [A] using hComponentPcf
    let j : Nat := max n i + 1
    have hnj : n < j := by
      exact Nat.lt_succ_of_le (Nat.le_max_left n i)
    have hij : i < j := by
      exact Nat.lt_succ_of_le (Nat.le_max_right n i)
    have hTailMem :
        natTailIUnionCardSet A n
          (Cardinal.aleph ((j : Ordinal.{u}) + 1)) := by
      exact ⟨j, hnj, rfl⟩
    have hTailPcf :
        cardinalProductRepresentation.pcf (natTailIUnionCardSet A n)
          (Cardinal.aleph ((j : Ordinal.{u}) + 1)) := by
      apply cardinalProductRepresentation_mem_pcf_of_mem
        (alephSuccSet_tail_alephOmegaCore n).regulars
      simpa [A] using hTailMem
    have hLe : Cardinal.aleph ((j : Ordinal.{u}) + 1) <= theta := by
      apply hMax.2
      simpa [A] using hTailPcf
    have hLt : theta < Cardinal.aleph ((j : Ordinal.{u}) + 1) := by
      rw [hThetaEq]
      apply Cardinal.aleph_lt_aleph.mpr
      exact_mod_cast (Nat.add_lt_add_right hij 1)
    exact (not_lt_of_ge hLe) hLt
  refine ⟨J, hUltra, hTcf, hNonprincipal, ?_, ?_⟩
  · intro m
    exact canonicalIUnion_eventually_mem_natTail_of_nonprincipal_indexIdeal
      A hUltra hNonprincipal m
  · intro m
    exact cardinalProductRepresentation_mem_pcf_natTail_of_nonprincipal_indexIdeal
      A hRegulars hRegular J hUltra hTcf hNonprincipal m

theorem alephSuccSet_tail_maxPcf_witness_mem_pcf_all_tails
    (n : Nat)
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) theta) :
    forall m : Nat,
      cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun k : Nat =>
            singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) m) theta := by
  obtain ⟨J, hUltra, hTcf, _hNonprincipal, _hTails, hPcf⟩ :=
    alephSuccSet_tail_maxPcf_witness_has_full_witness_and_all_tail_eventuality
      n hMax
  exact hPcf

theorem alephSuccSet_tail_maxPcf_witness_isMaxPcf_all_deeper_tails
    (n : Nat)
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) theta) :
    forall m, n <= m ->
      IsMaxPcf cardinalProductRepresentation
        (natTailIUnionCardSet
          (fun k : Nat =>
            singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) m) theta := by
  let A : Nat -> CardSet.{u} := fun k =>
    singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))
  have hRegulars : forall k, SetOfRegulars (A k) := by
    intro k beta hBeta
    change beta = Cardinal.aleph ((k : Ordinal.{u}) + 1) at hBeta
    rw [hBeta]
    exact Cardinal.isRegular_aleph_add_one (k : Ordinal.{u})
  intro m hnm
  have hMem :
      cardinalProductRepresentation.pcf (natTailIUnionCardSet A m) theta := by
    simpa [A] using
      (alephSuccSet_tail_maxPcf_witness_mem_pcf_all_tails n hMax m)
  have hBounds :
      forall beta,
        cardinalProductRepresentation.pcf (natTailIUnionCardSet A m) beta ->
          beta <= theta := by
    intro beta hBeta
    have hBetaAtN :
        cardinalProductRepresentation.pcf (natTailIUnionCardSet A n) beta :=
      (cardinalProductRepresentation_pcf_natTail_mono A hRegulars hnm)
        beta hBeta
    exact hMax.2 beta (by simpa [A] using hBetaAtN)
  exact ⟨by simpa [A] using hMem, hBounds⟩

theorem alephSuccSet_tail_maxPcf_theta_ge_targetAlephOmega
    (n : Nat)
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) theta) :
    targetAlephOmega <= theta := by
  apply le_of_forall_lt
  intro gamma hGamma
  obtain ⟨eta, hEta, hGammaLt, _hEtaBelow⟩ :=
    (alephSuccSet_tail_cofinalInAlephOmega n) gamma hGamma
  have hEtaPcf :
      cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
        eta :=
    cardinalProductRepresentation_mem_pcf_of_mem
      (alephSuccSet_tail_alephOmegaCore n).regulars hEta
  exact lt_of_lt_of_le hGammaLt (hMax.2 eta hEtaPcf)

theorem alephSuccSet_tail_maxPcf_theta_gt_targetAlephOmega
    (n : Nat)
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) theta) :
    targetAlephOmega < theta := by
  have hLower : targetAlephOmega <= theta :=
    alephSuccSet_tail_maxPcf_theta_ge_targetAlephOmega n hMax
  have hNe : Not (targetAlephOmega = theta) := by
    intro hEq
    apply targetAlephOmega_not_isRegular
    rw [hEq]
    exact cardinalProductRepresentation.mem_pcf_regular hMax.left
  exact lt_of_le_of_ne hLower hNe

theorem alephSuccSet_eq_first_union_zero_tail :
    alephSuccSet.{u} =
      UnionCardSet
        (singletonCardSet (Cardinal.aleph ((0 : Ordinal.{u}) + 1)))
        (natTailIUnionCardSet
          (fun k : Nat =>
            singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) 0) := by
  let A : Nat -> CardSet.{u} := fun k =>
    singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))
  have hPrefix : natPrefixIUnionCardSet A 0 = A 0 := by
    funext theta
    apply propext
    constructor
    · rintro ⟨k, hk, hAk⟩
      have hkZero : k = 0 := Nat.eq_zero_of_le_zero hk
      simpa [hkZero] using hAk
    · intro hA
      exact ⟨0, le_rfl, hA⟩
  rw [alephSuccSet_eq_iUnion_singleton]
  change iUnionCardSet A = _
  rw [iUnionCardSet_eq_union_natPrefix_natTail A 0, hPrefix]
  rfl

theorem cardinalProductRepresentation_pcf_alephSuccSet_eq_first_union_zero_tail :
    cardinalProductRepresentation.pcf alephSuccSet.{u} =
      UnionCardSet
        (cardinalProductRepresentation.pcf
          (singletonCardSet (Cardinal.aleph ((0 : Ordinal.{u}) + 1))))
        (cardinalProductRepresentation.pcf
          (natTailIUnionCardSet
            (fun k : Nat =>
              singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) 0)) := by
  let A : Nat -> CardSet.{u} := fun k =>
    singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))
  have hRegulars : forall k, SetOfRegulars (A k) := by
    intro k beta hBeta
    change beta = Cardinal.aleph ((k : Ordinal.{u}) + 1) at hBeta
    rw [hBeta]
    exact Cardinal.isRegular_aleph_add_one (k : Ordinal.{u})
  rw [alephSuccSet_eq_first_union_zero_tail]
  exact cardinalProductRepresentation_pcf_union
    (hRegulars 0)
    (natTailIUnionCardSet_setOfRegulars A hRegulars 0)

theorem alephSuccSet_tail_maxPcf_witness_isMaxPcf_all_tails
    (n : Nat)
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation
      (natTailIUnionCardSet
        (fun k : Nat =>
          singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) n) theta) :
    forall m,
      IsMaxPcf cardinalProductRepresentation
        (natTailIUnionCardSet
          (fun k : Nat =>
            singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) m) theta := by
  let A : Nat -> CardSet.{u} := fun k =>
    singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))
  have hRegulars : forall k, SetOfRegulars (A k) := by
    intro k beta hBeta
    change beta = Cardinal.aleph ((k : Ordinal.{u}) + 1) at hBeta
    rw [hBeta]
    exact Cardinal.isRegular_aleph_add_one (k : Ordinal.{u})
  have hThetaGt : targetAlephOmega < theta :=
    alephSuccSet_tail_maxPcf_theta_gt_targetAlephOmega n hMax
  intro m
  by_cases hnm : n <= m
  · simpa [A] using
      (alephSuccSet_tail_maxPcf_witness_isMaxPcf_all_deeper_tails
        n hMax m hnm)
  · have hmn : m <= n := Nat.le_of_not_ge hnm
    constructor
    · simpa [A] using
        (alephSuccSet_tail_maxPcf_witness_mem_pcf_all_tails n hMax m)
    · intro beta hBeta
      have hSplit :
          UnionCardSet
            (FinsetUnionCardSet
              ((Finset.range (n + 1)).filter (fun k => m < k))
              (fun k => cardinalProductRepresentation.pcf (A k)))
            (cardinalProductRepresentation.pcf
              (natTailIUnionCardSet A n)) beta := by
        rw [← cardinalProductRepresentation_pcf_natTail_eq_finiteDifference_union_tail
          A hRegulars hmn]
        simpa [A] using hBeta
      cases hSplit with
      | inl hFinite =>
          obtain ⟨k, _hk, hBetaComponent⟩ := hFinite
          have hBetaEq : beta = Cardinal.aleph ((k : Ordinal.{u}) + 1) :=
            (cardinalProductRepresentation_mem_pcf_singleton_iff
              (Cardinal.isRegular_aleph_add_one (k : Ordinal.{u}))).mp
              (by simpa [A] using hBetaComponent)
          rw [hBetaEq]
          exact (alephSuccSet_belowAlephOmega _ ⟨k, rfl⟩).le.trans
            (le_of_lt hThetaGt)
      | inr hTail =>
          exact hMax.2 beta (by simpa [A] using hTail)

theorem alephSuccSet_maxPcfWitness_of_tail
    (n : Nat)
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation
      (natTailIUnionCardSet
        (fun k : Nat =>
          singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) n) theta) :
    IsMaxPcf cardinalProductRepresentation alephSuccSet theta := by
  have hTailZero : IsMaxPcf cardinalProductRepresentation
      (natTailIUnionCardSet
        (fun k : Nat =>
          singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) 0) theta :=
    alephSuccSet_tail_maxPcf_witness_isMaxPcf_all_tails n hMax 0
  have hThetaGt : targetAlephOmega < theta :=
    alephSuccSet_tail_maxPcf_theta_gt_targetAlephOmega n hMax
  unfold IsMaxPcf
  rw [cardinalProductRepresentation_pcf_alephSuccSet_eq_first_union_zero_tail]
  constructor
  · exact Or.inr hTailZero.left
  · intro beta hBeta
    cases hBeta with
    | inl hFirst =>
        have hBetaEq : beta = Cardinal.aleph ((0 : Ordinal.{u}) + 1) :=
          (cardinalProductRepresentation_mem_pcf_singleton_iff
            (Cardinal.isRegular_aleph_add_one (0 : Ordinal.{u}))).mp hFirst
        rw [hBetaEq]
        exact (alephSuccSet_belowAlephOmega _ ⟨0, rfl⟩).le.trans
          (le_of_lt hThetaGt)
    | inr hTail =>
        exact hTailZero.right beta hTail

theorem alephSuccSet_maxPcf_witness_isMaxPcf_all_tails
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation alephSuccSet theta) :
    forall m,
      IsMaxPcf cardinalProductRepresentation
        (natTailIUnionCardSet
          (fun k : Nat =>
            singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))) m) theta := by
  let A : Nat -> CardSet.{u} := fun k =>
    singletonCardSet (Cardinal.aleph ((k : Ordinal.{u}) + 1))
  have hEq : alephSuccSet.{u} = iUnionCardSet A := by
    simpa [A] using alephSuccSet_eq_iUnion_singleton
  have hRegulars : forall k, SetOfRegulars (A k) := by
    intro k beta hBeta
    change beta = Cardinal.aleph ((k : Ordinal.{u}) + 1) at hBeta
    rw [hBeta]
    exact Cardinal.isRegular_aleph_add_one (k : Ordinal.{u})
  have hFullMem :
      cardinalProductRepresentation.pcf (iUnionCardSet A) theta := by
    rw [← hEq]
    exact hMax.left
  obtain ⟨hRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := iUnionCardSet A) (theta := theta)).mp hFullMem
  have hNonprincipal : forall i,
      Not (canonicalIUnionIndexIdeal A J = Ideal.excludePoint i) := by
    intro i hPrincipal
    have hEventually : J.Eventually (fun k => A i k.1) :=
      canonicalIUnion_eventually_component_of_indexIdeal_eq_excludePoint
        A hUltra hPrincipal
    have hComponentPcf : cardinalProductRepresentation.pcf (A i) theta :=
      cardinalProductRepresentation_mem_pcf_of_eventually_mem
        (A := A i) (B := iUnionCardSet A)
        (by
          intro beta hBeta
          exact ⟨i, hBeta⟩)
        (setOfRegulars_iUnion_of_forall A hRegulars)
        hRegular J hUltra hTcf hEventually
    have hThetaEq :
        theta = Cardinal.aleph ((i : Ordinal.{u}) + 1) := by
      apply (cardinalProductRepresentation_mem_pcf_singleton_iff
        (Cardinal.isRegular_aleph_add_one (i : Ordinal.{u}))).mp
      simpa [A] using hComponentPcf
    have hNextPcf :
        cardinalProductRepresentation.pcf (iUnionCardSet A)
          (Cardinal.aleph (((i + 1 : Nat) : Ordinal.{u}) + 1)) := by
      apply cardinalProductRepresentation_mem_pcf_of_mem
        (setOfRegulars_iUnion_of_forall A hRegulars)
      exact ⟨i + 1, by
        simpa [A] using (show A (i + 1)
          (Cardinal.aleph (((i + 1 : Nat) : Ordinal.{u}) + 1)) from rfl)⟩
    have hNextPcfGlobal :
        cardinalProductRepresentation.pcf alephSuccSet
          (Cardinal.aleph (((i + 1 : Nat) : Ordinal.{u}) + 1)) := by
      rw [hEq]
      exact hNextPcf
    have hNextLe :
        Cardinal.aleph (((i + 1 : Nat) : Ordinal.{u}) + 1) <= theta :=
      hMax.right _ hNextPcfGlobal
    have hThetaLt :
        theta < Cardinal.aleph (((i + 1 : Nat) : Ordinal.{u}) + 1) := by
      rw [hThetaEq]
      apply Cardinal.aleph_lt_aleph.mpr
      simpa only [Nat.cast_add, Nat.cast_one] using
        (lt_add_one ((i : Ordinal.{u}) + 1))
    exact (not_lt_of_ge hNextLe) hThetaLt
  have hTailMem : forall m,
      cardinalProductRepresentation.pcf (natTailIUnionCardSet A m) theta :=
    cardinalProductRepresentation_mem_pcf_all_natTails_of_nonprincipal_indexIdeal
      A hRegulars hRegular J hUltra hTcf hNonprincipal
  intro m
  constructor
  · simpa [A] using hTailMem m
  · intro beta hBeta
    have hBetaFull :
        cardinalProductRepresentation.pcf (iUnionCardSet A) beta :=
      cardinalProductRepresentation_pcf_mono
        (natTailIUnionCardSet_subset_iUnionCardSet A m)
        (setOfRegulars_iUnion_of_forall A hRegulars)
        beta hBeta
    have hBetaGlobal :
        cardinalProductRepresentation.pcf alephSuccSet beta := by
      rw [hEq]
      exact hBetaFull
    exact hMax.right beta hBetaGlobal

/-! The full successor-aleph maximum has the same strict lower bound as every
    strict tail.  The proof transports the supplied full maximum to the zero
    tail, where the cofinality argument has already been established. -/
theorem alephSuccSet_maxPcf_theta_ge_targetAlephOmega
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf cardinalProductRepresentation alephSuccSet theta) :
    targetAlephOmega <= theta := by
  exact alephSuccSet_tail_maxPcf_theta_ge_targetAlephOmega 0
    (alephSuccSet_maxPcf_witness_isMaxPcf_all_tails hMax 0)

#print axioms alephSuccSet_maxPcf_theta_ge_targetAlephOmega

/-! 自然数双射给出完整后继阿列夫乘积的可数且无限索引。 -/

noncomputable def alephSuccSetCardinalIndexOfNat (n : Nat) :
    CardinalIndex alephSuccSet.{u} :=
  ⟨Cardinal.aleph ((n : Ordinal.{u}) + 1), ⟨n, rfl⟩⟩

theorem alephSuccSetCardinalIndexOfNat_injective :
    Function.Injective (alephSuccSetCardinalIndexOfNat.{u}) := by
  classical
  intro m n hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hOrd :
        (m : Ordinal.{u}) + 1 < (n : Ordinal.{u}) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_lt.mpr (Nat.add_lt_add_right hlt 1))
    have hCard := Cardinal.aleph_lt_aleph.mpr hOrd
    have hEq :
        Cardinal.aleph ((m : Ordinal.{u}) + 1) =
          Cardinal.aleph ((n : Ordinal.{u}) + 1) :=
      congrArg Subtype.val hmn
    exact (ne_of_lt hCard) hEq
  · have hOrd :
        (n : Ordinal.{u}) + 1 < (m : Ordinal.{u}) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_lt.mpr (Nat.add_lt_add_right hlt 1))
    have hCard := Cardinal.aleph_lt_aleph.mpr hOrd
    have hEq :
        Cardinal.aleph ((m : Ordinal.{u}) + 1) =
          Cardinal.aleph ((n : Ordinal.{u}) + 1) :=
      congrArg Subtype.val hmn
    exact (ne_of_lt hCard) hEq.symm

/-! The explicit successor-aleph enumeration covers every canonical product
coordinate. Together with injectivity, this records the exact countable shape
of the index type without treating its ambient universe as countable by
definitional equality. -/
theorem alephSuccSetCardinalIndexOfNat_surjective :
    Function.Surjective (alephSuccSetCardinalIndexOfNat.{u}) := by
  rintro ⟨theta, ⟨n, hTheta⟩⟩
  exact ⟨n, Subtype.ext hTheta.symm⟩

#print axioms alephSuccSetCardinalIndexOfNat_surjective

/-! Although the canonical index type lives one universe above its cardinal
members, the displayed Nat enumeration makes it small in the cardinal
universe. This is universe bookkeeping, not a PCF scale construction. -/
theorem alephSuccSet_cardinalIndex_small :
    Small.{u} (CardinalIndex alephSuccSet.{u}) := by
  letI : Small.{0} (CardinalIndex alephSuccSet.{u}) := by
    exact small_of_surjective alephSuccSetCardinalIndexOfNat_surjective
  exact @small_lift.{u + 1, u, 0} _ _

#print axioms alephSuccSet_cardinalIndex_small

theorem alephSuccSet_cardinalIndex_infinite :
    Infinite (CardinalIndex alephSuccSet.{u}) := by
  exact Infinite.of_injective
    (alephSuccSetCardinalIndexOfNat.{u})
    (alephSuccSetCardinalIndexOfNat_injective.{u})

/-! 完整核心中的 PCF 元素具有严格的不可数下界。 -/

theorem alephSuccSet_pcf_mem_gt_aleph0
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf alephSuccSet theta) :
    Cardinal.aleph0 < theta := by
  apply cardinalProductRepresentation_mem_pcf_gt_aleph0_of_no_nat_cofinal_family
    (A := alephSuccSet) (theta := theta)
  · intro J hProper d
    apply cardinalProductFrame_not_isCofinalFamily_nat_of_aleph0_lt
      (A := alephSuccSet) (J := J) (d := d)
    · exact alephSuccSet_regulars
    · intro beta hBeta
      obtain ⟨n, rfl⟩ := hBeta
      exact Cardinal.aleph0_lt_aleph.mpr
        ((zero_le : (0 : Ordinal.{u}) <= (n : Ordinal.{u})).trans_lt
          (lt_add_one _))
    · exact hProper
  · exact hPcf

#print axioms alephSuccSet_pcf_mem_gt_aleph0

/-! 同一不可数下界对每个严格尾部成立。 -/

theorem alephSuccSet_tail_pcf_mem_gt_aleph0
    (n : Nat)
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
      theta) :
    Cardinal.aleph0 < theta := by
  apply cardinalProductRepresentation_mem_pcf_gt_aleph0_of_no_nat_cofinal_family
    (A := natTailIUnionCardSet
      (fun m : Nat =>
        singletonCardSet
          (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
    (theta := theta)
  · intro J hProper d
    apply cardinalProductFrame_not_isCofinalFamily_nat_of_aleph0_lt
      (A := natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
      (J := J) (d := d)
    · intro beta hBeta
      obtain ⟨m, _hmn, hBeta⟩ := hBeta
      change beta = Cardinal.aleph ((m : Ordinal.{u}) + 1) at hBeta
      subst beta
      exact Cardinal.isRegular_aleph_add_one (m : Ordinal.{u})
    · intro beta hBeta
      obtain ⟨m, _hmn, hBeta⟩ := hBeta
      change beta = Cardinal.aleph ((m : Ordinal.{u}) + 1) at hBeta
      subst beta
      exact Cardinal.aleph0_lt_aleph.mpr
        ((zero_le : (0 : Ordinal.{u}) <= (m : Ordinal.{u})).trans_lt
          (lt_add_one _))
    · exact hProper
  · exact hPcf

#print axioms alephSuccSet_tail_pcf_mem_gt_aleph0

/-! 完整核心的索引基数为 `aleph0`，其 PCF 值受可数幂控制。 -/

theorem alephSuccSet_cardinalIndex_mk_eq_aleph0 :
    Cardinal.mk (CardinalIndex alephSuccSet.{u}) = Cardinal.aleph0 := by
  letI : Infinite (CardinalIndex alephSuccSet.{u}) :=
    alephSuccSet_cardinalIndex_infinite
  letI : Countable (CardinalIndex alephSuccSet.{u}) :=
    Cardinal.mk_le_aleph0_iff.mp alephSuccSet_countable
  exact Cardinal.mk_eq_aleph0 _

#print axioms alephSuccSet_cardinalIndex_mk_eq_aleph0

/-! The full successor-aleph core has the same ambient countable-power bound
    already proved for each strict tail. This is a cardinal-product estimate;
    it does not identify the PCF value with the whole product. -/
theorem alephSuccSet_pcf_theta_le_alephOmega_power_aleph0
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.{u}.pcf
      alephSuccSet.{u} theta) :
    exists J : Ideal (CardinalIndex alephSuccSet.{u}),
      J.IsUltrafilterDual /\
      Cardinal.lift.{u + 1} theta <=
        (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^
          Cardinal.aleph0 := by
  obtain ⟨J, hUltra, hBound⟩ :=
    cardinalProductRepresentation_pcf_theta_le_power_of_countable_below_alephOmega
      alephSuccSet_countable alephSuccSet_belowAlephOmega hPcf
  refine ⟨J, hUltra, ?_⟩
  exact hBound

#print axioms alephSuccSet_pcf_theta_le_alephOmega_power_aleph0

/-! 严格尾部也有显式自然数索引和相同的可数幂上界。 -/

noncomputable def alephSuccSetTailCardinalIndexOfNat (n k : Nat) :
    CardinalIndex
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) :=
  ⟨Cardinal.aleph (((n + k + 1 : Nat) : Ordinal.{u}) + 1),
    ⟨n + k + 1, by omega, rfl⟩⟩

theorem alephSuccSetTailCardinalIndexOfNat_injective (n : Nat) :
    Function.Injective (alephSuccSetTailCardinalIndexOfNat.{u} n) := by
  classical
  intro k l hkl
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hOrd :
        ((n + k + 1 : Nat) : Ordinal.{u}) + 1 <
          ((n + l + 1 : Nat) : Ordinal.{u}) + 1 := by
      have hNat : n + k + 2 < n + l + 2 :=
        Nat.add_lt_add_right (Nat.add_lt_add_left hlt n) 2
      have hOrdNat :
          ((n + k + 2 : Nat) : Ordinal.{u}) <
            ((n + l + 2 : Nat) : Ordinal.{u}) :=
        Nat.cast_lt.mpr hNat
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hOrdNat
    have hCard := Cardinal.aleph_lt_aleph.mpr hOrd
    have hEq :
        Cardinal.aleph (((n + k + 1 : Nat) : Ordinal.{u}) + 1) =
          Cardinal.aleph (((n + l + 1 : Nat) : Ordinal.{u}) + 1) :=
      congrArg Subtype.val hkl
    exact (ne_of_lt hCard) hEq
  · have hOrd :
        ((n + l + 1 : Nat) : Ordinal.{u}) + 1 <
          ((n + k + 1 : Nat) : Ordinal.{u}) + 1 := by
      have hNat : n + l + 2 < n + k + 2 :=
        Nat.add_lt_add_right (Nat.add_lt_add_left hlt n) 2
      have hOrdNat :
          ((n + l + 2 : Nat) : Ordinal.{u}) <
            ((n + k + 2 : Nat) : Ordinal.{u}) :=
        Nat.cast_lt.mpr hNat
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hOrdNat
    have hCard := Cardinal.aleph_lt_aleph.mpr hOrd
    have hEq :
        Cardinal.aleph (((n + k + 1 : Nat) : Ordinal.{u}) + 1) =
          Cardinal.aleph (((n + l + 1 : Nat) : Ordinal.{u}) + 1) :=
      congrArg Subtype.val hkl
    exact (ne_of_lt hCard) hEq.symm

/-! The displayed tail enumeration covers every coordinate.  The subtraction
used to recover its Nat parameter is justified by the strict tail-membership
proof carried by the coordinate. -/
theorem alephSuccSetTailCardinalIndexOfNat_surjective (n : Nat) :
    Function.Surjective (alephSuccSetTailCardinalIndexOfNat.{u} n) := by
  rintro ⟨theta, ⟨m, hnm, hTheta⟩⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm
  refine ⟨k, Subtype.ext ?_⟩
  change Cardinal.aleph (((n + k + 1 : Nat) : Ordinal.{u}) + 1) = theta
  change theta = Cardinal.aleph ((m : Ordinal.{u}) + 1) at hTheta
  have hIndex : n + k + 1 = m := by omega
  simpa only [hIndex] using hTheta.symm

#print axioms alephSuccSetTailCardinalIndexOfNat_surjective

/-! Each strict successor-aleph tail has a canonical index small in the
cardinal universe, by its explicit Nat enumeration.  This is precisely the
universe reduction needed to turn its Zorn quotient cofinality into a scale. -/
theorem alephSuccSet_tail_cardinalIndex_small (n : Nat) :
    Small.{u}
      (CardinalIndex
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) := by
  letI : Small.{0}
      (CardinalIndex
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) := by
    exact small_of_surjective (alephSuccSetTailCardinalIndexOfNat_surjective n)
  exact @small_lift.{u + 1, u, 0} _ _

#print axioms alephSuccSet_tail_cardinalIndex_small

theorem alephSuccSet_tail_cardinalIndex_infinite (n : Nat) :
    Infinite
      (CardinalIndex
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) := by
  exact Infinite.of_injective
    (alephSuccSetTailCardinalIndexOfNat.{u} n)
    (alephSuccSetTailCardinalIndexOfNat_injective.{u} n)

theorem alephSuccSet_tail_cardinalIndex_mk_eq_aleph0
    (n : Nat) :
    Cardinal.mk
        (CardinalIndex
          (natTailIUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) =
      Cardinal.aleph0 := by
  letI : Infinite
      (CardinalIndex
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) :=
    alephSuccSet_tail_cardinalIndex_infinite n
  letI : Countable
      (CardinalIndex
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) :=
    Cardinal.mk_le_aleph0_iff.mp (alephSuccSet_tail_countable n)
  exact Cardinal.mk_eq_aleph0 _

#print axioms alephSuccSet_tail_cardinalIndex_mk_eq_aleph0

theorem alephSuccSet_tail_pcf_theta_le_alephOmega_power_aleph0
    (n : Nat)
    {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.{u}.pcf
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
      theta) :
    exists J : Ideal
        (CardinalIndex
          (natTailIUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)),
      J.IsUltrafilterDual /\
      Cardinal.lift.{u + 1} theta <=
        (Cardinal.lift.{u + 1} targetAlephOmega.{u}) ^
          Cardinal.aleph0 := by
  obtain ⟨J, hUltra, hBound⟩ :=
    cardinalProductRepresentation_pcf_theta_le_power_of_countable_below_alephOmega
      (alephSuccSet_tail_countable n)
      (alephSuccSet_tail_alephOmegaCore n).belowAlephOmega
      hPcf
  refine ⟨J, hUltra, ?_⟩
  exact hBound

#print axioms alephSuccSet_tail_pcf_theta_le_alephOmega_power_aleph0

/-! 核心证明只需要上面的可数尾部乘积估计；其后的旧终端接口均不参与主定理。 -/

end PcfProject
