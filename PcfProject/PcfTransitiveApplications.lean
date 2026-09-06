import PcfProject.PcfTransitiveGenerators
import PcfProject.PcfContinuumBridge

/-!
# Transitive-generator applications to the successor-aleph tail

This module applies the formalized Jech 24.31 construction to a sufficiently
high finite tail of the successor alephs below `aleph_omega`.  The tail is
chosen above one additional successor of the double-powerset bound, which is
the exact margin required after passing to the PCF spectrum.
-/

open Cardinal Set
open scoped Cardinal

namespace PcfProject

universe u

/-! Generator capture is insensitive to discarding coordinates outside an
eventual subfamily.  This is the bridge needed when a club ultrafilter on an
initial successor-aleph segment eventually lies in the high tail on which the
transitive generators were constructed. -/
theorem GeneratorCapturesCanonicalUltrafilters.eventually_of_eventually_subset
    {A : CardSet.{u}}
    {G : GeneratorSystem cardinalProductRepresentation A}
    (hCapture : GeneratorCapturesCanonicalUltrafilters G)
    {W : CardSet.{u}}
    (hRegularsW : SetOfRegulars W)
    (J : Ideal (CardinalIndex W))
    (hUltra : J.IsUltrafilterDual)
    (theta : Cardinal.{u})
    (hThetaRegular : Cardinal.IsRegular theta)
    (hThetaPcf : cardinalProductRepresentation.pcf A theta)
    (hTcf : HasTrueCofinality
      (cardinalProductFrame W J)
      (cardinalScaleLength theta))
    (hEventuallyA : J.Eventually (fun i => A i.1)) :
    J.Eventually (fun i => G.generator theta i.1) := by
  let V : CardSet.{u} := InterCardSet W A
  have hVW : SubsetOf V W := by
    intro gamma hGamma
    exact hGamma.1
  have hVA : SubsetOf V A := by
    intro gamma hGamma
    exact hGamma.2
  let f := cardinalIndexMap hVW
  let JV := J.restrictAlong f
  have hRange : J.Eventually (fun k => exists i, f i = k) := by
    apply (J.eventually_congr (fun k => ?_)).mpr hEventuallyA
    rw [cardinalIndexMap_mem_range_iff hVW]
    simp only [V, InterCardSet, k.2, true_and]
  have hUltraV : JV.IsUltrafilterDual :=
    hUltra.restrictAlong f (cardinalIndexMap_injective hVW) hRange
  have hPush : JV.pushforward f = J :=
    J.restrictAlong_pushforward_eq f hRange
  have hTcfPush : HasTrueCofinality
      (cardinalProductFrame W
        (JV.pushforward (cardinalIndexMap hVW)))
      (cardinalScaleLength theta) := by
    simpa only [f, hPush] using hTcf
  have hTcfV : HasTrueCofinality
      (cardinalProductFrame V JV)
      (cardinalScaleLength theta) :=
    restrictCardinalScale_hasTrueCofinality
      hVW hRegularsW hTcfPush
  have hCaptureV :
      JV.Eventually (fun i => G.generator theta i.1) :=
    hCapture V hVA JV hUltraV theta hThetaRegular hThetaPcf hTcfV
  have hViaPush :
      (JV.pushforward f).Eventually
        (fun k => G.generator theta k.1) := by
    rw [Ideal.pushforward_eventually_iff]
    simpa only [f, cardinalIndexMap] using hCaptureV
  simpa only [hPush] using hViaPush

#print axioms
  GeneratorCapturesCanonicalUltrafilters.eventually_of_eventually_subset

/-- Under the strong-limit hypothesis, a finite successor-aleph tail lies
strictly above the successor of its double-powerset index bound. -/
theorem exists_alephSuccSet_tail_successorDoublePowerBelow_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    exists n : Nat,
      @CardinalProductSuccessorDoublePowerBelowCoordinates.{u}
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
        (alephSuccSet_tail_cardinalIndex_small n) := by
  let delta : Cardinal.{u} :=
    (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Cardinal.aleph0)
  let epsilon : Cardinal.{u} := (2 : Cardinal.{u}) ^ delta
  have hContinuum : (2 : Cardinal.{u}) ^ Cardinal.aleph0 <
      targetAlephOmega :=
    two_power_aleph0_lt_targetAlephOmega_of_strongLimit hStrongLimit
  have hDelta : delta < targetAlephOmega := by
    exact hStrongLimit.isStrongPrelimit hContinuum
  have hEpsilon : epsilon < targetAlephOmega := by
    exact hStrongLimit.isStrongPrelimit hDelta
  obtain ⟨theta, hTheta, hEpsilonTheta, _hThetaTarget⟩ :=
    alephSuccSet_cofinalInAlephOmega epsilon hEpsilon
  obtain ⟨n, hThetaEq⟩ := hTheta
  refine ⟨n, ?_⟩
  letI : Small.{u}
      (CardinalIndex
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) :=
    alephSuccSet_tail_cardinalIndex_small n
  intro a
  obtain ⟨m, hnm, hm⟩ := a.2
  have hThetaLtA : theta < a.1 := by
    rw [hThetaEq, hm]
    have hnmOrd : (n : Ordinal.{u}) < (m : Ordinal.{u}) := by
      simpa only [Nat.cast_lt] using hnm
    exact Cardinal.aleph_lt_aleph.mpr (by
      simpa only [Order.succ_eq_add_one] using Order.succ_lt_succ hnmOrd)
  have hEpsilonA : epsilon < a.1 := hEpsilonTheta.trans hThetaLtA
  have hShrinkEq : Cardinal.mk
      (Shrink.{u}
        (CardinalIndex
          (natTailIUnionCardSet
            (fun m : Nat => singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n))) =
      Cardinal.aleph0 := by
    rw [← Cardinal.lift_inj.{u, u + 1}]
    simp only [Cardinal.lift_mk_shrink'', Cardinal.lift_aleph0,
      alephSuccSet_tail_cardinalIndex_mk_eq_aleph0]
  rw [hShrinkEq]
  exact (Order.succ_le_iff.mpr (Cardinal.cantor delta)).trans_lt hEpsilonA

#print axioms
  exists_alephSuccSet_tail_successorDoublePowerBelow_of_strongLimit

/-- The selected tail carries transitive, successor-directed generators on
its PCF spectrum, with no generator premise left to the caller. -/
theorem exists_alephSuccSet_tail_pcf_transitiveGenerators_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    exists n : Nat, exists G : GeneratorSystem cardinalProductRepresentation
        (cardinalProductRepresentation.pcf
          (natTailIUnionCardSet
            (fun m : Nat => singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)),
      @CardinalProductSuccessorDoublePowerBelowCoordinates.{u}
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
        (alephSuccSet_tail_cardinalIndex_small n) /\
        TransitiveGeneratorSystem G /\
        GeneratorAtMostIdealSuccessorDirected G := by
  obtain ⟨n, hSuccessorDouble⟩ :=
    exists_alephSuccSet_tail_successorDoublePowerBelow_of_strongLimit.{u}
      hStrongLimit
  let T : CardSet.{u} :=
    natTailIUnionCardSet
      (fun m : Nat => singletonCardSet
        (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n
  letI : Small.{u} (CardinalIndex T) :=
    alephSuccSet_tail_cardinalIndex_small n
  have hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex T) := by
    rw [alephSuccSet_tail_cardinalIndex_mk_eq_aleph0]
  obtain ⟨G, hTransitive, hDirected⟩ :=
    exists_pcf_transitive_successorDirected_generators_of_successorDoublePower
      (alephSuccSet_tail_alephOmegaCore n).regulars hInfinite hSuccessorDouble
  exact ⟨n, G, hSuccessorDouble, hTransitive, hDirected⟩

#print axioms
  exists_alephSuccSet_tail_pcf_transitiveGenerators_of_strongLimit

/-! Above the omitted finite prefix, every successor aleph already known to
belong to the full core spectrum belongs to the spectrum of the selected
strict tail. -/
theorem successorAleph_mem_tailPcf_of_mem_corePcf
    (n : Nat) {i : Ordinal.{u}}
    (hCore : cardinalProductRepresentation.pcf alephSuccSet
      (Cardinal.aleph (i + 1)))
    (hni : (n : Ordinal.{u}) < i) :
    cardinalProductRepresentation.pcf
      (natTailIUnionCardSet
        (fun m : Nat => singletonCardSet
          (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
      (Cardinal.aleph (i + 1)) := by
  classical
  let A : Nat -> CardSet.{u} := fun m =>
    singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))
  let P : CardSet.{u} := natPrefixIUnionCardSet A n
  let T : CardSet.{u} := natTailIUnionCardSet A n
  have hRegularsA : forall m, SetOfRegulars (A m) := by
    intro m gamma hGamma
    change gamma = Cardinal.aleph ((m : Ordinal.{u}) + 1) at hGamma
    rw [hGamma]
    exact Cardinal.isRegular_aleph_add_one (m : Ordinal.{u})
  have hRegularsP : SetOfRegulars P := by
    rw [show P = natPrefixIUnionCardSet A n from rfl,
      natPrefixIUnionCardSet_eq_finsetUnion_range]
    exact finsetUnionCardSet_regulars hRegularsA
  have hRegularsT : SetOfRegulars T :=
    natTailIUnionCardSet_setOfRegulars A hRegularsA n
  have hPcfSplit : cardinalProductRepresentation.pcf alephSuccSet.{u} =
      UnionCardSet (cardinalProductRepresentation.pcf P)
        (cardinalProductRepresentation.pcf T) := by
    rw [alephSuccSet_eq_iUnion_singleton,
      iUnionCardSet_eq_union_natPrefix_natTail A n]
    exact cardinalProductRepresentation_pcf_union hRegularsP hRegularsT
  have hPFinite : Finite (CardinalIndex P) := by
    rw [show P = natPrefixIUnionCardSet A n from rfl,
      natPrefixIUnionCardSet_eq_finsetUnion_range]
    exact finite_cardinalIndex_finsetUnion (Finset.range (n + 1)) A
      (fun m _hm => finite_cardinalIndex_singleton _)
  letI : Finite (CardinalIndex P) := hPFinite
  have hPcfP : cardinalProductRepresentation.pcf P = P :=
    cardinalProductRepresentation_pcf_eq_of_finite hRegularsP
  have hSplit := hCore
  rw [hPcfSplit] at hSplit
  cases hSplit with
  | inl hPrefix =>
      rw [hPcfP] at hPrefix
      obtain ⟨m, hmn, hm⟩ := hPrefix
      have hSuccEq : i + 1 = (m : Ordinal.{u}) + 1 :=
        Cardinal.aleph.injective hm
      have hiEq : i = (m : Ordinal.{u}) := by
        exact (Ordinal.add_right_cancel 1).mp
          (by simpa only [Nat.cast_one] using hSuccEq)
      have hmLe : (m : Ordinal.{u}) <= (n : Ordinal.{u}) := by
        exact_mod_cast hmn
      exact False.elim ((not_lt_of_ge hmLe) (hiEq ▸ hni))
  | inr hTail =>
      exact hTail

#print axioms successorAleph_mem_tailPcf_of_mem_corePcf

/-! Every club-extending ultrafilter on an uncountable-cofinality initial
segment is eventually supported by the PCF spectrum of any fixed strict
finite tail. -/
theorem successorAlephIio_eventually_mem_tailPcf
    (n : Nat) {theta eta : Ordinal.{u}}
    (hEtaTheta : eta < theta)
    (hEtaLimit : Order.IsSuccLimit eta)
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta)
    (J : Ideal (Set.Iio eta))
    (hClubs : forall C : Set (Set.Iio eta), IsClub C ->
      J.Eventually (fun i => i ∈ C)) :
    (J.pushforward (successorAlephIioCardinalIndex eta)).Eventually
      (fun k => cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) k.1) := by
  let a : Set.Iio eta :=
    ⟨((n + 1 : Nat) : Ordinal.{u}),
      Ordinal.natCast_lt_of_isSuccLimit hEtaLimit (n + 1)⟩
  rw [Ideal.pushforward_eventually_iff]
  apply J.eventually_mono (hClubs (Set.Ici a) (isClub_Ici a))
  intro j hj
  have hnj : (n : Ordinal.{u}) < j.1 := by
    have hnSucc : (n : Ordinal.{u}) < ((n + 1 : Nat) : Ordinal.{u}) := by
      exact_mod_cast Nat.lt_succ_self n
    exact hnSucc.trans_le hj
  simpa only [successorAlephIioCardinalIndex] using
    successorAleph_mem_tailPcf_of_mem_corePcf n
      (hCore j.1 (j.2.trans hEtaTheta)) hnj

#print axioms successorAlephIio_eventually_mem_tailPcf

/-- Maximum PCF witnesses combine across a binary union of regular sets. -/
theorem cardinalProductRepresentation_hasMaxPcf_union_of_hasMaxPcf
    {B C : CardSet.{u}} (hRegularsB : SetOfRegulars B)
    (hRegularsC : SetOfRegulars C)
    (hMaxB : HasMaxPcf cardinalProductRepresentation B)
    (hMaxC : HasMaxPcf cardinalProductRepresentation C) :
    HasMaxPcf cardinalProductRepresentation (UnionCardSet B C) := by
  obtain ⟨beta, hBetaMem, hBetaMax⟩ := hMaxB
  obtain ⟨gamma, hGammaMem, hGammaMax⟩ := hMaxC
  by_cases hBetaGamma : beta <= gamma
  · refine ⟨gamma, ?_, ?_⟩
    · rw [cardinalProductRepresentation_pcf_union hRegularsB hRegularsC]
      exact Or.inr hGammaMem
    · intro delta hDelta
      rw [cardinalProductRepresentation_pcf_union hRegularsB hRegularsC]
        at hDelta
      exact hDelta.elim
        (fun h => (hBetaMax delta h).trans hBetaGamma)
        (fun h => hGammaMax delta h)
  · have hGammaBeta : gamma <= beta := le_of_not_ge hBetaGamma
    refine ⟨beta, ?_, ?_⟩
    · rw [cardinalProductRepresentation_pcf_union hRegularsB hRegularsC]
      exact Or.inl hBetaMem
    · intro delta hDelta
      rw [cardinalProductRepresentation_pcf_union hRegularsB hRegularsC]
        at hDelta
      exact hDelta.elim
        (fun h => hBetaMax delta h)
        (fun h => (hGammaMax delta h).trans hGammaBeta)

#print axioms
  cardinalProductRepresentation_hasMaxPcf_union_of_hasMaxPcf

/-- Compact generators on one strict tail prove maximum existence for every
nonempty successor-aleph subfamily whose coordinates lie in the full core
spectrum. The omitted finite prefix is handled by the finite PCF theorem. -/
theorem successorAlephHasMaxPcfBelow_of_tailGeneratorCompactCover
    (n : Nat)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)))
    (hCompact : GeneratorCompactCover G)
    {theta : Ordinal.{u}}
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    SuccessorAlephHasMaxPcfBelow theta := by
  classical
  let A : Nat -> CardSet.{u} := fun m =>
    singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))
  let P : CardSet.{u} := natPrefixIUnionCardSet A n
  let T : CardSet.{u} := natTailIUnionCardSet A n
  have hRegularsA : forall m, SetOfRegulars (A m) := by
    intro m gamma hGamma
    change gamma = Cardinal.aleph ((m : Ordinal.{u}) + 1) at hGamma
    rw [hGamma]
    exact Cardinal.isRegular_aleph_add_one (m : Ordinal.{u})
  have hRegularsP : SetOfRegulars P := by
    rw [show P = natPrefixIUnionCardSet A n from rfl,
      natPrefixIUnionCardSet_eq_finsetUnion_range]
    exact finsetUnionCardSet_regulars hRegularsA
  have hRegularsT : SetOfRegulars T :=
    natTailIUnionCardSet_setOfRegulars A hRegularsA n
  have hPcfSplit : cardinalProductRepresentation.pcf alephSuccSet.{u} =
      UnionCardSet (cardinalProductRepresentation.pcf P)
        (cardinalProductRepresentation.pcf T) := by
    rw [alephSuccSet_eq_iUnion_singleton,
      iUnionCardSet_eq_union_natPrefix_natTail A n]
    exact cardinalProductRepresentation_pcf_union hRegularsP hRegularsT
  have hPFinite : Finite (CardinalIndex P) := by
    rw [show P = natPrefixIUnionCardSet A n from rfl,
      natPrefixIUnionCardSet_eq_finsetUnion_range]
    exact finite_cardinalIndex_finsetUnion (Finset.range (n + 1)) A
      (fun m _hm => finite_cardinalIndex_singleton _)
  letI : Finite (CardinalIndex P) := hPFinite
  have hPcfP : cardinalProductRepresentation.pcf P = P :=
    cardinalProductRepresentation_pcf_eq_of_finite hRegularsP
  intro X hXTheta hXNonempty
  let W : CardSet.{u} := successorAlephCardSet X
  have hWFull : SubsetOf W
      (cardinalProductRepresentation.pcf alephSuccSet.{u}) := by
    intro gamma hGamma
    obtain ⟨i, hiX, rfl⟩ := hGamma
    exact hCore i (hXTheta hiX)
  let XP : CardSet.{u} :=
    InterCardSet W (cardinalProductRepresentation.pcf P)
  let XT : CardSet.{u} :=
    InterCardSet W (cardinalProductRepresentation.pcf T)
  have hWEq : W = UnionCardSet XP XT := by
    funext gamma
    apply propext
    constructor
    · intro hGammaW
      have hSplit := hWFull gamma hGammaW
      rw [hPcfSplit] at hSplit
      exact hSplit.elim
        (fun h => Or.inl ⟨hGammaW, h⟩)
        (fun h => Or.inr ⟨hGammaW, h⟩)
    · intro hGamma
      exact hGamma.elim (fun h => h.1) (fun h => h.1)
  have hRegularsW : SetOfRegulars W :=
    setOfRegulars_of_subset hWFull
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
  have hRegularsXP : SetOfRegulars XP :=
    setOfRegulars_of_subset (fun gamma h => h.1) hRegularsW
  have hRegularsXT : SetOfRegulars XT :=
    setOfRegulars_of_subset (fun gamma h => h.1) hRegularsW
  let intoP : CardinalIndex XP -> CardinalIndex P := fun i =>
    ⟨i.1, by
      have hi := i.2.2
      rw [hPcfP] at hi
      exact hi⟩
  have hIntoPInjective : Function.Injective intoP := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : CardinalIndex P => x.1) hij
  letI : Finite (CardinalIndex XP) :=
    Finite.of_injective intoP hIntoPInjective
  have hXTSubset : SubsetOf XT (cardinalProductRepresentation.pcf T) :=
    fun _ h => h.2
  have hWNonempty : exists gamma, W gamma := by
    obtain ⟨i, hiX⟩ := hXNonempty
    exact ⟨Cardinal.aleph (i + 1), ⟨i, hiX, rfl⟩⟩
  change HasMaxPcf cardinalProductRepresentation W
  by_cases hXPNonempty : exists gamma, XP gamma
  · have hMaxXP : HasMaxPcf cardinalProductRepresentation XP :=
      (finiteMaxPcfWitness hRegularsXP hXPNonempty).hasMaxPcf
    by_cases hXTNonempty : exists gamma, XT gamma
    · have hMaxXT : HasMaxPcf cardinalProductRepresentation XT :=
        cardinalProductRepresentation_hasMaxPcf_of_generatorCompactCover
          (cardinalProductRepresentation.pcf_is_setOfRegulars T)
          G hCompact XT hXTSubset hXTNonempty
      rw [hWEq]
      exact cardinalProductRepresentation_hasMaxPcf_union_of_hasMaxPcf
        hRegularsXP hRegularsXT hMaxXP hMaxXT
    · have hWXP : W = XP := by
        funext gamma
        apply propext
        constructor
        · intro hGammaW
          have hUnion : UnionCardSet XP XT gamma := by
            rw [← hWEq]
            exact hGammaW
          exact hUnion.elim (fun h => h)
            (fun h => False.elim (hXTNonempty ⟨gamma, h⟩))
        · exact fun h => h.1
      rw [hWXP]
      exact hMaxXP
  · have hXTNonempty : exists gamma, XT gamma := by
      by_contra hXTEmpty
      obtain ⟨gamma, hGammaW⟩ := hWNonempty
      have hUnion : UnionCardSet XP XT gamma := by
        rw [← hWEq]
        exact hGammaW
      exact hUnion.elim
        (fun h => hXPNonempty ⟨gamma, h⟩)
        (fun h => hXTEmpty ⟨gamma, h⟩)
    have hMaxXT : HasMaxPcf cardinalProductRepresentation XT :=
      cardinalProductRepresentation_hasMaxPcf_of_generatorCompactCover
        (cardinalProductRepresentation.pcf_is_setOfRegulars T)
        G hCompact XT hXTSubset hXTNonempty
    have hWXT : W = XT := by
      funext gamma
      apply propext
      constructor
      · intro hGammaW
        have hUnion : UnionCardSet XP XT gamma := by
          rw [← hWEq]
          exact hGammaW
        exact hUnion.elim
          (fun h => False.elim (hXPNonempty ⟨gamma, h⟩))
          (fun h => h)
      · exact fun h => h.1
    rw [hWXT]
    exact hMaxXT

#print axioms
  successorAlephHasMaxPcfBelow_of_tailGeneratorCompactCover

/-! Corollary 24.30 only needs generators on a sufficiently high finite tail.
The club ultrafilters occurring in Theorem 24.16 eventually lie in that tail
spectrum; adding this support condition to the regressive predicate also
ensures that the final club-restricted family is literally contained in the
tail generator. -/
theorem successorAlephLocalCorollary2430UltrafilterData_of_tailGenerators
    (n : Nat)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G)
    (hPcfFixed : cardinalProductRepresentation.pcf
      (cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) =
      cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n))
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    SuccessorAlephLocalCorollary2430UltrafilterData hMax := by
  intro eta hEtaTheta hEtaLimit hEtaCof hPower
  let T : CardSet.{u} :=
    natTailIUnionCardSet
      (fun m : Nat => singletonCardSet
        (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n
  let W : CardSet.{u} := successorAlephCardSet (Set.Iio eta)
  let lambda : Cardinal.{u} := Cardinal.aleph (eta + 1)
  let P : Set.Iio eta -> Prop := fun i =>
    cardinalProductRepresentation.pcf T
        (Cardinal.aleph (i.1 + 1)) /\
      G.generator lambda (Cardinal.aleph (i.1 + 1))
  have hTcfFor : forall J : Ideal (Set.Iio eta),
      J.IsUltrafilterDual ->
      (forall C : Set (Set.Iio eta), IsClub C ->
        J.Eventually (fun i => i ∈ C)) ->
      HasTrueCofinality
        (cardinalProductFrame W
          (J.pushforward (successorAlephIioCardinalIndex eta)))
        (cardinalScaleLength lambda) := by
    intro J hUltra hClubs
    exact successorAlephLocalTheorem2416UltrafilterTcf
      eta hEtaLimit hEtaCof hPower J hUltra hClubs
  have hnEta : (n : Ordinal.{u}) < eta :=
    Ordinal.natCast_lt_of_isSuccLimit hEtaLimit n
  have hLambdaPcfTail : cardinalProductRepresentation.pcf T lambda := by
    exact successorAleph_mem_tailPcf_of_mem_corePcf n
      (hCore eta hEtaTheta) hnEta
  have hLambdaPcfAmbient : cardinalProductRepresentation.pcf
      (cardinalProductRepresentation.pcf T) lambda := by
    rw [hPcfFixed]
    exact hLambdaPcfTail
  refine ⟨P, ?_, ?_⟩
  · intro J hUltra hClubs
    have hEventuallyTail :
        (J.pushforward (successorAlephIioCardinalIndex eta)).Eventually
          (fun k => cardinalProductRepresentation.pcf T k.1) := by
      exact successorAlephIio_eventually_mem_tailPcf n hEtaTheta
        hEtaLimit hCore J hClubs
    have hEventuallyGenerator :
        (J.pushforward (successorAlephIioCardinalIndex eta)).Eventually
          (fun k => G.generator lambda k.1) := by
      exact hCapture.eventually_of_eventually_subset
        (successorAlephCardSet_regulars (Set.Iio eta))
        (J.pushforward (successorAlephIioCardinalIndex eta))
        (hUltra.pushforward (successorAlephIioCardinalIndex eta))
        lambda (Cardinal.isRegular_aleph_add_one eta)
        hLambdaPcfAmbient (hTcfFor J hUltra hClubs) hEventuallyTail
    have hBoth :=
      (J.pushforward (successorAlephIioCardinalIndex eta)).eventually_and
        hEventuallyTail hEventuallyGenerator
    rw [Ideal.pushforward_eventually_iff] at hBoth
    simpa only [P, successorAlephIioCardinalIndex] using hBoth
  · intro C hCClub hCP
    let X : Set (Ordinal.{u}) :=
      (fun i : Set.Iio eta => i.1) '' C
    have hXTheta : X ⊆ Set.Iio theta := by
      rintro i ⟨j, _hjC, rfl⟩
      exact j.2.trans hEtaTheta
    have hCNonempty : C.Nonempty := by
      letI : Nonempty (Set.Iio eta) := ⟨⟨0, hEtaLimit.bot_lt⟩⟩
      exact isClub_nonempty hCClub
    obtain ⟨i, hiC⟩ := hCNonempty
    have hXNonempty : X.Nonempty := ⟨i.1, ⟨i, hiC, rfl⟩⟩
    have hBoundedNonempty :
        (successorAlephBoundedIndexSet theta X).Nonempty :=
      hXNonempty.mono (fun x hx => ⟨hx, hXTheta hx⟩)
    have hLocalPcf : cardinalProductRepresentation.pcf
        (successorAlephCardSet X)
        (successorAlephLocalMaxPcfCardinal hMax X) := by
      have hRaw := successorAlephLocalMaxPcfCardinal_mem_pcf
        hMax hBoundedNonempty
      have hCardEq :
          successorAlephCardSet
              (successorAlephBoundedIndexSet theta X) =
            successorAlephCardSet X :=
        congrArg successorAlephCardSet
          (successorAlephBoundedIndexSet_eq_of_subset hXTheta)
      rw [hCardEq] at hRaw
      exact hRaw
    have hIntoGenerator : SubsetOf (successorAlephCardSet X)
        (InterCardSet
          (cardinalProductRepresentation.pcf T)
          (G.generator lambda)) := by
      intro gamma hGamma
      obtain ⟨alpha, hAlphaX, rfl⟩ := hGamma
      obtain ⟨j, hjC, rfl⟩ := hAlphaX
      exact ⟨(hCP j hjC).1, (hCP j hjC).2⟩
    have hLocalPcfInGenerator : cardinalProductRepresentation.pcf
        (InterCardSet
          (cardinalProductRepresentation.pcf T)
          (G.generator lambda))
        (successorAlephLocalMaxPcfCardinal hMax X) :=
      cardinalProductRepresentation_pcf_mono hIntoGenerator
        (fun gamma hGamma =>
          (cardinalProductRepresentation.pcf_is_setOfRegulars T)
            gamma hGamma.1)
        _ hLocalPcf
    have hUpper : successorAlephLocalMaxPcfCardinal hMax X <= lambda :=
      G.generator_pcf_le hLambdaPcfAmbient hLocalPcfInGenerator
    have hEtaLeIndex : eta <= successorAlephLocalMaxPcfIndex hMax X := by
      apply le_of_not_gt
      intro hIndexEta
      let k : Set.Iio eta :=
        ⟨successorAlephLocalMaxPcfIndex hMax X, hIndexEta⟩
      obtain ⟨j, hjC, hkj⟩ := hCClub.isCofinal k
      have hjLt := mem_lt_successorAlephLocalMaxPcfIndex hMax
        (X := X) (i := j.1) ⟨j, hjC, rfl⟩
        (j.2.trans hEtaTheta)
      exact (not_lt_of_ge hkj) hjLt
    have hAlephEtaSingular : (Cardinal.aleph eta).IsSingular := by
      rw [Cardinal.isSingular_aleph_iff]
      exact ⟨hEtaLimit, (Cardinal.cantor eta.cof).trans hPower⟩
    have hEtaLtIndex : eta < successorAlephLocalMaxPcfIndex hMax X := by
      apply lt_of_le_of_ne hEtaLeIndex
      intro hEq
      have hLocalRegular : Cardinal.IsRegular
          (successorAlephLocalMaxPcfCardinal hMax X) := by
        rw [successorAlephLocalMaxPcfCardinal_eq_of_nonempty
          hMax hBoundedNonempty]
        exact (successorAlephLocalMaxPcfWitness hMax X
          hBoundedNonempty).isRegular
      apply hLocalRegular.not_isSingular
      rw [← aleph_successorAlephLocalMaxPcfIndex_eq
        hMax hBoundedNonempty, ← hEq]
      exact hAlephEtaSingular
    have hLower : lambda <= successorAlephLocalMaxPcfCardinal hMax X := by
      rw [← aleph_successorAlephLocalMaxPcfIndex_eq
        hMax hBoundedNonempty]
      apply Cardinal.aleph_le_aleph.mpr
      simpa only [Order.succ_eq_add_one] using
        Order.succ_le_iff.mpr hEtaLtIndex
    exact le_antisymm hUpper hLower

#print axioms
  successorAlephLocalCorollary2430UltrafilterData_of_tailGenerators

theorem successorAlephLocalCorollary2430_of_tailGenerators
    (n : Nat)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G)
    (hPcfFixed : cardinalProductRepresentation.pcf
      (cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) =
      cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n))
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    SuccessorAlephLocalCorollary2430 hMax :=
  successorAlephLocalCorollary2430_of_ultrafilterData hMax
    (successorAlephLocalCorollary2430UltrafilterData_of_tailGenerators
      n G hCapture hPcfFixed hMax hCore)

#print axioms successorAlephLocalCorollary2430_of_tailGenerators

/-- Construct all generator and maximum data available on the strong-limit
branch from one selected strict tail. The existential form keeps the package
in `Prop`, as required for choice-free elimination inside later proofs. -/
theorem exists_alephSuccSet_strongLimitTailPackage
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    exists n : Nat, exists G : GeneratorSystem cardinalProductRepresentation
        (cardinalProductRepresentation.pcf
          (natTailIUnionCardSet
            (fun m : Nat => singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)),
      @CardinalProductSuccessorDoublePowerBelowCoordinates.{u}
        (natTailIUnionCardSet
          (fun m : Nat => singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)
        (alephSuccSet_tail_cardinalIndex_small n) /\
      TransitiveGeneratorSystem G /\
      GeneratorAtMostIdealSuccessorDirected G /\
      GeneratorCapturesCanonicalUltrafilters G /\
      GeneratorCompactCover G /\
      exists tailMax : MaxPcfWitness cardinalProductRepresentation
          (natTailIUnionCardSet
            (fun m : Nat => singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n),
        exists coreMax : MaxPcfWitness cardinalProductRepresentation
            alephSuccSet.{u},
          coreMax.theta = tailMax.theta /\
          SuccessorAlephInitialSegmentInCorePcf
            (maxPcfWitnessAlephIndex coreMax) /\
          SuccessorAlephHasMaxPcfBelow
            (maxPcfWitnessAlephIndex coreMax) := by
  classical
  obtain ⟨n, G, hSuccessorDouble, hTransitive, hDirected⟩ :=
    exists_alephSuccSet_tail_pcf_transitiveGenerators_of_strongLimit
      hStrongLimit
  let T : CardSet.{u} :=
    natTailIUnionCardSet
      (fun m : Nat => singletonCardSet
        (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n
  have hRegularsT : SetOfRegulars T :=
    (alephSuccSet_tail_alephOmegaCore n).regulars
  have hCapture : GeneratorCapturesCanonicalUltrafilters G :=
    generatorCapturesCanonicalUltrafilters_of_atMostIdealEscape
      (cardinalProductRepresentation.pcf_is_setOfRegulars T) G
      (generatorAtMostIdealEscapesCanonicalUltrafilters_of_successorDirected
        G hDirected)
  have hCompact : GeneratorCompactCover G :=
    generatorCompactCover_of_canonicalUltrafilterCapture
      (cardinalProductRepresentation.pcf_is_setOfRegulars T)
      (alephSuccSet_tail_pcf_cardinalIndex_small n)
      (fun _ hPcf => alephSuccSet_tail_pcf_mem_gt_aleph0 n hPcf)
      G hCapture
  have hTailSubset : SubsetOf T (cardinalProductRepresentation.pcf T) :=
    cardinalProductRepresentation_subset_pcf hRegularsT
  have hTailNonempty : exists gamma, T gamma := by
    exact ⟨Cardinal.aleph (((n + 1 : Nat) : Ordinal.{u}) + 1),
      ⟨n + 1, Nat.lt_succ_self n, rfl⟩⟩
  have hHasTailMax : HasMaxPcf cardinalProductRepresentation T :=
    cardinalProductRepresentation_hasMaxPcf_of_generatorCompactCover
      (cardinalProductRepresentation.pcf_is_setOfRegulars T)
      G hCompact T hTailSubset hTailNonempty
  let tailMax : MaxPcfWitness cardinalProductRepresentation T :=
    ⟨Classical.choose hHasTailMax, Classical.choose_spec hHasTailMax⟩
  let coreMax : MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u} :=
    ⟨tailMax.theta,
      alephSuccSet_maxPcfWitness_of_tail n tailMax.isMax⟩
  have hCoreInitial : SuccessorAlephInitialSegmentInCorePcf
      (maxPcfWitnessAlephIndex coreMax) :=
    successorAlephInitialSegmentInCorePcf_of_strongLimit_of_maxAlephIndex
      hStrongLimit coreMax
  have hLocalMax : SuccessorAlephHasMaxPcfBelow
      (maxPcfWitnessAlephIndex coreMax) :=
    successorAlephHasMaxPcfBelow_of_tailGeneratorCompactCover
      n G hCompact hCoreInitial
  exact ⟨n, G, hSuccessorDouble, hTransitive, hDirected, hCapture, hCompact,
    tailMax, coreMax, rfl, hCoreInitial, hLocalMax⟩

#print axioms exists_alephSuccSet_strongLimitTailPackage

/-- Localization Lemma 24.32 for the full successor-aleph core is now a
theorem under the strong-limit hypothesis: the required tail generators are
constructed above and finite-prefix transport returns to the full core. -/
theorem alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    CardinalProductPcfLocalizationOutput alephSuccSet.{u} := by
  obtain ⟨n, hSuccessorDouble⟩ :=
    exists_alephSuccSet_tail_successorDoublePowerBelow_of_strongLimit.{u}
      hStrongLimit
  let T : CardSet.{u} :=
    natTailIUnionCardSet
      (fun m : Nat => singletonCardSet
        (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n
  letI : Small.{u} (CardinalIndex T) :=
    alephSuccSet_tail_cardinalIndex_small n
  have hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex T) := by
    rw [alephSuccSet_tail_cardinalIndex_mk_eq_aleph0]
  have hDouble : CardinalProductDoublePowerBelowCoordinates T :=
    cardinalProductDoublePowerBelowCoordinates_of_successor hSuccessorDouble
  obtain ⟨G, hTransitive, hDirected⟩ :=
    exists_pcf_transitive_successorDirected_generators_of_successorDoublePower
      (alephSuccSet_tail_alephOmegaCore n).regulars hInfinite hSuccessorDouble
  have hCapture : GeneratorCapturesCanonicalUltrafilters G :=
    generatorCapturesCanonicalUltrafilters_of_atMostIdealEscape
      (cardinalProductRepresentation.pcf_is_setOfRegulars T) G
      (generatorAtMostIdealEscapesCanonicalUltrafilters_of_successorDirected
        G hDirected)
  exact alephSuccSet_cardinalProductPcfLocalizationOutput_of_tail n
    (alephSuccSet_tail_cardinalProductPcfLocalizationOutput_of_doublePowerBelow
      n hDouble G hTransitive hCapture)

#print axioms
  alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit

/-! The complete PCF argument.  The strong-limit hypothesis constructs one
sufficiently high tail, its transitive successor-directed generators, the
full-core maximum and all local maxima.  The tail form of Corollary 24.30 and
Localization 24.32 then feed the rank-reflection contradiction, while the
characteristic-function bridge compares the continuum with the core
maximum. -/
theorem targetConditionalStatement_of_strongLimit :
    targetConditionalStatement.{u} := by
  intro hStrongLimit
  obtain ⟨n, G, hSuccessorDouble, _hTransitive, hDirected, hCapture,
      hCompact, tailMax, coreMax, hCoreTailEq, hCore, hLocal⟩ :=
    exists_alephSuccSet_strongLimitTailPackage hStrongLimit
  let T : CardSet.{u} :=
    natTailIUnionCardSet
      (fun m : Nat => singletonCardSet
        (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n
  letI : Small.{u} (CardinalIndex T) :=
    alephSuccSet_tail_cardinalIndex_small n
  have hDouble : CardinalProductDoublePowerBelowCoordinates T :=
    cardinalProductDoublePowerBelowCoordinates_of_successor hSuccessorDouble
  have hPcfFixed : cardinalProductRepresentation.pcf
      (cardinalProductRepresentation.pcf T) =
        cardinalProductRepresentation.pcf T :=
    cardinalProductRepresentation_pcf_pcf_eq_of_doublePowerBelow
      T (alephSuccSet_tail_alephOmegaCore n).regulars hDouble
  have h2430 : SuccessorAlephLocalCorollary2430 hLocal :=
    successorAlephLocalCorollary2430_of_tailGenerators
      n G hCapture hPcfFixed hLocal hCore
  have hClub : SuccessorAlephLocalClubMaxPcfBelow
      hLocal targetIndexOmega4 :=
    successorAlephLocalClubMaxPcfBelow_of_corollary2430_of_strongLimit
      hLocal h2430 hStrongLimit
  have hLocalization :
      CardinalProductPcfLocalizationOutput alephSuccSet.{u} :=
    alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit
      hStrongLimit
  have hCoreMaxEq : coreMax.theta = Cardinal.aleph
      (maxPcfWitnessAlephIndex coreMax) :=
    (aleph_maxPcfWitnessAlephIndex_eq coreMax).symm
  have hMlt : coreMax.theta < targetAlephOmega4.{u} :=
    coreMaxPcfWitness_lt_targetAlephOmega4_of_localRankBoundedClubInputs
      hLocal hClub hLocalization hCore coreMax hCoreMaxEq
  have hContinuumLe : ContinuumAtAlephOmega.{u} <= coreMax.theta :=
    continuumAtAlephOmega_le_maxPcf_of_strongLimit_of_lt_alephOmega4
      hStrongLimit coreMax hMlt
  change ContinuumAtAlephOmega.{u} < targetAlephOmega4.{u}
  exact hContinuumLe.trans_lt hMlt

#print axioms targetConditionalStatement_of_strongLimit

/-- Shelah's `aleph_omega` bound in its direct cardinal-arithmetic form. -/
theorem two_power_alephOmega_lt_alephOmega4
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    (2 : Cardinal.{u}) ^ targetAlephOmega < targetAlephOmega4 :=
  targetConditionalStatement_of_strongLimit hStrongLimit

#print axioms two_power_alephOmega_lt_alephOmega4

end PcfProject
