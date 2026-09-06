import PcfProject.ShelahClosure
import Mathlib.Order.Interval.Set.InitialSeg

/-!
# Localized maximum-PCF rank

The source rank argument only evaluates maxima on successor-aleph families
below one fixed ordinal `theta`.  This module constructs that rank directly
from `SuccessorAlephHasMaxPcfBelow theta`, avoiding the stronger global
`SuccessorAlephHasMaxPcf` premise.
-/

namespace PcfProject

universe u

open Cardinal Set
open scoped Cardinal

theorem successorAlephHasMaxPcfBelow_mono
    {kappa theta : Ordinal.{u}}
    (hKappaTheta : kappa <= theta)
    (hMax : SuccessorAlephHasMaxPcfBelow theta) :
    SuccessorAlephHasMaxPcfBelow kappa := by
  intro X hX hXNonempty
  exact hMax X (hX.trans fun _ hx => hx.trans_le hKappaTheta) hXNonempty

#print axioms successorAlephHasMaxPcfBelow_mono

/-! Every displayed PCF maximum has an aleph index because it is regular,
hence at least `aleph0`.  No successor-index claim is used here. -/
noncomputable def maxPcfWitnessAlephIndex
    {A : CardSet.{u}}
    (M : MaxPcfWitness cardinalProductRepresentation A) : Ordinal.{u} :=
  Classical.choose
    (Cardinal.mem_range_aleph_iff.mpr M.isRegular.aleph0_le)

theorem aleph_maxPcfWitnessAlephIndex_eq
    {A : CardSet.{u}}
    (M : MaxPcfWitness cardinalProductRepresentation A) :
    Cardinal.aleph (maxPcfWitnessAlephIndex M) = M.theta :=
  Classical.choose_spec
    (Cardinal.mem_range_aleph_iff.mpr M.isRegular.aleph0_le)


/-! 核心论证只需最大 pcf 见证的阿列夫指标，以及其后的有界局部最大值装置。 -/
def successorAlephBoundedIndexSet
    (theta : Ordinal.{u}) (X : Set (Ordinal.{u})) : Set (Ordinal.{u}) :=
  X ∩ Set.Iio theta

theorem successorAlephBoundedIndexSet_subset
    (theta : Ordinal.{u}) (X : Set (Ordinal.{u})) :
    successorAlephBoundedIndexSet theta X ⊆ Set.Iio theta :=
  fun _ hx => hx.2

theorem successorAlephBoundedIndexSet_mono
    {theta : Ordinal.{u}} {X Y : Set (Ordinal.{u})}
    (hXY : X ⊆ Y) :
    successorAlephBoundedIndexSet theta X ⊆
      successorAlephBoundedIndexSet theta Y :=
  fun _ hx => ⟨hXY hx.1, hx.2⟩

theorem successorAlephBoundedIndexSet_eq_of_subset
    {theta : Ordinal.{u}} {X : Set (Ordinal.{u})}
    (hX : X ⊆ Set.Iio theta) :
    successorAlephBoundedIndexSet theta X = X := by
  ext i
  constructor
  · exact fun hi => hi.1
  · exact fun hi => ⟨hi, hX hi⟩

noncomputable def successorAlephLocalMaxPcfWitness
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (X : Set (Ordinal.{u}))
    (hX : (successorAlephBoundedIndexSet theta X).Nonempty) :
    MaxPcfWitness cardinalProductRepresentation
      (successorAlephCardSet (successorAlephBoundedIndexSet theta X)) :=
  ⟨Classical.choose
      (hMax _ (successorAlephBoundedIndexSet_subset theta X) hX),
    Classical.choose_spec
      (hMax _ (successorAlephBoundedIndexSet_subset theta X) hX)⟩

noncomputable def successorAlephLocalMaxPcfCardinal
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (X : Set (Ordinal.{u})) : Cardinal.{u} := by
  classical
  exact if hX : (successorAlephBoundedIndexSet theta X).Nonempty then
      (successorAlephLocalMaxPcfWitness hMax X hX).theta
    else 0

theorem successorAlephLocalMaxPcfCardinal_eq_of_nonempty
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X : Set (Ordinal.{u})}
    (hX : (successorAlephBoundedIndexSet theta X).Nonempty) :
    successorAlephLocalMaxPcfCardinal hMax X =
      (successorAlephLocalMaxPcfWitness hMax X hX).theta := by
  classical
  simp only [successorAlephLocalMaxPcfCardinal, dif_pos hX]

theorem successorAlephLocalMaxPcfCardinal_mem_pcf
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X : Set (Ordinal.{u})}
    (hX : (successorAlephBoundedIndexSet theta X).Nonempty) :
    cardinalProductRepresentation.pcf
      (successorAlephCardSet (successorAlephBoundedIndexSet theta X))
      (successorAlephLocalMaxPcfCardinal hMax X) := by
  rw [successorAlephLocalMaxPcfCardinal_eq_of_nonempty hMax hX]
  exact (successorAlephLocalMaxPcfWitness hMax X hX).mem_pcf

theorem successorAlephLocalMaxPcfCardinal_mono
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X Y : Set (Ordinal.{u})}
    (hXY : X ⊆ Y) :
    successorAlephLocalMaxPcfCardinal hMax X <=
      successorAlephLocalMaxPcfCardinal hMax Y := by
  by_cases hX : (successorAlephBoundedIndexSet theta X).Nonempty
  · have hY : (successorAlephBoundedIndexSet theta Y).Nonempty :=
      hX.mono (successorAlephBoundedIndexSet_mono hXY)
    rw [successorAlephLocalMaxPcfCardinal_eq_of_nonempty hMax hX,
      successorAlephLocalMaxPcfCardinal_eq_of_nonempty hMax hY]
    exact cardinalProductRepresentation_maxPcfWitness_mono
      (successorAlephLocalMaxPcfWitness hMax X hX)
      (successorAlephLocalMaxPcfWitness hMax Y hY)
      (successorAlephCardSet_mono
        (successorAlephBoundedIndexSet_mono hXY))
      (successorAlephCardSet_regulars _)
  · rw [successorAlephLocalMaxPcfCardinal]
    simp only [dif_neg hX]
    exact bot_le

theorem successorAlephCardinal_le_localMaxPcfCardinal
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X : Set (Ordinal.{u})} {i : Ordinal.{u}}
    (hiX : i ∈ X) (hiTheta : i < theta) :
    Cardinal.aleph (i + 1) <=
      successorAlephLocalMaxPcfCardinal hMax X := by
  have hiBounded : i ∈ successorAlephBoundedIndexSet theta X :=
    ⟨hiX, hiTheta⟩
  have hNonempty :
      (successorAlephBoundedIndexSet theta X).Nonempty :=
    ⟨i, hiBounded⟩
  rw [successorAlephLocalMaxPcfCardinal_eq_of_nonempty hMax hNonempty]
  exact (successorAlephLocalMaxPcfWitness hMax X hNonempty).bounds
    (successorAlephCardSet_mem_pcf hiBounded)

theorem aleph0_le_successorAlephLocalMaxPcfCardinal
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X : Set (Ordinal.{u})}
    (hX : (successorAlephBoundedIndexSet theta X).Nonempty) :
    Cardinal.aleph0 <= successorAlephLocalMaxPcfCardinal hMax X := by
  rw [successorAlephLocalMaxPcfCardinal_eq_of_nonempty hMax hX]
  exact (successorAlephLocalMaxPcfWitness hMax X hX).isRegular.aleph0_le

noncomputable def successorAlephLocalMaxPcfIndex
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (X : Set (Ordinal.{u})) : Ordinal.{u} := by
  classical
  exact if hX : (successorAlephBoundedIndexSet theta X).Nonempty then
      Classical.choose (Cardinal.mem_range_aleph_iff.mpr
        (aleph0_le_successorAlephLocalMaxPcfCardinal hMax hX))
    else 0

theorem aleph_successorAlephLocalMaxPcfIndex_eq
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X : Set (Ordinal.{u})}
    (hX : (successorAlephBoundedIndexSet theta X).Nonempty) :
    Cardinal.aleph (successorAlephLocalMaxPcfIndex hMax X) =
      successorAlephLocalMaxPcfCardinal hMax X := by
  classical
  simp only [successorAlephLocalMaxPcfIndex, dif_pos hX]
  exact Classical.choose_spec (Cardinal.mem_range_aleph_iff.mpr
    (aleph0_le_successorAlephLocalMaxPcfCardinal hMax hX))

theorem successorAlephLocalMaxPcfIndex_mono
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X Y : Set (Ordinal.{u})}
    (hXY : X ⊆ Y) :
    successorAlephLocalMaxPcfIndex hMax X <=
      successorAlephLocalMaxPcfIndex hMax Y := by
  by_cases hX : (successorAlephBoundedIndexSet theta X).Nonempty
  · have hY : (successorAlephBoundedIndexSet theta Y).Nonempty :=
      hX.mono (successorAlephBoundedIndexSet_mono hXY)
    apply Cardinal.aleph_le_aleph.mp
    rw [aleph_successorAlephLocalMaxPcfIndex_eq hMax hX,
      aleph_successorAlephLocalMaxPcfIndex_eq hMax hY]
    exact successorAlephLocalMaxPcfCardinal_mono hMax hXY
  · rw [successorAlephLocalMaxPcfIndex]
    simp only [dif_neg hX]
    exact bot_le

theorem mem_lt_successorAlephLocalMaxPcfIndex
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X : Set (Ordinal.{u})} {i : Ordinal.{u}}
    (hiX : i ∈ X) (hiTheta : i < theta) :
    i < successorAlephLocalMaxPcfIndex hMax X := by
  have hNonempty :
      (successorAlephBoundedIndexSet theta X).Nonempty :=
    ⟨i, hiX, hiTheta⟩
  have hCard : Cardinal.aleph (i + 1) <=
      Cardinal.aleph (successorAlephLocalMaxPcfIndex hMax X) := by
    rw [aleph_successorAlephLocalMaxPcfIndex_eq hMax hNonempty]
    exact successorAlephCardinal_le_localMaxPcfCardinal
      hMax hiX hiTheta
  exact (lt_add_one i).trans_le (Cardinal.aleph_le_aleph.mp hCard)

noncomputable def successorAlephLocalMaxPcfRank
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (X : Set (Ordinal.{u})) : Ordinal.{u} :=
  Ordinal.pred (successorAlephLocalMaxPcfIndex hMax X)

theorem successorAlephLocalMaxPcfRank_mono
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X Y : Set (Ordinal.{u})}
    (hXY : X ⊆ Y) :
    successorAlephLocalMaxPcfRank hMax X <=
      successorAlephLocalMaxPcfRank hMax Y := by
  rw [successorAlephLocalMaxPcfRank, successorAlephLocalMaxPcfRank,
    Ordinal.pred_le_iff_le_succ]
  exact (successorAlephLocalMaxPcfIndex_mono hMax hXY).trans
    (Ordinal.self_le_succ_pred _)

theorem mem_le_successorAlephLocalMaxPcfRank
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    {X : Set (Ordinal.{u})} {i : Ordinal.{u}}
    (hiX : i ∈ X) (hiTheta : i < theta) :
    i <= successorAlephLocalMaxPcfRank hMax X := by
  rw [successorAlephLocalMaxPcfRank]
  have hLt := mem_lt_successorAlephLocalMaxPcfIndex hMax hiX hiTheta
  rcases Order.mem_range_succ_or_isSuccPrelimit
      (successorAlephLocalMaxPcfIndex hMax X) with ⟨j, hj⟩ | hLimit
  · rw [← hj, Ordinal.pred_succ]
    rw [← hj, Order.lt_succ_iff] at hLt
    exact hLt
  · rw [hLimit.ordinalPred_eq]
    exact hLt.le

#print axioms successorAlephLocalMaxPcfCardinal_mono
#print axioms successorAlephLocalMaxPcfIndex_mono
#print axioms successorAlephLocalMaxPcfRank_mono
#print axioms mem_le_successorAlephLocalMaxPcfRank


/-! 后续证明直接使用局部化数据；旧的 club-max 适配层不参与核心定理。 -/
def SuccessorAlephLocalMaxPcfLocalization
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta) : Prop :=
  forall X : Set (Ordinal.{u}), X ⊆ Set.Iio theta -> X.Nonempty ->
    exists W : Set (Ordinal.{u}),
      W ⊆ X /\ W.Countable /\
        cardinalProductRepresentation.pcf
          (successorAlephCardSet W)
          (successorAlephLocalMaxPcfCardinal hMax X)

theorem successorAlephLocalMaxPcfLocalization_of_cardinalProductLocalization_of_corePcf
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hLocalization : CardinalProductPcfLocalizationOutput alephSuccSet.{u})
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    SuccessorAlephLocalMaxPcfLocalization hMax := by
  intro X hXTheta hXNonempty
  have hBoundedEq : successorAlephBoundedIndexSet theta X = X :=
    successorAlephBoundedIndexSet_eq_of_subset hXTheta
  have hBoundedNonempty :
      (successorAlephBoundedIndexSet theta X).Nonempty := by
    simpa only [hBoundedEq] using hXNonempty
  have hMaxMem : cardinalProductRepresentation.pcf
      (successorAlephCardSet X)
      (successorAlephLocalMaxPcfCardinal hMax X) := by
    simpa only [hBoundedEq] using
      (successorAlephLocalMaxPcfCardinal_mem_pcf hMax hBoundedNonempty)
  obtain ⟨B, hBSubset, hBSize, hBLocalized⟩ :=
    hLocalization (successorAlephCardSet X)
      (successorAlephLocalMaxPcfCardinal hMax X)
      (by
        intro cardinal hCardinal
        obtain ⟨i, hiX, rfl⟩ := hCardinal
        exact hCore i (hXTheta hiX))
      hMaxMem
  let W : Set (Ordinal.{u}) :=
    {i | i ∈ X /\ B (Cardinal.aleph (i + 1))}
  have hWX : W ⊆ X := fun _ hi => hi.1
  let encode : W -> CardinalIndex B := fun i =>
    ⟨Cardinal.aleph (i.1 + 1), i.2.2⟩
  have hEncodeInjective : Function.Injective encode := by
    intro i j hij
    apply Subtype.ext
    have hAleph : Cardinal.aleph (i.1 + 1) =
        Cardinal.aleph (j.1 + 1) := congrArg Subtype.val hij
    have hSucc : i.1 + 1 = j.1 + 1 := Cardinal.aleph.injective hAleph
    apply (Ordinal.add_right_cancel (a := i.1) (b := j.1) 1).mp
    simpa only [Nat.cast_one] using hSucc
  have hWCountable : W.Countable := by
    apply Cardinal.mk_le_aleph0_iff.mp
    exact (Cardinal.mk_le_of_injective hEncodeInjective).trans
      (hBSize.trans (by rw [alephSuccSet_cardinalIndex_mk_eq_aleph0]))
  have hB_eq : B = successorAlephCardSet W := by
    funext cardinal
    apply propext
    constructor
    · intro hCardinalB
      obtain ⟨i, hiX, hCardinal⟩ := hBSubset cardinal hCardinalB
      refine ⟨i, ⟨hiX, ?_⟩, hCardinal⟩
      rw [← hCardinal]
      exact hCardinalB
    · rintro ⟨i, ⟨_hiX, hiB⟩, rfl⟩
      exact hiB
  refine ⟨W, hWX, hWCountable, ?_⟩
  rw [← hB_eq]
  exact hBLocalized

#print axioms
  successorAlephLocalMaxPcfLocalization_of_cardinalProductLocalization_of_corePcf

def SuccessorAlephLocalMaxPcfRankCountableLocalizers
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta) : Prop :=
  forall X : Set (Ordinal.{u}), X ⊆ Set.Iio theta ->
    Ordinal.type ((· < ·) : X -> X -> Prop) =
      Ordinal.omega.{u + 1} 1 ->
    exists W : Set (Ordinal.{u}),
      W ⊆ X /\ W.Countable /\
        forall x, x ∈ X ->
          x <= successorAlephLocalMaxPcfRank hMax W

theorem successorAlephLocalMaxPcfRankCountableLocalizers_of_maxPcfLocalization
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hLocalization : SuccessorAlephLocalMaxPcfLocalization hMax) :
    SuccessorAlephLocalMaxPcfRankCountableLocalizers hMax := by
  intro X hXTheta hType
  have hTypePos : 0 < Ordinal.type ((· < ·) : X -> X -> Prop) := by
    rw [hType]
    simpa only [Cardinal.ord_aleph] using
      (Cardinal.isSuccLimit_ord
        (Cardinal.aleph0_le_aleph
          (1 : Ordinal.{u + 1}))).bot_lt
  let x0 : X := Ordinal.enum ((· < ·) : X -> X -> Prop)
    ⟨0, hTypePos⟩
  have hXNonempty : X.Nonempty := ⟨x0.1, x0.2⟩
  obtain ⟨W, hWX, hWCountable, hLocalized⟩ :=
    hLocalization X hXTheta hXNonempty
  have hWTheta : W ⊆ Set.Iio theta := fun _ hw => hXTheta (hWX hw)
  have hWNonempty : W.Nonempty := by
    obtain ⟨_cardinal, hMember⟩ :=
      cardinalProductRepresentation_nonempty_of_mem_pcf hLocalized
    obtain ⟨w, hw, _hEq⟩ := hMember
    exact ⟨w, hw⟩
  have hBoundedX : successorAlephBoundedIndexSet theta X = X :=
    successorAlephBoundedIndexSet_eq_of_subset hXTheta
  have hBoundedW : successorAlephBoundedIndexSet theta W = W :=
    successorAlephBoundedIndexSet_eq_of_subset hWTheta
  have hBoundedXNonempty :
      (successorAlephBoundedIndexSet theta X).Nonempty := by
    simpa only [hBoundedX] using hXNonempty
  have hBoundedWNonempty :
      (successorAlephBoundedIndexSet theta W).Nonempty := by
    simpa only [hBoundedW] using hWNonempty
  have hMaxWX : successorAlephLocalMaxPcfCardinal hMax W <=
      successorAlephLocalMaxPcfCardinal hMax X :=
    successorAlephLocalMaxPcfCardinal_mono hMax hWX
  have hMaxXW : successorAlephLocalMaxPcfCardinal hMax X <=
      successorAlephLocalMaxPcfCardinal hMax W := by
    rw [successorAlephLocalMaxPcfCardinal_eq_of_nonempty
      hMax hBoundedWNonempty]
    apply (successorAlephLocalMaxPcfWitness
      hMax W hBoundedWNonempty).bounds
    simpa only [hBoundedW] using hLocalized
  have hMaxEq : successorAlephLocalMaxPcfCardinal hMax X =
      successorAlephLocalMaxPcfCardinal hMax W :=
    le_antisymm hMaxXW hMaxWX
  have hIndexEq : successorAlephLocalMaxPcfIndex hMax X =
      successorAlephLocalMaxPcfIndex hMax W := by
    apply Cardinal.aleph.injective
    rw [aleph_successorAlephLocalMaxPcfIndex_eq hMax hBoundedXNonempty,
      aleph_successorAlephLocalMaxPcfIndex_eq hMax hBoundedWNonempty]
    exact hMaxEq
  have hRankEq : successorAlephLocalMaxPcfRank hMax X =
      successorAlephLocalMaxPcfRank hMax W := by
    rw [successorAlephLocalMaxPcfRank,
      successorAlephLocalMaxPcfRank, hIndexEq]
  refine ⟨W, hWX, hWCountable, ?_⟩
  intro x hx
  rw [← hRankEq]
  exact mem_le_successorAlephLocalMaxPcfRank hMax hx (hXTheta hx)

def SuccessorAlephLocalMaxPcfRankOmegaOneInitialSegment
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta) : Prop :=
  forall X : Set (Ordinal.{u}), X ⊆ Set.Iio theta ->
    Ordinal.type ((· < ·) : X -> X -> Prop) =
      Ordinal.omega.{u + 1} 1 ->
    exists gamma, gamma ∈ X /\
      forall x, x ∈ X ->
        x <= successorAlephLocalMaxPcfRank hMax
          (X ∩ Set.Iio gamma)

theorem successorAlephLocalMaxPcfRankOmegaOneInitialSegment_of_countableLocalizers
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hLocal : SuccessorAlephLocalMaxPcfRankCountableLocalizers hMax) :
    SuccessorAlephLocalMaxPcfRankOmegaOneInitialSegment hMax := by
  intro X hXTheta hType
  obtain ⟨W, hWX, hWCountable, hWDominates⟩ :=
    hLocal X hXTheta hType
  obtain ⟨gamma, hGammaX, hWGamma⟩ :=
    exists_mem_strict_upperBound_of_countable_subset_of_orderType_omega_one
      hWX hWCountable hType
  refine ⟨gamma, hGammaX, ?_⟩
  have hWInitial : W ⊆ X ∩ Set.Iio gamma := fun w hw =>
    ⟨hWX hw, hWGamma w hw⟩
  intro x hx
  exact (hWDominates x hx).trans
    (successorAlephLocalMaxPcfRank_mono hMax hWInitial)

theorem successorAlephLocalMaxPcfRankOmegaOneInitialSegment_of_cardinalProductLocalization_of_corePcf
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hLocalization : CardinalProductPcfLocalizationOutput alephSuccSet.{u})
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    SuccessorAlephLocalMaxPcfRankOmegaOneInitialSegment hMax :=
  successorAlephLocalMaxPcfRankOmegaOneInitialSegment_of_countableLocalizers
    hMax
    (successorAlephLocalMaxPcfRankCountableLocalizers_of_maxPcfLocalization
      hMax
      (successorAlephLocalMaxPcfLocalization_of_cardinalProductLocalization_of_corePcf
        hMax hLocalization hCore))

#print axioms
  successorAlephLocalMaxPcfRankOmegaOneInitialSegment_of_cardinalProductLocalization_of_corePcf

/-! A reflection pattern with an explicit rank cutoff.  The terminal
contradiction needs only the fixed cutoff `omega_4`, even when the local
maximum operator was defined on a larger ordinal domain. -/
def SuccessorAlephLocalMaxPcfRankReflectionBelowAt
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (bound delta : Ordinal.{u}) : Prop :=
  forall C : Set (Set.Iio delta), IsClub C ->
    exists X : Set (Ordinal.{u}),
      X ⊆ (fun i : Set.Iio delta => i.1) '' C /\
        Ordinal.type ((· < ·) : X -> X -> Prop) =
          Ordinal.omega.{u + 1} 1 /\
        forall gamma, gamma ∈ X ->
          successorAlephLocalMaxPcfRank hMax
              (X ∩ Set.Iio gamma) < bound ->
          successorAlephLocalMaxPcfRank hMax
              (X ∩ Set.Iio gamma) < sSup X


/-! 以下结构把有界反射结论落实为 ω₁ 长的共尾梯系统。 -/
def OmegaOneCofinalLadderAtAlephThree
    (alpha : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)
    (L : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)) : Prop :=
  (forall i, i ∈ L -> i < alpha) /\
  Ordinal.type ((· < ·) : L -> L -> Prop) =
    Ordinal.omega.{u + 1} 1 /\
  sSup ((fun i : Set.Iio
    (Cardinal.aleph (3 : Ordinal.{u})).ord => i.1) '' L) = alpha.1

def alephThreeInitialSegmentEmbedding
    (alpha : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)
    (i : Set.Iio alpha.1) :
    Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord :=
  ⟨i.1, (show i.1 < (Cardinal.aleph (3 : Ordinal.{u})).ord from
    i.2.trans alpha.2)⟩

/-! A source-faithful `omega_1` ladder is not merely cofinal: after pulling
it back below its endpoint it is a club. -/
def OmegaOneClubLadderAtAlephThree
    (alpha : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)
    (L : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)) : Prop :=
  OmegaOneCofinalLadderAtAlephThree alpha L /\
  IsClub {i : Set.Iio alpha.1 |
    alephThreeInitialSegmentEmbedding alpha i ∈ L}

def OmegaOneLadderSystemAtAlephThree
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)) : Prop :=
  forall alpha,
    alpha.1.cof = Cardinal.aleph 1 ->
      OmegaOneCofinalLadderAtAlephThree alpha (guess alpha)

def OmegaOneClubLadderSystemAtAlephThree
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)) : Prop :=
  forall alpha,
    alpha.1.cof = Cardinal.aleph 1 ->
      OmegaOneClubLadderAtAlephThree alpha (guess alpha)

/-! A literal club-guessing sequence on `omega_3`.  Both its closed-ladder
system and its simultaneous guessing clause are constructed below. -/
def OmegaOneClubGuessingAtAlephThree
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)) : Prop :=
  OmegaOneLadderSystemAtAlephThree guess /\
  forall D : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord),
    IsClub D ->
      exists alpha,
        alpha.1.cof = Cardinal.aleph 1 /\
        guess alpha ⊆ D


/-! 核心路线直接构造 club 梯系统，省略只服务于中间适配命题的包装层。 -/
theorem exists_omegaOneClubLadderAtAlephThree
    (alpha : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)
    (hAlphaCof : alpha.1.cof = Cardinal.aleph 1) :
    exists L, OmegaOneClubLadderAtAlephThree alpha L := by
  classical
  let a : Ordinal.{u} := (Cardinal.aleph (1 : Ordinal.{u})).ord
  have hCofOrd : alpha.1.cof.ord = a := by
    exact congrArg Cardinal.ord hAlphaCof
  have hALimit : Order.IsSuccLimit a := by
    exact Cardinal.isSuccLimit_ord
      (Cardinal.aleph0_le_aleph (1 : Ordinal.{u}))
  obtain ⟨f, hFund, hNormal⟩ :=
    exists_normal_isFundamentalSeq hCofOrd hALimit
  let intoOmegaThree : Set.Iio alpha.1 ->
      Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord :=
    alephThreeInitialSegmentEmbedding alpha
  let L : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) :=
    Set.range (intoOmegaThree ∘ f)
  have hIntoStrict : StrictMono intoOmegaThree := by
    intro i j hij
    exact hij
  have hMapStrict : StrictMono (intoOmegaThree ∘ f) :=
    hIntoStrict.comp hFund.strictMono
  have hPullback :
      {i : Set.Iio alpha.1 |
        alephThreeInitialSegmentEmbedding alpha i ∈ L} =
        Set.range f := by
    ext i
    constructor
    · rintro ⟨j, hj⟩
      change intoOmegaThree (f j) = intoOmegaThree i at hj
      exact ⟨j, hIntoStrict.injective hj⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
  have hClubPullback :
      IsClub {i : Set.Iio alpha.1 |
        alephThreeInitialSegmentEmbedding alpha i ∈ L} := by
    rw [hPullback]
    exact isClub_range_of_isNormal_of_isCofinal
      hNormal hFund.isCofinal_range
  have hBelow : forall i, i ∈ L -> i < alpha := by
    rintro i ⟨j, rfl⟩
    exact (f j).2
  have hTypeL : Ordinal.type ((· < ·) : L -> L -> Prop) =
      Ordinal.omega.{u + 1} 1 := by
    let toL : Set.Iio a -> L :=
      fun i => ⟨intoOmegaThree (f i), ⟨i, rfl⟩⟩
    have hToLStrict : StrictMono toL := by
      intro i j hij
      exact hMapStrict hij
    have hToLSurjective : Function.Surjective toL := by
      rintro ⟨x, i, rfl⟩
      exact ⟨i, rfl⟩
    let e : Set.Iio a ≃o L :=
      StrictMono.orderIsoOfSurjective toL hToLStrict hToLSurjective
    rw [← e.toRelIsoLT.ordinal_type_eq, Ordinal.type_lt_Iio]
    simp only [a, Cardinal.ord_aleph, Ordinal.lift_omega,
      Ordinal.lift_one]
  have hUnderlyingImage :
      (fun i : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord => i.1) '' L =
        Set.range (fun i => (f i).1) := by
    ext x
    constructor
    · rintro ⟨_i, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨intoOmegaThree (f j), ⟨j, rfl⟩, rfl⟩
  have hOneLtA : (1 : Ordinal.{u}) < a := by
    change (1 : Ordinal.{u}) < (Cardinal.aleph (1 : Ordinal.{u})).ord
    have hCard : (1 : Cardinal.{u}) <
        Cardinal.aleph (1 : Ordinal.{u}) :=
      Cardinal.one_lt_aleph0.trans_le
        (Cardinal.aleph0_le_aleph (1 : Ordinal.{u}))
    simpa only [Cardinal.ord_one] using Cardinal.ord_lt_ord.mpr hCard
  have hSup :
      sSup ((fun i : Set.Iio
        (Cardinal.aleph (3 : Ordinal.{u})).ord => i.1) '' L) = alpha.1 := by
    rw [hUnderlyingImage]
    change (⨆ i, (f i).1) = alpha.1
    exact hFund.iSup_eq hOneLtA
  exact ⟨L, ⟨⟨hBelow, hTypeL, hSup⟩, hClubPullback⟩⟩

#print axioms exists_omegaOneClubLadderAtAlephThree

theorem exists_omegaOneClubLadderSystemAtAlephThree :
    exists guess : Set.Iio
        (Cardinal.aleph (3 : Ordinal.{u})).ord ->
        Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord),
      OmegaOneClubLadderSystemAtAlephThree guess := by
  classical
  have hExists : forall alpha : Set.Iio
      (Cardinal.aleph (3 : Ordinal.{u})).ord,
      exists L : Set (Set.Iio
        (Cardinal.aleph (3 : Ordinal.{u})).ord),
        alpha.1.cof = Cardinal.aleph 1 ->
          OmegaOneClubLadderAtAlephThree alpha L := by
    intro alpha
    by_cases hAlphaCof : alpha.1.cof = Cardinal.aleph 1
    · obtain ⟨L, hL⟩ :=
        exists_omegaOneClubLadderAtAlephThree alpha hAlphaCof
      exact ⟨L, fun _ => hL⟩
    · exact ⟨∅, fun h => (hAlphaCof h).elim⟩
  choose guess hGuess using hExists
  exact ⟨guess, fun alpha hAlphaCof => hGuess alpha hAlphaCof⟩

#print axioms exists_omegaOneClubLadderSystemAtAlephThree


/-! 从这里开始建立 ω₂ 指标上的稳定化机制，供最终反射论证使用。 -/
def omegaTwoIndexSucc
    (i : Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord) :
    Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord :=
  ⟨Order.succ i.1,
    (Cardinal.isSuccLimit_ord
      (Cardinal.aleph0_le_aleph (2 : Ordinal.{u}))).succ_lt i.2⟩

theorem lt_omegaTwoIndexSucc
    (i : Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord) :
    i < omegaTwoIndexSucc i := by
  exact Order.lt_succ i.1

#print axioms lt_omegaTwoIndexSucc

/-! A decreasing family of subsets of a set smaller than `aleph_2` cannot
strictly decrease at all `aleph_2` successor stages. This is the pigeonhole
step at the end of Shelah's club-guessing proof. -/
theorem antitone_alephTwo_setFamily_stabilizes
    {alpha : Type (u + 1)}
    (A : Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord -> Set alpha)
    (hAnti : Antitone A)
    (hSmall : Cardinal.mk alpha <
      Cardinal.lift.{u + 1} (Cardinal.aleph (2 : Ordinal.{u}))) :
    exists i, A i = A (omegaTwoIndexSucc i) := by
  classical
  by_contra hNo
  have hNe : forall i, A i ≠ A (omegaTwoIndexSucc i) := by
    intro i hi
    exact hNo ⟨i, hi⟩
  have hDiff : forall i,
      (A i \ A (omegaTwoIndexSucc i)).Nonempty := by
    intro i
    have hSuccSubset : A (omegaTwoIndexSucc i) ⊆ A i :=
      hAnti (le_of_lt (lt_omegaTwoIndexSucc i))
    by_contra hEmpty
    have hSubsetSucc : A i ⊆ A (omegaTwoIndexSucc i) := by
      intro x hx
      by_contra hxSucc
      exact hEmpty ⟨x, hx, hxSucc⟩
    exact hNe i (Set.Subset.antisymm hSubsetSucc hSuccSubset)
  choose point hPoint using hDiff
  have hPointLeft (i) : point i ∈ A i := (hPoint i).1
  have hPointRight (i) : point i ∉ A (omegaTwoIndexSucc i) :=
    (hPoint i).2
  have hPointInjective : Function.Injective point := by
    intro i j hij
    by_contra hIndexNe
    rcases lt_or_gt_of_ne hIndexNe with hijIndex | hjiIndex
    · have hSuccLe : omegaTwoIndexSucc i ≤ j := by
        apply Subtype.coe_le_coe.mp
        exact Order.succ_le_iff.mpr hijIndex
      have hjMem : point j ∈ A (omegaTwoIndexSucc i) :=
        hAnti hSuccLe (hPointLeft j)
      exact hPointRight i (hij ▸ hjMem)
    · have hSuccLe : omegaTwoIndexSucc j ≤ i := by
        apply Subtype.coe_le_coe.mp
        exact Order.succ_le_iff.mpr hjiIndex
      have hiMem : point i ∈ A (omegaTwoIndexSucc j) :=
        hAnti hSuccLe (hPointLeft i)
      exact hPointRight j (hij.symm ▸ hiMem)
  have hDomainCard :
      Cardinal.mk (Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord) =
        Cardinal.lift.{u + 1} (Cardinal.aleph (2 : Ordinal.{u})) := by
    rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
  have hLarge : Cardinal.lift.{u + 1}
      (Cardinal.aleph (2 : Ordinal.{u})) ≤ Cardinal.mk alpha := by
    rw [← hDomainCard]
    exact Cardinal.mk_le_of_injective hPointInjective
  exact (not_le_of_gt hSmall) hLarge

#print axioms antitone_alephTwo_setFamily_stabilizes

theorem omegaTwoIndex_card :
    Cardinal.mk
      (Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord) =
        Cardinal.lift.{u + 1} (Cardinal.aleph (2 : Ordinal.{u})) := by
  rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]

#print axioms omegaTwoIndex_card

theorem omegaThreeIndex_card :
    Cardinal.mk
      (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) =
        Cardinal.lift.{u + 1} (Cardinal.aleph (3 : Ordinal.{u})) := by
  rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]

#print axioms omegaThreeIndex_card

theorem targetIndexOmega4_lift_cof_eq :
    (Ordinal.lift.{u + 1} targetIndexOmega4.{u}).cof =
      Cardinal.lift.{u + 1}
        (Cardinal.aleph (4 : Ordinal.{u})) := by
  have hRegular : (Cardinal.aleph (4 : Ordinal.{u})).IsRegular := by
    simpa only [Nat.cast_ofNat, OfNat.ofNat] using
      (Cardinal.isRegular_aleph_add_one (3 : Ordinal.{u}))
  rw [← Ordinal.lift_cof, hRegular.cof_ord]

#print axioms targetIndexOmega4_lift_cof_eq

theorem alephThreeIio_cof_eq :
    Order.cof
      (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) =
        Cardinal.lift.{u + 1} (Cardinal.aleph (3 : Ordinal.{u})) := by
  have hRegular : (Cardinal.aleph (3 : Ordinal.{u})).IsRegular := by
    simpa only [Nat.cast_ofNat, OfNat.ofNat] using
      (Cardinal.isRegular_aleph_add_one (2 : Ordinal.{u}))
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, hRegular.cof_ord]

#print axioms alephThreeIio_cof_eq

theorem alephThreeIio_cof_ne_aleph0 :
    Order.cof
      (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) ≠
        Cardinal.aleph0 := by
  rw [alephThreeIio_cof_eq]
  have hBase : Cardinal.aleph0 <
      Cardinal.aleph (3 : Ordinal.{u}) :=
    Cardinal.aleph0_lt_aleph.mpr (by simp)
  have hLift := Cardinal.lift_lt.mpr hBase
  rw [Cardinal.lift_aleph0] at hLift
  exact ne_of_gt hLift

#print axioms alephThreeIio_cof_ne_aleph0

/-! The exact successor-stage club used by the restriction proof:
`Lim(E ∩ D)` remains club in `omega_3`. -/
theorem strictLimitPoints_inter_isClub_alephThree
    {E D : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)}
    (hE : IsClub E)
    (hD : IsClub D) :
    IsClub (StrictLimitPoints (E ∩ D)) := by
  letI : Nonempty
      (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) :=
    ⟨⟨0, (Cardinal.isRegular_aleph_add_one
      (2 : Ordinal.{u})).ord_pos⟩⟩
  letI : NoMaxOrder
      (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) :=
    (Cardinal.isSuccLimit_ord
      (Cardinal.aleph0_le_aleph (3 : Ordinal.{u}))).isSuccPrelimit.noMaxOrder_Iio
  have hInter : IsClub (E ∩ D) :=
    IsClub.inter alephThreeIio_cof_ne_aleph0 hE hD
  exact strictLimitPoints_isClub alephThreeIio_cof_ne_aleph0
    hInter.isCofinal

#print axioms strictLimitPoints_inter_isClub_alephThree

/-! A club restriction of a fixed ladder system guesses all clubs.  This is
the intermediate conclusion produced by Shelah's recursive proof before the
restricted ladders are extended back to the whole stationary stratum. -/
def OmegaOneClubRestrictionGuessesAtAlephThree
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord))
    (E : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)) : Prop :=
  forall D,
    IsClub D ->
    exists alpha,
      alpha.1.cof = Cardinal.aleph 1 /\
      alpha ∈ StrictLimitPoints E /\
      guess alpha ∩ E ⊆ D

theorem exists_badClub_of_not_omegaOneClubRestrictionGuesses
    {guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)}
    {E : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)}
    (hNot : ¬ OmegaOneClubRestrictionGuessesAtAlephThree guess E) :
    exists D,
      IsClub D /\
      forall alpha,
        alpha.1.cof = Cardinal.aleph 1 ->
        alpha ∈ StrictLimitPoints E ->
        ¬ (guess alpha ∩ E ⊆ D) := by
  classical
  by_contra hNoBad
  apply hNot
  intro D hD
  by_contra hNoAlpha
  apply hNoBad
  refine ⟨D, hD, ?_⟩
  intro alpha hAlphaCof hAlphaLimit hSubset
  exact hNoAlpha ⟨alpha, hAlphaCof, hAlphaLimit, hSubset⟩

#print axioms exists_badClub_of_not_omegaOneClubRestrictionGuesses

theorem exists_strictClubRefinement_of_not_restrictionGuesses
    {guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)}
    {E : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)}
    (hE : IsClub E)
    (hNot : ¬ OmegaOneClubRestrictionGuessesAtAlephThree guess E) :
    exists E',
      IsClub E' /\
      E' ⊆ E /\
      forall alpha,
        alpha.1.cof = Cardinal.aleph 1 ->
        alpha ∈ E' ->
        ¬ (guess alpha ∩ E ⊆ E') := by
  obtain ⟨D, hD, hBad⟩ :=
    exists_badClub_of_not_omegaOneClubRestrictionGuesses hNot
  let E' : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) :=
    StrictLimitPoints (E ∩ D)
  have hE'Club : IsClub E' :=
    strictLimitPoints_inter_isClub_alephThree hE hD
  have hE'SubsetInter : E' ⊆ E ∩ D :=
    strictLimitPoints_subset_of_dirSupClosed
      (IsClub.inter alephThreeIio_cof_ne_aleph0 hE hD).dirSupClosed
  refine ⟨E', hE'Club, fun x hx => (hE'SubsetInter hx).1, ?_⟩
  intro alpha hAlphaCof hAlphaE'
  have hAlphaLimitE : alpha ∈ StrictLimitPoints E :=
    strictLimitPoints_mono Set.inter_subset_left hAlphaE'
  have hNotSubsetD := hBad alpha hAlphaCof hAlphaLimitE
  intro hSubsetE'
  apply hNotSubsetD
  exact hSubsetE'.trans (fun x hx => (hE'SubsetInter hx).2)

#print axioms exists_strictClubRefinement_of_not_restrictionGuesses

/-! The recursive configuration forced by failure of every club restriction
in Shelah's proof. Each successor stage remains club and strictly removes a
point from the current ladder section. -/
def OmegaOneClubRestrictionRefinementSequence
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord))
    (E : Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)) : Prop :=
  (forall i, IsClub (E i)) /\
  Antitone E /\
  forall i alpha,
    alpha.1.cof = Cardinal.aleph 1 ->
    alpha ∈ E (omegaTwoIndexSucc i) ->
    ¬ (guess alpha ∩ E i ⊆ E (omegaTwoIndexSucc i))

/-! The terminal contradiction in the club-restriction proof. It combines
the small intersection of `aleph_2` clubs, stationarity of
`E^{aleph_3}_{aleph_1}`, and stabilization of decreasing subsets of one
`aleph_1` ladder. -/
theorem not_exists_omegaOneClubRestrictionRefinementSequence
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord))
    (hLadder : OmegaOneLadderSystemAtAlephThree guess) :
    ¬ exists E, OmegaOneClubRestrictionRefinementSequence guess E := by
  classical
  rintro ⟨E, hEClub, hEAnti, hStrict⟩
  have hIndexSmall :
      Cardinal.mk
          (Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord) <
        Order.cof
          (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) := by
    calc
      _ = Cardinal.lift.{u + 1}
          (Cardinal.aleph (2 : Ordinal.{u})) := omegaTwoIndex_card
      _ < Cardinal.lift.{u + 1}
          (Cardinal.aleph (3 : Ordinal.{u})) :=
        Cardinal.lift_lt.mpr (Cardinal.aleph_lt_aleph.mpr (by
          exact_mod_cast (show (2 : Nat) < 3 by decide)))
      _ = _ := alephThreeIio_cof_eq.symm
  have hIndexSmallLift :
      Cardinal.lift.{u + 1}
          (Cardinal.mk
            (Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord)) <
        Cardinal.lift.{u + 1}
          (Order.cof
            (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)) :=
    Cardinal.lift_lt.mpr hIndexSmall
  have hFinalClub : IsClub (Set.iInter E) :=
    IsClub.iInter alephThreeIio_cof_ne_aleph0 hIndexSmallLift hEClub
  obtain ⟨alpha, hAlphaCof, hAlphaFinal⟩ :=
    stationary_ordinalCof_eq_alephOne_below_alephThree
      (Set.iInter E) hFinalClub
  let A : Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord ->
      Set (guess alpha) :=
    fun i => {x | x.1 ∈ E i}
  have hAAnti : Antitone A := by
    intro i j hij x hx
    exact hEAnti hij hx
  have hGuessCard : Cardinal.mk (guess alpha) =
      Cardinal.aleph (1 : Ordinal.{u + 1}) := by
    rw [← Ordinal.card_type ((· < ·) : guess alpha -> guess alpha -> Prop),
      (hLadder alpha hAlphaCof).2.1, Ordinal.card_omega]
  have hGuessSmall : Cardinal.mk (guess alpha) <
      Cardinal.lift.{u + 1} (Cardinal.aleph (2 : Ordinal.{u})) := by
    rw [hGuessCard, Cardinal.lift_aleph, Ordinal.lift_ofNat]
    exact Cardinal.aleph_lt_aleph.mpr (by simp)
  obtain ⟨i, hStable⟩ :=
    antitone_alephTwo_setFamily_stabilizes A hAAnti hGuessSmall
  have hAlphaNext : alpha ∈ E (omegaTwoIndexSucc i) :=
    Set.mem_iInter.mp hAlphaFinal (omegaTwoIndexSucc i)
  apply hStrict i alpha hAlphaCof hAlphaNext
  intro x hx
  let xGuess : guess alpha := ⟨x, hx.1⟩
  have hxA : xGuess ∈ A i := hx.2
  have hxNextA : xGuess ∈ A (omegaTwoIndexSucc i) := by
    rw [← hStable]
    exact hxA
  exact hxNextA

#print axioms not_exists_omegaOneClubRestrictionRefinementSequence

/-! The missing transfinite-recursion half of the club-restriction proof.
If every club restriction fails, well-founded recursion through `aleph_2`
intersects all earlier clubs and then chooses a strict club refinement. -/
theorem exists_omegaOneClubRestrictionRefinementSequence_of_forall_not
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord))
    (hFail : forall E,
      IsClub E ->
      ¬ OmegaOneClubRestrictionGuessesAtAlephThree guess E) :
    exists E, OmegaOneClubRestrictionRefinementSequence guess E := by
  classical
  let omegaTwo :=
    Set.Iio (Cardinal.aleph (2 : Ordinal.{u})).ord
  let omegaThree :=
    Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord
  let ClubThree := {E : Set omegaThree // IsClub E}
  have hOmegaTwoOrderType :
      (Cardinal.mk omegaTwo).ord =
        Ordinal.type ((· < ·) : omegaTwo -> omegaTwo -> Prop) := by
    rw [omegaTwoIndex_card]
    exact (Cardinal.lift_ord
      (Cardinal.aleph (2 : Ordinal.{u}))).symm.trans
        (Ordinal.type_lt_Iio
          (Cardinal.aleph (2 : Ordinal.{u})).ord).symm
  have hChoose : forall (i : omegaTwo)
      (previous : forall j, j < i -> ClubThree),
      exists next : ClubThree,
        next.1 ⊆ Set.iInter (fun j : Set.Iio i =>
          (previous j.1 j.2).1) /\
        forall alpha,
          alpha.1.cof = Cardinal.aleph 1 ->
          alpha ∈ next.1 ->
          ¬ (guess alpha ∩
              Set.iInter (fun j : Set.Iio i =>
                (previous j.1 j.2).1) ⊆ next.1) := by
    intro i previous
    let base : Set omegaThree :=
      Set.iInter (fun j : Set.Iio i => (previous j.1 j.2).1)
    have hPreSmall : Cardinal.mk (Set.Iio i) < Order.cof omegaThree := by
      calc
        Cardinal.mk (Set.Iio i) < Cardinal.mk omegaTwo :=
          Cardinal.mk_Iio_lt i hOmegaTwoOrderType
        _ = Cardinal.lift.{u + 1}
            (Cardinal.aleph (2 : Ordinal.{u})) := omegaTwoIndex_card
        _ < Cardinal.lift.{u + 1}
            (Cardinal.aleph (3 : Ordinal.{u})) :=
          Cardinal.lift_lt.mpr (Cardinal.aleph_lt_aleph.mpr (by
            exact_mod_cast (show (2 : Nat) < 3 by decide)))
        _ = Order.cof omegaThree := alephThreeIio_cof_eq.symm
    have hPreSmallLift :
        Cardinal.lift.{u + 1} (Cardinal.mk (Set.Iio i)) <
          Cardinal.lift.{u + 1} (Order.cof omegaThree) :=
      Cardinal.lift_lt.mpr hPreSmall
    have hBaseClub : IsClub base := by
      exact IsClub.iInter alephThreeIio_cof_ne_aleph0 hPreSmallLift
        (fun j => (previous j.1 j.2).2)
    obtain ⟨next, hNextClub, hNextSubset, hNextStrict⟩ :=
      exists_strictClubRefinement_of_not_restrictionGuesses
        hBaseClub (hFail base hBaseClub)
    exact ⟨⟨next, hNextClub⟩, hNextSubset, hNextStrict⟩
  let clubSeq : omegaTwo -> ClubThree :=
    WellFounded.fix wellFounded_lt
      (fun i previous => Classical.choose (hChoose i previous))
  have hClubSeqEq : forall i,
      clubSeq i = Classical.choose
        (hChoose i (fun j hj => clubSeq j)) := by
    intro i
    exact WellFounded.fix_eq _ _ i
  let E : omegaTwo -> Set omegaThree := fun i => (clubSeq i).1
  have hEClub : forall i, IsClub (E i) := fun i => (clubSeq i).2
  have hEAnti : Antitone E := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact fun _ hx => hx
    · change (clubSeq j).1 ⊆ (clubSeq i).1
      rw [hClubSeqEq j]
      have hSpec := Classical.choose_spec
        (hChoose j (fun k hk => clubSeq k))
      exact hSpec.1.trans
        (Set.iInter_subset _ (show Set.Iio j from ⟨i, hij⟩))
  have hEStrict : forall i alpha,
      alpha.1.cof = Cardinal.aleph 1 ->
      alpha ∈ E (omegaTwoIndexSucc i) ->
      ¬ (guess alpha ∩ E i ⊆ E (omegaTwoIndexSucc i)) := by
    intro i alpha hAlphaCof hAlphaNext hSubset
    simp only [E] at hAlphaNext hSubset ⊢
    rw [hClubSeqEq (omegaTwoIndexSucc i)] at hAlphaNext hSubset
    have hSpec := Classical.choose_spec
      (hChoose (omegaTwoIndexSucc i)
        (fun k hk => clubSeq k))
    apply hSpec.2 alpha hAlphaCof hAlphaNext
    intro x hx
    apply hSubset
    exact ⟨hx.1,
      Set.mem_iInter.mp hx.2
        ⟨i, lt_omegaTwoIndexSucc i⟩⟩
  exact ⟨E, hEClub, hEAnti, hEStrict⟩

#print axioms
  exists_omegaOneClubRestrictionRefinementSequence_of_forall_not

theorem exists_club_omegaOneClubRestrictionGuessesAtAlephThree
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord))
    (hLadder : OmegaOneLadderSystemAtAlephThree guess) :
    exists E,
      IsClub E /\
      OmegaOneClubRestrictionGuessesAtAlephThree guess E := by
  classical
  by_contra hNo
  have hFail : forall E,
      IsClub E ->
      ¬ OmegaOneClubRestrictionGuessesAtAlephThree guess E := by
    intro E hE hGuess
    exact hNo ⟨E, hE, hGuess⟩
  exact not_exists_omegaOneClubRestrictionRefinementSequence guess hLadder
    (exists_omegaOneClubRestrictionRefinementSequence_of_forall_not
      guess hFail)

#print axioms
  exists_club_omegaOneClubRestrictionGuessesAtAlephThree

theorem alephThreeClub_pullback_isClub_of_strictLimitPoint
    {E : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)}
    (hE : IsClub E)
    {alpha : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord}
    (hAlphaLimit : alpha ∈ StrictLimitPoints E) :
    IsClub {i : Set.Iio alpha.1 |
      alephThreeInitialSegmentEmbedding alpha i ∈ E} := by
  let embed := alephThreeInitialSegmentEmbedding alpha
  have hEmbedStrict : StrictMono embed := by
    intro i j hij
    exact hij
  refine ⟨?_, ?_⟩
  · intro s hs hsNonempty hsDirected b hb
    let imageS : Set (Set.Iio
        (Cardinal.aleph (3 : Ordinal.{u})).ord) := embed '' s
    have hImageSubset : imageS ⊆ E := by
      rintro _ ⟨i, hi, rfl⟩
      exact hs hi
    have hImageNonempty : imageS.Nonempty := hsNonempty.image embed
    have hImageDirected : DirectedOn (· <= ·) imageS := by
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      obtain ⟨k, hk, hik, hjk⟩ := hsDirected i hi j hj
      exact ⟨embed k, ⟨k, hk, rfl⟩,
        hEmbedStrict.monotone hik, hEmbedStrict.monotone hjk⟩
    have hImageLUB : IsLUB imageS (embed b) := by
      constructor
      · rintro _ ⟨i, hi, rfl⟩
        exact hEmbedStrict.monotone (hb.1 hi)
      · intro y hy
        apply Subtype.coe_le_coe.mp
        change b.1 <= y.1
        by_cases hAlphaY : alpha <= y
        · exact b.2.le.trans hAlphaY
        · have hYAlpha : y < alpha := lt_of_not_ge hAlphaY
          let yLocal : Set.Iio alpha.1 := ⟨y.1, hYAlpha⟩
          have hBYLocal : b <= yLocal := by
            apply hb.2
            intro i hi
            apply Subtype.coe_le_coe.mp
            exact hy ⟨i, hi, rfl⟩
          exact hBYLocal
    exact hE.dirSupClosed hImageSubset hImageNonempty
      hImageDirected hImageLUB
  · intro beta
    obtain ⟨y, hyE, hBetaY, hYAlpha⟩ :=
      hAlphaLimit.2 (alephThreeInitialSegmentEmbedding alpha beta) beta.2
    let yLocal : Set.Iio alpha.1 := ⟨y.1, hYAlpha⟩
    exact ⟨yLocal, hyE, hBetaY.le⟩

#print axioms alephThreeClub_pullback_isClub_of_strictLimitPoint

theorem omegaOneClubLadder_inter_of_mem_strictLimitPoints
    {alpha : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord}
    {L E : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)}
    (hAlphaCof : alpha.1.cof = Cardinal.aleph 1)
    (hL : OmegaOneClubLadderAtAlephThree alpha L)
    (hE : IsClub E)
    (hAlphaLimit : alpha ∈ StrictLimitPoints E) :
    OmegaOneClubLadderAtAlephThree alpha (L ∩ E) := by
  classical
  let embed := alephThreeInitialSegmentEmbedding alpha
  let LBelow : Set (Set.Iio alpha.1) := {i | embed i ∈ L}
  let EBelow : Set (Set.Iio alpha.1) := {i | embed i ∈ E}
  let MBelow : Set (Set.Iio alpha.1) := LBelow ∩ EBelow
  let M : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) := L ∩ E
  have hCofAlpha : Order.cof (Set.Iio alpha.1) =
      Cardinal.lift.{u + 1} (Cardinal.aleph (1 : Ordinal.{u})) := by
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, hAlphaCof]
  have hCofAlphaNe : Order.cof (Set.Iio alpha.1) ≠ Cardinal.aleph0 := by
    rw [hCofAlpha]
    have hlt : Cardinal.lift.{u + 1} Cardinal.aleph0 <
        Cardinal.lift.{u + 1}
          (Cardinal.aleph (1 : Ordinal.{u})) :=
      Cardinal.lift_lt.mpr (Cardinal.aleph0_lt_aleph.mpr (by simp))
    rw [Cardinal.lift_aleph0] at hlt
    exact ne_of_gt hlt
  have hEBelowClub : IsClub EBelow := by
    exact alephThreeClub_pullback_isClub_of_strictLimitPoint
      hE hAlphaLimit
  have hMBelowClub : IsClub MBelow := by
    exact IsClub.inter hCofAlphaNe hL.2 hEBelowClub
  have hTypeLBelow :
      Ordinal.type ((· < ·) : LBelow -> LBelow -> Prop) =
        Ordinal.omega.{u + 1} 1 := by
    let toL : LBelow -> L := fun i => ⟨embed i.1, i.2⟩
    have hToLStrict : StrictMono toL := by
      intro i j hij
      exact hij
    have hToLSurjective : Function.Surjective toL := by
      rintro ⟨i, hiL⟩
      let iLocal : Set.Iio alpha.1 := ⟨i.1, hL.1.1 i hiL⟩
      let iBelow : LBelow := ⟨iLocal, hiL⟩
      exact ⟨iBelow, Subtype.ext rfl⟩
    let e : LBelow ≃o L :=
      StrictMono.orderIsoOfSurjective toL hToLStrict hToLSurjective
    exact e.toRelIsoLT.ordinal_type_eq.trans hL.1.2.1
  have hTypeUpper :
      Ordinal.type ((· < ·) : MBelow -> MBelow -> Prop) <=
        Ordinal.omega.{u + 1} 1 := by
    exact (Ordinal.type_mono Set.inter_subset_left).trans_eq hTypeLBelow
  let inclusion : MBelow -> Set.Iio alpha.1 := fun i => i.1
  have hInclusionStrict : StrictMono inclusion := by
    intro i j hij
    exact hij
  have hInclusionCofinal : IsCofinal (Set.range inclusion) := by
    simpa only [inclusion, Subtype.range_coe_subtype] using
      hMBelowClub.isCofinal
  have hCofMBelow : Order.cof MBelow =
      Cardinal.lift.{u + 1} (Cardinal.aleph (1 : Ordinal.{u})) := by
    rw [Order.cof_congr_of_strictMono hInclusionStrict hInclusionCofinal,
      hCofAlpha]
  have hTypeLower : Ordinal.omega.{u + 1} 1 <=
      Ordinal.type ((· < ·) : MBelow -> MBelow -> Prop) := by
    have hOrdCofLe : (Order.cof MBelow).ord <=
        Ordinal.type ((· < ·) : MBelow -> MBelow -> Prop) := by
      rw [← Ordinal.cof_type]
      exact Ordinal.ord_cof_le _
    rw [hCofMBelow, ← Cardinal.lift_ord, Cardinal.ord_aleph,
      Ordinal.lift_omega, Ordinal.lift_one] at hOrdCofLe
    exact hOrdCofLe
  have hTypeMBelow :
      Ordinal.type ((· < ·) : MBelow -> MBelow -> Prop) =
        Ordinal.omega.{u + 1} 1 :=
    le_antisymm hTypeUpper hTypeLower
  have hBelow : forall i, i ∈ M -> i < alpha := by
    intro i hi
    exact hL.1.1 i hi.1
  have hPullbackEq :
      {i : Set.Iio alpha.1 | embed i ∈ M} = MBelow := by
    rfl
  have hTypeM :
      Ordinal.type ((· < ·) : M -> M -> Prop) =
        Ordinal.omega.{u + 1} 1 := by
    let toM : MBelow -> M :=
      fun i => ⟨embed i.1, i.2⟩
    have hToMStrict : StrictMono toM := by
      intro i j hij
      exact hij
    have hToMSurjective : Function.Surjective toM := by
      rintro ⟨i, hiM⟩
      let iLocal : Set.Iio alpha.1 := ⟨i.1, hBelow i hiM⟩
      let iBelow : MBelow := ⟨iLocal, hiM⟩
      exact ⟨iBelow, Subtype.ext rfl⟩
    let e : MBelow ≃o M :=
      StrictMono.orderIsoOfSurjective toM hToMStrict hToMSurjective
    exact e.toRelIsoLT.ordinal_type_eq.symm.trans hTypeMBelow
  let underlying : Set (Ordinal.{u}) :=
    (fun i : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord => i.1) ''
      M
  have hUnderlyingNonempty : underlying.Nonempty := by
    obtain ⟨betaAmbient, hBetaAlpha⟩ := hAlphaLimit.1
    let betaLocal : Set.Iio alpha.1 := ⟨betaAmbient.1, hBetaAlpha⟩
    obtain ⟨y, hyM, _⟩ := hMBelowClub.isCofinal betaLocal
    exact ⟨y.1, ⟨embed y, hyM, rfl⟩⟩
  have hUnderlyingBdd : BddAbove underlying := by
    refine ⟨alpha.1, ?_⟩
    rintro _ ⟨i, hiM, rfl⟩
    exact (hBelow i hiM).le
  have hSupLe : sSup underlying <= alpha.1 :=
    csSup_le hUnderlyingNonempty (fun x hx => by
      obtain ⟨i, hiM, rfl⟩ := hx
      exact (hBelow i hiM).le)
  have hAlphaLe : alpha.1 <= sSup underlying := by
    apply le_of_forall_lt
    intro beta hBetaAlpha
    let betaAmbient : Set.Iio
        (Cardinal.aleph (3 : Ordinal.{u})).ord :=
      ⟨beta, hBetaAlpha.trans alpha.2⟩
    obtain ⟨z, _hzE, hBetaZ, hZAlpha⟩ :=
      hAlphaLimit.2 betaAmbient hBetaAlpha
    let zLocal : Set.Iio alpha.1 := ⟨z.1, hZAlpha⟩
    obtain ⟨y, hyM, hZY⟩ := hMBelowClub.isCofinal zLocal
    have hyUnderlying : (embed y).1 ∈ underlying :=
      ⟨embed y, hyM, rfl⟩
    have hBetaZVal : beta < z.1 := hBetaZ
    have hZYVal : z.1 <= y.1 := hZY
    exact hBetaZVal.trans_le
      (hZYVal.trans (le_csSup hUnderlyingBdd hyUnderlying))
  refine ⟨⟨hBelow, hTypeM, ?_⟩, ?_⟩
  · exact le_antisymm hSupLe hAlphaLe
  · rw [hPullbackEq]
    exact hMBelowClub

#print axioms omegaOneClubLadder_inter_of_mem_strictLimitPoints

/-! Restrict a closed ladder system to the club supplied by the recursive
argument.  At limit points of that club the restriction is still an
`omega_1`-ladder, while the restriction theorem supplies the guessing
property. -/
theorem exists_omegaOneClubGuessingAtAlephThree :
    exists guess : Set.Iio
        (Cardinal.aleph (3 : Ordinal.{u})).ord ->
        Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord),
      OmegaOneClubGuessingAtAlephThree guess := by
  classical
  obtain ⟨guess, hGuessClub⟩ :=
    exists_omegaOneClubLadderSystemAtAlephThree
  have hGuessLadder : OmegaOneLadderSystemAtAlephThree guess := by
    intro alpha hAlphaCof
    exact (hGuessClub alpha hAlphaCof).1
  obtain ⟨E, hE, hRestrict⟩ :=
    exists_club_omegaOneClubRestrictionGuessesAtAlephThree
      guess hGuessLadder
  let refined := fun alpha =>
    if alpha.1.cof = Cardinal.aleph 1 /\
        alpha ∈ StrictLimitPoints E then
      guess alpha ∩ E
    else
      guess alpha
  refine ⟨refined, ?_, ?_⟩
  · intro alpha hAlphaCof
    by_cases hAlphaLimit : alpha ∈ StrictLimitPoints E
    · have hClosed :=
        omegaOneClubLadder_inter_of_mem_strictLimitPoints
          hAlphaCof (hGuessClub alpha hAlphaCof) hE hAlphaLimit
      simpa [refined, hAlphaCof, hAlphaLimit] using hClosed.1
    · simpa [refined, hAlphaCof, hAlphaLimit] using
        hGuessLadder alpha hAlphaCof
  · intro D hD
    obtain ⟨alpha, hAlphaCof, hAlphaLimit, hSubset⟩ :=
      hRestrict D hD
    refine ⟨alpha, hAlphaCof, ?_⟩
    simpa [refined, hAlphaCof, hAlphaLimit] using hSubset

#print axioms exists_omegaOneClubGuessingAtAlephThree

noncomputable def omegaOneClubGuessingSystemAtAlephThree :
    Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) :=
  Classical.choose exists_omegaOneClubGuessingAtAlephThree

theorem omegaOneClubGuessingSystemAtAlephThree_spec :
    OmegaOneClubGuessingAtAlephThree
      omegaOneClubGuessingSystemAtAlephThree :=
  Classical.choose_spec exists_omegaOneClubGuessingAtAlephThree

#print axioms omegaOneClubGuessingSystemAtAlephThree_spec

/-! The purely ordinal part of the later closed trace.  A club trace is a
continuous cofinal embedding of `omega_3`: normality is exposed through
strict monotonicity and preservation of clubs by inverse image. -/

/-! 正规像上确界引理足以支撑后续有界秩闭包。 -/

theorem normal_map_omegaOneCofinalLadder_sSup
    {delta : Ordinal.{u}}
    {eta : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set.Iio delta}
    (hEta : Order.IsNormal eta)
    {alpha : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord}
    {L : Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord)}
    (hL : OmegaOneCofinalLadderAtAlephThree alpha L) :
    sSup ((fun i : Set.Iio
        (Cardinal.aleph (3 : Ordinal.{u})).ord => (eta i).1) '' L) =
      (eta alpha).1 := by
  have hTypePos : 0 < Ordinal.type ((· < ·) : L -> L -> Prop) := by
    rw [hL.2.1]
    simpa only [Cardinal.ord_aleph] using
      (Cardinal.isSuccLimit_ord
        (Cardinal.aleph0_le_aleph (1 : Ordinal.{u + 1}))).bot_lt
  haveI : Nonempty L :=
    Ordinal.type_ne_zero_iff_nonempty.mp hTypePos.ne'
  let l0 : L := Classical.choice inferInstance
  have hLNonempty : L.Nonempty := ⟨l0.1, l0.2⟩
  have hLUB : IsLUB L alpha := by
    constructor
    · intro i hi
      exact (hL.1 i hi).le
    · intro b hb
      change alpha.1 ≤ b.1
      rw [← hL.2.2]
      apply csSup_le (hLNonempty.image fun i => i.1)
      rintro _ ⟨i, hi, rfl⟩
      exact hb hi
  have hValueNormal : Order.IsNormal
      (fun i : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord =>
        (eta i).1) := by
    simpa only [Function.comp_apply, Set.principalSegIio_apply] using
      (Set.principalSegIio delta).isNormal.comp hEta
  exact (hValueNormal.map_isLUB hLUB hLNonempty).csSup_eq
    (hLNonempty.image fun i => (eta i).1)

#print axioms normal_map_omegaOneCofinalLadder_sSup

/-! The continuous-chain content used after a club-guessing sequence has
been fixed.  Pullback of clubs records continuity/cofinality of the trace;
the first two fields now have the unconditional constructor above.  The last
clause is precisely the elementary-chain rank closure for the countable
guessed initial segments. -/

/-! 核心仅使用有界的秩闭包结构。 -/

def SuccessorAlephLocalMaxPcfRankOmegaThreeRankClosureBelowAt
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (bound : Ordinal.{u})
    {delta : Ordinal.{u}}
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord))
    (eta : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set.Iio delta)
    (alpha : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) : Prop :=
  forall i, i ∈ guess alpha ->
    (((fun j : Set.Iio
        (Cardinal.aleph (3 : Ordinal.{u})).ord => (eta j).1) ''
          guess alpha) ∩ Set.Iio (eta i).1).Countable ->
    successorAlephLocalMaxPcfRank hMax
        (((fun j : Set.Iio
          (Cardinal.aleph (3 : Ordinal.{u})).ord => (eta j).1) ''
            guess alpha) ∩ Set.Iio (eta i).1) < bound ->
    successorAlephLocalMaxPcfRank hMax
        (((fun j : Set.Iio
          (Cardinal.aleph (3 : Ordinal.{u})).ord => (eta j).1) ''
            guess alpha) ∩ Set.Iio (eta i).1) < (eta alpha).1

def SuccessorAlephLocalMaxPcfRankOmegaThreeClubRankClosureBelow
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (bound : Ordinal.{u})
    {delta : Ordinal.{u}}
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord))
    (eta : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set.Iio delta) : Prop :=
  IsClub {alpha |
    alpha.1.cof = Cardinal.aleph 1 ->
      SuccessorAlephLocalMaxPcfRankOmegaThreeRankClosureBelowAt
        hMax bound guess eta alpha}


/-! 后续反射证明只需后继索引及有界正规闭包定理。 -/

def omegaThreeIndexSucc
    (i : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) :
    Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord :=
  ⟨i.1 + 1,
    (Cardinal.isSuccLimit_ord
      (Cardinal.aleph0_le_aleph (3 : Ordinal.{u}))).succ_lt i.2⟩

theorem lt_omegaThreeIndexSucc
    (i : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) :
    i < omegaThreeIndexSucc i := by
  exact Order.lt_succ i.1


/-! 核心直接使用有界的正规闭包反射定理；省去不被调用的初始迹与无界版本。 -/

theorem successorAlephLocalMaxPcfRankReflectionBelowAt_of_normal_of_clubRankClosureBelow
    {theta bound delta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord))
    (eta : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord ->
      Set.Iio delta)
    (hDeltaCof : delta.cof = Cardinal.aleph 3)
    (hGuess : OmegaOneClubGuessingAtAlephThree guess)
    (hFundamental : Ordinal.IsFundamentalSeq eta)
    (hNormal : Order.IsNormal eta)
    (hRankClub :
      SuccessorAlephLocalMaxPcfRankOmegaThreeClubRankClosureBelow
        hMax bound guess eta) :
    SuccessorAlephLocalMaxPcfRankReflectionBelowAt
      hMax bound delta := by
  intro C hC
  obtain ⟨hGuessShape, hGuesses⟩ := hGuess
  have hCofIio : Order.cof (Set.Iio delta) =
      Cardinal.lift.{u + 1} (Cardinal.aleph (3 : Ordinal.{u})) := by
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, hDeltaCof]
  have hCofIioNe : Order.cof (Set.Iio delta) ≠ Cardinal.aleph0 := by
    rw [hCofIio]
    have hlt : Cardinal.lift.{u + 1} Cardinal.aleph0 <
        Cardinal.lift.{u + 1}
          (Cardinal.aleph (3 : Ordinal.{u})) :=
      Cardinal.lift_lt.mpr
        (Cardinal.aleph0_lt_aleph.mpr (by simp))
    rw [Cardinal.lift_aleph0] at hlt
    exact ne_of_gt hlt
  have hPullback : IsClub (eta ⁻¹' C) :=
    isClub_preimage_of_isNormal_of_isCofinal
      hNormal hFundamental.isCofinal_range hCofIioNe hC
  have hSelectClub : IsClub ((eta ⁻¹' C) ∩
      {alpha |
        alpha.1.cof = Cardinal.aleph 1 ->
          SuccessorAlephLocalMaxPcfRankOmegaThreeRankClosureBelowAt
            hMax bound guess eta alpha}) :=
    IsClub.inter alephThreeIio_cof_ne_aleph0 hPullback hRankClub
  obtain ⟨alpha, hAlphaCof, hGuessSubset⟩ :=
    hGuesses _ hSelectClub
  have hLadder := hGuessShape alpha hAlphaCof
  have hTypePos : 0 <
      Ordinal.type ((· < ·) : guess alpha -> guess alpha -> Prop) := by
    rw [hLadder.2.1]
    simpa only [Cardinal.ord_aleph] using
      (Cardinal.isSuccLimit_ord
        (Cardinal.aleph0_le_aleph
          (1 : Ordinal.{u + 1}))).bot_lt
  haveI : Nonempty (guess alpha) :=
    Ordinal.type_ne_zero_iff_nonempty.mp hTypePos.ne'
  let i0 : guess alpha := Classical.choice inferInstance
  have hLadderNonempty : (guess alpha).Nonempty := ⟨i0.1, i0.2⟩
  have hLadderDirected : DirectedOn (· ≤ ·) (guess alpha) := by
    intro i hi j hj
    by_cases hij : i ≤ j
    · exact ⟨j, hj, hij, le_rfl⟩
    · exact ⟨i, hi, le_rfl, le_of_not_ge hij⟩
  have hLadderLUB : IsLUB (guess alpha) alpha := by
    constructor
    · intro i hi
      exact (hLadder.1 i hi).le
    · intro b hb
      change alpha.1 ≤ b.1
      rw [← hLadder.2.2]
      apply csSup_le (hLadderNonempty.image fun i => i.1)
      rintro _ ⟨i, hi, rfl⟩
      exact hb hi
  have hAlphaGood :
      alpha.1.cof = Cardinal.aleph 1 ->
        SuccessorAlephLocalMaxPcfRankOmegaThreeRankClosureBelowAt
          hMax bound guess eta alpha := by
    apply hRankClub.dirSupClosed
      (d := guess alpha) (a := alpha)
    · intro i hi
      exact (hGuessSubset hi).2
    · exact hLadderNonempty
    · exact hLadderDirected
    · exact hLadderLUB
  let X : Set (Ordinal.{u}) :=
    (fun i : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord =>
      (eta i).1) '' guess alpha
  have hEtaValueStrict : StrictMono
      (fun i : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord =>
        (eta i).1) := by
    intro i j hij
    exact hNormal.strictMono hij
  have hTypeX : Ordinal.type ((· < ·) : X -> X -> Prop) =
      Ordinal.omega.{u + 1} 1 := by
    have hIso : guess alpha ≃o X :=
      StrictMonoOn.orderIso
        (fun i : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord =>
          (eta i).1)
        (guess alpha)
        (hEtaValueStrict.strictMonoOn (guess alpha))
    rw [← hIso.toRelIsoLT.ordinal_type_eq]
    exact hLadder.2.1
  have hXC : X ⊆ (fun i : Set.Iio delta => i.1) '' C := by
    rintro x ⟨i, hiGuess, rfl⟩
    exact ⟨eta i, (hGuessSubset hiGuess).1, rfl⟩
  have hSup : sSup X = (eta alpha).1 :=
    normal_map_omegaOneCofinalLadder_sSup hNormal hLadder
  refine ⟨X, hXC, hTypeX, ?_⟩
  intro gamma hGamma hRankBound
  obtain ⟨i, hiGuess, rfl⟩ := hGamma
  rw [hSup]
  exact hAlphaGood hAlphaCof i hiGuess
    (countable_inter_Iio_of_orderType_omegaOne hTypeX
      ⟨i, hiGuess, rfl⟩)
    hRankBound

#print axioms
  successorAlephLocalMaxPcfRankReflectionBelowAt_of_normal_of_clubRankClosureBelow


/-! 排除反射由构造模块直接完成；此处保留其目标有界原则类型。 -/

def SuccessorAlephLocalOmegaFourTargetReflectionPrinciple
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta) : Prop :=
  targetIndexOmega4.{u} <= theta ->
    exists delta : Ordinal.{u},
      delta < theta /\
        delta < targetIndexOmega4.{u} /\
        Order.IsSuccLimit delta /\
        Cardinal.aleph0 < delta.cof /\
        SuccessorAlephLocalMaxPcfRankReflectionBelowAt
          hMax targetIndexOmega4 delta


/-! 最终路径只保留目标有界反射原则，并直接定义最大见证的阿列夫指标。 -/

noncomputable def alephSuccSetAtMostIdealEscapeMaxAlephIndex
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hEscape : GeneratorAtMostIdealEscapesCanonicalUltrafilters G) :
    Ordinal.{u} :=
  maxPcfWitnessAlephIndex
    (alephSuccSetMaxPcfWitnessOfAtMostIdealEscape G hEscape)

theorem alephSuccSetAtMostIdealEscapeMax_eq_alephIndex
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hEscape : GeneratorAtMostIdealEscapesCanonicalUltrafilters G) :
    (alephSuccSetMaxPcfWitnessOfAtMostIdealEscape G hEscape).theta =
      Cardinal.aleph
        (alephSuccSetAtMostIdealEscapeMaxAlephIndex G hEscape) :=
  (aleph_maxPcfWitnessAlephIndex_eq
    (alephSuccSetMaxPcfWitnessOfAtMostIdealEscape G hEscape)).symm

#print axioms alephSuccSetAtMostIdealEscapeMax_eq_alephIndex

/-! 核心只需把最大 PCF 见证写成阿列夫形式；其后的输入套餐适配不参与最终证明。 -/

end PcfProject
