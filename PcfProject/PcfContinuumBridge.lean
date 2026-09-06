import PcfProject.PcfCharacteristicModels
import PcfProject.RankClosureConstruction
import PcfProject.PcfNoHoles

/-!
# The `aleph_omega` characteristic-model bridge

This file specializes the pointwise family of Jech 24.21 to the finite-aleph
tail used by the characteristic-model construction in Theorem 24.18.
-/

open Cardinal Set
open scoped Cardinal

namespace PcfProject

universe u

noncomputable def alephSuccSetIndexEquiv :
    Nat ≃ CardinalIndex alephSuccSet.{u} :=
  Equiv.ofBijective alephSuccSetCardinalIndexOfNat
    ⟨alephSuccSetCardinalIndexOfNat_injective,
      alephSuccSetCardinalIndexOfNat_surjective⟩

@[simp] theorem alephSuccSetIndexEquiv_apply (n : Nat) :
    alephSuccSetIndexEquiv.{u} n =
      alephSuccSetCardinalIndexOfNat n := rfl

theorem alephSuccSetIndexEquiv_cardinal (n : Nat) :
    (alephSuccSetIndexEquiv.{u} n).1 = finiteAleph (n + 1) := by
  simp [alephSuccSetIndexEquiv, alephSuccSetCardinalIndexOfNat,
    finiteAleph, Nat.cast_add, Nat.cast_one]

noncomputable def alephSuccFiniteMaxTailMember
    (k : Nat)
    (s : CardinalProductFiniteMaxIndex
      (CardinalProductAllUltrafilterScaleIndex
        alephSuccSet.{u} alephSuccSet_regulars
        alephSuccSet_cardinalIndex_small
        (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta)))
    (n : Nat) : (finiteAleph.{u} (k + n + 1)).ord.ToType :=
  let i := alephSuccSetIndexEquiv.{u} (k + n)
  let value := cardinalProductOrdinalValue
    (cardinalProductAllUltrafilterFiniteMaxFamily
      alephSuccSet.{u} alephSuccSet_regulars
      alephSuccSet_cardinalIndex_small
      (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta) s) i
  Ordinal.ToType.mk ⟨value, by
    have h := cardinalProductOrdinalValue_lt
      (cardinalProductAllUltrafilterFiniteMaxFamily
        alephSuccSet.{u} alephSuccSet_regulars
        alephSuccSet_cardinalIndex_small
        (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta) s) i
    rw [alephSuccSetIndexEquiv_cardinal] at h
    simpa only [Nat.add_assoc] using h⟩

noncomputable def alephOmegaTailOrdinalValue
    (k : Nat)
    (g : forall n : Nat,
      (finiteAleph.{u} (k + n + 1)).ord.ToType)
    (n : Nat) : Ordinal.{u} :=
  ((Ordinal.ToType.mk : Set.Iio
      (finiteAleph.{u} (k + n + 1)).ord ≃o
        (finiteAleph.{u} (k + n + 1)).ord.ToType).symm
    (g n)).1

theorem alephOmegaTailOrdinalValue_lt
    (k : Nat)
    (g : forall n : Nat,
      (finiteAleph.{u} (k + n + 1)).ord.ToType)
    (n : Nat) :
    alephOmegaTailOrdinalValue k g n <
      (finiteAleph (k + n + 1)).ord :=
  ((Ordinal.ToType.mk : Set.Iio
      (finiteAleph.{u} (k + n + 1)).ord ≃o
        (finiteAleph.{u} (k + n + 1)).ord.ToType).symm
    (g n)).2

noncomputable def alephSuccTailExtension
    (k : Nat)
    (g : forall n : Nat,
      (finiteAleph.{u} (k + n + 1)).ord.ToType) :
    ProductElement
      (cardinalProductFrame alephSuccSet.{u}
        (Ideal.emptyOnly (CardinalIndex alephSuccSet.{u}))) := fun i =>
  let m := alephSuccSetIndexEquiv.symm i
  if hkm : k <= m then
    Ordinal.ToType.mk ⟨alephOmegaTailOrdinalValue k g (m - k), by
      have hValue := alephOmegaTailOrdinalValue_lt k g (m - k)
      have hNat : k + (m - k) + 1 = m + 1 := by omega
      have hIndex : alephSuccSetIndexEquiv.{u} m = i :=
        alephSuccSetIndexEquiv.apply_symm_apply i
      have hCard : finiteAleph.{u} (k + (m - k) + 1) = i.1 := by
        rw [hNat, ← alephSuccSetIndexEquiv_cardinal m, hIndex]
      rwa [hCard] at hValue⟩
  else
    Ordinal.ToType.mk ⟨0, Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans
        (alephSuccSet_aleph0_lt i.1 i.2))⟩

theorem alephSuccTailExtension_ordinalValue
    (k : Nat)
    (g : forall n : Nat,
      (finiteAleph.{u} (k + n + 1)).ord.ToType)
    (n : Nat) :
    cardinalProductOrdinalValue (alephSuccTailExtension k g)
        (alephSuccSetIndexEquiv.{u} (k + n)) =
      alephOmegaTailOrdinalValue k g n := by
  have hm : alephSuccSetIndexEquiv.symm
      (alephSuccSetIndexEquiv.{u} (k + n)) = k + n :=
    alephSuccSetIndexEquiv.symm_apply_apply (k + n)
  unfold cardinalProductOrdinalValue alephSuccTailExtension
  dsimp only
  simp only [hm, dif_pos (Nat.le_add_right k n),
    Nat.add_sub_cancel_left]
  exact congrArg Subtype.val
    ((Ordinal.ToType.mk : Set.Iio
      (alephSuccSetIndexEquiv.{u} (k + n)).1.ord ≃o
        (alephSuccSetIndexEquiv.{u} (k + n)).1.ord.ToType).symm_apply_apply _)

theorem alephSuccFiniteMaxTailMember_ordinalValue
    (k : Nat)
    (s : CardinalProductFiniteMaxIndex
      (CardinalProductAllUltrafilterScaleIndex
        alephSuccSet.{u} alephSuccSet_regulars
        alephSuccSet_cardinalIndex_small
        (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta)))
    (n : Nat) :
    ((Ordinal.ToType.mk : Set.Iio
        (finiteAleph.{u} (k + n + 1)).ord ≃o
          (finiteAleph.{u} (k + n + 1)).ord.ToType).symm
      (alephSuccFiniteMaxTailMember k s n)).1 =
    cardinalProductOrdinalValue
      (cardinalProductAllUltrafilterFiniteMaxFamily
        alephSuccSet.{u} alephSuccSet_regulars
        alephSuccSet_cardinalIndex_small
        (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta) s)
      (alephSuccSetIndexEquiv.{u} (k + n)) := by
  simp [alephSuccFiniteMaxTailMember]

noncomputable def alephSuccFiniteMaxTailFamily (k : Nat) :
    AlephOmegaTailCofinalFamily.{u} k where
  Index := CardinalProductFiniteMaxIndex
    (CardinalProductAllUltrafilterScaleIndex
      alephSuccSet.{u} alephSuccSet_regulars
      alephSuccSet_cardinalIndex_small
      (fun _ hTheta => alephSuccSet_aleph0_lt _ hTheta))
  member := alephSuccFiniteMaxTailMember k
  pointwiseCofinal := by
    intro g
    obtain ⟨s, hs⟩ :=
      alephSuccSet_allUltrafilterFiniteMaxFamily_pointwise_cofinal
        (alephSuccTailExtension k g)
    refine ⟨s, ?_⟩
    intro n
    let E := (Ordinal.ToType.mk : Set.Iio
      (finiteAleph.{u} (k + n + 1)).ord ≃o
        (finiteAleph.{u} (k + n + 1)).ord.ToType)
    rw [← E.apply_symm_apply (g n),
      ← E.apply_symm_apply (alephSuccFiniteMaxTailMember k s n)]
    apply E.monotone
    change alephOmegaTailOrdinalValue k g n <=
      ((E.symm (alephSuccFiniteMaxTailMember k s n)).1)
    rw [alephSuccFiniteMaxTailMember_ordinalValue,
      ← alephSuccTailExtension_ordinalValue]
    exact (Ordinal.ToType.mk : Set.Iio
      (alephSuccSetIndexEquiv.{u} (k + n)).1.ord ≃o
        (alephSuccSetIndexEquiv.{u} (k + n)).1.ord.ToType).symm.monotone
      (hs (alephSuccSetIndexEquiv.{u} (k + n)))

#print axioms alephSuccFiniteMaxTailFamily

noncomputable def alephOmegaStageCode
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (i : AlephOmegaChainStage.{u} k) :
    F.Index × AlephOmegaChainStage.{u} k :=
  (F.characteristicIndex
      (alephOmegaChainPreviousCarrier hk F a ha i)
      (mk_alephOmegaChainPreviousCarrier_le hk F a ha i), i)

theorem alephOmegaStageCode_injective
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    Function.Injective (alephOmegaStageCode hk F a ha) := by
  intro i j hij
  exact congrArg Prod.snd hij

def alephOmegaCharacteristicWitness
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    Set (F.Index × AlephOmegaChainStage.{u} k) :=
  Set.range (alephOmegaStageCode hk F a ha)

theorem mk_alephOmegaCharacteristicWitness
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    Cardinal.mk (alephOmegaCharacteristicWitness hk F a ha) =
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
  have hRange := Cardinal.mk_range_eq_of_injective
    (alephOmegaStageCode_injective hk F a ha)
  rw [Cardinal.mk_ord_toType] at hRange
  rw [Cardinal.lift_id'.{u, u + 1}] at hRange
  exact hRange

def alephOmegaWitnessStages
    {k : Nat} {F : AlephOmegaTailCofinalFamily.{u} k}
    (X : Set (F.Index × AlephOmegaChainStage.{u} k)) :
    Set (AlephOmegaChainStage.{u} k) :=
  Prod.snd '' X

theorem alephOmegaWitnessStages_isCofinal
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (X : Set (F.Index × AlephOmegaChainStage.{u} k))
    (hXSubset : X ⊆ alephOmegaCharacteristicWitness hk F a ha)
    (hXCard : Cardinal.mk X =
      Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :
    IsCofinal (alephOmegaWitnessStages X) := by
  have hSndInj : Set.InjOn Prod.snd X := by
    intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := hXSubset hx
    obtain ⟨j, rfl⟩ := hXSubset hy
    have hij : i = j := hxy
    subst j
    rfl
  have hStagesCard : Cardinal.lift.{u + 1}
      (Cardinal.mk (alephOmegaWitnessStages X)) = Cardinal.mk X := by
    have hImage := Cardinal.mk_image_eq_of_injOn_lift
      Prod.snd X hSndInj
    rw [Cardinal.lift_id'.{u, u + 1}] at hImage
    simpa only [alephOmegaWitnessStages] using hImage
  by_contra hNotCofinal
  obtain ⟨j, hj⟩ := BddAbove.of_not_isCofinal hNotCofinal
  have hSubsetIic : alephOmegaWitnessStages X ⊆ Set.Iic j := by
    intro i hi
    exact hj hi
  have hSmallInitial :=
    smallInitialSegments_ord_toType_of_isRegular
      (finiteAleph_isRegular k) j
  rw [Ordinal.cof_toType, (finiteAleph_isRegular k).cof_ord,
    Cardinal.lift_id'.{u, u}, Cardinal.lift_id'.{u, u}]
    at hSmallInitial
  have hStrict : Cardinal.lift.{u + 1}
      (Cardinal.mk (alephOmegaWitnessStages X)) <
        Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
    calc
      Cardinal.lift.{u + 1}
          (Cardinal.mk (alephOmegaWitnessStages X)) <=
          Cardinal.lift.{u + 1} (Cardinal.mk (Set.Iic j)) :=
        Cardinal.lift_le.mpr (Cardinal.mk_subtype_mono hSubsetIic)
      _ < Cardinal.lift.{u + 1}
          (finiteAleph.{u} k) := by
        exact Cardinal.lift_lt.mpr hSmallInitial
  rw [hStagesCard, hXCard] at hStrict
  exact (lt_irrefl _ hStrict)

#print axioms mk_alephOmegaCharacteristicWitness
#print axioms alephOmegaWitnessStages_isCofinal

theorem AlephOmegaTailCofinalFamily.memberPoint_lt
    {k : Nat} (F : AlephOmegaTailCofinalFamily.{u} k)
    (q : F.Index) (n : Nat) :
    (F.memberPoint q n).1 <
      (finiteAleph (k + n + 1)).ord := by
  unfold AlephOmegaTailCofinalFamily.memberPoint
  exact ((Ordinal.ToType.mk : Set.Iio
    (finiteAleph.{u} (k + n + 1)).ord ≃o
      (finiteAleph.{u} (k + n + 1)).ord.ToType).symm
    (F.member q n)).2

theorem alephOmegaStageMemberPoint_mem_modelChain
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) (i : AlephOmegaChainStage.{u} k) :
    F.memberPoint (alephOmegaStageCode hk F a ha i).1 n ∈
      (alephOmegaModelChain hk F a ha i).substructure := by
  apply alephOmegaStageSeed_subset_modelChain hk F a ha i
  exact Or.inr (Set.mem_range_self n)

theorem alephOmegaStageCharacteristic_le_memberPoint
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) (i : AlephOmegaChainStage.{u} k) :
    alephOmegaStageCharacteristic hk F a ha n i <=
      (F.memberPoint (alephOmegaStageCode hk F a ha i).1 n).1 := by
  have h := F.characteristic_le
    (alephOmegaChainPreviousCarrier hk F a ha i)
    (mk_alephOmegaChainPreviousCarrier_le hk F a ha i) n
  have h' := (Ordinal.ToType.mk : Set.Iio
    (finiteAleph.{u} (k + n + 1)).ord ≃o
      (finiteAleph.{u} (k + n + 1)).ord.ToType).symm.monotone h
  simpa [alephOmegaStageCharacteristic, alephOmegaStageCode,
    AlephOmegaTailCofinalFamily.memberPoint] using h'

#print axioms alephOmegaStageCharacteristic_le_memberPoint

theorem alephOmegaCharacteristicWitness_exists_code_ge
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (X : Set (F.Index × AlephOmegaChainStage.{u} k))
    (hXSubset : X ⊆ alephOmegaCharacteristicWitness hk F a ha)
    (hXCard : Cardinal.mk X =
      Cardinal.lift.{u + 1} (finiteAleph.{u} k))
    (i : AlephOmegaChainStage.{u} k) :
    exists j : AlephOmegaChainStage.{u} k,
      i <= j ∧ alephOmegaStageCode hk F a ha j ∈ X := by
  obtain ⟨j, hjStages, hij⟩ :=
    (alephOmegaWitnessStages_isCofinal
      hk F a ha X hXSubset hXCard) i
  obtain ⟨p, hpX, hpj⟩ := hjStages
  obtain ⟨r, hr⟩ := hXSubset hpX
  have hrj : r = j := (congrArg Prod.snd hr).trans hpj
  refine ⟨r, hij.trans_eq hrj.symm, ?_⟩
  simpa only [hr] using hpX

noncomputable def alephOmegaWitnessReconstruct
    {k : Nat} (F : AlephOmegaTailCofinalFamily.{u} k)
    (X : Set (F.Index × AlephOmegaChainStage.{u} k)) :
    Nat -> Ordinal.{u} := fun n =>
  sSup ((fun p : F.Index × AlephOmegaChainStage.{u} k =>
    (F.memberPoint p.1 n).1 + 1) '' X)

theorem alephOmegaWitnessReconstruct_of_subset
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (X : Set (F.Index × AlephOmegaChainStage.{u} k))
    (hXSubset : X ⊆ alephOmegaCharacteristicWitness hk F a ha)
    (hXCard : Cardinal.mk X =
      Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :
    alephOmegaWitnessReconstruct F X =
      alephOmegaFinalCharacteristic hk F a ha := by
  funext n
  let values : Set Ordinal.{u} :=
    (fun p : F.Index × AlephOmegaChainStage.{u} k =>
      (F.memberPoint p.1 n).1 + 1) '' X
  have hValueUpper : forall z, z ∈ values ->
      z <= alephOmegaFinalCharacteristic hk F a ha n := by
    intro z hz
    obtain ⟨p, hpX, rfl⟩ := hz
    obtain ⟨i, rfl⟩ := hXSubset hpX
    have hModel := alephOmegaStageMemberPoint_mem_modelChain
      hk F a ha n i
    have hFinal : F.memberPoint
        (alephOmegaStageCode hk F a ha i).1 n ∈
        alephOmegaFinalSubstructure hk F a ha :=
      (alephOmegaFinalSubstructure_mem_iff hk F a ha _).mpr
        ⟨i, hModel⟩
    exact Order.add_one_le_iff.mpr
      (alephOmegaFinalSubstructure_below_characteristic
        hk F a ha n _ hFinal (F.memberPoint_lt _ _))
  have hValuesBounded : BddAbove values :=
    ⟨alephOmegaFinalCharacteristic hk F a ha n, hValueUpper⟩
  have hReconstructLe : alephOmegaWitnessReconstruct F X n <=
      alephOmegaFinalCharacteristic hk F a ha n := by
    unfold alephOmegaWitnessReconstruct
    exact csSup_le' hValueUpper
  apply le_antisymm hReconstructLe
  unfold alephOmegaFinalCharacteristic alephOmegaSetCharacteristic
  apply csSup_le'
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨i, hiModel⟩ := Set.mem_iUnion.1 hp.1
  letI : NoMaxOrder (AlephOmegaChainStage.{u} k) :=
    Cardinal.noMaxOrder hk
  obtain ⟨j, hij⟩ := exists_gt i
  obtain ⟨l, hjl, hlX⟩ :=
    alephOmegaCharacteristicWitness_exists_code_ge
      hk F a ha X hXSubset hXCard j
  have hil : i < l := hij.trans_le hjl
  have hpCarrier : p ∈
      alephOmegaChainPreviousCarrier hk F a ha l :=
    alephOmegaModelChain_subset_chainPreviousCarrier
      hk F a ha hil hiModel
  have hpStage : p.1 <
      alephOmegaStageCharacteristic hk F a ha n l :=
    lt_alephOmegaSetCharacteristic k n _ hpCarrier hp.2
  have hpMember : p.1 <
      (F.memberPoint (alephOmegaStageCode hk F a ha l).1 n).1 :=
    hpStage.trans_le
      (alephOmegaStageCharacteristic_le_memberPoint hk F a ha n l)
  have hMemberValue :
      (F.memberPoint (alephOmegaStageCode hk F a ha l).1 n).1 + 1 ∈
        values := ⟨alephOmegaStageCode hk F a ha l, hlX, rfl⟩
  exact (Order.add_one_le_iff.mpr hpMember).trans
    ((lt_add_one _).le.trans (le_csSup hValuesBounded hMemberValue))

#print axioms alephOmegaWitnessReconstruct_of_subset

abbrev CountableAlephOmegaSubset : Type (u + 1) :=
  {a : Set AlephOmegaOrdinal.{u} // Cardinal.mk a <= Cardinal.aleph0}

noncomputable def alephOmegaCountableSubsetCharacteristic
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : CountableAlephOmegaSubset.{u}) : Nat -> Ordinal.{u} :=
  alephOmegaFinalCharacteristic hk F a.1 a.2

abbrev AlephOmegaCharacteristicRange
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k) :=
  Set.range (alephOmegaCountableSubsetCharacteristic hk F)

noncomputable def alephOmegaCharacteristicSource
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (chi : AlephOmegaCharacteristicRange hk F) :
    CountableAlephOmegaSubset.{u} :=
  Classical.choose chi.2

theorem alephOmegaCharacteristicSource_spec
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (chi : AlephOmegaCharacteristicRange hk F) :
    alephOmegaCountableSubsetCharacteristic hk F
        (alephOmegaCharacteristicSource hk F chi) = chi.1 :=
  Classical.choose_spec chi.2

noncomputable def alephOmegaUniformSubsetCharacteristicCoding
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k) :
    UniformSubsetCharacteristicCoding
      (AlephOmegaCharacteristicRange hk F)
      (F.Index × AlephOmegaChainStage.{u} k)
      (Nat -> Ordinal.{u})
      (Cardinal.lift.{u + 1} (finiteAleph.{u} k)) where
  characteristic := Subtype.val
  characteristic_injective := Subtype.val_injective
  witness := fun chi =>
    let a := alephOmegaCharacteristicSource hk F chi
    alephOmegaCharacteristicWitness hk F a.1 a.2
  witness_cardinal := by
    intro chi
    exact mk_alephOmegaCharacteristicWitness hk F _ _
  reconstruct := alephOmegaWitnessReconstruct F
  reconstruct_of_subset := by
    intro chi X hXSubset hXCard
    let a := alephOmegaCharacteristicSource hk F chi
    calc
      alephOmegaWitnessReconstruct F X =
          alephOmegaFinalCharacteristic hk F a.1 a.2 :=
        alephOmegaWitnessReconstruct_of_subset
          hk F a.1 a.2 X hXSubset hXCard
      _ = chi.1 := alephOmegaCharacteristicSource_spec hk F chi

#print axioms alephOmegaUniformSubsetCharacteristicCoding

noncomputable def uniformSubsetCover_of_card_lt_aleph
    (K : Type u) {mu : Cardinal.{u}}
    (hMu : Cardinal.IsRegular mu)
    (hK : Cardinal.mk K < Cardinal.aleph mu.ord) :
    UniformSubsetCover K mu :=
  let C := uniformSubsetCover_of_lt_aleph hMu hK
  let e : (Cardinal.mk K).ord.ToType ≃ K :=
    (Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk K))).some
  C.mapEquiv e

theorem alephOmegaCharacteristicRange_mk_le
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (alpha : Cardinal.{u + 1})
    (hAlphaInfinite : Cardinal.aleph0 <= alpha)
    (hIndex : Cardinal.mk F.Index <= alpha)
    (hStage : Cardinal.lift.{u + 1} (finiteAleph.{u} k) <= alpha)
    (hPower : (2 : Cardinal.{u + 1}) ^
      (Cardinal.lift.{u + 1} (finiteAleph.{u} k)) <= alpha)
    (hAlphaLt : alpha < Cardinal.aleph
      (Cardinal.lift.{u + 1} (finiteAleph.{u} k)).ord) :
    Cardinal.mk (AlephOmegaCharacteristicRange hk F) <= alpha := by
  let K := F.Index × AlephOmegaChainStage.{u} k
  let mu := Cardinal.lift.{u + 1} (finiteAleph.{u} k)
  have hK : Cardinal.mk K <= alpha := by
    calc
      Cardinal.mk K = Cardinal.mk F.Index *
          Cardinal.lift.{u + 1}
            (Cardinal.mk (AlephOmegaChainStage.{u} k)) := by
        rw [Cardinal.mk_prod, Cardinal.lift_id'.{u, u + 1}]
      _ = Cardinal.mk F.Index * mu := by
        rw [Cardinal.mk_ord_toType]
      _ <= alpha * alpha := mul_le_mul' hIndex hStage
      _ = alpha := Cardinal.mul_eq_self hAlphaInfinite
  let C : UniformSubsetCover K mu :=
    uniformSubsetCover_of_card_lt_aleph K
      (finiteAleph_isRegular k).lift (hK.trans_lt hAlphaLt)
  exact (alephOmegaUniformSubsetCharacteristicCoding hk F).mk_le_of_uniformSubsetCover
    C hPower hK

#print axioms alephOmegaCharacteristicRange_mk_le

theorem mk_alephOmegaFinalSubstructure_le
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    Cardinal.mk (alephOmegaFinalSubstructure hk F a ha) <=
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
  have hCarrier :
      ((alephOmegaFinalSubstructure hk F a ha :
        Set AlephOmegaOrdinal.{u})) =
        alephOmegaModelUnion hk F a ha := by
    ext x
    change (x ∈ alephOmegaFinalSubstructure hk F a ha) ↔
      x ∈ alephOmegaModelUnion hk F a ha
    rw [alephOmegaFinalSubstructure_mem_iff]
    simp only [alephOmegaModelUnion, Set.mem_iUnion]
    constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, hi⟩
  exact (Cardinal.mk_congr (Equiv.setCongr hCarrier)).le.trans
    (mk_alephOmegaModelUnion_le hk F a ha)

abbrev AlephOmegaSequence : Type (u + 1) :=
  Nat -> AlephOmegaOrdinal.{u}

noncomputable def alephOmegaSequenceSubset
    (f : AlephOmegaSequence.{u}) : CountableAlephOmegaSubset.{u} :=
  ⟨Set.range f, by
    have h := Cardinal.mk_range_le_lift (f := f)
    rw [Cardinal.lift_id'.{0, u + 1}, Cardinal.mk_nat,
      Cardinal.lift_aleph0] at h
    exact h⟩

noncomputable def alephOmegaSequenceCharacteristic
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (f : AlephOmegaSequence.{u}) :
    AlephOmegaCharacteristicRange hk F :=
  ⟨alephOmegaCountableSubsetCharacteristic hk F
      (alephOmegaSequenceSubset f),
    Set.mem_range_self (alephOmegaSequenceSubset f)⟩

noncomputable def alephOmegaSequenceFiberEmbedding
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (hkUncountable : Cardinal.aleph0 < finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (chi : AlephOmegaCharacteristicRange hk F) :
    {f : AlephOmegaSequence.{u} |
      alephOmegaSequenceCharacteristic hk F f = chi} ↪
      (Nat -> alephOmegaFinalSubstructure hk F
        (alephOmegaCharacteristicSource hk F chi).1
        (alephOmegaCharacteristicSource hk F chi).2) where
  toFun := fun f n => ⟨f.1 n, by
    let af := alephOmegaSequenceSubset f.1
    let ac := alephOmegaCharacteristicSource hk F chi
    have hOwn : f.1 n ∈
        alephOmegaFinalSubstructure hk F af.1 af.2 :=
      alephOmegaInput_subset_finalSubstructure hk F af.1 af.2
        (Set.mem_range_self n)
    have hCharF : alephOmegaCountableSubsetCharacteristic hk F af = chi.1 := by
      exact congrArg Subtype.val f.2
    have hCharC : alephOmegaCountableSubsetCharacteristic hk F ac = chi.1 :=
      alephOmegaCharacteristicSource_spec hk F chi
    have hModels := alephOmegaFinalSubstructure_eq_of_characteristic_eq
      hk hkUncountable F af.1 ac.1 af.2 ac.2
      (hCharF.trans hCharC.symm)
    rw [hModels] at hOwn
    exact hOwn⟩
  inj' := by
    intro f g hfg
    apply Subtype.ext
    funext n
    exact congrArg (fun h => (h n).1) hfg

theorem alephOmegaSequenceCharacteristic_fiber_mk_le
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (hkUncountable : Cardinal.aleph0 < finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (chi : AlephOmegaCharacteristicRange hk F) :
    Cardinal.mk {f : AlephOmegaSequence.{u} |
        alephOmegaSequenceCharacteristic hk F f = chi} <=
      (2 : Cardinal.{u + 1}) ^
        Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
  let ac := alephOmegaCharacteristicSource hk F chi
  let mu := Cardinal.lift.{u + 1} (finiteAleph.{u} k)
  calc
    Cardinal.mk {f : AlephOmegaSequence.{u} |
        alephOmegaSequenceCharacteristic hk F f = chi} <=
        Cardinal.mk (Nat -> alephOmegaFinalSubstructure hk F ac.1 ac.2) :=
      Cardinal.mk_le_of_injective
        (alephOmegaSequenceFiberEmbedding hk hkUncountable F chi).injective
    _ = Cardinal.mk (alephOmegaFinalSubstructure hk F ac.1 ac.2) ^
        Cardinal.aleph0 := by
      simp only [Cardinal.mk_arrow, Cardinal.mk_nat,
        Cardinal.lift_aleph0, Cardinal.lift_id']
    _ <= mu ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_right
        (mk_alephOmegaFinalSubstructure_le hk F ac.1 ac.2)
    _ <= ((2 : Cardinal.{u + 1}) ^ mu) ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_right (Cardinal.cantor mu).le
    _ = (2 : Cardinal.{u + 1}) ^ mu := by
      rw [← Cardinal.power_mul,
        Cardinal.mul_aleph0_eq
          (Cardinal.aleph0_le_lift.mpr hk)]

#print axioms alephOmegaSequenceCharacteristic_fiber_mk_le

theorem alephOmegaSequence_mk_le
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (hkUncountable : Cardinal.aleph0 < finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (alpha : Cardinal.{u + 1})
    (hAlphaInfinite : Cardinal.aleph0 <= alpha)
    (hCharacteristic :
      Cardinal.mk (AlephOmegaCharacteristicRange hk F) <= alpha)
    (hPower : (2 : Cardinal.{u + 1}) ^
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) <= alpha) :
    Cardinal.mk (AlephOmegaSequence.{u}) <= alpha := by
  calc
    Cardinal.mk (AlephOmegaSequence.{u}) <=
        Cardinal.mk (AlephOmegaCharacteristicRange hk F) *
          ((2 : Cardinal.{u + 1}) ^
            Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :=
      Cardinal.mk_le_mk_mul_of_mk_preimage_le
        (alephOmegaSequenceCharacteristic hk F)
        (alephOmegaSequenceCharacteristic_fiber_mk_le
          hk hkUncountable F)
    _ <= alpha * alpha := mul_le_mul' hCharacteristic hPower
    _ = alpha := Cardinal.mul_eq_self hAlphaInfinite

theorem lift_targetAlephOmega_power_aleph0_eq_sequence_mk :
    Cardinal.lift.{u + 1}
        (targetAlephOmega.{u} ^ Cardinal.aleph0) =
      Cardinal.mk (AlephOmegaSequence.{u}) := by
  simp only [AlephOmegaSequence, Cardinal.mk_arrow,
    Cardinal.mk_nat, Cardinal.lift_power, Cardinal.lift_aleph0,
    AlephOmegaOrdinal, Cardinal.mk_Iio_ordinal, Cardinal.card_ord,
    Cardinal.lift_id']

theorem lift_targetAlephOmega_power_aleph0_le_of_characteristic_bound
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (hkUncountable : Cardinal.aleph0 < finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (alpha : Cardinal.{u + 1})
    (hAlphaInfinite : Cardinal.aleph0 <= alpha)
    (hCharacteristic :
      Cardinal.mk (AlephOmegaCharacteristicRange hk F) <= alpha)
    (hPower : (2 : Cardinal.{u + 1}) ^
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) <= alpha) :
    Cardinal.lift.{u + 1}
        (targetAlephOmega.{u} ^ Cardinal.aleph0) <= alpha := by
  rw [lift_targetAlephOmega_power_aleph0_eq_sequence_mk]
  exact alephOmegaSequence_mk_le
    hk hkUncountable F alpha hAlphaInfinite hCharacteristic hPower

#print axioms
  lift_targetAlephOmega_power_aleph0_le_of_characteristic_bound

theorem aleph0_le_finiteAleph_four :
    Cardinal.aleph0 <= finiteAleph.{u} 4 := by
  simp [finiteAleph]

theorem aleph0_lt_finiteAleph_four :
    Cardinal.aleph0 < finiteAleph.{u} 4 := by
  simp [finiteAleph]

theorem targetAlephOmega4_eq_aleph_finiteAleph_four_ord :
    targetAlephOmega4.{u} =
      Cardinal.aleph (finiteAleph.{u} 4).ord := rfl

theorem lift_targetAlephOmega4_eq_aleph_lift_finiteAleph_four_ord :
    Cardinal.lift.{u + 1} targetAlephOmega4.{u} =
      Cardinal.aleph
        (Cardinal.lift.{u + 1} (finiteAleph.{u} 4)).ord := by
  rw [targetAlephOmega4_eq_aleph_finiteAleph_four_ord,
    Cardinal.lift_aleph, Cardinal.lift_ord]

/-! Jech's Theorem 24.18 in the exact form needed downstream: under the
strong-limit hypothesis, a maximum PCF witness below `aleph_(aleph_4)`
already bounds `aleph_omega ^ aleph_0`. -/
theorem targetAlephOmega_power_aleph0_le_maxPcf_of_strongLimit_of_lt_alephOmega4
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    (M : MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u})
    (hMlt : M.theta < targetAlephOmega4.{u}) :
    targetAlephOmega.{u} ^ Cardinal.aleph0 <= M.theta := by
  let F := alephSuccFiniteMaxTailFamily.{u} 4
  have hThetaLower : targetAlephOmega.{u} <= M.theta :=
    alephSuccSet_maxPcf_theta_ge_targetAlephOmega M.isMax
  have hIndex : Cardinal.mk F.Index <=
      Cardinal.lift.{u + 1} M.theta := by
    simpa only [F, alephSuccFiniteMaxTailFamily] using
      (alephSuccSet_mk_allUltrafilterFiniteMaxIndex_le_maxPcf
        hStrongLimit M)
  have hStage : Cardinal.lift.{u + 1} (finiteAleph.{u} 4) <=
      Cardinal.lift.{u + 1} M.theta :=
    Cardinal.lift_le.mpr
      ((finiteAleph_lt_targetAlephOmega 4).le.trans hThetaLower)
  have hPowerBase : (2 : Cardinal.{u}) ^ finiteAleph.{u} 4 <=
      M.theta :=
    (hStrongLimit.isStrongPrelimit
      (finiteAleph_lt_targetAlephOmega 4)).le.trans hThetaLower
  have hPower : (2 : Cardinal.{u + 1}) ^
      Cardinal.lift.{u + 1} (finiteAleph.{u} 4) <=
        Cardinal.lift.{u + 1} M.theta := by
    simpa only [Cardinal.lift_power, Cardinal.lift_ofNat] using
      (Cardinal.lift_le.mpr hPowerBase)
  have hAlphaLt : Cardinal.lift.{u + 1} M.theta <
      Cardinal.aleph
        (Cardinal.lift.{u + 1} (finiteAleph.{u} 4)).ord := by
    have h := Cardinal.lift_lt.mpr hMlt
    rwa [lift_targetAlephOmega4_eq_aleph_lift_finiteAleph_four_ord]
      at h
  have hCharacteristic :
      Cardinal.mk (AlephOmegaCharacteristicRange
        aleph0_le_finiteAleph_four F) <=
          Cardinal.lift.{u + 1} M.theta :=
    alephOmegaCharacteristicRange_mk_le
      aleph0_le_finiteAleph_four F
      (Cardinal.lift.{u + 1} M.theta)
      (Cardinal.aleph0_le_lift.mpr M.isRegular.aleph0_le)
      hIndex hStage hPower hAlphaLt
  have hLift : Cardinal.lift.{u + 1}
      (targetAlephOmega.{u} ^ Cardinal.aleph0) <=
        Cardinal.lift.{u + 1} M.theta :=
    lift_targetAlephOmega_power_aleph0_le_of_characteristic_bound
      aleph0_le_finiteAleph_four aleph0_lt_finiteAleph_four F
      (Cardinal.lift.{u + 1} M.theta)
      (Cardinal.aleph0_le_lift.mpr M.isRegular.aleph0_le)
      hCharacteristic hPower
  exact Cardinal.lift_le.mp hLift

#print axioms
  targetAlephOmega_power_aleph0_le_maxPcf_of_strongLimit_of_lt_alephOmega4

theorem continuumAtAlephOmega_le_maxPcf_of_strongLimit_of_lt_alephOmega4
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    (M : MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u})
    (hMlt : M.theta < targetAlephOmega4.{u}) :
    continuumAtAlephOmega.{u} <= M.theta := by
  rw [continuumAtAlephOmega_eq_targetAlephOmega_power_aleph0_of_strongLimit
    hStrongLimit]
  exact targetAlephOmega_power_aleph0_le_maxPcf_of_strongLimit_of_lt_alephOmega4
    hStrongLimit M hMlt


/-! Under the target's own strong-limit premise, the continuum is below
`aleph_omega`. The proved no-holes theorem above the continuum, together
with the elementary low-core membership theorem, supplies every successor
aleph below the displayed core maximum. No no-holes premise is needed. -/
theorem successorAlephInitialSegmentInCorePcf_of_strongLimit_of_maxAlephIndex
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    (M : MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u}) :
    SuccessorAlephInitialSegmentInCorePcf (maxPcfWitnessAlephIndex M) := by
  intro i hi
  have hUncountable : Cardinal.aleph0 < Cardinal.aleph (i + 1) :=
    Cardinal.aleph0_lt_aleph.mpr ((zero_le : (0 : Ordinal.{u}) <= i).trans_lt (lt_add_one i))
  by_cases hLow : Cardinal.aleph (i + 1) < targetAlephOmega
  · exact cardinalProductRepresentation_mem_pcf_of_mem alephSuccSet_regulars
      (alephSuccSet_of_aleph0_lt_of_lt_targetAlephOmega hUncountable hLow)
  · apply alephSuccSet_mem_pcf_of_regular_above_continuum_le_pcf
      (Cardinal.isRegular_aleph_add_one i) _ _ M.mem_pcf
    · have hAleph0 : Cardinal.aleph0 < targetAlephOmega.{u} :=
        Cardinal.aleph0_lt_aleph.mpr Ordinal.omega0_pos
      exact (hStrongLimit.isStrongPrelimit hAleph0).trans_le (le_of_not_gt hLow)
    · rw [← aleph_maxPcfWitnessAlephIndex_eq M]
      exact Cardinal.aleph_le_aleph.mpr (Order.succ_le_iff.mpr hi)

#print axioms successorAlephInitialSegmentInCorePcf_of_strongLimit_of_maxAlephIndex

end PcfProject
