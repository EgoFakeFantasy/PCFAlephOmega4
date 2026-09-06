import PcfProject.FinalAssembly
import PcfProject.PcfIdempotence
import PcfProject.Stationary

/-!
# Shelah-style PCF closure interfaces

This module records the closure operation used in the usual proof of the
`aleph_(omega_4)` bound.  The elementary algebra of the closure is proved
from the canonical PCF monotonicity theorem.  The genuinely difficult part of
Shelah's argument is kept visible in `ShelahClosureCoverCertificate`: it is a
certificate that a small family of countable closures covers all countable
subsets.  The final covering-number bridge then uses only the already proved
covering-number API.

The closure below is the successor-aleph version of
`cl X = { i : aleph_(i+1) ∈ pcf({ aleph_(j+1) : j ∈ X }) }`.
We retain the ordinal bound `i < targetIndexOmega4` in the closure, as in the
standard `omega_4` argument.
-/

namespace PcfProject

universe u v

open Cardinal Set
open scoped Cardinal

/-! The successor-aleph image of a set of ordinal indices. -/
def successorAlephCardSet (X : Set (Ordinal.{u})) : CardSet.{u} :=
  fun theta => exists i, i ∈ X /\ theta = Cardinal.aleph (i + 1)

/-! The canonical small index used to present the successor-aleph core. -/
def naturalOrdinalIndex : Set (Ordinal.{u}) :=
  Set.range (fun n : Nat => (n : Ordinal.{u}))

theorem naturalOrdinalIndex_countable :
    naturalOrdinalIndex.{u}.Countable := by
  exact Set.countable_range (fun n : Nat => (n : Ordinal.{u}))

theorem naturalOrdinalIndex_subset_target :
    naturalOrdinalIndex.{u} ⊆ Set.Iio targetIndexOmega4 := by
  intro i hi
  obtain ⟨n, rfl⟩ := hi
  have hNat : (n : Ordinal.{u}) < Ordinal.omega0 :=
    Ordinal.natCast_lt_omega0 n
  have hOmega : (Ordinal.omega0 : Ordinal.{u}) < targetIndexOmega4 := by
    simpa only [targetIndexOmega4] using
      (Cardinal.omega0_lt_ord (a := Cardinal.aleph (4 : Ordinal.{u}))).mpr
        (Cardinal.aleph0_lt_aleph.mpr (by simp))
  exact hNat.trans hOmega

theorem naturalOrdinalIndex_zero_mem :
    (0 : Ordinal.{u}) ∈ naturalOrdinalIndex := by
  exact ⟨0, by simp⟩

theorem successorAlephCardSet_naturalOrdinalIndex_eq :
    successorAlephCardSet naturalOrdinalIndex.{u} = alephSuccSet.{u} := by
  funext theta
  apply propext
  constructor
  · rintro ⟨i, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    rfl
  · rintro ⟨n, rfl⟩
    exact ⟨(n : Ordinal.{u}), ⟨n, rfl⟩, rfl⟩

/-! The standard successor-aleph core is convex among regular cardinals.  The
proof uses only the aleph-index representation of every cardinal above
`aleph0` and the fact that the interval is bounded by two finite aleph
indices. -/
theorem alephSuccSet_interval :
    CardinalInterval alephSuccSet.{u} := by
  intro left theta right hLeft hRight _hRegular hBetween
  obtain ⟨n, hLeftEq⟩ := hLeft
  obtain ⟨m, hRightEq⟩ := hRight
  have hThetaAleph0 : Cardinal.aleph0 < theta := by
    have hLeftAleph0 : Cardinal.aleph0 < left := by
      rw [hLeftEq]
      exact Cardinal.aleph0_lt_aleph.mpr
        ((zero_le : (0 : Ordinal.{u}) <= (n : Ordinal.{u})).trans_lt
          (lt_add_one _))
    exact hLeftAleph0.trans hBetween.1
  obtain ⟨o, hThetaEq⟩ :=
    Cardinal.mem_range_aleph_iff.mpr hThetaAleph0.le
  have hLeftIndex :
      (n : Ordinal.{u}) + 1 < o := by
    apply Cardinal.aleph_lt_aleph.mp
    calc
      Cardinal.aleph ((n : Ordinal.{u}) + 1) = left := hLeftEq.symm
      _ < theta := hBetween.1
      _ = Cardinal.aleph o := hThetaEq.symm
  have hRightIndex :
      o < (m : Ordinal.{u}) + 1 := by
    apply Cardinal.aleph_lt_aleph.mp
    calc
      Cardinal.aleph o = theta := hThetaEq
      _ < right := hBetween.2
      _ = Cardinal.aleph ((m : Ordinal.{u}) + 1) := hRightEq
  have hNatIndex : o < Ordinal.omega0 := by
    have hm : (m : Ordinal.{u}) + 1 < Ordinal.omega0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Ordinal.natCast_lt_omega0 (m + 1)
    exact hRightIndex.trans hm
  obtain ⟨k, hOk⟩ := Ordinal.lt_omega0.mp hNatIndex
  have hkZero : k ≠ 0 := by
    intro hk
    subst k
    have hOzero : o = 0 := hOk
    rw [hOzero] at hLeftIndex
    exact (not_lt_of_ge
      (show (0 : Ordinal.{u}) ≤ (n : Ordinal.{u}) + 1 from zero_le)) hLeftIndex
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hkZero
  refine ⟨p, ?_⟩
  calc
    theta = Cardinal.aleph o := hThetaEq.symm
    _ = Cardinal.aleph ((p : Ordinal.{u}) + 1) := by
      rw [hOk, hp]
      simp [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]

theorem successorAlephCardSet_mono
    {X Y : Set (Ordinal.{u})}
    (hXY : X ⊆ Y) :
    SubsetOf (successorAlephCardSet X) (successorAlephCardSet Y) := by
  intro theta hTheta
  obtain ⟨i, hi, rfl⟩ := hTheta
  exact ⟨i, hXY hi, rfl⟩

theorem successorAlephCardSet_union
    (X Y : Set (Ordinal.{u})) :
    successorAlephCardSet (X ∪ Y) =
      UnionCardSet (successorAlephCardSet X)
        (successorAlephCardSet Y) := by
  funext theta
  apply propext
  constructor
  · rintro ⟨i, hi, rfl⟩
    cases hi with
    | inl hi => exact Or.inl ⟨i, hi, rfl⟩
    | inr hi => exact Or.inr ⟨i, hi, rfl⟩
  · intro hTheta
    cases hTheta with
    | inl hX =>
        obtain ⟨i, hi, hTheta⟩ := hX
        exact ⟨i, Or.inl hi, hTheta⟩
    | inr hY =>
        obtain ⟨i, hi, hTheta⟩ := hY
        exact ⟨i, Or.inr hi, hTheta⟩

theorem successorAlephCardSet_regulars
    (X : Set (Ordinal.{u})) :
    SetOfRegulars (successorAlephCardSet X) := by
  intro theta hTheta
  obtain ⟨i, hi, rfl⟩ := hTheta
  exact Cardinal.isRegular_aleph_add_one i

theorem successorAlephCardSet_mem_pcf
    {X : Set (Ordinal.{u})}
    {i : Ordinal.{u}}
    (hi : i ∈ X) :
    cardinalProductRepresentation.pcf (successorAlephCardSet X)
      (Cardinal.aleph (i + 1)) := by
  apply cardinalProductRepresentation_mem_pcf_of_mem
    (successorAlephCardSet_regulars X)
  exact ⟨i, hi, rfl⟩

/-! The maximum-PCF existence input in the form needed to define Jech's
    rank operator.  Empty index sets are excluded here because their PCF
    spectrum has no maximum; the total cardinal-valued operator below uses
    zero on the empty set. -/
def SuccessorAlephHasMaxPcf : Prop :=
  forall X : Set (Ordinal.{u}), X.Nonempty ->
    HasMaxPcf cardinalProductRepresentation (successorAlephCardSet X)

/-! The local maximum-existence contract actually used below a fixed rank
domain.  Unlike `SuccessorAlephHasMaxPcf`, it makes the ambient bound on the
index set explicit. -/
def SuccessorAlephHasMaxPcfBelow (theta : Ordinal.{u}) : Prop :=
  forall X : Set (Ordinal.{u}), X ⊆ Set.Iio theta -> X.Nonempty ->
    HasMaxPcf cardinalProductRepresentation (successorAlephCardSet X)

/-! Choose the actual maximum witness supplied for a nonempty successor-aleph
    index set.  The choice is canonical up to its cardinal value because
    maximum PCF values are unique. -/
noncomputable def successorAlephMaxPcfWitness
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (X : Set (Ordinal.{u}))
    (hX : X.Nonempty) :
    MaxPcfWitness cardinalProductRepresentation
      (successorAlephCardSet X) where
  theta := Classical.choose (hMax X hX)
  isMax := Classical.choose_spec (hMax X hX)

/-! The total cardinal-valued maximum-PCF operator: it is the selected
    maximum on nonempty sets and zero on the empty set.  Passing later to an
    aleph index is a separate step, so no successor-index representation is
    hidden in this definition. -/
noncomputable def successorAlephMaxPcfCardinal
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (X : Set (Ordinal.{u})) : Cardinal.{u} := by
  classical
  exact if hX : X.Nonempty then
      (successorAlephMaxPcfWitness hMax X hX).theta
    else 0

theorem successorAlephMaxPcfCardinal_eq_of_nonempty
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X : Set (Ordinal.{u})}
    (hX : X.Nonempty) :
    successorAlephMaxPcfCardinal hMax X =
      (successorAlephMaxPcfWitness hMax X hX).theta := by
  classical
  simp only [successorAlephMaxPcfCardinal, dif_pos hX]

theorem successorAlephMaxPcfCardinal_empty
    (hMax : SuccessorAlephHasMaxPcf.{u}) :
    successorAlephMaxPcfCardinal hMax (∅ : Set (Ordinal.{u})) = 0 := by
  classical
  simp [successorAlephMaxPcfCardinal]

theorem successorAlephMaxPcfCardinal_mem_pcf
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X : Set (Ordinal.{u})}
    (hX : X.Nonempty) :
    cardinalProductRepresentation.pcf (successorAlephCardSet X)
      (successorAlephMaxPcfCardinal hMax X) := by
  rw [successorAlephMaxPcfCardinal_eq_of_nonempty hMax hX]
  exact (successorAlephMaxPcfWitness hMax X hX).mem_pcf

theorem successorAlephMaxPcfCardinal_mono
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X Y : Set (Ordinal.{u})}
    (hXY : X ⊆ Y) :
    successorAlephMaxPcfCardinal hMax X <=
      successorAlephMaxPcfCardinal hMax Y := by
  by_cases hX : X.Nonempty
  · have hY : Y.Nonempty := hX.mono hXY
    rw [successorAlephMaxPcfCardinal_eq_of_nonempty hMax hX,
      successorAlephMaxPcfCardinal_eq_of_nonempty hMax hY]
    exact cardinalProductRepresentation_maxPcfWitness_mono
      (successorAlephMaxPcfWitness hMax X hX)
      (successorAlephMaxPcfWitness hMax Y hY)
      (successorAlephCardSet_mono hXY)
      (successorAlephCardSet_regulars Y)
  · rw [successorAlephMaxPcfCardinal]
    simp only [dif_neg hX]
    exact bot_le

/-! Binary unions introduce no new canonical PCF values beyond the two
    component spectra.  Consequently the maximum-PCF cardinal operator
    preserves binary maxima, including the totalized empty cases. -/
theorem successorAlephMaxPcfCardinal_union
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (X Y : Set (Ordinal.{u})) :
    successorAlephMaxPcfCardinal hMax (X ∪ Y) =
      max (successorAlephMaxPcfCardinal hMax X)
        (successorAlephMaxPcfCardinal hMax Y) := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp only [Set.empty_union, successorAlephMaxPcfCardinal_empty]
    exact (max_eq_right bot_le).symm
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp only [Set.union_empty, successorAlephMaxPcfCardinal_empty]
    exact (max_eq_left bot_le).symm
  have hUnion : (X ∪ Y).Nonempty := hX.mono Set.subset_union_left
  rw [successorAlephMaxPcfCardinal_eq_of_nonempty hMax hUnion,
    successorAlephMaxPcfCardinal_eq_of_nonempty hMax hX,
    successorAlephMaxPcfCardinal_eq_of_nonempty hMax hY]
  apply le_antisymm
  · have hMem :
        cardinalProductRepresentation.pcf
          (UnionCardSet (successorAlephCardSet X)
            (successorAlephCardSet Y))
          (successorAlephMaxPcfWitness hMax (X ∪ Y) hUnion).theta := by
      rw [← successorAlephCardSet_union]
      exact (successorAlephMaxPcfWitness hMax (X ∪ Y) hUnion).mem_pcf
    rw [
      cardinalProductRepresentation_pcf_union
        (successorAlephCardSet_regulars X)
        (successorAlephCardSet_regulars Y)] at hMem
    rcases hMem with hMem | hMem
    · exact ((successorAlephMaxPcfWitness hMax X hX).bounds hMem).trans
        (le_max_left _ _)
    · exact ((successorAlephMaxPcfWitness hMax Y hY).bounds hMem).trans
        (le_max_right _ _)
  · apply max_le
    · apply (successorAlephMaxPcfWitness hMax (X ∪ Y) hUnion).bounds
      rw [successorAlephCardSet_union,
        cardinalProductRepresentation_pcf_union
          (successorAlephCardSet_regulars X)
          (successorAlephCardSet_regulars Y)]
      exact Or.inl (successorAlephMaxPcfWitness hMax X hX).mem_pcf
    · apply (successorAlephMaxPcfWitness hMax (X ∪ Y) hUnion).bounds
      rw [successorAlephCardSet_union,
        cardinalProductRepresentation_pcf_union
          (successorAlephCardSet_regulars X)
          (successorAlephCardSet_regulars Y)]
      exact Or.inr (successorAlephMaxPcfWitness hMax Y hY).mem_pcf

theorem successorAlephMaxPcfCardinal_finsetUnion
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {α : Type v}
    (s : Finset α)
    (X : α -> Set (Ordinal.{u})) :
    successorAlephMaxPcfCardinal hMax (⋃ a ∈ s, X a) =
      s.sup (fun a => successorAlephMaxPcfCardinal hMax (X a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [successorAlephMaxPcfCardinal_empty]
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, successorAlephMaxPcfCardinal_union,
        Finset.sup_insert, ih]

theorem successorAlephCardinal_le_maxPcfCardinal
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X : Set (Ordinal.{u})}
    {i : Ordinal.{u}}
    (hi : i ∈ X) :
    Cardinal.aleph (i + 1) <= successorAlephMaxPcfCardinal hMax X := by
  have hX : X.Nonempty := ⟨i, hi⟩
  rw [successorAlephMaxPcfCardinal_eq_of_nonempty hMax hX]
  exact (successorAlephMaxPcfWitness hMax X hX).bounds
    (successorAlephCardSet_mem_pcf hi)

theorem aleph0_le_successorAlephMaxPcfCardinal
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X : Set (Ordinal.{u})}
    (hX : X.Nonempty) :
    Cardinal.aleph0 <= successorAlephMaxPcfCardinal hMax X := by
  rw [successorAlephMaxPcfCardinal_eq_of_nonempty hMax hX]
  exact (successorAlephMaxPcfWitness hMax X hX).isRegular.aleph0_le

/-! The ordinal-valued maximum-PCF index.  For nonempty `X`, this is an
    aleph index of `max pcf {aleph (i+1) | i in X}`; on the empty set it is
    zero.  We intentionally do not assert that this index is a successor,
    since that requires a separate PCF theorem. -/
noncomputable def successorAlephMaxPcfIndex
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (X : Set (Ordinal.{u})) : Ordinal.{u} := by
  classical
  exact if hX : X.Nonempty then
      Classical.choose (Cardinal.mem_range_aleph_iff.mpr
        (aleph0_le_successorAlephMaxPcfCardinal hMax hX))
    else 0

theorem successorAlephMaxPcfIndex_empty
    (hMax : SuccessorAlephHasMaxPcf.{u}) :
    successorAlephMaxPcfIndex hMax (∅ : Set (Ordinal.{u})) = 0 := by
  classical
  simp [successorAlephMaxPcfIndex]

theorem aleph_successorAlephMaxPcfIndex_eq
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X : Set (Ordinal.{u})}
    (hX : X.Nonempty) :
    Cardinal.aleph (successorAlephMaxPcfIndex hMax X) =
      successorAlephMaxPcfCardinal hMax X := by
  classical
  simp only [successorAlephMaxPcfIndex, dif_pos hX]
  exact Classical.choose_spec (Cardinal.mem_range_aleph_iff.mpr
    (aleph0_le_successorAlephMaxPcfCardinal hMax hX))

theorem successorAlephMaxPcfIndex_mono
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X Y : Set (Ordinal.{u})}
    (hXY : X ⊆ Y) :
    successorAlephMaxPcfIndex hMax X <=
      successorAlephMaxPcfIndex hMax Y := by
  by_cases hX : X.Nonempty
  · have hY : Y.Nonempty := hX.mono hXY
    apply Cardinal.aleph_le_aleph.mp
    rw [aleph_successorAlephMaxPcfIndex_eq hMax hX,
      aleph_successorAlephMaxPcfIndex_eq hMax hY]
    exact successorAlephMaxPcfCardinal_mono hMax hXY
  · rw [successorAlephMaxPcfIndex]
    simp only [dif_neg hX]
    exact bot_le

theorem successorAlephMaxPcfIndex_union
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (X Y : Set (Ordinal.{u})) :
    successorAlephMaxPcfIndex hMax (X ∪ Y) =
      max (successorAlephMaxPcfIndex hMax X)
        (successorAlephMaxPcfIndex hMax Y) := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp only [Set.empty_union, successorAlephMaxPcfIndex_empty]
    exact (max_eq_right bot_le).symm
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp only [Set.union_empty, successorAlephMaxPcfIndex_empty]
    exact (max_eq_left bot_le).symm
  have hUnion : (X ∪ Y).Nonempty := hX.mono Set.subset_union_left
  apply le_antisymm
  · apply Cardinal.aleph_le_aleph.mp
    rw [aleph_successorAlephMaxPcfIndex_eq hMax hUnion,
      Cardinal.aleph_max,
      aleph_successorAlephMaxPcfIndex_eq hMax hX,
      aleph_successorAlephMaxPcfIndex_eq hMax hY,
      successorAlephMaxPcfCardinal_union]
  · apply Cardinal.aleph_le_aleph.mp
    rw [Cardinal.aleph_max,
      aleph_successorAlephMaxPcfIndex_eq hMax hX,
      aleph_successorAlephMaxPcfIndex_eq hMax hY,
      aleph_successorAlephMaxPcfIndex_eq hMax hUnion,
      successorAlephMaxPcfCardinal_union]

theorem successorAlephMaxPcfIndex_finsetUnion
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {α : Type v}
    (s : Finset α)
    (X : α -> Set (Ordinal.{u})) :
    successorAlephMaxPcfIndex hMax (⋃ a ∈ s, X a) =
      s.sup (fun a => successorAlephMaxPcfIndex hMax (X a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [successorAlephMaxPcfIndex_empty]
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, successorAlephMaxPcfIndex_union,
        Finset.sup_insert, ih]

theorem mem_lt_successorAlephMaxPcfIndex
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X : Set (Ordinal.{u})}
    {i : Ordinal.{u}}
    (hi : i ∈ X) :
    i < successorAlephMaxPcfIndex hMax X := by
  have hX : X.Nonempty := ⟨i, hi⟩
  have hCard :
      Cardinal.aleph (i + 1) <=
        Cardinal.aleph (successorAlephMaxPcfIndex hMax X) := by
    rw [aleph_successorAlephMaxPcfIndex_eq hMax hX]
    exact successorAlephCardinal_le_maxPcfCardinal hMax hi
  have hSucc : i + 1 <= successorAlephMaxPcfIndex hMax X :=
    Cardinal.aleph_le_aleph.mp hCard
  exact (lt_add_one i).trans_le hSucc

/-! Jech's rank convention takes the ordinal predecessor of the aleph index.
    This definition is total even when the selected index is a limit; the
    equation identifying its successor aleph with the maximum is therefore
    stated below with the exact non-limit premise it needs. -/
noncomputable def successorAlephMaxPcfRank
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (X : Set (Ordinal.{u})) : Ordinal.{u} :=
  Ordinal.pred (successorAlephMaxPcfIndex hMax X)

theorem successorAlephMaxPcfRank_empty
    (hMax : SuccessorAlephHasMaxPcf.{u}) :
    successorAlephMaxPcfRank hMax (∅ : Set (Ordinal.{u})) = 0 := by
  rw [successorAlephMaxPcfRank, successorAlephMaxPcfIndex_empty]
  exact Ordinal.pred_zero

theorem successorAlephMaxPcfRank_mono
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X Y : Set (Ordinal.{u})}
    (hXY : X ⊆ Y) :
    successorAlephMaxPcfRank hMax X <=
      successorAlephMaxPcfRank hMax Y := by
  rw [successorAlephMaxPcfRank, successorAlephMaxPcfRank,
    Ordinal.pred_le_iff_le_succ]
  exact (successorAlephMaxPcfIndex_mono hMax hXY).trans
    (Ordinal.self_le_succ_pred _)

theorem successorAlephMaxPcfRank_union
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (X Y : Set (Ordinal.{u})) :
    successorAlephMaxPcfRank hMax (X ∪ Y) =
      max (successorAlephMaxPcfRank hMax X)
        (successorAlephMaxPcfRank hMax Y) := by
  rw [successorAlephMaxPcfRank, successorAlephMaxPcfIndex_union,
    successorAlephMaxPcfRank, successorAlephMaxPcfRank]
  rcases le_total (successorAlephMaxPcfIndex hMax X)
      (successorAlephMaxPcfIndex hMax Y) with hXY | hYX
  · rw [max_eq_right hXY]
    rw [max_eq_right]
    rw [Ordinal.pred_le_iff_le_succ]
    exact hXY.trans (Ordinal.self_le_succ_pred _)
  · rw [max_eq_left hYX]
    rw [max_eq_left]
    rw [Ordinal.pred_le_iff_le_succ]
    exact hYX.trans (Ordinal.self_le_succ_pred _)

theorem successorAlephMaxPcfRank_finsetUnion
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {α : Type v}
    (s : Finset α)
    (X : α -> Set (Ordinal.{u})) :
    successorAlephMaxPcfRank hMax (⋃ a ∈ s, X a) =
      s.sup (fun a => successorAlephMaxPcfRank hMax (X a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [successorAlephMaxPcfRank_empty]
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, successorAlephMaxPcfRank_union,
        Finset.sup_insert, ih]

theorem exists_mem_successorAlephMaxPcfRank_finsetUnion_eq
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {α : Type v}
    {s : Finset α}
    (hs : s.Nonempty)
    (X : α -> Set (Ordinal.{u})) :
    exists a, a ∈ s ∧
      successorAlephMaxPcfRank hMax (⋃ b ∈ s, X b) =
        successorAlephMaxPcfRank hMax (X a) := by
  rw [successorAlephMaxPcfRank_finsetUnion]
  exact Finset.exists_mem_eq_sup s hs
    (fun a => successorAlephMaxPcfRank hMax (X a))

theorem successorAlephMaxPcfRank_finsetUnion_lt_target
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {α : Type v}
    (s : Finset α)
    (X : α -> Set (Ordinal.{u}))
    (hBound : forall a, a ∈ s ->
      successorAlephMaxPcfRank hMax (X a) < targetIndexOmega4) :
    successorAlephMaxPcfRank hMax (⋃ a ∈ s, X a) <
      targetIndexOmega4 := by
  rw [successorAlephMaxPcfRank_finsetUnion]
  apply (Finset.sup_lt_iff ?_).mpr hBound
  exact (Cardinal.isSuccLimit_ord
    (Cardinal.aleph0_le_aleph (4 : Ordinal.{u}))).bot_lt

theorem mem_le_successorAlephMaxPcfRank
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X : Set (Ordinal.{u})}
    {i : Ordinal.{u}}
    (hi : i ∈ X) :
    i <= successorAlephMaxPcfRank hMax X := by
  rw [successorAlephMaxPcfRank]
  have hLt := mem_lt_successorAlephMaxPcfIndex hMax hi
  rcases
    Order.mem_range_succ_or_isSuccPrelimit
      (successorAlephMaxPcfIndex hMax X) with ⟨j, hj⟩ | hLimit
  · rw [← hj, Ordinal.pred_succ]
    rw [← hj, Order.lt_succ_iff] at hLt
    exact hLt
  · rw [hLimit.ordinalPred_eq]
    exact hLt.le

theorem aleph_successorAlephMaxPcfRank_add_one_eq
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {X : Set (Ordinal.{u})}
    (hX : X.Nonempty)
    (hIndex :
      ¬ Order.IsSuccPrelimit (successorAlephMaxPcfIndex hMax X)) :
    Cardinal.aleph (successorAlephMaxPcfRank hMax X + 1) =
      successorAlephMaxPcfCardinal hMax X := by
  rw [successorAlephMaxPcfRank, ← Order.succ_eq_add_one,
    (Ordinal.succ_pred_eq_iff_not_isSuccPrelimit.mpr hIndex),
    aleph_successorAlephMaxPcfIndex_eq hMax hX]

/-! Corollary 24.30 in the exact form consumed by Jech's rank argument:
below `theta`, every uncountable-cofinality limit `eta` has a club whose
successor-aleph PCF maximum is `aleph (eta + 1)`.  This remains a named deep
PCF input; the theorem below proves that it supplies the corresponding rank
witness without adding a successor-index assumption. -/
def SuccessorAlephClubMaxPcf
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (theta : Ordinal.{u}) : Prop :=
  forall eta, eta < theta -> Order.IsSuccLimit eta ->
    Cardinal.aleph0 < eta.cof ->
    exists C : Set (Set.Iio eta),
      IsClub C /\
        successorAlephMaxPcfCardinal hMax
            ((fun i : Set.Iio eta => i.1) '' C) =
          Cardinal.aleph (eta + 1)

/-! Jech (24.18)(ii), stated for the formal maximum-PCF rank. -/
def SuccessorAlephMaxPcfRankClubWitness
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (theta : Ordinal.{u}) : Prop :=
  forall eta, eta < theta -> Order.IsSuccLimit eta ->
    Cardinal.aleph0 < eta.cof ->
    exists C : Set (Set.Iio eta),
      IsClub C /\
        successorAlephMaxPcfRank hMax
            ((fun i : Set.Iio eta => i.1) '' C) = eta

theorem successorAlephMaxPcfRankClubWitness_of_clubMaxPcf
    (hMax : SuccessorAlephHasMaxPcf.{u})
    {theta : Ordinal.{u}}
    (hClub : SuccessorAlephClubMaxPcf hMax theta) :
    SuccessorAlephMaxPcfRankClubWitness hMax theta := by
  intro eta hEtaTheta hEtaLimit hEtaCof
  obtain ⟨C, hCClub, hCard⟩ :=
    hClub eta hEtaTheta hEtaLimit hEtaCof
  refine ⟨C, hCClub, ?_⟩
  letI : Nonempty (Set.Iio eta) :=
    ⟨⟨0, hEtaLimit.bot_lt⟩⟩
  have hCNonempty : C.Nonempty := isClub_nonempty hCClub
  have hXNonempty :
      (((fun i : Set.Iio eta => i.1) '' C) :
        Set (Ordinal.{u})).Nonempty :=
    hCNonempty.image (fun i : Set.Iio eta => i.1)
  have hIndex :
      successorAlephMaxPcfIndex hMax
          ((fun i : Set.Iio eta => i.1) '' C) = eta + 1 := by
    apply Cardinal.aleph.injective
    rw [aleph_successorAlephMaxPcfIndex_eq hMax hXNonempty,
      hCard]
  rw [successorAlephMaxPcfRank, hIndex, ← Order.succ_eq_add_one,
    Ordinal.pred_succ]

/-! The PCF Localization Lemma enters the final proof through this precise
countable-localizer output: for a set of order type `omega_1`, one countable
subset has maximum-PCF rank above every member of the original set. -/
def SuccessorAlephMaxPcfRankCountableLocalizers
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (theta : Ordinal.{u}) : Prop :=
  forall X : Set (Ordinal.{u}), X ⊆ Set.Iio theta ->
    Ordinal.type ((· < ·) : X -> X -> Prop) =
      Ordinal.omega.{u + 1} 1 ->
    exists W : Set (Ordinal.{u}),
      W ⊆ X /\ W.Countable /\
        forall x, x ∈ X ->
          x <= successorAlephMaxPcfRank hMax W

/-! The direct specialization of Jech's Localization Lemma 24.32 used in
the proof of (24.18)(iii): the maximum PCF value of a nonempty
successor-aleph set is already realized over a countable subset.  The
ambient-set cardinal arithmetic needed to prove this proposition is not
hidden here; this is its exact output at the rank-function boundary. -/
def SuccessorAlephMaxPcfLocalization
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (theta : Ordinal.{u}) : Prop :=
  forall X : Set (Ordinal.{u}), X ⊆ Set.Iio theta -> X.Nonempty ->
    exists W : Set (Ordinal.{u}),
      W ⊆ X /\ W.Countable /\
        cardinalProductRepresentation.pcf
          (successorAlephCardSet W)
          (successorAlephMaxPcfCardinal hMax X)

/-! The elementary thinning step inside Localization Lemma 24.32.  A union
of subsets of `A` has a subfamily, indexed by at most `|A|` many original
indices, which covers the same union.  The selected indices stay in the
original subtype; no PCF fact is used here. -/
theorem exists_small_subfamily_cover_iUnionCardSet
    (A Y : CardSet.{u})
    (B : CardinalIndex Y -> CardSet.{u})
    (hBA : forall y, SubsetOf (B y) A) :
    exists S : Set (CardinalIndex Y),
      Cardinal.mk S <= Cardinal.mk (CardinalIndex A) /\
        forall theta, iUnionCardSet B theta ->
          exists y, y ∈ S /\ B y theta := by
  let E : Type (u + 1) := CardinalIndex (iUnionCardSet B)
  let owner : E -> CardinalIndex Y := fun e =>
    Classical.choose e.2
  have hOwner : forall e : E, B (owner e) e.1 := by
    intro e
    exact Classical.choose_spec e.2
  let S : Set (CardinalIndex Y) := Set.range owner
  have hUnionSubset : SubsetOf (iUnionCardSet B) A := by
    intro theta hTheta
    obtain ⟨y, hy⟩ := hTheta
    exact hBA y theta hy
  have hELe : Cardinal.mk E <= Cardinal.mk (CardinalIndex A) :=
    Cardinal.mk_subtype_mono hUnionSubset
  refine ⟨S, Cardinal.mk_range_le.trans hELe, ?_⟩
  intro theta hTheta
  let e : E := ⟨theta, hTheta⟩
  exact ⟨owner e, Set.mem_range_self e, hOwner e⟩

#print axioms exists_small_subfamily_cover_iUnionCardSet

/-! The output form of Localization Lemma 24.32 for the canonical cardinal
product.  If `X` lies in `pcf A` and `lambda` lies in `pcf X`, it can be
localized to a subset whose cardinality is at most that of `A`.  The
cardinal-arithmetic hypotheses used by the theorem are deliberately not
folded into this output proposition.  The proposition is parameterized by
the fixed ambient set `A`, matching the source theorem's scope. -/
def CardinalProductPcfLocalizationOutput (A : CardSet.{u}) : Prop :=
  forall (X : CardSet.{u}) (lambda : Cardinal.{u}),
    SubsetOf X (cardinalProductRepresentation.pcf A) ->
    cardinalProductRepresentation.pcf X lambda ->
    exists W : CardSet.{u},
      SubsetOf W X /\
        Cardinal.mk (CardinalIndex W) <= Cardinal.mk (CardinalIndex A) /\
        cardinalProductRepresentation.pcf W lambda

/-! Source ingredients used in the proof of Localization Lemma 24.32.  They
separate the genuinely deep PCF theorems (maximum reduction, transitive
generators, compactness, and `pcf (pcf E) = pcf E`) from the elementary
thinning and finite-union argument proved below. -/
def CardinalProductPcfIdempotenceBelow (A : CardSet.{u}) : Prop :=
  forall E : CardSet.{u}, SubsetOf E A ->
    cardinalProductRepresentation.pcf
        (cardinalProductRepresentation.pcf E) =
      cardinalProductRepresentation.pcf E

/-! Lemma 24.24 discharges the localization proof's idempotence input once
its source smallness hypothesis is available for every subfamily used below
the ambient set. -/
theorem cardinalProductPcfIdempotenceBelow_of_spectrumSmall
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hSmall : forall E : CardSet.{u}, SubsetOf E A ->
      CardinalProductPcfSpectrumSmallBelowCoordinates E) :
    CardinalProductPcfIdempotenceBelow A := by
  intro E hEA
  exact cardinalProductRepresentation_pcf_pcf_eq_of_spectrumSmall
    E (setOfRegulars_of_subset hEA hRegulars) (hSmall E hEA)

#print axioms
  cardinalProductPcfIdempotenceBelow_of_spectrumSmall

/-! The hereditary double-power bound is a concrete sufficient condition
for the whole below-ambient idempotence interface. -/
theorem cardinalProductPcfIdempotenceBelow_of_doublePowerBelow
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hDouble : CardinalProductDoublePowerBelowCoordinates A) :
    CardinalProductPcfIdempotenceBelow A :=
  cardinalProductPcfIdempotenceBelow_of_spectrumSmall A hRegulars
    (fun _E hEA =>
      cardinalProductPcfSpectrumSmallBelowCoordinates_of_doublePower_subset
        hEA hDouble)

#print axioms
  cardinalProductPcfIdempotenceBelow_of_doublePowerBelow

/-! Under the strong-limit hypothesis one can discard finitely many initial
successor alephs so that the elementary double-power bound lies below every
remaining coordinate.  This is the tail selection used before applying the
source localization theorem. -/
theorem exists_alephSuccSet_tail_doublePowerBelow_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    exists n : Nat,
      CardinalProductDoublePowerBelowCoordinates
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) := by
  let delta : Cardinal.{u} :=
    (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Cardinal.aleph0)
  have hContinuum : (2 : Cardinal.{u}) ^ Cardinal.aleph0 <
      targetAlephOmega :=
    two_power_aleph0_lt_targetAlephOmega_of_strongLimit hStrongLimit
  have hDelta : delta < targetAlephOmega := by
    exact hStrongLimit.isStrongPrelimit hContinuum
  obtain ⟨theta, hTheta, hDeltaTheta, _hThetaTarget⟩ :=
    alephSuccSet_cofinalInAlephOmega delta hDelta
  obtain ⟨n, hThetaEq⟩ := hTheta
  refine ⟨n, ?_⟩
  intro a
  obtain ⟨m, hnm, hm⟩ := a.2
  have hThetaLtA : theta < a.1 := by
    rw [hThetaEq, hm]
    have hnmOrd : (n : Ordinal.{u}) < (m : Ordinal.{u}) := by
      simpa only [Nat.cast_lt] using hnm
    exact Cardinal.aleph_lt_aleph.mpr (by
      simpa only [Order.succ_eq_add_one] using Order.succ_lt_succ hnmOrd)
  have hDeltaA : delta < a.1 := hDeltaTheta.trans hThetaLtA
  rw [alephSuccSet_tail_cardinalIndex_mk_eq_aleph0 n]
  have hLiftDelta : Cardinal.lift.{u + 1} delta =
      (2 : Cardinal.{u + 1}) ^
        ((2 : Cardinal.{u + 1}) ^ Cardinal.aleph0) := by
    simp only [delta, Cardinal.lift_power, Cardinal.lift_ofNat,
      Cardinal.lift_aleph0]
  rw [← hLiftDelta]
  exact Cardinal.lift_lt.mpr hDeltaA

#print axioms
  exists_alephSuccSet_tail_doublePowerBelow_of_strongLimit

/-! Consequently the full below-tail PCF idempotence input used by
localization is no longer independent once that strong-limit tail is chosen. -/
theorem exists_alephSuccSet_tail_pcfIdempotenceBelow_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    exists n : Nat,
      CardinalProductPcfIdempotenceBelow
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) := by
  obtain ⟨n, hDouble⟩ :=
    exists_alephSuccSet_tail_doublePowerBelow_of_strongLimit hStrongLimit
  exact ⟨n, cardinalProductPcfIdempotenceBelow_of_doublePowerBelow
    _ (alephSuccSet_tail_alephOmegaCore n).regulars hDouble⟩

#print axioms
  exists_alephSuccSet_tail_pcfIdempotenceBelow_of_strongLimit

def CardinalProductPcfMaxReductionAt (A : CardSet.{u}) : Prop :=
  forall (X : CardSet.{u}) (lambda : Cardinal.{u}),
    SubsetOf X (cardinalProductRepresentation.pcf A) ->
    cardinalProductRepresentation.pcf X lambda ->
    exists Y : CardSet.{u},
      SubsetOf Y X /\
        IsMaxPcf cardinalProductRepresentation Y lambda

def GeneratorBaseRealization
    (A : CardSet.{u})
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf A)) : Prop :=
  forall theta, cardinalProductRepresentation.pcf A theta ->
    cardinalProductRepresentation.pcf
      (InterCardSet A (G.generator theta)) theta

def TransitiveGeneratorSystem
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A) : Prop :=
  forall {mu lambda : Cardinal.{u}}, G.generator lambda mu ->
    SubsetOf (G.generator mu) (G.generator lambda)

def GeneratorCompactCover
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A) : Prop :=
  forall W : CardSet.{u}, SubsetOf W A ->
    exists s : Finset (Cardinal.{u}),
      (forall mu, mu ∈ s ->
        cardinalProductRepresentation.pcf W mu) /\
      SubsetOf W (FinsetUnionCardSet s G.generator)

/-! A bounded family of same-universe cardinals has a small index type.
The embedding into the small cardinal interval `Iic bound` makes the
universe bookkeeping explicit. -/
theorem cardinalIndex_small_of_boundedAbove
    (A : CardSet.{u})
    (bound : Cardinal.{u})
    (hBound : forall theta, A theta -> theta <= bound) :
    Small.{u} (CardinalIndex A) := by
  let toIic : CardinalIndex A -> Set.Iic bound := fun i =>
    ⟨i.1, hBound i.1 i.2⟩
  have hInjective : Function.Injective toIic := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : Set.Iic bound => x.1) hij
  exact small_of_injective hInjective

#print axioms cardinalIndex_small_of_boundedAbove

/-! This is the canonical-product form of the concentration conclusion in
Theorem 24.25(b): when an ultrafilter product over a subfamily `W` realizes
`theta`, the corresponding generator is large in that ultrafilter.  The
explicit PCF-membership premise records that the generator belongs to the
ambient system. -/
def GeneratorCapturesCanonicalUltrafilters
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A) : Prop :=
  forall (W : CardSet.{u}) (_hWA : SubsetOf W A)
    (J : Ideal (CardinalIndex W)) (_hUltra : J.IsUltrafilterDual)
    (theta : Cardinal.{u}),
      Cardinal.IsRegular theta ->
      cardinalProductRepresentation.pcf A theta ->
      HasTrueCofinality
        (cardinalProductFrame W J)
        (cardinalScaleLength theta) ->
      J.Eventually (fun i => G.generator theta i.1)

/-! The remaining cofinality obstruction behind generator concentration:
the canonical at-most ideal at the realized true cofinality cannot be
contained in the ultrafilter-dual ideal (viewed on all cardinals). -/
def GeneratorAtMostIdealEscapesCanonicalUltrafilters
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A) : Prop :=
  forall (W : CardSet.{u}) (_hWA : SubsetOf W A)
    (J : Ideal (CardinalIndex W)) (_hUltra : J.IsUltrafilterDual)
    (theta : Cardinal.{u}),
      Cardinal.IsRegular theta ->
      cardinalProductRepresentation.pcf A theta ->
      HasTrueCofinality
        (cardinalProductFrame W J)
        (cardinalScaleLength theta) ->
      Not (Ideal.Le (G.atMostIdeal theta)
        (J.pushforward fun i => i.1))

/-! The source-directedness invariant behind Theorem 24.25(b).  On every
subfamily, restricting the semantic at-most ideal to its coordinates leaves
the product pointwise-strictly directed below the successor of the threshold.
This is the exact invariant used in the standard contradiction with a
true-cofinality witness of length `theta`. -/
def GeneratorAtMostIdealSuccessorDirected
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A) : Prop :=
  forall (W : CardSet.{u}) (_hWA : SubsetOf W A)
    (theta : Cardinal.{u}),
      cardinalProductRepresentation.pcf A theta ->
      (cardinalProductFrame W
        ((G.atMostIdeal theta).restrictAlong
          (fun i : CardinalIndex W => i.1))).PointwiseStrictDirectedBelow
            (Order.succ theta)

/-! Successor-directedness of the semantic at-most ideal forces the precise
escape statement needed for generator concentration.  If the at-most ideal
were contained in the witnessing ultrafilter ideal, its restriction to the
displayed coordinates would be contained there as well.  The resulting
`theta⁺`-directedness supplies a strict upper bound for the alleged
`theta`-scale, contradicting cofinality. -/
theorem generatorAtMostIdealEscapesCanonicalUltrafilters_of_successorDirected
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hDirected : GeneratorAtMostIdealSuccessorDirected G) :
    GeneratorAtMostIdealEscapesCanonicalUltrafilters G := by
  intro W hWA J hUltra theta _hThetaRegular hThetaPcf hTcf hLe
  let inclusion : CardinalIndex W -> Cardinal.{u} := fun i => i.1
  let K : Ideal (CardinalIndex W) :=
    (G.atMostIdeal theta).restrictAlong inclusion
  have hKLeJ : Ideal.Le K J := by
    intro S hS
    have hImageSmall : (J.pushforward inclusion).Small
        (fun gamma => exists i, inclusion i = gamma /\ S i) :=
      hLe _ hS
    exact J.subset_small hImageSmall (by
      intro i hi
      exact ⟨i, rfl, hi⟩)
  have hDirectedJ :
      (cardinalProductFrame W J).PointwiseStrictDirectedBelow
        (Order.succ theta) := by
    have hRaw :=
      (hDirected W hWA theta hThetaPcf).withLargerIdeal J hKLeJ
    simpa only [K, inclusion, ReducedProductFrame.withIdeal,
      cardinalProductFrame] using hRaw
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  have hLevelSmall :
      Cardinal.mk (cardinalScaleLength theta).Level < Order.succ theta := by
    simpa only [mk_cardinalScaleLength_level] using Order.lt_succ theta
  obtain ⟨g, hg⟩ :=
    hDirectedJ (cardinalScaleLength theta).Level hLevelSmall s.seq
  obtain ⟨alpha, hga⟩ := s.cofinal g
  have hStrict :=
    (cardinalProductFrame W J).eventuallyLt_of_eventually_pointwiseStrict
      hUltra.isProper (hg alpha)
  exact hStrict.right hga

#print axioms
  generatorAtMostIdealEscapesCanonicalUltrafilters_of_successorDirected

/-! Any set below the realized cofinality is small in the witnessing
ultrafilter.  Otherwise that ultrafilter would concentrate on the set, and
restriction of the same true-cofinality witness would put `theta` below
itself in the strict canonical ideal. -/
theorem GeneratorSystem.belowIdeal_le_pushforward_of_trueCofinality
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hRegulars : SetOfRegulars A)
    (W : CardSet.{u})
    (hWA : SubsetOf W A)
    (J : Ideal (CardinalIndex W))
    (hUltra : J.IsUltrafilterDual)
    (theta : Cardinal.{u})
    (hThetaRegular : Cardinal.IsRegular theta)
    (hTcf : HasTrueCofinality
      (cardinalProductFrame W J)
      (cardinalScaleLength theta)) :
    Ideal.Le (G.belowIdeal theta)
      (J.pushforward fun i => i.1) := by
  intro B hBelow
  change J.Small (fun i => B i.1)
  cases hUltra.small_or_compl_small (fun i => B i.1) with
  | inl hSmall => exact hSmall
  | inr hEventually =>
      have hRegularsW : SetOfRegulars W :=
        setOfRegulars_of_subset hWA hRegulars
      have hEventuallyInter :
          J.Eventually (fun i => InterCardSet W B i.1) := by
        exact J.subset_small hEventually (by
          intro i hNotInter hNotB
          exact hNotInter ⟨i.2, hNotB⟩)
      have hThetaInterW : cardinalProductRepresentation.pcf
          (InterCardSet W B) theta :=
        cardinalProductRepresentation_mem_pcf_of_eventually_mem
          (A := InterCardSet W B) (B := W)
          (fun gamma hGamma => hGamma.1)
          hRegularsW hThetaRegular J hUltra hTcf hEventuallyInter
      have hInterSubset :
          SubsetOf (InterCardSet W B) (InterCardSet A B) := by
        intro gamma hGamma
        exact ⟨hWA gamma hGamma.1, hGamma.2⟩
      have hThetaInterA : cardinalProductRepresentation.pcf
          (InterCardSet A B) theta :=
        cardinalProductRepresentation_pcf_mono
          hInterSubset
          (fun gamma hGamma => hRegulars gamma hGamma.1)
          theta hThetaInterW
      exact False.elim ((G.belowIdeal_small_iff theta B).mp
        hBelow theta hThetaInterA |>.false)

#print axioms
  GeneratorSystem.belowIdeal_le_pushforward_of_trueCofinality

/-! The generator-equivalence axiom now turns the isolated at-most-ideal
obstruction into Theorem 24.25(b)'s ultrafilter concentration conclusion.
The strict-below part is discharged by the preceding theorem. -/
theorem generatorCapturesCanonicalUltrafilters_of_atMostIdealEscape
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hEscape : GeneratorAtMostIdealEscapesCanonicalUltrafilters G) :
    GeneratorCapturesCanonicalUltrafilters G := by
  intro W hWA J hUltra theta hThetaRegular hThetaPcf hTcf
  have hBelowLe : Ideal.Le (G.belowIdeal theta)
      (J.pushforward fun i => i.1) :=
    G.belowIdeal_le_pushforward_of_trueCofinality
      hRegulars W hWA J hUltra theta hThetaRegular hTcf
  by_contra hNotEventually
  have hGeneratorSmall :
      (J.pushforward fun i => i.1).Small (G.generator theta) := by
    change J.Small (fun i => G.generator theta i.1)
    exact (hUltra.small_iff_not_eventually
      (fun i => G.generator theta i.1)).mpr hNotEventually
  apply hEscape W hWA J hUltra theta hThetaRegular hThetaPcf hTcf
  intro B hAtMost
  obtain ⟨T, hTBelow, hCover⟩ :=
    G.atMost_le_generated hThetaPcf B hAtMost
  exact (J.pushforward fun i => i.1).subset_small
    ((J.pushforward fun i => i.1).union_small
      (hBelowLe T hTBelow) hGeneratorSmall)
    hCover

#print axioms
  generatorCapturesCanonicalUltrafilters_of_atMostIdealEscape

/-! Generator concentration also supplies the base-realization clause used
in Localization.  Unpack a witness for `theta in pcf A`, view `A` inside
`pcf A`, apply capture, and restrict the same ultrafilter witness to the
intersection with the `theta`-generator. -/
theorem generatorBaseRealization_of_canonicalUltrafilterCapture
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf A))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G) :
    GeneratorBaseRealization A G := by
  intro theta hThetaPcfA
  obtain ⟨hThetaRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := A) (theta := theta)).mp hThetaPcfA
  have hAPcfA : SubsetOf A
      (cardinalProductRepresentation.pcf A) := by
    intro gamma hGamma
    exact cardinalProductRepresentation_mem_pcf_of_mem hRegulars hGamma
  have hThetaPcfPcfA : cardinalProductRepresentation.pcf
      (cardinalProductRepresentation.pcf A) theta :=
    cardinalProductRepresentation_pcf_mono
      hAPcfA
      (cardinalProductRepresentation.pcf_is_setOfRegulars A)
      theta hThetaPcfA
  have hEventuallyGenerator :
      J.Eventually (fun i => G.generator theta i.1) :=
    hCapture A hAPcfA J hUltra theta hThetaRegular
      hThetaPcfPcfA hTcf
  have hEventuallyInter :
      J.Eventually (fun i => InterCardSet A (G.generator theta) i.1) := by
    exact J.eventually_mono hEventuallyGenerator (by
      intro i hGenerator
      exact ⟨i.2, hGenerator⟩)
  exact cardinalProductRepresentation_mem_pcf_of_eventually_mem
    (A := InterCardSet A (G.generator theta)) (B := A)
    (fun gamma hGamma => hGamma.1)
    hRegulars hThetaRegular J hUltra hTcf hEventuallyInter

#print axioms
  generatorBaseRealization_of_canonicalUltrafilterCapture

/-! The same concentration theorem supplies the preliminary maximum
reduction used by Localization.  For `lambda in pcf X`, intersect `X` with
the `lambda`-generator.  Restriction preserves the displayed witness for
`lambda`, while the generator's canonical at-most property bounds every PCF
value of the intersection by `lambda`. -/
theorem cardinalProductPcfMaxReductionAt_of_canonicalUltrafilterCapture
    (A : CardSet.{u})
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf A))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G) :
    CardinalProductPcfMaxReductionAt A := by
  intro X lambda hXA hLambdaX
  obtain ⟨hLambdaRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := X) (theta := lambda)).mp hLambdaX
  have hRegularsX : SetOfRegulars X :=
    setOfRegulars_of_subset hXA
      (cardinalProductRepresentation.pcf_is_setOfRegulars A)
  have hLambdaPcfPcfA : cardinalProductRepresentation.pcf
      (cardinalProductRepresentation.pcf A) lambda :=
    cardinalProductRepresentation_pcf_mono
      hXA (cardinalProductRepresentation.pcf_is_setOfRegulars A)
      lambda hLambdaX
  have hEventuallyGenerator :
      J.Eventually (fun i => G.generator lambda i.1) :=
    hCapture X hXA J hUltra lambda hLambdaRegular
      hLambdaPcfPcfA hTcf
  let Y : CardSet.{u} := InterCardSet X (G.generator lambda)
  have hYX : SubsetOf Y X := fun gamma hGamma => hGamma.1
  have hEventuallyY : J.Eventually (fun i => Y i.1) := by
    exact J.eventually_mono hEventuallyGenerator (by
      intro i hGenerator
      exact ⟨i.2, hGenerator⟩)
  have hLambdaY : cardinalProductRepresentation.pcf Y lambda :=
    cardinalProductRepresentation_mem_pcf_of_eventually_mem
      (A := Y) (B := X) hYX hRegularsX hLambdaRegular
      J hUltra hTcf hEventuallyY
  refine ⟨Y, hYX, hLambdaY, ?_⟩
  intro beta hBetaY
  have hGeneratorSubset : SubsetOf (G.generator lambda)
      (cardinalProductRepresentation.pcf A) :=
    G.subset_of_mem_pcf hLambdaPcfPcfA
  have hGeneratorRegulars : SetOfRegulars (G.generator lambda) :=
    setOfRegulars_of_subset hGeneratorSubset
      (cardinalProductRepresentation.pcf_is_setOfRegulars A)
  have hBetaGenerator : cardinalProductRepresentation.pcf
      (G.generator lambda) beta :=
    cardinalProductRepresentation_pcf_mono
      (fun gamma hGamma => hGamma.2)
      hGeneratorRegulars beta hBetaY
  have hInterEq : InterCardSet
      (cardinalProductRepresentation.pcf A)
      (G.generator lambda) = G.generator lambda := by
    funext gamma
    apply propext
    constructor
    · exact fun hGamma => hGamma.2
    · intro hGamma
      exact ⟨hGeneratorSubset gamma hGamma, hGamma⟩
  apply G.generator_pcf_le hLambdaPcfPcfA
  rw [hInterEq]
  exact hBetaGenerator

#print axioms
  cardinalProductPcfMaxReductionAt_of_canonicalUltrafilterCapture

/-! Jech Corollary 24.29 in canonical-product form.  If no finite collection
of generators covers `W`, the complements of all relevant generators have
the finite-intersection property.  The ultrafilter lemma then supplies one
ultrafilter avoiding every such generator.  Its canonical true cofinality is
a member of `pcf W`, while generator concentration says that its own
generator is large in the same ultrafilter, a contradiction. -/
theorem generatorCompactCover_of_canonicalUltrafilterCapture
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hAleph0 : forall theta, A theta -> Cardinal.aleph0 < theta)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hCapture : GeneratorCapturesCanonicalUltrafilters G) :
    GeneratorCompactCover G := by
  classical
  intro W hWA
  let toA : CardinalIndex W -> CardinalIndex A := fun i =>
    ⟨i.1, hWA i.1 i.2⟩
  have hToAInjective : Function.Injective toA := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : CardinalIndex A => x.1) hij
  letI : Small.{u} (CardinalIndex A) := hSmall
  have hSmallW : Small.{u} (CardinalIndex W) :=
    small_of_injective hToAInjective
  have hRegularsW : SetOfRegulars W :=
    setOfRegulars_of_subset hWA hRegulars
  have hAleph0W : forall theta, W theta -> Cardinal.aleph0 < theta :=
    fun theta hTheta => hAleph0 theta (hWA theta hTheta)
  let K := CardinalIndex (cardinalProductRepresentation.pcf W)
  let P : K -> CardinalIndex W -> Prop := fun mu i =>
    G.generator mu.1 i.1
  by_contra hNoCover
  have hCompatible : forall s : Finset K,
      ((Ideal.emptyOnly (CardinalIndex W)).extendBy
        (finitePredicateUnion P s)).IsProper := by
    intro s
    rw [Ideal.extendBy_isProper_iff_not_eventually]
    intro hEventually
    have hCoverIndex : forall i : CardinalIndex W,
        finitePredicateUnion P s i := by
      intro i
      by_contra hi
      exact hEventually i hi
    let t : Finset (Cardinal.{u}) := s.image fun mu => mu.1
    have hTPcf : forall mu, mu ∈ t ->
        cardinalProductRepresentation.pcf W mu := by
      intro mu hMu
      obtain ⟨nu, hNuS, hNu⟩ := Finset.mem_image.mp hMu
      simpa only [hNu] using nu.2
    have hTCover : SubsetOf W (FinsetUnionCardSet t G.generator) := by
      intro theta hTheta
      let i : CardinalIndex W := ⟨theta, hTheta⟩
      obtain ⟨mu, hMuS, hGenerator⟩ := hCoverIndex i
      exact ⟨mu.1, Finset.mem_image.mpr ⟨mu, hMuS, rfl⟩,
        hGenerator⟩
    exact hNoCover ⟨t, hTPcf, hTCover⟩
  obtain ⟨J, hUltra, _hLe, hAvoid⟩ :=
    exists_ultrafilterDual_ideal_avoiding_eventual_family
      (Ideal.emptyOnly (CardinalIndex W)) P hCompatible
  obtain ⟨theta, hThetaRegular, hTcf, _hThetaAleph0⟩ :=
    cardinalProductFrame_exists_trueCofinality_of_small_cardinalIndex_of_aleph0_lt
      hRegularsW hUltra hSmallW hAleph0W
  have hThetaPcfW : cardinalProductRepresentation.pcf W theta :=
    cardinalProductRepresentation_mem_pcf_iff.mpr
      ⟨hThetaRegular, J, hUltra, hTcf⟩
  have hThetaPcfA : cardinalProductRepresentation.pcf A theta :=
    cardinalProductRepresentation_pcf_mono
      hWA hRegulars theta hThetaPcfW
  have hEventually : J.Eventually (fun i => G.generator theta i.1) :=
    hCapture W hWA J hUltra theta hThetaRegular hThetaPcfA hTcf
  exact hAvoid ⟨theta, hThetaPcfW⟩ hEventually

#print axioms generatorCompactCover_of_canonicalUltrafilterCapture

/-! A finite generator cover already yields a maximum PCF value for every
nonempty subfamily of the ambient generator domain.  Choose the largest
index in the finite cover.  Its membership in `pcf W` gives the lower half
of maximality; finite-union PCF and the generator bound give the upper half. -/
theorem cardinalProductRepresentation_hasMaxPcf_of_generatorCompactCover
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hCompact : GeneratorCompactCover G)
    (W : CardSet.{u})
    (hWA : SubsetOf W A)
    (hWNonempty : exists theta, W theta) :
    HasMaxPcf cardinalProductRepresentation W := by
  classical
  obtain ⟨s, hSupportPcf, hCover⟩ := hCompact W hWA
  have hSNonempty : s.Nonempty := by
    obtain ⟨theta, hThetaW⟩ := hWNonempty
    obtain ⟨mu, hMuS, _hThetaGenerator⟩ := hCover theta hThetaW
    exact ⟨mu, hMuS⟩
  let lambda : Cardinal.{u} := s.max' hSNonempty
  have hLambdaS : lambda ∈ s := Finset.max'_mem s hSNonempty
  refine ⟨lambda, hSupportPcf lambda hLambdaS, ?_⟩
  intro beta hBetaW
  let Gen : Cardinal.{u} -> CardSet.{u} := fun mu =>
    if mu ∈ s then G.generator mu else emptyCardSet
  have hGenRegulars : forall mu, SetOfRegulars (Gen mu) := by
    intro mu gamma hGamma
    by_cases hMuS : mu ∈ s
    · have hMuPcfA : cardinalProductRepresentation.pcf A mu :=
        cardinalProductRepresentation_pcf_mono
          hWA hRegulars mu (hSupportPcf mu hMuS)
      exact hRegulars gamma (G.subset_of_mem_pcf hMuPcfA gamma (by
        simpa [Gen, hMuS] using hGamma))
    · simp [Gen, hMuS, emptyCardSet] at hGamma
  have hUnionEq : FinsetUnionCardSet s Gen =
      FinsetUnionCardSet s G.generator := by
    funext gamma
    apply propext
    constructor
    · rintro ⟨mu, hMuS, hGamma⟩
      exact ⟨mu, hMuS, by simpa [Gen, hMuS] using hGamma⟩
    · rintro ⟨mu, hMuS, hGamma⟩
      exact ⟨mu, hMuS, by simpa [Gen, hMuS] using hGamma⟩
  have hBetaUnion : cardinalProductRepresentation.pcf
      (FinsetUnionCardSet s Gen) beta := by
    apply cardinalProductRepresentation_pcf_mono
      (B := FinsetUnionCardSet s Gen)
      (A := W)
      (by
        intro gamma hGammaW
        rw [hUnionEq]
        exact hCover gamma hGammaW)
      (finsetUnionCardSet_regulars hGenRegulars)
      beta hBetaW
  rw [cardinalProductRepresentation_pcf_finsetUnion
    s Gen hGenRegulars] at hBetaUnion
  obtain ⟨mu, hMuS, hBetaGenerator⟩ := hBetaUnion
  have hMuPcfA : cardinalProductRepresentation.pcf A mu :=
    cardinalProductRepresentation_pcf_mono
      hWA hRegulars mu (hSupportPcf mu hMuS)
  have hInterEq : InterCardSet A (G.generator mu) =
      G.generator mu := by
    funext gamma
    apply propext
    constructor
    · exact fun hGamma => hGamma.2
    · intro hGamma
      exact ⟨G.subset_of_mem_pcf hMuPcfA gamma hGamma, hGamma⟩
  have hBetaLeMu : beta <= mu := by
    apply G.generator_pcf_le hMuPcfA
    rw [hInterEq]
    simpa [Gen, hMuS] using hBetaGenerator
  exact hBetaLeMu.trans (by
    simpa [lambda] using Finset.le_max' s mu hMuS)

#print axioms
  cardinalProductRepresentation_hasMaxPcf_of_generatorCompactCover

/-! The preceding theorem gives an actual maximum witness for the fixed
successor-aleph core once generators on its PCF spectrum have the compact
cover property. -/
noncomputable def alephSuccSetMaxPcfWitnessOfGeneratorCompactCover
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCompact : GeneratorCompactCover G) :
    MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u} := by
  have hCoreSubset : SubsetOf alephSuccSet.{u}
      (cardinalProductRepresentation.pcf alephSuccSet.{u}) := by
    intro theta hTheta
    exact cardinalProductRepresentation_mem_pcf_of_mem
      alephSuccSet_regulars hTheta
  have hHasMax : HasMaxPcf cardinalProductRepresentation
      alephSuccSet.{u} :=
    cardinalProductRepresentation_hasMaxPcf_of_generatorCompactCover
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
      G hCompact alephSuccSet hCoreSubset
      ⟨Cardinal.aleph ((0 : Ordinal.{u}) + 1), ⟨0, rfl⟩⟩
  exact ⟨Classical.choose hHasMax, Classical.choose_spec hHasMax⟩

theorem alephSuccSetMaxPcfWitnessOfGeneratorCompactCover_mem_pcf
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCompact : GeneratorCompactCover G) :
    cardinalProductRepresentation.pcf alephSuccSet.{u}
      (alephSuccSetMaxPcfWitnessOfGeneratorCompactCover G hCompact).theta :=
  (alephSuccSetMaxPcfWitnessOfGeneratorCompactCover G hCompact).mem_pcf

#print axioms
  alephSuccSetMaxPcfWitnessOfGeneratorCompactCover_mem_pcf

/-! Consequently, generator compactness on the PCF spectrum of the fixed
core proves maximum existence for every successor-aleph family lying below
an ambient PCF rank domain.  This is the local maximum premise used by the
rank argument, not a claim about arbitrary ordinal index sets. -/
theorem successorAlephHasMaxPcfBelow_of_generatorCompactCover
    {theta : Ordinal.{u}}
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCompact : GeneratorCompactCover G)
    (hCore : forall i, i < theta ->
      cardinalProductRepresentation.pcf alephSuccSet.{u}
        (Cardinal.aleph (i + 1))) :
    SuccessorAlephHasMaxPcfBelow theta := by
  intro X hXTheta hXNonempty
  apply cardinalProductRepresentation_hasMaxPcf_of_generatorCompactCover
    (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
    G hCompact (successorAlephCardSet X)
  · intro gamma hGamma
    obtain ⟨i, hiX, rfl⟩ := hGamma
    exact hCore i (hXTheta hiX)
  · obtain ⟨i, hiX⟩ := hXNonempty
    exact ⟨Cardinal.aleph (i + 1), ⟨i, hiX, rfl⟩⟩

#print axioms successorAlephHasMaxPcfBelow_of_generatorCompactCover

/-! The source proof of Localization Lemma 24.32, after its four hard PCF
inputs have been exposed.  The proof constructs the union `E` of base
pieces, thins it to at most `|A|` many indices, and uses compactness plus
transitivity to rule out failure of localization. -/
theorem cardinalProductPcfLocalizationOutput_of_transitiveGenerators
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hIdempotent : CardinalProductPcfIdempotenceBelow A)
    (hReduction : CardinalProductPcfMaxReductionAt A)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf A))
    (hBase : GeneratorBaseRealization A G)
    (hTransitive : TransitiveGeneratorSystem G)
    (hCompact : GeneratorCompactCover G) :
    CardinalProductPcfLocalizationOutput A := by
  intro X lambda hXA hLambdaX
  obtain ⟨Y, hYX, hLambdaMax⟩ :=
    hReduction X lambda hXA hLambdaX
  let B : CardinalIndex Y -> CardSet.{u} := fun y =>
    InterCardSet A (G.generator y.1)
  let E : CardSet.{u} := iUnionCardSet B
  have hBSubset : forall y, SubsetOf (B y) A := by
    intro y theta hTheta
    exact hTheta.1
  obtain ⟨S, hSSize, hSCover⟩ :=
    exists_small_subfamily_cover_iUnionCardSet A Y B hBSubset
  let W : CardSet.{u} := fun theta =>
    exists y : S, theta = y.1.1
  have hWY : SubsetOf W Y := by
    intro theta hTheta
    obtain ⟨y, rfl⟩ := hTheta
    exact y.1.2
  have hWX : SubsetOf W X := fun theta hTheta =>
    hYX theta (hWY theta hTheta)
  let toW : S -> CardinalIndex W := fun y =>
    ⟨y.1.1, ⟨y, rfl⟩⟩
  have hToWSurjective : Function.Surjective toW := by
    rintro ⟨theta, y, hTheta⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hTheta.symm
  have hWSize :
      Cardinal.mk (CardinalIndex W) <= Cardinal.mk (CardinalIndex A) :=
    (Cardinal.mk_le_of_surjective hToWSurjective).trans hSSize
  have hESubsetA : SubsetOf E A := by
    intro theta hTheta
    obtain ⟨y, hy⟩ := hTheta
    exact hy.1
  have hERegulars : SetOfRegulars E :=
    setOfRegulars_of_subset hESubsetA hRegulars
  have hYSubsetPcfE :
      SubsetOf Y (cardinalProductRepresentation.pcf E) := by
    intro nu hNuY
    let y : CardinalIndex Y := ⟨nu, hNuY⟩
    have hNuA : cardinalProductRepresentation.pcf A nu :=
      hXA nu (hYX nu hNuY)
    have hNuB : cardinalProductRepresentation.pcf (B y) nu :=
      hBase nu hNuA
    have hBE : SubsetOf (B y) E := by
      intro theta hTheta
      exact ⟨y, hTheta⟩
    exact cardinalProductRepresentation_pcf_mono
      hBE hERegulars nu hNuB
  have hLambdaPcfPcfE :
      cardinalProductRepresentation.pcf
        (cardinalProductRepresentation.pcf E) lambda :=
    cardinalProductRepresentation_pcf_mono
      hYSubsetPcfE
      (cardinalProductRepresentation.pcf_is_setOfRegulars E)
      lambda hLambdaMax.1
  have hLambdaE : cardinalProductRepresentation.pcf E lambda := by
    rw [hIdempotent E hESubsetA] at hLambdaPcfPcfE
    exact hLambdaPcfPcfE
  refine ⟨W, hWX, hWSize, ?_⟩
  by_contra hLambdaW
  have hWSubsetPcfA :
      SubsetOf W (cardinalProductRepresentation.pcf A) :=
    fun theta hTheta => hXA theta (hWX theta hTheta)
  obtain ⟨s, hSupportPcf, hWCover⟩ :=
    hCompact W hWSubsetPcfA
  have hSupportLt : forall mu, mu ∈ s -> mu < lambda := by
    intro mu hMuS
    have hMuW : cardinalProductRepresentation.pcf W mu :=
      hSupportPcf mu hMuS
    have hYRegulars : SetOfRegulars Y :=
      setOfRegulars_of_subset
        (fun theta hTheta => hXA theta (hYX theta hTheta))
        (cardinalProductRepresentation.pcf_is_setOfRegulars A)
    have hMuY : cardinalProductRepresentation.pcf Y mu :=
      cardinalProductRepresentation_pcf_mono
        hWY hYRegulars mu hMuW
    have hMuLe : mu <= lambda := hLambdaMax.2 mu hMuY
    exact lt_of_le_of_ne hMuLe (fun hEq => hLambdaW (hEq ▸ hMuW))
  have hEFiniteUnion :
      SubsetOf E (FinsetUnionCardSet s G.generator) := by
    intro theta hTheta
    obtain ⟨y, hyS, hThetaB⟩ := hSCover theta hTheta
    have hYW : W y.1 := ⟨⟨y, hyS⟩, rfl⟩
    obtain ⟨mu, hMuS, hGenMuY⟩ := hWCover y.1 hYW
    exact ⟨mu, hMuS,
      hTransitive hGenMuY theta hThetaB.2⟩
  have hFiniteUnionRegulars :
      SetOfRegulars (FinsetUnionCardSet s G.generator) := by
    intro theta hTheta
    obtain ⟨mu, hMuS, hGen⟩ := hTheta
    have hMuPcfPcfA :
        cardinalProductRepresentation.pcf
          (cardinalProductRepresentation.pcf A) mu :=
      cardinalProductRepresentation_pcf_mono
        hWSubsetPcfA
        (cardinalProductRepresentation.pcf_is_setOfRegulars A)
        mu (hSupportPcf mu hMuS)
    exact (cardinalProductRepresentation.pcf_is_setOfRegulars A)
      theta (G.subset_of_mem_pcf hMuPcfPcfA theta hGen)
  have hLambdaFiniteUnion :
      cardinalProductRepresentation.pcf
        (FinsetUnionCardSet s G.generator) lambda :=
    cardinalProductRepresentation_pcf_mono
      hEFiniteUnion hFiniteUnionRegulars lambda hLambdaE
  let Gen : Cardinal.{u} -> CardSet.{u} := fun mu =>
    if mu ∈ s then G.generator mu else emptyCardSet
  have hGenRegulars : forall mu, SetOfRegulars (Gen mu) := by
    intro mu theta hTheta
    by_cases hMuS : mu ∈ s
    · have hMuPcfPcfA :
          cardinalProductRepresentation.pcf
            (cardinalProductRepresentation.pcf A) mu :=
        cardinalProductRepresentation_pcf_mono
          hWSubsetPcfA
          (cardinalProductRepresentation.pcf_is_setOfRegulars A)
          mu (hSupportPcf mu hMuS)
      exact (cardinalProductRepresentation.pcf_is_setOfRegulars A)
        theta (G.subset_of_mem_pcf hMuPcfPcfA theta (by
          simpa [Gen, hMuS] using hTheta))
    · simp [Gen, hMuS, emptyCardSet] at hTheta
  have hUnionEq :
      FinsetUnionCardSet s Gen = FinsetUnionCardSet s G.generator := by
    funext theta
    apply propext
    constructor
    · rintro ⟨mu, hMuS, hTheta⟩
      exact ⟨mu, hMuS, by simpa [Gen, hMuS] using hTheta⟩
    · rintro ⟨mu, hMuS, hTheta⟩
      exact ⟨mu, hMuS, by simpa [Gen, hMuS] using hTheta⟩
  rw [← hUnionEq,
    cardinalProductRepresentation_pcf_finsetUnion s Gen hGenRegulars]
      at hLambdaFiniteUnion
  obtain ⟨mu, hMuS, hLambdaGen⟩ := hLambdaFiniteUnion
  have hMuW : cardinalProductRepresentation.pcf W mu :=
    hSupportPcf mu hMuS
  have hMuPcfPcfA :
      cardinalProductRepresentation.pcf
        (cardinalProductRepresentation.pcf A) mu :=
    cardinalProductRepresentation_pcf_mono
      hWSubsetPcfA
      (cardinalProductRepresentation.pcf_is_setOfRegulars A)
      mu hMuW
  have hInterEq :
      InterCardSet (cardinalProductRepresentation.pcf A)
          (G.generator mu) =
        G.generator mu := by
    funext theta
    apply propext
    constructor
    · exact fun hTheta => hTheta.2
    · intro hTheta
      exact ⟨G.subset_of_mem_pcf hMuPcfPcfA theta hTheta, hTheta⟩
  have hLambdaInter :
      cardinalProductRepresentation.pcf
        (InterCardSet (cardinalProductRepresentation.pcf A)
          (G.generator mu)) lambda := by
    rw [hInterEq]
    simpa [Gen, hMuS] using hLambdaGen
  have hLambdaLeMu : lambda <= mu :=
    G.generator_pcf_le hMuPcfPcfA hLambdaInter
  exact (not_le_of_gt (hSupportLt mu hMuS)) hLambdaLeMu

#print axioms
  cardinalProductPcfLocalizationOutput_of_transitiveGenerators

/-! The preceding compactness theorem can be fed directly into the source
proof of Localization Lemma 24.32.  Thus compact cover is no longer an
independent premise: it is derived from smallness, uncountability of the
ambient coordinates, and the Theorem 24.25(b)-style concentration input. -/
theorem cardinalProductPcfLocalizationOutput_of_ultrafilterGenerators
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hIdempotent : CardinalProductPcfIdempotenceBelow A)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf A))
    (hTransitive : TransitiveGeneratorSystem G)
    (hPcfSmall : Small.{u} (CardinalIndex
      (cardinalProductRepresentation.pcf A)))
    (hPcfAleph0 : forall theta,
      cardinalProductRepresentation.pcf A theta ->
        Cardinal.aleph0 < theta)
    (hCapture : GeneratorCapturesCanonicalUltrafilters G) :
    CardinalProductPcfLocalizationOutput A :=
  cardinalProductPcfLocalizationOutput_of_transitiveGenerators
    A hRegulars hIdempotent
    (cardinalProductPcfMaxReductionAt_of_canonicalUltrafilterCapture
      A G hCapture)
    G
    (generatorBaseRealization_of_canonicalUltrafilterCapture
      A hRegulars G hCapture)
    hTransitive
    (generatorCompactCover_of_canonicalUltrafilterCapture
      (cardinalProductRepresentation.pcf_is_setOfRegulars A)
      hPcfSmall hPcfAleph0 G hCapture)

#print axioms
  cardinalProductPcfLocalizationOutput_of_ultrafilterGenerators

/-! The elementary hereditary double-power bound is enough to run the
ultrafilter-generator localization route: Lemma 24.24 supplies the only
idempotence input used by the proof. -/
theorem cardinalProductPcfLocalizationOutput_of_ultrafilterGenerators_of_doublePowerBelow
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (hDouble : CardinalProductDoublePowerBelowCoordinates A)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf A))
    (hTransitive : TransitiveGeneratorSystem G)
    (hPcfSmall : Small.{u} (CardinalIndex
      (cardinalProductRepresentation.pcf A)))
    (hPcfAleph0 : forall theta,
      cardinalProductRepresentation.pcf A theta ->
        Cardinal.aleph0 < theta)
    (hCapture : GeneratorCapturesCanonicalUltrafilters G) :
    CardinalProductPcfLocalizationOutput A :=
  cardinalProductPcfLocalizationOutput_of_ultrafilterGenerators
    A hRegulars
    (cardinalProductPcfIdempotenceBelow_of_doublePowerBelow
      A hRegulars hDouble)
    G hTransitive hPcfSmall hPcfAleph0 hCapture

#print axioms
  cardinalProductPcfLocalizationOutput_of_ultrafilterGenerators_of_doublePowerBelow

/-! The canonical PCF spectrum of the countable successor-aleph core is a
small type.  Every member is bounded by the already proved countable-product
cardinal, and bounded families of same-universe cardinals are small. -/
theorem alephSuccSet_pcf_cardinalIndex_small :
    Small.{u} (CardinalIndex
      (cardinalProductRepresentation.pcf alephSuccSet.{u})) := by
  apply cardinalIndex_small_of_boundedAbove
    (cardinalProductRepresentation.pcf alephSuccSet.{u})
    (targetAlephOmega.{u} ^ Cardinal.aleph0)
  intro theta hTheta
  apply Cardinal.lift_le.mp
  obtain ⟨J, hUltra, hBound⟩ :=
    alephSuccSet_pcf_theta_le_alephOmega_power_aleph0 hTheta
  simpa only [Cardinal.lift_power, Cardinal.lift_aleph0] using hBound

#print axioms alephSuccSet_pcf_cardinalIndex_small

/-! Every finite tail of the successor-aleph core has a small canonical PCF
spectrum.  The proof is the full-core boundedness argument with the exact
tail product estimate. -/
theorem alephSuccSet_tail_pcf_cardinalIndex_small (n : Nat) :
    Small.{u} (CardinalIndex
      (cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n))) := by
  apply cardinalIndex_small_of_boundedAbove
    (cardinalProductRepresentation.pcf
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n))
    (targetAlephOmega.{u} ^ Cardinal.aleph0)
  intro theta hTheta
  apply Cardinal.lift_le.mp
  obtain ⟨J, hUltra, hBound⟩ :=
    alephSuccSet_tail_pcf_theta_le_alephOmega_power_aleph0 n hTheta
  simpa only [Cardinal.lift_power, Cardinal.lift_aleph0] using hBound

#print axioms alephSuccSet_tail_pcf_cardinalIndex_small

/-! Tail-specialized localization with the source smallness condition made
explicit.  Together with the strong-limit tail-selection theorem above,
this removes the old full-core idempotence premise from the source route. -/
theorem alephSuccSet_tail_cardinalProductPcfLocalizationOutput_of_doublePowerBelow
    (n : Nat)
    (hDouble : CardinalProductDoublePowerBelowCoordinates
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n))
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)))
    (hTransitive : TransitiveGeneratorSystem G)
    (hCapture : GeneratorCapturesCanonicalUltrafilters G) :
    CardinalProductPcfLocalizationOutput
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) :=
  cardinalProductPcfLocalizationOutput_of_ultrafilterGenerators_of_doublePowerBelow
    _ (alephSuccSet_tail_alephOmegaCore n).regulars hDouble
    G hTransitive (alephSuccSet_tail_pcf_cardinalIndex_small n)
    (fun _ hPcf => alephSuccSet_tail_pcf_mem_gt_aleph0 n hPcf)
    hCapture

#print axioms
  alephSuccSet_tail_cardinalProductPcfLocalizationOutput_of_doublePowerBelow

/-! Localization on one strict successor-aleph tail extends to the full
core.  The omitted prefix is finite, and canonical PCF turns the full core
into the union of the prefix spectrum and the tail spectrum; a PCF witness
therefore lies on one side of that finite split. -/
theorem alephSuccSet_cardinalProductPcfLocalizationOutput_of_tail
    (n : Nat)
    (hTailLocalization : CardinalProductPcfLocalizationOutput
      (natTailIUnionCardSet
        (fun m : Nat =>
          singletonCardSet
            (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)) :
    CardinalProductPcfLocalizationOutput alephSuccSet.{u} := by
  let A : Nat -> CardSet.{u} := fun m =>
    singletonCardSet (Cardinal.aleph ((m : Ordinal.{u}) + 1))
  let P : CardSet.{u} := natPrefixIUnionCardSet A n
  let T : CardSet.{u} := natTailIUnionCardSet A n
  have hRegularsA : forall m, SetOfRegulars (A m) := by
    intro m theta hTheta
    change theta = Cardinal.aleph ((m : Ordinal.{u}) + 1) at hTheta
    rw [hTheta]
    exact Cardinal.isRegular_aleph_add_one (m : Ordinal.{u})
  have hRegularsP : SetOfRegulars P := by
    rw [show P = natPrefixIUnionCardSet A n from rfl,
      natPrefixIUnionCardSet_eq_finsetUnion_range]
    exact finsetUnionCardSet_regulars hRegularsA
  have hRegularsT : SetOfRegulars T := by
    exact natTailIUnionCardSet_setOfRegulars A hRegularsA n
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
  intro X lambda hXFull hLambdaX
  let XP : CardSet.{u} :=
    InterCardSet X (cardinalProductRepresentation.pcf P)
  let XT : CardSet.{u} :=
    InterCardSet X (cardinalProductRepresentation.pcf T)
  have hXEq : X = UnionCardSet XP XT := by
    funext theta
    apply propext
    constructor
    · intro hThetaX
      have hThetaSplit := hXFull theta hThetaX
      rw [hPcfSplit] at hThetaSplit
      exact hThetaSplit.elim
        (fun hThetaP => Or.inl ⟨hThetaX, hThetaP⟩)
        (fun hThetaT => Or.inr ⟨hThetaX, hThetaT⟩)
    · intro hTheta
      exact hTheta.elim (fun h => h.1) (fun h => h.1)
  have hRegularsXP : SetOfRegulars XP :=
    setOfRegulars_of_subset
      (fun theta hTheta => hXFull theta hTheta.1)
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
  have hRegularsXT : SetOfRegulars XT :=
    setOfRegulars_of_subset
      (fun theta hTheta => hXFull theta hTheta.1)
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
  have hLambdaSplit :
      cardinalProductRepresentation.pcf XP lambda \/
        cardinalProductRepresentation.pcf XT lambda := by
    rw [hXEq,
      cardinalProductRepresentation_pcf_union hRegularsXP hRegularsXT]
      at hLambdaX
    exact hLambdaX
  cases hLambdaSplit with
  | inl hLambdaXP =>
      refine ⟨XP, (fun theta hTheta => hTheta.1), ?_, hLambdaXP⟩
      have hXPSubsetP : SubsetOf XP P := by
        intro theta hTheta
        rw [← hPcfP]
        exact hTheta.2
      have hXPLeP : Cardinal.mk (CardinalIndex XP) <=
          Cardinal.mk (CardinalIndex P) :=
        Cardinal.mk_subtype_mono hXPSubsetP
      have hPLt : Cardinal.mk (CardinalIndex P) < Cardinal.aleph0 :=
        Cardinal.mk_lt_aleph0
      exact hXPLeP.trans hPLt.le |>.trans (by
        rw [alephSuccSet_cardinalIndex_mk_eq_aleph0])
  | inr hLambdaXT =>
      have hXTSubsetT : SubsetOf XT
          (cardinalProductRepresentation.pcf T) :=
        fun theta hTheta => hTheta.2
      obtain ⟨W, hWXT, hWSize, hLambdaW⟩ :=
        hTailLocalization XT lambda hXTSubsetT hLambdaXT
      refine ⟨W, (fun theta hTheta => hWXT theta hTheta |>.1), ?_, hLambdaW⟩
      exact hWSize.trans (Cardinal.mk_subtype_mono (by
        intro theta hTheta
        obtain ⟨m, hnm, hThetaEq⟩ := hTheta
        exact ⟨m, hThetaEq⟩))

#print axioms
  alephSuccSet_cardinalProductPcfLocalizationOutput_of_tail

/-! Source-accurate strong-limit localization interface.  A finite tail is
selected above the double-power bound, its localization is supplied by
generators on that tail, and the finite-prefix theorem transports the result
back to the full successor-aleph core. -/
theorem alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit_tailGenerators
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    (hGenerators : forall n : Nat,
      CardinalProductDoublePowerBelowCoordinates
          (natTailIUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) ->
        exists G : GeneratorSystem cardinalProductRepresentation
            (cardinalProductRepresentation.pcf
              (natTailIUnionCardSet
                (fun m : Nat =>
                  singletonCardSet
                    (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)),
          TransitiveGeneratorSystem G /\
            GeneratorCapturesCanonicalUltrafilters G) :
    CardinalProductPcfLocalizationOutput alephSuccSet.{u} := by
  obtain ⟨n, hDouble⟩ :=
    exists_alephSuccSet_tail_doublePowerBelow_of_strongLimit hStrongLimit
  obtain ⟨G, hTransitive, hCapture⟩ := hGenerators n hDouble
  exact alephSuccSet_cardinalProductPcfLocalizationOutput_of_tail n
    (alephSuccSet_tail_cardinalProductPcfLocalizationOutput_of_doublePowerBelow
      n hDouble G hTransitive hCapture)

#print axioms
  alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit_tailGenerators

/-! The source induction naturally produces successor-directed semantic
at-most ideals rather than an ultrafilter statement.  The proved escape and
capture lemmas convert that invariant into the tail-generator interface
used above. -/
theorem alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit_tailDirectedGenerators
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    (hGenerators : forall n : Nat,
      CardinalProductDoublePowerBelowCoordinates
          (natTailIUnionCardSet
            (fun m : Nat =>
              singletonCardSet
                (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n) ->
        exists G : GeneratorSystem cardinalProductRepresentation
            (cardinalProductRepresentation.pcf
              (natTailIUnionCardSet
                (fun m : Nat =>
                  singletonCardSet
                    (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n)),
          TransitiveGeneratorSystem G /\
            GeneratorAtMostIdealSuccessorDirected G) :
    CardinalProductPcfLocalizationOutput alephSuccSet.{u} := by
  apply
    alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit_tailGenerators
      hStrongLimit
  intro n hDouble
  obtain ⟨G, hTransitive, hDirected⟩ := hGenerators n hDouble
  exact ⟨G, hTransitive,
    generatorCapturesCanonicalUltrafilters_of_atMostIdealEscape
      (cardinalProductRepresentation.pcf_is_setOfRegulars
        (natTailIUnionCardSet
          (fun m : Nat =>
            singletonCardSet
              (Cardinal.aleph ((m : Ordinal.{u}) + 1))) n))
      G
      (generatorAtMostIdealEscapesCanonicalUltrafilters_of_successorDirected
        G hDirected)⟩

#print axioms
  alephSuccSet_cardinalProductPcfLocalizationOutput_of_strongLimit_tailDirectedGenerators

/-! Stable name for the core maximum obtained directly from canonical
ultrafilter capture, via Corollary 24.29. -/
noncomputable def alephSuccSetMaxPcfWitnessOfCanonicalUltrafilterCapture
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G) :
    MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u} :=
  alephSuccSetMaxPcfWitnessOfGeneratorCompactCover G
    (generatorCompactCover_of_canonicalUltrafilterCapture
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
      alephSuccSet_pcf_cardinalIndex_small
      (fun _ hPcf => alephSuccSet_pcf_mem_gt_aleph0 hPcf)
      G hCapture)

theorem alephSuccSetMaxPcfWitnessOfCanonicalUltrafilterCapture_isMax
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G) :
    IsMaxPcf cardinalProductRepresentation alephSuccSet.{u}
      (alephSuccSetMaxPcfWitnessOfCanonicalUltrafilterCapture
        G hCapture).theta :=
  (alephSuccSetMaxPcfWitnessOfCanonicalUltrafilterCapture
    G hCapture).isMax

#print axioms
  alephSuccSetMaxPcfWitnessOfCanonicalUltrafilterCapture_isMax

/-! The same core maximum with the concentration step expanded to the exact
at-most-ideal escape obstruction. -/
noncomputable def alephSuccSetMaxPcfWitnessOfAtMostIdealEscape
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hEscape : GeneratorAtMostIdealEscapesCanonicalUltrafilters G) :
    MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u} :=
  alephSuccSetMaxPcfWitnessOfCanonicalUltrafilterCapture G
    (generatorCapturesCanonicalUltrafilters_of_atMostIdealEscape
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
      G hEscape)

theorem alephSuccSetMaxPcfWitnessOfAtMostIdealEscape_isMax
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hEscape : GeneratorAtMostIdealEscapesCanonicalUltrafilters G) :
    IsMaxPcf cardinalProductRepresentation alephSuccSet.{u}
      (alephSuccSetMaxPcfWitnessOfAtMostIdealEscape G hEscape).theta :=
  (alephSuccSetMaxPcfWitnessOfAtMostIdealEscape G hEscape).isMax

#print axioms
  alephSuccSetMaxPcfWitnessOfAtMostIdealEscape_isMax

theorem successorAlephHasMaxPcfBelow_of_canonicalUltrafilterCapture
    {theta : Ordinal.{u}}
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G)
    (hCore : forall i, i < theta ->
      cardinalProductRepresentation.pcf alephSuccSet.{u}
        (Cardinal.aleph (i + 1))) :
    SuccessorAlephHasMaxPcfBelow theta :=
  successorAlephHasMaxPcfBelow_of_generatorCompactCover G
    (generatorCompactCover_of_canonicalUltrafilterCapture
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
      alephSuccSet_pcf_cardinalIndex_small
      (fun _ hPcf => alephSuccSet_pcf_mem_gt_aleph0 hPcf)
      G hCapture)
    hCore

theorem successorAlephHasMaxPcfBelow_of_atMostIdealEscape
    {theta : Ordinal.{u}}
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hEscape : GeneratorAtMostIdealEscapesCanonicalUltrafilters G)
    (hCore : forall i, i < theta ->
      cardinalProductRepresentation.pcf alephSuccSet.{u}
        (Cardinal.aleph (i + 1))) :
    SuccessorAlephHasMaxPcfBelow theta :=
  successorAlephHasMaxPcfBelow_of_canonicalUltrafilterCapture G
    (generatorCapturesCanonicalUltrafilters_of_atMostIdealEscape
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
      G hEscape)
    hCore

#print axioms
  successorAlephHasMaxPcfBelow_of_canonicalUltrafilterCapture
#print axioms successorAlephHasMaxPcfBelow_of_atMostIdealEscape

/-! Decode the general cardinal-set localization output back to successor
aleph indices.  Countability of the ambient coordinate set makes the decoded
index set countable; injectivity of `i |-> aleph (i+1)` loses no elements. -/
theorem successorAlephMaxPcfLocalization_of_cardinalProductLocalization
    (hMax : SuccessorAlephHasMaxPcf.{u})
    (A : CardSet.{u})
    (hLocalization : CardinalProductPcfLocalizationOutput A)
    (theta : Ordinal.{u})
    (hAcountable :
      Cardinal.mk (CardinalIndex A) <= Cardinal.aleph0)
    (hAmbient : forall i, i < theta ->
      cardinalProductRepresentation.pcf A
        (Cardinal.aleph (i + 1))) :
    SuccessorAlephMaxPcfLocalization hMax theta := by
  intro X hXTheta hXNonempty
  obtain ⟨B, hBSubset, hBSize, hBLocalized⟩ :=
    hLocalization (successorAlephCardSet X)
      (successorAlephMaxPcfCardinal hMax X)
      (by
        intro cardinal hCardinal
        obtain ⟨i, hiX, rfl⟩ := hCardinal
        exact hAmbient i (hXTheta hiX))
      (successorAlephMaxPcfCardinal_mem_pcf hMax hXNonempty)
  let W : Set (Ordinal.{u}) :=
    {i | i ∈ X /\ B (Cardinal.aleph (i + 1))}
  have hWX : W ⊆ X := by
    intro i hi
    exact hi.1
  have hBCountable :
      Cardinal.mk (CardinalIndex B) <= Cardinal.aleph0 :=
    hBSize.trans hAcountable
  let encode : W -> CardinalIndex B := fun i =>
    ⟨Cardinal.aleph (i.1 + 1), i.2.2⟩
  have hEncodeInjective : Function.Injective encode := by
    intro i j hij
    apply Subtype.ext
    have hAleph : Cardinal.aleph (i.1 + 1) =
        Cardinal.aleph (j.1 + 1) := by
      exact congrArg Subtype.val hij
    have hSucc : i.1 + 1 = j.1 + 1 :=
      Cardinal.aleph.injective hAleph
    apply (Ordinal.add_right_cancel (a := i.1) (b := j.1) 1).mp
    simpa only [Nat.cast_one] using hSucc
  have hWCountable : W.Countable := by
    apply Cardinal.mk_le_aleph0_iff.mp
    exact (Cardinal.mk_le_of_injective hEncodeInjective).trans
      hBCountable
  have hB_eq : B = successorAlephCardSet W := by
    funext theta
    apply propext
    constructor
    · intro hThetaB
      obtain ⟨i, hiX, hTheta⟩ := hBSubset theta hThetaB
      refine ⟨i, ⟨hiX, ?_⟩, hTheta⟩
      rw [← hTheta]
      exact hThetaB
    · rintro ⟨i, ⟨_hiX, hiB⟩, rfl⟩
      exact hiB
  refine ⟨W, hWX, hWCountable, ?_⟩
  rw [← hB_eq]
  exact hBLocalized

#print axioms
  successorAlephMaxPcfLocalization_of_cardinalProductLocalization

/-! The other ambient input used in Jech 24.34: every successor aleph below
the rank domain already belongs to the PCF spectrum of the countable core
`{aleph_(n+1) | n < omega}`. -/
def SuccessorAlephInitialSegmentInCorePcf
    (theta : Ordinal.{u}) : Prop :=
  forall i, i < theta ->
    cardinalProductRepresentation.pcf alephSuccSet.{u}
      (Cardinal.aleph (i + 1))

/-! 核心在此保留“较低后继阿列夫属于核心 PCF”这一接口；中间覆盖证书与替代终端均无外部调用。 -/

/-! The finite-support bookkeeping has a small cardinal-arithmetic component
    which is independent of the substantive closure construction.  Finite
    subsets are quotients of lists, so their cardinality is bounded by the
    maximum of the base cardinal and `aleph0`. -/
theorem mk_finset_le_max_aleph0_mk (Base : Type u) :
    Cardinal.mk (Finset Base) <= max Cardinal.aleph0 (Cardinal.mk Base) := by
  classical
  exact (Cardinal.mk_le_of_surjective List.toFinset_surjective).trans
    (Cardinal.mk_list_le_max Base)

#print axioms mk_finset_le_max_aleph0_mk

/-! 上式是核心闭包构造实际使用的最后一项有限支撑基数估计；后续历史接口不进入主定理。 -/

end PcfProject
