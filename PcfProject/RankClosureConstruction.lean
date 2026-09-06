import PcfProject.LocalRank
import PcfProject.StationaryIdeal

open Cardinal Set
open scoped Cardinal


namespace PcfProject

universe u

/-! This module constructs the bounded rank-reflection principle used by the
main PCF argument. The recursion anticipates every earlier ladder initial segment
whose local rank is below `omega_4`.  Regularity of `aleph_4` keeps every
stage below the cutoff, and continuity at limit stages makes the resulting
trace normal. -/

theorem omegaThreeIndex_card_lt_targetIndexOmega4_cof :
    Cardinal.mk
        (Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord) <
      (Ordinal.lift.{u + 1} targetIndexOmega4.{u}).cof := by
  rw [omegaThreeIndex_card, targetIndexOmega4_lift_cof_eq]
  simp only [Cardinal.lift_aleph]
  rw [Cardinal.aleph_lt_aleph]
  apply Ordinal.lift_lt.mpr
  exact_mod_cast (show (3 : Nat) < 4 by decide)

abbrev OmegaThreeIndex : Type (u + 1) :=
  Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord

noncomputable def successorAlephLocalRankClosedStep
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u})
    (i : OmegaThreeIndex.{u})
    (previous : forall j, j < i -> Set.Iio targetIndexOmega4.{u}) :
    Set.Iio targetIndexOmega4.{u} := by
  classical
  let initial : forall j : OmegaThreeIndex.{u}, j < i ->
      OmegaThreeIndex.{u} -> Set (Ordinal.{u}) := fun j hj alpha =>
    (fun k : Set.Iio j =>
      (previous k.1 (k.2.trans hj)).1) ''
        {k : Set.Iio j | k.1 ∈ guess alpha}
  let contribution : forall j : OmegaThreeIndex.{u}, j < i ->
      OmegaThreeIndex.{u} -> Ordinal.{u} := fun j hj alpha =>
    if successorAlephLocalMaxPcfRank hMax (initial j hj alpha) <
        targetIndexOmega4.{u} then
      successorAlephLocalMaxPcfRank hMax (initial j hj alpha)
    else 0
  let priorSup : Ordinal.{u} :=
    ⨆ j : OmegaThreeIndex.{u}, if hj : j < i then
      (previous j hj).1 + 1 else 0
  let contributionSup : Ordinal.{u} :=
    ⨆ j : OmegaThreeIndex.{u}, if hj : j < i then
      ⨆ alpha : OmegaThreeIndex.{u}, contribution j hj alpha + 1
    else 0
  refine ⟨priorSup ⊔ contributionSup, ?_⟩
  have hAllSmall : Cardinal.mk OmegaThreeIndex.{u} <
      (Ordinal.lift.{u + 1} targetIndexOmega4.{u}).cof :=
    omegaThreeIndex_card_lt_targetIndexOmega4_cof
  have hAllSmall' : Cardinal.lift.{u} (Cardinal.mk OmegaThreeIndex.{u}) <
      (Ordinal.lift.{u + 1} targetIndexOmega4.{u}).cof := by
    simpa using hAllSmall
  have hPrior : priorSup < targetIndexOmega4.{u} := by
    apply Ordinal.lift_iSup_lt_of_lt_cof hAllSmall'
    intro j
    split_ifs with h
    · exact (Cardinal.isSuccLimit_ord
        (Cardinal.isRegular_aleph_add_one (3 : Ordinal.{u})).aleph0_le).add_one_lt
          (previous j h).2
    · exact (Cardinal.isSuccLimit_ord
        (Cardinal.isRegular_aleph_add_one (3 : Ordinal.{u})).aleph0_le).bot_lt
  have hContributionPoint (j : OmegaThreeIndex.{u}) (hj : j < i)
      (alpha : OmegaThreeIndex.{u}) :
      contribution j hj alpha < targetIndexOmega4.{u} := by
    dsimp [contribution]
    split_ifs with h
    · exact h
    · exact (Cardinal.isSuccLimit_ord
        (Cardinal.isRegular_aleph_add_one (3 : Ordinal.{u})).aleph0_le).bot_lt
  have hContributionInner (j : OmegaThreeIndex.{u}) (hj : j < i) :
      (⨆ alpha : OmegaThreeIndex.{u}, contribution j hj alpha + 1) <
        targetIndexOmega4.{u} :=
    Ordinal.lift_iSup_add_one_lt_of_lt_cof hAllSmall'
      (hContributionPoint j hj)
  have hContribution : contributionSup < targetIndexOmega4.{u} := by
    apply Ordinal.lift_iSup_lt_of_lt_cof hAllSmall'
    intro j
    split_ifs with hj
    · exact hContributionInner j hj
    · exact (Cardinal.isSuccLimit_ord
        (Cardinal.isRegular_aleph_add_one (3 : Ordinal.{u})).aleph0_le).bot_lt
  exact max_lt hPrior hContribution

noncomputable def successorAlephLocalRankClosedSequence
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    OmegaThreeIndex.{u} -> Set.Iio targetIndexOmega4.{u} :=
  WellFounded.fix wellFounded_lt (successorAlephLocalRankClosedStep hMax guess)

theorem successorAlephLocalRankClosedSequence_eq
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u})
    (i : OmegaThreeIndex.{u}) :
    successorAlephLocalRankClosedSequence hMax guess i =
      successorAlephLocalRankClosedStep hMax guess i
        (fun j _hj => successorAlephLocalRankClosedSequence hMax guess j) := by
  exact WellFounded.fix_eq _ _ i

theorem successorAlephLocalRankClosedSequence_strictMono
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    StrictMono (successorAlephLocalRankClosedSequence hMax guess) := by
  intro i j hij
  rw [successorAlephLocalRankClosedSequence_eq hMax guess j]
  change (successorAlephLocalRankClosedSequence hMax guess i).1 <
    (let initial : forall k : OmegaThreeIndex.{u}, k < j ->
          OmegaThreeIndex.{u} -> Set (Ordinal.{u}) := fun k hk alpha =>
        (fun l : Set.Iio k =>
          (successorAlephLocalRankClosedSequence hMax guess l.1).1) ''
            {l : Set.Iio k | l.1 ∈ guess alpha}
      let contribution : forall k : OmegaThreeIndex.{u}, k < j ->
          OmegaThreeIndex.{u} -> Ordinal.{u} := fun k hk alpha =>
        if successorAlephLocalMaxPcfRank hMax (initial k hk alpha) <
            targetIndexOmega4.{u} then
          successorAlephLocalMaxPcfRank hMax (initial k hk alpha)
        else 0
      let priorSup : Ordinal.{u} :=
        ⨆ k : OmegaThreeIndex.{u}, if hk : k < j then
          (successorAlephLocalRankClosedSequence hMax guess k).1 + 1 else 0
      let contributionSup : Ordinal.{u} :=
        ⨆ k : OmegaThreeIndex.{u}, if hk : k < j then
          ⨆ alpha : OmegaThreeIndex.{u}, contribution k hk alpha + 1
        else 0
      priorSup ⊔ contributionSup)
  dsimp only
  apply (lt_add_one (successorAlephLocalRankClosedSequence hMax guess i).1).trans_le
  calc
    (successorAlephLocalRankClosedSequence hMax guess i).1 + 1 =
        (if hk : i < j then
          (successorAlephLocalRankClosedSequence hMax guess i).1 + 1 else 0) :=
      by simp only [dif_pos hij]
    _ <= (⨆ k : OmegaThreeIndex.{u}, if hk : k < j then
          (successorAlephLocalRankClosedSequence hMax guess k).1 + 1 else 0) :=
      Ordinal.le_iSup _ i
    _ <= _ := le_sup_left

theorem successorAlephLocalRankClosedSequence_isNormal
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    Order.IsNormal (successorAlephLocalRankClosedSequence hMax guess) := by
  rw [Order.isNormal_iff]
  refine ⟨successorAlephLocalRankClosedSequence_strictMono hMax guess, ?_⟩
  intro i hi b hb
  rw [successorAlephLocalRankClosedSequence_eq hMax guess i]
  apply Subtype.coe_le_coe.mp
  change
    (let initial : forall j : OmegaThreeIndex.{u}, j < i ->
          OmegaThreeIndex.{u} -> Set (Ordinal.{u}) := fun j hj alpha =>
        (fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
          {k : Set.Iio j | k.1 ∈ guess alpha}
      let contribution : forall j : OmegaThreeIndex.{u}, j < i ->
          OmegaThreeIndex.{u} -> Ordinal.{u} := fun j hj alpha =>
        if successorAlephLocalMaxPcfRank hMax (initial j hj alpha) <
            targetIndexOmega4.{u} then
          successorAlephLocalMaxPcfRank hMax (initial j hj alpha)
        else 0
      let priorSup : Ordinal.{u} :=
        ⨆ j : OmegaThreeIndex.{u}, if hj : j < i then
          (successorAlephLocalRankClosedSequence hMax guess j).1 + 1 else 0
      let contributionSup : Ordinal.{u} :=
        ⨆ j : OmegaThreeIndex.{u}, if hj : j < i then
          ⨆ alpha : OmegaThreeIndex.{u}, contribution j hj alpha + 1
        else 0
      priorSup ⊔ contributionSup) <= b.1
  dsimp only
  apply max_le
  · apply Ordinal.iSup_le
    intro j
    split_ifs with hj
    · let sj : OmegaThreeIndex.{u} := Order.succ j
      have hsj : sj < i := hi.succ_lt hj
      have hjs : j < sj := Order.lt_succ_of_not_isMax hj.not_isMax
      have hStep : (successorAlephLocalRankClosedSequence hMax guess j).1 + 1 <=
          (successorAlephLocalRankClosedSequence hMax guess sj).1 := by
        rw [Order.add_one_le_iff]
        exact successorAlephLocalRankClosedSequence_strictMono hMax guess hjs
      exact hStep.trans (Subtype.coe_le_coe.mpr (hb sj hsj))
    · exact bot_le
  · apply Ordinal.iSup_le
    intro j
    split_ifs with hj
    · apply Ordinal.iSup_le
      intro alpha
      let sj : OmegaThreeIndex.{u} := Order.succ j
      have hsj : sj < i := hi.succ_lt hj
      have hjs : j < sj := Order.lt_succ_of_not_isMax hj.not_isMax
      apply le_trans ?_ (Subtype.coe_le_coe.mpr (hb sj hsj))
      rw [successorAlephLocalRankClosedSequence_eq hMax guess sj]
      change
        (if hRank : successorAlephLocalMaxPcfRank hMax
              ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
                {k : Set.Iio j | k.1 ∈ guess alpha}) <
              targetIndexOmega4.{u} then
            successorAlephLocalMaxPcfRank hMax
              ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
                {k : Set.Iio j | k.1 ∈ guess alpha})
          else 0) + 1 <= _
      apply le_trans ?_ le_sup_right
      apply le_trans ?_ (Ordinal.le_iSup
        (fun k : OmegaThreeIndex.{u} =>
          if hk : k < sj then
            ⨆ beta : OmegaThreeIndex.{u},
              (if hRank : successorAlephLocalMaxPcfRank hMax
                    ((fun l : Set.Iio k => (successorAlephLocalRankClosedSequence hMax guess l.1).1) ''
                      {l : Set.Iio k | l.1 ∈ guess beta}) <
                    targetIndexOmega4.{u} then
                  successorAlephLocalMaxPcfRank hMax
                    ((fun l : Set.Iio k => (successorAlephLocalRankClosedSequence hMax guess l.1).1) ''
                      {l : Set.Iio k | l.1 ∈ guess beta})
                else 0) + 1
          else 0) j)
      rw [dif_pos hjs]
      exact Ordinal.le_iSup _ alpha
    · exact bot_le

theorem successorAlephLocalRankClosedSequence_initial_eq
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u})
    (j alpha : OmegaThreeIndex.{u}) :
    ((fun k : OmegaThreeIndex.{u} => (successorAlephLocalRankClosedSequence hMax guess k).1) ''
        guess alpha) ∩ Set.Iio (successorAlephLocalRankClosedSequence hMax guess j).1 =
      (fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
        {k : Set.Iio j | k.1 ∈ guess alpha} := by
  ext y
  constructor
  · rintro ⟨⟨k, hkGuess, rfl⟩, hkRank⟩
    have hkj : k < j :=
      (successorAlephLocalRankClosedSequence_strictMono hMax guess).lt_iff_lt.mp hkRank
    exact ⟨⟨k, hkj⟩, hkGuess, rfl⟩
  · rintro ⟨k, hkGuess, rfl⟩
    exact ⟨⟨k.1, hkGuess, rfl⟩,
      successorAlephLocalRankClosedSequence_strictMono hMax guess k.2⟩

theorem successorAlephLocalRankClosedSequence_rank_lt_succ
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u})
    (j alpha : OmegaThreeIndex.{u})
    (hRank : successorAlephLocalMaxPcfRank hMax
        ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
          {k : Set.Iio j | k.1 ∈ guess alpha}) < targetIndexOmega4.{u}) :
    successorAlephLocalMaxPcfRank hMax
        ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
          {k : Set.Iio j | k.1 ∈ guess alpha}) <
      (successorAlephLocalRankClosedSequence hMax guess (omegaThreeIndexSucc j)).1 := by
  rw [successorAlephLocalRankClosedSequence_eq hMax guess (omegaThreeIndexSucc j)]
  change
    successorAlephLocalMaxPcfRank hMax
        ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
          {k : Set.Iio j | k.1 ∈ guess alpha}) <
      (let initial : forall k : OmegaThreeIndex.{u},
            k < omegaThreeIndexSucc j ->
            OmegaThreeIndex.{u} -> Set (Ordinal.{u}) := fun k hk beta =>
          (fun l : Set.Iio k => (successorAlephLocalRankClosedSequence hMax guess l.1).1) ''
            {l : Set.Iio k | l.1 ∈ guess beta}
        let contribution : forall k : OmegaThreeIndex.{u},
            k < omegaThreeIndexSucc j ->
            OmegaThreeIndex.{u} -> Ordinal.{u} := fun k hk beta =>
          if successorAlephLocalMaxPcfRank hMax (initial k hk beta) <
              targetIndexOmega4.{u} then
            successorAlephLocalMaxPcfRank hMax (initial k hk beta)
          else 0
        let priorSup : Ordinal.{u} :=
          ⨆ k : OmegaThreeIndex.{u},
            if hk : k < omegaThreeIndexSucc j then
              (successorAlephLocalRankClosedSequence hMax guess k).1 + 1 else 0
        let contributionSup : Ordinal.{u} :=
          ⨆ k : OmegaThreeIndex.{u},
            if hk : k < omegaThreeIndexSucc j then
              ⨆ beta : OmegaThreeIndex.{u}, contribution k hk beta + 1
            else 0
        priorSup ⊔ contributionSup)
  dsimp only
  apply (lt_add_one _).trans_le
  calc
    successorAlephLocalMaxPcfRank hMax
          ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
            {k : Set.Iio j | k.1 ∈ guess alpha}) + 1 =
        (if h : successorAlephLocalMaxPcfRank hMax
              ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
                {k : Set.Iio j | k.1 ∈ guess alpha}) <
              targetIndexOmega4.{u} then
            successorAlephLocalMaxPcfRank hMax
              ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
                {k : Set.Iio j | k.1 ∈ guess alpha})
          else 0) + 1 := by rw [dif_pos hRank]
    _ <= ⨆ beta : OmegaThreeIndex.{u},
          (if h : successorAlephLocalMaxPcfRank hMax
                ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
                  {k : Set.Iio j | k.1 ∈ guess beta}) <
                targetIndexOmega4.{u} then
              successorAlephLocalMaxPcfRank hMax
                ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
                  {k : Set.Iio j | k.1 ∈ guess beta})
            else 0) + 1 := Ordinal.le_iSup _ alpha
    _ = (if hj : j < omegaThreeIndexSucc j then
          ⨆ beta : OmegaThreeIndex.{u},
            (if h : successorAlephLocalMaxPcfRank hMax
                  ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
                    {k : Set.Iio j | k.1 ∈ guess beta}) <
                  targetIndexOmega4.{u} then
                successorAlephLocalMaxPcfRank hMax
                  ((fun k : Set.Iio j => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
                    {k : Set.Iio j | k.1 ∈ guess beta})
              else 0) + 1
        else 0) := by rw [dif_pos (lt_omegaThreeIndexSucc j)]
    _ <= (⨆ k : OmegaThreeIndex.{u},
          if hk : k < omegaThreeIndexSucc j then
            ⨆ beta : OmegaThreeIndex.{u},
              (if h : successorAlephLocalMaxPcfRank hMax
                    ((fun l : Set.Iio k => (successorAlephLocalRankClosedSequence hMax guess l.1).1) ''
                      {l : Set.Iio k | l.1 ∈ guess beta}) <
                    targetIndexOmega4.{u} then
                  successorAlephLocalMaxPcfRank hMax
                    ((fun l : Set.Iio k => (successorAlephLocalRankClosedSequence hMax guess l.1).1) ''
                      {l : Set.Iio k | l.1 ∈ guess beta})
                else 0) + 1
          else 0) := Ordinal.le_iSup _ j
    _ <= _ := le_sup_right

noncomputable def successorAlephLocalRankClosedDelta
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    Ordinal.{u} :=
  ⨆ i : OmegaThreeIndex.{u}, (successorAlephLocalRankClosedSequence hMax guess i).1 + 1

theorem successorAlephLocalRankClosedDelta_lt_target
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    successorAlephLocalRankClosedDelta hMax guess < targetIndexOmega4.{u} := by
  have hAllSmall : Cardinal.mk OmegaThreeIndex.{u} <
      (Ordinal.lift.{u + 1} targetIndexOmega4.{u}).cof :=
    omegaThreeIndex_card_lt_targetIndexOmega4_cof
  have hAllSmall' : Cardinal.lift.{u} (Cardinal.mk OmegaThreeIndex.{u}) <
      (Ordinal.lift.{u + 1} targetIndexOmega4.{u}).cof := by
    simpa using hAllSmall
  apply Ordinal.lift_iSup_add_one_lt_of_lt_cof hAllSmall'
  intro i
  exact (successorAlephLocalRankClosedSequence hMax guess i).2

noncomputable def successorAlephLocalRankClosedEta
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    OmegaThreeIndex.{u} -> Set.Iio (successorAlephLocalRankClosedDelta hMax guess) :=
  fun i => ⟨(successorAlephLocalRankClosedSequence hMax guess i).1,
    Ordinal.lt_iSup_add_one
      (fun j : OmegaThreeIndex.{u} => (successorAlephLocalRankClosedSequence hMax guess j).1) i⟩

theorem successorAlephLocalRankClosedEta_strictMono
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    StrictMono (successorAlephLocalRankClosedEta hMax guess) := by
  intro i j hij
  exact successorAlephLocalRankClosedSequence_strictMono hMax guess hij

theorem successorAlephLocalRankClosedEta_isNormal
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    Order.IsNormal (successorAlephLocalRankClosedEta hMax guess) := by
  rw [Order.isNormal_iff]
  refine ⟨successorAlephLocalRankClosedEta_strictMono hMax guess, ?_⟩
  intro i hi b hb
  let bTarget : Set.Iio targetIndexOmega4.{u} :=
    ⟨b.1, b.2.trans (successorAlephLocalRankClosedDelta_lt_target hMax guess)⟩
  have hbTarget : bTarget ∈ upperBounds
      (successorAlephLocalRankClosedSequence hMax guess '' Set.Iio i) := by
    intro _ hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact Subtype.coe_le_coe.mpr (hb j hj)
  change (successorAlephLocalRankClosedSequence hMax guess i).1 <= b.1
  exact (successorAlephLocalRankClosedSequence_isNormal hMax guess).2 hi hbTarget

theorem successorAlephLocalRankClosedDelta_cof_eq_alephThree
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    (successorAlephLocalRankClosedDelta hMax guess).cof = Cardinal.aleph 3 := by
  rw [successorAlephLocalRankClosedDelta, Ordinal.cof_iSup_Iio_add_one]
  · have hIndex : (3 : Ordinal.{u}) = 2 + 1 := by
      exact_mod_cast (show (3 : Nat) = 2 + 1 by decide)
    rw [hIndex]
    exact (Cardinal.isRegular_aleph_add_one (2 : Ordinal.{u})).cof_ord
  · intro i j hij
    exact successorAlephLocalRankClosedSequence_strictMono hMax guess hij

theorem successorAlephLocalRankClosedEta_isCofinal_range
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    IsCofinal (Set.range (successorAlephLocalRankClosedEta hMax guess)) := by
  intro b
  have hb : b.1 < ⨆ i : OmegaThreeIndex.{u},
      (successorAlephLocalRankClosedSequence hMax guess i).1 + 1 := b.2
  rw [Ordinal.lt_iSup_iff] at hb
  obtain ⟨i, hi⟩ := hb
  refine ⟨successorAlephLocalRankClosedEta hMax guess i, Set.mem_range_self i, ?_⟩
  change b.1 <= (successorAlephLocalRankClosedSequence hMax guess i).1
  simpa using hi

theorem successorAlephLocalRankClosedEta_isFundamentalSeq
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u}) :
    Ordinal.IsFundamentalSeq (successorAlephLocalRankClosedEta hMax guess) := by
  refine ⟨?_, successorAlephLocalRankClosedEta_strictMono hMax guess,
    successorAlephLocalRankClosedEta_isCofinal_range hMax guess⟩
  rw [successorAlephLocalRankClosedDelta_cof_eq_alephThree hMax guess]

theorem successorAlephLocalRankClosedEta_rankClosureBelowAt
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u})
    (hGuess : OmegaOneLadderSystemAtAlephThree guess)
    (alpha : OmegaThreeIndex.{u})
    (hAlphaCof : alpha.1.cof = Cardinal.aleph 1) :
    SuccessorAlephLocalMaxPcfRankOmegaThreeRankClosureBelowAt
      hMax targetIndexOmega4 guess (successorAlephLocalRankClosedEta hMax guess) alpha := by
  intro i hiGuess _hCountable hRank
  have hInitial :
      ((fun k : OmegaThreeIndex.{u} =>
          (successorAlephLocalRankClosedEta hMax guess k).1) '' guess alpha) ∩
          Set.Iio (successorAlephLocalRankClosedEta hMax guess i).1 =
        (fun k : Set.Iio i => (successorAlephLocalRankClosedSequence hMax guess k.1).1) ''
          {k : Set.Iio i | k.1 ∈ guess alpha} :=
    successorAlephLocalRankClosedSequence_initial_eq hMax guess i alpha
  rw [hInitial] at hRank ⊢
  have hIAlpha : i.1 < alpha.1 :=
    hGuess alpha hAlphaCof |>.1 i hiGuess
  have hAlphaLimit : Order.IsSuccLimit alpha.1 :=
    Ordinal.one_lt_cof_iff.mp (by
      rw [hAlphaCof]
      exact Cardinal.one_lt_aleph0.trans_le
        (Cardinal.aleph0_le_aleph 1))
  have hSuccAlpha : omegaThreeIndexSucc i < alpha := by
    exact hAlphaLimit.succ_lt hIAlpha
  exact (successorAlephLocalRankClosedSequence_rank_lt_succ hMax guess i alpha hRank).trans
    (successorAlephLocalRankClosedSequence_strictMono hMax guess hSuccAlpha)

theorem successorAlephLocalRankClosedEta_clubRankClosureBelow
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (guess : OmegaThreeIndex.{u} -> Set OmegaThreeIndex.{u})
    (hGuess : OmegaOneLadderSystemAtAlephThree guess) :
    SuccessorAlephLocalMaxPcfRankOmegaThreeClubRankClosureBelow
      hMax targetIndexOmega4 guess (successorAlephLocalRankClosedEta hMax guess) := by
  refine ⟨?_, ?_⟩
  · intro s _hs _hNonempty _hDirected alpha _hLUB hAlphaCof
    exact successorAlephLocalRankClosedEta_rankClosureBelowAt
      hMax guess hGuess alpha hAlphaCof
  · intro alpha
    refine ⟨alpha, ?_, le_rfl⟩
    intro hAlphaCof
    exact successorAlephLocalRankClosedEta_rankClosureBelowAt
      hMax guess hGuess alpha hAlphaCof

theorem successorAlephLocalOmegaFourTargetReflectionPrinciple_of_rankConstruction
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta) :
    SuccessorAlephLocalOmegaFourTargetReflectionPrinciple hMax := by
  intro hTargetTheta
  let guess := omegaOneClubGuessingSystemAtAlephThree
  let delta := successorAlephLocalRankClosedDelta hMax guess
  let eta := successorAlephLocalRankClosedEta hMax guess
  have hDeltaTarget : delta < targetIndexOmega4.{u} :=
    successorAlephLocalRankClosedDelta_lt_target hMax guess
  have hDeltaTheta : delta < theta := hDeltaTarget.trans_le hTargetTheta
  have hDeltaCof : delta.cof = Cardinal.aleph 3 :=
    successorAlephLocalRankClosedDelta_cof_eq_alephThree hMax guess
  have hDeltaLimit : Order.IsSuccLimit delta :=
    Ordinal.one_lt_cof_iff.mp (by
      rw [hDeltaCof]
      exact Cardinal.one_lt_aleph0.trans_le
        (Cardinal.aleph0_le_aleph 3))
  have hDeltaUncountable : Cardinal.aleph0 < delta.cof := by
    rw [hDeltaCof]
    exact Cardinal.aleph0_lt_aleph.mpr (by simp)
  refine ⟨delta, hDeltaTheta, hDeltaTarget, hDeltaLimit,
    hDeltaUncountable, ?_⟩
  exact
    successorAlephLocalMaxPcfRankReflectionBelowAt_of_normal_of_clubRankClosureBelow
      hMax guess eta hDeltaCof
      omegaOneClubGuessingSystemAtAlephThree_spec
      (successorAlephLocalRankClosedEta_isFundamentalSeq hMax guess)
      (successorAlephLocalRankClosedEta_isNormal hMax guess)
      (successorAlephLocalRankClosedEta_clubRankClosureBelow hMax guess
        omegaOneClubGuessingSystemAtAlephThree_spec.1)

#print axioms
  successorAlephLocalOmegaFourTargetReflectionPrinciple_of_rankConstruction

/-! Only the part of Corollary 24.30 below a fixed cutoff is used by the
bounded reflection contradiction. -/
def SuccessorAlephLocalClubMaxPcfBelow
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (bound : Ordinal.{u}) : Prop :=
  forall eta, eta < theta -> eta < bound -> Order.IsSuccLimit eta ->
    Cardinal.aleph0 < eta.cof ->
    exists C : Set (Set.Iio eta),
      IsClub C /\
        successorAlephLocalMaxPcfCardinal hMax
            ((fun i : Set.Iio eta => i.1) '' C) =
          Cardinal.aleph (eta + 1)

theorem ordinalCof_lt_targetAlephOmega_of_lt_targetIndexOmega4
    {eta : Ordinal.{u}}
    (hEtaTarget : eta < targetIndexOmega4.{u}) :
    eta.cof < targetAlephOmega.{u} := by
  have hCard4 : eta.card < Cardinal.aleph (4 : Ordinal.{u}) :=
    Cardinal.lt_ord.mp hEtaTarget
  have hFourOmega : Cardinal.aleph (4 : Ordinal.{u}) <
      targetAlephOmega.{u} := by
    apply Cardinal.aleph_lt_aleph.mpr
    exact Ordinal.natCast_lt_omega0 4
  exact (Ordinal.cof_le_card eta).trans_lt (hCard4.trans hFourOmega)

theorem two_power_ordinalCof_lt_aleph_of_strongLimit_of_uncountableCof
    {eta : Ordinal.{u}}
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u})
    (hEtaTarget : eta < targetIndexOmega4.{u})
    (hEtaCof : Cardinal.aleph0 < eta.cof) :
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta := by
  have hCofTarget : eta.cof < targetAlephOmega.{u} :=
    ordinalCof_lt_targetAlephOmega_of_lt_targetIndexOmega4 hEtaTarget
  have hPowerTarget : (2 : Cardinal.{u}) ^ eta.cof <
      targetAlephOmega.{u} :=
    hStrongLimit.isStrongPrelimit hCofTarget
  have hOmegaEta : Ordinal.omega0 < eta := by
    apply lt_of_not_ge
    intro hEtaOmega
    have hCardLe : eta.card <= Ordinal.omega0.card :=
      Ordinal.card_le_card hEtaOmega
    have hCofCard : Cardinal.aleph0 < eta.card :=
      hEtaCof.trans_le (Ordinal.cof_le_card eta)
    rw [Ordinal.card_omega0] at hCardLe
    exact (not_lt_of_ge hCardLe) hCofCard
  exact hPowerTarget.trans (Cardinal.aleph_lt_aleph.mpr hOmegaEta)

#print axioms
  two_power_ordinalCof_lt_aleph_of_strongLimit_of_uncountableCof

/-! Corollary 24.30 specialized to the successor-aleph index families used
in the rank proof.  The strong-limit arithmetic needed in Shelah's
application is deliberately kept outside this source theorem. -/
def SuccessorAlephLocalCorollary2430
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta) : Prop :=
  forall eta, eta < theta -> Order.IsSuccLimit eta ->
    Cardinal.aleph0 < eta.cof ->
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    exists C : Set (Set.Iio eta),
      IsClub C /\
        successorAlephLocalMaxPcfCardinal hMax
            ((fun i : Set.Iio eta => i.1) '' C) =
          Cardinal.aleph (eta + 1)

/-! The two genuinely PCF-specific assertions used inside the proof of
Corollary 24.30: a generator-index set belongs to every ultrafilter extending
the club filter, and restricting to a club inside that set has the required
maximum.  The next theorem proves that these data imply the club conclusion;
the ultrafilter compactness step itself is no longer assumed. -/
def SuccessorAlephLocalCorollary2430UltrafilterData
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta) : Prop :=
  forall eta, eta < theta -> Order.IsSuccLimit eta ->
    Cardinal.aleph0 < eta.cof ->
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    exists P : Set.Iio eta -> Prop,
      (forall J : Ideal (Set.Iio eta),
        J.IsUltrafilterDual ->
        (forall C : Set (Set.Iio eta), IsClub C ->
          J.Eventually (fun i => i ∈ C)) ->
        J.Eventually P) /\
      forall C : Set (Set.Iio eta), IsClub C ->
        (forall i, i ∈ C -> P i) ->
        successorAlephLocalMaxPcfCardinal hMax
            ((fun i : Set.Iio eta => i.1) '' C) =
          Cardinal.aleph (eta + 1)

/-! The canonical coordinate map from the ordinal index below `eta` to the
successor-aleph product indexed by that same initial segment.  Its
injectivity records that no coordinate is duplicated. -/
noncomputable def successorAlephIioCardinalIndex
    (eta : Ordinal.{u}) (i : Set.Iio eta) :
    CardinalIndex (successorAlephCardSet (Set.Iio eta)) :=
  ⟨Cardinal.aleph (i.1 + 1), ⟨i.1, i.2, rfl⟩⟩

theorem successorAlephIioCardinalIndex_injective
    (eta : Ordinal.{u}) :
    Function.Injective (successorAlephIioCardinalIndex eta) := by
  intro i j hij
  apply Subtype.ext
  apply Order.succ_injective
  apply Cardinal.aleph.injective
  exact congrArg Subtype.val hij

#print axioms successorAlephIioCardinalIndex_injective

/-! The coordinate map for a fundamental sequence below `eta`.  The ambient
cardinal set remains the successor-aleph family below `eta`, while the ideal
is supported only on the cofinal sequence, exactly as in Theorem 24.16. -/
noncomputable def successorAlephFundamentalCardinalIndex
    (eta : Ordinal.{u})
    (f : Set.Iio eta.cof.ord -> Set.Iio eta)
    (i : Set.Iio eta.cof.ord) :
    CardinalIndex (successorAlephCardSet (Set.Iio eta)) :=
  successorAlephIioCardinalIndex eta (f i)

theorem successorAlephFundamentalCardinalIndex_injective
    (eta : Ordinal.{u})
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hf : Function.Injective f) :
    Function.Injective (successorAlephFundamentalCardinalIndex eta f) :=
  (successorAlephIioCardinalIndex_injective eta).comp hf

#print axioms successorAlephFundamentalCardinalIndex_injective

/-! Along a fundamental sequence into a limit index `eta`, the corresponding
successor-aleph coordinates are eventually above every cardinal below
`aleph eta`.  The witnessing tail is a club in the source order, hence is
eventual for its nonstationary ideal. -/
theorem successorAlephFundamental_eventually_unbounded
    (eta : Ordinal.{u})
    (hEtaLimit : Order.IsSuccLimit eta)
    (hEtaCof : Cardinal.aleph0 < eta.cof)
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hFundamental : Ordinal.IsFundamentalSeq f) :
    forall kappa : Cardinal.{u}, kappa < Cardinal.aleph eta ->
      exists B : CardinalIndex
          (successorAlephCardSet (Set.Iio eta)) -> Prop,
        ((nonstationaryIdeal (Set.Iio eta.cof.ord)
          (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
            (successorAlephFundamentalCardinalIndex eta f)).Eventually B /\
        forall i, B i -> kappa < i.1 := by
  let hSourceCofNe : Order.cof (Set.Iio eta.cof.ord) ≠
      Cardinal.aleph0 :=
    cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof
  letI : Nonempty (Set.Iio eta.cof.ord) :=
    ⟨⟨0, Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans hEtaCof)⟩⟩
  intro kappa hKappa
  have hAlephLimit : Cardinal.aleph eta =
      ⨆ beta : Set.Iio eta, Cardinal.aleph beta.1 :=
    Cardinal.aleph_limit hEtaLimit
  rw [hAlephLimit] at hKappa
  obtain ⟨beta, hKappaBeta⟩ := exists_lt_of_lt_ciSup' hKappa
  obtain ⟨fi, ⟨i, rfl⟩, hBetaFi⟩ :=
    hFundamental.isCofinal_range beta
  let B : CardinalIndex
      (successorAlephCardSet (Set.Iio eta)) -> Prop :=
    fun k => kappa < k.1
  refine ⟨B, ?_, fun i hi => hi⟩
  rw [Ideal.pushforward_eventually_iff]
  apply (nonstationaryIdeal_eventually_iff_contains_club
    hSourceCofNe _).mpr
  refine ⟨Set.Ici i, isClub_Ici i, ?_⟩
  intro j hij
  change kappa < Cardinal.aleph ((f j).1 + 1)
  have hBetaJ : beta.1 <= (f j).1 := by
    exact hBetaFi.trans (hFundamental.strictMono.monotone hij)
  exact hKappaBeta.trans (Cardinal.aleph_lt_aleph.mpr
    (hBetaJ.trans_lt (lt_add_one (f j).1)))

#print axioms successorAlephFundamental_eventually_unbounded

theorem successorAlephFundamental_eventually_rapidSupportBelow_small
    (eta : Ordinal.{u})
    (hEtaLimit : Order.IsSuccLimit eta)
    (hEtaCof : Cardinal.aleph0 < eta.cof)
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hFundamental : Ordinal.IsFundamentalSeq f)
    (beta alpha : Set.Iio (Cardinal.aleph (eta + 1)).ord) :
    ((nonstationaryIdeal (Set.Iio eta.cof.ord)
      (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
        (successorAlephFundamentalCardinalIndex eta f)).Eventually
      (fun k => Cardinal.mk
          (cardinalProductRapidSupportBelow (Cardinal.aleph eta)
            (Cardinal.aleph (eta + 1)) beta alpha) <
        Cardinal.lift.{u + 1} k.1) := by
  classical
  let J := (nonstationaryIdeal (Set.Iio eta.cof.ord)
    (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
      (successorAlephFundamentalCardinalIndex eta f)
  by_cases hBetaCof : beta.1.cof < Cardinal.aleph eta
  · by_cases hAlphaBeta : alpha < beta
    · by_cases hBetaLimit : Order.IsSuccLimit beta.1
      · obtain ⟨B, hB, hBound⟩ :=
          successorAlephFundamental_eventually_unbounded
            eta hEtaLimit hEtaCof hFundamental beta.1.cof hBetaCof
        exact J.eventually_mono hB (by
          intro k hk
          exact (cardinalProductRapidSupportBelow_mk_lt_cof
            hBetaCof hBetaLimit hAlphaBeta).trans
              (Cardinal.lift_lt.mpr (hBound k hk)))
      · have hEmpty : cardinalProductRapidSupportBelow
            (Cardinal.aleph eta) (Cardinal.aleph (eta + 1)) beta alpha = ∅ := by
          rw [cardinalProductRapidSupportBelow_eq hBetaCof,
            cardinalProductRapidSupport_eq hAlphaBeta,
            smallInitialClub, dif_neg hBetaLimit]
          simp
        apply J.eventually_of_forall
        intro k
        rw [hEmpty]
        have hkPos : (0 : Cardinal.{u + 1}) <
            Cardinal.lift.{u + 1} k.1 :=
          by simpa using
            (Cardinal.lift_lt.{u, u + 1}.mpr
              ((successorAlephCardSet_regulars (Set.Iio eta)
                k.1 k.2).pos))
        simpa using hkPos
    · have hEmpty : cardinalProductRapidSupportBelow
          (Cardinal.aleph eta) (Cardinal.aleph (eta + 1)) beta alpha = ∅ := by
        rw [cardinalProductRapidSupportBelow_eq hBetaCof,
          cardinalProductRapidSupport, dif_neg hAlphaBeta]
      apply J.eventually_of_forall
      intro k
      rw [hEmpty]
      have hkPos : (0 : Cardinal.{u + 1}) <
          Cardinal.lift.{u + 1} k.1 :=
        by simpa using
          (Cardinal.lift_lt.{u, u + 1}.mpr
            ((successorAlephCardSet_regulars (Set.Iio eta)
              k.1 k.2).pos))
      simpa using hkPos
  · have hEmpty : cardinalProductRapidSupportBelow
        (Cardinal.aleph eta) (Cardinal.aleph (eta + 1)) beta alpha = ∅ := by
      rw [cardinalProductRapidSupportBelow, if_neg hBetaCof]
    apply J.eventually_of_forall
    intro k
    rw [hEmpty]
    have hkPos : (0 : Cardinal.{u + 1}) <
        Cardinal.lift.{u + 1} k.1 :=
      by simpa using
        (Cardinal.lift_lt.{u, u + 1}.mpr
          ((successorAlephCardSet_regulars (Set.Iio eta)
            k.1 k.2).pos))
    simpa using hkPos

#print axioms
  successorAlephFundamental_eventually_rapidSupportBelow_small

theorem successorAlephFundamental_exists_strictIncreasing_rapidBelow_of_directed
    (eta : Ordinal.{u})
    (hEtaLimit : Order.IsSuccLimit eta)
    (hEtaCof : Cardinal.aleph0 < eta.cof)
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hFundamental : Ordinal.IsFundamentalSeq f)
    (K : Ideal (CardinalIndex
      (successorAlephCardSet (Set.Iio eta))))
    (hBaseLe : Ideal.Le
      ((nonstationaryIdeal (Set.Iio eta.cof.ord)
        (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
          (successorAlephFundamentalCardinalIndex eta f)) K)
    (hDirected : (cardinalProductFrame
      (successorAlephCardSet (Set.Iio eta)) K).PointwiseStrictDirectedBelow
        (Order.succ (Cardinal.aleph (eta + 1)))) :
    exists d : Set.Iio (Cardinal.aleph (eta + 1)).ord ->
        ProductElement (cardinalProductFrame
          (successorAlephCardSet (Set.Iio eta)) K),
      (forall {alpha beta}, alpha < beta ->
        (cardinalProductFrame
          (successorAlephCardSet (Set.Iio eta)) K).eventuallyPointwiseLt
            (d alpha) (d beta)) /\
      forall gamma : Cardinal.{u}, Cardinal.aleph0 < gamma ->
        gamma < Cardinal.aleph eta ->
          CardinalProductGammaRapid K gamma
            (Cardinal.aleph (eta + 1)) d := by
  apply exists_cardinalProduct_strictIncreasing_rapidBelow_of_directed
    (successorAlephCardSet_regulars (Set.Iio eta)) hDirected
  intro beta alpha
  exact hBaseLe _
    (successorAlephFundamental_eventually_rapidSupportBelow_small
      eta hEtaLimit hEtaCof hFundamental beta alpha)

#print axioms
  successorAlephFundamental_exists_strictIncreasing_rapidBelow_of_directed

/-! At a limit source stage of a normal fundamental sequence, the
cofinality of the attained ordinal is strictly below the cofinality indexing
the whole sequence.  The restricted normal map has cofinal range below the
attained value, while the source initial segment has cardinality below
`cof eta`. -/
theorem normalFundamental_value_cof_lt_sourceCof
    {eta : Ordinal.{u}}
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hNormal : Order.IsNormal f)
    (i : Set.Iio eta.cof.ord)
    (hi : Order.IsSuccLimit i) :
    (f i).1.cof < eta.cof := by
  let embed (j : Set.Iio i.1) : Set.Iio eta.cof.ord :=
    ⟨j.1, Set.mem_Iio.mpr
      ((Set.mem_Iio.mp j.2).trans (Set.mem_Iio.mp i.2))⟩
  let q : Set.Iio i.1 -> Set.Iio (f i).1 := fun j =>
    ⟨(f (embed j)).1, hNormal.strictMono
      (show embed j < i from j.2)⟩
  have hq : IsCofinal (Set.range q) := by
    intro b
    let b' : Set.Iio eta := ⟨b.1, Set.mem_Iio.mpr
      ((Set.mem_Iio.mp b.2).trans (Set.mem_Iio.mp (f i).2))⟩
    have hb' : b' < f i := Set.mem_Iio.mp b.2
    obtain ⟨j, hji, hbj⟩ := (hNormal.lt_iff_exists_lt hi).mp hb'
    let j' : Set.Iio i.1 := ⟨j.1, hji⟩
    refine ⟨q j', Set.mem_range_self j', hbj.le⟩
  have hCofLe : Order.cof (Set.Iio (f i).1) <=
      Cardinal.mk (Set.Iio i.1) :=
    (Order.cof_le hq).trans Cardinal.mk_range_le
  have hCardI : i.1.card < eta.cof := Cardinal.lt_ord.mp i.2
  have hLiftCardI : Cardinal.lift.{u + 1} i.1.card <
      Cardinal.lift.{u + 1} eta.cof := Cardinal.lift_lt.mpr hCardI
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof,
    Cardinal.mk_Iio_ordinal] at hCofLe
  exact Cardinal.lift_lt.mp (hCofLe.trans_lt hLiftCardI)

#print axioms normalFundamental_value_cof_lt_sourceCof

/-! Below a successor-aleph coordinate attained at a normal limit stage,
the cofinality of any proper closed value is already below the predecessor
aleph, once that predecessor dominates the source cofinality.  If the value
is a limit, its cofinality is regular and therefore cannot equal the
singular predecessor aleph; otherwise its cofinality is at most one. -/
theorem closedOrdinal_cof_lt_predecessorAleph_at_normalLimit
    {eta : Ordinal.{u}}
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hNormal : Order.IsNormal f)
    (i : Set.Iio eta.cof.ord)
    (hi : Order.IsSuccLimit i)
    (hCofTail : eta.cof < Cardinal.aleph (f i).1)
    {o : Ordinal.{u}}
    (hBad : o < (Cardinal.aleph ((f i).1 + 1)).ord) :
    o.cof < Cardinal.aleph (f i).1 := by
  have hFiLimit : Order.IsSuccLimit (f i).1 :=
    (hNormal.map_isSuccLimit hi).subtypeVal (isLowerSet_Iio eta)
  have hFiSingular : (Cardinal.aleph (f i).1).IsSingular := by
    rw [Cardinal.isSingular_aleph_iff]
    exact ⟨hFiLimit,
      (normalFundamental_value_cof_lt_sourceCof hNormal i hi).trans hCofTail⟩
  have hCardLe : o.card <= Cardinal.aleph (f i).1 := by
    rw [← Order.lt_succ_iff, Cardinal.succ_aleph]
    exact Cardinal.lt_ord.mp hBad
  have hCofLe : o.cof <= Cardinal.aleph (f i).1 :=
    (Ordinal.cof_le_card o).trans hCardLe
  by_cases hoLimit : Order.IsSuccLimit o
  · exact hCofLe.lt_of_ne (fun hEq =>
      hFiSingular.not_isRegular (hEq ▸ Cardinal.isRegular_cof hoLimit))
  · have hCofLeOne : o.cof <= 1 :=
      le_of_not_gt (fun h => hoLimit (Ordinal.one_lt_cof_iff.mp h))
    exact hCofLeOne.trans_lt
      (Cardinal.one_lt_aleph0.trans_le
        (Cardinal.aleph0_le_aleph (f i).1))

#print axioms closedOrdinal_cof_lt_predecessorAleph_at_normalLimit

/-! The stationary/Fodor conclusion in the final paragraph of Jech's
Theorem 24.16.  A closed exact upper bound of a sequence which is rapid for
all regular cardinals below `aleph eta` reaches the coordinate top on an
eventual set.  The small-coordinate argument is performed on the actual
range of the fundamental sequence, not on the larger ambient card set. -/
theorem successorAlephFundamental_eventually_top_of_localized_closedExactUpperBound
    (eta : Ordinal.{u})
    (hEtaLimit : Order.IsSuccLimit eta)
    (hEtaCof : Cardinal.aleph0 < eta.cof)
    (hPower : (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta)
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hFundamental : Ordinal.IsFundamentalSeq f)
    (hNormal : Order.IsNormal f)
    (P : Set.Iio eta.cof.ord -> Prop)
    (d : Set.Iio (Cardinal.aleph (eta + 1)).ord ->
      ProductElement (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        (((nonstationaryIdeal (Set.Iio eta.cof.ord)
          (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).localize P).pushforward
            (successorAlephFundamentalCardinalIndex eta f))))
    (hIncreasing : forall {alpha beta}, alpha < beta ->
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        (((nonstationaryIdeal (Set.Iio eta.cof.ord)
          (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).localize P).pushforward
            (successorAlephFundamentalCardinalIndex eta f))).eventuallyPointwiseLt
        (d alpha) (d beta))
    (hRapid : forall gamma : Cardinal.{u}, Cardinal.aleph0 < gamma ->
      gamma < Cardinal.aleph eta ->
        CardinalProductGammaRapid
          (((nonstationaryIdeal (Set.Iio eta.cof.ord)
            (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).localize P).pushforward
              (successorAlephFundamentalCardinalIndex eta f))
          gamma (Cardinal.aleph (eta + 1)) d)
    (g : CardinalProductClosedElement
      (successorAlephCardSet (Set.Iio eta)))
    (hExact : CardinalProductClosedExactUpperBound
      (((nonstationaryIdeal (Set.Iio eta.cof.ord)
        (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).localize P).pushforward
          (successorAlephFundamentalCardinalIndex eta f)) d g) :
    (((nonstationaryIdeal (Set.Iio eta.cof.ord)
      (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).localize P).pushforward
        (successorAlephFundamentalCardinalIndex eta f)).Eventually
      (fun k => k.1.ord <= (g k).1) := by
  classical
  let source := Set.Iio eta.cof.ord
  let hSourceCofNe : Order.cof source ≠ Cardinal.aleph0 :=
    cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof
  let NS : Ideal source := nonstationaryIdeal source hSourceCofNe
  let coord := successorAlephFundamentalCardinalIndex eta f
  let A := successorAlephCardSet (Set.Iio eta)
  let K := NS.localize P
  let J := K.pushforward coord
  change J.Eventually (fun k => k.1.ord <= (g k).1)
  rw [Ideal.pushforward_eventually_iff]
  by_contra hNotTop
  let Bad : Set source := {i | (g (coord i)).1 < (coord i).1.ord}
  have hBadStationary : Stationary (Bad ∩ {i | P i}) := by
    apply Classical.byContradiction
    intro hNotStationary
    apply hNotTop
    change K.Small (fun i => Not ((coord i).1.ord <= (g (coord i)).1))
    change NS.Small (fun i =>
      Not ((coord i).1.ord <= (g (coord i)).1) /\ P i)
    have hSmall : Nonstationary
        ({i | (g (coord i)).1 < (coord i).1.ord /\ P i} : Set source) :=
      (nonstationary_iff_not_stationary _).mpr (by
        simpa only [Bad, Set.mem_inter_iff, Set.mem_setOf_eq]
          using hNotStationary)
    exact NS.subset_small hSmall (by
      intro i hi
      exact ⟨lt_of_not_ge hi.1, hi.2⟩)
  letI : Nonempty source :=
    ⟨⟨0, Cardinal.ord_pos.mpr (Cardinal.aleph0_pos.trans hEtaCof)⟩⟩
  letI : NoMaxOrder source := by
    dsimp only [source]
    exact (Cardinal.isSuccLimit_ord
      (Cardinal.isRegular_cof hEtaLimit).aleph0_le).isSuccPrelimit.noMaxOrder_Iio
  let Limit : Set source := StrictLimitPoints (Set.univ : Set source)
  have hLimitClub : IsClub Limit :=
    strictLimitPoints_isClub hSourceCofNe IsCofinal.univ
  have hSuccCofLt : Order.succ eta.cof < Cardinal.aleph eta :=
    (Order.succ_le_iff.mpr (Cardinal.cantor eta.cof)).trans_lt hPower
  obtain ⟨B, hB, hBound⟩ :=
    successorAlephFundamental_eventually_unbounded
      eta hEtaLimit hEtaCof hFundamental (Order.succ eta.cof) hSuccCofLt
  have hBSource : NS.Eventually (fun i => B (coord i)) := by
    exact (Ideal.pushforward_eventually_iff NS coord B).mp hB
  obtain ⟨C, hCClub, hC⟩ :=
    (nonstationaryIdeal_eventually_iff_contains_club
      hSourceCofNe _).mp hBSource
  have hBadLimit : Stationary ((Bad ∩ {i | P i}) ∩ Limit) :=
    stationary_inter_isClub hSourceCofNe hBadStationary hLimitClub
  have hS : Stationary (((Bad ∩ {i | P i}) ∩ Limit) ∩ C) :=
    stationary_inter_isClub hSourceCofNe hBadLimit hCClub
  let S : Set source := ((Bad ∩ {i | P i}) ∩ Limit) ∩ C
  have hExistsRank : forall i, i ∈ S -> exists j, j < i /\
      (g (coord i)).1.cof < Cardinal.aleph (f j).1 := by
    intro i hi
    have hiLimit : Order.IsSuccLimit i :=
      isSuccLimit_of_mem_strictLimitPoints_univ hi.1.2
    have hCoordBound := hBound (coord i) (hC i hi.2)
    have hCofTail : eta.cof < Cardinal.aleph (f i).1 := by
      change Order.succ eta.cof < Cardinal.aleph ((f i).1 + 1) at hCoordBound
      rw [← Cardinal.succ_aleph, Order.succ_lt_succ_iff] at hCoordBound
      exact hCoordBound
    have hBad : (g (coord i)).1 <
        (Cardinal.aleph ((f i).1 + 1)).ord := by
      simpa only [Bad, coord, successorAlephFundamentalCardinalIndex,
        successorAlephIioCardinalIndex] using hi.1.1.1
    have hLocal := closedOrdinal_cof_lt_predecessorAleph_at_normalLimit
      hNormal i hiLimit hCofTail hBad
    have hAlephLimit : Cardinal.aleph (f i).1 =
        ⨆ beta : Set.Iio (f i).1, Cardinal.aleph beta.1 :=
      Cardinal.aleph_limit
        ((hNormal.map_isSuccLimit hiLimit).subtypeVal (isLowerSet_Iio eta))
    rw [hAlephLimit] at hLocal
    obtain ⟨beta, hBeta⟩ := exists_lt_of_lt_ciSup' hLocal
    let betaAtEta : Set.Iio eta :=
      ⟨beta.1, Set.mem_Iio.mpr
        ((Set.mem_Iio.mp beta.2).trans (Set.mem_Iio.mp (f i).2))⟩
    have hBetaFi : betaAtEta < f i := beta.2
    obtain ⟨j, hji, hBetaJ⟩ :=
      (hNormal.lt_iff_exists_lt hiLimit).mp hBetaFi
    refine ⟨j, hji, hBeta.trans ?_⟩
    exact Cardinal.aleph_lt_aleph.mpr hBetaJ
  let rank (i : source) : source :=
    if hi : i ∈ S then Classical.choose (hExistsRank i hi) else i
  have hRankSpec : forall i (hi : i ∈ S),
      rank i < i /\
        (g (coord i)).1.cof < Cardinal.aleph (f (rank i)).1 := by
    intro i hi
    rw [show rank i = Classical.choose (hExistsRank i hi) by
      simp only [rank, dif_pos hi]]
    exact Classical.choose_spec (hExistsRank i hi)
  have hRegressive : RegressiveOn S rank := fun i hi => (hRankSpec i hi).1
  obtain ⟨j0, T, hTSub, hTStationary, hRankConst⟩ :=
    exists_stationary_subset_eqOn_const_of_small_initial_segments
      hSourceCofNe
      (smallInitialSegments_Iio_ord_of_isRegular
        (Cardinal.isRegular_cof hEtaLimit))
      hS hRegressive
  have hTNonempty : T.Nonempty := stationary_nonempty hTStationary
  let i0 : source := hTNonempty.choose
  have hi0T : i0 ∈ T := hTNonempty.choose_spec
  have hi0S : i0 ∈ S := hTSub hi0T
  have hj0i0 : j0 < i0 := by
    calc
      j0 = rank i0 := (hRankConst hi0T).symm
      _ < i0 := (hRankSpec i0 hi0S).1
  let gamma : Cardinal.{u} := Cardinal.aleph ((f i0).1 + 1)
  have hGammaRegular : gamma.IsRegular :=
    Cardinal.isRegular_aleph_add_one (f i0).1
  have hGammaUncountable : Cardinal.aleph0 < gamma := by
    exact (Cardinal.aleph0_le_aleph (f i0).1).trans_lt
      (Cardinal.aleph_lt_aleph.mpr (lt_add_one (f i0).1))
  have hGammaEta : gamma < Cardinal.aleph eta := by
    exact Cardinal.aleph_lt_aleph.mpr
      (hEtaLimit.add_one_lt (f i0).2)
  have hGammaLambda : gamma < Cardinal.aleph (eta + 1) :=
    hGammaEta.trans (Cardinal.aleph_lt_aleph.mpr (lt_add_one eta))
  have hEtaCofGamma : eta.cof < gamma := by
    have hCoordBound0 := hBound (coord i0) (hC i0 hi0S.2)
    change Order.succ eta.cof <
      Cardinal.aleph ((f i0).1 + 1) at hCoordBound0
    rw [← Cardinal.succ_aleph] at hCoordBound0
    exact (Order.succ_lt_succ_iff.mp hCoordBound0).trans
        (Cardinal.aleph_lt_aleph.mpr (lt_add_one (f i0).1))
  let R : CardinalIndex A -> Prop := fun k => exists i, coord i = k
  have hCoordInjective : Function.Injective coord :=
    successorAlephFundamentalCardinalIndex_injective eta
      hFundamental.strictMono.injective
  have hRSmall : Cardinal.lift.{u, u + 1}
      (Cardinal.mk {k : CardinalIndex A // R k}) <
        Cardinal.lift.{u + 1} gamma := by
    rw [Cardinal.lift_id'.{u, u + 1},
      show {k : CardinalIndex A // R k} = Set.range coord by rfl,
      ← Cardinal.mk_congr (Equiv.ofInjective coord hCoordInjective),
      Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
    exact Cardinal.lift_lt.mpr hEtaCofGamma
  have hREventual : J.Eventually R := by
    rw [Ideal.pushforward_eventually_iff]
    exact K.eventually_of_forall (fun i => ⟨i, rfl⟩)
  have hCofEventually : J.Eventually
      (fun k => gamma <= (g k).1.cof) := by
    apply hExact.eventually_cof_ge_of_gammaRapid_of_support
      hGammaRegular hGammaUncountable
      (Cardinal.isRegular_aleph_add_one eta) hGammaLambda
      R hRSmall hREventual
    · exact hIncreasing
    · exact hRapid gamma hGammaUncountable hGammaEta
  have hCofEventuallySource : K.Eventually
      (fun i => gamma <= (g (coord i)).1.cof) :=
    (Ideal.pushforward_eventually_iff K coord _).mp hCofEventually
  have hCofEventuallyConditional : NS.Eventually
      (fun i => P i -> gamma <= (g (coord i)).1.cof) := by
    change NS.Small (fun i => Not (P i -> gamma <= (g (coord i)).1.cof))
    exact NS.subset_small hCofEventuallySource (by
      intro i hi
      refine ⟨?_, ?_⟩
      · intro hCof
        exact hi (fun _ => hCof)
      · by_contra hNotPi
        exact hi (fun hPi => False.elim (hNotPi hPi)))
  obtain ⟨D, hDClub, hD⟩ :=
    (nonstationaryIdeal_eventually_iff_contains_club
      hSourceCofNe _).mp hCofEventuallyConditional
  obtain ⟨i, hiT, hiD⟩ := hTStationary D hDClub
  have hiS : i ∈ S := hTSub hiT
  have hSmallCof : (g (coord i)).1.cof < gamma := by
    have hAtRank := (hRankSpec i hiS).2
    rw [hRankConst hiT] at hAtRank
    change (g (coord i)).1.cof < Cardinal.aleph (f j0).1 at hAtRank
    have hFj0Fi0 : (f j0).1 < (f i0).1 := hNormal.strictMono hj0i0
    exact hAtRank.trans (Cardinal.aleph_lt_aleph.mpr
      (hFj0Fi0.trans (lt_add_one (f i0).1)))
  exact (not_lt_of_ge (hD i hiD hiS.1.1.2)) hSmallCof

#print axioms
  successorAlephFundamental_eventually_top_of_localized_closedExactUpperBound

/-! The unlocalized stationary/Fodor conclusion is the special case of the
preceding theorem on the full source set. -/
theorem successorAlephFundamental_eventually_top_of_closedExactUpperBound
    (eta : Ordinal.{u})
    (hEtaLimit : Order.IsSuccLimit eta)
    (hEtaCof : Cardinal.aleph0 < eta.cof)
    (hPower : (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta)
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hFundamental : Ordinal.IsFundamentalSeq f)
    (hNormal : Order.IsNormal f)
    (d : Set.Iio (Cardinal.aleph (eta + 1)).ord ->
      ProductElement (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        ((nonstationaryIdeal (Set.Iio eta.cof.ord)
          (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
            (successorAlephFundamentalCardinalIndex eta f))))
    (hIncreasing : forall {alpha beta}, alpha < beta ->
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        ((nonstationaryIdeal (Set.Iio eta.cof.ord)
          (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
            (successorAlephFundamentalCardinalIndex eta f))).eventuallyPointwiseLt
        (d alpha) (d beta))
    (hRapid : forall gamma : Cardinal.{u}, Cardinal.aleph0 < gamma ->
      gamma < Cardinal.aleph eta ->
        CardinalProductGammaRapid
          ((nonstationaryIdeal (Set.Iio eta.cof.ord)
            (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
              (successorAlephFundamentalCardinalIndex eta f))
          gamma (Cardinal.aleph (eta + 1)) d)
    (g : CardinalProductClosedElement
      (successorAlephCardSet (Set.Iio eta)))
    (hExact : CardinalProductClosedExactUpperBound
      ((nonstationaryIdeal (Set.Iio eta.cof.ord)
        (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
          (successorAlephFundamentalCardinalIndex eta f)) d g) :
    ((nonstationaryIdeal (Set.Iio eta.cof.ord)
      (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
        (successorAlephFundamentalCardinalIndex eta f)).Eventually
      (fun k => k.1.ord <= (g k).1) := by
  let NS := nonstationaryIdeal (Set.Iio eta.cof.ord)
    (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)
  have hLocal :=
    successorAlephFundamental_eventually_top_of_localized_closedExactUpperBound
      eta hEtaLimit hEtaCof hPower hFundamental hNormal (fun _ => True)
  rw [Ideal.localize_true] at hLocal
  exact hLocal d hIncreasing hRapid g hExact

#print axioms
  successorAlephFundamental_eventually_top_of_closedExactUpperBound

/-! The ordinal index whose successor aleph is represented by a coordinate
of `successorAlephCardSet (Iio eta)`. -/
noncomputable def successorAlephCardinalIndexRank
    (eta : Ordinal.{u})
    (k : CardinalIndex (successorAlephCardSet (Set.Iio eta))) :
    Ordinal.{u} :=
  Classical.choose k.2

theorem successorAlephCardinalIndexRank_value
    (eta : Ordinal.{u})
    (k : CardinalIndex (successorAlephCardSet (Set.Iio eta))) :
    k.1 = Cardinal.aleph (successorAlephCardinalIndexRank eta k + 1) :=
  (Classical.choose_spec k.2).2

theorem successorAlephCardinalIndexRank_fundamental
    (eta : Ordinal.{u})
    (f : Set.Iio eta.cof.ord -> Set.Iio eta)
    (j : Set.Iio eta.cof.ord) :
    successorAlephCardinalIndexRank eta
      (successorAlephFundamentalCardinalIndex eta f j) = (f j).1 := by
  have h := successorAlephCardinalIndexRank_value eta
    (successorAlephFundamentalCardinalIndex eta f j)
  change Cardinal.aleph ((f j).1 + 1) =
    Cardinal.aleph
      (successorAlephCardinalIndexRank eta
        (successorAlephFundamentalCardinalIndex eta f j) + 1) at h
  have hs := Cardinal.aleph.injective h
  apply (Ordinal.add_right_cancel 1).mp
  simpa using hs.symm

#print axioms successorAlephCardinalIndexRank_fundamental

/-! The fundamental-sequence product is directed for every family smaller
than the singular limit `aleph eta`.  The coordinate cardinals eventually
dominate the family's cardinality, and regularity then supplies a strict
coordinatewise diagonal upper bound on that tail. -/
theorem successorAlephFundamental_pointwiseStrictDirectedBelow_aleph
    (eta : Ordinal.{u})
    (hEtaLimit : Order.IsSuccLimit eta)
    (hEtaCof : Cardinal.aleph0 < eta.cof)
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hFundamental : Ordinal.IsFundamentalSeq f) :
    ReducedProductFrame.PointwiseStrictDirectedBelow
      (cardinalProductFrame
      (successorAlephCardSet (Set.Iio eta))
      ((nonstationaryIdeal (Set.Iio eta.cof.ord)
        (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
          (successorAlephFundamentalCardinalIndex eta f)))
      (Cardinal.aleph eta) := by
  apply
    cardinalProductFrame_pointwiseStrictDirectedBelow_of_eventually_coordinate
      (successorAlephCardSet_regulars (Set.Iio eta))
  intro ι hSmall
  obtain ⟨B, hB, hBound⟩ :=
    successorAlephFundamental_eventually_unbounded
      eta hEtaLimit hEtaCof hFundamental (Cardinal.mk ι) hSmall
  exact ((nonstationaryIdeal (Set.Iio eta.cof.ord)
    (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
      (successorAlephFundamentalCardinalIndex eta f)).eventually_mono
        hB hBound

#print axioms
  successorAlephFundamental_pointwiseStrictDirectedBelow_aleph

/-! The stronger directedness used by Theorem 24.16.  A family of size below
`aleph (eta+1)` has size at most `aleph eta`, so encode it into the initial
ordinal `omega eta`.  At coordinate `aleph (beta+1)` only the members whose
codes lie below `omega beta` are diagonalized.  That layer has size at most
`aleph beta`, while every fixed code is included on a tail of the fundamental
sequence.  The nonstationary ideal regards that tail as eventual. -/
theorem successorAlephFundamental_pointwiseStrictDirectedBelow_alephSucc
    (eta : Ordinal.{u})
    (hEtaLimit : Order.IsSuccLimit eta)
    (hEtaCof : Cardinal.aleph0 < eta.cof)
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hFundamental : Ordinal.IsFundamentalSeq f) :
    ReducedProductFrame.PointwiseStrictDirectedBelow
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        ((nonstationaryIdeal (Set.Iio eta.cof.ord)
          (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
            (successorAlephFundamentalCardinalIndex eta f)))
      (Cardinal.aleph (eta + 1)) := by
  classical
  intro ι hSmall d
  have hιLe : Cardinal.mk ι <= Cardinal.aleph eta := by
    rw [← Cardinal.succ_aleph] at hSmall
    exact Order.lt_succ_iff.mp hSmall
  have hιLeMk : Cardinal.mk ι <=
      Cardinal.mk (Cardinal.aleph eta).ord.ToType := by
    simpa only [Cardinal.mk_ord_toType] using hιLe
  let e : ι ↪ (Cardinal.aleph eta).ord.ToType :=
    Classical.choice hιLeMk
  let rank : ι -> Ordinal.{u} := fun i =>
    Ordinal.typein
      (fun a b : (Cardinal.aleph eta).ord.ToType => a < b) (e i)
  let B : CardinalIndex (successorAlephCardSet (Set.Iio eta)) -> ι -> Prop :=
    fun k i => rank i <
      Ordinal.omega (successorAlephCardinalIndexRank eta k)
  apply cardinalProductFrame_exists_eventuallyPointwiseLt_of_layered
    (successorAlephCardSet_regulars (Set.Iio eta)) B
  · intro k
    let code : {i : ι // B k i} ->
        (Ordinal.omega
          (successorAlephCardinalIndexRank eta k)).ToType :=
      fun i => Ordinal.ToType.mk ⟨rank i.1, i.2⟩
    have hCode : Function.Injective code := by
      intro a b hab
      apply Subtype.ext
      apply e.injective
      apply Ordinal.typein_injective
        (fun a b : (Cardinal.aleph eta).ord.ToType => a < b)
      exact congrArg Subtype.val ((Ordinal.ToType.mk).injective hab)
    calc
      Cardinal.mk {i : ι // B k i} <=
          Cardinal.mk
            (Ordinal.omega
              (successorAlephCardinalIndexRank eta k)).ToType :=
        Cardinal.mk_le_of_injective hCode
      _ = Cardinal.aleph
          (successorAlephCardinalIndexRank eta k) := by
        rw [Cardinal.mk_toType, Ordinal.card_omega]
      _ < Cardinal.aleph
          (successorAlephCardinalIndexRank eta k + 1) :=
        Cardinal.aleph_lt_aleph.mpr
          (lt_add_one (successorAlephCardinalIndexRank eta k))
      _ = k.1 := (successorAlephCardinalIndexRank_value eta k).symm
  · intro i
    rw [Ideal.pushforward_eventually_iff]
    apply (nonstationaryIdeal_eventually_iff_contains_club
      (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof) _).mpr
    have hrank : rank i < Ordinal.omega eta := by
      rw [← Cardinal.ord_aleph]
      exact Ordinal.typein_lt_self (e i)
    have homega : Ordinal.omega eta =
        ⨆ beta : Set.Iio eta, Ordinal.omega beta.1 :=
      Ordinal.isNormal_omega.apply_of_isSuccLimit hEtaLimit
    rw [homega] at hrank
    obtain ⟨beta, hRankBeta⟩ := exists_lt_of_lt_ciSup' hrank
    obtain ⟨fi, ⟨j, rfl⟩, hBetaFi⟩ :=
      hFundamental.isCofinal_range beta
    refine ⟨Set.Ici j, isClub_Ici j, ?_⟩
    intro l hjl
    change rank i < Ordinal.omega
      (successorAlephCardinalIndexRank eta
        (successorAlephFundamentalCardinalIndex eta f l))
    rw [show successorAlephCardinalIndexRank eta
      (successorAlephFundamentalCardinalIndex eta f l) = (f l).1 from
        successorAlephCardinalIndexRank_fundamental eta f l]
    exact hRankBeta.trans_le (Ordinal.omega_strictMono.monotone
      (hBetaFi.trans (hFundamental.strictMono.monotone hjl)))

#print axioms
  successorAlephFundamental_pointwiseStrictDirectedBelow_alephSucc

/-! This is the lower-bound half of Theorem 24.16.  Eventual coordinate
unboundedness forces any regular scale length above `aleph eta`; the power
hypothesis makes `aleph eta` singular, so the successor-cardinal property
upgrades that strict inequality to `aleph (eta+1) <= theta`.  No scale is
constructed here. -/
theorem successorAlephFundamental_regularScaleLength_ge_alephSucc
    (eta : Ordinal.{u})
    (hEtaLimit : Order.IsSuccLimit eta)
    (hEtaCof : Cardinal.aleph0 < eta.cof)
    (hPower : (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta)
    {f : Set.Iio eta.cof.ord -> Set.Iio eta}
    (hFundamental : Ordinal.IsFundamentalSeq f)
    {theta : Cardinal.{u}}
    (hThetaRegular : Cardinal.IsRegular theta)
    (hScale : HasScaleWitness
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        ((nonstationaryIdeal (Set.Iio eta.cof.ord)
          (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
            (successorAlephFundamentalCardinalIndex eta f)))
      (cardinalScaleLength theta)) :
    Cardinal.aleph (eta + 1) <= theta := by
  let hSourceCofNe : Order.cof (Set.Iio eta.cof.ord) ≠
      Cardinal.aleph0 :=
    cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof
  let NS : Ideal (Set.Iio eta.cof.ord) :=
    nonstationaryIdeal (Set.Iio eta.cof.ord) hSourceCofNe
  let coord := successorAlephFundamentalCardinalIndex eta f
  letI : Nonempty (Set.Iio eta.cof.ord) :=
    ⟨⟨0, Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans hEtaCof)⟩⟩
  have hProper : (NS.pushforward coord).IsProper :=
    (nonstationaryIdeal_isProper hSourceCofNe).pushforward coord
  have hAlephEtaSingular : (Cardinal.aleph eta).IsSingular := by
    rw [Cardinal.isSingular_aleph_iff]
    exact ⟨hEtaLimit, (Cardinal.cantor eta.cof).trans hPower⟩
  have hGt : Cardinal.aleph eta < theta := by
    apply cardinalProductFrame_cardinalScaleLength_gt_of_eventually_unbounded_of_not_isRegular
      (successorAlephCardSet_regulars (Set.Iio eta)) hProper hScale
    · exact successorAlephFundamental_eventually_unbounded
        eta hEtaLimit hEtaCof hFundamental
    · exact hAlephEtaSingular.not_isRegular
    · exact hThetaRegular
  rw [← Cardinal.succ_aleph]
  exact Order.succ_le_iff.mpr hGt

#print axioms
  successorAlephFundamental_regularScaleLength_ge_alephSucc

/-! The predicates on the literal cofinality index have exactly the powerset
cardinality appearing in Theorem 24.16.  The universe lift is unavoidable
because an ordinal initial segment lives one universe above its cardinal. -/
theorem mk_predicates_Iio_cofOrd
    (eta : Ordinal.{u}) :
    Cardinal.mk (Set.Iio eta.cof.ord -> Prop) =
      Cardinal.lift.{u + 1} ((2 : Cardinal.{u}) ^ eta.cof) := by
  change Cardinal.mk (Set (Set.Iio eta.cof.ord)) = _
  rw [Cardinal.mk_set, Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
  exact (Cardinal.lift_two_power eta.cof).symm

#print axioms mk_predicates_Iio_cofOrd

theorem mk_predicates_Iio_cofOrd_le_lift
    (eta : Ordinal.{u})
    {theta : Cardinal.{u}}
    (hPower : (2 : Cardinal.{u}) ^ eta.cof <= theta) :
    Cardinal.mk (Set.Iio eta.cof.ord -> Prop) <=
      Cardinal.lift.{u + 1} theta := by
  rw [mk_predicates_Iio_cofOrd]
  exact Cardinal.lift_le.mpr hPower

#print axioms mk_predicates_Iio_cofOrd_le_lift

/-! The source-sized exact-upper-bound package needed from Jech Lemma 24.10
for the fundamental-sequence product.  The power hypothesis is the one
available in the local Theorem 24.16 application. -/
def SuccessorAlephLocalLemma2410ExactUpperBounds : Prop :=
  forall eta : Ordinal.{u},
    forall hEtaCof : Cardinal.aleph0 < eta.cof,
    forall _hPower : (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta,
    forall f : Set.Iio eta.cof.ord -> Set.Iio eta,
      Ordinal.IsFundamentalSeq f ->
      Order.IsNormal f ->
      let A := successorAlephCardSet (Set.Iio eta)
      let J := (nonstationaryIdeal (Set.Iio eta.cof.ord)
        (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
          (successorAlephFundamentalCardinalIndex eta f)
      let theta := Cardinal.aleph (eta + 1)
      CardinalProductClosedExactUpperBoundPrinciple A J theta /\
        forall X : CardinalIndex A -> Prop,
          (J.localize X).IsProper ->
          CardinalProductClosedExactUpperBoundPrinciple A (J.localize X) theta

/-! Lemma 24.10 for the pushed nonstationary product and all its
localizations.  The W-tree hull in `CanonicalProduct` is branched by the
literal cofinality source, so its code cardinal is at most
`2 ^ eta.cof` even though the ambient cardinal set can be larger. -/
theorem successorAlephLocalLemma2410ExactUpperBounds :
    SuccessorAlephLocalLemma2410ExactUpperBounds.{u} := by
  intro eta hEtaCof hPower f hFundamental hNormal
  let source := Set.Iio eta.cof.ord
  let hSourceCofNe : Order.cof source ≠ Cardinal.aleph0 :=
    cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof
  let NS : Ideal source := nonstationaryIdeal source hSourceCofNe
  let A := successorAlephCardSet (Set.Iio eta)
  let coord := successorAlephFundamentalCardinalIndex eta f
  let theta := Cardinal.aleph (eta + 1)
  have hSourceMk : Cardinal.mk source =
      Cardinal.lift.{u + 1} eta.cof := by
    dsimp only [source]
    rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
  have hSourceInfinite : Cardinal.aleph0 <= Cardinal.mk source := by
    rw [hSourceMk]
    calc
      Cardinal.aleph0.{u + 1} =
          Cardinal.lift.{u + 1, u} Cardinal.aleph0.{u} :=
        (Cardinal.lift_aleph0.{u + 1, u}).symm
      _ <= Cardinal.lift.{u + 1, u} eta.cof :=
        Cardinal.lift_le.mpr hEtaCof.le
  have hThetaRegular : Cardinal.IsRegular theta :=
    Cardinal.isRegular_aleph_add_one eta
  have hThetaUncountable : Cardinal.aleph0 < theta := by
    exact Cardinal.aleph0_lt_aleph.mpr (by simp)
  have hSourcePower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk source <
      Cardinal.lift.{u + 1} theta := by
    rw [hSourceMk, ← Cardinal.lift_two_power]
    exact Cardinal.lift_lt.mpr
      (hPower.trans (Cardinal.aleph_lt_aleph.mpr (lt_add_one eta)))
  constructor
  · simpa only [A, NS, coord, theta, source, hSourceCofNe] using
      (pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
        (J := NS) coord hSourceInfinite hThetaRegular hThetaUncountable
          hSourcePower)
  · intro X _hProper
    simpa only [A, NS, coord, theta, source, hSourceCofNe] using
      (localizedPushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
        (J := NS) coord hSourceInfinite hThetaRegular hThetaUncountable
          hSourcePower X)

#print axioms successorAlephLocalLemma2410ExactUpperBounds

/-! The true-cofinality conclusion used from Theorem 24.16 after transporting
the continuous cofinal sequence to the ordinal interval below `eta`.  For
every ultrafilter-dual ideal containing all clubs, the successor-aleph product
has true cofinality `aleph (eta + 1)`. -/
def SuccessorAlephLocalTheorem2416UltrafilterTcf : Prop :=
  forall eta : Ordinal.{u}, Order.IsSuccLimit eta ->
    Cardinal.aleph0 < eta.cof ->
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    forall J : Ideal (Set.Iio eta),
      J.IsUltrafilterDual ->
      (forall C : Set (Set.Iio eta), IsClub C ->
        J.Eventually (fun i => i ∈ C)) ->
      HasTrueCofinality
        (cardinalProductFrame
          (successorAlephCardSet (Set.Iio eta))
          (J.pushforward (successorAlephIioCardinalIndex eta)))
        (cardinalScaleLength (Cardinal.aleph (eta + 1)))

/-! Source-scale form of Theorem 24.16.  It asks for one pointwise-strict,
cofinal scale modulo the nonstationary ideal.  Unlike the preceding
club-ultrafilter formulation, it does not quantify over ultrafilters; the
next theorem proves that transport. -/
def SuccessorAlephLocalTheorem2416NonstationaryScale : Prop :=
  forall eta : Ordinal.{u},
    forall (_hEtaLimit : Order.IsSuccLimit eta),
    forall hEtaCof : Cardinal.aleph0 < eta.cof,
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    Nonempty (PointwiseStrictScale
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        ((nonstationaryIdeal (Set.Iio eta)
          (cof_Iio_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
            (successorAlephIioCardinalIndex eta)))
      (cardinalScaleLength (Cardinal.aleph (eta + 1))))

/-! Source-faithful scale form of Theorem 24.16.  Its index type is
`Iio (cf eta).ord`, and it applies to every continuous normal fundamental
sequence into `eta`.  The only assumed mathematical content is the
pointwise-strict cofinal scale modulo the nonstationary ideal on that source
index; existence of a normal fundamental sequence is proved independently. -/
def SuccessorAlephLocalTheorem2416FundamentalSequenceScale : Prop :=
  forall eta : Ordinal.{u},
    forall (_hEtaLimit : Order.IsSuccLimit eta),
    forall hEtaCof : Cardinal.aleph0 < eta.cof,
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    forall f : Set.Iio eta.cof.ord -> Set.Iio eta,
      Ordinal.IsFundamentalSeq f ->
      Order.IsNormal f ->
      Nonempty (PointwiseStrictScale
        (cardinalProductFrame
          (successorAlephCardSet (Set.Iio eta))
          ((nonstationaryIdeal (Set.Iio eta.cof.ord)
            (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
              (successorAlephFundamentalCardinalIndex eta f)))
        (cardinalScaleLength (Cardinal.aleph (eta + 1))))

/-! Source endpoint immediately before cofinality in the proof of Theorem
24.16.  Lemma 24.10 supplies the closed exact upper bound, while Lemma
24.14 and Corollary 24.15 force it to reach the coordinate top on an
eventual set.  The next theorem turns exactly those two conclusions into the
cofinal family used by the already verified strictification step. -/
def SuccessorAlephLocalTheorem2416ExactUpperBoundAtTop : Prop :=
  forall eta : Ordinal.{u},
    forall (_hEtaLimit : Order.IsSuccLimit eta),
    forall hEtaCof : Cardinal.aleph0 < eta.cof,
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    forall f : Set.Iio eta.cof.ord -> Set.Iio eta,
      Ordinal.IsFundamentalSeq f ->
      Order.IsNormal f ->
      let A := successorAlephCardSet (Set.Iio eta)
      let J := (nonstationaryIdeal (Set.Iio eta.cof.ord)
        (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
          (successorAlephFundamentalCardinalIndex eta f)
      exists d : (cardinalScaleLength
          (Cardinal.aleph (eta + 1))).Level ->
          ProductElement (cardinalProductFrame A J),
        exists g : CardinalProductClosedElement A,
          CardinalProductClosedExactUpperBound J d g /\
            J.Eventually (fun k => k.1.ord <= (g k).1)

/-! The remaining cofinal-family core of Theorem 24.16.  Directedness of the
product is now proved above, so the only source input here is a cofinal family
of the target successor length; the next theorem recursively strictifies it. -/
def SuccessorAlephLocalTheorem2416CofinalFamily : Prop :=
  forall eta : Ordinal.{u},
    forall (_hEtaLimit : Order.IsSuccLimit eta),
    forall hEtaCof : Cardinal.aleph0 < eta.cof,
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    forall f : Set.Iio eta.cof.ord -> Set.Iio eta,
      Ordinal.IsFundamentalSeq f ->
      Order.IsNormal f ->
      exists d : (cardinalScaleLength
          (Cardinal.aleph (eta + 1))).Level ->
        ProductElement
          (cardinalProductFrame
            (successorAlephCardSet (Set.Iio eta))
            ((nonstationaryIdeal (Set.Iio eta.cof.ord)
              (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
                (successorAlephFundamentalCardinalIndex eta f))),
        (cardinalProductFrame
          (successorAlephCardSet (Set.Iio eta))
          ((nonstationaryIdeal (Set.Iio eta.cof.ord)
            (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
              (successorAlephFundamentalCardinalIndex eta f))).IsCofinalFamily d

theorem successorAlephLocalTheorem2416CofinalFamily_of_exactUpperBoundAtTop
    (hExactTop :
      SuccessorAlephLocalTheorem2416ExactUpperBoundAtTop.{u}) :
    SuccessorAlephLocalTheorem2416CofinalFamily.{u} := by
  intro eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  obtain ⟨d, g, hExact, hTop⟩ :=
    hExactTop eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  exact ⟨d, hExact.isCofinalFamily_of_eventually_top hTop⟩

#print axioms
  successorAlephLocalTheorem2416CofinalFamily_of_exactUpperBoundAtTop

theorem successorAlephLocalTheorem2416FundamentalSequenceScale_of_cofinalFamily
    (hCofinal : SuccessorAlephLocalTheorem2416CofinalFamily.{u}) :
    SuccessorAlephLocalTheorem2416FundamentalSequenceScale.{u} := by
  intro eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  obtain ⟨d, hd⟩ :=
    hCofinal eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  have hRegular : Cardinal.IsRegular (Cardinal.aleph (eta + 1)) :=
    Cardinal.isRegular_aleph_add_one eta
  exact pointwiseStrictScale_of_directedBelow_of_cofinalFamily
    hRegular
    (successorAlephFundamental_pointwiseStrictDirectedBelow_alephSucc
      eta hEtaLimit hEtaCof hFundamental)
    d hd

#print axioms
  successorAlephLocalTheorem2416FundamentalSequenceScale_of_cofinalFamily

/-! Full assembly of the source proof of Theorem 24.16 from Lemma 24.10.
Corollary 24.12 has three branches.  A successor-directed branch supports the
rapid recursion directly; a scale branch is already the conclusion; and in
the split branch the same rapid/exact-bound argument constructs a scale on
the directed side, after which the two localized scales are joined into one
global cofinal family and strictified. -/
theorem successorAlephLocalTheorem2416FundamentalSequenceScale_of_lemma2410
    (hLemma : SuccessorAlephLocalLemma2410ExactUpperBounds.{u}) :
    SuccessorAlephLocalTheorem2416FundamentalSequenceScale.{u} := by
  intro eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  let source := Set.Iio eta.cof.ord
  let hSourceCofNe : Order.cof source ≠ Cardinal.aleph0 :=
    cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof
  let NS : Ideal source := nonstationaryIdeal source hSourceCofNe
  let coord := successorAlephFundamentalCardinalIndex eta f
  let A := successorAlephCardSet (Set.Iio eta)
  let J := NS.pushforward coord
  let theta := Cardinal.aleph (eta + 1)
  letI : LinearOrder (cardinalScaleLength theta).Level := by
    dsimp only [cardinalScaleLength]
    infer_instance
  have hThetaRegular : Cardinal.IsRegular theta :=
    Cardinal.isRegular_aleph_add_one eta
  have hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
      theta := by
    simpa only [A, J, NS, coord, theta, source, hSourceCofNe] using
      successorAlephFundamental_pointwiseStrictDirectedBelow_alephSucc
        eta hEtaLimit hEtaCof hFundamental
  obtain ⟨hExact, hExactLocalized⟩ :=
    hLemma eta hEtaCof hPower f hFundamental hNormal
  have hExact' : CardinalProductClosedExactUpperBoundPrinciple A J theta := by
    simpa only [A, J, NS, coord, theta, source, hSourceCofNe] using hExact
  have hExactLocalized' : forall X : CardinalIndex A -> Prop,
      (J.localize X).IsProper ->
      CardinalProductClosedExactUpperBoundPrinciple A (J.localize X) theta := by
    simpa only [A, J, NS, coord, theta, source, hSourceCofNe] using
      hExactLocalized
  obtain ⟨d0, _⟩ := hDirected PEmpty (by
    simp only [Cardinal.mk_pempty, theta]
    exact hThetaRegular.pos) (fun z => nomatch z)
  have hPredicates : Cardinal.mk (source -> Prop) <=
      Cardinal.lift.{u + 1} theta := by
    apply mk_predicates_Iio_cofOrd_le_lift eta
    exact hPower.le.trans
      (Cardinal.aleph_lt_aleph.mpr (lt_add_one eta)).le
  rcases pointwiseStrictCorollary2412_of_pushforward_exactUpperBounds
      hThetaRegular hPredicates hDirected hExact' hExactLocalized' d0 with
    hSucc | hScale | hSplit
  · obtain ⟨d, hIncreasing, hRapid⟩ :=
      successorAlephFundamental_exists_strictIncreasing_rapidBelow_of_directed
        eta hEtaLimit hEtaCof hFundamental J (fun _ h => h) hSucc
    let e : Set.Iio theta.ord ≃o (cardinalScaleLength theta).Level :=
      Ordinal.ToType.mk
    let dLevel : (cardinalScaleLength theta).Level ->
        ProductElement (cardinalProductFrame A J) := fun alpha =>
      d (e.symm alpha)
    have hIncreasingLevel : forall {alpha beta},
        (cardinalScaleLength theta).lt alpha beta ->
          (cardinalProductFrame A J).eventuallyPointwiseLt
            (dLevel alpha) (dLevel beta) := by
      intro alpha beta hab
      exact hIncreasing (e.symm.strictMono hab)
    obtain ⟨g, hExactLevel⟩ := hExact' dLevel hIncreasingLevel
    have hExactD : CardinalProductClosedExactUpperBound J d g := by
      have hReindexed := hExactLevel.reindex e.symm.toEquiv
      convert hReindexed using 1
      funext k
      change d k = d (e.symm (e k))
      rw [e.symm_apply_apply]
    have hTop := successorAlephFundamental_eventually_top_of_closedExactUpperBound
      eta hEtaLimit hEtaCof hPower hFundamental hNormal
      d hIncreasing hRapid g hExactD
    exact pointwiseStrictScale_of_directedBelow_of_cofinalFamily
      hThetaRegular hDirected dLevel
      (hExactLevel.isCofinalFamily_of_eventually_top hTop)
  · exact hScale
  · obtain ⟨X, Y, hCover, _hXProper, hYProper, ⟨sX⟩, hSuccY⟩ := hSplit
    let P : source -> Prop := fun i => Y (coord i)
    have hIdealEq : J.localize Y = (NS.localize P).pushforward coord := by
      exact NS.pushforward_localize coord Y
    have hDirectedY :
        (cardinalProductFrame A (J.localize Y)).PointwiseStrictDirectedBelow
          theta := by
      intro iota hSmall q
      exact hSuccY iota (hSmall.trans (Order.lt_succ theta)) q
    obtain ⟨d, hIncreasing, hRapid⟩ :=
      successorAlephFundamental_exists_strictIncreasing_rapidBelow_of_directed
        eta hEtaLimit hEtaCof hFundamental (J.localize Y)
          (J.le_localize Y) hSuccY
    let e : Set.Iio theta.ord ≃o (cardinalScaleLength theta).Level :=
      Ordinal.ToType.mk
    let dLevel : (cardinalScaleLength theta).Level ->
        ProductElement (cardinalProductFrame A (J.localize Y)) := fun alpha =>
      d (e.symm alpha)
    have hIncreasingLevel : forall {alpha beta},
        (cardinalScaleLength theta).lt alpha beta ->
          (cardinalProductFrame A (J.localize Y)).eventuallyPointwiseLt
            (dLevel alpha) (dLevel beta) := by
      intro alpha beta hab
      exact hIncreasing (e.symm.strictMono hab)
    obtain ⟨g, hExactLevel⟩ :=
      hExactLocalized' Y hYProper dLevel hIncreasingLevel
    have hExactD : CardinalProductClosedExactUpperBound
        (J.localize Y) d g := by
      have hReindexed := hExactLevel.reindex e.symm.toEquiv
      convert hReindexed using 1
      funext k
      change d k = d (e.symm (e k))
      rw [e.symm_apply_apply]
    have hIncreasing' : forall {alpha beta}, alpha < beta ->
        (cardinalProductFrame A ((NS.localize P).pushforward coord)).eventuallyPointwiseLt
          (d alpha) (d beta) := by
      rw [← hIdealEq]
      exact hIncreasing
    have hRapid' : forall gamma : Cardinal.{u}, Cardinal.aleph0 < gamma ->
        gamma < Cardinal.aleph eta ->
          CardinalProductGammaRapid ((NS.localize P).pushforward coord)
            gamma theta d := by
      rw [← hIdealEq]
      exact hRapid
    have hExactD' : CardinalProductClosedExactUpperBound
        ((NS.localize P).pushforward coord) d g := by
      rw [← hIdealEq]
      exact hExactD
    have hTop' :=
      successorAlephFundamental_eventually_top_of_localized_closedExactUpperBound
        eta hEtaLimit hEtaCof hPower hFundamental hNormal P
          d hIncreasing' hRapid' g hExactD'
    have hTop : (J.localize Y).Eventually
        (fun k => k.1.ord <= (g k).1) := by
      rw [hIdealEq]
      exact hTop'
    have hCofinalY := hExactLevel.isCofinalFamily_of_eventually_top hTop
    obtain ⟨sY⟩ := pointwiseStrictScale_of_directedBelow_of_cofinalFamily
      hThetaRegular hDirectedY dLevel hCofinalY
    obtain ⟨q, hq⟩ :=
      exists_cardinalProduct_cofinalFamily_of_localizedScales_cover
        hCover sX sY
    exact pointwiseStrictScale_of_directedBelow_of_cofinalFamily
      hThetaRegular hDirected q hq

#print axioms
  successorAlephLocalTheorem2416FundamentalSequenceScale_of_lemma2410

/-! The local Theorem 24.16 scale is now unconditional under its displayed
source hypotheses: Lemma 24.10 is supplied by the source-sized W-tree hull. -/
theorem successorAlephLocalTheorem2416FundamentalSequenceScale :
    SuccessorAlephLocalTheorem2416FundamentalSequenceScale.{u} :=
  successorAlephLocalTheorem2416FundamentalSequenceScale_of_lemma2410
    successorAlephLocalLemma2410ExactUpperBounds

#print axioms
  successorAlephLocalTheorem2416FundamentalSequenceScale

/-! Upper-bound half of the source-faithful Theorem 24.16 assertion.  It asks
only for some regular pointwise-strict cofinal scale whose length is at most
`aleph (eta+1)`.  The proved eventual-unboundedness theorem forces the reverse
inequality, so the following theorem recovers the exact scale length. -/
def SuccessorAlephLocalTheorem2416ScaleUpperBound : Prop :=
  forall eta : Ordinal.{u},
    forall (_hEtaLimit : Order.IsSuccLimit eta),
    forall hEtaCof : Cardinal.aleph0 < eta.cof,
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    forall f : Set.Iio eta.cof.ord -> Set.Iio eta,
      Ordinal.IsFundamentalSeq f ->
      Order.IsNormal f ->
      exists theta : Cardinal.{u},
        Cardinal.IsRegular theta /\
        theta <= Cardinal.aleph (eta + 1) /\
        Nonempty (PointwiseStrictScale
          (cardinalProductFrame
            (successorAlephCardSet (Set.Iio eta))
            ((nonstationaryIdeal (Set.Iio eta.cof.ord)
              (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
                (successorAlephFundamentalCardinalIndex eta f)))
          (cardinalScaleLength theta))

/-! A constructive decomposition of the upper-bound half of Theorem 24.16.
Instead of assuming the scale itself, it asks for the two ingredients used by
the standard recursion: every family of size below `theta` has an eventual
pointwise-strict upper bound, and there is a cofinal family of length `theta`.
The next theorem performs the well-founded recursion and produces the scale. -/
def SuccessorAlephLocalTheorem2416DirectedCofinalUpperBound : Prop :=
  forall eta : Ordinal.{u},
    forall (_hEtaLimit : Order.IsSuccLimit eta),
    forall hEtaCof : Cardinal.aleph0 < eta.cof,
    (2 : Cardinal.{u}) ^ eta.cof < Cardinal.aleph eta ->
    forall f : Set.Iio eta.cof.ord -> Set.Iio eta,
      Ordinal.IsFundamentalSeq f ->
      Order.IsNormal f ->
      exists theta : Cardinal.{u},
        Cardinal.IsRegular theta /\
        theta <= Cardinal.aleph (eta + 1) /\
        let F := cardinalProductFrame
          (successorAlephCardSet (Set.Iio eta))
          ((nonstationaryIdeal (Set.Iio eta.cof.ord)
            (cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof)).pushforward
              (successorAlephFundamentalCardinalIndex eta f))
        F.PointwiseStrictDirectedBelow theta /\
          exists d : (cardinalScaleLength theta).Level -> ProductElement F,
            F.IsCofinalFamily d

theorem successorAlephLocalTheorem2416ScaleUpperBound_of_directedCofinalUpperBound
    (hUpper :
      SuccessorAlephLocalTheorem2416DirectedCofinalUpperBound.{u}) :
    SuccessorAlephLocalTheorem2416ScaleUpperBound.{u} := by
  intro eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  obtain ⟨theta, hThetaRegular, hThetaLe, hDirected, d, hCofinal⟩ :=
    hUpper eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  exact ⟨theta, hThetaRegular, hThetaLe,
    pointwiseStrictScale_of_directedBelow_of_cofinalFamily
      hThetaRegular hDirected d hCofinal⟩

#print axioms
  successorAlephLocalTheorem2416ScaleUpperBound_of_directedCofinalUpperBound

theorem successorAlephLocalTheorem2416FundamentalSequenceScale_of_scaleUpperBound
    (hUpper : SuccessorAlephLocalTheorem2416ScaleUpperBound.{u}) :
    SuccessorAlephLocalTheorem2416FundamentalSequenceScale.{u} := by
  intro eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  obtain ⟨theta, hThetaRegular, hThetaLe, ⟨s⟩⟩ :=
    hUpper eta hEtaLimit hEtaCof hPower f hFundamental hNormal
  let hSourceCofNe : Order.cof (Set.Iio eta.cof.ord) ≠
      Cardinal.aleph0 :=
    cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof
  let NS : Ideal (Set.Iio eta.cof.ord) :=
    nonstationaryIdeal (Set.Iio eta.cof.ord) hSourceCofNe
  let coord := successorAlephFundamentalCardinalIndex eta f
  letI : Nonempty (Set.Iio eta.cof.ord) :=
    ⟨⟨0, Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans hEtaCof)⟩⟩
  have hProper : (NS.pushforward coord).IsProper :=
    (nonstationaryIdeal_isProper hSourceCofNe).pushforward coord
  have hScaleWitness : HasScaleWitness
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        (NS.pushforward coord))
      (cardinalScaleLength theta) := by
    refine ⟨?_⟩
    have hRaw := s.toScale hProper
    simpa only [NS, coord, hSourceCofNe] using hRaw
  have hLower : Cardinal.aleph (eta + 1) <= theta :=
    successorAlephFundamental_regularScaleLength_ge_alephSucc
      eta hEtaLimit hEtaCof hPower hFundamental hThetaRegular (by
        simpa only [NS, coord, hSourceCofNe] using hScaleWitness)
  have hEq : theta = Cardinal.aleph (eta + 1) :=
    le_antisymm hThetaLe hLower
  rw [← hEq]
  exact ⟨s⟩

#print axioms
  successorAlephLocalTheorem2416FundamentalSequenceScale_of_scaleUpperBound

/-! A pointwise-strict nonstationary-ideal scale transports to every
club-ultrafilter extension.  Regularity of the target length then turns the
transported scale into a true-cofinality witness. -/
theorem successorAlephLocalTheorem2416UltrafilterTcf_of_nonstationaryScale
    (h2416 : SuccessorAlephLocalTheorem2416NonstationaryScale.{u}) :
    SuccessorAlephLocalTheorem2416UltrafilterTcf.{u} := by
  intro eta hEtaLimit hEtaCof hPower J hUltra hClubs
  let hCofIioNe : Order.cof (Set.Iio eta) ≠ Cardinal.aleph0 :=
    cof_Iio_ne_aleph0_of_aleph0_lt_cof hEtaCof
  let NS : Ideal (Set.Iio eta) :=
    nonstationaryIdeal (Set.Iio eta) hCofIioNe
  have hNSLe : Ideal.Le NS J :=
    (nonstationaryIdeal_le_iff_eventually_of_isClub
      hCofIioNe J).mpr hClubs
  let coord := successorAlephIioCardinalIndex eta
  have hPushLe : Ideal.Le (NS.pushforward coord) (J.pushforward coord) :=
    Ideal.pushforward_mono hNSLe coord
  obtain ⟨s⟩ := h2416 eta hEtaLimit hEtaCof hPower
  have hScale : Scale
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        (J.pushforward coord))
      (cardinalScaleLength (Cardinal.aleph (eta + 1))) := by
    have hRaw :=
      (s.withLargerIdeal (J.pushforward coord) hPushLe).toScale
        (hUltra.pushforward coord).isProper
    simpa only [NS, coord, hCofIioNe,
      ReducedProductFrame.withIdeal, cardinalProductFrame] using hRaw
  exact cardinalScaleLength_hasTrueCofinality
    (Cardinal.isRegular_aleph_add_one eta) hScale

#print axioms
  successorAlephLocalTheorem2416UltrafilterTcf_of_nonstationaryScale

/-! The literal cofinality-indexed scale from Theorem 24.16 also suffices for
every club ultrafilter on `Iio eta`.  A normal fundamental sequence has club
range; restricting the target ultrafilter along it yields an ultrafilter
extending the source nonstationary ideal.  After transporting the strict
scale, functoriality of ideal pushforward identifies the resulting product
with the target club-ultrafilter product. -/
theorem successorAlephLocalTheorem2416UltrafilterTcf_of_fundamentalSequenceScale
    (h2416 : SuccessorAlephLocalTheorem2416FundamentalSequenceScale.{u}) :
    SuccessorAlephLocalTheorem2416UltrafilterTcf.{u} := by
  intro eta hEtaLimit hEtaCof hPower J hUltra hClubs
  obtain ⟨f, hFundamental, hNormal⟩ :=
    exists_normal_isFundamentalSeq (o := eta) (a := eta.cof.ord)
      rfl (Cardinal.isSuccLimit_ord hEtaCof.le)
  have s := h2416 eta hEtaLimit hEtaCof hPower
    f hFundamental hNormal
  let hSourceCofNe : Order.cof (Set.Iio eta.cof.ord) ≠
      Cardinal.aleph0 :=
    cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof hEtaCof
  let NS : Ideal (Set.Iio eta.cof.ord) :=
    nonstationaryIdeal (Set.Iio eta.cof.ord) hSourceCofNe
  letI : Nonempty (Set.Iio eta.cof.ord) :=
    ⟨⟨0, Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans hEtaCof)⟩⟩
  have hfInjective : Function.Injective f :=
    hNormal.strictMono.injective
  have hRangeClub : IsClub (Set.range f) :=
    isClub_range_of_isNormal_of_isCofinal
      hNormal hFundamental.isCofinal_range
  have hRange : J.Eventually (fun i => exists j, f j = i) := by
    simpa only [Set.mem_range] using hClubs (Set.range f) hRangeClub
  let Jr : Ideal (Set.Iio eta.cof.ord) := J.restrictAlong f
  have hJrUltra : Jr.IsUltrafilterDual := by
    exact hUltra.restrictAlong f hfInjective hRange
  have hNSLe : Ideal.Le NS Jr := by
    exact nonstationaryIdeal_le_restrictAlong_of_isNormal_of_isCofinal
      hSourceCofNe J hClubs f hNormal hFundamental.isCofinal_range
  let sourceCoord := successorAlephFundamentalCardinalIndex eta f
  let targetCoord := successorAlephIioCardinalIndex eta
  have hPushLe : Ideal.Le (NS.pushforward sourceCoord)
      (Jr.pushforward sourceCoord) :=
    Ideal.pushforward_mono hNSLe sourceCoord
  obtain ⟨s⟩ := s
  have hRaw : Scale
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        (Jr.pushforward sourceCoord))
      (cardinalScaleLength (Cardinal.aleph (eta + 1))) := by
    have hTransport :=
      (s.withLargerIdeal (Jr.pushforward sourceCoord) hPushLe).toScale
        hJrUltra.isProper
    simpa only [NS, sourceCoord, hSourceCofNe,
      ReducedProductFrame.withIdeal, cardinalProductFrame] using hTransport
  have hIdealEq : Jr.pushforward sourceCoord =
      J.pushforward targetCoord := by
    change (J.restrictAlong f).pushforward
        (targetCoord ∘ f) = J.pushforward targetCoord
    rw [← Ideal.pushforward_comp,
      J.restrictAlong_pushforward_eq f hRange]
  have hScale : Scale
      (cardinalProductFrame
        (successorAlephCardSet (Set.Iio eta))
        (J.pushforward targetCoord))
      (cardinalScaleLength (Cardinal.aleph (eta + 1))) := by
    rw [← hIdealEq]
    exact hRaw
  exact cardinalScaleLength_hasTrueCofinality
    (Cardinal.isRegular_aleph_add_one eta) hScale

#print axioms
  successorAlephLocalTheorem2416UltrafilterTcf_of_fundamentalSequenceScale

/-! The club-ultrafilter true-cofinality form of local Theorem 24.16 is now
unconditional under its displayed source hypotheses. -/
theorem successorAlephLocalTheorem2416UltrafilterTcf :
    SuccessorAlephLocalTheorem2416UltrafilterTcf.{u} :=
  successorAlephLocalTheorem2416UltrafilterTcf_of_fundamentalSequenceScale
    successorAlephLocalTheorem2416FundamentalSequenceScale

#print axioms successorAlephLocalTheorem2416UltrafilterTcf

/-! Theorem 24.16 plus the generator-concentration conclusion of Theorem
24.25(b) supplies all of the PCF-specific ultrafilter data in Corollary
24.30.  The upper bound for a club restriction is the generator-ideal bound;
the reverse bound follows from club cofinality and singularity of
`aleph eta`. -/
theorem
    successorAlephLocalCorollary2430UltrafilterData_of_theorem2416_of_generators
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G)
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta)
    (h2416 : SuccessorAlephLocalTheorem2416UltrafilterTcf.{u}) :
    SuccessorAlephLocalCorollary2430UltrafilterData hMax := by
  intro eta hEtaTheta hEtaLimit hEtaCof hPower
  let W : CardSet.{u} := successorAlephCardSet (Set.Iio eta)
  let lambda : Cardinal.{u} := Cardinal.aleph (eta + 1)
  let P : Set.Iio eta -> Prop := fun i =>
    G.generator lambda (Cardinal.aleph (i.1 + 1))
  have hWA : SubsetOf W
      (cardinalProductRepresentation.pcf alephSuccSet) := by
    intro gamma hGamma
    obtain ⟨i, hiEta, rfl⟩ := hGamma
    exact hCore i (hiEta.trans hEtaTheta)
  have hTcfFor : forall J : Ideal (Set.Iio eta),
      J.IsUltrafilterDual ->
      (forall C : Set (Set.Iio eta), IsClub C ->
        J.Eventually (fun i => i ∈ C)) ->
      HasTrueCofinality
        (cardinalProductFrame W
          (J.pushforward (successorAlephIioCardinalIndex eta)))
        (cardinalScaleLength lambda) := by
    intro J hUltra hClubs
    exact h2416 eta hEtaLimit hEtaCof hPower J hUltra hClubs
  have hLambdaPcfW : cardinalProductRepresentation.pcf W lambda := by
    have hCofIioNe : Order.cof (Set.Iio eta) ≠ Cardinal.aleph0 := by
      rw [Ordinal.cof_Iio, ← Ordinal.lift_cof]
      have hlt : Cardinal.lift.{u + 1} Cardinal.aleph0 <
          Cardinal.lift.{u + 1} eta.cof :=
        Cardinal.lift_lt.mpr hEtaCof
      rw [Cardinal.lift_aleph0] at hlt
      exact ne_of_gt hlt
    have hNSProper :
        (nonstationaryIdeal (Set.Iio eta) hCofIioNe).IsProper := by
      letI : Nonempty (Set.Iio eta) := ⟨⟨0, hEtaLimit.bot_lt⟩⟩
      exact nonstationaryIdeal_isProper hCofIioNe
    obtain ⟨J, hUltra, hNSLe⟩ :=
      exists_ultrafilterDual_ideal_extending
        (nonstationaryIdeal (Set.Iio eta) hCofIioNe) hNSProper
    have hClubs : forall C : Set (Set.Iio eta), IsClub C ->
        J.Eventually (fun i => i ∈ C) :=
      (nonstationaryIdeal_le_iff_eventually_of_isClub
        hCofIioNe J).mp hNSLe
    exact (cardinalProductRepresentation_mem_pcf_iff
      (A := W) (theta := lambda)).mpr
      ⟨Cardinal.isRegular_aleph_add_one eta,
        J.pushforward (successorAlephIioCardinalIndex eta),
        hUltra.pushforward (successorAlephIioCardinalIndex eta),
        hTcfFor J hUltra hClubs⟩
  have hLambdaPcfAmbient : cardinalProductRepresentation.pcf
      (cardinalProductRepresentation.pcf alephSuccSet) lambda :=
    cardinalProductRepresentation_pcf_mono hWA
      (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
      lambda hLambdaPcfW
  refine ⟨P, ?_, ?_⟩
  · intro J hUltra hClubs
    have hEventually := hCapture W hWA
      (J.pushforward (successorAlephIioCardinalIndex eta))
      (hUltra.pushforward (successorAlephIioCardinalIndex eta))
      lambda (Cardinal.isRegular_aleph_add_one eta)
      hLambdaPcfAmbient (hTcfFor J hUltra hClubs)
    exact hEventually
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
          (cardinalProductRepresentation.pcf alephSuccSet)
          (G.generator lambda)) := by
      intro gamma hGamma
      obtain ⟨alpha, hAlphaX, rfl⟩ := hGamma
      obtain ⟨j, hjC, rfl⟩ := hAlphaX
      exact ⟨hCore j.1 (j.2.trans hEtaTheta), hCP j hjC⟩
    have hLocalPcfInGenerator : cardinalProductRepresentation.pcf
        (InterCardSet
          (cardinalProductRepresentation.pcf alephSuccSet)
          (G.generator lambda))
        (successorAlephLocalMaxPcfCardinal hMax X) :=
      cardinalProductRepresentation_pcf_mono hIntoGenerator
        (fun gamma hGamma =>
          (cardinalProductRepresentation.pcf_is_setOfRegulars alephSuccSet)
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
  successorAlephLocalCorollary2430UltrafilterData_of_theorem2416_of_generators

/-! With local Theorem 24.16 proved, generator concentration and the initial
core segment are the only PCF inputs needed for the ultrafilter data in
Corollary 24.30. -/
theorem successorAlephLocalCorollary2430UltrafilterData_of_generators
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G)
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    SuccessorAlephLocalCorollary2430UltrafilterData hMax :=
  successorAlephLocalCorollary2430UltrafilterData_of_theorem2416_of_generators
    hMax G hCapture hCore successorAlephLocalTheorem2416UltrafilterTcf

#print axioms
  successorAlephLocalCorollary2430UltrafilterData_of_generators

theorem successorAlephLocalCorollary2430_of_ultrafilterData
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hData : SuccessorAlephLocalCorollary2430UltrafilterData hMax) :
    SuccessorAlephLocalCorollary2430 hMax := by
  intro eta hEtaTheta hEtaLimit hEtaCof hPower
  obtain ⟨P, hEveryExtension, hRestrictedMax⟩ :=
    hData eta hEtaTheta hEtaLimit hEtaCof hPower
  have hCofIioNe : Order.cof (Set.Iio eta) ≠ Cardinal.aleph0 := by
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof]
    have hlt : Cardinal.lift.{u + 1} Cardinal.aleph0 <
        Cardinal.lift.{u + 1} eta.cof :=
      Cardinal.lift_lt.mpr hEtaCof
    rw [Cardinal.lift_aleph0] at hlt
    exact ne_of_gt hlt
  obtain ⟨C, hCClub, hCP⟩ :=
    exists_club_subset_of_forall_nonstationaryIdeal_extension_eventually
      hCofIioNe P (by
        intro J hUltra hLe
        exact hEveryExtension J hUltra
          ((nonstationaryIdeal_le_iff_eventually_of_isClub
            hCofIioNe J).mp hLe))
  exact ⟨C, hCClub, hRestrictedMax C hCClub hCP⟩

#print axioms successorAlephLocalCorollary2430_of_ultrafilterData

/-! Generator concentration now yields local Corollary 24.30 directly; its
Theorem 24.16 input is discharged by the exact-upper-bound construction. -/
theorem successorAlephLocalCorollary2430_of_generators
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (G : GeneratorSystem cardinalProductRepresentation
      (cardinalProductRepresentation.pcf alephSuccSet.{u}))
    (hCapture : GeneratorCapturesCanonicalUltrafilters G)
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    SuccessorAlephLocalCorollary2430 hMax :=
  successorAlephLocalCorollary2430_of_ultrafilterData hMax
    (successorAlephLocalCorollary2430UltrafilterData_of_generators
      hMax G hCapture hCore)

#print axioms successorAlephLocalCorollary2430_of_generators

theorem successorAlephLocalClubMaxPcfBelow_of_corollary2430_of_strongLimit
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (h2430 : SuccessorAlephLocalCorollary2430 hMax)
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    SuccessorAlephLocalClubMaxPcfBelow hMax targetIndexOmega4 := by
  intro eta hEtaTheta hEtaTarget hEtaLimit hEtaCof
  exact h2430 eta hEtaTheta hEtaLimit hEtaCof
    (two_power_ordinalCof_lt_aleph_of_strongLimit_of_uncountableCof
      hStrongLimit hEtaTarget hEtaCof)

#print axioms
  successorAlephLocalClubMaxPcfBelow_of_corollary2430_of_strongLimit

def SuccessorAlephLocalMaxPcfRankClubWitnessBelow
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (bound : Ordinal.{u}) : Prop :=
  forall eta, eta < theta -> eta < bound -> Order.IsSuccLimit eta ->
    Cardinal.aleph0 < eta.cof ->
    exists C : Set (Set.Iio eta),
      IsClub C /\
        successorAlephLocalMaxPcfRank hMax
            ((fun i : Set.Iio eta => i.1) '' C) = eta

theorem successorAlephLocalMaxPcfRankClubWitnessBelow_of_clubMaxPcfBelow
    {theta bound : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hClub : SuccessorAlephLocalClubMaxPcfBelow hMax bound) :
    SuccessorAlephLocalMaxPcfRankClubWitnessBelow hMax bound := by
  intro eta hEtaTheta hEtaBound hEtaLimit hEtaCof
  obtain ⟨C, hCClub, hCard⟩ :=
    hClub eta hEtaTheta hEtaBound hEtaLimit hEtaCof
  refine ⟨C, hCClub, ?_⟩
  letI : Nonempty (Set.Iio eta) := ⟨⟨0, hEtaLimit.bot_lt⟩⟩
  have hCNonempty : C.Nonempty := isClub_nonempty hCClub
  obtain ⟨i, hiC⟩ := hCNonempty
  let X : Set (Ordinal.{u}) := (fun j : Set.Iio eta => j.1) '' C
  have hiX : i.1 ∈ X := ⟨i, hiC, rfl⟩
  have hXBound : X ⊆ Set.Iio theta := by
    rintro x ⟨j, _hjC, rfl⟩
    exact j.2.trans hEtaTheta
  have hBoundedNonempty :
      (successorAlephBoundedIndexSet theta X).Nonempty :=
    ⟨i.1, hiX, hXBound hiX⟩
  have hIndex : successorAlephLocalMaxPcfIndex hMax X = eta + 1 := by
    apply Cardinal.aleph.injective
    rw [aleph_successorAlephLocalMaxPcfIndex_eq hMax hBoundedNonempty]
    exact hCard
  rw [successorAlephLocalMaxPcfRank, hIndex,
    ← Order.succ_eq_add_one, Ordinal.pred_succ]

#print axioms
  successorAlephLocalMaxPcfRankClubWitnessBelow_of_clubMaxPcfBelow

def SuccessorAlephLocalMaxPcfRankJechPropertiesBelow
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (bound : Ordinal.{u}) : Prop :=
  (forall X Y : Set (Ordinal.{u}), X ⊆ Y ->
    successorAlephLocalMaxPcfRank hMax X <=
      successorAlephLocalMaxPcfRank hMax Y) /\
  SuccessorAlephLocalMaxPcfRankClubWitnessBelow hMax bound /\
  SuccessorAlephLocalMaxPcfRankOmegaOneInitialSegment hMax

theorem successorAlephLocalMaxPcfRankJechPropertiesBelow_of_sourceInputs
    {theta bound : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hClub : SuccessorAlephLocalClubMaxPcfBelow hMax bound)
    (hLocalization : CardinalProductPcfLocalizationOutput alephSuccSet.{u})
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    SuccessorAlephLocalMaxPcfRankJechPropertiesBelow hMax bound := by
  exact ⟨fun _ _ hXY => successorAlephLocalMaxPcfRank_mono hMax hXY,
    successorAlephLocalMaxPcfRankClubWitnessBelow_of_clubMaxPcfBelow
      hMax hClub,
    successorAlephLocalMaxPcfRankOmegaOneInitialSegment_of_cardinalProductLocalization_of_corePcf
      hMax hLocalization hCore⟩

#print axioms
  successorAlephLocalMaxPcfRankJechPropertiesBelow_of_sourceInputs

theorem not_successorAlephLocalMaxPcfRankReflectionBelowAt_of_boundedJechProperties
    {theta bound delta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hProperties :
      SuccessorAlephLocalMaxPcfRankJechPropertiesBelow hMax bound)
    (hDeltaTheta : delta < theta)
    (hDeltaBound : delta < bound)
    (hDeltaLimit : Order.IsSuccLimit delta)
    (hDeltaCof : Cardinal.aleph0 < delta.cof) :
    ¬ SuccessorAlephLocalMaxPcfRankReflectionBelowAt hMax bound delta := by
  rintro hReflection
  obtain ⟨hMono, hClub, hOmegaOne⟩ := hProperties
  obtain ⟨C, hCClub, hRankC⟩ :=
    hClub delta hDeltaTheta hDeltaBound hDeltaLimit hDeltaCof
  obtain ⟨X, hXC, hType, hReflect⟩ := hReflection C hCClub
  have hXTheta : X ⊆ Set.Iio theta := by
    intro x hx
    obtain ⟨i, hiC, rfl⟩ := hXC hx
    exact i.2.trans hDeltaTheta
  obtain ⟨gamma, hGammaX, hDominates⟩ :=
    hOmegaOne X hXTheta hType
  have hInitialC : X ∩ Set.Iio gamma ⊆
      (fun i : Set.Iio delta => i.1) '' C := fun _ hx => hXC hx.1
  have hRankInitialBound :
      successorAlephLocalMaxPcfRank hMax
          (X ∩ Set.Iio gamma) < bound :=
    (hMono _ _ hInitialC).trans_lt (hRankC.symm ▸ hDeltaBound)
  have hRankInitialSup :
      successorAlephLocalMaxPcfRank hMax
          (X ∩ Set.Iio gamma) < sSup X :=
    hReflect gamma hGammaX hRankInitialBound
  have hTypePos : 0 < Ordinal.type ((· < ·) : X -> X -> Prop) := by
    rw [hType]
    simpa only [Cardinal.ord_aleph] using
      (Cardinal.isSuccLimit_ord
        (Cardinal.aleph0_le_aleph
          (1 : Ordinal.{u + 1}))).bot_lt
  let x0 : X := Ordinal.enum ((· < ·) : X -> X -> Prop)
    ⟨0, hTypePos⟩
  have hXNonempty : X.Nonempty := ⟨x0.1, x0.2⟩
  have hSupLe : sSup X <= successorAlephLocalMaxPcfRank hMax
      (X ∩ Set.Iio gamma) :=
    csSup_le hXNonempty (fun x hx => hDominates x hx)
  exact (not_lt_of_ge hSupLe) hRankInitialSup

#print axioms
  not_successorAlephLocalMaxPcfRankReflectionBelowAt_of_boundedJechProperties

theorem successorAlephLocalRankDomain_lt_targetIndexOmega4_of_boundedClubInputs
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hClub : SuccessorAlephLocalClubMaxPcfBelow
      hMax targetIndexOmega4)
    (hLocalization : CardinalProductPcfLocalizationOutput alephSuccSet.{u})
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta) :
    theta < targetIndexOmega4.{u} := by
  apply lt_of_not_ge
  intro hTargetTheta
  obtain ⟨delta, hDeltaTheta, hDeltaTarget, hDeltaLimit,
    hDeltaCof, hReflectAt⟩ :=
    successorAlephLocalOmegaFourTargetReflectionPrinciple_of_rankConstruction
      hMax hTargetTheta
  exact
    (not_successorAlephLocalMaxPcfRankReflectionBelowAt_of_boundedJechProperties
      hMax
      (successorAlephLocalMaxPcfRankJechPropertiesBelow_of_sourceInputs
        hMax hClub hLocalization hCore)
      hDeltaTheta hDeltaTarget hDeltaLimit hDeltaCof) hReflectAt

#print axioms
  successorAlephLocalRankDomain_lt_targetIndexOmega4_of_boundedClubInputs

theorem coreMaxPcfWitness_lt_targetAlephOmega4_of_localRankBoundedClubInputs
    {theta : Ordinal.{u}}
    (hMax : SuccessorAlephHasMaxPcfBelow theta)
    (hClub : SuccessorAlephLocalClubMaxPcfBelow
      hMax targetIndexOmega4)
    (hLocalization : CardinalProductPcfLocalizationOutput alephSuccSet.{u})
    (hCore : SuccessorAlephInitialSegmentInCorePcf theta)
    (M : MaxPcfWitness cardinalProductRepresentation alephSuccSet.{u})
    (hMaxIndexEq : M.theta = Cardinal.aleph theta) :
    M.theta < targetAlephOmega4.{u} := by
  have hTheta : theta < targetIndexOmega4.{u} :=
    successorAlephLocalRankDomain_lt_targetIndexOmega4_of_boundedClubInputs
      hMax hClub hLocalization hCore
  rw [hMaxIndexEq]
  exact Cardinal.aleph_lt_aleph.mpr hTheta

#print axioms
  coreMaxPcfWitness_lt_targetAlephOmega4_of_localRankBoundedClubInputs


/-! 核心端点直接使用上面的局部秩界；这里省去不参与主证明的替代输入适配层。 -/


end PcfProject
