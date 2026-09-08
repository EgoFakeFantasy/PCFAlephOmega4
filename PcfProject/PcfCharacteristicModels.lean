import PcfProject.UniformSubsetCover
import Mathlib.ModelTheory.Skolem
import Mathlib.SetTheory.Cardinal.Cofinality.Club

open Cardinal Set
open scoped Cardinal

namespace PcfProject

universe u

abbrev AlephOmegaOrdinal := Set.Iio targetAlephOmega.ord

noncomputable abbrev finiteAleph (n : Nat) : Cardinal.{u} :=
  Cardinal.aleph (n : Ordinal.{u})

theorem finiteAleph_isRegular (n : Nat) :
    Cardinal.IsRegular (finiteAleph.{u} n) := by
  cases n with
  | zero => simpa [finiteAleph] using Cardinal.isRegular_aleph0.{u}
  | succ n =>
      simpa [finiteAleph, Nat.cast_add, Nat.cast_one, add_assoc] using
        Cardinal.isRegular_aleph_add_one (n : Ordinal.{u})

theorem finiteAleph_succ (n : Nat) :
    finiteAleph (n + 1) = Order.succ (finiteAleph n) := by
  simp [finiteAleph, Nat.cast_add, Nat.cast_one]

theorem finiteAleph_lt_targetAlephOmega (n : Nat) :
    finiteAleph n < targetAlephOmega.{u} := by
  apply Cardinal.aleph_lt_aleph.mpr
  exact Ordinal.natCast_lt_omega0 n

theorem finiteAleph_ord_lt_targetAlephOmega_ord (n : Nat) :
    (finiteAleph n).ord < targetAlephOmega.{u}.ord :=
  Cardinal.ord_lt_ord.mpr (finiteAleph_lt_targetAlephOmega n)

theorem AlephOmegaOrdinal.exists_lt_finiteAleph_ord
    (x : AlephOmegaOrdinal.{u}) :
    exists n : Nat, x.1 < (finiteAleph n).ord := by
  have hCardBelow : x.1.card < targetAlephOmega.{u} :=
    Cardinal.lt_ord.mp x.2
  by_cases hSmall : x.1.card <= Cardinal.aleph0
  · refine ⟨1, ?_⟩
    rw [finiteAleph, Nat.cast_one, ← Cardinal.succ_aleph0]
    exact Cardinal.lt_ord.mpr (hSmall.trans_lt (Order.lt_succ _))
  · have hAleph0 : Cardinal.aleph0 < x.1.card := lt_of_not_ge hSmall
    obtain ⟨m, hm⟩ :=
      alephSuccSet_of_aleph0_lt_of_lt_targetAlephOmega
        hAleph0 hCardBelow
    refine ⟨(m + 1) + 1, ?_⟩
    have hx := Cardinal.lt_ord_succ_card x.1
    rw [hm, Cardinal.succ_aleph] at hx
    have hIndex : ((((m + 1) + 1 : Nat) : Ordinal.{u})) =
        (m : Ordinal.{u}) + 1 + 1 := by
      calc
        ((((m + 1) + 1 : Nat) : Ordinal.{u})) =
            ((m + 1 : Nat) : Ordinal.{u}) + 1 := by
              rw [Nat.cast_add, Nat.cast_one]
        _ = (m : Ordinal.{u}) + 1 + 1 := by
              rw [Nat.cast_add, Nat.cast_one]
    change x.1 < (Cardinal.aleph
      ((((m + 1) + 1 : Nat) : Ordinal.{u}))).ord
    rw [hIndex]
    exact hx

theorem ordinal_card_eq_finiteAleph_of_interval
    (n : Nat) (gamma : Ordinal.{u})
    (hLower : (finiteAleph n).ord ≤ gamma)
    (hUpper : gamma < (finiteAleph (n + 1)).ord) :
    gamma.card = finiteAleph n := by
  apply le_antisymm
  · rw [finiteAleph_succ] at hUpper
    exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp hUpper)
  · exact Cardinal.ord_le.mp hLower

noncomputable def finiteAlephIntervalEquiv
    (n : Nat) (gamma : Ordinal.{u})
    (hLower : (finiteAleph n).ord ≤ gamma)
    (hUpper : gamma < (finiteAleph (n + 1)).ord) :
    Set.Iio (finiteAleph n).ord ≃ Set.Iio gamma := by
  apply Classical.choice
  apply Cardinal.eq.mp
  rw [Cardinal.mk_Iio_ordinal, Cardinal.mk_Iio_ordinal,
    ordinal_card_eq_finiteAleph_of_interval n gamma hLower hUpper,
    Cardinal.card_ord]

inductive AlephOmegaClosureFunc : Nat -> Type
  | forward (n : Nat) : AlephOmegaClosureFunc 2
  | backward (n : Nat) : AlephOmegaClosureFunc 2

def alephOmegaClosureLanguage : FirstOrder.Language.{0, 0} where
  Functions := AlephOmegaClosureFunc
  Relations := fun _ => Empty

def alephOmegaClosureFunctionSymbolCode :
    (Sigma AlephOmegaClosureFunc) -> Nat × Bool
  | ⟨_, .forward n⟩ => (n, false)
  | ⟨_, .backward n⟩ => (n, true)

theorem alephOmegaClosureFunctionSymbolCode_injective :
    Function.Injective alephOmegaClosureFunctionSymbolCode := by
  intro a b hab
  rcases a with ⟨_, a⟩
  rcases b with ⟨_, b⟩
  cases a <;> cases b <;>
    simp only [alephOmegaClosureFunctionSymbolCode,
      Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
      and_false] at hab ⊢
  all_goals simp_all

theorem alephOmegaClosureLanguage_card_le_aleph0 :
    alephOmegaClosureLanguage.card <= Cardinal.aleph0 := by
  rw [FirstOrder.Language.card_eq_card_functions_add_card_relations]
  have hFunctions :
      Cardinal.sum (fun n =>
        Cardinal.lift.{0} #(alephOmegaClosureLanguage.Functions n)) <=
        Cardinal.aleph0 := by
    simp only [Cardinal.lift_id]
    rw [← Cardinal.mk_sigma]
    exact (Cardinal.mk_le_of_injective
      alephOmegaClosureFunctionSymbolCode_injective).trans (by simp)
  have hRelations :
      Cardinal.sum (fun n =>
        Cardinal.lift.{0} #(alephOmegaClosureLanguage.Relations n)) = 0 := by
    simp [alephOmegaClosureLanguage]
  rw [hRelations, add_zero]
  exact hFunctions

noncomputable def alephOmegaZero : AlephOmegaOrdinal.{u} :=
  ⟨0, (Cardinal.ord_pos.mpr
    (Cardinal.aleph0_pos.trans_le targetAlephOmega_aleph0_le))⟩

noncomputable def alephOmegaForward
    (n : Nat) (gamma xi : AlephOmegaOrdinal.{u}) :
    AlephOmegaOrdinal.{u} :=
  if hLower : (finiteAleph n).ord ≤ gamma.1 then
    if hUpper : gamma.1 < (finiteAleph (n + 1)).ord then
      if hXi : xi.1 < (finiteAleph n).ord then
        let y := finiteAlephIntervalEquiv n gamma.1 hLower hUpper ⟨xi.1, hXi⟩
        ⟨y.1, by
          exact lt_trans
            (show y.1 < gamma.1 from y.2)
            (show gamma.1 < targetAlephOmega.ord from gamma.2)⟩
      else alephOmegaZero
    else alephOmegaZero
  else alephOmegaZero

noncomputable def alephOmegaBackward
    (n : Nat) (gamma eta : AlephOmegaOrdinal.{u}) :
    AlephOmegaOrdinal.{u} :=
  if hLower : (finiteAleph n).ord ≤ gamma.1 then
    if hUpper : gamma.1 < (finiteAleph (n + 1)).ord then
      if hEta : eta.1 < gamma.1 then
        let x := (finiteAlephIntervalEquiv n gamma.1 hLower hUpper).symm
          ⟨eta.1, hEta⟩
        ⟨x.1, (x.2.trans_le hLower).trans gamma.2⟩
      else alephOmegaZero
    else alephOmegaZero
  else alephOmegaZero

noncomputable instance alephOmegaClosureStructure :
    alephOmegaClosureLanguage.Structure AlephOmegaOrdinal.{u} where
  funMap {arity} symbol args := by
    cases symbol with
    | forward n => exact alephOmegaForward n (args 0) (args 1)
    | backward n => exact alephOmegaBackward n (args 0) (args 1)
  RelMap {arity} relation _ := by
    change Empty at relation
    exact relation.elim

noncomputable def alephOmegaElementaryHull
    (k : Nat) (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (s : Set AlephOmegaOrdinal.{u})
    (hs : Cardinal.mk s <= Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :
    alephOmegaClosureLanguage.ElementarySubstructure
      AlephOmegaOrdinal.{u} :=
  Classical.choose
    (FirstOrder.Language.exists_elementarySubstructure_card_eq.{0, 0, u + 1, u + 1}
      alephOmegaClosureLanguage (M := AlephOmegaOrdinal.{u})
      s (Cardinal.lift.{u + 1} (finiteAleph.{u} k))
      (Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk)
      (by simpa using hs)
      (by
        have hLanguage :
            Cardinal.lift.{u + 1} alephOmegaClosureLanguage.card <=
              Cardinal.aleph0 := by
          simpa only [Cardinal.lift_aleph0] using
            (Cardinal.lift_le.{u + 1, 0}.mpr
              alephOmegaClosureLanguage_card_le_aleph0)
        simpa only [Cardinal.lift_aleph0, Cardinal.lift_id',
          Cardinal.lift_lift] using
          hLanguage.trans
            (Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk))
      (by
        rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
        simpa only [Cardinal.lift_id', Cardinal.lift_lift] using
          (Cardinal.lift_le.{u + 1, u}.mpr
            (finiteAleph_lt_targetAlephOmega k).le)))

theorem alephOmegaElementaryHull_contains
    (k : Nat) (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (s : Set AlephOmegaOrdinal.{u})
    (hs : Cardinal.mk s <= Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :
    s ⊆ alephOmegaElementaryHull k hk s hs :=
  (Classical.choose_spec
    (FirstOrder.Language.exists_elementarySubstructure_card_eq.{0, 0, u + 1, u + 1}
      alephOmegaClosureLanguage (M := AlephOmegaOrdinal.{u})
      s (Cardinal.lift.{u + 1} (finiteAleph.{u} k))
      (Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk)
      (by simpa using hs)
      (by
        have hLanguage :
            Cardinal.lift.{u + 1} alephOmegaClosureLanguage.card <=
              Cardinal.aleph0 := by
          simpa only [Cardinal.lift_aleph0] using
            (Cardinal.lift_le.{u + 1, 0}.mpr
              alephOmegaClosureLanguage_card_le_aleph0)
        simpa only [Cardinal.lift_aleph0, Cardinal.lift_id',
          Cardinal.lift_lift] using
          hLanguage.trans
            (Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk))
      (by
        rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
        simpa only [Cardinal.lift_id', Cardinal.lift_lift] using
          (Cardinal.lift_le.{u + 1, u}.mpr
            (finiteAleph_lt_targetAlephOmega k).le)))).1

theorem mk_alephOmegaElementaryHull
    (k : Nat) (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (s : Set AlephOmegaOrdinal.{u})
    (hs : Cardinal.mk s <= Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :
    Cardinal.mk (alephOmegaElementaryHull k hk s hs) =
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
  have h := (Classical.choose_spec
    (FirstOrder.Language.exists_elementarySubstructure_card_eq.{0, 0, u + 1, u + 1}
      alephOmegaClosureLanguage (M := AlephOmegaOrdinal.{u})
      s (Cardinal.lift.{u + 1} (finiteAleph.{u} k))
      (Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk)
      (by simpa using hs)
      (by
        have hLanguage :
            Cardinal.lift.{u + 1} alephOmegaClosureLanguage.card <=
              Cardinal.aleph0 := by
          simpa only [Cardinal.lift_aleph0] using
            (Cardinal.lift_le.{u + 1, 0}.mpr
              alephOmegaClosureLanguage_card_le_aleph0)
        simpa only [Cardinal.lift_aleph0, Cardinal.lift_id',
          Cardinal.lift_lift] using
          hLanguage.trans
            (Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk))
      (by
        rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
        simpa only [Cardinal.lift_id', Cardinal.lift_lift] using
          (Cardinal.lift_le.{u + 1, u}.mpr
            (finiteAleph_lt_targetAlephOmega k).le)))).2
  unfold alephOmegaElementaryHull
  exact Cardinal.lift_inj.mp h

def alephOmegaBoundedValues
    (k n : Nat) (s : Set AlephOmegaOrdinal.{u}) : Set (Ordinal.{u}) :=
  (fun x : AlephOmegaOrdinal.{u} => x.1) ''
    {x | x ∈ s ∧ x.1 < (finiteAleph (k + n + 1)).ord}

noncomputable def alephOmegaSetCharacteristic
    (k n : Nat) (s : Set AlephOmegaOrdinal.{u}) : Ordinal.{u} :=
  sSup ((fun x : Ordinal.{u} => x + 1) ''
    alephOmegaBoundedValues k n s)

theorem mk_alephOmegaBoundedValues_le
    (k n : Nat) (s : Set AlephOmegaOrdinal.{u}) :
    Cardinal.mk (alephOmegaBoundedValues k n s) <= Cardinal.mk s := by
  exact Cardinal.mk_image_le.trans
    (Cardinal.mk_subtype_mono (fun _ hx => hx.1))

theorem alephOmegaSetCharacteristic_lt
    (k n : Nat) (s : Set AlephOmegaOrdinal.{u})
    (hs : Cardinal.mk s <= Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :
    alephOmegaSetCharacteristic k n s <
      (finiteAleph (k + n + 1)).ord := by
  apply Ordinal.sSup_add_one_lt_of_lt_cof
  · calc
      Cardinal.mk (alephOmegaBoundedValues k n s) <=
          Cardinal.mk s := mk_alephOmegaBoundedValues_le k n s
      _ <= Cardinal.lift.{u + 1} (finiteAleph.{u} k) := hs
      _ < Cardinal.lift.{u + 1}
          (finiteAleph (k + n + 1)) :=
        Cardinal.lift_lt.mpr (Cardinal.aleph_lt_aleph.mpr (by
          exact_mod_cast (by omega : k < k + n + 1)))
      _ = (Ordinal.lift.{u + 1}
          (finiteAleph (k + n + 1)).ord).cof := by
        have hRegular : Cardinal.IsRegular
            (finiteAleph (k + n + 1)) := by
          simpa [finiteAleph, Nat.cast_add, Nat.cast_one,
            add_assoc] using
              (Cardinal.isRegular_aleph_add_one
                ((k + n : Nat) : Ordinal.{u}))
        rw [← Ordinal.lift_cof, hRegular.cof_ord]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hy.2

theorem lt_alephOmegaSetCharacteristic
    (k n : Nat) (s : Set AlephOmegaOrdinal.{u})
    {x : AlephOmegaOrdinal.{u}}
    (hxs : x ∈ s)
    (hxUpper : x.1 < (finiteAleph (k + n + 1)).ord) :
    x.1 < alephOmegaSetCharacteristic k n s := by
  apply (lt_add_one x.1).trans_le
  apply le_csSup
  · exact ⟨(finiteAleph (k + n + 1)).ord,
      by
        rintro y ⟨z, hz, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hz
        exact (Cardinal.isSuccLimit_ord
          (Cardinal.aleph0_le_aleph _)).add_one_lt hx.2 |>.le⟩
  · exact ⟨x.1, ⟨x, ⟨hxs, hxUpper⟩, rfl⟩, rfl⟩

abbrev AlephOmegaChainStage (k : Nat) :=
  (finiteAleph.{u} k).ord.ToType

structure AlephOmegaStageModel (k : Nat) where
  substructure :
    alephOmegaClosureLanguage.ElementarySubstructure
      AlephOmegaOrdinal.{u}
  cardinal_eq : Cardinal.mk substructure =
    Cardinal.lift.{u + 1} (finiteAleph.{u} k)

def alephOmegaPreviousCarrier
    {k : Nat} (i : AlephOmegaChainStage.{u} k)
    (previous : forall j : AlephOmegaChainStage.{u} k,
      j < i -> AlephOmegaStageModel.{u} k) :
    Set AlephOmegaOrdinal.{u} :=
  ⋃ j : Set.Iio i, ((previous j.1 j.2).substructure :
    Set AlephOmegaOrdinal.{u})

theorem mk_alephOmegaPreviousCarrier_le
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (i : AlephOmegaChainStage.{u} k)
    (previous : forall j : AlephOmegaChainStage.{u} k,
      j < i -> AlephOmegaStageModel.{u} k) :
    Cardinal.mk (alephOmegaPreviousCarrier i previous) <=
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
  let family : Set.Iio i -> Set AlephOmegaOrdinal.{u} := fun j =>
    ((previous j.1 j.2).substructure : Set AlephOmegaOrdinal.{u})
  have hUnion := Cardinal.mk_iUnion_le_lift family
  rw [Cardinal.lift_id'.{u, u + 1}] at hUnion
  have hLiftFamily : forall j,
      Cardinal.lift.{u} (Cardinal.mk (family j)) =
        Cardinal.mk (family j) := fun j =>
    Cardinal.lift_id'.{u, u + 1} (Cardinal.mk (family j))
  simp_rw [hLiftFamily] at hUnion
  have hIndex : Cardinal.lift.{u + 1} (Cardinal.mk (Set.Iio i)) <=
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
    apply Cardinal.lift_le.mpr
    exact (Cardinal.mk_subtype_le _).trans_eq
      (Cardinal.mk_ord_toType (finiteAleph.{u} k))
  have hFamily : forall j, Cardinal.mk (family j) =
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
    intro j
    exact (previous j.1 j.2).cardinal_eq
  calc
    Cardinal.mk (alephOmegaPreviousCarrier i previous) <=
      Cardinal.lift.{u + 1} (Cardinal.mk (Set.Iio i)) *
          ⨆ j, Cardinal.mk (family j) := by
      simpa only [alephOmegaPreviousCarrier, family] using hUnion
    _ <= Cardinal.lift.{u + 1} (finiteAleph.{u} k) *
        Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
      apply mul_le_mul' hIndex
      apply ciSup_le'
      intro j
      rw [hFamily j]
    _ = Cardinal.lift.{u + 1} (finiteAleph.{u} k) :=
      Cardinal.mul_eq_self
        (Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk)

def alephOmegaBase (k : Nat) : Set AlephOmegaOrdinal.{u} :=
  {x | x.1 < (finiteAleph.{u} k).ord}

theorem mk_alephOmegaBase_le (k : Nat) :
    Cardinal.mk (alephOmegaBase.{u} k) <=
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
  let e : alephOmegaBase.{u} k -> Set.Iio (finiteAleph.{u} k).ord :=
    fun x => ⟨x.1.1, x.2⟩
  calc
    Cardinal.mk (alephOmegaBase.{u} k) <=
        Cardinal.mk (Set.Iio (finiteAleph.{u} k).ord) :=
      Cardinal.mk_le_of_injective (f := e) (by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : Set.Iio (finiteAleph.{u} k).ord => z.1) hxy)
    _ = Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
      rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]

theorem mk_union_le_infinite
    {α : Type u} {s t : Set α} {mu : Cardinal.{u}}
    (hMu : Cardinal.aleph0 <= mu)
    (hs : Cardinal.mk s <= mu) (ht : Cardinal.mk t <= mu) :
    Cardinal.mk (s ∪ t : Set α) <= mu := by
  calc
    Cardinal.mk (s ∪ t : Set α) <= Cardinal.mk s + Cardinal.mk t :=
      Cardinal.mk_union_le s t
    _ <= mu + mu := add_le_add hs ht
    _ = mu := Cardinal.add_eq_left hMu le_rfl

theorem mk_range_nat_le_infinite
    {α : Type u} {mu : Cardinal.{u}}
    (hMu : Cardinal.aleph0 <= mu) (f : Nat -> α) :
    Cardinal.mk (Set.range f) <= mu := by
  have hRange : Cardinal.mk (Set.range f) <= Cardinal.aleph0 := by
    have hr := Cardinal.mk_range_le_lift (f := f)
    rw [Cardinal.lift_id'.{0, u}] at hr
    simpa only [Cardinal.lift_aleph0, Cardinal.mk_nat] using hr
  exact hRange.trans hMu

structure AlephOmegaTailCofinalFamily (k : Nat) where
  Index : Type (u + 1)
  member : Index -> forall n : Nat,
    (finiteAleph.{u} (k + n + 1)).ord.ToType
  pointwiseCofinal : forall g : forall n : Nat,
      (finiteAleph.{u} (k + n + 1)).ord.ToType,
    exists i, forall n, g n <= member i n

noncomputable def AlephOmegaTailCofinalFamily.characteristicIndex
    {k : Nat} (F : AlephOmegaTailCofinalFamily.{u} k)
    (s : Set AlephOmegaOrdinal.{u})
    (hs : Cardinal.mk s <= Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :
    F.Index :=
  Classical.choose (F.pointwiseCofinal (fun n =>
    Ordinal.ToType.mk
      ⟨alephOmegaSetCharacteristic k n s,
        alephOmegaSetCharacteristic_lt k n s hs⟩))

theorem AlephOmegaTailCofinalFamily.characteristic_le
    {k : Nat} (F : AlephOmegaTailCofinalFamily.{u} k)
    (s : Set AlephOmegaOrdinal.{u})
    (hs : Cardinal.mk s <= Cardinal.lift.{u + 1} (finiteAleph.{u} k))
    (n : Nat) :
    Ordinal.ToType.mk
        ⟨alephOmegaSetCharacteristic k n s,
          alephOmegaSetCharacteristic_lt k n s hs⟩ <=
      F.member (F.characteristicIndex s hs) n :=
  Classical.choose_spec (F.pointwiseCofinal (fun n =>
    Ordinal.ToType.mk
      ⟨alephOmegaSetCharacteristic k n s,
        alephOmegaSetCharacteristic_lt k n s hs⟩)) n

noncomputable def alephOmegaCharacteristicPoint
    (k n : Nat) (s : Set AlephOmegaOrdinal.{u})
    (hs : Cardinal.mk s <= Cardinal.lift.{u + 1} (finiteAleph.{u} k)) :
    AlephOmegaOrdinal.{u} :=
  ⟨alephOmegaSetCharacteristic k n s,
    (alephOmegaSetCharacteristic_lt k n s hs).trans
      (finiteAleph_ord_lt_targetAlephOmega_ord (k + n + 1))⟩

noncomputable def AlephOmegaTailCofinalFamily.memberPoint
    {k : Nat} (F : AlephOmegaTailCofinalFamily.{u} k)
    (i : F.Index) (n : Nat) : AlephOmegaOrdinal.{u} :=
  ⟨((Ordinal.ToType.mk : Set.Iio
      (finiteAleph.{u} (k + n + 1)).ord ≃o
        (finiteAleph.{u} (k + n + 1)).ord.ToType).symm
      (F.member i n)).1,
    by
      exact lt_trans
        (show ((Ordinal.ToType.mk : Set.Iio
          (finiteAleph.{u} (k + n + 1)).ord ≃o
            (finiteAleph.{u} (k + n + 1)).ord.ToType).symm
          (F.member i n)).1 < (finiteAleph.{u} (k + n + 1)).ord from
            ((Ordinal.ToType.mk : Set.Iio
              (finiteAleph.{u} (k + n + 1)).ord ≃o
                (finiteAleph.{u} (k + n + 1)).ord.ToType).symm
              (F.member i n)).2)
        (finiteAleph_ord_lt_targetAlephOmega_ord (k + n + 1))⟩

def alephOmegaStageSeed
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (i : AlephOmegaChainStage.{u} k)
    (previous : forall j : AlephOmegaChainStage.{u} k,
      j < i -> AlephOmegaStageModel.{u} k) :
    Set AlephOmegaOrdinal.{u} :=
  let p := alephOmegaPreviousCarrier i previous
  let hp := mk_alephOmegaPreviousCarrier_le hk i previous
  (((alephOmegaBase k ∪ a) ∪ p) ∪
      Set.range (fun n => alephOmegaCharacteristicPoint k n p hp)) ∪
    Set.range (fun n =>
      F.memberPoint (F.characteristicIndex p hp) n)

theorem mk_alephOmegaStageSeed_le
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (i : AlephOmegaChainStage.{u} k)
    (previous : forall j : AlephOmegaChainStage.{u} k,
      j < i -> AlephOmegaStageModel.{u} k) :
    Cardinal.mk (alephOmegaStageSeed hk F a i previous) <=
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
  let mu := Cardinal.lift.{u + 1} (finiteAleph.{u} k)
  have hMu : Cardinal.aleph0 <= mu :=
    Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk
  let p := alephOmegaPreviousCarrier i previous
  let hp : Cardinal.mk p <= mu :=
    mk_alephOmegaPreviousCarrier_le hk i previous
  have hBase : Cardinal.mk (alephOmegaBase.{u} k) <= mu :=
    mk_alephOmegaBase_le k
  have ha' : Cardinal.mk a <= mu := ha.trans hMu
  have hChar : Cardinal.mk (Set.range (fun n =>
      alephOmegaCharacteristicPoint k n p hp)) <= mu :=
    mk_range_nat_le_infinite hMu _
  have hMember : Cardinal.mk (Set.range (fun n =>
      F.memberPoint (F.characteristicIndex p hp) n)) <= mu :=
    mk_range_nat_le_infinite hMu _
  exact mk_union_le_infinite hMu
    (mk_union_le_infinite hMu
      (mk_union_le_infinite hMu
        (mk_union_le_infinite hMu hBase ha') hp)
      hChar)
    hMember

noncomputable def alephOmegaStageStep
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (i : AlephOmegaChainStage.{u} k)
    (previous : forall j : AlephOmegaChainStage.{u} k,
      j < i -> AlephOmegaStageModel.{u} k) :
    AlephOmegaStageModel.{u} k :=
  let seed := alephOmegaStageSeed hk F a i previous
  let hSeed := mk_alephOmegaStageSeed_le hk F a ha i previous
  { substructure := alephOmegaElementaryHull k hk seed hSeed
    cardinal_eq := mk_alephOmegaElementaryHull k hk seed hSeed }

noncomputable def alephOmegaModelChain
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    AlephOmegaChainStage.{u} k -> AlephOmegaStageModel.{u} k :=
  WellFounded.fix wellFounded_lt fun i previous =>
    alephOmegaStageStep hk F a ha i previous

theorem alephOmegaModelChain_eq_stageStep
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (i : AlephOmegaChainStage.{u} k) :
    alephOmegaModelChain hk F a ha i =
      alephOmegaStageStep hk F a ha i
        (fun j _ => alephOmegaModelChain hk F a ha j) := by
  rw [alephOmegaModelChain, WellFounded.fix_eq]

def alephOmegaModelUnion
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    Set AlephOmegaOrdinal.{u} :=
  ⋃ i : AlephOmegaChainStage.{u} k,
    ((alephOmegaModelChain hk F a ha i).substructure :
      Set AlephOmegaOrdinal.{u})

theorem alephOmegaStageSeed_subset_modelChain
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (i : AlephOmegaChainStage.{u} k) :
    alephOmegaStageSeed hk F a i
        (fun j _ => alephOmegaModelChain hk F a ha j) ⊆
      (alephOmegaModelChain hk F a ha i).substructure := by
  rw [alephOmegaModelChain_eq_stageStep]
  simpa only [alephOmegaStageStep] using
    (alephOmegaElementaryHull_contains k hk
      (alephOmegaStageSeed hk F a i
        (fun j _ => alephOmegaModelChain hk F a ha j))
      (mk_alephOmegaStageSeed_le hk F a ha i
        (fun j _ => alephOmegaModelChain hk F a ha j)))

theorem alephOmegaModelChain_mono
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    {i j : AlephOmegaChainStage.{u} k} (hij : i <= j) :
    (alephOmegaModelChain hk F a ha i).substructure.toSubstructure <=
      (alephOmegaModelChain hk F a ha j).substructure.toSubstructure := by
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · intro x hx
    apply alephOmegaStageSeed_subset_modelChain hk F a ha j
    exact Or.inl (Or.inl (Or.inr
      (Set.mem_iUnion.2 ⟨⟨i, hij⟩, hx⟩)))

noncomputable def alephOmegaFinalSubstructure
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    alephOmegaClosureLanguage.Substructure AlephOmegaOrdinal.{u} :=
  ⨆ i : AlephOmegaChainStage.{u} k,
    (alephOmegaModelChain hk F a ha i).substructure.toSubstructure

theorem alephOmegaFinalSubstructure_mem_iff
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (x : AlephOmegaOrdinal.{u}) :
    x ∈ alephOmegaFinalSubstructure hk F a ha ↔
      exists i : AlephOmegaChainStage.{u} k,
        x ∈ (alephOmegaModelChain hk F a ha i).substructure := by
  let zero : AlephOmegaChainStage.{u} k :=
    Ordinal.ToType.mk ⟨0, Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans_le hk)⟩
  letI : Nonempty (AlephOmegaChainStage.{u} k) := ⟨zero⟩
  apply FirstOrder.Language.Substructure.mem_iSup_of_directed
  intro i j
  rcases le_total i j with hij | hji
  · exact ⟨j, alephOmegaModelChain_mono hk F a ha hij, le_rfl⟩
  · exact ⟨i, le_rfl, alephOmegaModelChain_mono hk F a ha hji⟩

theorem mk_alephOmegaModelUnion_le
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    Cardinal.mk (alephOmegaModelUnion hk F a ha) <=
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
  let family : AlephOmegaChainStage.{u} k ->
      Set AlephOmegaOrdinal.{u} := fun i =>
    ((alephOmegaModelChain hk F a ha i).substructure :
      Set AlephOmegaOrdinal.{u})
  have hUnion := Cardinal.mk_iUnion_le_lift family
  rw [Cardinal.lift_id'.{u, u + 1}] at hUnion
  have hLiftFamily : forall i,
      Cardinal.lift.{u} (Cardinal.mk (family i)) =
        Cardinal.mk (family i) := fun i =>
    Cardinal.lift_id'.{u, u + 1} (Cardinal.mk (family i))
  simp_rw [hLiftFamily] at hUnion
  have hIndex : Cardinal.lift.{u + 1}
      (Cardinal.mk (AlephOmegaChainStage.{u} k)) =
        Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
    rw [Cardinal.mk_ord_toType]
  have hFamily : forall i, Cardinal.mk (family i) =
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) := fun i =>
    (alephOmegaModelChain hk F a ha i).cardinal_eq
  calc
    Cardinal.mk (alephOmegaModelUnion hk F a ha) <=
        Cardinal.lift.{u + 1}
            (Cardinal.mk (AlephOmegaChainStage.{u} k)) *
          ⨆ i, Cardinal.mk (family i) := by
      simpa only [alephOmegaModelUnion, family] using hUnion
    _ = Cardinal.lift.{u + 1} (finiteAleph.{u} k) *
        Cardinal.lift.{u + 1} (finiteAleph.{u} k) := by
      rw [hIndex]
      congr 1
      apply le_antisymm
      · apply ciSup_le'
        intro i
        rw [hFamily i]
      · let zero : AlephOmegaChainStage.{u} k :=
          Ordinal.ToType.mk ⟨0, Cardinal.ord_pos.mpr
            (Cardinal.aleph0_pos.trans_le hk)⟩
        exact (hFamily zero) ▸ le_ciSup bddAbove_of_small zero
    _ = Cardinal.lift.{u + 1} (finiteAleph.{u} k) :=
      Cardinal.mul_eq_self
        (Cardinal.aleph0_le_lift.{u, u + 1}.mpr hk)

theorem alephOmegaBase_subset_finalSubstructure
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    alephOmegaBase.{u} k ⊆ alephOmegaFinalSubstructure hk F a ha := by
  intro x hx
  let zero : AlephOmegaChainStage.{u} k :=
    Ordinal.ToType.mk ⟨0, Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans_le hk)⟩
  apply (alephOmegaFinalSubstructure_mem_iff hk F a ha x).mpr
  refine ⟨zero, alephOmegaStageSeed_subset_modelChain hk F a ha zero ?_⟩
  exact Or.inl (Or.inl (Or.inl (Or.inl hx)))

theorem alephOmegaInput_subset_finalSubstructure
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    a ⊆ alephOmegaFinalSubstructure hk F a ha := by
  intro x hx
  let zero : AlephOmegaChainStage.{u} k :=
    Ordinal.ToType.mk ⟨0, Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans_le hk)⟩
  apply (alephOmegaFinalSubstructure_mem_iff hk F a ha x).mpr
  refine ⟨zero, alephOmegaStageSeed_subset_modelChain hk F a ha zero ?_⟩
  exact Or.inl (Or.inl (Or.inl (Or.inr hx)))

def alephOmegaChainPreviousCarrier
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (i : AlephOmegaChainStage.{u} k) :
    Set AlephOmegaOrdinal.{u} :=
  alephOmegaPreviousCarrier i
    (fun j _ => alephOmegaModelChain hk F a ha j)

theorem mk_alephOmegaChainPreviousCarrier_le
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (i : AlephOmegaChainStage.{u} k) :
    Cardinal.mk (alephOmegaChainPreviousCarrier hk F a ha i) <=
      Cardinal.lift.{u + 1} (finiteAleph.{u} k) :=
  mk_alephOmegaPreviousCarrier_le hk i
    (fun j _ => alephOmegaModelChain hk F a ha j)

noncomputable def alephOmegaFinalCharacteristic
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) : Ordinal.{u} :=
  alephOmegaSetCharacteristic k n (alephOmegaModelUnion hk F a ha)

theorem alephOmegaFinalCharacteristic_lt
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) :
    alephOmegaFinalCharacteristic hk F a ha n <
      (finiteAleph (k + n + 1)).ord :=
  alephOmegaSetCharacteristic_lt k n _
    (mk_alephOmegaModelUnion_le hk F a ha)

noncomputable def alephOmegaStageCharacteristic
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) (i : AlephOmegaChainStage.{u} k) : Ordinal.{u} :=
  alephOmegaSetCharacteristic k n
    (alephOmegaChainPreviousCarrier hk F a ha i)

theorem alephOmegaStageCharacteristicPoint_mem_final
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) (i : AlephOmegaChainStage.{u} k) :
    alephOmegaCharacteristicPoint k n
        (alephOmegaChainPreviousCarrier hk F a ha i)
        (mk_alephOmegaChainPreviousCarrier_le hk F a ha i) ∈
      alephOmegaFinalSubstructure hk F a ha := by
  apply (alephOmegaFinalSubstructure_mem_iff hk F a ha _).mpr
  refine ⟨i, alephOmegaStageSeed_subset_modelChain hk F a ha i ?_⟩
  exact Or.inl (Or.inr (Set.mem_range_self n))

theorem alephOmegaStageCharacteristic_lt_final
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) (i : AlephOmegaChainStage.{u} k) :
    alephOmegaStageCharacteristic hk F a ha n i <
      alephOmegaFinalCharacteristic hk F a ha n := by
  change (alephOmegaCharacteristicPoint k n
      (alephOmegaChainPreviousCarrier hk F a ha i)
      (mk_alephOmegaChainPreviousCarrier_le hk F a ha i)).1 <
    alephOmegaSetCharacteristic k n (alephOmegaModelUnion hk F a ha)
  apply lt_alephOmegaSetCharacteristic k n
    (alephOmegaModelUnion hk F a ha)
  · have hMem := alephOmegaStageCharacteristicPoint_mem_final
      hk F a ha n i
    rw [alephOmegaFinalSubstructure_mem_iff] at hMem
    obtain ⟨j, hj⟩ := hMem
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  · exact alephOmegaSetCharacteristic_lt k n _
      (mk_alephOmegaChainPreviousCarrier_le hk F a ha i)

noncomputable def alephOmegaStageCharacteristicInFinal
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) (i : AlephOmegaChainStage.{u} k) :
    Set.Iio (alephOmegaFinalCharacteristic hk F a ha n) :=
  ⟨alephOmegaStageCharacteristic hk F a ha n i,
    alephOmegaStageCharacteristic_lt_final hk F a ha n i⟩

theorem alephOmegaStageCharacteristicPoint_mem_modelChain
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) (i : AlephOmegaChainStage.{u} k) :
    alephOmegaCharacteristicPoint k n
        (alephOmegaChainPreviousCarrier hk F a ha i)
        (mk_alephOmegaChainPreviousCarrier_le hk F a ha i) ∈
      (alephOmegaModelChain hk F a ha i).substructure := by
  apply alephOmegaStageSeed_subset_modelChain hk F a ha i
  exact Or.inl (Or.inr (Set.mem_range_self n))

theorem alephOmegaModelChain_subset_chainPreviousCarrier
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    {i j : AlephOmegaChainStage.{u} k} (hij : i < j) :
    ((alephOmegaModelChain hk F a ha i).substructure :
        Set AlephOmegaOrdinal.{u}) ⊆
      alephOmegaChainPreviousCarrier hk F a ha j := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨i, hij⟩, hx⟩

theorem alephOmegaStageCharacteristic_strictMono
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) :
    StrictMono (alephOmegaStageCharacteristic hk F a ha n) := by
  intro i j hij
  change (alephOmegaCharacteristicPoint k n
      (alephOmegaChainPreviousCarrier hk F a ha i)
      (mk_alephOmegaChainPreviousCarrier_le hk F a ha i)).1 <
    alephOmegaSetCharacteristic k n
      (alephOmegaChainPreviousCarrier hk F a ha j)
  apply lt_alephOmegaSetCharacteristic k n _
  · apply alephOmegaModelChain_subset_chainPreviousCarrier hk F a ha hij
    exact alephOmegaStageCharacteristicPoint_mem_modelChain
      hk F a ha n i
  · exact alephOmegaSetCharacteristic_lt k n _
      (mk_alephOmegaChainPreviousCarrier_le hk F a ha i)

theorem alephOmegaStageCharacteristicInFinal_isCofinal
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) :
    IsCofinal (Set.range
      (alephOmegaStageCharacteristicInFinal hk F a ha n)) := by
  intro x
  have hx : x.1 < alephOmegaSetCharacteristic k n
      (alephOmegaModelUnion hk F a ha) := x.2
  unfold alephOmegaSetCharacteristic at hx
  have hBounded : BddAbove
      ((fun x : Ordinal.{u} => x + 1) ''
        alephOmegaBoundedValues k n
          (alephOmegaModelUnion hk F a ha)) :=
    ⟨(finiteAleph (k + n + 1)).ord, by
      rintro z ⟨y, hy, rfl⟩
      obtain ⟨p, hp, rfl⟩ := hy
      exact (Cardinal.isSuccLimit_ord
        (Cardinal.aleph0_le_aleph _)).add_one_lt hp.2 |>.le⟩
  obtain ⟨z, hz, hxz⟩ :=
    (lt_csSup_iff' (a := x.1) hBounded).mp hx
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨p, hp, rfl⟩ := hy
  have hyUnion := hp.1
  have hyUpper := hp.2
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hyUnion
  letI : NoMaxOrder (AlephOmegaChainStage.{u} k) :=
    Cardinal.noMaxOrder hk
  obtain ⟨i, hji⟩ := exists_gt j
  have hpCarrier : p ∈ alephOmegaChainPreviousCarrier hk F a ha i :=
    alephOmegaModelChain_subset_chainPreviousCarrier hk F a ha hji hj
  refine ⟨alephOmegaStageCharacteristicInFinal hk F a ha n i,
    Set.mem_range_self i, ?_⟩
  apply Subtype.mk_le_mk.mpr
  have hxle : x.1 ≤ p.1 := by
    exact Order.lt_add_one_iff.mp hxz
  exact hxle.trans
    (lt_alephOmegaSetCharacteristic k n _ hpCarrier hyUpper).le

theorem alephOmegaStageCharacteristicInFinal_dirSupClosed
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) :
    DirSupClosed (Set.range
      (alephOmegaStageCharacteristicInFinal hk F a ha n)) := by
  rw [dirSupClosed_iff_of_linearOrder]
  intro d hd hdNonempty z hz
  let f := alephOmegaStageCharacteristicInFinal hk F a ha n
  have hf : StrictMono f := by
    intro i j hij
    apply Subtype.mk_lt_mk.mpr
    exact alephOmegaStageCharacteristic_strictMono hk F a ha n hij
  have hExists : exists i : AlephOmegaChainStage.{u} k, z <= f i := by
    obtain ⟨y, hyRange, hzy⟩ :=
      alephOmegaStageCharacteristicInFinal_isCofinal hk F a ha n z
    obtain ⟨i, rfl⟩ := hyRange
    exact ⟨i, hzy⟩
  obtain ⟨i, hiMinimal⟩ := exists_minimal_of_wellFoundedLT
    (fun i : AlephOmegaChainStage.{u} k => z <= f i) hExists
  have hi := minimal_iff_forall_lt.mp hiMinimal
  by_cases hzi : z = f i
  · exact hzi.symm ▸ Set.mem_range_self i
  have hziLt : z < f i := hi.1.lt_of_ne hzi
  have hBetween : forall j : AlephOmegaChainStage.{u} k, j < i ->
      exists l : AlephOmegaChainStage.{u} k, j < l ∧ l < i := by
    intro j hji
    by_contra hNoBetween
    have hUpper : forall w, w ∈ d -> w <= f j := by
      intro w hw
      obtain ⟨r, rfl⟩ := hd hw
      have hri : r < i := hf.lt_iff_lt.mp ((hz.1 hw).trans_lt hziLt)
      have hrj : r <= j := by
        apply le_of_not_gt
        intro hjr
        exact hNoBetween ⟨r, hjr, hri⟩
      exact hf.monotone hrj
    exact (hi.2 hji) (hz.2 hUpper)
  have hStageLe :
      alephOmegaStageCharacteristic hk F a ha n i <= z.1 := by
    unfold alephOmegaStageCharacteristic alephOmegaSetCharacteristic
    apply csSup_le'
    intro b hb
    obtain ⟨y, hy, rfl⟩ := hb
    obtain ⟨p, hp, rfl⟩ := hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hp.1
    obtain ⟨l, hjl, hli⟩ := hBetween j.1 j.2
    have hpCarrier : p ∈
        alephOmegaChainPreviousCarrier hk F a ha l :=
      alephOmegaModelChain_subset_chainPreviousCarrier
        hk F a ha hjl hj
    have hpLt : p.1 <
        alephOmegaStageCharacteristic hk F a ha n l :=
      lt_alephOmegaSetCharacteristic k n _ hpCarrier hp.2
    have hStageLtZ :
        alephOmegaStageCharacteristic hk F a ha n l < z.1 := by
      have hNot : ¬ z <= f l := hi.2 hli
      exact lt_of_not_ge (fun h => hNot (Subtype.mk_le_mk.mpr h))
    exact (Order.add_one_le_iff.mpr hpLt).trans hStageLtZ.le
  have : f i <= z := Subtype.mk_le_mk.mpr hStageLe
  exact (not_lt_of_ge this hziLt).elim

theorem alephOmegaStageCharacteristicInFinal_isClub
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) :
    IsClub (Set.range
      (alephOmegaStageCharacteristicInFinal hk F a ha n)) :=
  ⟨alephOmegaStageCharacteristicInFinal_dirSupClosed hk F a ha n,
    alephOmegaStageCharacteristicInFinal_isCofinal hk F a ha n⟩

theorem alephOmegaFinalCharacteristic_cof_ne_aleph0
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (hkUncountable : Cardinal.aleph0 < finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) :
    Order.cof (Set.Iio
      (alephOmegaFinalCharacteristic hk F a ha n)) ≠ Cardinal.aleph0 := by
  intro hCof
  let target := Set.Iio (alephOmegaFinalCharacteristic hk F a ha n)
  let f := alephOmegaStageCharacteristicInFinal hk F a ha n
  have hf : StrictMono f := by
    intro i j hij
    apply Subtype.mk_lt_mk.mpr
    exact alephOmegaStageCharacteristic_strictMono hk F a ha n hij
  obtain ⟨s, hsCofinal, hsCard⟩ := Order.exists_cof_eq target
  have hsCardAleph0 : Cardinal.mk s = Cardinal.aleph0 :=
    hsCard.trans hCof
  choose y hyRange hxy using fun x : s =>
    (alephOmegaStageCharacteristicInFinal_isCofinal
      hk F a ha n) x.1
  choose index hindex using fun x : s => hyRange x
  have hxIndex : forall x : s, x.1 <= f (index x) := by
    intro x
    exact (hxy x).trans_eq (hindex x).symm
  have hCofStage : Order.cof (AlephOmegaChainStage.{u} k) =
      finiteAleph.{u} k := by
    rw [Ordinal.cof_toType, (finiteAleph_isRegular k).cof_ord]
  have hIndexNotCofinal : ¬ IsCofinal (Set.range index) := by
    intro hIndexCofinal
    have hSmall : Cardinal.mk (Set.range index) <= Cardinal.aleph0 := by
      have hRange := Cardinal.mk_range_le_lift (f := index)
      rw [Cardinal.lift_id'.{u, u + 1}] at hRange
      have hLiftSmall : Cardinal.lift.{u + 1}
          (Cardinal.mk (Set.range index)) <= Cardinal.aleph0 := by
        calc
          Cardinal.lift.{u + 1} (Cardinal.mk (Set.range index)) <=
              Cardinal.mk s := by simpa using hRange
          _ = Cardinal.aleph0 := hsCardAleph0
      have hLiftSmall' : Cardinal.lift.{u + 1}
          (Cardinal.mk (Set.range index)) <=
          Cardinal.lift.{u + 1} (Cardinal.aleph0.{u}) := by
        simpa only [Cardinal.lift_aleph0] using hLiftSmall
      exact Cardinal.lift_le.mp hLiftSmall'
    have hLe : finiteAleph.{u} k <= Cardinal.aleph0 := by
      rw [← hCofStage]
      exact (Order.cof_le hIndexCofinal).trans hSmall
    exact (not_le_of_gt hkUncountable) hLe
  obtain ⟨j, hj⟩ := BddAbove.of_not_isCofinal hIndexNotCofinal
  letI : NoMaxOrder (AlephOmegaChainStage.{u} k) :=
    Cardinal.noMaxOrder hk
  obtain ⟨l, hjl⟩ := exists_gt j
  obtain ⟨z, hzS, hflz⟩ := hsCofinal (f l)
  let z' : s := ⟨z, hzS⟩
  have hzUpper : z <= f j :=
    (hxIndex z').trans (hf.monotone (hj (Set.mem_range_self z')))
  exact (not_lt_of_ge (hflz.trans hzUpper) (hf hjl))

theorem alephOmegaFinalSubstructure_below_characteristic
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (n : Nat) (x : AlephOmegaOrdinal.{u})
    (hx : x ∈ alephOmegaFinalSubstructure hk F a ha)
    (hxUpper : x.1 < (finiteAleph (k + n + 1)).ord) :
    x.1 < alephOmegaFinalCharacteristic hk F a ha n := by
  apply lt_alephOmegaSetCharacteristic k n _
  · rw [alephOmegaFinalSubstructure_mem_iff] at hx
    obtain ⟨i, hi⟩ := hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  · exact hxUpper

theorem alephOmegaForward_value
    (n : Nat) (gamma xi : AlephOmegaOrdinal.{u})
    (hLower : (finiteAleph n).ord ≤ gamma.1)
    (hUpper : gamma.1 < (finiteAleph (n + 1)).ord)
    (hXi : xi.1 < (finiteAleph n).ord) :
    (alephOmegaForward n gamma xi).1 =
      (finiteAlephIntervalEquiv n gamma.1 hLower hUpper ⟨xi.1, hXi⟩).1 := by
  unfold alephOmegaForward
  rw [dif_pos hLower, dif_pos hUpper, dif_pos hXi]

theorem alephOmegaBackward_value
    (n : Nat) (gamma eta : AlephOmegaOrdinal.{u})
    (hLower : (finiteAleph n).ord ≤ gamma.1)
    (hUpper : gamma.1 < (finiteAleph (n + 1)).ord)
    (hEta : eta.1 < gamma.1) :
    (alephOmegaBackward n gamma eta).1 =
      ((finiteAlephIntervalEquiv n gamma.1 hLower hUpper).symm
        ⟨eta.1, hEta⟩).1 := by
  unfold alephOmegaBackward
  rw [dif_pos hLower, dif_pos hUpper, dif_pos hEta]

theorem alephOmegaForward_backward
    (n : Nat) (gamma eta : AlephOmegaOrdinal.{u})
    (hLower : (finiteAleph n).ord ≤ gamma.1)
    (hUpper : gamma.1 < (finiteAleph (n + 1)).ord)
    (hEta : eta.1 < gamma.1) :
    alephOmegaForward n gamma (alephOmegaBackward n gamma eta) = eta := by
  apply Subtype.ext
  have hBack : (alephOmegaBackward n gamma eta).1 <
      (finiteAleph n).ord := by
    rw [alephOmegaBackward_value n gamma eta hLower hUpper hEta]
    exact ((finiteAlephIntervalEquiv n gamma.1 hLower hUpper).symm
      ⟨eta.1, hEta⟩).2
  rw [alephOmegaForward_value n gamma (alephOmegaBackward n gamma eta)
    hLower hUpper hBack]
  let x := (finiteAlephIntervalEquiv n gamma.1 hLower hUpper).symm
    ⟨eta.1, hEta⟩
  have hx : (⟨(alephOmegaBackward n gamma eta).1, hBack⟩ :
      Set.Iio (finiteAleph n).ord) = x := by
    apply Subtype.ext
    exact alephOmegaBackward_value n gamma eta hLower hUpper hEta
  rw [hx]
  exact congrArg Subtype.val
    ((finiteAlephIntervalEquiv n gamma.1 hLower hUpper).apply_symm_apply
      ⟨eta.1, hEta⟩)

theorem alephOmegaSubstructure_forward_mem
    (S : alephOmegaClosureLanguage.Substructure AlephOmegaOrdinal.{u})
    (n : Nat) {gamma xi : AlephOmegaOrdinal.{u}}
    (hGamma : gamma ∈ S) (hXi : xi ∈ S) :
    alephOmegaForward n gamma xi ∈ S := by
  have h := S.fun_mem (AlephOmegaClosureFunc.forward n)
    ![gamma, xi] (by
      simp [hGamma, hXi])
  change alephOmegaForward n gamma xi ∈ S at h
  exact h

theorem alephOmegaSubstructure_backward_mem
    (S : alephOmegaClosureLanguage.Substructure AlephOmegaOrdinal.{u})
    (n : Nat) {gamma eta : AlephOmegaOrdinal.{u}}
    (hGamma : gamma ∈ S) (hEta : eta ∈ S) :
    alephOmegaBackward n gamma eta ∈ S := by
  have h := S.fun_mem (AlephOmegaClosureFunc.backward n)
    ![gamma, eta] (by
      simp [hGamma, hEta])
  change alephOmegaBackward n gamma eta ∈ S at h
  exact h

theorem alephOmegaSubstructure_mem_iff_backward_mem
    (S : alephOmegaClosureLanguage.Substructure AlephOmegaOrdinal.{u})
    (n : Nat) {gamma eta : AlephOmegaOrdinal.{u}}
    (hGamma : gamma ∈ S)
    (hLower : (finiteAleph n).ord ≤ gamma.1)
    (hUpper : gamma.1 < (finiteAleph (n + 1)).ord)
    (hEta : eta.1 < gamma.1) :
    eta ∈ S ↔ alephOmegaBackward n gamma eta ∈ S := by
  constructor
  · exact alephOmegaSubstructure_backward_mem S n hGamma
  · intro hBack
    rw [← alephOmegaForward_backward n gamma eta hLower hUpper hEta]
    exact alephOmegaSubstructure_forward_mem S n hGamma hBack

theorem alephOmegaSubstructure_mem_iff_of_common_interval_point
    (S T : alephOmegaClosureLanguage.Substructure AlephOmegaOrdinal.{u})
    (n : Nat) {gamma eta : AlephOmegaOrdinal.{u}}
    (hGammaS : gamma ∈ S) (hGammaT : gamma ∈ T)
    (hLower : (finiteAleph n).ord ≤ gamma.1)
    (hUpper : gamma.1 < (finiteAleph (n + 1)).ord)
    (hEta : eta.1 < gamma.1)
    (hAgreeLower : forall x : AlephOmegaOrdinal.{u},
      x.1 < (finiteAleph n).ord -> (x ∈ S ↔ x ∈ T)) :
    eta ∈ S ↔ eta ∈ T := by
  rw [alephOmegaSubstructure_mem_iff_backward_mem S n hGammaS
      hLower hUpper hEta,
    alephOmegaSubstructure_mem_iff_backward_mem T n hGammaT
      hLower hUpper hEta]
  apply hAgreeLower
  rw [alephOmegaBackward_value n gamma eta hLower hUpper hEta]
  exact ((finiteAlephIntervalEquiv n gamma.1 hLower hUpper).symm
    ⟨eta.1, hEta⟩).2

theorem alephOmegaSubstructures_agree_next_of_characteristic_clubs
    (S T : alephOmegaClosureLanguage.Substructure AlephOmegaOrdinal.{u})
    (n : Nat) (delta : Ordinal.{u})
    (hDeltaUpper : delta < (finiteAleph (n + 1)).ord)
    (hUpperTarget : (finiteAleph (n + 1)).ord <
      targetAlephOmega.ord)
    (hCofNe : Order.cof (Set.Iio delta) ≠ Cardinal.aleph0)
    (CS CT : Set (Set.Iio delta))
    (hCS : IsClub CS) (hCT : IsClub CT)
    (hCSmem : forall gamma : Set.Iio delta, gamma ∈ CS ->
      (⟨gamma.1, gamma.2.trans
        (hDeltaUpper.trans hUpperTarget)⟩ : AlephOmegaOrdinal.{u}) ∈ S)
    (hCTmem : forall gamma : Set.Iio delta, gamma ∈ CT ->
      (⟨gamma.1, gamma.2.trans
        (hDeltaUpper.trans hUpperTarget)⟩ : AlephOmegaOrdinal.{u}) ∈ T)
    (hSBelow : forall x : AlephOmegaOrdinal.{u}, x ∈ S ->
      x.1 < (finiteAleph (n + 1)).ord -> x.1 < delta)
    (hTBelow : forall x : AlephOmegaOrdinal.{u}, x ∈ T ->
      x.1 < (finiteAleph (n + 1)).ord -> x.1 < delta)
    (hAgreeLower : forall x : AlephOmegaOrdinal.{u},
      x.1 < (finiteAleph n).ord -> (x ∈ S ↔ x ∈ T)) :
    forall eta : AlephOmegaOrdinal.{u},
      eta.1 < (finiteAleph (n + 1)).ord -> (eta ∈ S ↔ eta ∈ T) := by
  have hCommon : IsClub (CS ∩ CT) := hCS.inter hCofNe hCT
  have oneDirection : forall
      (U V : alephOmegaClosureLanguage.Substructure AlephOmegaOrdinal.{u})
      (CU CV : Set (Set.Iio delta)),
      IsClub (CU ∩ CV) ->
      (forall gamma : Set.Iio delta, gamma ∈ CU ->
        (⟨gamma.1, gamma.2.trans
          (hDeltaUpper.trans hUpperTarget)⟩ : AlephOmegaOrdinal.{u}) ∈ U) ->
      (forall gamma : Set.Iio delta, gamma ∈ CV ->
        (⟨gamma.1, gamma.2.trans
          (hDeltaUpper.trans hUpperTarget)⟩ : AlephOmegaOrdinal.{u}) ∈ V) ->
      (forall x : AlephOmegaOrdinal.{u}, x ∈ U ->
        x.1 < (finiteAleph (n + 1)).ord -> x.1 < delta) ->
      (forall x : AlephOmegaOrdinal.{u},
        x.1 < (finiteAleph n).ord -> (x ∈ U ↔ x ∈ V)) ->
      forall eta : AlephOmegaOrdinal.{u},
        eta.1 < (finiteAleph (n + 1)).ord -> eta ∈ U -> eta ∈ V := by
    intro U V CU CV hClub hCUmem hCVmem hUBelow hAgree eta hEtaUpper hEtaU
    have hEtaDelta : eta.1 < delta := hUBelow eta hEtaU hEtaUpper
    by_cases hDeltaLower : delta ≤ (finiteAleph n).ord
    · exact (hAgree eta (hEtaDelta.trans_le hDeltaLower)).mp hEtaU
    · have hLowerDelta : (finiteAleph n).ord < delta :=
        lt_of_not_ge hDeltaLower
      let lower : Set.Iio delta :=
        ⟨(finiteAleph n).ord, hLowerDelta⟩
      let eta' : Set.Iio delta := ⟨eta.1, hEtaDelta⟩
      obtain ⟨gamma, hGammaCommon, hTargetGamma⟩ :=
        hClub.isCofinal (max lower eta')
      have hLowerGamma : (finiteAleph n).ord ≤ gamma.1 := by
        exact (le_max_left lower eta').trans hTargetGamma
      have hEtaGamma : eta.1 ≤ gamma.1 := by
        exact (le_max_right lower eta').trans hTargetGamma
      let gamma' : AlephOmegaOrdinal.{u} :=
        ⟨gamma.1, gamma.2.trans (hDeltaUpper.trans hUpperTarget)⟩
      have hGammaU : gamma' ∈ U :=
        hCUmem gamma hGammaCommon.1
      have hGammaV : gamma' ∈ V :=
        hCVmem gamma hGammaCommon.2
      rcases hEtaGamma.eq_or_lt with hEq | hLt
      · have hEtaEq : eta = gamma' := by
          apply Subtype.ext
          exact hEq
        exact hEtaEq ▸ hGammaV
      · exact
          (alephOmegaSubstructure_mem_iff_of_common_interval_point
            U V n hGammaU hGammaV hLowerGamma
            (gamma.2.trans hDeltaUpper) hLt hAgree).mp hEtaU
  intro eta hEtaUpper
  constructor
  · exact oneDirection S T CS CT hCommon hCSmem hCTmem hSBelow
      hAgreeLower eta hEtaUpper
  · exact oneDirection T S CT CS (by simpa [Set.inter_comm] using hCommon)
      hCTmem hCSmem hTBelow
      (fun x hx => (hAgreeLower x hx).symm) eta hEtaUpper

/-! The exact abstract content of the model part of Jech's Lemma 24.22.
The model is represented only by the substructure needed for the selected
interval bijections.  At every tail coordinate it carries a club contained
in the model below its characteristic ordinal. -/
structure AlephOmegaCharacteristicModel
    (k : Nat) (chi : Nat -> Ordinal.{u}) where
  substructure :
    alephOmegaClosureLanguage.Substructure AlephOmegaOrdinal.{u}
  containsBase : forall x : AlephOmegaOrdinal.{u},
    x.1 < (finiteAleph k).ord -> x ∈ substructure
  characteristic_lt : forall n,
    chi n < (finiteAleph (k + n + 1)).ord
  characteristic_cof_ne_aleph0 : forall n,
    Order.cof (Set.Iio (chi n)) ≠ Cardinal.aleph0
  characteristicClub : forall n, Set (Set.Iio (chi n))
  characteristicClub_isClub : forall n,
    IsClub (characteristicClub n)
  characteristicClub_mem : forall n (gamma : Set.Iio (chi n)),
    gamma ∈ characteristicClub n ->
      (⟨gamma.1, gamma.2.trans
        ((characteristic_lt n).trans
          (finiteAleph_ord_lt_targetAlephOmega_ord (k + n + 1)))⟩ :
        AlephOmegaOrdinal.{u}) ∈ substructure
  below_characteristic : forall n (x : AlephOmegaOrdinal.{u}),
    x ∈ substructure ->
      x.1 < (finiteAleph (k + n + 1)).ord -> x.1 < chi n

theorem AlephOmegaCharacteristicModel.substructure_transport
    {k : Nat} {chi psi : Nat -> Ordinal.{u}}
    (h : chi = psi) (M : AlephOmegaCharacteristicModel k chi) :
    (h ▸ M).substructure = M.substructure := by
  cases h
  rfl

noncomputable def alephOmegaFinalCharacteristicModel
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (hkUncountable : Cardinal.aleph0 < finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    AlephOmegaCharacteristicModel k
      (alephOmegaFinalCharacteristic hk F a ha) where
  substructure := alephOmegaFinalSubstructure hk F a ha
  containsBase := by
    intro x hx
    exact alephOmegaBase_subset_finalSubstructure hk F a ha hx
  characteristic_lt :=
    alephOmegaFinalCharacteristic_lt hk F a ha
  characteristic_cof_ne_aleph0 :=
    alephOmegaFinalCharacteristic_cof_ne_aleph0
      hk hkUncountable F a ha
  characteristicClub := fun n => Set.range
    (alephOmegaStageCharacteristicInFinal hk F a ha n)
  characteristicClub_isClub :=
    alephOmegaStageCharacteristicInFinal_isClub hk F a ha
  characteristicClub_mem := by
    intro n gamma hGamma
    obtain ⟨i, rfl⟩ := hGamma
    have hMem := alephOmegaStageCharacteristicPoint_mem_final
      hk F a ha n i
    convert hMem using 1
  below_characteristic :=
    alephOmegaFinalSubstructure_below_characteristic hk F a ha

@[simp] theorem alephOmegaFinalCharacteristicModel_substructure
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (hkUncountable : Cardinal.aleph0 < finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0) :
    (alephOmegaFinalCharacteristicModel
      hk hkUncountable F a ha).substructure =
        alephOmegaFinalSubstructure hk F a ha := rfl

theorem AlephOmegaCharacteristicModel.agree_below_finiteAleph
    {k : Nat} {chi : Nat -> Ordinal.{u}}
    (M N : AlephOmegaCharacteristicModel k chi) :
    forall n (x : AlephOmegaOrdinal.{u}),
      x.1 < (finiteAleph (k + n)).ord ->
        (x ∈ M.substructure ↔ x ∈ N.substructure) := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp only [Nat.add_zero] at hx
      exact ⟨fun _ => N.containsBase x hx,
        fun _ => M.containsBase x hx⟩
  | succ n ih =>
      have hStep :=
        alephOmegaSubstructures_agree_next_of_characteristic_clubs
          M.substructure N.substructure (k + n) (chi n)
          (by simpa [Nat.add_assoc] using M.characteristic_lt n)
          (finiteAleph_ord_lt_targetAlephOmega_ord (k + n + 1))
          (M.characteristic_cof_ne_aleph0 n)
          (M.characteristicClub n) (N.characteristicClub n)
          (M.characteristicClub_isClub n)
          (N.characteristicClub_isClub n)
          (by
            intro gamma hGamma
            simpa [Nat.add_assoc] using
              M.characteristicClub_mem n gamma hGamma)
          (by
            intro gamma hGamma
            simpa [Nat.add_assoc] using
              N.characteristicClub_mem n gamma hGamma)
          (by
            intro x hx hUpper
            exact M.below_characteristic n x hx
              (by simpa [Nat.add_assoc] using hUpper))
          (by
            intro x hx hUpper
            exact N.below_characteristic n x hx
              (by simpa [Nat.add_assoc] using hUpper))
          (by
            intro x hx
            exact ih x (by simpa [Nat.add_assoc] using hx))
      intro x hx
      apply hStep x
      simpa [Nat.add_assoc, Nat.add_comm 1 n, Nat.add_left_comm] using hx

theorem AlephOmegaCharacteristicModel.substructure_eq
    {k : Nat} {chi : Nat -> Ordinal.{u}}
    (M N : AlephOmegaCharacteristicModel k chi) :
    M.substructure = N.substructure := by
  apply FirstOrder.Language.Substructure.ext
  intro x
  obtain ⟨q, hq⟩ :=
    AlephOmegaOrdinal.exists_lt_finiteAleph_ord x
  have hq' : x.1 < (finiteAleph (k + (q + 1))).ord := by
    exact hq.trans_le (Cardinal.ord_le_ord.mpr
      (Cardinal.aleph.monotone (by
        exact_mod_cast (by omega : q <= k + (q + 1)))))
  exact M.agree_below_finiteAleph N (q + 1) x hq'

theorem AlephOmegaCharacteristicModel.substructure_eq_of_characteristic_eq
    {k : Nat} {chi psi : Nat -> Ordinal.{u}}
    (M : AlephOmegaCharacteristicModel k chi)
    (N : AlephOmegaCharacteristicModel k psi)
    (h : chi = psi) :
    M.substructure = N.substructure := by
  let N' : AlephOmegaCharacteristicModel k chi := h.symm ▸ N
  exact (M.substructure_eq N').trans
    (AlephOmegaCharacteristicModel.substructure_transport h.symm N)

theorem alephOmegaFinalSubstructure_eq_of_characteristic_eq
    {k : Nat} (hk : Cardinal.aleph0 <= finiteAleph.{u} k)
    (hkUncountable : Cardinal.aleph0 < finiteAleph.{u} k)
    (F : AlephOmegaTailCofinalFamily.{u} k)
    (a b : Set AlephOmegaOrdinal.{u})
    (ha : Cardinal.mk a <= Cardinal.aleph0)
    (hb : Cardinal.mk b <= Cardinal.aleph0)
    (hCharacteristic :
      alephOmegaFinalCharacteristic hk F a ha =
        alephOmegaFinalCharacteristic hk F b hb) :
    alephOmegaFinalSubstructure hk F a ha =
      alephOmegaFinalSubstructure hk F b hb := by
  simpa only [alephOmegaFinalCharacteristicModel_substructure] using
    (AlephOmegaCharacteristicModel.substructure_eq_of_characteristic_eq
      (alephOmegaFinalCharacteristicModel hk hkUncountable F a ha)
      (alephOmegaFinalCharacteristicModel hk hkUncountable F b hb)
      hCharacteristic)

end PcfProject
