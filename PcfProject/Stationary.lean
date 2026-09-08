import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.FundamentalSequence
import Mathlib.Order.Interval.Set.InitialSeg

/-!
# Stationary sets over Mathlib club sets

Field provenance table:

- A. Mathlib native: `Set`, `IsClub`, `IsCofinal`, `Order.cof`,
  `Cardinal.aleph0`, `Set.Nonempty`, set intersection, set difference,
  complement, set-builder notation, indexed union/intersection,
  `Cardinal.mk`, `Cardinal.lift`, `Cardinal.IsRegular`, `Cardinal.ord`,
  `Ordinal.ToType`, `Cardinal.mk_Iic_lt`, `Ordinal.cof_toType`,
  `Cardinal.IsRegular.cof_ord`, and subset.
- B. Project-proved in this file:
  `stationary_meets_club`,
  `stationary_nonempty`,
  `stationary_mono`,
  `Nonstationary`,
  `nonstationary_empty`,
  `not_stationary_empty`,
  `nonstationary_iff_not_stationary`,
  `nonstationary_mono`,
  `nonstationary_union`,
  `nonstationary_iUnion_of_small`,
  `stationary_iUnion_of_stationary`,
  `exists_stationary_of_stationary_iUnion_of_small`,
  `exists_stationary_of_subset_iUnion_of_small`,
  `subset_iUnion_stationaryFiber_of_value_cover`,
  `exists_stationaryFiber_of_small_value_cover`,
  `exists_stationary_subset_eqOn_const_of_small_value_cover`,
  `exists_stationary_subset_eqOn_value_of_small_value_cover`,
  `exists_stationaryFiber_mem_of_range_subset_small`,
  `exists_stationaryFiber_of_range_subset_small`,
  `exists_stationary_subset_eqOn_const_of_range_subset_small`,
  `exists_stationary_subset_mem_eqOn_const_of_range_subset_small`,
  `exists_stationaryFiber_mem_lt_of_range_subset_small`,
  `exists_stationaryFiber_lt_of_range_subset_small`,
  `exists_stationary_subset_mem_lt_eqOn_const_of_range_subset_small`,
  `exists_stationaryFiber_of_small_range`,
  `exists_stationary_subset_eqOn_const_of_small_range`,
  `exists_stationaryFiber_mem_range_of_small_range`,
  `exists_stationary_subset_mem_range_eqOn_const_of_small_range`,
  `exists_stationaryFiber_mem_range_lt_of_small_range`,
  `exists_stationary_subset_mem_range_lt_eqOn_const_of_small_range`,
  `stationary_iUnion_iff_of_small`,
  `DiagonalInter`,
  `DiagonalClubHypothesis`,
  `DiagonalCofinalHypothesis`,
  `SmallInitialSegments`,
  `smallInitialSegments_ord_toType_of_isRegular`,
  `cof_ord_toType_ne_aleph0_of_isRegular_of_aleph0_lt`,
  `exists_mem_strict_upperBound_of_countable_subset_of_orderType_omega_one`,
  `mem_diagonalInter_iff`,
  `diagonalInter_mem`,
  `diagonalInter_dirSupClosed`,
  `diagonalInter_isClub_of_cofinal`,
  `diagonalClubHypothesis_of_diagonalCofinalHypothesis`,
  `diagonalCofinalHypothesis_of_small_initial_segments`,
  `diagonalClubHypothesis_of_small_initial_segments`,
  `mem_stationaryFiber_self`,
  `exists_stationaryFiber_of_diagonalClubHypothesis`,
  `exists_stationaryFiber_mem_range_of_diagonalClubHypothesis`,
  `exists_stationaryFiber_mem_of_range_subset_diagonalClubHypothesis`,
  `exists_stationaryFiber_lt_of_diagonalClubHypothesis`,
  `exists_stationaryFiber_mem_lt_of_range_subset_diagonalClubHypothesis`,
  `exists_stationary_subset_eqOn_const_of_diagonalClubHypothesis`,
  `exists_stationary_subset_lt_eqOn_const_of_diagonalClubHypothesis`,
  `exists_stationary_subset_mem_range_eqOn_const_of_diagonalClubHypothesis`,
  `exists_stationary_subset_mem_eqOn_const_of_range_subset_diagonalClubHypothesis`,
  `exists_stationary_subset_mem_lt_eqOn_const_of_range_subset_diagonalClubHypothesis`,
  `exists_stationaryFiber_of_diagonalCofinalHypothesis`,
  `exists_stationaryFiber_mem_range_of_diagonalCofinalHypothesis`,
  `exists_stationaryFiber_mem_of_range_subset_diagonalCofinalHypothesis`,
  `exists_stationaryFiber_lt_of_diagonalCofinalHypothesis`,
  `exists_stationaryFiber_mem_lt_of_range_subset_diagonalCofinalHypothesis`,
  `exists_stationary_subset_eqOn_const_of_diagonalCofinalHypothesis`,
  `exists_stationary_subset_lt_eqOn_const_of_diagonalCofinalHypothesis`,
  `exists_stationary_subset_mem_range_eqOn_const_of_diagonalCofinalHypothesis`,
  `exists_stationary_subset_mem_eqOn_const_of_range_subset_diagonalCofinalHypothesis`,
  `exists_stationary_subset_mem_lt_eqOn_const_of_range_subset_diagonalCofinalHypothesis`,
  `exists_stationaryFiber_of_small_initial_segments`,
  `exists_stationary_subset_eqOn_const_of_small_initial_segments`,
  `exists_stationary_subset_mem_range_lt_eqOn_const_of_small_initial_segments`,
  `exists_stationaryFiber_ord_toType_of_isRegular_of_aleph0_lt`,
  `exists_stationary_subset_eqOn_const_ord_toType_of_isRegular_of_aleph0_lt`,
  `exists_stationary_subset_mem_range_lt_eqOn_const_ord_toType_of_isRegular_of_aleph0_lt`,
  `IsClub.isNormal_subtypeVal`,
  `isClub_image_of_isNormal_of_isCofinal`,
  `isClub_Ici`,
  `stationary_isCofinal`,
  `isClub_nonempty`,
  `isClub_stationary`,
  `univ_stationary`,
  `stationary_union_of_left`,
  `stationary_union_of_right`,
  `stationary_union_iff`,
  `not_stationary_iff_exists_club_avoids`,
  `stationary_inter_isClub`,
  `stationary_diff_of_nonstationary`,
  `compl_stationary_of_nonstationary`,
  `mem_stationaryFiber_iff`,
  `stationaryFiber_subset_base`,
  `stationaryFiber_value`,
  `stationaryFiber_eqOn_const`,
  `stationaryFiber_mapsTo_singleton`,
  `stationaryFiber_nonempty`,
  `stationaryFiber_exists_mem_eq`,
  `regressiveOn_stationaryFiber_exists_lt`,
  `regressiveOn_stationaryFiber_lt`,
  `stationary_of_stationaryFiber`,
  `exists_stationary_subset_eqOn_const_of_stationaryFiber`.
- C. Pressing-down scope:
  pressing down is proved for the
  canonical well-order `c.ord.ToType` of every regular uncountable cardinal
  `c`. Transport to other concrete presentations requires an order isomorphism
  and is not asserted here.
-/

namespace PcfProject

open scoped Cardinal

universe u v

open Set

def Stationary {alpha : Type u} [LinearOrder alpha] (S : Set alpha) : Prop :=
  forall C : Set alpha, IsClub C -> (S.inter C).Nonempty

def ClubAvoids {alpha : Type u} (S C : Set alpha) : Prop :=
  forall x, x ∈ C -> Not (x ∈ S)

def Nonstationary {alpha : Type u} [LinearOrder alpha] (S : Set alpha) :
    Prop :=
  exists C : Set alpha, IsClub C /\ ClubAvoids S C

theorem nonstationary_empty
    {alpha : Type u}
    [LinearOrder alpha] :
    Nonstationary (∅ : Set alpha) := by
  refine ⟨Set.univ, IsClub.univ, ?_⟩
  intro x _hxUniv hxEmpty
  exact hxEmpty

def RegressiveOn {alpha : Type u} [LT alpha] (S : Set alpha)
    (f : alpha -> alpha) : Prop :=
  forall x, x ∈ S -> f x < x

def StationaryFiber {alpha : Type u} (S : Set alpha) (f : alpha -> alpha)
    (beta : alpha) : Set alpha :=
  S.inter {x | f x = beta}

def DiagonalInter {alpha : Type u} [LT alpha]
    (C : alpha -> Set alpha) : Set alpha :=
  {x | forall beta, beta < x -> x ∈ C beta}

def DiagonalClubHypothesis {alpha : Type u} [LinearOrder alpha] : Prop :=
  forall C : alpha -> Set alpha,
    (forall beta, IsClub (C beta)) ->
    IsClub (DiagonalInter C)

def DiagonalCofinalHypothesis {alpha : Type u} [LinearOrder alpha] : Prop :=
  forall C : alpha -> Set alpha,
    (forall beta, IsClub (C beta)) ->
    IsCofinal (DiagonalInter C)

def SmallInitialSegments {alpha : Type u} [LinearOrder alpha] : Prop :=
  forall a : alpha,
    Cardinal.lift.{u, u} (Cardinal.mk (Set.Iic a)) <
      Cardinal.lift.{u, u} (Order.cof alpha)

theorem smallInitialSegments_ord_toType_of_isRegular
    {c : Cardinal.{u}}
    (hc : c.IsRegular) :
    SmallInitialSegments (alpha := c.ord.ToType) := by
  intro a
  rw [Ordinal.cof_toType, hc.cof_ord]
  simpa using Cardinal.mk_Iic_lt a (by simp) (by
    simpa using hc.aleph0_le)

/-! The literal ordinal interval below the initial ordinal of a regular
cardinal has small closed initial segments.  This is the source-index form
needed when pressing down directly on `Iio c.ord`, rather than transporting
the argument through `c.ord.ToType`. -/
theorem smallInitialSegments_Iio_ord_of_isRegular
    {c : Cardinal.{u}}
    (hc : c.IsRegular) :
    SmallInitialSegments (alpha := Set.Iio c.ord) := by
  intro a
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, hc.cof_ord]
  simpa [Cardinal.mk_Iio_ordinal, Cardinal.card_ord] using
    Cardinal.mk_Iic_lt a (by simp) (by
      simpa [Cardinal.mk_Iio_ordinal, Cardinal.card_ord] using
        Cardinal.lift_le.{u + 1, u}.mpr hc.aleph0_le)

theorem cof_ord_toType_ne_aleph0_of_isRegular_of_aleph0_lt
    {c : Cardinal.{u}}
    (hc : c.IsRegular)
    (huncountable : Cardinal.aleph0 < c) :
    Not (Order.cof c.ord.ToType = Cardinal.aleph0) := by
  rw [Ordinal.cof_toType, hc.cof_ord]
  exact ne_of_gt huncountable

/-! A countable subset of a set of ordinals of order type `omega_1` is
strictly bounded by another member of the ambient set.  This is the pure
ordinal compactness step used after the PCF Localization Lemma in Jech's
property (24.18)(iii). -/
theorem exists_mem_strict_upperBound_of_countable_subset_of_orderType_omega_one
    {X W : Set (Ordinal.{u})}
    (hWX : W ⊆ X)
    (hW : W.Countable)
    (hType : Ordinal.type ((· < ·) : X -> X -> Prop) =
      Ordinal.omega.{u + 1} 1) :
    exists gamma, gamma ∈ X ∧ forall w, w ∈ W -> w < gamma := by
  let e : W -> X := fun w => ⟨w.1, hWX w.2⟩
  haveI : Countable W := Set.countable_coe_iff.mpr hW
  let f : W -> Ordinal.{u + 1} := fun w =>
    Ordinal.typein ((· < ·) : X -> X -> Prop) (e w) +
      (1 : Ordinal.{u + 1})
  have hf : forall w, f w < Ordinal.omega.{u + 1} 1 := by
    intro w
    change Ordinal.typein ((· < ·) : X -> X -> Prop) (e w) + 1 <
      Ordinal.omega.{u + 1} 1
    have hLimitType : Order.IsSuccLimit
        (Ordinal.type ((· < ·) : X -> X -> Prop)) := by
      rw [hType]
      simpa only [Cardinal.ord_aleph] using
        (Cardinal.isSuccLimit_ord
          (Cardinal.aleph0_le_aleph (1 : Ordinal.{u + 1})))
    rw [← hType]
    exact hLimitType.add_one_lt
      (Ordinal.typein_lt_type _ (e w))
  have hSup : (⨆ w, f w) < Ordinal.omega.{u + 1} 1 :=
    Ordinal.iSup_lt_omega_one hf
  have hSupType : (⨆ w, f w) <
      Ordinal.type ((· < ·) : X -> X -> Prop) := by
    rw [hType]
    exact hSup
  let gammaX : X := Ordinal.enum ((· < ·) : X -> X -> Prop)
    ⟨⨆ w, f w, hSupType⟩
  refine ⟨gammaX.1, gammaX.2, ?_⟩
  intro w hw
  let wW : W := ⟨w, hw⟩
  have hTypeinLt :
      Ordinal.typein ((· < ·) : X -> X -> Prop) (e wW) <
        Ordinal.typein ((· < ·) : X -> X -> Prop) gammaX := by
    rw [Ordinal.typein_enum]
    exact (lt_add_one _).trans_le
      (Ordinal.le_iSup f wW)
  exact (Ordinal.typein_lt_typein
    ((· < ·) : X -> X -> Prop)).mp hTypeinLt

theorem stationary_meets_club
    {alpha : Type u}
    [LinearOrder alpha]
    {S C : Set alpha}
    (hS : Stationary S)
    (hC : IsClub C) :
    (S.inter C).Nonempty :=
  hS C hC

theorem stationary_nonempty
    {alpha : Type u}
    [LinearOrder alpha]
    {S : Set alpha}
    (hS : Stationary S) :
    S.Nonempty := by
  rcases hS Set.univ IsClub.univ with ⟨x, hxS, _hxUniv⟩
  exact ⟨x, hxS⟩

theorem stationary_mono
    {alpha : Type u}
    [LinearOrder alpha]
    {S T : Set alpha}
    (hST : S <= T)
    (hS : Stationary S) :
    Stationary T := by
  intro C hC
  rcases hS C hC with ⟨x, hxS, hxC⟩
  exact ⟨x, hST hxS, hxC⟩

theorem stationary_iUnion_of_stationary
    {alpha : Type u}
    [LinearOrder alpha]
    {idx : Type v}
    {S : idx -> Set alpha}
    {i : idx}
    (hSi : Stationary (S i)) :
    Stationary (Set.iUnion S) :=
  stationary_mono (by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨i, hx⟩) hSi

theorem stationary_union_of_left
    {alpha : Type u}
    [LinearOrder alpha]
    {S T : Set alpha}
    (hS : Stationary S) :
    Stationary (S ∪ T) :=
  stationary_mono (by
    intro x hx
    exact Or.inl hx) hS

theorem stationary_union_of_right
    {alpha : Type u}
    [LinearOrder alpha]
    {S T : Set alpha}
    (hT : Stationary T) :
    Stationary (S ∪ T) :=
  stationary_mono (by
    intro x hx
    exact Or.inr hx) hT

theorem nonstationary_mono
    {alpha : Type u}
    [LinearOrder alpha]
    {S T : Set alpha}
    (hST : S <= T)
    (hT : Nonstationary T) :
    Nonstationary S := by
  rcases hT with ⟨C, hC, hAvoids⟩
  exact ⟨C, hC, fun x hxC hxS => hAvoids x hxC (hST hxS)⟩

theorem nonstationary_union
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    {S T : Set alpha}
    (hS : Nonstationary S)
    (hT : Nonstationary T) :
    Nonstationary (S ∪ T) := by
  rcases hS with ⟨C, hC, hAvoidS⟩
  rcases hT with ⟨D, hD, hAvoidT⟩
  refine ⟨C.inter D, IsClub.inter hcof hC hD, ?_⟩
  intro x hxCD hxUnion
  rcases hxUnion with hxS | hxT
  · exact hAvoidS x hxCD.left hxS
  · exact hAvoidT x hxCD.right hxT

theorem nonstationary_iUnion_of_small
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    {ι : Type v}
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    (hι :
      Cardinal.lift.{u, v} (Cardinal.mk ι) <
        Cardinal.lift.{v, u} (Order.cof alpha))
    {S : ι -> Set alpha}
    (hS : forall i, Nonstationary (S i)) :
    Nonstationary (Set.iUnion S) := by
  classical
  choose C hC using hS
  refine ⟨Set.iInter C, IsClub.iInter hcof hι (fun i => (hC i).left), ?_⟩
  intro x hxInter hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxi⟩
  exact (hC i).right x (Set.mem_iInter.mp hxInter i) hxi

theorem mem_stationaryFiber_iff
    {alpha : Type u}
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta x : alpha} :
    x ∈ StationaryFiber S f beta <-> x ∈ S /\ f x = beta :=
  Iff.rfl

theorem stationaryFiber_subset_base
    {alpha : Type u}
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta : alpha} :
    StationaryFiber S f beta <= S := by
  intro x hx
  exact hx.left

theorem stationaryFiber_value
    {alpha : Type u}
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta x : alpha}
    (hx : x ∈ StationaryFiber S f beta) :
    f x = beta :=
  hx.right

theorem stationaryFiber_eqOn_const
    {alpha : Type u}
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta : alpha} :
    Set.EqOn f (fun _ => beta) (StationaryFiber S f beta) := by
  intro x hx
  exact hx.right

theorem stationaryFiber_mapsTo_singleton
    {alpha : Type u}
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta : alpha} :
    Set.MapsTo f (StationaryFiber S f beta) ({beta} : Set alpha) := by
  intro x hx
  exact hx.right

theorem mem_stationaryFiber_self
    {alpha : Type u}
    {S : Set alpha}
    {f : alpha -> alpha}
    {x : alpha}
    (hxS : x ∈ S) :
    x ∈ StationaryFiber S f (f x) :=
  And.intro hxS rfl

theorem stationaryFiber_nonempty
    {alpha : Type u}
    [LinearOrder alpha]
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta : alpha}
    (hFiber : Stationary (StationaryFiber S f beta)) :
    (StationaryFiber S f beta).Nonempty :=
  stationary_nonempty hFiber

theorem stationaryFiber_exists_mem_eq
    {alpha : Type u}
    [LinearOrder alpha]
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta : alpha}
    (hFiber : Stationary (StationaryFiber S f beta)) :
    exists x, x ∈ S /\ f x = beta := by
  rcases stationaryFiber_nonempty hFiber with ⟨x, hx⟩
  exact ⟨x, hx.left, hx.right⟩

theorem regressiveOn_stationaryFiber_lt
    {alpha : Type u}
    [LT alpha]
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta x : alpha}
    (hreg : RegressiveOn S f)
    (hx : x ∈ StationaryFiber S f beta) :
    beta < x := by
  have hlt : f x < x := hreg x hx.left
  rw [hx.right] at hlt
  exact hlt

theorem regressiveOn_stationaryFiber_exists_lt
    {alpha : Type u}
    [LinearOrder alpha]
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta : alpha}
    (hreg : RegressiveOn S f)
    (hFiber : Stationary (StationaryFiber S f beta)) :
    exists x, x ∈ S /\ f x = beta /\ beta < x := by
  rcases stationaryFiber_nonempty hFiber with ⟨x, hx⟩
  exact ⟨x, hx.left, hx.right, regressiveOn_stationaryFiber_lt hreg hx⟩

theorem stationary_of_stationaryFiber
    {alpha : Type u}
    [LinearOrder alpha]
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta : alpha}
    (hFiber : Stationary (StationaryFiber S f beta)) :
    Stationary S :=
  stationary_mono stationaryFiber_subset_base hFiber

theorem exists_stationary_subset_eqOn_const_of_stationaryFiber
    {alpha : Type u}
    [LinearOrder alpha]
    {S : Set alpha}
    {f : alpha -> alpha}
    {beta : alpha}
    (hFiber : Stationary (StationaryFiber S f beta)) :
    exists T : Set alpha,
      And (T <= S) (And (Stationary T) (Set.EqOn f (fun _ => beta) T)) := by
  exact Exists.intro (StationaryFiber S f beta)
    (And.intro
      (stationaryFiber_subset_base (S := S) (f := f) (beta := beta))
      (And.intro hFiber
        (stationaryFiber_eqOn_const (S := S) (f := f) (beta := beta))))

theorem mem_diagonalInter_iff
    {alpha : Type u}
    [LT alpha]
    {C : alpha -> Set alpha}
    {x : alpha} :
    x ∈ DiagonalInter C <->
      forall beta, beta < x -> x ∈ C beta :=
  Iff.rfl

theorem diagonalInter_mem
    {alpha : Type u}
    [LT alpha]
    {C : alpha -> Set alpha}
    {beta x : alpha}
    (hx : x ∈ DiagonalInter C)
    (hbeta : beta < x) :
    x ∈ C beta :=
  hx beta hbeta

theorem diagonalInter_dirSupClosed
    {alpha : Type u}
    [LinearOrder alpha]
    {C : alpha -> Set alpha}
    (hClosed : forall beta, DirSupClosed (C beta)) :
    DirSupClosed (DiagonalInter C) := by
  intro d hd hne hdir a ha beta hbeta
  have hExists : exists y, y ∈ d /\ beta < y := by
    by_contra hNo
    have hUpperBeta : beta ∈ upperBounds d := by
      intro y hy
      exact le_of_not_gt (by
        intro hbetaY
        exact hNo ⟨y, hy, hbetaY⟩)
    exact (not_lt_of_ge (ha.2 hUpperBeta)) hbeta
  rcases hExists with ⟨y, hyD, hbetaY⟩
  let e : Set alpha := d ∩ Set.Ici y
  have heSubset : e <= C beta := by
    intro z hz
    exact hd hz.left beta (lt_of_lt_of_le hbetaY hz.right)
  have heNonempty : e.Nonempty := ⟨y, hyD, le_rfl⟩
  have heDirected : DirectedOn (· <= ·) e := by
    intro p hp q hq
    rcases hdir p hp.left q hq.left with ⟨r, hrD, hpr, hqr⟩
    exact ⟨r, ⟨hrD, le_trans hp.right hpr⟩, hpr, hqr⟩
  have heLUB : IsLUB e a := by
    constructor
    · intro z hz
      exact ha.1 hz.left
    · intro b hb
      apply ha.2
      intro z hz
      rcases hdir z hz y hyD with ⟨r, hrD, hzr, hyr⟩
      exact le_trans hzr (hb ⟨hrD, hyr⟩)
  exact hClosed beta heSubset heNonempty heDirected heLUB

theorem diagonalInter_isClub_of_cofinal
    {alpha : Type u}
    [LinearOrder alpha]
    {C : alpha -> Set alpha}
    (hClub : forall beta, IsClub (C beta))
    (hCofinal : IsCofinal (DiagonalInter C)) :
    IsClub (DiagonalInter C) where
  dirSupClosed :=
    diagonalInter_dirSupClosed (fun beta => (hClub beta).dirSupClosed)
  isCofinal := hCofinal

theorem diagonalClubHypothesis_of_diagonalCofinalHypothesis
    {alpha : Type u}
    [LinearOrder alpha]
    (hCofinal : DiagonalCofinalHypothesis (alpha := alpha)) :
    DiagonalClubHypothesis (alpha := alpha) := by
  intro C hClub
  exact diagonalInter_isClub_of_cofinal hClub (hCofinal C hClub)

/-! Strict limit points of a set.  This is the `Lim(E)` operation used in
the standard recursive proof of club guessing. -/
def StrictLimitPoints {alpha : Type u} [LT alpha]
    (E : Set alpha) : Set alpha :=
  {x | (exists beta, beta < x) /\
    forall beta, beta < x ->
      exists y, y ∈ E /\ beta < y /\ y < x}

/-! A strict limit point of the whole order is a successor-limit element. -/
theorem isSuccLimit_of_mem_strictLimitPoints_univ
    {alpha : Type u}
    [LinearOrder alpha]
    {x : alpha}
    (hx : x ∈ StrictLimitPoints (Set.univ : Set alpha)) :
    Order.IsSuccLimit x := by
  refine ⟨not_isMin_iff.mpr hx.1, ?_⟩
  intro b hCov
  obtain ⟨c, _hc, hbc, hcx⟩ := hx.2 b hCov.lt
  exact ((not_covBy_iff hCov.lt).mpr ⟨c, hbc, hcx⟩) hCov

theorem strictLimitPoints_dirSupClosed
    {alpha : Type u}
    [LinearOrder alpha]
    {E : Set alpha} :
    DirSupClosed (StrictLimitPoints E) := by
  intro d hd hdNonempty _hdDirected a ha
  constructor
  · obtain ⟨x, hxD⟩ := hdNonempty
    obtain ⟨beta, hBetaX⟩ := (hd hxD).1
    exact ⟨beta, hBetaX.trans_le (ha.1 hxD)⟩
  intro beta hBetaA
  have hAbove : exists x, x ∈ d /\ beta < x := by
    by_contra hNo
    have hBetaUpper : beta ∈ upperBounds d := by
      intro x hx
      exact le_of_not_gt (fun hBetaX => hNo ⟨x, hx, hBetaX⟩)
    exact (not_lt_of_ge (ha.2 hBetaUpper)) hBetaA
  obtain ⟨x, hxD, hBetaX⟩ := hAbove
  obtain ⟨y, hyE, hBetaY, hYX⟩ := (hd hxD).2 beta hBetaX
  exact ⟨y, hyE, hBetaY, hYX.trans_le (ha.1 hxD)⟩

theorem strictLimitPoints_mono
    {alpha : Type u}
    [LT alpha]
    {E F : Set alpha}
    (hEF : E ⊆ F) :
    StrictLimitPoints E ⊆ StrictLimitPoints F := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro beta hBetaX
  obtain ⟨y, hyE, hBetaY, hyX⟩ := hx.2 beta hBetaX
  exact ⟨y, hEF hyE, hBetaY, hyX⟩

theorem strictLimitPoints_subset_of_dirSupClosed
    {alpha : Type u}
    [LinearOrder alpha]
    {E : Set alpha}
    (hE : DirSupClosed E) :
    StrictLimitPoints E ⊆ E := by
  intro x hx
  let below : Set alpha := {y | y ∈ E /\ y < x}
  have hBelowNonempty : below.Nonempty := by
    obtain ⟨beta, hBetaX⟩ := hx.1
    obtain ⟨y, hyE, _hBetaY, hyX⟩ := hx.2 beta hBetaX
    exact ⟨y, hyE, hyX⟩
  have hBelowSubset : below ⊆ E := fun _ hy => hy.1
  have hBelowDirected : DirectedOn (· <= ·) below := by
    intro a ha b hb
    rcases le_total a b with hab | hba
    · exact ⟨b, hb, hab, le_rfl⟩
    · exact ⟨a, ha, le_rfl, hba⟩
  have hBelowLUB : IsLUB below x := by
    constructor
    · intro y hy
      exact hy.2.le
    · intro b hb
      by_contra hXB
      have hBX : b < x := lt_of_not_ge hXB
      obtain ⟨y, hyE, hBY, hyX⟩ := hx.2 b hBX
      exact (not_lt_of_ge (hb ⟨hyE, hyX⟩)) hBY
  exact hE hBelowSubset hBelowNonempty hBelowDirected hBelowLUB

theorem strictLimitPoints_isCofinal
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    [Nonempty alpha]
    [NoMaxOrder alpha]
    (hcof : Order.cof alpha ≠ Cardinal.aleph0)
    {E : Set alpha}
    (hE : IsCofinal E) :
    IsCofinal (StrictLimitPoints E) := by
  classical
  letI := WellFoundedLT.toOrderBot alpha
  letI := WellFoundedLT.conditionallyCompleteLinearOrderBot alpha
  let next (x : alpha) : alpha := by
    let z : alpha := Classical.choose (exists_gt x)
    exact Classical.choose (hE z)
  have hNextMem (x : alpha) : next x ∈ E := by
    simp only [next]
    exact (Classical.choose_spec
      (hE (Classical.choose (exists_gt x)))).1
  have hNextGt (x : alpha) : x < next x := by
    simp only [next]
    exact (Classical.choose_spec (exists_gt x)).trans_le
      (Classical.choose_spec
        (hE (Classical.choose (exists_gt x)))).2
  intro a
  let g : Nat -> alpha := Nat.rec a (fun _ x => next x)
  have hGSuc (n : Nat) : g (n + 1) = next (g n) := by
    simp [g]
  have hGStrictStep (n : Nat) : g n < g (n + 1) := by
    rw [hGSuc]
    exact hNextGt (g n)
  have hGBdd : BddAbove (Set.range g) := by
    apply BddAbove.of_not_isCofinal
    intro hRange
    exact (Order.cof_le hRange).not_gt
      ((Order.aleph0_le_cof.lt_of_ne' hcof).trans_le' (by
        simpa using Cardinal.mk_range_le_lift (f := g)))
  let b : alpha := sSup (Set.range g)
  have hGLtSup (n : Nat) : g n < b := by
    exact (hGStrictStep n).trans_le
      (le_csSup hGBdd (Set.mem_range_self (n + 1)))
  have hBLimit : b ∈ StrictLimitPoints E := by
    refine ⟨⟨g 0, hGLtSup 0⟩, ?_⟩
    intro beta hBetaB
    change beta < sSup (Set.range g) at hBetaB
    obtain ⟨x, hxRange, hBetaX⟩ :=
      (lt_csSup_iff hGBdd (Set.range_nonempty g)).mp hBetaB
    obtain ⟨n, rfl⟩ := hxRange
    refine ⟨g (n + 1), ?_, hBetaX.trans (hGStrictStep n), ?_⟩
    · rw [hGSuc]
      exact hNextMem (g n)
    · exact hGLtSup (n + 1)
  exact ⟨b, hBLimit, le_csSup hGBdd (Set.mem_range_self 0)⟩

theorem strictLimitPoints_isClub
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    [Nonempty alpha]
    [NoMaxOrder alpha]
    (hcof : Order.cof alpha ≠ Cardinal.aleph0)
    {E : Set alpha}
    (hE : IsCofinal E) :
    IsClub (StrictLimitPoints E) where
  dirSupClosed := strictLimitPoints_dirSupClosed
  isCofinal := strictLimitPoints_isCofinal hcof hE

/-! A normal map with cofinal range has closed range even when its source and
target are different well-orders.  Mathlib's `IsNormal.isClub_range` is the
self-map specialization; this form is useful for continuous cofinal
sequences. -/
theorem isClub_range_of_isNormal_of_isCofinal
    {alpha : Type u} {beta : Type v}
    [LinearOrder alpha] [WellFoundedLT alpha]
    [LinearOrder beta]
    {f : alpha -> beta}
    (hf : Order.IsNormal f)
    (hCof : IsCofinal (Set.range f)) :
    IsClub (Set.range f) := by
  refine ⟨?_, hCof⟩
  intro s hs hsNonempty _ b hb
  have hPreNonempty : (f ⁻¹' s).Nonempty := by
    obtain ⟨y, hy⟩ := hsNonempty
    obtain ⟨x, rfl⟩ := hs hy
    exact ⟨x, hy⟩
  obtain ⟨zValue, ⟨z, rfl⟩, hbz⟩ := hCof b
  have hPreBdd : BddAbove (f ⁻¹' s) := by
    refine ⟨z, ?_⟩
    intro x hx
    exact hf.strictMono.le_iff_le.mp ((hb.1 hx).trans hbz)
  letI : Nonempty alpha := ⟨Classical.choose hPreNonempty⟩
  letI := WellFoundedLT.toOrderBot alpha
  letI := WellFoundedLT.conditionallyCompleteLinearOrderBot alpha
  have hPreLUB : IsLUB (f ⁻¹' s) (sSup (f ⁻¹' s)) :=
    isLUB_csSup hPreNonempty hPreBdd
  have hImageLUB := hf.map_isLUB hPreLUB hPreNonempty
  rw [Set.image_preimage_eq_of_subset hs] at hImageLUB
  obtain rfl := hb.unique hImageLUB
  exact Set.mem_range_self _

/-! The inclusion of a club into its ambient well-order is normal.  The only
subtle point is continuity at limit points of the club subtype: if the
supremum of the predecessors were below the point, the successor-prelimit
property would provide another club point strictly between them. -/
theorem IsClub.isNormal_subtypeVal
    {alpha : Type u}
    [LinearOrder alpha] [WellFoundedLT alpha] [Nonempty alpha]
    {C : Set alpha}
    (hC : IsClub C) :
    Order.IsNormal (fun c : C => c.1) := by
  letI := WellFoundedLT.toOrderBot alpha
  letI := WellFoundedLT.conditionallyCompleteLinearOrderBot alpha
  rw [Order.isNormal_iff]
  refine ⟨fun _ _ h => h, ?_⟩
  intro a ha b hb
  let S : Set alpha := (fun c : C => c.1) '' Set.Iio a
  have hSNonempty : S.Nonempty := by
    obtain ⟨c, hca⟩ := ha.nonempty_Iio
    exact ⟨c.1, ⟨c, hca, rfl⟩⟩
  have hSDirected : DirectedOn (· <= ·) S := by
    intro x hx y hy
    obtain ⟨cx, hcx, rfl⟩ := hx
    obtain ⟨cy, hcy, rfl⟩ := hy
    by_cases hxy : cx <= cy
    · exact ⟨cy.1, ⟨cy, hcy, rfl⟩, hxy, le_rfl⟩
    · have hyx : cy <= cx := le_of_not_ge hxy
      exact ⟨cx.1, ⟨cx, hcx, rfl⟩, le_rfl, hyx⟩
  have hSBdd : BddAbove S :=
    ⟨a.1, by
      rintro x ⟨c, hca, rfl⟩
      exact hca.le⟩
  have hSLUB : IsLUB S (sSup S) := isLUB_csSup hSNonempty hSBdd
  have hSupC : sSup S ∈ C :=
    hC.dirSupClosed (fun _ hx => by
      obtain ⟨c, _hc, rfl⟩ := hx
      exact c.2) hSNonempty hSDirected hSLUB
  have hSupEq : sSup S = a.1 := by
    apply le_antisymm
    · exact hSLUB.2 (by
        rintro x ⟨c, hca, rfl⟩
        exact hca.le)
    · apply le_of_not_gt
      intro hSupA
      let z : C := ⟨sSup S, hSupC⟩
      have hza : z < a := hSupA
      obtain ⟨c, hzc, hca⟩ :=
        (not_covBy_iff hza).mp (ha.2 z)
      have hcS : c.1 ∈ S := ⟨c, hca, rfl⟩
      exact (not_lt_of_ge (hSLUB.1 hcS)) hzc
  rw [← hSupEq]
  exact hSLUB.2 (by
    intro x hx
    obtain ⟨c, hca, rfl⟩ := hx
    exact hb c hca)

/-! A normal cofinal map sends every club in its source to a club in its
target.  This is the image counterpart to the preimage lemma below and is
the direction needed when restricting a club ultrafilter along a fundamental
sequence. -/
theorem isClub_image_of_isNormal_of_isCofinal
    {alpha : Type u} {beta : Type v}
    [LinearOrder alpha] [WellFoundedLT alpha] [Nonempty alpha]
    [LinearOrder beta]
    {f : alpha -> beta}
    (hf : Order.IsNormal f)
    (hCof : IsCofinal (Set.range f))
    {C : Set alpha}
    (hC : IsClub C) :
    IsClub (f '' C) := by
  let inclusion : C -> alpha := fun c => c.1
  have hInclusionNormal : Order.IsNormal inclusion :=
    PcfProject.IsClub.isNormal_subtypeVal hC
  have hCompNormal : Order.IsNormal (f ∘ inclusion) :=
    hf.comp hInclusionNormal
  have hCompCofinal : IsCofinal (Set.range (f ∘ inclusion)) := by
    intro b
    obtain ⟨fa, ⟨a, rfl⟩, hba⟩ := hCof b
    obtain ⟨c, hcC, hac⟩ := hC.isCofinal a
    exact ⟨f c, ⟨⟨c, hcC⟩, rfl⟩,
      hba.trans (hf.monotone hac)⟩
  have hRange : IsClub (Set.range (f ∘ inclusion)) :=
    isClub_range_of_isNormal_of_isCofinal hCompNormal hCompCofinal
  have hEq : Set.range (f ∘ inclusion) = f '' C := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨a, haC, rfl⟩
      exact ⟨⟨a, haC⟩, rfl⟩
  rw [← hEq]
  exact hRange

/-! Pulling a club back along a normal cofinal map again gives a club.  The
closure half is continuity of the normal map; for cofinality, intersect the
target club with the map's club range. -/
theorem isClub_preimage_of_isNormal_of_isCofinal
    {alpha : Type u} {beta : Type v}
    [LinearOrder alpha] [WellFoundedLT alpha]
    [LinearOrder beta] [WellFoundedLT beta]
    {f : alpha -> beta}
    (hf : Order.IsNormal f)
    (hCof : IsCofinal (Set.range f))
    (hBetaCof : Order.cof beta ≠ Cardinal.aleph0)
    {C : Set beta}
    (hC : IsClub C) :
    IsClub (f ⁻¹' C) := by
  have hRange : IsClub (Set.range f) :=
    isClub_range_of_isNormal_of_isCofinal hf hCof
  have hRangeInter : IsClub (Set.range f ∩ C) :=
    IsClub.inter hBetaCof hRange hC
  refine ⟨?_, ?_⟩
  · intro s hs hNonempty hDirected a hLUB
    apply hC.dirSupClosed (d := f '' s) (a := f a)
    · rintro _ ⟨x, hx, rfl⟩
      exact hs hx
    · exact hNonempty.image f
    · exact DirectedOn.mono_comp hf.monotone hDirected
    · exact hf.map_isLUB hLUB hNonempty
  · intro a
    obtain ⟨y, hy, hFaY⟩ := hRangeInter.isCofinal (f a)
    obtain ⟨⟨b, rfl⟩, hbC⟩ := hy
    exact ⟨b, hbC, hf.strictMono.le_iff_le.mp hFaY⟩

/-! Every fundamental sequence whose index ordinal is a successor limit can
be replaced by a continuous (normal) fundamental sequence.  At index `i` we
take the supremum of `q(j) + 1` for `j < i`; successor indices make the new
sequence strictly increasing, while limit indices make it continuous. -/
theorem exists_normal_isFundamentalSeq
    {a o : Ordinal.{u}}
    (hCof : o.cof.ord = a)
    (hLimit : Order.IsSuccLimit a) :
    exists f : Set.Iio a -> Set.Iio o,
      Ordinal.IsFundamentalSeq f /\ Order.IsNormal f := by
  classical
  obtain ⟨q, hq⟩ := Ordinal.exists_isFundamentalSeq hCof
  let qAt (i : Set.Iio a) : Ordinal.{u} := (q i).1
  let value (i : Set.Iio a) : Ordinal.{u} :=
    ⨆ j : Set.Iio i.1,
      qAt ⟨j.1, (show j.1 < a from j.2.trans i.2)⟩ + 1
  have hValueLe (i : Set.Iio a) : value i <= qAt i := by
    apply Ordinal.iSup_add_one_le
    intro j
    exact hq.strictMono j.2
  let f : Set.Iio a -> Set.Iio o :=
    fun i => ⟨value i, (hValueLe i).trans_lt (q i).2⟩
  have hStrict : StrictMono f := by
    intro i j hij
    have hStep : qAt i + 1 <= value j := by
      exact Ordinal.le_iSup
        (fun k : Set.Iio j.1 =>
          qAt ⟨k.1, (show k.1 < a from k.2.trans j.2)⟩ + 1)
        ⟨i.1, hij⟩
    exact (hValueLe i).trans_lt
      ((lt_add_one (qAt i)).trans_le hStep)
  letI : NoMaxOrder (Set.Iio a) := hLimit.isSuccPrelimit.noMaxOrder_Iio
  have hRangeCofinal : IsCofinal (Set.range f) := by
    intro b
    obtain ⟨qi, ⟨i, rfl⟩, hbi⟩ := hq.isCofinal_range b
    obtain ⟨j, hij⟩ := exists_gt i
    have hQiStep : qAt i + 1 <= value j := by
      exact Ordinal.le_iSup
        (fun k : Set.Iio j.1 =>
          qAt ⟨k.1, (show k.1 < a from k.2.trans j.2)⟩ + 1)
        ⟨i.1, hij⟩
    exact ⟨f j, Set.mem_range_self j,
      hbi.trans ((lt_add_one (qAt i)).trans_le hQiStep).le⟩
  have hNormal : Order.IsNormal f := by
    rw [Order.isNormal_iff]
    refine ⟨hStrict, ?_⟩
    intro i hi b hb
    apply Subtype.coe_le_coe.mp
    change value i <= b.1
    apply Ordinal.iSup_le
    intro k
    let kGlobal : Set.Iio a :=
      ⟨k.1, (show k.1 < a from k.2.trans i.2)⟩
    let jGlobal : Set.Iio a := Order.succ kGlobal
    have hJGlobalI : jGlobal < i := by
      exact hi.succ_lt k.2
    have hkStep : qAt kGlobal + 1 <= value jGlobal := by
      exact Ordinal.le_iSup
        (fun t : Set.Iio jGlobal.1 =>
          qAt ⟨t.1, (show t.1 < a from t.2.trans jGlobal.2)⟩ + 1)
        ⟨k.1, Order.lt_succ kGlobal⟩
    exact hkStep.trans (Subtype.coe_le_coe.mpr
      (hb jGlobal hJGlobalI))
  exact ⟨f, ⟨hCof.symm.le, hStrict, hRangeCofinal⟩, hNormal⟩

/-! A normal cofinal enumeration of an ordinal has fewer than `cof o`
many values below every fixed target stage.  The proof embeds that initial
part into a proper initial segment of the canonical cofinality index. -/
theorem mk_range_inter_Iio_lt_lift_cof
    {o : Ordinal.{u}}
    (q : Set.Iio o.cof.ord -> Set.Iio o)
    (hNormal : Order.IsNormal q)
    (hCofinal : IsCofinal (Set.range q))
    (alpha : Set.Iio o) :
    Cardinal.mk ↑(Set.range q ∩
      (Set.Iio alpha : Set (Set.Iio o))) <
      Cardinal.lift.{u + 1} o.cof := by
  obtain ⟨_, ⟨j, rfl⟩, hAlphaLe⟩ := hCofinal alpha
  have hSub : Set.range q ∩
      (Set.Iio alpha : Set (Set.Iio o)) ⊆
      q '' (Set.Iio j : Set (Set.Iio o.cof.ord)) := by
    rintro _ ⟨⟨i, rfl⟩, hi⟩
    refine ⟨i, ?_, rfl⟩
    exact hNormal.strictMono.lt_iff_lt.mp (hi.trans_le hAlphaLe)
  calc
    Cardinal.mk ↑(Set.range q ∩
        (Set.Iio alpha : Set (Set.Iio o))) ≤
        Cardinal.mk ↑(q ''
          (Set.Iio j : Set (Set.Iio o.cof.ord))) :=
      Cardinal.mk_subtype_mono hSub
    _ ≤ Cardinal.mk ↑(Set.Iio j : Set (Set.Iio o.cof.ord)) :=
      Cardinal.mk_image_le
    _ < Cardinal.mk (Set.Iio o.cof.ord) := by
      apply Cardinal.mk_Iio_lt
      rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
      exact (Cardinal.lift_ord o.cof).symm.trans
        (Ordinal.type_lt_Iio o.cof.ord).symm
    _ = Cardinal.lift.{u + 1} o.cof := by
      rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]

/-! Every limit ordinal has a club whose proper initial pieces have
cardinality strictly below the ordinal's cofinality.  This is the club system
used in the rapid recursion of Theorem 24.16. -/
theorem exists_club_with_initial_segments_mk_lt_cof
    {o : Ordinal.{u}}
    (hLimit : Order.IsSuccLimit o) :
    exists C : Set (Set.Iio o), IsClub C /\
      forall alpha : Set.Iio o,
        Cardinal.mk ↑(C ∩
          (Set.Iio alpha : Set (Set.Iio o))) <
          Cardinal.lift.{u + 1} o.cof := by
  obtain ⟨q, hFundamental, hNormal⟩ :=
    exists_normal_isFundamentalSeq (o := o) (a := o.cof.ord)
      rfl (Cardinal.isSuccLimit_ord
        (Ordinal.aleph0_le_cof_iff.mpr
          (Ordinal.one_lt_cof_iff.mpr hLimit)))
  refine ⟨Set.range q,
    isClub_range_of_isNormal_of_isCofinal
      hNormal hFundamental.isCofinal_range, ?_⟩
  intro alpha
  exact mk_range_inter_Iio_lt_lift_cof
    q hNormal hFundamental.isCofinal_range alpha

/-! A canonical choice of the preceding club, used to define all rapid
supports simultaneously.  Non-limit ordinals receive the empty set; only
the limit case is consumed below. -/
noncomputable def smallInitialClub
    (o : Ordinal.{u}) : Set (Set.Iio o) := by
  classical
  exact if h : Order.IsSuccLimit o then
      Classical.choose (exists_club_with_initial_segments_mk_lt_cof h)
    else ∅

theorem smallInitialClub_isClub
    {o : Ordinal.{u}}
    (hLimit : Order.IsSuccLimit o) :
    IsClub (smallInitialClub o) := by
  classical
  rw [smallInitialClub, dif_pos hLimit]
  exact (Classical.choose_spec
    (exists_club_with_initial_segments_mk_lt_cof hLimit)).1

theorem smallInitialClub_initial_mk_lt_cof
    {o : Ordinal.{u}}
    (hLimit : Order.IsSuccLimit o)
    (alpha : Set.Iio o) :
    Cardinal.mk ↑(smallInitialClub o ∩
      (Set.Iio alpha : Set (Set.Iio o))) <
      Cardinal.lift.{u + 1} o.cof := by
  classical
  rw [smallInitialClub, dif_pos hLimit]
  exact (Classical.choose_spec
    (exists_club_with_initial_segments_mk_lt_cof hLimit)).2 alpha

theorem diagonalCofinalHypothesis_of_small_initial_segments
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    (hSmall : SmallInitialSegments (alpha := alpha)) :
    DiagonalCofinalHypothesis (alpha := alpha) := by
  intro C hClub
  cases isEmpty_or_nonempty alpha with
  | inl => exact IsCofinal.of_isEmpty
  | inr hNonempty =>
      letI : Nonempty alpha := hNonempty
      cases topOrderOrNoTopOrder alpha with
      | inl hTop =>
          letI : OrderTop alpha := hTop
          intro a
          have hTopDiag : DiagonalInter C (Top.top : alpha) := by
            intro beta _hbeta
            exact (hClub beta).isCofinal.top_mem
          exact Exists.intro (Top.top : alpha) (And.intro hTopDiag le_top)
      | inr hNoTop =>
          letI : NoTopOrder alpha := hNoTop
          letI : NoMaxOrder alpha := NoTopOrder.to_noMaxOrder alpha
          letI := WellFoundedLT.toOrderBot alpha
          letI := WellFoundedLT.conditionallyCompleteLinearOrderBot alpha
          have hInterClub (x : alpha) :
              IsClub (Set.iInter (fun beta : Set.Iic x => C beta.1)) := by
            exact IsClub.iInter hcof (hSmall x) (fun beta => hClub beta.1)
          let next (x : alpha) : alpha :=
            Classical.choose ((hInterClub x).isCofinal x)
          have hnext_mem (x : alpha) :
              Set.iInter (fun beta : Set.Iic x => C beta.1) (next x) :=
            (Classical.choose_spec ((hInterClub x).isCofinal x)).left
          have hnext_ge (x : alpha) : x <= next x :=
            (Classical.choose_spec ((hInterClub x).isCofinal x)).right
          intro a
          let g : Nat -> alpha := Nat.rec a (fun _ x => next x)
          have hg_succ (n : Nat) : g (n + 1) = next (g n) := by
            simp [g]
          have hg_le_succ (n : Nat) : g n <= g (n + 1) := by
            rw [hg_succ]
            exact hnext_ge (g n)
          have hg_mono : Monotone g :=
            monotone_nat_of_le_succ hg_le_succ
          have hg_succ_mem (n : Nat) {beta : alpha}
              (hbeta : beta <= g n) : C beta (g (n + 1)) := by
            rw [hg_succ]
            exact Set.mem_iInter.mp (hnext_mem (g n))
              (Subtype.mk beta hbeta)
          have hgBdd : BddAbove (Set.range g) := by
            apply BddAbove.of_not_isCofinal
            intro hRange
            exact (Order.cof_le hRange).not_gt
              ((Order.aleph0_le_cof.lt_of_ne' hcof).trans_le' (by
                simpa using Cardinal.mk_range_le_lift (f := g)))
          let b : alpha := sSup (Set.range g)
          have hbDiag : DiagonalInter C b := by
            change (forall beta, beta < b -> C beta b)
            intro beta hbeta
            change beta < sSup (Set.range g) at hbeta
            have hExists :=
              (lt_csSup_iff hgBdd (Set.range_nonempty g)).mp hbeta
            cases hExists with
            | intro y hy =>
                cases Set.mem_range.mp hy.left with
                | intro n hyn =>
                    have hbetaN : beta < g n := by
                      rw [hyn]
                      exact hy.right
                    let tail : Nat -> alpha := fun k => g (n + 1 + k)
                    have htailSubset : Set.range tail <= C beta := by
                      intro z hz
                      cases Set.mem_range.mp hz with
                      | intro k hk =>
                          subst z
                          have hbetaCurrent : beta <= g (n + k) :=
                            le_trans (le_of_lt hbetaN)
                              (hg_mono (Nat.le_add_right n k))
                          simpa [tail, Nat.add_assoc, Nat.add_comm,
                            Nat.add_left_comm] using
                            hg_succ_mem (n + k) hbetaCurrent
                    have htailMono : Monotone tail := by
                      intro i j hij
                      exact hg_mono (Nat.add_le_add_left hij (n + 1))
                    have htailUpper : upperBounds (Set.range tail) b := by
                      intro z hz
                      cases Set.mem_range.mp hz with
                      | intro k hk =>
                          subst z
                          simpa [b, tail] using
                            le_csSup hgBdd
                              (Set.mem_range_self (n + 1 + k))
                    have htailLeast :
                        lowerBounds (upperBounds (Set.range tail)) b := by
                      intro c hc
                      change sSup (Set.range g) <= c
                      apply csSup_le (Set.range_nonempty g)
                      intro z hz
                      cases Set.mem_range.mp hz with
                      | intro k hk =>
                          subst z
                          have hTailLe : tail k <= c :=
                            hc (Set.mem_range_self k)
                          exact le_trans
                            (hg_mono (Nat.le_add_left k (n + 1)))
                            (by simpa [tail] using hTailLe)
                    have htailLUB : IsLUB (Set.range tail) b :=
                      And.intro htailUpper htailLeast
                    exact (hClub beta).dirSupClosed
                      htailSubset
                      (Set.range_nonempty tail)
                      (directedOn_range.mpr htailMono.directed_le)
                      htailLUB
          have hab : a <= b := by
            change a <= sSup (Set.range g)
            simpa [g] using le_csSup hgBdd (Set.mem_range_self 0)
          exact Exists.intro b (And.intro hbDiag hab)

theorem diagonalClubHypothesis_of_small_initial_segments
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    (hSmall : SmallInitialSegments (alpha := alpha)) :
    DiagonalClubHypothesis (alpha := alpha) :=
  diagonalClubHypothesis_of_diagonalCofinalHypothesis
    (diagonalCofinalHypothesis_of_small_initial_segments hcof hSmall)

theorem isClub_Ici
    {alpha : Type u}
    [LinearOrder alpha]
    (a : alpha) :
    IsClub (Set.Ici a) := by
  refine ⟨?_, ?_⟩
  · intro d hd hne _hdir x hx
    rcases hne with ⟨y, hy⟩
    exact (hd hy).trans (hx.left hy)
  · intro x
    refine ⟨max a x, ?_, ?_⟩
    · exact le_max_left a x
    · exact le_max_right a x

theorem stationary_isCofinal
    {alpha : Type u}
    [LinearOrder alpha]
    {S : Set alpha}
    (hS : Stationary S) :
    IsCofinal S := by
  intro a
  rcases hS (Set.Ici a) (isClub_Ici a) with ⟨x, hxS, hxa⟩
  exact ⟨x, hxS, hxa⟩

theorem isClub_nonempty
    {alpha : Type u}
    [LinearOrder alpha]
    [Nonempty alpha]
    {C : Set alpha}
    (hC : IsClub C) :
    C.Nonempty := by
  cases (inferInstance : Nonempty alpha) with
  | intro a =>
      cases hC.isCofinal a with
      | intro x hx =>
          exact Exists.intro x hx.left

theorem isClub_stationary
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    [Nonempty alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    {C : Set alpha}
    (hC : IsClub C) :
    Stationary C := by
  intro D hD
  have hInter : IsClub (C.inter D) :=
    IsClub.inter hcof hC hD
  exact isClub_nonempty hInter

theorem univ_stationary
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    [Nonempty alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0)) :
    Stationary (Set.univ : Set alpha) :=
  isClub_stationary hcof IsClub.univ

theorem not_stationary_iff_exists_club_avoids
    {alpha : Type u}
    [LinearOrder alpha]
    (S : Set alpha) :
    Not (Stationary S) <->
      exists C : Set alpha, IsClub C /\ ClubAvoids S C := by
  classical
  constructor
  · intro hNot
    unfold Stationary at hNot
    rcases Classical.not_forall.mp hNot with ⟨C, hCbad⟩
    have hClubAndNoMeet :
        IsClub C /\ Not ((S.inter C).Nonempty) :=
      Classical.not_imp.mp hCbad
    refine ⟨C, hClubAndNoMeet.left, ?_⟩
    intro x hxC hxS
    exact hClubAndNoMeet.right ⟨x, hxS, hxC⟩
  · rintro ⟨C, hC, hAvoids⟩ hS
    rcases hS C hC with ⟨x, hxS, hxC⟩
    exact hAvoids x hxC hxS

theorem nonstationary_iff_not_stationary
    {alpha : Type u}
    [LinearOrder alpha]
    (S : Set alpha) :
    Nonstationary S <-> Not (Stationary S) := by
  simpa [Nonstationary] using
    (not_stationary_iff_exists_club_avoids (S := S)).symm

theorem not_stationary_empty
    {alpha : Type u}
    [LinearOrder alpha] :
    Not (Stationary (∅ : Set alpha)) :=
  (nonstationary_iff_not_stationary (∅ : Set alpha)).mp nonstationary_empty

theorem stationary_union_iff
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    {S T : Set alpha} :
    Stationary (S ∪ T) <-> Stationary S ∨ Stationary T := by
  constructor
  · intro hUnion
    by_cases hS : Stationary S
    · exact Or.inl hS
    · by_cases hT : Stationary T
      · exact Or.inr hT
      · have hNonS : Nonstationary S :=
          (nonstationary_iff_not_stationary S).mpr hS
        have hNonT : Nonstationary T :=
          (nonstationary_iff_not_stationary T).mpr hT
        have hNonUnion : Nonstationary (S ∪ T) :=
          nonstationary_union hcof hNonS hNonT
        have hNotUnion : Not (Stationary (S ∪ T)) :=
          (nonstationary_iff_not_stationary (S ∪ T)).mp hNonUnion
        exact False.elim (hNotUnion hUnion)
  · intro h
    rcases h with hS | hT
    · exact stationary_union_of_left hS
    · exact stationary_union_of_right hT

theorem exists_stationary_of_stationary_iUnion_of_small
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    {ι : Type v}
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    (hι :
      Cardinal.lift.{u, v} (Cardinal.mk ι) <
        Cardinal.lift.{v, u} (Order.cof alpha))
    {S : ι -> Set alpha}
    (hUnion : Stationary (Set.iUnion S)) :
    exists i, Stationary (S i) := by
  classical
  by_contra hNone
  have hAllNon : forall i, Nonstationary (S i) := by
    intro i
    exact (nonstationary_iff_not_stationary (S i)).mpr (by
      intro hSi
      exact hNone ⟨i, hSi⟩)
  have hNonUnion : Nonstationary (Set.iUnion S) :=
    nonstationary_iUnion_of_small hcof hι hAllNon
  exact (nonstationary_iff_not_stationary (Set.iUnion S)).mp hNonUnion hUnion

/-! A coloring of a stationary set into fewer than the cofinality many
colors is constant on a stationary subset.  This packages the regular-fiber
step used in the elementary-submodel proof of Jech Lemma 24.10, without
requiring the color type to coincide with the ordered domain. -/
theorem exists_stationary_eqOn_const_of_small_codomain
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    [Nonempty alpha]
    {beta : Type v}
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    (hSmall : Cardinal.lift.{u, v} (Cardinal.mk beta) <
      Cardinal.lift.{v, u} (Order.cof alpha))
    (f : alpha -> beta)
    {S : Set alpha}
    (hS : Stationary S) :
    exists b : beta, exists T : Set alpha,
      T <= S /\ Stationary T /\ Set.EqOn f (fun _ => b) T := by
  let fiber : beta -> Set alpha := fun b => {a | S a /\ f a = b}
  have hUnion : Set.iUnion fiber = S := by
    ext a
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨b, ha, _⟩
      exact ha
    · intro ha
      exact ⟨f a, ha, rfl⟩
  have hStationaryUnion : Stationary (Set.iUnion fiber) := by
    rw [hUnion]
    exact hS
  obtain ⟨b, hb⟩ :=
    exists_stationary_of_stationary_iUnion_of_small hcof hSmall hStationaryUnion
  refine ⟨b, fiber b, ?_, hb, ?_⟩
  · intro a ha
    exact ha.1
  · intro a ha
    exact ha.2

theorem not_injOn_of_isCofinal_of_lift_mk_lt_lift_cof
    {alpha : Type u} {beta : Type v}
    [Preorder alpha]
    (hSmall : Cardinal.lift.{u, v} (Cardinal.mk beta) <
      Cardinal.lift.{v, u} (Order.cof alpha))
    (f : alpha -> beta)
    {S : Set alpha}
    (hS : IsCofinal S) :
    Not (Set.InjOn f S) := by
  intro hInjective
  let e : S ↪ beta :=
    ⟨fun x => f x.1, fun x y hxy =>
      Subtype.ext (hInjective x.2 y.2 hxy)⟩
  have hCardLe : Cardinal.lift.{v, u} (Cardinal.mk S) <=
      Cardinal.lift.{u, v} (Cardinal.mk beta) :=
    Cardinal.lift_mk_le'.mpr ⟨e⟩
  have hCofLe : Cardinal.lift.{v, u} (Order.cof alpha) <=
      Cardinal.lift.{v, u} (Cardinal.mk S) :=
    Cardinal.lift_le.mpr (Order.cof_le hS)
  exact (not_lt_of_ge (hCofLe.trans hCardLe)) hSmall

/-! Club-restricted form of the terminal small-range contradiction.  This
is the form used after aligning a normal failure recursion with a rapidity
club: strict increase is only needed at the club indices retained by that
alignment. -/
theorem no_repeated_coordinate_strict_pattern_on_club_of_lift_small
    {alpha : Type u} {A : Type v} {beta : Type w}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    [Nonempty alpha]
    [LinearOrder beta]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    (hASmall : Cardinal.lift.{u, v} (Cardinal.mk A) <
      Cardinal.lift.{v, u} (Order.cof alpha))
    {D : Set alpha}
    (hD : IsClub D)
    (coordinate : alpha -> A)
    (values : A -> alpha -> beta)
    (hValueSmall : forall a,
      Cardinal.lift.{u, w} (Cardinal.mk (Set.range (values a))) <
        Cardinal.lift.{w, u} (Order.cof alpha))
    (hStrict : forall {i j}, i ∈ D -> j ∈ D -> i < j ->
      coordinate i = coordinate j ->
        values (coordinate i) i < values (coordinate j) j) :
    False := by
  obtain ⟨a, T, _hTSub, hTStationary, hCoordinate⟩ :=
    exists_stationary_eqOn_const_of_small_codomain
      hcof hASmall coordinate (isClub_stationary hcof hD)
  let valueInRange : alpha -> Set.range (values a) := fun i =>
    ⟨values a i, Set.mem_range_self i⟩
  have hInjective : Set.InjOn valueInRange T := by
    intro i hi j hj hij
    have hiD : i ∈ D := _hTSub hi
    have hjD : j ∈ D := _hTSub hj
    apply le_antisymm
    · by_contra hijOrder
      have hjiLt : j < i := lt_of_not_ge hijOrder
      have hCoordEq : coordinate j = coordinate i := by
        rw [hCoordinate hj, hCoordinate hi]
      have hValueLt := hStrict hjD hiD hjiLt hCoordEq
      have hValueEq : values a i = values a j := congrArg Subtype.val hij
      rw [hCoordinate hj, hCoordinate hi, ← hValueEq] at hValueLt
      exact (lt_irrefl _ hValueLt)
    · by_contra hjiOrder
      have hijLt : i < j := lt_of_not_ge hjiOrder
      have hCoordEq : coordinate i = coordinate j := by
        rw [hCoordinate hi, hCoordinate hj]
      have hValueLt := hStrict hiD hjD hijLt hCoordEq
      have hValueEq : values a i = values a j := congrArg Subtype.val hij
      rw [hCoordinate hi, hCoordinate hj, hValueEq] at hValueLt
      exact (lt_irrefl _ hValueLt)
  exact not_injOn_of_isCofinal_of_lift_mk_lt_lift_cof
    (hValueSmall a) valueInRange (stationary_isCofinal hTStationary)
    hInjective

theorem exists_stationaryFiber_of_diagonalClubHypothesis
    {alpha : Type u}
    [LinearOrder alpha]
    (hDiag : DiagonalClubHypothesis (alpha := alpha))
    {S : Set alpha}
    {f : alpha -> alpha}
    (hS : Stationary S)
    (hreg : RegressiveOn S f) :
    exists beta, Stationary (StationaryFiber S f beta) := by
  classical
  by_contra hNoFiber
  have hAllNonstationary :
      forall beta, Nonstationary (StationaryFiber S f beta) := by
    intro beta
    exact (nonstationary_iff_not_stationary
      (StationaryFiber S f beta)).mpr (by
        intro hFiber
        exact hNoFiber (Exists.intro beta hFiber))
  choose C hC using hAllNonstationary
  have hDiagonalClub : IsClub (DiagonalInter C) :=
    hDiag C (fun beta => (hC beta).left)
  rcases hS (DiagonalInter C) hDiagonalClub with ⟨x, hxS, hxDiagonal⟩
  have hxFiber : x ∈ StationaryFiber S f (f x) :=
    mem_stationaryFiber_self hxS
  have hxClub : x ∈ C (f x) :=
    diagonalInter_mem hxDiagonal (hreg x hxS)
  exact (hC (f x)).right x hxClub hxFiber

theorem exists_stationary_subset_eqOn_const_of_small_initial_segments
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    (hSmall : SmallInitialSegments (alpha := alpha))
    {S : Set alpha}
    {f : alpha -> alpha}
    (hS : Stationary S)
    (hreg : RegressiveOn S f) :
    exists beta, exists T : Set alpha,
      And (T <= S) (And (Stationary T) (Set.EqOn f (fun _ => beta) T)) := by
  obtain ⟨beta, hFiber⟩ :=
    exists_stationaryFiber_of_diagonalClubHypothesis
      (diagonalClubHypothesis_of_diagonalCofinalHypothesis
        (diagonalCofinalHypothesis_of_small_initial_segments hcof hSmall))
      hS hreg
  exact ⟨beta, exists_stationary_subset_eqOn_const_of_stationaryFiber hFiber⟩

theorem stationary_inter_isClub
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    {S C : Set alpha}
    (hS : Stationary S)
    (hC : IsClub C) :
    Stationary (S.inter C) := by
  intro D hD
  have hClubInter : IsClub (C.inter D) :=
    IsClub.inter hcof hC hD
  rcases hS (C.inter D) hClubInter with ⟨x, hxS, hxCD⟩
  exact ⟨x, ⟨hxS, hxCD.left⟩, hxCD.right⟩

theorem stationary_diff_of_nonstationary
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    {S T : Set alpha}
    (hS : Stationary S)
    (hT : Not (Stationary T)) :
    Stationary (S \ T) := by
  rcases (not_stationary_iff_exists_club_avoids T).mp hT with
    ⟨C, hC, hAvoids⟩
  have hSC : Stationary (S.inter C) :=
    stationary_inter_isClub hcof hS hC
  refine stationary_mono (S := S.inter C) (T := S \ T) ?_ hSC
  intro x hx
  exact ⟨hx.left, hAvoids x hx.right⟩

theorem compl_stationary_of_nonstationary
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    [Nonempty alpha]
    (hcof : Not (Order.cof alpha = Cardinal.aleph0))
    {T : Set alpha}
    (hT : Not (Stationary T)) :
    Stationary (Tᶜ) := by
  have hdiff : Stationary ((Set.univ : Set alpha) \ T) :=
    stationary_diff_of_nonstationary hcof (univ_stationary hcof) hT
  simpa [Set.diff_eq] using hdiff

/-! A strengthened witness form of the standard stationary-cofinality
argument. Besides the point of cofinality `mu`, it retains the cofinal
suborder of the given club used to construct that point. -/
theorem exists_ordinalCof_eq_of_regular_lt_mem_club_with_cofinal_subset
    {mu c : Cardinal.{u}}
    (hMu : mu.IsRegular)
    (hC : c.IsRegular)
    (hMuC : mu < c)
    {D : Set (Set.Iio c.ord)}
    (hD : IsClub D) :
    exists delta : Set.Iio c.ord,
      delta.1.cof = mu /\
      delta ∈ D /\
      exists X : Set (Ordinal.{u}),
        X ⊆ (fun i : Set.Iio c.ord => i.1) '' D /\
        X ⊆ Set.Iio delta.1 /\
        Ordinal.type ((· < ·) : X -> X -> Prop) =
          (Cardinal.lift.{u + 1} mu).ord /\
        sSup X = delta.1 := by
  let inclusion : D -> Set.Iio c.ord := fun x => x.1
  have hInclusionStrict : StrictMono inclusion := by
    intro x y hxy
    exact hxy
  have hInclusionCofinal : IsCofinal (Set.range inclusion) := by
    simpa only [inclusion, Subtype.range_coe_subtype] using hD.isCofinal
  have hCofD : Order.cof D = Cardinal.lift.{u + 1} c := by
    rw [Order.cof_congr_of_strictMono hInclusionStrict hInclusionCofinal,
      Ordinal.cof_Iio, ← Ordinal.lift_cof, hC.cof_ord]
  let muLift : Cardinal.{u + 1} := Cardinal.lift.{u + 1} mu
  let I : Type (u + 1) := muLift.ord.ToType
  have hTypeI : Ordinal.type ((· < ·) : I -> I -> Prop) = muLift.ord := by
    simpa only [I] using Ordinal.type_toType muLift.ord
  have hMuOrdLeTypeD : muLift.ord <=
      Ordinal.type ((· < ·) : D -> D -> Prop) := by
    have hMuLiftC : muLift < Cardinal.lift.{u + 1} c := by
      exact Cardinal.lift_lt.mpr hMuC
    have hCofOrdLe : (Order.cof D).ord <=
        Ordinal.type ((· < ·) : D -> D -> Prop) := by
      rw [← Ordinal.cof_type]
      exact Ordinal.ord_cof_le _
    exact (Cardinal.ord_lt_ord.mpr (hCofD ▸ hMuLiftC)).le.trans hCofOrdLe
  have hTypeLe : Ordinal.type ((· < ·) : I -> I -> Prop) <=
      Ordinal.type ((· < ·) : D -> D -> Prop) := by
    rw [hTypeI]
    exact hMuOrdLeTypeD
  let e : InitialSeg ((· < ·) : I -> I -> Prop)
      ((· < ·) : D -> D -> Prop) :=
    Classical.choice (Ordinal.type_le_iff.mp hTypeLe)
  let f : I -> D := e
  let value : I -> Ordinal.{u} := fun i => (f i).1.1
  have hValueStrict : StrictMono value := by
    intro i j hij
    exact e.strictMono hij
  let X : Set (Ordinal.{u}) := Set.range value
  have hTypeX : Ordinal.type ((· < ·) : X -> X -> Prop) = muLift.ord := by
    have hIso : I ≃o X := hValueStrict.orderIso value
    rw [← hIso.toRelIsoLT.ordinal_type_eq, hTypeI]
  have hCardX : #X = muLift := by
    rw [← Ordinal.card_type ((· < ·) : X -> X -> Prop),
      hTypeX, Cardinal.card_ord]
  have hXBound : forall x, x ∈ X -> x < c.ord := by
    rintro x ⟨i, rfl⟩
    exact (f i).1.2
  have hSupLt : sSup X < c.ord := by
    apply Ordinal.sSup_lt_of_lt_cof
    · rw [hCardX, ← Ordinal.lift_cof, hC.cof_ord]
      exact Cardinal.lift_lt.mpr hMuC
    · exact hXBound
  let delta : Set.Iio c.ord := ⟨sSup X, hSupLt⟩
  have hMuLiftRegular : muLift.IsRegular := hMu.lift
  haveI : Nonempty I := by
    apply Ordinal.nonempty_toType_iff.mpr
    exact hMuLiftRegular.ord_pos.ne'
  letI : NoMaxOrder I := Cardinal.noMaxOrder hMuLiftRegular.aleph0_le
  have hXNonempty : X.Nonempty := Set.range_nonempty value
  have hXBdd : BddAbove X :=
    ⟨c.ord, fun x hx => (hXBound x hx).le⟩
  have hValueLtSup (i : I) : value i < sSup X := by
    obtain ⟨j, hij⟩ := exists_gt i
    exact (hValueStrict hij).trans_le
      (le_csSup hXBdd (Set.mem_range_self j))
  let g : I -> Set.Iio c.ord := fun i => (f i).1
  have hRangeGSubset : Set.range g ⊆ D := by
    rintro _ ⟨i, rfl⟩
    exact (f i).2
  have hGMono : Monotone g := by
    exact hValueStrict.monotone
  have hRangeGDirected : DirectedOn (· <= ·) (Set.range g) :=
    directedOn_range.mpr hGMono.directed_le
  have hRangeGLUB : IsLUB (Set.range g) delta := by
    constructor
    · rintro _ ⟨i, rfl⟩
      exact le_csSup hXBdd (Set.mem_range_self i)
    · intro b hb
      apply Subtype.coe_le_coe.mp
      change sSup X <= b.1
      apply csSup_le hXNonempty
      rintro x ⟨i, rfl⟩
      exact hb (Set.mem_range_self i)
  have hDeltaD : delta ∈ D :=
    hD.dirSupClosed hRangeGSubset (Set.range_nonempty g)
      hRangeGDirected hRangeGLUB
  let toDelta : I -> Set.Iio delta.1 :=
    fun i => ⟨value i, hValueLtSup i⟩
  have hToDeltaStrict : StrictMono toDelta := by
    intro i j hij
    exact hValueStrict hij
  have hToDeltaCofinal : IsCofinal (Set.range toDelta) := by
    intro beta
    obtain ⟨x, hxX, hBetaX⟩ :=
      (lt_csSup_iff hXBdd hXNonempty).mp beta.2
    obtain ⟨i, rfl⟩ := hxX
    exact ⟨toDelta i, Set.mem_range_self i, hBetaX.le⟩
  have hCofOrders : Order.cof I = Order.cof (Set.Iio delta.1) :=
    Order.cof_congr_of_strictMono hToDeltaStrict hToDeltaCofinal
  have hLiftDeltaCof : Cardinal.lift.{u + 1} delta.1.cof = muLift := by
    calc
      Cardinal.lift.{u + 1} delta.1.cof =
          (Ordinal.lift.{u + 1} delta.1).cof := Ordinal.lift_cof _
      _ = Order.cof (Set.Iio delta.1) := (Ordinal.cof_Iio _).symm
      _ = Order.cof I := hCofOrders.symm
      _ = muLift.ord.cof := by
        simpa only [I] using Ordinal.cof_toType muLift.ord
      _ = muLift := hMuLiftRegular.cof_ord
  have hDeltaCof : delta.1.cof = mu := by
    exact Cardinal.lift_inj.mp hLiftDeltaCof
  have hXSubsetD : X ⊆ (fun i : Set.Iio c.ord => i.1) '' D := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(f i).1, (f i).2, rfl⟩
  have hXSubsetDelta : X ⊆ Set.Iio delta.1 := by
    rintro _ ⟨i, rfl⟩
    exact hValueLtSup i
  exact ⟨delta, hDeltaCof, hDeltaD, X, hXSubsetD,
    hXSubsetDelta, hTypeX, rfl⟩

/-! The standard stationary cofinality strata below a regular cardinal.
For regular `mu < c`, every club in `c.ord` contains a point whose
cofinality is exactly `mu`. -/
theorem stationary_ordinalCof_eq_of_regular_lt
    {mu c : Cardinal.{u}}
    (hMu : mu.IsRegular)
    (hC : c.IsRegular)
    (hMuC : mu < c) :
    Stationary
      {delta : Set.Iio c.ord | delta.1.cof = mu} := by
  intro D hD
  obtain ⟨delta, hDeltaCof, hDeltaD, _X, _hXSubsetD,
    _hXSubsetDelta, _hTypeX, _hSupX⟩ :=
    exists_ordinalCof_eq_of_regular_lt_mem_club_with_cofinal_subset
      hMu hC hMuC hD
  exact ⟨delta, hDeltaCof, hDeltaD⟩

theorem stationary_ordinalCof_eq_alephOne_below_alephThree :
    Stationary
      {delta : Set.Iio (Cardinal.aleph (3 : Ordinal.{u})).ord |
        delta.1.cof = Cardinal.aleph 1} := by
  apply stationary_ordinalCof_eq_of_regular_lt
    Cardinal.isRegular_aleph_one
  · simpa only [Nat.cast_ofNat, OfNat.ofNat] using
      (Cardinal.isRegular_aleph_add_one (2 : Ordinal.{u}))
  · exact Cardinal.aleph_lt_aleph.mpr (by simp)

/-! Every proper initial segment of a well-ordered set of order type
`omega_1` is countable. -/
theorem countable_inter_Iio_of_orderType_omegaOne
    {X : Set (Ordinal.{u})}
    (hType : Ordinal.type ((· < ·) : X -> X -> Prop) =
      Ordinal.omega.{u + 1} 1)
    {gamma : Ordinal.{u}}
    (hGamma : gamma ∈ X) :
    (X ∩ Set.Iio gamma).Countable := by
  let gammaX : X := ⟨gamma, hGamma⟩
  let embedInitial : {x : Ordinal.{u} // x ∈ X ∩ Set.Iio gamma} ->
      Set.Iio gammaX :=
    fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  have hEmbedInitial : Function.Injective embedInitial := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z => z.1.1) hxy
  have hCardX : #X = Cardinal.aleph (1 : Ordinal.{u + 1}) := by
    rw [← Ordinal.card_type ((· < ·) : X -> X -> Prop), hType,
      Ordinal.card_omega]
  have hInitialOrder : Cardinal.ord #X =
      Ordinal.type ((· < ·) : X -> X -> Prop) := by
    rw [hCardX, hType, Cardinal.ord_aleph]
  rw [← Cardinal.le_aleph0_iff_set_countable,
    ← Cardinal.lt_aleph_one_iff]
  calc
    #({x : Ordinal.{u} // x ∈ X ∩ Set.Iio gamma}) <=
        #(Set.Iio gammaX) :=
      Cardinal.mk_le_of_injective hEmbedInitial
    _ < #X := Cardinal.mk_Iio_lt gammaX hInitialOrder
    _ = Cardinal.aleph (1 : Ordinal.{u + 1}) := hCardX

/-! In the recursion used for Jech's Lemma 24.14, a strictly increasing
`gamma`-sequence below a larger regular cardinal `lambda` has a supremum
still below `lambda`, and that supremum has cofinality exactly `gamma`.
Consequently the recursion does not need a separate continuity hypothesis
in order to obtain the required cofinality at its terminal stage. -/
theorem cardinalScaleLength_strictSequence_iSup_lt_and_cof_eq
    {gamma lambda : Cardinal.{u}}
    (hGamma : gamma.IsRegular)
    (hLambda : lambda.IsRegular)
    (hGammaLambda : gamma < lambda)
    (stage : gamma.ord.ToType -> Ordinal.{u})
    (hStageStrict : StrictMono stage)
    (hStageBound : forall i, stage i < lambda.ord) :
    (iSup stage < lambda.ord) /\ (iSup stage).cof = gamma := by
  constructor
  · apply Ordinal.iSup_lt_of_lt_cof
    · rw [Cardinal.mk_toType, Cardinal.card_ord, hLambda.cof_ord]
      exact hGammaLambda
    · exact hStageBound
  · letI : NoMaxOrder gamma.ord.ToType :=
      Cardinal.noMaxOrder hGamma.aleph0_le
    rw [Ordinal.cof_iSup hStageStrict, Ordinal.cof_toType,
      hGamma.cof_ord]

/-! The failure recursion can be chosen continuous as well as strictly
increasing.  At a limit index its value is the supremum of the requested
advances at all earlier indices; every such request already lies below a
still earlier stage cofinal in that limit.  This is the normal sequence
needed to intersect the recursion with the club supplied by rapidity. -/
theorem exists_normal_advance_sequence
    {gamma lambda : Cardinal.{u}}
    (hLambda : lambda.IsRegular)
    (hGammaLambda : gamma < lambda)
    (advance : Set.Iio lambda.ord -> Set.Iio lambda.ord)
    (hAdvance : forall alpha, alpha < advance alpha) :
    exists stage : gamma.ord.ToType -> Set.Iio lambda.ord,
      Order.IsNormal (fun i => (stage i).1) /\
        forall i j, i < j -> advance (stage i) < stage j := by
  classical
  let I := gamma.ord.ToType
  letI : LinearOrder I := by
    change LinearOrder gamma.ord.ToType
    infer_instance
  letI : WellFoundedLT I := by
    dsimp only [I]
    exact gamma.ord.out.wo.toIsWellFounded
  have hLimit : Order.IsSuccLimit lambda.ord :=
    Cardinal.isSuccLimit_ord hLambda.aleph0_le
  let candidate (alpha : I)
      (previous : forall beta, beta < alpha -> Set.Iio lambda.ord) :
      Ordinal.{u} :=
    iSup fun beta : I => if hbeta : beta < alpha then
      (advance (previous beta hbeta)).1 + 1 else 0
  have hCandidate : forall (alpha : I)
      (previous : forall beta, beta < alpha -> Set.Iio lambda.ord),
      candidate alpha previous < lambda.ord := by
    intro alpha previous
    dsimp only [candidate]
    apply Ordinal.iSup_lt_of_lt_cof
    · change Cardinal.mk gamma.ord.ToType < lambda.ord.cof
      rw [Cardinal.mk_toType, Cardinal.card_ord, hLambda.cof_ord]
      exact hGammaLambda
    · intro beta
      split_ifs with hbeta
      · exact hLimit.succ_lt (advance (previous beta hbeta)).2
      · exact hLambda.ord_pos
  let step (alpha : I)
      (previous : forall beta, beta < alpha -> Set.Iio lambda.ord) :
      Set.Iio lambda.ord :=
    ⟨candidate alpha previous, hCandidate alpha previous⟩
  have hStepAdvance : forall (alpha : I)
      (previous : forall beta, beta < alpha -> Set.Iio lambda.ord)
      (beta : I) (hbeta : beta < alpha),
      advance (previous beta hbeta) < step alpha previous := by
    intro alpha previous beta hbeta
    change (advance (previous beta hbeta)).1 < candidate alpha previous
    apply (lt_add_one _).trans_le
    dsimp only [candidate]
    have hLe := Ordinal.le_iSup
      (fun eta : I => if heta : eta < alpha then
        (advance (previous eta heta)).1 + 1 else 0) beta
    rw [dif_pos hbeta] at hLe
    simpa only using hLe
  let stage : I -> Set.Iio lambda.ord :=
    WellFounded.fix (inferInstance : WellFoundedLT I).wf
      (fun alpha previous => step alpha previous)
  have hStageEq : forall alpha,
      stage alpha = step alpha (fun beta hbeta => stage beta) := by
    intro alpha
    exact WellFounded.fix_eq _ _ alpha
  have hAdvanceStage : forall i j, i < j ->
      advance (stage i) < stage j := by
    intro i j hij
    rw [hStageEq j]
    exact hStepAdvance j (fun beta hbeta => stage beta) i hij
  have hStageStrict : StrictMono stage := by
    intro i j hij
    exact (hAdvance (stage i)).trans (hAdvanceStage i j hij)
  have hNormal : Order.IsNormal (fun i => (stage i).1) := by
    rw [Order.isNormal_iff]
    refine ⟨fun i j hij => hStageStrict hij, ?_⟩
    intro j hj a ha
    rw [hStageEq j]
    change candidate j (fun beta hbeta => stage beta) <= a
    dsimp only [candidate]
    apply Ordinal.iSup_le
    intro beta
    split_ifs with hbeta
    · obtain ⟨delta, hBetaDelta, hDeltaJ⟩ :=
        (not_covBy_iff hbeta).mp (hj.2 beta)
      have hAdvanceLe : (advance (stage beta)).1 + 1 <=
          (stage delta).1 :=
        Order.succ_le_iff.mpr (hAdvanceStage beta delta hBetaDelta)
      exact hAdvanceLe.trans (ha delta hDeltaJ)
    · exact bot_le
  exact ⟨stage, hNormal, hAdvanceStage⟩

/-! Terminal form of the normal recursion.  Its supremum `beta` remains
below `lambda`, has cofinality `gamma`, and the recursion becomes a normal
cofinal map into `beta`.  This packages exactly the data required to pull a
club in `beta` back to a club of recursion indices. -/
theorem exists_normal_cofinal_advance_sequence_below
    {gamma lambda : Cardinal.{u}}
    (hGamma : gamma.IsRegular)
    (hLambda : lambda.IsRegular)
    (hGammaLambda : gamma < lambda)
    (advance : Set.Iio lambda.ord -> Set.Iio lambda.ord)
    (hAdvance : forall alpha, alpha < advance alpha) :
    exists beta : Ordinal.{u}, exists hBetaLt : beta < lambda.ord,
      exists stage : gamma.ord.ToType -> Set.Iio beta,
        beta.cof = gamma /\ Order.IsNormal stage /\
          IsCofinal (Set.range stage) /\
          forall i j, i < j ->
            advance ⟨(stage i).1, (stage i).2.trans hBetaLt⟩ <
              ⟨(stage j).1, (stage j).2.trans hBetaLt⟩ := by
  classical
  obtain ⟨raw, hRawNormal, hAdvanceRaw⟩ :=
    exists_normal_advance_sequence hLambda hGammaLambda advance hAdvance
  let beta : Ordinal.{u} := iSup fun i => (raw i).1
  obtain ⟨hBetaLt, hBetaCof⟩ :=
    cardinalScaleLength_strictSequence_iSup_lt_and_cof_eq
      hGamma hLambda hGammaLambda (fun i => (raw i).1)
        hRawNormal.strictMono (fun i => (raw i).2)
  letI : NoMaxOrder gamma.ord.ToType :=
    Cardinal.noMaxOrder hGamma.aleph0_le
  have hRawLt : forall i, (raw i).1 < beta := by
    intro i
    obtain ⟨j, hij⟩ := exists_gt i
    exact (hRawNormal.strictMono hij).trans_le
      (Ordinal.le_iSup (fun k => (raw k).1) j)
  let stage : gamma.ord.ToType -> Set.Iio beta :=
    fun i => ⟨(raw i).1, hRawLt i⟩
  have hStageNormal : Order.IsNormal stage := by
    rw [Order.isNormal_iff]
    refine ⟨fun i j hij => hRawNormal.strictMono hij, ?_⟩
    intro i hi b hb
    change (raw i).1 <= b.1
    rw [hRawNormal.le_iff_forall_le hi]
    intro j hji
    exact hb j hji
  have hStageCofinal : IsCofinal (Set.range stage) := by
    intro b
    obtain ⟨i, hi⟩ := Ordinal.lt_iSup_iff.mp b.2
    exact ⟨stage i, Set.mem_range_self i, hi.le⟩
  refine ⟨beta, hBetaLt, stage, hBetaCof, hStageNormal,
    hStageCofinal, ?_⟩
  intro i j hij
  exact hAdvanceRaw i j hij

end PcfProject
