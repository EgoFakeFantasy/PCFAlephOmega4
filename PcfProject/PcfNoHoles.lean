import PcfProject.CanonicalProduct
import PcfProject.CofinalCore

/-!
# Cofinality profiles for the no-holes argument

The profile of a closed exact upper bound is constrained by the length of
the original increasing family. These are construction lemmas for Jech
24.19; the final PCF interpolation theorem is not assumed here.
-/

namespace PcfProject

universe u v w

theorem CardinalProductClosedExactUpperBound.lift_cardinal_le_of_cofinalBelow
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta) (hProper : J.IsProper)
    {d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hIncreasing : forall {alpha beta},
      (cardinalScaleLength theta).lt alpha beta ->
        (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta))
    (hExact : CardinalProductClosedExactUpperBound J d f)
    {iota : Type v}
    (e : iota -> ProductElement (cardinalProductFrame A J))
    (hBelow : forall i, CardinalProductEventuallyLtClosed J (e i) f)
    (hCofinal : forall h : ProductElement (cardinalProductFrame A J),
      CardinalProductEventuallyLtClosed J h f ->
        exists i, (cardinalProductFrame A J).eventuallyLe h (e i)) :
    Cardinal.lift.{v} theta <= Cardinal.lift.{u} (Cardinal.mk iota) := by
  classical
  by_contra hNot
  let stage : iota -> theta.ord.ToType := fun i =>
    Classical.choose (hExact.2 (e i) (hBelow i))
  have hStage : forall i,
      (cardinalProductFrame A J).eventuallyLe (e i) (d (stage i)) :=
    fun i => Classical.choose_spec (hExact.2 (e i) (hBelow i))
  have hRangeSmall : Cardinal.mk (Set.range stage) < theta := by
    apply Cardinal.lift_lt.mp
    exact Cardinal.mk_range_le_lift.trans_lt (lt_of_not_ge hNot)
  obtain ⟨beta, hBeta⟩ := exists_strict_upper_bound_of_mk_lt_regular
    hRegular hRangeSmall (fun i : Set.range stage => i.1)
  obtain ⟨i, hi⟩ := hCofinal (d beta) (hExact.1 beta)
  have hLt := (cardinalProductFrame A J).eventuallyLt_of_eventually_pointwiseStrict
    hProper (hIncreasing (hBeta ⟨stage i, i, rfl⟩))
  exact hLt.2 ((cardinalProductFrame A J).eventuallyLe_trans hi (hStage i))

#print axioms CardinalProductClosedExactUpperBound.lift_cardinal_le_of_cofinalBelow

/-! Coordinatewise cofinal sets below an exact bound give an actual product
family. The lower cardinal bound counts that family, including its larger
universe, and does not assume a cofinality-profile transport theorem. -/
theorem CardinalProductClosedExactUpperBound.lift_cardinal_le_coordinateSets
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta) (hProper : J.IsProper)
    {d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hIncreasing : forall {alpha beta},
      (cardinalScaleLength theta).lt alpha beta ->
        (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta))
    (hExact : CardinalProductClosedExactUpperBound J d f)
    (S : CardinalIndex A -> Set (Ordinal.{u}))
    (hNonempty : forall k, (S k).Nonempty)
    (hTop : forall k x, x ∈ S k -> x < k.1.ord)
    (hBelow : J.Eventually (fun k => forall x, x ∈ S k -> x < (f k).1))
    (hCofinal : J.Eventually (fun k => forall x, x < (f k).1 ->
      exists y, y ∈ S k /\ x <= y)) :
    Cardinal.lift.{u + 1} theta <= Cardinal.mk (forall k, S k) := by
  classical
  let e (a : forall k, S k) : ProductElement (cardinalProductFrame A J) :=
    fun k => Ordinal.ToType.mk ⟨(a k).1, hTop k _ (a k).2⟩
  have hValue (a : forall k, S k) (k : CardinalIndex A) :
      cardinalProductOrdinalValue (e a) k = (a k).1 := by
    simp only [e, cardinalProductOrdinalValue, OrderIso.symm_apply_apply]
  have heBelow : forall a, CardinalProductEventuallyLtClosed J (e a) f := by
    intro a
    exact J.eventually_mono hBelow (by
      intro k hk
      rw [hValue]
      exact hk _ (a k).2)
  have heCofinal : forall h : ProductElement (cardinalProductFrame A J),
      CardinalProductEventuallyLtClosed J h f ->
        exists a, (cardinalProductFrame A J).eventuallyLe h (e a) := by
    intro h hh
    choose fallback hFallback using hNonempty
    let a : forall k, S k := fun k =>
      if H : exists y, y ∈ S k /\ cardinalProductOrdinalValue h k <= y then
        ⟨Classical.choose H, (Classical.choose_spec H).1⟩
      else ⟨fallback k, hFallback k⟩
    refine ⟨a, J.eventually_mono (J.eventually_and hh hCofinal) ?_⟩
    intro k hk
    have H : exists y, y ∈ S k /\ cardinalProductOrdinalValue h k <= y :=
      hk.2 _ hk.1
    have hOrdinal : cardinalProductOrdinalValue h k <=
        cardinalProductOrdinalValue (e a) k := by
      rw [hValue]
      exact (by simpa only [a, dif_pos H] using (Classical.choose_spec H).2)
    exact (Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm.le_iff_le.mp
      hOrdinal
  have H := hExact.lift_cardinal_le_of_cofinalBelow hRegular hProper hIncreasing
    e heBelow heCofinal
  exact H.trans_eq (Cardinal.lift_id'.{u, u + 1} _)

#print axioms CardinalProductClosedExactUpperBound.lift_cardinal_le_coordinateSets

/-! The small-profile obstruction in Jech 24.19. If `kappa^|A|` is smaller
than the regular sequence length, the cofinality of its exact bound exceeds
`kappa` almost everywhere. Fundamental sequences construct the competing
family on the allegedly positive bad set; no rapidness assumption is used. -/
theorem CardinalProductClosedExactUpperBound.eventually_cof_gt_of_power_lt
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {theta kappa : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    (hKappa : Cardinal.aleph0 <= kappa)
    (hPower : (Cardinal.lift.{u + 1} kappa) ^
      Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} theta)
    {d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hIncreasing : forall {alpha beta},
      (cardinalScaleLength theta).lt alpha beta ->
        (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta))
    (hExact : CardinalProductClosedExactUpperBound J d f) :
    J.Eventually (fun k => kappa < (f k).1.cof) := by
  classical
  let B : CardinalIndex A -> Prop := fun k => (f k).1.cof <= kappa
  by_contra hNot
  have hBNotSmall : Not (J.Small B) := by
    simpa only [Ideal.Eventually, B, not_lt] using hNot
  have hProper : (J.localize B).IsProper :=
    (J.localize_isProper_iff B).mpr hBNotSmall
  let alpha0 : (cardinalScaleLength theta).Level :=
    Ordinal.ToType.mk ⟨0, hRegular.ord_pos⟩
  choose q hq using fun k : CardinalIndex A =>
    Ordinal.exists_isFundamentalSeq
      (o := (f k).1) (a := (f k).1.cof.ord) rfl
  let base (k : CardinalIndex A) : Set (Ordinal.{u}) :=
    Set.range (fun i : Set.Iio (f k).1.cof.ord => (q k i).1)
  let fallback (k : CardinalIndex A) := cardinalProductOrdinalValue (d alpha0) k
  let S (k : CardinalIndex A) : Set (Ordinal.{u}) :=
    if B k then Set.insert (fallback k) (base k) else {fallback k}
  have hSNonempty : forall k, (S k).Nonempty := by
    intro k
    refine ⟨fallback k, ?_⟩
    by_cases hk : B k
    · simp only [S, if_pos hk]
      exact Set.mem_insert _ _
    · simp only [S, if_neg hk, Set.mem_singleton_iff]
  have hSTop : forall k x, x ∈ S k -> x < k.1.ord := by
    intro k x hx
    by_cases hk : B k
    · simp only [S, if_pos hk] at hx
      rcases hx with rfl | ⟨i, rfl⟩
      · exact cardinalProductOrdinalValue_lt (d alpha0) k
      · exact (q k i).2.trans_le (f k).2
    · have hxEq : x = fallback k := by simpa only [S, if_neg hk, Set.mem_singleton_iff] using hx
      rw [hxEq]
      exact cardinalProductOrdinalValue_lt (d alpha0) k
  have hBSelf : (J.localize B).Eventually B := by
    change J.Small (fun k => Not (B k) /\ B k)
    exact J.subset_small J.empty_small (by simp)
  have hSBelow : (J.localize B).Eventually
      (fun k => forall x, x ∈ S k -> x < (f k).1) := by
    exact (J.localize B).eventually_mono
      ((J.localize B).eventually_and hBSelf
        (J.le_localize B _ (hExact.1 alpha0))) (by
      intro k hk x hx
      simp only [S, if_pos hk.1] at hx
      rcases hx with rfl | ⟨i, rfl⟩
      · exact hk.2
      · exact (q k i).2)
  have hSCofinal : (J.localize B).Eventually
      (fun k => forall x, x < (f k).1 -> exists y, y ∈ S k /\ x <= y) := by
    exact (J.localize B).eventually_mono hBSelf (by
      intro k hk x hx
      obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := (hq k).isCofinal_range ⟨x, hx⟩
      refine ⟨(q k i).1, ?_, hxy⟩
      simp only [S, if_pos hk]
      exact Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hKappaLift : Cardinal.aleph0.{u + 1} <= Cardinal.lift.{u + 1} kappa := by
    simpa only [Cardinal.lift_aleph0] using Cardinal.lift_le.{u + 1}.mpr hKappa
  have hSSize : forall k, Cardinal.mk (S k) <= Cardinal.lift.{u + 1} kappa := by
    intro k
    by_cases hk : B k
    · have hBase : Cardinal.mk (base k) <= Cardinal.lift.{u + 1} kappa := by
        calc
          Cardinal.mk (base k) <= Cardinal.mk (Set.Iio (f k).1.cof.ord) :=
            Cardinal.mk_range_le
          _ = Cardinal.lift.{u + 1} (f k).1.cof := by
            rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
          _ <= Cardinal.lift.{u + 1} kappa := Cardinal.lift_le.mpr hk
      rw [show S k = Set.insert (fallback k) (base k) by simp only [S, if_pos hk]]
      exact Cardinal.mk_insert_le.trans
        ((add_le_add hBase (Cardinal.one_le_aleph0.trans hKappaLift)).trans_eq
          (Cardinal.add_eq_self hKappaLift))
    · simp only [S, if_neg hk, Cardinal.mk_singleton]
      exact Cardinal.one_le_aleph0.trans hKappaLift
  have hProductSize : Cardinal.mk (forall k, S k) <=
      (Cardinal.lift.{u + 1} kappa) ^ Cardinal.mk (CardinalIndex A) := by
    calc
      Cardinal.mk (forall k, S k) = Cardinal.prod (fun k => Cardinal.mk (S k)) :=
        Cardinal.mk_pi _
      _ <= Cardinal.prod (fun _ : CardinalIndex A => Cardinal.lift.{u + 1} kappa) :=
        Cardinal.prod_le_prod _ _ hSSize
      _ = _ := by simp only [Cardinal.prod_const, Cardinal.lift_id]
  have hLocalIncreasing : forall {alpha beta},
      (cardinalScaleLength theta).lt alpha beta ->
        (cardinalProductFrame A (J.localize B)).eventuallyPointwiseLt
          (d alpha) (d beta) := by
    intro alpha beta hab
    exact (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
      (J.localize B) (J.le_localize B) (hIncreasing hab)
  have hLower := (hExact.localize alpha0 B).lift_cardinal_le_coordinateSets
    hRegular hProper hLocalIncreasing S hSNonempty hSTop hSBelow hSCofinal
  exact (hLower.trans hProductSize).not_gt hPower

#print axioms CardinalProductClosedExactUpperBound.eventually_cof_gt_of_power_lt

theorem CardinalProductClosedExactUpperBound.eventually_regular_cof_of_power_lt
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {theta kappa : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    (hKappa : Cardinal.aleph0 <= kappa)
    (hPower : (Cardinal.lift.{u + 1} kappa) ^
      Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} theta)
    {d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hIncreasing : forall {alpha beta},
      (cardinalScaleLength theta).lt alpha beta ->
        (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta))
    (hExact : CardinalProductClosedExactUpperBound J d f) :
    J.Eventually (fun k => Cardinal.IsRegular (f k).1.cof /\
      kappa < (f k).1.cof /\ (f k).1.cof <= k.1) := by
  apply J.eventually_mono
    (hExact.eventually_cof_gt_of_power_lt hRegular hKappa hPower hIncreasing)
  intro k hk
  refine ⟨Cardinal.isRegular_cof
      (Ordinal.one_lt_cof_iff.mp (Cardinal.one_lt_aleph0.trans_le (hKappa.trans hk.le))),
    hk, ?_⟩
  calc
    (f k).1.cof <= (f k).1.card := Ordinal.cof_le_card _
    _ <= k.1.ord.card := Ordinal.card_le_card (f k).2
    _ = k.1 := Cardinal.card_ord _

#print axioms CardinalProductClosedExactUpperBound.eventually_regular_cof_of_power_lt

/-! In the countable-coordinate application, the profile is above the
continuum because `(2^aleph0)^aleph0 = 2^aleph0`. This is the exact lower
cutoff used before transporting the profile in Jech 24.19--24.20. -/
theorem CardinalProductClosedExactUpperBound.eventually_cof_gt_continuum_of_countable
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    (hCountable : Cardinal.mk (CardinalIndex A) <= Cardinal.aleph0)
    (hContinuum : (2 : Cardinal.{u}) ^ Cardinal.aleph0 < theta)
    {d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hIncreasing : forall {alpha beta},
      (cardinalScaleLength theta).lt alpha beta ->
        (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta))
    (hExact : CardinalProductClosedExactUpperBound J d f) :
    J.Eventually (fun k => Cardinal.IsRegular (f k).1.cof /\
      (2 : Cardinal.{u}) ^ Cardinal.aleph0 < (f k).1.cof /\
      (f k).1.cof <= k.1) := by
  have hKappa : Cardinal.aleph0.{u} <= (2 : Cardinal.{u}) ^ Cardinal.aleph0 :=
    (Cardinal.cantor Cardinal.aleph0).le
  apply hExact.eventually_regular_cof_of_power_lt hRegular hKappa _ hIncreasing
  calc
    (Cardinal.lift.{u + 1} ((2 : Cardinal.{u}) ^ Cardinal.aleph0)) ^
        Cardinal.mk (CardinalIndex A) <=
      (Cardinal.lift.{u + 1} ((2 : Cardinal.{u}) ^ Cardinal.aleph0)) ^
        Cardinal.aleph0 := Cardinal.power_le_power_left
          (by
            rw [ne_eq, Cardinal.lift_eq_zero]
            exact (Cardinal.aleph0_pos.trans_le hKappa).ne') hCountable
    _ = Cardinal.lift.{u + 1} ((2 : Cardinal.{u}) ^ Cardinal.aleph0) := by
      simp only [Cardinal.lift_power, Cardinal.lift_ofNat, Cardinal.lift_aleph0,
        ← Cardinal.power_mul, Cardinal.aleph0_mul_aleph0]
    _ < Cardinal.lift.{u + 1} theta := Cardinal.lift_lt.mpr hContinuum

#print axioms CardinalProductClosedExactUpperBound.eventually_cof_gt_continuum_of_countable

/-! A profile map need not be injective. Regularity bounds all values in each
small fiber simultaneously, so pullback along the map is cofinal. This is the
fiber synchronization step, not an assumption of PCF interpolation. -/

theorem exists_strict_upper_bound_of_lift_mk_lt_regular
    {theta : Cardinal.{u}} (hRegular : Cardinal.IsRegular theta)
    {I : Type v}
    (hSmall : Cardinal.lift.{u} (Cardinal.mk I) < Cardinal.lift.{v} theta)
    (d : I -> theta.ord.ToType) :
    exists b, forall i, d i < b := by
  have hRange : Cardinal.mk (Set.range d) < theta := by
    apply Cardinal.lift_lt.mp
    exact Cardinal.mk_range_le_lift.trans_lt hSmall
  obtain ⟨b, hb⟩ := exists_strict_upper_bound_of_mk_lt_regular hRegular hRange
    (fun i : Set.range d => i.1)
  exact ⟨b, fun i => hb ⟨d i, i, rfl⟩⟩

#print axioms exists_strict_upper_bound_of_lift_mk_lt_regular

noncomputable abbrev cardinalReindexedProductFrame
    {A : CardSet.{u}} {I : Type v} (J : Ideal I)
    (p : I -> CardinalIndex A) : ReducedProductFrame.{v, u} where
  Index := I
  Coord i := (p i).1.ord.ToType
  le _ := (· <= ·)
  le_refl _ := le_refl
  le_trans _ := le_trans
  J := J

theorem cardinalReindexedProduct_exists_fiber_bound
    {A : CardSet.{u}} {I : Type v} (J : Ideal I)
    (p : I -> CardinalIndex A) (hRegulars : SetOfRegulars A)
    (hFibers : forall k : CardinalIndex A,
      Cardinal.lift.{u} (Cardinal.mk {i : I // p i = k}) <
        Cardinal.lift.{v} k.1)
    (d : ProductElement (cardinalReindexedProductFrame J p)) :
    exists b : ProductElement (cardinalProductFrame A (J.pushforward p)),
      forall i, d i < b (p i) := by
  classical
  have hBound : forall k : CardinalIndex A,
      exists b : k.1.ord.ToType, forall (i : I) (hi : p i = k),
        (hi ▸ d i) < b := by
    intro k
    let e : {i : I // p i = k} -> k.1.ord.ToType := fun i => i.2 ▸ d i.1
    obtain ⟨b, hb⟩ := exists_strict_upper_bound_of_lift_mk_lt_regular
      (hRegulars k.1 k.2) (hFibers k) e
    exact ⟨b, fun i hi => hb ⟨i, hi⟩⟩
  choose b hb using hBound
  exact ⟨b, fun i => hb (p i) i rfl⟩

#print axioms cardinalReindexedProduct_exists_fiber_bound

theorem cardinalReindexedProduct_isCofinalFamily_pullback_iff
    {A : CardSet.{u}} {I : Type v} (J : Ideal I)
    (p : I -> CardinalIndex A) (hRegulars : SetOfRegulars A)
    (hFibers : forall k : CardinalIndex A,
      Cardinal.lift.{u} (Cardinal.mk {i : I // p i = k}) <
        Cardinal.lift.{v} k.1)
    {K : Type w}
    (d : K -> ProductElement (cardinalProductFrame A (J.pushforward p))) :
    (cardinalReindexedProductFrame J p).IsCofinalFamily
      (fun a i => d a (p i)) <->
    (cardinalProductFrame A (J.pushforward p)).IsCofinalFamily d := by
  constructor
  · intro h g
    exact h (fun i => g (p i))
  · intro h g
    obtain ⟨b, hb⟩ := cardinalReindexedProduct_exists_fiber_bound J p hRegulars hFibers g
    obtain ⟨a, ha⟩ := h b
    refine ⟨a, J.eventually_mono ha ?_⟩
    intro i hi
    exact (hb i).le.trans hi

#print axioms cardinalReindexedProduct_isCofinalFamily_pullback_iff

theorem cardinalReindexedProduct_pointwiseStrictDirectedBelow_of_scale
    {A : CardSet.{u}} {I : Type v} (J : Ideal I)
    (p : I -> CardinalIndex A) (hRegulars : SetOfRegulars A)
    (hFibers : forall k : CardinalIndex A,
      Cardinal.lift.{u} (Cardinal.mk {i : I // p i = k}) <
        Cardinal.lift.{v} k.1)
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (s : PointwiseStrictScale (cardinalReindexedProductFrame J p)
      (cardinalScaleLength theta)) :
    (cardinalProductFrame A (J.pushforward p)).PointwiseStrictDirectedBelow theta := by
  classical
  intro K hK d
  choose stage hStage using fun a : K => s.cofinal (fun i => d a (p i))
  obtain ⟨beta, hBeta⟩ := exists_strict_upper_bound_of_mk_lt_regular hTheta hK stage
  obtain ⟨b, hb⟩ := cardinalReindexedProduct_exists_fiber_bound J p hRegulars
    hFibers (s.seq beta)
  refine ⟨b, ?_⟩
  intro a
  have hStrict := (cardinalReindexedProductFrame J p).eventuallyLe_eventuallyPointwiseLt_trans
    (hStage a) (s.increasing (hBeta a))
  exact J.eventually_mono hStrict (by
    intro i hi
    have hlt : (show (p i).1.ord.ToType from d a (p i)) < b (p i) :=
      hi.1.trans_lt (hb i)
    exact ⟨hlt.le, not_le_of_gt hlt⟩)

#print axioms cardinalReindexedProduct_pointwiseStrictDirectedBelow_of_scale

/-- A regular-length pointwise-strict scale on repeated coordinates gives a
scale of the same length on the pushforward ideal. The fiber bounds and the
recursive strictification are constructed, not supplied as hypotheses. -/
theorem cardinalReindexedProduct_pushforward_scale
    {A : CardSet.{u}} {I : Type v} (J : Ideal I)
    (p : I -> CardinalIndex A) (hRegulars : SetOfRegulars A)
    (hFibers : forall k : CardinalIndex A,
      Cardinal.lift.{u} (Cardinal.mk {i : I // p i = k}) <
        Cardinal.lift.{v} k.1)
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (s : PointwiseStrictScale (cardinalReindexedProductFrame J p)
      (cardinalScaleLength theta)) :
    Nonempty (PointwiseStrictScale (cardinalProductFrame A (J.pushforward p))
      (cardinalScaleLength theta)) := by
  classical
  choose d hd using fun a => cardinalReindexedProduct_exists_fiber_bound
    J p hRegulars hFibers (s.seq a)
  apply pointwiseStrictScale_of_directedBelow_of_cofinalFamily hTheta
    (cardinalReindexedProduct_pointwiseStrictDirectedBelow_of_scale
      J p hRegulars hFibers hTheta s) d
  intro g
  obtain ⟨a, ha⟩ := s.cofinal (fun i => g (p i))
  refine ⟨a, J.eventually_mono ha ?_⟩
  intro i hi
  exact hi.trans (hd a i).le

#print axioms cardinalReindexedProduct_pushforward_scale

theorem cardinalReindexedProduct_pushforward_hasTrueCofinality
    {A : CardSet.{u}} {I : Type v} (J : Ideal I)
    (hProper : J.IsProper)
    (p : I -> CardinalIndex A) (hRegulars : SetOfRegulars A)
    (hFibers : forall k : CardinalIndex A,
      Cardinal.lift.{u} (Cardinal.mk {i : I // p i = k}) <
        Cardinal.lift.{v} k.1)
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (s : PointwiseStrictScale (cardinalReindexedProductFrame J p)
      (cardinalScaleLength theta)) :
    HasTrueCofinality (cardinalProductFrame A (J.pushforward p))
      (cardinalScaleLength theta) := by
  obtain ⟨t⟩ := cardinalReindexedProduct_pushforward_scale J p hRegulars hFibers hTheta s
  exact cardinalScaleLength_hasTrueCofinality hTheta (t.toScale (hProper.pushforward p))

#print axioms cardinalReindexedProduct_pushforward_hasTrueCofinality

theorem cardinalReindexedProduct_mem_pcf_of_scale
    {A : CardSet.{u}} {I : Type v} (J : Ideal I)
    (hUltra : J.IsUltrafilterDual)
    (p : I -> CardinalIndex A) (hRegulars : SetOfRegulars A)
    (hFibers : forall k : CardinalIndex A,
      Cardinal.lift.{u} (Cardinal.mk {i : I // p i = k}) <
        Cardinal.lift.{v} k.1)
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (s : PointwiseStrictScale (cardinalReindexedProductFrame J p)
      (cardinalScaleLength theta)) :
    cardinalProductRepresentation.pcf A theta := by
  exact cardinalProductRepresentation_mem_pcf_iff.mpr
    ⟨hTheta, J.pushforward p, hUltra.pushforward p,
      cardinalReindexedProduct_pushforward_hasTrueCofinality J hUltra.isProper
        p hRegulars hFibers hTheta s⟩

#print axioms cardinalReindexedProduct_mem_pcf_of_scale

/-! A cofinal order representation below an exact bound carries a genuine
scale of the original regular length. Regularity bounds all stage choices
for each short family; exactness supplies cofinality and strictification
constructs the scale. The next theorem constructs the representation from
coordinate fundamental sequences. -/
theorem CardinalProductClosedExactUpperBound.scale_of_cofinal_orderMap
    {A B : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {K : Ideal (CardinalIndex B)} {theta : Cardinal.{u}}
    (hTheta : Cardinal.IsRegular theta)
    {d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hIncreasing : forall {alpha beta}, (cardinalScaleLength theta).lt alpha beta ->
      (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta))
    (hExact : CardinalProductClosedExactUpperBound J d f)
    (e : ProductElement (cardinalProductFrame B K) ->
      ProductElement (cardinalProductFrame A J))
    (hBelow : forall x, CardinalProductEventuallyLtClosed J (e x) f)
    (hCofinal : forall x, CardinalProductEventuallyLtClosed J x f ->
      exists y, (cardinalProductFrame A J).eventuallyLe x (e y))
    (hReflectLe : forall x y, (cardinalProductFrame A J).eventuallyLe (e x) (e y) ->
      (cardinalProductFrame B K).eventuallyLe x y)
    (hReflectLt : forall x y, (cardinalProductFrame A J).eventuallyPointwiseLt (e x) (e y) ->
      (cardinalProductFrame B K).eventuallyPointwiseLt x y) :
    Nonempty (PointwiseStrictScale (cardinalProductFrame B K)
      (cardinalScaleLength theta)) := by
  classical
  choose c hc using fun alpha => hCofinal (d alpha) (hExact.1 alpha)
  have hDirected : (cardinalProductFrame B K).PointwiseStrictDirectedBelow theta := by
    intro T hT x
    choose stage hStage using fun i : T => hExact.2 (e (x i)) (hBelow (x i))
    obtain ⟨beta, hBeta⟩ := exists_strict_upper_bound_of_mk_lt_regular hTheta hT stage
    refine ⟨c beta, ?_⟩
    intro i
    apply hReflectLt
    have hStrict := (cardinalProductFrame A J).eventuallyLe_eventuallyPointwiseLt_trans
      (hStage i) (hIncreasing (hBeta i))
    exact J.eventually_mono (J.eventually_and hStrict (hc beta)) (by
      intro k hk
      exact ⟨le_trans hk.1.1 hk.2, fun hReverse =>
        hk.1.2 (le_trans hk.2 hReverse)⟩)
  apply pointwiseStrictScale_of_directedBelow_of_cofinalFamily hTheta hDirected c
  intro x
  obtain ⟨alpha, hAlpha⟩ := hExact.2 (e x) (hBelow x)
  exact ⟨alpha, hReflectLe x (c alpha)
    ((cardinalProductFrame A J).eventuallyLe_trans hAlpha (hc alpha))⟩

#print axioms CardinalProductClosedExactUpperBound.scale_of_cofinal_orderMap

theorem CardinalProductClosedExactUpperBound.scale_of_eventually_cof_profile
    {A B : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    {d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hIncreasing : forall {alpha beta}, (cardinalScaleLength theta).lt alpha beta ->
      (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta))
    (hExact : CardinalProductClosedExactUpperBound J d f)
    (p : CardinalIndex A -> CardinalIndex B) (hRegulars : SetOfRegulars B)
    (hProfile : J.Eventually (fun k => (p k).1 = (f k).1.cof))
    (hFibers : forall b : CardinalIndex B,
      Cardinal.mk {k : CardinalIndex A // p k = b} < Cardinal.lift.{u + 1} b.1) :
    Nonempty (PointwiseStrictScale (cardinalProductFrame B (J.pushforward p))
      (cardinalScaleLength theta)) := by
  classical
  let G : CardinalIndex A -> Prop := fun k => (p k).1 = (f k).1.cof
  have hSeq : forall k : CardinalIndex A, G k ->
      exists q : (p k).1.ord.ToType -> Set.Iio (f k).1,
        StrictMono q /\ IsCofinal (Set.range q) := by
    intro k hk
    obtain ⟨q, hq⟩ := Ordinal.exists_isFundamentalSeq (congrArg Cardinal.ord hk.symm)
    refine ⟨fun i => q ((Ordinal.ToType.mk).symm i),
      hq.strictMono.comp (Ordinal.ToType.mk).symm.strictMono, ?_⟩
    intro x
    obtain ⟨y, ⟨i, rfl⟩, hi⟩ := hq.isCofinal_range x
    exact ⟨q i, ⟨Ordinal.ToType.mk i, by simp⟩, hi⟩
  choose q hqMono hqCofinal using hSeq
  let alpha0 : (cardinalScaleLength theta).Level :=
    Ordinal.ToType.mk ⟨0, hTheta.ord_pos⟩
  let e (x : ProductElement (cardinalProductFrame B (J.pushforward p))) :
      ProductElement (cardinalProductFrame A J) := fun k =>
    if hk : G k then
      Ordinal.ToType.mk ⟨(q k hk (x (p k))).1, by
        have hLt : (q k hk (x (p k))).1 < (f k).1 := (q k hk (x (p k))).2
        exact hLt.trans_le (f k).2⟩
    else d alpha0 k
  have hValue (x : ProductElement (cardinalProductFrame B (J.pushforward p)))
      (k : CardinalIndex A) (hk : G k) :
      cardinalProductOrdinalValue (e x) k = (q k hk (x (p k))).1 := by
    simp only [e, dif_pos hk, cardinalProductOrdinalValue, OrderIso.symm_apply_apply]
  have hBelow : forall x, CardinalProductEventuallyLtClosed J (e x) f := by
    intro x
    exact J.eventually_mono hProfile (by
      intro k hk
      rw [hValue x k hk]
      exact (q k hk (x (p k))).2)
  have hCofinal : forall x : ProductElement (cardinalProductFrame A J),
      CardinalProductEventuallyLtClosed J x f ->
        exists y, (cardinalProductFrame A J).eventuallyLe x (e y) := by
    intro x hx
    have hRound : forall (k : CardinalIndex A) (hk : G k),
        cardinalProductOrdinalValue x k < (f k).1 ->
          exists i : (p k).1.ord.ToType,
            cardinalProductOrdinalValue x k <= (q k hk i).1 := by
      intro k hk hxk
      obtain ⟨y, ⟨i, rfl⟩, hi⟩ := hqCofinal k hk ⟨cardinalProductOrdinalValue x k, hxk⟩
      exact ⟨i, hi⟩
    let r : ProductElement (cardinalReindexedProductFrame J p) := fun k =>
      if H : G k /\ cardinalProductOrdinalValue x k < (f k).1 then
        Classical.choose (hRound k H.1 H.2)
      else Ordinal.ToType.mk ⟨0, (hRegulars (p k).1 (p k).2).ord_pos⟩
    have hFibersLift : forall b : CardinalIndex B,
        Cardinal.lift.{u} (Cardinal.mk {k : CardinalIndex A // p k = b}) <
          Cardinal.lift.{u + 1} b.1 := by
      intro b
      exact (Cardinal.lift_id'.{u, u + 1} _).trans_lt (hFibers b)
    obtain ⟨b, hb⟩ := cardinalReindexedProduct_exists_fiber_bound J p hRegulars hFibersLift r
    refine ⟨b, J.eventually_mono (J.eventually_and hProfile hx) ?_⟩
    intro k hk
    have hk' : G k /\ cardinalProductOrdinalValue x k < (f k).1 := hk
    have hxr : cardinalProductOrdinalValue x k <= (q k hk.1 (r k)).1 := by
      simpa only [r, dif_pos hk'] using (Classical.choose_spec (hRound k hk.1 hk.2))
    have hxb : cardinalProductOrdinalValue x k <= cardinalProductOrdinalValue (e b) k := by
      rw [hValue b k hk.1]
      exact hxr.trans ((hqMono k hk.1).monotone (hb k).le)
    exact (Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm.le_iff_le.mp hxb
  apply hExact.scale_of_cofinal_orderMap hTheta hIncreasing e hBelow hCofinal
  · intro x y hxy
    exact J.eventually_mono (J.eventually_and hProfile hxy) (by
      intro k hk
      have hOrd : cardinalProductOrdinalValue (e x) k <=
          cardinalProductOrdinalValue (e y) k :=
        (Ordinal.ToType.mk : Set.Iio k.1.ord ≃o k.1.ord.ToType).symm.le_iff_le.mpr hk.2
      rw [hValue x k hk.1, hValue y k hk.1] at hOrd
      exact (hqMono k hk.1).le_iff_le.mp hOrd)
  · intro x y hxy
    have hOrd := (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue (e x) (e y)).mp hxy
    exact J.eventually_mono (J.eventually_and hProfile hOrd) (by
      intro k hk
      rcases hk with ⟨hg, hxyk⟩
      rw [hValue x k hg, hValue y k hg] at hxyk
      have hLt := (hqMono k hg).lt_iff_lt.mp hxyk
      exact ⟨hLt.le, not_le_of_gt hLt⟩)

#print axioms CardinalProductClosedExactUpperBound.scale_of_eventually_cof_profile

theorem CardinalProductClosedExactUpperBound.mem_pcf_of_eventually_cof_mem
    {A B : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual)
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    {d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J)}
    {f : CardinalProductClosedElement A}
    (hIncreasing : forall {alpha beta}, (cardinalScaleLength theta).lt alpha beta ->
      (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta))
    (hExact : CardinalProductClosedExactUpperBound J d f)
    (hRegulars : SetOfRegulars B)
    (hSize : forall b, B b -> Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} b)
    (hMem : J.Eventually (fun k => B (f k).1.cof)) :
    cardinalProductRepresentation.pcf B theta := by
  classical
  have hNonempty : exists k : CardinalIndex A, B (f k).1.cof := by
    by_contra hNot
    exact hUltra.isProper.not_eventually_of_forall_not
      (fun k hk => hNot ⟨k, hk⟩) hMem
  obtain ⟨k0, hk0⟩ := hNonempty
  let p : CardinalIndex A -> CardinalIndex B := fun k =>
    if hk : B (f k).1.cof then ⟨(f k).1.cof, hk⟩ else ⟨(f k0).1.cof, hk0⟩
  have hProfile : J.Eventually (fun k => (p k).1 = (f k).1.cof) :=
    J.eventually_mono hMem (by intro k hk; simp only [p, dif_pos hk])
  have hFibers : forall b : CardinalIndex B,
      Cardinal.mk {k : CardinalIndex A // p k = b} < Cardinal.lift.{u + 1} b.1 := by
    intro b
    exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt (hSize b.1 b.2)
  obtain ⟨s⟩ := hExact.scale_of_eventually_cof_profile hTheta hIncreasing p
    hRegulars hProfile hFibers
  exact cardinalProductRepresentation_mem_pcf_of_scale
    (J.pushforward p) (hUltra.pushforward p) hTheta
    (s.toScale (hUltra.isProper.pushforward p))

#print axioms CardinalProductClosedExactUpperBound.mem_pcf_of_eventually_cof_mem

theorem cardinalProductFrame_eventuallyPointwiseLt_of_ultrafilter_eventuallyLt
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    (hUltra : J.IsUltrafilterDual)
    {x y : ProductElement (cardinalProductFrame A J)}
    (hxy : (cardinalProductFrame A J).eventuallyLt x y) :
    (cardinalProductFrame A J).eventuallyPointwiseLt x y := by
  have hSmall : J.Small (fun k => (cardinalProductFrame A J).le k (y k) (x k)) :=
    (hUltra.small_iff_not_eventually _).mpr hxy.2
  have hNot : J.Eventually (fun k =>
      Not ((cardinalProductFrame A J).le k (y k) (x k))) := by
    simpa only [Ideal.Eventually, not_not] using hSmall
  exact J.eventually_and hxy.1 hNot

#print axioms cardinalProductFrame_eventuallyPointwiseLt_of_ultrafilter_eventuallyLt

/-- Countable no-holes above the continuum for a regular set closed under
regular profiles below its coordinates. Both the exact bound and the new
PCF witness are constructed from the original PCF scale. -/
theorem cardinalProductRepresentation_mem_pcf_of_countable_profile_closed
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hCountable : CountableCardSet A)
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hUncountable : forall a, A a -> Cardinal.aleph0 < a)
    (hClosed : forall a, A a -> forall rho, Cardinal.IsRegular rho ->
      (2 : Cardinal.{u}) ^ Cardinal.aleph0 < rho -> rho <= a -> A rho)
    {theta mu : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (hContinuum : (2 : Cardinal.{u}) ^ Cardinal.aleph0 < theta)
    (hThetaMu : theta <= mu)
    (hMu : cardinalProductRepresentation.pcf A mu) :
    cardinalProductRepresentation.pcf A theta := by
  classical
  obtain ⟨_hMuRegular, J, hUltra, hTcf⟩ := cardinalProductRepresentation_mem_pcf_iff.mp hMu
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  let embed : theta.ord.ToType -> mu.ord.ToType := fun alpha =>
    Ordinal.ToType.mk ⟨((Ordinal.ToType.mk).symm alpha).1, by
      have hLt : ((Ordinal.ToType.mk).symm alpha).1 < theta.ord :=
        ((Ordinal.ToType.mk).symm alpha).2
      exact hLt.trans_le (Cardinal.ord_le_ord.mpr hThetaMu)⟩
  have hEmbed : StrictMono embed := by
    intro alpha beta hab
    apply (Ordinal.ToType.mk).strictMono
    exact (Ordinal.ToType.mk).symm.strictMono hab
  let d : (cardinalScaleLength theta).Level ->
      ProductElement (cardinalProductFrame A J) := fun alpha => s.seq (embed alpha)
  have hIncreasing : forall {alpha beta}, (cardinalScaleLength theta).lt alpha beta ->
      (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha) (d beta) := by
    intro alpha beta hab
    exact cardinalProductFrame_eventuallyPointwiseLt_of_ultrafilter_eventuallyLt hUltra
      (s.increasing (hEmbed hab))
  have hThetaUncountable : Cardinal.aleph0 < theta :=
    (Cardinal.cantor Cardinal.aleph0).trans hContinuum
  have hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
      Cardinal.lift.{u + 1} theta := by
    calc
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <=
          (2 : Cardinal.{u + 1}) ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left (by simp) hCountable
      _ < Cardinal.lift.{u + 1} theta := by
        have hLift : Cardinal.lift.{u + 1} ((2 : Cardinal.{u}) ^ Cardinal.aleph0) <
            Cardinal.lift.{u + 1} theta := Cardinal.lift_lt.mpr hContinuum
        simpa only [Cardinal.lift_power, Cardinal.lift_ofNat, Cardinal.lift_aleph0]
          using hLift
  have hPrinciple : CardinalProductClosedExactUpperBoundPrinciple A J theta := by
    simpa only [Ideal.pushforward_id] using
      pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
        (J := J) id hInfinite hTheta hThetaUncountable hPower
  obtain ⟨f, hf⟩ := hPrinciple d hIncreasing
  apply hf.mem_pcf_of_eventually_cof_mem hUltra hTheta hIncreasing hRegulars
  · intro a ha
    have hLift : Cardinal.lift.{u + 1} Cardinal.aleph0.{u} < Cardinal.lift.{u + 1} a :=
      Cardinal.lift_lt.mpr (hUncountable a ha)
    exact hCountable.trans_lt (by
      simpa only [Cardinal.lift_aleph0] using hLift)
  · exact J.eventually_mono
      (hf.eventually_cof_gt_continuum_of_countable hTheta hCountable hContinuum hIncreasing)
      (fun k hk => hClosed k.1 k.2 _ hk.1 hk.2.1 hk.2.2)

#print axioms cardinalProductRepresentation_mem_pcf_of_countable_profile_closed

theorem alephSuccSet_mem_pcf_of_regular_above_continuum_le_pcf
    {theta mu : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (hContinuum : (2 : Cardinal.{u}) ^ Cardinal.aleph0 < theta)
    (hThetaMu : theta <= mu)
    (hMu : cardinalProductRepresentation.pcf alephSuccSet mu) :
    cardinalProductRepresentation.pcf alephSuccSet theta := by
  letI : Infinite (CardinalIndex alephSuccSet.{u}) :=
    infinite_cardinalIndex_of_cofinalInAlephOmega alephSuccSet_cofinalInAlephOmega
  apply cardinalProductRepresentation_mem_pcf_of_countable_profile_closed
    alephSuccSet_regulars alephSuccSet_countable (Cardinal.aleph0_le_mk _)
    alephSuccSet_aleph0_lt _ hTheta hContinuum hThetaMu hMu
  intro a ha rho _hRho hContinuumRho hRhoA
  exact alephSuccSet_of_aleph0_lt_of_lt_targetAlephOmega
    ((Cardinal.cantor Cardinal.aleph0).trans hContinuumRho)
    (hRhoA.trans_lt (alephSuccSet_belowAlephOmega a ha))

#print axioms alephSuccSet_mem_pcf_of_regular_above_continuum_le_pcf

end PcfProject
