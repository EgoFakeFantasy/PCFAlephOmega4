import PcfProject.CanonicalPcf
import PcfProject.StationaryIdeal
import PcfProject.ShelahClosure

/-!
# Generator construction under a powerset gap

The cardinal induction and semantic generator construction of Jech 24.25
are proved under the displayed small-index, infinite-index and powerset-gap
hypotheses. Transitivity and the final target applications remain separate.
-/

namespace PcfProject

universe u

theorem pointwiseStrictDirectedBelow_succ_of_isSingular
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {theta : Cardinal.{u}} (hSingular : Cardinal.IsSingular theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta) := by
  classical
  apply pointwiseStrictDirectedBelow_succ_of_directedAt
    (Cardinal.aleph0_pos.trans_le hSingular.aleph0_le) hDirected
  intro d
  let L := theta.ord.ToType
  letI : Nonempty L := ⟨Ordinal.ToType.mk ⟨0,
    Cardinal.ord_pos.mpr (Cardinal.aleph0_pos.trans_le hSingular.aleph0_le)⟩⟩
  letI : NoMaxOrder L := Cardinal.noMaxOrder hSingular.aleph0_le
  obtain ⟨S, hSCofinal, hSCard⟩ := Order.exists_cof_eq L
  have hSSmall : Cardinal.mk S < theta := by
    rw [hSCard]
    exact (Ordinal.cof_toType theta.ord).trans_lt hSingular.cof_ord_lt
  have hSmall : forall beta : L, Cardinal.mk {alpha : L // alpha < beta} < theta := by
    intro beta
    have hOrderType : (Cardinal.mk L).ord = Ordinal.type (fun x y : L => x < y) := by
      rw [show Cardinal.mk L = theta from Cardinal.mk_ord_toType theta]
      exact (Ordinal.type_toType theta.ord).symm
    exact (Cardinal.mk_Iio_lt beta hOrderType).trans_eq (Cardinal.mk_ord_toType theta)
  have hBounds : forall beta : S, exists g : ProductElement (cardinalProductFrame A J),
      forall alpha : {alpha : L // alpha < beta.1},
        (cardinalProductFrame A J).eventuallyPointwiseLt (d alpha.1) g := by
    intro beta
    exact hDirected _ (hSmall beta.1) (fun alpha => d alpha.1)
  choose g hg using hBounds
  obtain ⟨b, hb⟩ := hDirected S hSSmall g
  refine ⟨b, ?_⟩
  intro alpha
  obtain ⟨beta, hAlphaBeta⟩ := exists_gt (show L from alpha)
  obtain ⟨gamma, hGamma, hBetaGamma⟩ := hSCofinal beta
  exact (cardinalProductFrame A J).eventuallyPointwiseLt_trans
    (hg ⟨gamma, hGamma⟩ ⟨alpha, hAlphaBeta.trans_le hBetaGamma⟩) (hb ⟨gamma, hGamma⟩)

/-- A scale modulo an arbitrary proper ideal yields PCF membership after
extending that ideal to an ultrafilter dual. Pointwise strictness ensures
that the scale survives the extension. -/
theorem cardinalProductRepresentation_mem_pcf_of_proper_pointwiseStrictScale
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper) {theta : Cardinal.{u}}
    (hTheta : Cardinal.IsRegular theta)
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta)) :
    cardinalProductRepresentation.pcf A theta := by
  obtain ⟨K, hUltra, hLe⟩ := exists_ultrafilterDual_ideal_extending J hProper
  apply cardinalProductRepresentation_mem_pcf_of_scale K hUltra hTheta
  exact (s.withLargerIdeal K hLe).toScale hUltra.isProper

/-- The regular non-PCF step of Jech 24.25(ii). A failure to upgrade
directedness would produce a positive localized scale, hence a forbidden
PCF witness. The exact-bound principle is explicit in this reusable form. -/
theorem pointwiseStrictDirectedBelow_succ_of_regular_not_mem_pcf
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    (hProper : J.IsProper) {theta : Cardinal.{u}}
    (hTheta : Cardinal.IsRegular theta)
    (hNotPcf : Not (cardinalProductRepresentation.pcf A theta))
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta)
    (hExact : CardinalProductClosedExactUpperBoundPrinciple A J theta) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta) := by
  apply pointwiseStrictDirectedBelow_succ_of_directedAt hTheta.pos hDirected
  apply pointwiseStrictDirectedAt_of_no_scale hTheta hDirected hExact
  · rintro ⟨s⟩
    exact hNotPcf (cardinalProductRepresentation_mem_pcf_of_proper_pointwiseStrictScale
      hProper hTheta s)
  · intro X hX
    rintro ⟨s⟩
    exact hNotPcf (cardinalProductRepresentation_mem_pcf_of_proper_pointwiseStrictScale
      hX hTheta s)

theorem pointwiseStrictDirectedBelow_succ_of_not_mem_pcf_of_two_power_lt
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} (hProper : J.IsProper)
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    {theta : Cardinal.{u}} (hUncountable : Cardinal.aleph0 < theta)
    (hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
      Cardinal.lift.{u + 1} theta)
    (hNotPcf : Not (cardinalProductRepresentation.pcf A theta))
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta) := by
  by_cases hRegular : Cardinal.IsRegular theta
  · apply pointwiseStrictDirectedBelow_succ_of_regular_not_mem_pcf
      hProper hRegular hNotPcf hDirected
    simpa only [Ideal.pushforward_id] using
      pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
        (J := J) id hInfinite hRegular hUncountable hPower
  · have hSingular : Cardinal.IsSingular theta := by
      exact ⟨hUncountable.le, fun hEq =>
        hRegular ⟨hUncountable.le, hEq.symm.le⟩⟩
    exact pointwiseStrictDirectedBelow_succ_of_isSingular hSingular hDirected

/-- The strict canonical filtration is contained in every witnessing
ultrafilter whose true cofinality is at least the threshold. This statement
does not require generators to have already been constructed. -/
theorem canonicalBelowIdeal_le_pushforward_of_trueCofinality
    {A W : CardSet.{u}} (hRegulars : SetOfRegulars A) (hWA : SubsetOf W A)
    {J : Ideal (CardinalIndex W)} (hUltra : J.IsUltrafilterDual)
    {kappa theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (hKappaTheta : kappa <= theta)
    (hTcf : HasTrueCofinality (cardinalProductFrame W J) (cardinalScaleLength theta)) :
    Ideal.Le (canonicalBelowIdeal A hRegulars kappa) (J.pushforward fun i => i.1) := by
  intro B hBelow
  change J.Small (fun i => B i.1)
  cases hUltra.small_or_compl_small (fun i => B i.1) with
  | inl hSmall => exact hSmall
  | inr hEventually =>
    have hRegularsW : SetOfRegulars W := setOfRegulars_of_subset hWA hRegulars
    have hInter : J.Eventually (fun i => interCardSet W B i.1) :=
      J.eventually_mono hEventually (fun i hi => ⟨i.2, hi⟩)
    have hPcfW : cardinalProductRepresentation.pcf (interCardSet W B) theta :=
      cardinalProductRepresentation_mem_pcf_of_eventually_mem
        (A := interCardSet W B) (B := W) (fun _ h => h.1)
        hRegularsW hTheta J hUltra hTcf hInter
    have hPcfA : cardinalProductRepresentation.pcf (interCardSet A B) theta :=
      cardinalProductRepresentation_pcf_mono
        (fun gamma h => ⟨hWA gamma h.1, h.2⟩)
        (fun gamma h => hRegulars gamma h.1) theta hPcfW
    exact False.elim ((hBelow theta hPcfA).not_ge hKappaTheta)

theorem canonicalBelowIndexIdeal_le_of_trueCofinality
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    {J : Ideal (CardinalIndex A)} (hUltra : J.IsUltrafilterDual)
    {kappa theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (hKappaTheta : kappa <= theta)
    (hTcf : HasTrueCofinality (cardinalProductFrame A J) (cardinalScaleLength theta)) :
    Ideal.Le ((canonicalBelowIdeal A hRegulars kappa).restrictAlong
      (fun i : CardinalIndex A => i.1)) J := by
  have hLe := canonicalBelowIdeal_le_pushforward_of_trueCofinality
    hRegulars (fun _ h => h) hUltra hTheta hKappaTheta hTcf
  intro S hS
  have hImage := hLe _ hS
  exact J.subset_small hImage (fun i hi => ⟨i, rfl, hi⟩)

theorem canonicalBelowIndexIdeal_not_succ_directed_of_mem_pcf
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A) {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta) :
    Not ((cardinalProductFrame A ((canonicalBelowIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow (Order.succ theta)) := by
  intro hDirected
  obtain ⟨hTheta, J, hUltra, hTcf⟩ := cardinalProductRepresentation_mem_pcf_iff.mp hPcf
  have hLe := canonicalBelowIndexIdeal_le_of_trueCofinality hRegulars hUltra hTheta le_rfl hTcf
  have hDirectedJ : (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta) :=
    hDirected.withLargerIdeal J hLe
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  obtain ⟨g, hg⟩ := hDirectedJ (cardinalScaleLength theta).Level
    (by simpa only [mk_cardinalScaleLength_level] using Order.lt_succ theta) s.seq
  obtain ⟨alpha, hAlpha⟩ := s.cofinal g
  exact ((cardinalProductFrame A J).eventuallyLt_of_eventually_pointwiseStrict
    hUltra.isProper (hg alpha)).2 hAlpha

theorem isMaxPcf_of_canonicalBelowIndexIdeal_scale
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A) {theta : Cardinal.{u}}
    (hPcf : cardinalProductRepresentation.pcf A theta)
    (s : PointwiseStrictScale (cardinalProductFrame A
      ((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1))) (cardinalScaleLength theta)) :
    IsMaxPcf cardinalProductRepresentation A theta := by
  refine ⟨hPcf, ?_⟩
  intro mu hMu
  by_cases hLess : mu < theta
  · exact hLess.le
  obtain ⟨hMuRegular, J, hUltra, hTcf⟩ := cardinalProductRepresentation_mem_pcf_iff.mp hMu
  have hLe := canonicalBelowIndexIdeal_le_of_trueCofinality
    hRegulars hUltra hMuRegular (le_of_not_gt hLess) hTcf
  have hTheta := (cardinalProductRepresentation_mem_pcf_iff.mp hPcf).1
  have hTcfTheta : HasTrueCofinality (cardinalProductFrame A J) (cardinalScaleLength theta) :=
    cardinalScaleLength_hasTrueCofinality hTheta ((s.withLargerIdeal J hLe).toScale hUltra.isProper)
  have hEq : mu = theta := by
    simpa only [mk_cardinalScaleLength_level] using
      cardinal_mk_level_eq_of_hasTrueCofinality hTcf hTcfTheta
  exact hEq.le

/-- The nonmaximal PCF stage of the generator recursion. Assuming only the
previous-stage directedness invariant, it constructs a positive scale set
whose adjunction leaves a proper successor-directed ideal. -/
theorem exists_generator_step_of_canonicalBelow_directed_of_nonmax
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    {theta : Cardinal.{u}}
    (hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
      Cardinal.lift.{u + 1} theta)
    (hPcf : cardinalProductRepresentation.pcf A theta)
    (hNonmax : exists mu, cardinalProductRepresentation.pcf A mu /\ theta < mu)
    (hDirected : (cardinalProductFrame A
      ((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow theta) :
    let J := (canonicalBelowIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1)
    exists X : CardinalIndex A -> Prop,
      (J.localize X).IsProper /\
      Nonempty (PointwiseStrictScale (cardinalProductFrame A (J.localize X))
        (cardinalScaleLength theta)) /\
      (J.extendBy X).IsProper /\
      (cardinalProductFrame A (J.extendBy X)).PointwiseStrictDirectedBelow (Order.succ theta) := by
  classical
  let J := (canonicalBelowIdeal A hRegulars theta).restrictAlong
    (fun i : CardinalIndex A => i.1)
  have hTheta := (cardinalProductRepresentation_mem_pcf_iff.mp hPcf).1
  have hUncountable : Cardinal.aleph0 < theta := by
    have hLift : Cardinal.aleph0.{u + 1} < Cardinal.lift.{u + 1} theta :=
      hInfinite.trans_lt ((Cardinal.cantor _).trans hPower)
    exact Cardinal.lift_lt.mp (by simpa only [Cardinal.lift_aleph0] using hLift)
  have hNoGlobal : Not (Nonempty (PointwiseStrictScale (cardinalProductFrame A J)
      (cardinalScaleLength theta))) := by
    rintro ⟨s⟩
    obtain ⟨mu, hMu, hThetaMu⟩ := hNonmax
    exact hThetaMu.not_ge ((isMaxPcf_of_canonicalBelowIndexIdeal_scale hRegulars hPcf s).2 mu hMu)
  have hExact : CardinalProductClosedExactUpperBoundPrinciple A J theta := by
    simpa only [Ideal.pushforward_id] using
      pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
        (J := J) id hInfinite hTheta hUncountable hPower
  have hExactLocal : forall X : CardinalIndex A -> Prop, (J.localize X).IsProper ->
      CardinalProductClosedExactUpperBoundPrinciple A (J.localize X) theta := by
    intro X _hX
    simpa only [Ideal.pushforward_id] using
      pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
        (J := J.localize X) id hInfinite hTheta hUncountable hPower
  let d0 : ProductElement (cardinalProductFrame A J) := fun k =>
    Ordinal.ToType.mk ⟨0, (hRegulars k.1 k.2).ord_pos⟩
  have hPred : Cardinal.mk (CardinalIndex A -> Prop) <= Cardinal.lift.{u + 1} theta := by
    rw [Cardinal.mk_arrow, Cardinal.mk_Prop, Cardinal.lift_ofNat,
      Cardinal.lift_id'.{0, u + 1}]
    exact hPower.le
  rcases pointwiseStrictCorollary2412_of_exactUpperBounds_of_mk_predicates_le
      hTheta hPred hDirected hExact hExactLocal d0 with hSucc | hGlobal | hSplit
  · exact False.elim (canonicalBelowIndexIdeal_not_succ_directed_of_mem_pcf hRegulars hPcf hSucc)
  · exact False.elim (hNoGlobal hGlobal)
  · obtain ⟨X, Y, hCover, hX, _hY, ⟨s⟩, hYDirected⟩ := hSplit
    have hNotEventually : Not (J.Eventually X) := by
      intro hEventually
      have hLocalLe : Ideal.Le (J.localize X) J := by
        intro S hS
        exact J.subset_small (J.union_small hS hEventually) (by
          intro k hk
          by_cases hXk : X k
          · exact Or.inl ⟨hk, hXk⟩
          · exact Or.inr hXk)
      exact hNoGlobal ⟨s.withLargerIdeal J hLocalLe⟩
    have hYLe : Ideal.Le (J.localize Y) (J.extendBy X) := by
      intro S hS
      refine ⟨(fun k => S k /\ Y k), hS, ?_⟩
      intro k hk
      rcases hCover k with hXk | hYk
      · exact Or.inr hXk
      · exact Or.inl ⟨hk, hYk⟩
    exact ⟨X, hX, ⟨s⟩, (J.extendBy_isProper_iff_not_eventually X).mpr hNotEventually,
      hYDirected.withLargerIdeal (J.extendBy X) hYLe⟩

theorem exists_pcf_gt_of_proper_successor_directed
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hUncountable : forall a, A a -> Cardinal.aleph0 < a)
    {J : Ideal (CardinalIndex A)} (hProper : J.IsProper) {theta : Cardinal.{u}}
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta)) :
    exists mu, cardinalProductRepresentation.pcf A mu /\ theta < mu := by
  obtain ⟨K, hUltra, hLe⟩ := exists_ultrafilterDual_ideal_extending J hProper
  obtain ⟨mu, hMuRegular, hTcf, _hMuUncountable⟩ :=
    cardinalProductFrame_exists_trueCofinality_of_small_cardinalIndex_of_aleph0_lt
      hRegulars hUltra hSmall hUncountable
  refine ⟨mu, cardinalProductRepresentation_mem_pcf_iff.mpr ⟨hMuRegular, K, hUltra, hTcf⟩, ?_⟩
  by_contra hNot
  have hMuSmall : Cardinal.mk (cardinalScaleLength mu).Level < Order.succ theta := by
    rw [mk_cardinalScaleLength_level]
    exact Order.lt_succ_iff.mpr (le_of_not_gt hNot)
  have hDirectedK : (cardinalProductFrame A K).PointwiseStrictDirectedBelow (Order.succ theta) :=
    hDirected.withLargerIdeal K hLe
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  obtain ⟨g, hg⟩ := hDirectedK (cardinalScaleLength mu).Level hMuSmall s.seq
  obtain ⟨alpha, ha⟩ := s.cofinal g
  exact ((cardinalProductFrame A K).eventuallyLt_of_eventually_pointwiseStrict
    hUltra.isProper (hg alpha)).2 ha

theorem pointwiseStrictCorollary2412_of_two_power_lt
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
      Cardinal.lift.{u + 1} theta)
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta)
    (d0 : ProductElement (cardinalProductFrame A J)) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta) \/
      Nonempty (PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta)) \/
      exists X Y : CardinalIndex A -> Prop,
        (forall k, X k \/ Y k) /\ (J.localize X).IsProper /\ (J.localize Y).IsProper /\
        Nonempty (PointwiseStrictScale (cardinalProductFrame A (J.localize X))
          (cardinalScaleLength theta)) /\
        (cardinalProductFrame A (J.localize Y)).PointwiseStrictDirectedBelow (Order.succ theta) := by
  have hUncountable : Cardinal.aleph0 < theta := by
    have hLift : Cardinal.aleph0.{u + 1} < Cardinal.lift.{u + 1} theta :=
      hInfinite.trans_lt ((Cardinal.cantor _).trans hPower)
    exact Cardinal.lift_lt.mp (by simpa only [Cardinal.lift_aleph0] using hLift)
  have hPred : Cardinal.mk (CardinalIndex A -> Prop) <= Cardinal.lift.{u + 1} theta := by
    rw [Cardinal.mk_arrow, Cardinal.mk_Prop, Cardinal.lift_ofNat, Cardinal.lift_id'.{0, u + 1}]
    exact hPower.le
  have hExact : forall K : Ideal (CardinalIndex A),
      CardinalProductClosedExactUpperBoundPrinciple A K theta := by
    intro K
    simpa only [Ideal.pushforward_id] using
      pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
        (J := K) id hInfinite hTheta hUncountable hPower
  exact pointwiseStrictCorollary2412_of_exactUpperBounds_of_mk_predicates_le
    hTheta hPred hDirected (hExact J) (fun X _ => hExact (J.localize X)) d0

/-- The maximal PCF stage of Jech 24.25(iv). Every other branch of the
trichotomy would yield a PCF value strictly above the supplied maximum. -/
theorem exists_canonicalBelowIndexIdeal_scale_of_max_of_directed
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hUncountable : forall a, A a -> Cardinal.aleph0 < a)
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    {theta : Cardinal.{u}}
    (hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
      Cardinal.lift.{u + 1} theta)
    (hMax : IsMaxPcf cardinalProductRepresentation A theta)
    (hDirected : (cardinalProductFrame A
      ((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow theta) :
    Nonempty (PointwiseStrictScale (cardinalProductFrame A
      ((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1))) (cardinalScaleLength theta)) := by
  let J := (canonicalBelowIdeal A hRegulars theta).restrictAlong
    (fun i : CardinalIndex A => i.1)
  have hTheta := (cardinalProductRepresentation_mem_pcf_iff.mp hMax.1).1
  let d0 : ProductElement (cardinalProductFrame A J) := fun k =>
    Ordinal.ToType.mk ⟨0, (hRegulars k.1 k.2).ord_pos⟩
  rcases pointwiseStrictCorollary2412_of_two_power_lt hInfinite hTheta hPower hDirected d0 with
    hSucc | hGlobal | hSplit
  · exact False.elim (canonicalBelowIndexIdeal_not_succ_directed_of_mem_pcf hRegulars hMax.1 hSucc)
  · exact hGlobal
  · obtain ⟨_X, Y, _hCover, _hX, hY, _hScale, hYDirected⟩ := hSplit
    obtain ⟨mu, hMu, hThetaMu⟩ := exists_pcf_gt_of_proper_successor_directed
      hRegulars hSmall hUncountable hY hYDirected
    exact False.elim (hThetaMu.not_ge (hMax.2 mu hMu))

/-- Successor-directedness forces every set whose PCF spectrum is bounded
by the threshold to be small. A positive counterexample yields an actual
ultrafilter scale on that set, contradicting directedness. -/
theorem canonicalAtMostIndexIdeal_le_of_successorDirected
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hUncountable : forall a, A a -> Cardinal.aleph0 < a)
    {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (hDirected : (cardinalProductFrame A J).PointwiseStrictDirectedBelow (Order.succ theta)) :
    Ideal.Le ((canonicalAtMostIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1)) J := by
  classical
  intro S hS
  by_contra hNotSmall
  obtain ⟨K, hUltra, hLocalLe⟩ := exists_ultrafilterDual_ideal_extending (J.localize S)
    ((J.localize_isProper_iff S).mpr hNotSmall)
  have hLe : Ideal.Le J K := Ideal.le_trans (J.le_localize S) hLocalLe
  obtain ⟨mu, hMuRegular, hTcf, _⟩ :=
    cardinalProductFrame_exists_trueCofinality_of_small_cardinalIndex_of_aleph0_lt
      hRegulars hUltra hSmall hUncountable
  let W : CardSet.{u} := interCardSet A (fun a => exists i : CardinalIndex A, i.1 = a /\ S i)
  have hLocalS : (J.localize S).Eventually S := by
    change J.Small (fun k => Not (S k) /\ S k)
    exact J.subset_small J.empty_small (fun k hk => hk.1 hk.2)
  have hEventuallyS : K.Eventually S := hLocalLe _ hLocalS
  have hEventuallyW : K.Eventually (fun k => W k.1) :=
    K.eventually_mono hEventuallyS (fun k hk => ⟨k.2, k, rfl, hk⟩)
  have hMuW : cardinalProductRepresentation.pcf W mu :=
    cardinalProductRepresentation_mem_pcf_of_eventually_mem
      (A := W) (B := A) (fun _ h => h.1) hRegulars hMuRegular K hUltra hTcf hEventuallyW
  have hMuLe : mu <= theta := hS mu hMuW
  have hDirectedK : (cardinalProductFrame A K).PointwiseStrictDirectedBelow (Order.succ theta) :=
    hDirected.withLargerIdeal K hLe
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  obtain ⟨g, hg⟩ := hDirectedK (cardinalScaleLength mu).Level
    (by rw [mk_cardinalScaleLength_level]; exact Order.lt_succ_iff.mpr hMuLe) s.seq
  obtain ⟨alpha, ha⟩ := s.cofinal g
  exact ((cardinalProductFrame A K).eventuallyLt_of_eventually_pointwiseStrict
    hUltra.isProper (hg alpha)).2 ha

theorem canonicalAtMostIndexIdeal_small_of_localized_scale
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (X : CardinalIndex A -> Prop)
    (s : PointwiseStrictScale (cardinalProductFrame A
      (((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1)).localize X)) (cardinalScaleLength theta)) :
    ((canonicalAtMostIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1)).Small X := by
  classical
  let W : CardSet.{u} := interCardSet A (fun a => exists i : CardinalIndex A, i.1 = a /\ X i)
  change forall mu, cardinalProductRepresentation.pcf W mu -> mu <= theta
  intro mu hMu
  by_contra hNot
  have hThetaMu : theta < mu := lt_of_not_ge hNot
  obtain ⟨hMuRegular, U, hUltraU, hTcfU⟩ := cardinalProductRepresentation_mem_pcf_iff.mp hMu
  have hWA : SubsetOf W A := fun _ h => h.1
  let K := U.pushforward (cardinalIndexMap hWA)
  have hUltra : K.IsUltrafilterDual := hUltraU.pushforward _
  obtain ⟨t⟩ := hTcfU.hasScaleWitness
  have hTcf : HasTrueCofinality (cardinalProductFrame A K) (cardinalScaleLength mu) :=
    extendCardinalScale_hasTrueCofinality hWA hRegulars hMuRegular t
  let J := (canonicalBelowIdeal A hRegulars theta).restrictAlong
    (fun i : CardinalIndex A => i.1)
  have hBelowLe : Ideal.Le J K :=
    canonicalBelowIndexIdeal_le_of_trueCofinality hRegulars hUltra hMuRegular hThetaMu.le hTcf
  have hX : K.Eventually X := by
    change U.Eventually (fun k => X (cardinalIndexMap hWA k))
    apply U.eventually_of_forall
    intro k
    obtain ⟨i, hi, hXi⟩ := k.2.2
    have hEq : i = cardinalIndexMap hWA k := Subtype.ext hi
    exact hEq ▸ hXi
  have hLocalLe : Ideal.Le (J.localize X) K := by
    intro S hS
    exact K.subset_small (K.union_small (hBelowLe _ hS) hX) (by
      intro k hk
      by_cases hXk : X k
      · exact Or.inl ⟨hk, hXk⟩
      · exact Or.inr hXk)
  have hTcfTheta : HasTrueCofinality (cardinalProductFrame A K) (cardinalScaleLength theta) :=
    cardinalScaleLength_hasTrueCofinality hTheta ((s.withLargerIdeal K hLocalLe).toScale hUltra.isProper)
  have hEq : mu = theta := by
    simpa only [mk_cardinalScaleLength_level] using
      cardinal_mk_level_eq_of_hasTrueCofinality hTcf hTcfTheta
  exact hThetaMu.ne hEq.symm

/-- The adjoined ideal from the generator step is exactly the canonical
at-most ideal. One inclusion uses the localized scale; the other uses the
successor-directedness obstruction. No ideal-equivalence field is assumed. -/
theorem canonicalBelowIndexIdeal_extendBy_eq_atMost_of_scale_and_directed
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hUncountable : forall a, A a -> Cardinal.aleph0 < a)
    {theta : Cardinal.{u}} (hTheta : Cardinal.IsRegular theta)
    (X : CardinalIndex A -> Prop)
    (s : PointwiseStrictScale (cardinalProductFrame A
      (((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1)).localize X)) (cardinalScaleLength theta))
    (hDirected : (cardinalProductFrame A
      (((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1)).extendBy X)).PointwiseStrictDirectedBelow (Order.succ theta)) :
    (((canonicalBelowIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1)).extendBy X) =
    (canonicalAtMostIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1) := by
  let K := (canonicalAtMostIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1)
  have hX : K.Small X := canonicalAtMostIndexIdeal_small_of_localized_scale hRegulars hTheta X s
  have hReverse := canonicalAtMostIndexIdeal_le_of_successorDirected hRegulars hSmall hUncountable hDirected
  apply Ideal.ext
  intro S
  constructor
  · rintro ⟨T, hT, hCover⟩
    have hTK : K.Small T := fun mu hMu => (hT mu hMu).le
    exact K.subset_small (K.union_small hTK hX) hCover
  · exact hReverse S

theorem cardinalProduct_pointwiseStrictDirectedBelow_of_not_proper
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    {J : Ideal (CardinalIndex A)} (hNotProper : Not J.IsProper)
    (theta : Cardinal.{u}) :
    (cardinalProductFrame A J).PointwiseStrictDirectedBelow theta := by
  classical
  have hTop : J.Small (fun _ => True) := by
    simpa only [Ideal.IsProper, not_not] using hNotProper
  intro T _hT d
  let g : ProductElement (cardinalProductFrame A J) := fun k =>
    Ordinal.ToType.mk ⟨0, (hRegulars k.1 k.2).ord_pos⟩
  exact ⟨g, fun _ => J.subset_small hTop (fun _ _ => True.intro)⟩

theorem canonicalAtMostIndexIdeal_successorDirected_of_belowDirected
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hUncountable : forall a, A a -> Cardinal.aleph0 < a)
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    {theta : Cardinal.{u}}
    (hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
      Cardinal.lift.{u + 1} theta)
    (hDirected : (cardinalProductFrame A
      ((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow theta) :
    (cardinalProductFrame A ((canonicalAtMostIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow (Order.succ theta) := by
  classical
  by_cases hPcf : cardinalProductRepresentation.pcf A theta
  · by_cases hNonmax : exists mu, cardinalProductRepresentation.pcf A mu /\ theta < mu
    · obtain ⟨X, _hXProper, ⟨s⟩, _hExtendedProper, hExtendedDirected⟩ :=
        exists_generator_step_of_canonicalBelow_directed_of_nonmax
          hRegulars hInfinite hPower hPcf hNonmax hDirected
      have hEq := canonicalBelowIndexIdeal_extendBy_eq_atMost_of_scale_and_directed
        hRegulars hSmall hUncountable (cardinalProductRepresentation_mem_pcf_iff.mp hPcf).1
        X s hExtendedDirected
      rwa [hEq] at hExtendedDirected
    · apply cardinalProduct_pointwiseStrictDirectedBelow_of_not_proper hRegulars
      intro hProper
      apply hProper
      intro mu hMu
      have hMuA : cardinalProductRepresentation.pcf A mu :=
        cardinalProductRepresentation_pcf_mono (fun _ h => h.1) hRegulars mu hMu
      exact le_of_not_gt (fun h => hNonmax ⟨mu, hMuA, h⟩)
  · have hEq := canonicalBelowIdeal_eq_canonicalAtMostIdeal_of_not_mem hRegulars hPcf
    rw [← hEq]
    by_cases hProper : ((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1)).IsProper
    · have hUncTheta : Cardinal.aleph0 < theta := by
        have hLift : Cardinal.aleph0.{u + 1} < Cardinal.lift.{u + 1} theta :=
          hInfinite.trans_lt ((Cardinal.cantor _).trans hPower)
        exact Cardinal.lift_lt.mp (by simpa only [Cardinal.lift_aleph0] using hLift)
      exact pointwiseStrictDirectedBelow_succ_of_not_mem_pcf_of_two_power_lt
        hProper hInfinite hUncTheta hPower hPcf hDirected
    · exact cardinalProduct_pointwiseStrictDirectedBelow_of_not_proper hRegulars hProper _

/-- The full directedness induction of Jech 24.25(i). For a family of
cardinality `lambda < theta`, either coordinatewise regularity bounds it
directly, or the induction hypothesis at `lambda` supplies the successor
step. This treats limit thresholds without assuming continuity of ideals. -/
theorem canonicalBelowIndexIdeal_directed_of_two_power_below_coordinates
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    (theta : Cardinal.{u}) :
    (cardinalProductFrame A ((canonicalBelowIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow theta := by
  classical
  have hUncountable : forall a, A a -> Cardinal.aleph0 < a := by
    intro a ha
    have hLift : Cardinal.aleph0.{u + 1} < Cardinal.lift.{u + 1} a :=
      hInfinite.trans_lt ((Cardinal.cantor _).trans (hPower a ha))
    exact Cardinal.lift_lt.mp (by simpa only [Cardinal.lift_aleph0] using hLift)
  refine Cardinal.lt_wf.induction (C := fun kappa : Cardinal.{u} =>
    (cardinalProductFrame A ((canonicalBelowIdeal A hRegulars kappa).restrictAlong
      (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow kappa) theta ?_
  intro kappa ih T hT d
  let J := (canonicalBelowIdeal A hRegulars kappa).restrictAlong
    (fun i : CardinalIndex A => i.1)
  by_cases hCoordinate : forall a, A a -> Cardinal.mk T < a
  · obtain ⟨g, hg⟩ := cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt
      hRegulars hCoordinate d
    exact ⟨g, fun i => J.eventually_of_forall (fun k => ⟨(hg i k).le, not_le_of_gt (hg i k)⟩)⟩
  · have hLarge : exists a, A a /\ a <= Cardinal.mk T := by
      by_contra hNot
      apply hCoordinate
      intro a ha
      exact lt_of_not_ge (fun h => hNot ⟨a, ha, h⟩)
    obtain ⟨a, ha, haT⟩ := hLarge
    have hPowerT : (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} (Cardinal.mk T) :=
      (hPower a ha).trans_le (Cardinal.lift_le.mpr haT)
    have hStep := canonicalAtMostIndexIdeal_successorDirected_of_belowDirected
      hRegulars hSmall hUncountable hInfinite hPowerT (ih (Cardinal.mk T) hT)
    have hLe : Ideal.Le ((canonicalAtMostIdeal A hRegulars (Cardinal.mk T)).restrictAlong
        (fun i : CardinalIndex A => i.1)) J := by
      intro S hS
      exact (canonicalAtMostIdeal_le_canonicalBelowIdeal_of_lt hRegulars hT) _ hS
    have hDirectedJ : (cardinalProductFrame A J).PointwiseStrictDirectedBelow
        (Order.succ (Cardinal.mk T)) := hStep.withLargerIdeal J hLe
    exact hDirectedJ T (Order.lt_succ _) d

theorem canonicalBelowIdeal_succ_eq_atMost
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A) (theta : Cardinal.{u}) :
    canonicalBelowIdeal A hRegulars (Order.succ theta) = canonicalAtMostIdeal A hRegulars theta := by
  apply Ideal.ext
  intro S
  change (forall mu, cardinalProductRepresentation.pcf (interCardSet A S) mu -> mu < Order.succ theta) <->
    (forall mu, cardinalProductRepresentation.pcf (interCardSet A S) mu -> mu <= theta)
  simp only [Order.lt_succ_iff]

theorem canonicalAtMostIndexIdeal_successorDirected_of_two_power_below_coordinates
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    (theta : Cardinal.{u}) :
    (cardinalProductFrame A ((canonicalAtMostIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow (Order.succ theta) := by
  have h := canonicalBelowIndexIdeal_directed_of_two_power_below_coordinates
    hRegulars hSmall hInfinite hPower (Order.succ theta)
  rwa [canonicalBelowIdeal_succ_eq_atMost] at h

theorem exists_canonicalIndex_generator_of_two_power_below_coordinates
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    {theta : Cardinal.{u}} (hPcf : cardinalProductRepresentation.pcf A theta) :
    let J := (canonicalBelowIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1)
    exists X : CardinalIndex A -> Prop,
      Nonempty (PointwiseStrictScale (cardinalProductFrame A (J.localize X)) (cardinalScaleLength theta)) /\
      J.extendBy X = (canonicalAtMostIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1) := by
  classical
  let J := (canonicalBelowIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1)
  have hUncountable : forall a, A a -> Cardinal.aleph0 < a := by
    intro a ha
    have hLift : Cardinal.aleph0.{u + 1} < Cardinal.lift.{u + 1} a :=
      hInfinite.trans_lt ((Cardinal.cantor _).trans (hPower a ha))
    exact Cardinal.lift_lt.mp (by simpa only [Cardinal.lift_aleph0] using hLift)
  obtain ⟨a, ha, haTheta⟩ := cardinalProductRepresentation_mem_pcf_exists_member_le hRegulars hPcf
  have hPowerTheta := (hPower a ha).trans_le (Cardinal.lift_le.mpr haTheta)
  have hTheta := (cardinalProductRepresentation_mem_pcf_iff.mp hPcf).1
  have hDirected := canonicalBelowIndexIdeal_directed_of_two_power_below_coordinates
    hRegulars hSmall hInfinite hPower theta
  by_cases hNonmax : exists mu, cardinalProductRepresentation.pcf A mu /\ theta < mu
  · obtain ⟨X, _hX, ⟨s⟩, _hExt, hExtDirected⟩ :=
      exists_generator_step_of_canonicalBelow_directed_of_nonmax
        hRegulars hInfinite hPowerTheta hPcf hNonmax hDirected
    exact ⟨X, ⟨s⟩, canonicalBelowIndexIdeal_extendBy_eq_atMost_of_scale_and_directed
      hRegulars hSmall hUncountable hTheta X s hExtDirected⟩
  · have hMax : IsMaxPcf cardinalProductRepresentation A theta :=
      ⟨hPcf, fun mu hMu => le_of_not_gt (fun h => hNonmax ⟨mu, hMu, h⟩)⟩
    obtain ⟨s⟩ := exists_canonicalBelowIndexIdeal_scale_of_max_of_directed
      hRegulars hSmall hUncountable hInfinite hPowerTheta hMax hDirected
    have hScale : Nonempty (PointwiseStrictScale (cardinalProductFrame A (J.localize (fun _ => True)))
        (cardinalScaleLength theta)) := by simpa only [Ideal.localize_true] using (Nonempty.intro s)
    obtain ⟨t⟩ := hScale
    have hExtDirected : (cardinalProductFrame A (J.extendBy (fun _ => True))).PointwiseStrictDirectedBelow
        (Order.succ theta) := by
      apply cardinalProduct_pointwiseStrictDirectedBelow_of_not_proper hRegulars
      intro hProper
      exact hProper (J.generator_small_in_extendBy (fun _ => True))
    exact ⟨(fun _ => True), ⟨t⟩, canonicalBelowIndexIdeal_extendBy_eq_atMost_of_scale_and_directed
      hRegulars hSmall hUncountable hTheta _ t hExtDirected⟩

/-- Lift the index-level ideal identity to the ambient cardinal predicates.
Outside `A`, all predicates are already in the canonical strict-below ideal. -/
theorem canonicalGenerator_ideal_equiv_of_index_eq
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A) {theta : Cardinal.{u}}
    (X : CardinalIndex A -> Prop)
    (hEq : (((canonicalBelowIdeal A hRegulars theta).restrictAlong
      (fun i : CardinalIndex A => i.1)).extendBy X) =
      (canonicalAtMostIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1)) :
    Ideal.Equivalent (canonicalAtMostIdeal A hRegulars theta)
      ((canonicalBelowIdeal A hRegulars theta).extendBy
        (fun a => exists i : CardinalIndex A, i.1 = a /\ X i)) := by
  classical
  let B : CardSet.{u} := fun a => exists i : CardinalIndex A, i.1 = a /\ X i
  let J := (canonicalBelowIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1)
  let K := (canonicalAtMostIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1)
  have hB : (canonicalAtMostIdeal A hRegulars theta).Small B := by
    have hX : K.Small X := by
      change ((canonicalAtMostIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1)).Small X
      rw [← hEq]
      exact J.generator_small_in_extendBy X
    exact hX
  constructor
  · intro S hS
    have hIndexS : K.Small (fun i => S i.1) := by
      intro mu hMu
      apply hS mu
      apply cardinalProductRepresentation_pcf_mono _ (interCardSet_regulars hRegulars) mu hMu
      intro a ha
      obtain ⟨i, hi, hSi⟩ := ha.2
      exact ⟨ha.1, hi ▸ hSi⟩
    have hGenerated : (J.extendBy X).Small (fun i => S i.1) := by
      change (((canonicalBelowIdeal A hRegulars theta).restrictAlong
        (fun i : CardinalIndex A => i.1)).extendBy X).Small _
      rw [hEq]
      exact hIndexS
    obtain ⟨T, hT, hCover⟩ := hGenerated
    let R : CardSet.{u} := fun a => A a -> exists i : CardinalIndex A, i.1 = a /\ T i
    have hR : (canonicalBelowIdeal A hRegulars theta).Small R := by
      intro mu hMu
      apply hT mu
      exact cardinalProductRepresentation_pcf_mono
        (fun _ h => ⟨h.1, h.2 h.1⟩) (interCardSet_regulars hRegulars) mu hMu
    refine ⟨R, hR, ?_⟩
    intro a ha
    by_cases hAa : A a
    · rcases hCover ⟨a, hAa⟩ ha with hTa | hXa
      · exact Or.inl (fun _ => ⟨⟨a, hAa⟩, rfl, hTa⟩)
      · exact Or.inr ⟨⟨a, hAa⟩, rfl, hXa⟩
    · exact Or.inl (fun h => False.elim (hAa h))
  · rintro S ⟨T, hT, hCover⟩
    exact (canonicalAtMostIdeal A hRegulars theta).subset_small
      ((canonicalAtMostIdeal A hRegulars theta).union_small
        (fun mu hMu => (hT mu hMu).le) hB) hCover

noncomputable def canonicalGeneratorIndexSet
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    (theta : Cardinal.{u}) : CardinalIndex A -> Prop :=
  by
    classical
    exact if h : cardinalProductRepresentation.pcf A theta then
      Classical.choose (exists_canonicalIndex_generator_of_two_power_below_coordinates
        hRegulars hSmall hInfinite hPower h)
    else fun _ => False

noncomputable def canonicalGeneratorPointwiseScale
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    {theta : Cardinal.{u}} (hTheta : cardinalProductRepresentation.pcf A theta) :
    PointwiseStrictScale
      (cardinalProductFrame A
        (((canonicalBelowIdeal A hRegulars theta).restrictAlong
          (fun i : CardinalIndex A => i.1)).localize
            (canonicalGeneratorIndexSet hRegulars hSmall hInfinite hPower theta)))
      (cardinalScaleLength theta) := by
  classical
  simpa only [canonicalGeneratorIndexSet, dif_pos hTheta] using
    (Classical.choice
      (Classical.choose_spec (exists_canonicalIndex_generator_of_two_power_below_coordinates
        hRegulars hSmall hInfinite hPower hTheta)).1)

/-- The semantic generator system is constructed under the displayed
small-index and powerset gap hypotheses. No generator or ideal-equivalence
field is supplied by the caller. Transitivity is not asserted here. -/
noncomputable def canonicalGeneratorSystemOfTwoPowerBelowCoordinates
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a) :
    GeneratorSystem cardinalProductRepresentation A := by
  classical
  let X (theta : Cardinal.{u}) : CardinalIndex A -> Prop :=
    canonicalGeneratorIndexSet hRegulars hSmall hInfinite hPower theta
  let B (theta : Cardinal.{u}) : CardSet.{u} :=
    fun a => exists i : CardinalIndex A, i.1 = a /\ X theta i
  apply canonicalGeneratorSystemOfGenerator hRegulars B
  · intro theta _hTheta a ha
    obtain ⟨i, hi, _⟩ := ha
    exact hi ▸ i.2
  · intro theta hTheta
    apply canonicalGenerator_ideal_equiv_of_index_eq hRegulars (X theta)
    simpa only [X, canonicalGeneratorIndexSet, dif_pos hTheta] using
      (Classical.choose_spec (exists_canonicalIndex_generator_of_two_power_below_coordinates
        hRegulars hSmall hInfinite hPower hTheta)).2

theorem canonicalGeneratorSystem_generator_at_index_iff
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    (theta : Cardinal.{u}) (i : CardinalIndex A) :
    (canonicalGeneratorSystemOfTwoPowerBelowCoordinates hRegulars hSmall hInfinite hPower).generator
        theta i.1 <-> canonicalGeneratorIndexSet hRegulars hSmall hInfinite hPower theta i := by
  classical
  change (exists j : CardinalIndex A, j.1 = i.1 /\
    canonicalGeneratorIndexSet hRegulars hSmall hInfinite hPower theta j) <-> _
  constructor
  · rintro ⟨j, hj, hX⟩
    have hji : j = i := Subtype.ext hj
    simpa only [hji] using hX
  · intro hX
    exact ⟨i, rfl, hX⟩

/-- The scale selected during the generator construction really is a scale
on the displayed semantic generator, not merely on its internal index code. -/
theorem canonicalGeneratorSystem_generator_hasPointwiseScale
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    {theta : Cardinal.{u}} (hTheta : cardinalProductRepresentation.pcf A theta) :
    let G := canonicalGeneratorSystemOfTwoPowerBelowCoordinates hRegulars hSmall hInfinite hPower
    Nonempty (PointwiseStrictScale
      (cardinalProductFrame A
        (((G.belowIdeal theta).restrictAlong (fun i : CardinalIndex A => i.1)).localize
          (fun i => G.generator theta i.1)))
      (cardinalScaleLength theta)) := by
  classical
  let G := canonicalGeneratorSystemOfTwoPowerBelowCoordinates hRegulars hSmall hInfinite hPower
  have hIdeal : (((G.belowIdeal theta).restrictAlong (fun i : CardinalIndex A => i.1)).localize
      (fun i => G.generator theta i.1)) =
      (((canonicalBelowIdeal A hRegulars theta).restrictAlong (fun i : CardinalIndex A => i.1)).localize
        (canonicalGeneratorIndexSet hRegulars hSmall hInfinite hPower theta)) := by
    rw [G.belowIdeal_eq_canonical hRegulars theta]
    apply Ideal.ext
    intro S
    change (canonicalBelowIdeal A hRegulars theta).Small
        (fun a => exists i : CardinalIndex A, i.1 = a /\ S i /\ G.generator theta i.1) <->
      (canonicalBelowIdeal A hRegulars theta).Small
        (fun a => exists i : CardinalIndex A, i.1 = a /\ S i /\
          canonicalGeneratorIndexSet hRegulars hSmall hInfinite hPower theta i)
    have hPred : (fun a => exists i : CardinalIndex A,
        i.1 = a /\ S i /\ G.generator theta i.1) =
        (fun a => exists i : CardinalIndex A, i.1 = a /\ S i /\
          canonicalGeneratorIndexSet hRegulars hSmall hInfinite hPower theta i) := by
      funext a
      apply propext
      constructor <;> rintro ⟨i, hi, hSi, hGi⟩
      · exact ⟨i, hi, hSi,
          (canonicalGeneratorSystem_generator_at_index_iff
            hRegulars hSmall hInfinite hPower theta i).mp hGi⟩
      · exact ⟨i, hi, hSi,
          (canonicalGeneratorSystem_generator_at_index_iff
            hRegulars hSmall hInfinite hPower theta i).mpr hGi⟩
    rw [hPred]
  change Nonempty (PointwiseStrictScale
      (cardinalProductFrame A
        (((G.belowIdeal theta).restrictAlong (fun i : CardinalIndex A => i.1)).localize
          (fun i => G.generator theta i.1)))
      (cardinalScaleLength theta))
  rw [hIdeal]
  exact ⟨canonicalGeneratorPointwiseScale hRegulars hSmall hInfinite hPower hTheta⟩

noncomputable def canonicalSemanticGeneratorPointwiseScale
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    {theta : Cardinal.{u}} (hTheta : cardinalProductRepresentation.pcf A theta) :
    let G := canonicalGeneratorSystemOfTwoPowerBelowCoordinates hRegulars hSmall hInfinite hPower
    PointwiseStrictScale
      (cardinalProductFrame A
        (((G.belowIdeal theta).restrictAlong (fun i : CardinalIndex A => i.1)).localize
          (fun i => G.generator theta i.1)))
      (cardinalScaleLength theta) := by
  classical
  exact Classical.choice (canonicalGeneratorSystem_generator_hasPointwiseScale
    hRegulars hSmall hInfinite hPower hTheta)

/-- Restrict directedness along a subset of the coordinates while retaining
the same ambient ideal. No size or infinitude assumption on the subset is needed. -/
theorem cardinalProduct_directed_restrict_subset
    {A W : CardSet.{u}} (hWA : SubsetOf W A) (hRegulars : SetOfRegulars A)
    (I : Ideal Cardinal.{u}) {theta : Cardinal.{u}}
    (hDirected : (cardinalProductFrame A (I.restrictAlong
      (fun i : CardinalIndex A => i.1))).PointwiseStrictDirectedBelow theta) :
    (cardinalProductFrame W (I.restrictAlong
      (fun i : CardinalIndex W => i.1))).PointwiseStrictDirectedBelow theta := by
  classical
  intro T hT d
  let e (t : T) : ProductElement (cardinalProductFrame A
      (I.restrictAlong (fun i : CardinalIndex A => i.1))) :=
    extendCardinalProductElement hWA hRegulars (d t)
  obtain ⟨g, hg⟩ := hDirected T hT e
  refine ⟨(fun i => g (cardinalIndexMap hWA i)), ?_⟩
  intro t
  apply I.subset_small (hg t)
  rintro a ⟨i, hi, hBad⟩
  refine ⟨cardinalIndexMap hWA i, hi, ?_⟩
  simpa only [e, extendCardinalProductElement_at_indexMap] using hBad

/-- The successor-directed invariant on every subfamily is derived from the
canonical filtration, independently of which semantic generators are chosen. -/
theorem generatorAtMostIdealSuccessorDirected_of_two_power_below_coordinates
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    (G : GeneratorSystem cardinalProductRepresentation A) :
    GeneratorAtMostIdealSuccessorDirected G := by
  intro W hWA theta _hTheta
  rw [G.atMostIdeal_eq_canonical hRegulars theta]
  exact cardinalProduct_directed_restrict_subset hWA hRegulars _
    (canonicalAtMostIndexIdeal_successorDirected_of_two_power_below_coordinates
      hRegulars hSmall hInfinite hPower theta)

/-- Capture realizes each PCF value on its own generator. -/
theorem generator_mem_pcf_of_successorDirected
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hDirected : GeneratorAtMostIdealSuccessorDirected G)
    {theta : Cardinal.{u}} (hTheta : cardinalProductRepresentation.pcf A theta) :
    cardinalProductRepresentation.pcf (interCardSet A (G.generator theta)) theta := by
  obtain ⟨hReg, J, hUltra, hTcf⟩ := cardinalProductRepresentation_mem_pcf_iff.mp hTheta
  have hCapture := generatorCapturesCanonicalUltrafilters_of_atMostIdealEscape hRegulars G
    (generatorAtMostIdealEscapesCanonicalUltrafilters_of_successorDirected G hDirected)
  have hEv := hCapture A (fun _ h => h) J hUltra theta hReg hTheta hTcf
  exact cardinalProductRepresentation_mem_pcf_of_eventually_mem
    (fun _ h => h.1) hRegulars hReg J hUltra hTcf
    (J.eventually_mono hEv (fun i h => ⟨i.2, h⟩))

/-- Different PCF values have different generator predicates on the actual
coordinate set: each is the maximum PCF value of its generator. -/
theorem generator_predicate_injective_of_successorDirected
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hDirected : GeneratorAtMostIdealSuccessorDirected G) :
    Function.Injective (fun theta : CardinalIndex (cardinalProductRepresentation.pcf A) =>
      fun i : CardinalIndex A => G.generator theta.1 i.1) := by
  intro theta mu hEq
  have hInter : interCardSet A (G.generator theta.1) = interCardSet A (G.generator mu.1) := by
    funext a
    apply propext
    constructor
    · rintro ⟨ha, h⟩
      have hPoint : G.generator theta.1 a = G.generator mu.1 a := congrFun hEq ⟨a, ha⟩
      exact ⟨ha, hPoint ▸ h⟩
    · rintro ⟨ha, h⟩
      have hPoint : G.generator theta.1 a = G.generator mu.1 a := congrFun hEq ⟨a, ha⟩
      exact ⟨ha, hPoint.symm ▸ h⟩
  apply Subtype.ext
  apply le_antisymm
  · apply G.generator_pcf_le mu.2
    rw [← hInter]
    exact generator_mem_pcf_of_successorDirected hRegulars G hDirected theta.2
  · apply G.generator_pcf_le theta.2
    rw [hInter]
    exact generator_mem_pcf_of_successorDirected hRegulars G hDirected mu.2

/-- The generator theorem sharpens the pre-generator double-powerset bound
to the single-powerset bound on the spectrum. -/
theorem cardinal_mk_cardinalIndex_pcf_le_two_power_of_two_power_below_coordinates
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a) :
    Cardinal.mk (CardinalIndex (cardinalProductRepresentation.pcf A)) <=
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) := by
  let G := canonicalGeneratorSystemOfTwoPowerBelowCoordinates hRegulars hSmall hInfinite hPower
  have hDir := generatorAtMostIdealSuccessorDirected_of_two_power_below_coordinates
    hRegulars hSmall hInfinite hPower G
  have hBound := Cardinal.mk_le_of_injective
    (generator_predicate_injective_of_successorDirected hRegulars G hDir)
  simpa only [Cardinal.mk_pi, Cardinal.mk_Prop, Cardinal.lift_ofNat,
    Cardinal.prod_const, Cardinal.lift_id'.{0, u + 1}] using hBound

/-- The source double-powerset gap yields the single-powerset gap needed
to construct generators on the spectrum itself. -/
theorem pcf_two_power_below_coordinates_of_doublePower
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hDouble : CardinalProductDoublePowerBelowCoordinates A) :
    forall theta, cardinalProductRepresentation.pcf A theta ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex (cardinalProductRepresentation.pcf A)) <
        Cardinal.lift.{u + 1} theta := by
  have hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a :=
    fun a ha => (Cardinal.cantor _).trans (hDouble ⟨a, ha⟩)
  have hBound := cardinal_mk_cardinalIndex_pcf_le_two_power_of_two_power_below_coordinates
    hRegulars hSmall hInfinite hPower
  intro theta hTheta
  obtain ⟨a, ha, haTheta⟩ := cardinalProductRepresentation_mem_pcf_exists_member_le hRegulars hTheta
  exact (Cardinal.power_le_power_left two_ne_zero hBound).trans_lt
    ((hDouble ⟨a, ha⟩).trans_le (Cardinal.lift_le.mpr haTheta))

end PcfProject
