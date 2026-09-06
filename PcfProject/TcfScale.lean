import PcfProject.IdealProduct
import Mathlib.SetTheory.Cardinal.Basic

/-!
# True cofinality and scales

This file builds on the verified abstract reduced-product layer. It defines
strict eventual comparison, abstract scale lengths, scales, cofinal families,
and true cofinality. A scale witness alone is deliberately kept separate from
true cofinality: the latter also says that every cofinal family has cardinality
at least the scale length. It remains abstract: no PCF structural theorem or
cardinal arithmetic bound is asserted here.
-/

namespace PcfProject

universe u v w

namespace ReducedProductFrame

variable (F : ReducedProductFrame.{u, v})

/-- The asymmetric strict part of the reduced product's eventual preorder. -/
def eventuallyLt (x y : ProductElement F) : Prop :=
  F.eventuallyLe x y /\ Not (F.eventuallyLe y x)

/-- The source-level strict order used in PCF scale constructions: on an
eventual set of coordinates, `x` is below `y` and `y` is not below `x`.
Unlike preorder asymmetry, this relation is preserved when the ideal is
enlarged. -/
def eventuallyPointwiseLt (x y : ProductElement F) : Prop :=
  F.J.Eventually (fun i =>
    F.le i (x i) (y i) /\ Not (F.le i (y i) (x i)))

theorem eventuallyPointwiseLt_trans
    {x y z : ProductElement F}
    (hxy : F.eventuallyPointwiseLt x y)
    (hyz : F.eventuallyPointwiseLt y z) :
    F.eventuallyPointwiseLt x z := by
  classical
  exact F.J.eventually_mono (F.J.eventually_and hxy hyz) (by
    intro i h
    exact ⟨F.le_trans i h.1.1 h.2.1, fun hzx =>
      h.1.2 (F.le_trans i h.2.1 hzx)⟩)

#print axioms ReducedProductFrame.eventuallyPointwiseLt_trans

theorem eventuallyLe_eventuallyPointwiseLt_trans
    {x y z : ProductElement F}
    (hxy : F.eventuallyLe x y)
    (hyz : F.eventuallyPointwiseLt y z) :
    F.eventuallyPointwiseLt x z := by
  classical
  exact F.J.eventually_mono (F.J.eventually_and hxy hyz) (by
    intro i h
    exact ⟨F.le_trans i h.1 h.2.1, fun hzx =>
      h.2.2 (F.le_trans i hzx h.1)⟩)

#print axioms
  ReducedProductFrame.eventuallyLe_eventuallyPointwiseLt_trans

/-! Coordinate extraction used in the contradiction argument of Jech Lemma
24.14.  Two eventual pointwise-strict comparisons can be intersected; if
the next family member is not eventually below the last function, one
coordinate in that intersection must complete a four-term strict chain. -/
theorem exists_pointwiseStrict_chain_of_not_eventuallyLe
    (hTotal : forall (k : F.Index) (x y : F.Coord k),
      F.le k x y \/ F.le k y x)
    {s f h next : ProductElement F}
    (hsf : F.eventuallyPointwiseLt s f)
    (hfh : F.eventuallyPointwiseLt f h)
    (hNotNextLe : Not (F.eventuallyLe next h)) :
    exists k : F.Index,
      (F.le k (s k) (f k) /\ Not (F.le k (f k) (s k))) /\
      (F.le k (f k) (h k) /\ Not (F.le k (h k) (f k))) /\
      (F.le k (h k) (next k) /\ Not (F.le k (next k) (h k))) := by
  classical
  by_contra hNoChain
  apply hNotNextLe
  have hGood := F.J.eventually_and hsf hfh
  exact F.J.eventually_mono hGood (by
    intro k hk
    by_contra hNextNotLe
    have hLast : F.le k (h k) (next k) /\
        Not (F.le k (next k) (h k)) :=
      ⟨(hTotal k (h k) (next k)).resolve_right hNextNotLe, hNextNotLe⟩
    exact hNoChain ⟨k, hk.1, hk.2, hLast⟩)

#print axioms
  ReducedProductFrame.exists_pointwiseStrict_chain_of_not_eventuallyLe

/-- A family is cofinal in the reduced product when every product element is
eventually below one of its members. -/
def IsCofinalFamily
    {ι : Type w}
    (d : ι -> ProductElement F) : Prop :=
  forall g : ProductElement F, exists i, F.eventuallyLe g (d i)

/-- A family is pointwise-strictly below `g` at every index. This is the
source-level upper-bound notion used in the exact-upper-bound argument of
Jech 24.10--24.12.  Pointwise eventual strictness is used because it is the
comparison that survives localization or enlargement of a non-maximal ideal. -/
def IsPointwiseStrictUpperBound
    {ι : Type w}
    (d : ι -> ProductElement F)
    (g : ProductElement F) : Prop :=
  forall i, F.eventuallyPointwiseLt (d i) g

/-- Every product element strictly below `g` is eventually dominated by the family. -/
def IsPointwiseStrictCofinalBelow
    {ι : Type w}
    (d : ι -> ProductElement F)
    (g : ProductElement F) : Prop :=
  forall h : ProductElement F,
    F.eventuallyPointwiseLt h g ->
      exists i, F.eventuallyLe h (d i)

/-- The family has a strict upper bound which itself lies strictly below `g`. -/
def IsPointwiseStrictBoundedBelow
    {ι : Type w}
    (d : ι -> ProductElement F)
    (g : ProductElement F) : Prop :=
  exists h : ProductElement F,
    F.IsPointwiseStrictUpperBound d h /\
      F.eventuallyPointwiseLt h g

/-- `g` is a strict upper bound and the family is cofinal among elements below it. -/
def IsPointwiseStrictExactUpperBound
    {ι : Type w}
    (d : ι -> ProductElement F)
    (g : ProductElement F) : Prop :=
  F.IsPointwiseStrictUpperBound d g /\
    F.IsPointwiseStrictCofinalBelow d g

theorem IsPointwiseStrictExactUpperBound.isUpperBound
    {ι : Type w}
    {d : ι -> ProductElement F}
    {g : ProductElement F}
    (h : F.IsPointwiseStrictExactUpperBound d g) :
    F.IsPointwiseStrictUpperBound d g :=
  h.1

theorem IsPointwiseStrictExactUpperBound.cofinalBelow
    {ι : Type w}
    {d : ι -> ProductElement F}
    {g : ProductElement F}
    (h : F.IsPointwiseStrictExactUpperBound d g) :
    F.IsPointwiseStrictCofinalBelow d g :=
  h.2

#print axioms
  ReducedProductFrame.IsPointwiseStrictExactUpperBound.isUpperBound
#print axioms
  ReducedProductFrame.IsPointwiseStrictExactUpperBound.cofinalBelow

theorem eventuallyPointwiseLt_withLargerIdeal
    {x y : ProductElement F}
    (J : Ideal F.Index)
    (hLe : Ideal.Le F.J J)
    (hxy : F.eventuallyPointwiseLt x y) :
    (F.withIdeal J).eventuallyPointwiseLt x y :=
  hLe _ hxy

#print axioms
  ReducedProductFrame.eventuallyPointwiseLt_withLargerIdeal

/-! An exact upper bound remains exact after localizing the ideal to any
predicate.  To test local cofinality, splice the local test function with one
fixed member of the family outside the predicate, apply global exactness, and
then restrict the resulting domination back to the predicate. -/
theorem IsPointwiseStrictExactUpperBound.localize
    {ι : Type w}
    {d : ι -> ProductElement F}
    {g : ProductElement F}
    (hExact : F.IsPointwiseStrictExactUpperBound d g)
    (i0 : ι)
    (X : F.Index -> Prop) :
    (F.withIdeal (F.J.localize X)).IsPointwiseStrictExactUpperBound d g := by
  classical
  constructor
  · intro i
    exact F.eventuallyPointwiseLt_withLargerIdeal
      (F.J.localize X) (F.J.le_localize X)
      (IsPointwiseStrictExactUpperBound.isUpperBound F hExact i)
  · intro h hh
    let h' : ProductElement F := fun k =>
      if X k then h k else d i0 k
    have hh' : F.eventuallyPointwiseLt h' g := by
      change F.J.Small (fun k => Not
        (F.le k (h' k) (g k) /\ Not (F.le k (g k) (h' k))))
      have hhX : F.J.Small (fun k =>
          Not (F.le k (h k) (g k) /\ Not (F.le k (g k) (h k))) /\ X k) :=
        hh
      have hd0 : F.J.Small (fun k => Not
          (F.le k (d i0 k) (g k) /\ Not (F.le k (g k) (d i0 k)))) :=
        IsPointwiseStrictExactUpperBound.isUpperBound F hExact i0
      exact F.J.subset_small (F.J.union_small hhX hd0) (by
        intro k hk
        by_cases hkX : X k
        · left
          refine ⟨?_, hkX⟩
          simpa only [h', if_pos hkX] using hk
        · right
          simpa only [h', if_neg hkX] using hk)
    obtain ⟨i, hi⟩ :=
      IsPointwiseStrictExactUpperBound.cofinalBelow F hExact h' hh'
    refine ⟨i, ?_⟩
    change F.J.Small (fun k => Not (F.le k (h k) (d i k)) /\ X k)
    exact F.J.subset_small hi (by
      intro k hk
      have : Not (F.le k (h' k) (d i k)) := by
        simpa only [h', if_pos hk.2] using hk.1
      exact this)

#print axioms
  ReducedProductFrame.IsPointwiseStrictExactUpperBound.localize

/-! If `f` is exact and another bound `g` is eventually below `f`, then the
family is cofinal below `g`.  A test function strictly below `g` is strictly
below `f` by transitivity, so exactness applies. -/
theorem IsPointwiseStrictExactUpperBound.cofinalBelow_of_eventuallyLe
    {ι : Type w}
    {d : ι -> ProductElement F}
    {f g : ProductElement F}
    (hExact : F.IsPointwiseStrictExactUpperBound d f)
    (hgf : F.eventuallyLe g f) :
    F.IsPointwiseStrictCofinalBelow d g := by
  intro h hhg
  apply IsPointwiseStrictExactUpperBound.cofinalBelow F hExact h
  exact F.J.eventually_mono (F.J.eventually_and hhg hgf) (by
    intro k hk
    refine ⟨F.le_trans k hk.1.1 hk.2, ?_⟩
    intro hfh
    exact hk.1.2 (F.le_trans k hk.2 hfh))

#print axioms
  ReducedProductFrame.IsPointwiseStrictExactUpperBound.cofinalBelow_of_eventuallyLe

/-! Exact-upper-bound decomposition (the order-theoretic content of Jech
24.11).  With coordinatewise total comparison, an exact upper bound `f`
relative to a comparison function `g` yields either a bound strictly below
`g`, cofinality below `g`, or a partition into two positive localized ideals
carrying those two alternatives separately. -/
theorem exactUpperBound_bounded_or_cofinal_or_localized_split
    (hTotal : forall (k : F.Index) (x y : F.Coord k),
      F.le k x y \/ F.le k y x)
    {ι : Type w}
    {d : ι -> ProductElement F}
    {f g : ProductElement F}
    (i0 : ι)
    (hExact : F.IsPointwiseStrictExactUpperBound d f) :
    F.IsPointwiseStrictBoundedBelow d g \/
      F.IsPointwiseStrictCofinalBelow d g \/
      exists X : F.Index -> Prop,
        (F.J.localize X).IsProper /\
        (F.J.localize (fun k => Not (X k))).IsProper /\
        (F.withIdeal (F.J.localize X)).IsPointwiseStrictBoundedBelow d g /\
        IsPointwiseStrictCofinalBelow
          (F.withIdeal (F.J.localize (fun k => Not (X k)))) d g := by
  classical
  let X : F.Index -> Prop := fun k =>
    F.le k (f k) (g k) /\ Not (F.le k (g k) (f k))
  by_cases hXSmall : F.J.Small X
  · right
    left
    apply hExact.cofinalBelow_of_eventuallyLe
    exact F.J.subset_small hXSmall (by
      intro k hgf
      exact ⟨(hTotal k (f k) (g k)).resolve_right hgf, hgf⟩)
  · by_cases hComplSmall : F.J.Small (fun k => Not (X k))
    · left
      exact ⟨f, hExact.isUpperBound, hComplSmall⟩
    · right
      right
      refine ⟨X, (F.J.localize_isProper_iff X).mpr hXSmall,
        (F.J.localize_isProper_iff (fun k => Not (X k))).mpr hComplSmall,
        ?_, ?_⟩
      · refine ⟨f,
          IsPointwiseStrictExactUpperBound.isUpperBound
            (F.withIdeal (F.J.localize X))
            (IsPointwiseStrictExactUpperBound.localize F hExact i0 X), ?_⟩
        change F.J.Small (fun k => Not (X k) /\ X k)
        exact F.J.subset_small F.J.empty_small (by
          intro k hk
          exact hk.1 hk.2)
      · apply
          IsPointwiseStrictExactUpperBound.cofinalBelow_of_eventuallyLe
            (F.withIdeal (F.J.localize (fun k => Not (X k))))
            (IsPointwiseStrictExactUpperBound.localize F hExact i0
              (fun k => Not (X k)))
        change F.J.Small (fun k =>
          Not (F.le k (g k) (f k)) /\ Not (X k))
        exact F.J.subset_small F.J.empty_small (by
          intro k hk
          apply hk.1
          by_cases hgf : F.le k (g k) (f k)
          · exact hgf
          · exact False.elim (hk.2
              ⟨(hTotal k (f k) (g k)).resolve_right hgf, hgf⟩))

#print axioms
  ReducedProductFrame.exactUpperBound_bounded_or_cofinal_or_localized_split

/-! A finitely compatible family of coordinatewise comparison sets can be
    defeated in one ultrafilter-dual extension of the frame's ideal.  The
    compactness/Zorn construction lives in `IdealProduct`; here its fixed
    witness `g` directly refutes reduced-product cofinality. -/
theorem exists_ultrafilterDual_ideal_not_isCofinalFamily
    {K : Type w}
    (d : K -> ProductElement F)
    (g : ProductElement F)
    (hCompatible : forall s : Finset K,
      (F.J.extendBy (finitePredicateUnion
        (fun k i => F.le i (g i) (d k i)) s)).IsProper) :
    exists J : Ideal F.Index,
      J.IsUltrafilterDual /\
        Ideal.Le F.J J /\
        Not ((F.withIdeal J).IsCofinalFamily d) := by
  obtain ⟨J, hUltra, hLe, hAvoid⟩ :=
    F.exists_ultrafilterDual_ideal_avoiding_eventuallyLe_family
      d g hCompatible
  refine ⟨J, hUltra, hLe, ?_⟩
  intro hCofinal
  obtain ⟨k, hgk⟩ := hCofinal g
  exact hAvoid k hgk

/-! With the finite-set ideal as the base, the chosen ultrafilter-dual ideal
    is nonprincipal as well as defeating the proposed cofinal family.  This
    is the reduced-product compactness form used on countable PCF cores. -/
theorem exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily
    [Infinite F.Index]
    {K : Type w}
    (d : K -> ProductElement F)
    (g : ProductElement F)
    (hCompatible : forall s : Finset K,
      ((Ideal.finiteSet F.Index).extendBy
        (finitePredicateUnion
          (fun k i => F.le i (g i) (d k i)) s)).IsProper) :
    exists J : Ideal F.Index,
      J.IsUltrafilterDual /\
        (forall i, Not (J = Ideal.excludePoint i)) /\
        Not ((F.withIdeal J).IsCofinalFamily d) := by
  obtain ⟨J, hUltra, hNonprincipal, hAvoid⟩ :=
    exists_nonprincipal_ultrafilterDual_ideal_avoiding_eventual_family
      (fun k i => F.le i (g i) (d k i)) hCompatible
  refine ⟨J, hUltra, hNonprincipal, ?_⟩
  intro hCofinal
  obtain ⟨k, hgk⟩ := hCofinal g
  exact hAvoid k (by
    simpa only [withIdeal, eventuallyLe] using hgk)

/-! The compactness step behind Jech's pointwise-cofinal-family lemma.
    If one fixed family is cofinal modulo every ultrafilter-dual ideal, then
    every product element is coordinatewise covered by finitely many members
    of that family.  In a coordinatewise linear order, taking their finite
    pointwise maximum gives the usual formulation of the lemma.

    The proof is a genuine ultrafilter argument: failure of a finite
    coordinatewise cover makes every finite family of comparison predicates
    compatible with the least ideal.  The ultrafilter-extension theorem then
    produces a quotient in which the proposed family is not cofinal. -/
theorem exists_finset_pointwise_cover_of_forall_ultrafilterDual_isCofinalFamily
    {K : Type w}
    (d : K -> ProductElement F)
    (hCofinal : forall J : Ideal F.Index,
      J.IsUltrafilterDual ->
        (F.withIdeal J).IsCofinalFamily d) :
    forall g : ProductElement F,
      exists s : Finset K,
        forall i,
          finitePredicateUnion
            (fun k i => F.le i (g i) (d k i)) s i := by
  classical
  intro g
  by_contra hNoCover
  push Not at hNoCover
  let F0 : ReducedProductFrame.{u, v} :=
    F.withIdeal (Ideal.emptyOnly F.Index)
  have hCompatible : forall s : Finset K,
      (F0.J.extendBy (finitePredicateUnion
        (fun k i => F0.le i (g i) (d k i)) s)).IsProper := by
    intro s
    rw [Ideal.extendBy_isProper_iff_not_eventually]
    intro hEventually
    obtain ⟨i, hi⟩ := hNoCover s
    apply hi
    apply Classical.byContradiction
    exact hEventually i
  obtain ⟨J, hUltra, _hLe, hNotCofinal⟩ :=
    F0.exists_ultrafilterDual_ideal_not_isCofinalFamily d g hCompatible
  exact hNotCofinal (hCofinal J hUltra)

#print axioms
  ReducedProductFrame.exists_ultrafilterDual_ideal_not_isCofinalFamily
#print axioms
  ReducedProductFrame.exists_nonprincipal_ultrafilterDual_ideal_not_isCofinalFamily
#print axioms
  ReducedProductFrame.exists_finset_pointwise_cover_of_forall_ultrafilterDual_isCofinalFamily

end ReducedProductFrame

/-- A type equipped with a specified well-order, used to index a scale. -/
structure ScaleLength where
  Level : Type w
  lt : Level -> Level -> Prop
  isWellOrder : IsWellOrder Level lt

/-- An increasing family cofinal in the eventual preorder of a reduced product. -/
structure Scale
    (F : ReducedProductFrame.{u, v})
    (L : ScaleLength.{w}) where
  seq : L.Level -> ProductElement F
  increasing :
    forall {alpha beta}, L.lt alpha beta ->
      F.eventuallyLt (seq alpha) (seq beta)
  cofinal :
    forall g : ProductElement F,
      exists alpha, F.eventuallyLe g (seq alpha)

/-! A scale whose strict comparisons hold on an eventual set coordinate by
coordinate. This is the source meaning of `<_I` that is stable when the ideal
is enlarged; it is stronger than asymmetry of the reduced-product preorder
for a non-maximal ideal. -/
structure PointwiseStrictScale
    (F : ReducedProductFrame.{u, v})
    (L : ScaleLength.{w}) where
  seq : L.Level -> ProductElement F
  increasing :
    forall {alpha beta}, L.lt alpha beta ->
      F.J.Eventually (fun i =>
        F.le i (seq alpha i) (seq beta i) /\
          Not (F.le i (seq beta i) (seq alpha i)))
  cofinal :
    forall g : ProductElement F,
      exists alpha, F.eventuallyLe g (seq alpha)

/-! A strict chain constructed above a prescribed family.  Unlike a scale,
it need not be cofinal; its `dominates` field is the ingredient used to turn
an unbounded family into an unbounded increasing sequence in the proof of
Jech 24.12. -/
structure PointwiseStrictDominatingSequence
    (F : ReducedProductFrame.{u, v})
    (L : ScaleLength.{w})
    (d : L.Level -> ProductElement F) where
  seq : L.Level -> ProductElement F
  increasing :
    forall {alpha beta}, L.lt alpha beta ->
      F.eventuallyPointwiseLt (seq alpha) (seq beta)
  dominates :
    forall alpha, F.eventuallyPointwiseLt (d alpha) (seq alpha)

/-! `F` is pointwise-strictly directed below `theta` when every family whose
index cardinal is smaller than `theta` has one common source-level strict
upper bound.  This is the exact directedness input used by the recursive
scale construction, not an assertion that such bounds exist. -/
def ReducedProductFrame.PointwiseStrictDirectedBelow
    (F : ReducedProductFrame.{u, v})
    (theta : Cardinal.{w}) : Prop :=
  forall (ι : Type w), Cardinal.mk ι < theta ->
    forall d : ι -> ProductElement F,
      exists g : ProductElement F,
        forall i, F.eventuallyPointwiseLt (d i) g

theorem ReducedProductFrame.PointwiseStrictDirectedBelow.withLargerIdeal
    {F : ReducedProductFrame.{u, v}}
    {theta : Cardinal.{w}}
    (hDirected : F.PointwiseStrictDirectedBelow theta)
    (J : Ideal F.Index)
    (hLe : Ideal.Le F.J J) :
    (F.withIdeal J).PointwiseStrictDirectedBelow theta := by
  intro iota hSmall d
  obtain ⟨g, hg⟩ := hDirected iota hSmall d
  refine ⟨g, ?_⟩
  intro i
  exact F.eventuallyPointwiseLt_withLargerIdeal J hLe (hg i)

#print axioms
  ReducedProductFrame.PointwiseStrictDirectedBelow.withLargerIdeal

theorem ReducedProductFrame.eventuallyLt_of_eventually_pointwiseStrict
    {F : ReducedProductFrame.{u, v}}
    (hProper : F.J.IsProper)
    {x y : ProductElement F}
    (hStrict : F.J.Eventually (fun i =>
      F.le i (x i) (y i) /\ Not (F.le i (y i) (x i)))) :
    F.eventuallyLt x y := by
  refine ⟨F.J.eventually_mono hStrict (fun _ hi => hi.1), ?_⟩
  intro hReverse
  have hBoth := F.J.eventually_and hStrict hReverse
  have hFalse : F.J.Eventually (fun _ => False) :=
    F.J.eventually_mono hBoth (by
      intro i hi
      exact hi.1.2 hi.2)
  exact hProper.not_eventually_false hFalse

#print axioms
  ReducedProductFrame.eventuallyLt_of_eventually_pointwiseStrict

namespace PointwiseStrictScale

variable {F : ReducedProductFrame.{u, v}} {L : ScaleLength.{w}}

/-! A pointwise-strict cofinal scale over a proper ideal cannot have one
common pointwise-strict upper bound. -/
theorem not_exists_pointwiseStrictUpperBound
    (s : PointwiseStrictScale F L)
    (hProper : F.J.IsProper) :
    Not (exists p : ProductElement F,
      F.IsPointwiseStrictUpperBound s.seq p) := by
  intro hBound
  obtain ⟨p, hp⟩ := hBound
  obtain ⟨alpha, hpa⟩ := s.cofinal p
  have hBoth := F.J.eventually_and hpa (hp alpha)
  have hFalse : F.J.Eventually (fun _ => False) :=
    F.J.eventually_mono hBoth (by
      intro i hi
      exact hi.2.2 hi.1)
  exact hProper.not_eventually_false hFalse

#print axioms
  PointwiseStrictScale.not_exists_pointwiseStrictUpperBound

/-! Forgetting pointwise strictness gives an ordinary scale whenever the
underlying ideal is proper. -/
def toScale
    (s : PointwiseStrictScale F L)
    (hProper : F.J.IsProper) : Scale F L where
  seq := s.seq
  increasing := fun h =>
    F.eventuallyLt_of_eventually_pointwiseStrict hProper (s.increasing h)
  cofinal := s.cofinal

/-! A pointwise-strict scale survives enlargement of its ideal. Coordinates
and functions are definitionally unchanged by `withIdeal`; only eventual
sets are transported by the ideal inclusion. -/
def withLargerIdeal
    (s : PointwiseStrictScale F L)
    (J : Ideal F.Index)
    (hLe : Ideal.Le F.J J) :
    PointwiseStrictScale (F.withIdeal J) L where
  seq := s.seq
  increasing := fun h => hLe _ (s.increasing h)
  cofinal := by
    intro g
    obtain ⟨alpha, hAlpha⟩ := s.cofinal g
    exact ⟨alpha, hLe _ hAlpha⟩

end PointwiseStrictScale

/-- The weak assertion that a scale of the specified length exists. -/
def HasScaleWitness
    (F : ReducedProductFrame.{u, v})
    (L : ScaleLength.{w}) : Prop :=
  Nonempty (Scale F L)

/-- The reduced product has true cofinality represented by `L`: a scale of
that length exists, and no cofinal family indexed by a smaller type exists. -/
def HasTrueCofinality
    (F : ReducedProductFrame.{u, v})
    (L : ScaleLength.{w}) : Prop :=
  HasScaleWitness F L /\
    forall (ι : Type w) (d : ι -> ProductElement F),
      F.IsCofinalFamily d ->
        Cardinal.mk L.Level <= Cardinal.mk ι

namespace HasTrueCofinality

variable {F : ReducedProductFrame.{u, v}} {L : ScaleLength.{w}}

theorem hasScaleWitness
    (h : HasTrueCofinality F L) :
    HasScaleWitness F L :=
  h.1

theorem cardinal_le_of_cofinalFamily
    (h : HasTrueCofinality F L)
    {ι : Type w}
    (d : ι -> ProductElement F)
    (hCofinal : F.IsCofinalFamily d) :
    Cardinal.mk L.Level <= Cardinal.mk ι :=
  h.2 ι d hCofinal

end HasTrueCofinality

namespace Scale

variable {F : ReducedProductFrame.{u, v}} {L : ScaleLength.{w}}

theorem eventuallyLe_of_lt
    (s : Scale F L)
    {alpha beta : L.Level}
    (h : L.lt alpha beta) :
    F.eventuallyLe (s.seq alpha) (s.seq beta) :=
  (s.increasing h).left

theorem not_eventuallyLe_of_lt
    (s : Scale F L)
    {alpha beta : L.Level}
    (h : L.lt alpha beta) :
    Not (F.eventuallyLe (s.seq beta) (s.seq alpha)) :=
  (s.increasing h).right

theorem isCofinalFamily_seq
    (s : Scale F L) :
    F.IsCofinalFamily s.seq :=
  s.cofinal

theorem hasScaleWitness
    (s : Scale F L) :
    HasScaleWitness F L :=
  Nonempty.intro s

end Scale

theorem cardinal_mk_level_eq_of_hasTrueCofinality
    {F : ReducedProductFrame.{u, v}}
    {L M : ScaleLength.{w}}
    (hL : HasTrueCofinality F L)
    (hM : HasTrueCofinality F M) :
    Cardinal.mk L.Level = Cardinal.mk M.Level := by
  apply le_antisymm
  · obtain ⟨s⟩ := hM.hasScaleWitness
    exact hL.cardinal_le_of_cofinalFamily
      s.seq s.isCofinalFamily_seq
  · obtain ⟨s⟩ := hL.hasScaleWitness
    exact hM.cardinal_le_of_cofinalFamily
      s.seq s.isCofinalFamily_seq

end PcfProject
