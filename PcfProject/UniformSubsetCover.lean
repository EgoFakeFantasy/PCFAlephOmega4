import PcfProject.PcfPointwiseCover
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-!
# Uniform downward covers of fixed-size subsets

This module formalizes the cardinal-combinatorial core of Jech's Lemma
24.23.  The first step says that when `mu` is infinite regular and the
cofinality of a well-order is not `mu`, every `mu`-sized subset has a bounded
subsubset of the same size.  The two cases are the standard cofinality split:
either the whole set is bounded, or infinite pigeonhole supplies one large
fiber below a member of a small cofinal set.
-/

open Cardinal Set
open scoped Cardinal

namespace PcfProject

universe u

/-- A family of `mu`-sized subsets which is downward cofinal among all
`mu`-sized subsets of a type. -/
structure UniformSubsetCover (α : Type u) (mu : Cardinal.{u}) where
  Index : Type u
  member : Index -> Set α
  index_cardinal : Cardinal.mk Index <= max ((2 : Cardinal.{u}) ^ mu) (Cardinal.mk α)
  member_cardinal : forall i, Cardinal.mk (member i) = mu
  downward_cofinal : forall Z : Set α, Cardinal.mk Z = mu ->
    exists i, member i ⊆ Z

namespace UniformSubsetCover

/-- Transport a uniform subset cover along a bijection of its ground type. -/
def mapEquiv
    {α β : Type u}
    {mu : Cardinal.{u}}
    (C : UniformSubsetCover α mu)
    (e : α ≃ β) :
    UniformSubsetCover β mu where
  Index := C.Index
  member := fun i => e '' C.member i
  index_cardinal := by
    simpa only [Cardinal.mk_congr e] using C.index_cardinal
  member_cardinal := by
    intro i
    rw [Cardinal.mk_image_eq e.injective]
    exact C.member_cardinal i
  downward_cofinal := by
    intro Z hZ
    have hPreimage : Cardinal.mk (e ⁻¹' Z) = mu := by
      rw [Cardinal.mk_preimage_equiv e Z, hZ]
    obtain ⟨i, hi⟩ := C.downward_cofinal (e ⁻¹' Z) hPreimage
    refine ⟨i, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hi hx

end UniformSubsetCover

/-! The bounded-subset dichotomy used at every non-base stage of the
transfinite construction. -/
theorem exists_bounded_subset_mk_eq_of_isRegular_of_cof_ne
    {α : Type u}
    [LinearOrder α]
    {mu : Cardinal.{u}}
    (hMu : Cardinal.IsRegular mu)
    {Z : Set α}
    (hZ : Cardinal.mk Z = mu)
    (hCofNe : Order.cof α ≠ mu) :
    exists b : α, exists X : Set α,
      X ⊆ Z /\ Cardinal.mk X = mu /\ forall x, x ∈ X -> x <= b := by
  rcases lt_or_gt_of_ne hCofNe with hCofMu | hMuCof
  · obtain ⟨C, hCofinal, hCCard⟩ := Order.exists_cof_eq α
    let chooseBound : Z -> C := fun z =>
      ⟨Classical.choose (hCofinal z.1),
        (Classical.choose_spec (hCofinal z.1)).1⟩
    have chooseBound_spec : forall z : Z, z.1 <= (chooseBound z).1 := by
      intro z
      exact (Classical.choose_spec (hCofinal z.1)).2
    obtain ⟨c, X, hXZ, hXCardLower, hFiber⟩ :=
      Cardinal.infinite_pigeonhole_set
        chooseBound mu hZ.ge hMu.aleph0_le (by
          rw [hCCard, hMu.cof_ord]
          exact hCofMu)
    have hXCard : Cardinal.mk X = mu := by
      apply le_antisymm
      · exact (Cardinal.mk_le_mk_of_subset hXZ).trans_eq hZ
      · exact hXCardLower
    refine ⟨c.1, X, hXZ, hXCard, ?_⟩
    intro x hx
    let z : Z := ⟨x, hXZ hx⟩
    have hEq : chooseBound z = c := hFiber hx
    simpa only [z, hEq] using chooseBound_spec z
  · have hNotCofinal : Not (IsCofinal Z) := by
      intro hZCofinal
      have hLe : Order.cof α <= Cardinal.mk Z := Order.cof_le hZCofinal
      exact (not_le_of_gt hMuCof) (hZ ▸ hLe)
    obtain ⟨b, hb⟩ := not_isCofinal_iff.mp hNotCofinal
    exact ⟨b, Z, Subset.rfl, hZ, fun x hx => (hb x hx).le⟩

/-! At cardinality at most `2^mu`, all injectively enumerated `mu`-sets form
a sufficiently small downward cover. -/
noncomputable def uniformSubsetCoverOfMkLeTwoPower
    (α : Type u)
    {mu : Cardinal.{u}}
    (hMu : Cardinal.IsRegular mu)
    (hAlpha : Cardinal.mk α <= (2 : Cardinal.{u}) ^ mu) :
    UniformSubsetCover α mu where
  Index := mu.out ↪ α
  member := fun e => Set.range e
  index_cardinal := by
    calc
      Cardinal.mk (mu.out ↪ α) <= Cardinal.mk (mu.out -> α) :=
        Cardinal.mk_embedding_le_arrow _ _
      _ = Cardinal.mk α ^ mu := by
        simp only [Cardinal.mk_arrow, Cardinal.mk_out, Cardinal.lift_id]
      _ <= ((2 : Cardinal.{u}) ^ mu) ^ mu :=
        Cardinal.power_le_power_right hAlpha
      _ = (2 : Cardinal.{u}) ^ mu := by
        rw [← Cardinal.power_mul, Cardinal.mul_eq_self hMu.aleph0_le]
      _ <= max ((2 : Cardinal.{u}) ^ mu) (Cardinal.mk α) :=
        le_max_left _ _
  member_cardinal := by
    intro e
    rw [Cardinal.mk_range_eq e e.injective, Cardinal.mk_out]
  downward_cofinal := by
    intro Z hZ
    have hEq : Cardinal.mk mu.out = Cardinal.mk Z := by
      rw [Cardinal.mk_out, hZ]
    let eZ : mu.out ≃ Z := Classical.choice (Cardinal.eq.mp hEq)
    let e : mu.out ↪ α :=
      eZ.toEmbedding.trans (Function.Embedding.subtype fun x : α => x ∈ Z)
    refine ⟨e, ?_⟩
    intro x hx
    obtain ⟨a, ha⟩ := hx
    rw [← ha]
    exact (eZ a).2

/-! Assemble covers of all proper initial-cardinal segments into a cover of
one larger initial ordinal.  The cofinality hypothesis supplies a bounded
`mu`-subsubset, which is then handled by the corresponding smaller cover. -/
noncomputable def uniformSubsetCoverOfSmaller
    {mu alpha : Cardinal.{u}}
    (hMu : Cardinal.IsRegular mu)
    (hPowerAlpha : (2 : Cardinal.{u}) ^ mu < alpha)
    (hCofNe : Order.cof alpha.ord.ToType ≠ mu)
    (C : forall gamma : Cardinal.{u}, gamma < alpha ->
      UniformSubsetCover gamma.ord.ToType mu) :
    UniformSubsetCover alpha.ord.ToType mu := by
  let T := alpha.ord.ToType
  let gamma : T -> Cardinal.{u} := fun b => Cardinal.mk (Set.Iic b)
  have hAlphaInfinite : Cardinal.aleph0 <= alpha :=
    hMu.aleph0_le.trans (by
      exact le_trans (Cardinal.cantor _).le hPowerAlpha.le)
  have hGamma : forall b : T, gamma b < alpha := by
    have hMkT : Cardinal.mk T = alpha := by
      dsimp only [T]
      exact Cardinal.mk_ord_toType alpha
    have hTypeT : (Cardinal.mk T).ord =
        Ordinal.type (fun x y : T => x < y) := by
      rw [hMkT]
      change alpha.ord = Ordinal.type
        (fun x y : alpha.ord.ToType => x < y)
      exact (Ordinal.type_toType alpha.ord).symm
    have hInfiniteT : Cardinal.aleph0 <= Cardinal.mk T := by
      rw [hMkT]
      exact hAlphaInfinite
    intro b
    have hb := Cardinal.mk_Iic_lt b hTypeT hInfiniteT
    dsimp only [gamma]
    rw [hMkT] at hb
    exact hb
  let smaller : forall b : T,
      UniformSubsetCover (gamma b).ord.ToType mu := fun b =>
    C (gamma b) (hGamma b)
  let segmentEquiv : forall b : T,
      (gamma b).ord.ToType ≃ Set.Iic b := fun b =>
    Classical.choice (Cardinal.eq.mp (by
      simp only [Cardinal.mk_ord_toType, gamma]))
  let segmentEmbedding : forall b : T,
      (gamma b).ord.ToType ↪ T := fun b =>
    (segmentEquiv b).toEmbedding.trans
      (Function.Embedding.subtype fun x : T => x <= b)
  exact {
    Index := Sigma fun b : T => (smaller b).Index
    member := fun z =>
      segmentEmbedding z.1 '' (smaller z.1).member z.2
    index_cardinal := by
      rw [Cardinal.mk_sigma]
      calc
        Cardinal.sum (fun b : T => Cardinal.mk (smaller b).Index) <=
            Cardinal.mk T *
              ⨆ b : T, Cardinal.mk (smaller b).Index :=
          Cardinal.sum_le_mk_mul_iSup _
        _ <= alpha * alpha := by
          apply mul_le_mul'
          · dsimp only [T]
            rw [Cardinal.mk_ord_toType]
          · apply ciSup_le'
            intro b
            have hIndex := (smaller b).index_cardinal
            rw [Cardinal.mk_ord_toType] at hIndex
            exact hIndex.trans (max_le hPowerAlpha.le (hGamma b).le)
        _ = alpha := Cardinal.mul_eq_self hAlphaInfinite
        _ <= max ((2 : Cardinal.{u}) ^ mu)
            (Cardinal.mk alpha.ord.ToType) := by
          rw [Cardinal.mk_ord_toType]
          exact le_max_right _ _
    member_cardinal := by
      intro z
      rw [Cardinal.mk_image_eq (segmentEmbedding z.1).injective]
      exact (smaller z.1).member_cardinal z.2
    downward_cofinal := by
      intro Z hZ
      obtain ⟨b, X, hXZ, hXCard, hXBound⟩ :=
        exists_bounded_subset_mk_eq_of_isRegular_of_cof_ne
          hMu hZ hCofNe
      have hXRange : X ⊆ Set.range (segmentEmbedding b) := by
        intro x hx
        let xb : Set.Iic b := ⟨x, hXBound x hx⟩
        refine ⟨(segmentEquiv b).symm xb, ?_⟩
        change ((segmentEquiv b) ((segmentEquiv b).symm xb)).1 = x
        rw [(segmentEquiv b).apply_symm_apply]
      have hPreimageCard :
          Cardinal.mk (segmentEmbedding b ⁻¹' X) = mu := by
        rw [Cardinal.mk_preimage_of_injective_of_subset_range
          (segmentEmbedding b) X (segmentEmbedding b).injective hXRange,
          hXCard]
      obtain ⟨i, hi⟩ :=
        (smaller b).downward_cofinal
          (segmentEmbedding b ⁻¹' X) hPreimageCard
      refine ⟨⟨b, i⟩, ?_⟩
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hXZ (hi hx)
  }

theorem orderCof_cardinalOrdToType
    (alpha : Cardinal.{u}) :
    Order.cof alpha.ord.ToType = alpha.ord.cof := by
  rw [← Ordinal.cof_type, Ordinal.type_toType]

/-! Jech 24.23 with its cofinality avoidance premise exposed.  Strong
induction on the ambient cardinal uses the all-embeddings cover below
`2^mu`, and the bounded-subset assembly above at every larger stage. -/
theorem nonempty_uniformSubsetCover_of_no_equal_cofinality
    {mu bound alpha : Cardinal.{u}}
    (hMu : Cardinal.IsRegular mu)
    (hAlphaBound : alpha <= bound)
    (hNoCof : forall gamma : Cardinal.{u},
      (2 : Cardinal.{u}) ^ mu < gamma -> gamma <= bound ->
        gamma.ord.cof ≠ mu) :
    Nonempty (UniformSubsetCover alpha.ord.ToType mu) := by
  induction alpha using Cardinal.lt_wf.induction with
  | h alpha ih =>
      by_cases hSmall : alpha <= (2 : Cardinal.{u}) ^ mu
      · exact ⟨uniformSubsetCoverOfMkLeTwoPower
          alpha.ord.ToType hMu (by
            rw [Cardinal.mk_ord_toType]
            exact hSmall)⟩
      · have hPowerAlpha : (2 : Cardinal.{u}) ^ mu < alpha :=
          lt_of_not_ge hSmall
        have hCofNe : Order.cof alpha.ord.ToType ≠ mu := by
          rw [orderCof_cardinalOrdToType]
          exact hNoCof alpha hPowerAlpha hAlphaBound
        let smaller : forall gamma : Cardinal.{u}, gamma < alpha ->
            UniformSubsetCover gamma.ord.ToType mu := fun gamma hGamma =>
          Classical.choice (ih gamma hGamma
            (hGamma.le.trans hAlphaBound))
        exact ⟨uniformSubsetCoverOfSmaller
          hMu hPowerAlpha hCofNe smaller⟩

noncomputable def uniformSubsetCoverOfNoEqualCofinality
    {mu bound alpha : Cardinal.{u}}
    (hMu : Cardinal.IsRegular mu)
    (hAlphaBound : alpha <= bound)
    (hNoCof : forall gamma : Cardinal.{u},
      (2 : Cardinal.{u}) ^ mu < gamma -> gamma <= bound ->
        gamma.ord.cof ≠ mu) :
    UniformSubsetCover alpha.ord.ToType mu :=
  Classical.choice
    (nonempty_uniformSubsetCover_of_no_equal_cofinality
      hMu hAlphaBound hNoCof)

/-! No cardinal strictly between `2^mu` and `aleph_(mu.ord)` can have
cofinality `mu`.  If such a cardinal is `aleph_delta`, the strict lower
bound rules out zero and successor `delta`; normality of `omega_delta` at a
limit then gives `mu <= |delta|`, contradicting the strict upper bound. -/
theorem cardinal_ord_cof_ne_of_two_power_lt_of_lt_aleph
    {mu gamma : Cardinal.{u}}
    (hMu : Cardinal.IsRegular mu)
    (hPower : (2 : Cardinal.{u}) ^ mu < gamma)
    (hUpper : gamma < Cardinal.aleph mu.ord) :
    gamma.ord.cof ≠ mu := by
  intro hCof
  have hMuGamma : mu < gamma :=
    (Cardinal.cantor mu).trans hPower
  have hGammaInfinite : Cardinal.aleph0 <= gamma :=
    hMu.aleph0_le.trans hMuGamma.le
  obtain ⟨delta, hDelta⟩ :=
    Cardinal.mem_range_aleph_iff.mpr hGammaInfinite
  rcases Ordinal.zero_or_succ_or_isSuccLimit delta with
      hZero | hSucc | hLimit
  · rw [hZero, Cardinal.aleph_zero] at hDelta
    exact (not_lt_of_ge hMu.aleph0_le) (hDelta ▸ hMuGamma)
  · obtain ⟨eta, hEta⟩ := hSucc
    have hGammaRegular : Cardinal.IsRegular gamma := by
      rw [← hDelta, ← hEta]
      simpa only [Order.succ_eq_add_one] using
        Cardinal.isRegular_aleph_add_one eta
    have hMuEqGamma : mu = gamma := by
      rw [← hCof, hGammaRegular.cof_ord]
    exact (ne_of_lt hMuGamma) hMuEqGamma
  · have hMuLeDeltaCard : mu <= delta.card := by
      have hMuEqDeltaCof : mu = delta.cof := by
        calc
          mu = gamma.ord.cof := hCof.symm
          _ = (Cardinal.aleph delta).ord.cof := by rw [hDelta]
          _ = (Ordinal.omega delta).cof := by
            rw [Cardinal.ord_aleph]
          _ = delta.cof :=
            Ordinal.cof_map_of_isNormal Ordinal.isNormal_omega hLimit
      rw [hMuEqDeltaCof]
      exact Ordinal.cof_le_card delta
    have hMuOrdLeDelta : mu.ord <= delta :=
      (Cardinal.ord_le_ord.mpr hMuLeDeltaCard).trans
        (Cardinal.ord_card_le delta)
    have hAlephLeGamma : Cardinal.aleph mu.ord <= gamma := by
      rw [← hDelta]
      exact Cardinal.aleph.monotone hMuOrdLeDelta
    exact (not_lt_of_ge hAlephLeGamma) hUpper

/-! Source form of Jech 24.23: below `aleph_(mu.ord)` the cofinality
avoidance condition is automatic. -/
noncomputable def uniformSubsetCoverOfLtAleph
    {mu alpha : Cardinal.{u}}
    (hMu : Cardinal.IsRegular mu)
    (hAlpha : alpha < Cardinal.aleph mu.ord) :
    UniformSubsetCover alpha.ord.ToType mu :=
  uniformSubsetCoverOfNoEqualCofinality (bound := alpha) hMu le_rfl
    (fun _gamma hPower hGamma =>
      cardinal_ord_cof_ne_of_two_power_lt_of_lt_aleph
        hMu hPower (hGamma.trans_lt hAlpha))

/-! Abstract final compression pattern of the proof of Theorem 24.18.
`witness a` is the `mu`-sized set of dominating functions attached to a
countable set `a`; any `mu`-sized subfamily determines its characteristic.
Lemma 24.23 then supplies a small injective code for all countable sets. -/
structure UniformSubsetCharacteristicCoding
    (A K Characteristic : Type u)
    (mu : Cardinal.{u}) where
  characteristic : A -> Characteristic
  characteristic_injective : Function.Injective characteristic
  witness : A -> Set K
  witness_cardinal : forall a, Cardinal.mk (witness a) = mu
  reconstruct : Set K -> Characteristic
  reconstruct_of_subset : forall a X,
    X ⊆ witness a -> Cardinal.mk X = mu ->
      reconstruct X = characteristic a

theorem UniformSubsetCharacteristicCoding.mk_le_of_uniformSubsetCover
    {A K Characteristic : Type u}
    {mu alpha : Cardinal.{u}}
    (D : UniformSubsetCharacteristicCoding A K Characteristic mu)
    (C : UniformSubsetCover K mu)
    (hPower : (2 : Cardinal.{u}) ^ mu <= alpha)
    (hK : Cardinal.mk K <= alpha) :
    Cardinal.mk A <= alpha := by
  let code : A -> C.Index := fun a =>
    Classical.choose (C.downward_cofinal
      (D.witness a) (D.witness_cardinal a))
  have code_spec : forall a,
      C.member (code a) ⊆ D.witness a := by
    intro a
    exact Classical.choose_spec (C.downward_cofinal
      (D.witness a) (D.witness_cardinal a))
  have code_injective : Function.Injective code := by
    intro a b hab
    apply D.characteristic_injective
    calc
      D.characteristic a = D.reconstruct (C.member (code a)) :=
        (D.reconstruct_of_subset a _ (code_spec a)
          (C.member_cardinal (code a))).symm
      _ = D.reconstruct (C.member (code b)) := by rw [hab]
      _ = D.characteristic b :=
        D.reconstruct_of_subset b _ (code_spec b)
          (C.member_cardinal (code b))
  exact (Cardinal.mk_le_of_injective code_injective).trans
    (C.index_cardinal.trans (max_le hPower hK))

end PcfProject
