import PcfProject.CanonicalProduct
import PcfProject.Generators
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max

/-!
# Canonical PCF structural consequences

This file connects structural hypotheses for the canonical cardinal-product
representation to the concrete inclusion `A subset pcf(A)`.
-/

namespace PcfProject

universe u v

def emptyCardSet : CardSet.{u} :=
  fun _ => False

def UnionCardSet (A B : CardSet.{u}) : CardSet.{u} :=
  fun theta => A theta \/ B theta

theorem subset_union_left
    (A B : CardSet.{u}) :
    SubsetOf A (UnionCardSet A B) := by
  intro theta hTheta
  exact Or.inl hTheta

theorem subset_union_right
    (A B : CardSet.{u}) :
    SubsetOf B (UnionCardSet A B) := by
  intro theta hTheta
  exact Or.inr hTheta

theorem unionCardSet_regulars
    {A B : CardSet.{u}}
    (hRegularsA : SetOfRegulars A)
    (hRegularsB : SetOfRegulars B) :
    SetOfRegulars (UnionCardSet A B) := by
  intro theta hTheta
  cases hTheta with
  | inl hA => exact hRegularsA theta hA
  | inr hB => exact hRegularsB theta hB

theorem interCardSet_regulars
    {A B : CardSet.{u}}
    (hRegulars : SetOfRegulars A) :
    SetOfRegulars (InterCardSet A B) :=
  setOfRegulars_of_subset
    (by
      intro theta hTheta
      exact hTheta.1)
    hRegulars

theorem inter_unionCardSet
    (A B C : CardSet.{u}) :
    InterCardSet A (UnionCardSet B C) =
      UnionCardSet (InterCardSet A B) (InterCardSet A C) := by
  funext theta
  apply propext
  constructor
  · intro h
    cases h.2 with
    | inl hB => exact Or.inl ⟨h.1, hB⟩
    | inr hC => exact Or.inr ⟨h.1, hC⟩
  · intro h
    cases h with
    | inl hAB => exact ⟨hAB.1, Or.inl hAB.2⟩
    | inr hAC => exact ⟨hAC.1, Or.inr hAC.2⟩

theorem cardinalProductRepresentation_not_mem_pcf_empty
    (beta : Cardinal.{u}) :
    Not (cardinalProductRepresentation.pcf emptyCardSet beta) := by
  intro hBeta
  obtain ⟨_hRegular, J, hUltra, _hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := emptyCardSet) (theta := beta)).mp hBeta
  apply hUltra.isProper
  exact J.subset_small J.empty_small (by
    intro i _
    exact i.property)

theorem cardinalProductRepresentation_pcf_empty :
    cardinalProductRepresentation.pcf emptyCardSet = emptyCardSet := by
  funext beta
  apply propext
  constructor
  · exact cardinalProductRepresentation_not_mem_pcf_empty beta
  · intro hFalse
    exact False.elim hFalse

theorem cardinalProductRepresentation_nonempty_of_mem_pcf
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hTheta : cardinalProductRepresentation.pcf A theta) :
    exists beta, A beta := by
  obtain ⟨_hRegular, J, hUltra, _hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := A) (theta := theta)).mp hTheta
  by_contra hA
  apply hUltra.isProper
  exact J.subset_small J.empty_small (by
    intro i _
    exact hA ⟨i.1, i.2⟩)

/-- Canonical PCF is monotone on sets of regular cardinals. The source set
does not need a separate regularity hypothesis because it is a subset of the
regular target set. -/
theorem cardinalProductRepresentation_pcf_mono
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B) :
    SubsetOf
      (cardinalProductRepresentation.pcf A)
      (cardinalProductRepresentation.pcf B) := by
  intro theta hTheta
  obtain ⟨hRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := A) (theta := theta)).mp hTheta
  obtain ⟨s⟩ := hTcf.hasScaleWitness
  exact (cardinalProductRepresentation_mem_pcf_iff
    (A := B) (theta := theta)).mpr
      ⟨hRegular,
        J.pushforward (cardinalIndexMap hAB),
        hUltra.pushforward (cardinalIndexMap hAB),
        extendCardinalScale_hasTrueCofinality
          hAB hRegulars hRegular s⟩

/-! A finite-generator closure certificate has the exact canonical PCF
    localization property once its substantive `covered` field is supplied.
    The reverse inclusion is the already proved monotonicity of canonical PCF;
    the forward inclusion is precisely the certificate's coverage assertion.
    This theorem therefore records the semantic output of a certificate and
    does not manufacture the difficult coverage field. -/
theorem GeneratorSystem.FiniteGeneratorClosureCertificate.canonical_pcf_closure_eq
    {A : CardSet.{u}}
    {G : GeneratorSystem cardinalProductRepresentation.{u} A}
    {theta : Cardinal.{u}}
    (C : GeneratorSystem.FiniteGeneratorClosureCertificate G theta)
    (hRegulars : SetOfRegulars A) :
    cardinalProductRepresentation.pcf (InterCardSet A C.closure) =
      cardinalProductRepresentation.pcf A := by
  have hInter : InterCardSet A C.closure = C.closure := by
    funext beta
    apply propext
    constructor
    · intro hBeta
      exact hBeta.2
    · intro hBeta
      exact ⟨C.closure_subset beta hBeta, hBeta⟩
  funext beta
  apply propext
  constructor
  · intro hBeta
    rw [hInter] at hBeta
    exact cardinalProductRepresentation_pcf_mono
      C.closure_subset hRegulars beta hBeta
  · intro hBeta
    exact C.closure_covered hBeta

#print axioms
  GeneratorSystem.FiniteGeneratorClosureCertificate.canonical_pcf_closure_eq

/-- A canonical PCF witness on `B` descends to `A subset B` when its
ultrafilter is concentrated on the coordinates belonging to `A`. -/
theorem cardinalProductRepresentation_mem_pcf_of_eventually_mem
    {A B : CardSet.{u}}
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B)
    {theta : Cardinal.{u}}
    (hRegular : Cardinal.IsRegular theta)
    (J : Ideal (CardinalIndex B))
    (hUltra : J.IsUltrafilterDual)
    (hTcf : HasTrueCofinality
      (cardinalProductFrame B J)
      (cardinalScaleLength theta))
    (hEventually : J.Eventually (fun i => A i.1)) :
    cardinalProductRepresentation.pcf A theta := by
  let f := cardinalIndexMap hAB
  let JA := J.restrictAlong f
  have hRange : J.Eventually (fun k => exists i, f i = k) :=
    (J.eventually_congr (fun k =>
      cardinalIndexMap_mem_range_iff hAB k)).mpr hEventually
  have hUltraA : JA.IsUltrafilterDual :=
    hUltra.restrictAlong f (cardinalIndexMap_injective hAB) hRange
  have hPush : JA.pushforward f = J :=
    J.restrictAlong_pushforward_eq f hRange
  have hTcfPush : HasTrueCofinality
      (cardinalProductFrame B
        (JA.pushforward (cardinalIndexMap hAB)))
      (cardinalScaleLength theta) := by
    simpa only [f, hPush] using hTcf
  exact cardinalProductRepresentation_mem_pcf_of_concentrated_witness
    hAB hRegulars hRegular hUltraA hTcfPush

/-- Canonical PCF preserves binary unions of sets of regular cardinals. The
nontrivial direction restricts an ultrafilter witness to whichever side of
the partition it concentrates on. -/
theorem cardinalProductRepresentation_pcf_union
    {A B : CardSet.{u}}
    (hRegularsA : SetOfRegulars A)
    (hRegularsB : SetOfRegulars B) :
    cardinalProductRepresentation.pcf (UnionCardSet A B) =
      UnionCardSet
        (cardinalProductRepresentation.pcf A)
        (cardinalProductRepresentation.pcf B) := by
  funext theta
  apply propext
  constructor
  · intro hTheta
    obtain ⟨hRegular, J, hUltra, hTcf⟩ :=
      (cardinalProductRepresentation_mem_pcf_iff
        (A := UnionCardSet A B) (theta := theta)).mp hTheta
    cases hUltra.eventually_or_eventually_not (fun i => A i.1) with
    | inl hA =>
        exact Or.inl
          (cardinalProductRepresentation_mem_pcf_of_eventually_mem
            (subset_union_left A B)
            (unionCardSet_regulars hRegularsA hRegularsB)
            hRegular J hUltra hTcf hA)
    | inr hNotA =>
        have hB : J.Eventually (fun i => B i.1) :=
          J.eventually_mono hNotA (by
            intro i hNotAi
            cases i.2 with
            | inl hAi => exact False.elim (hNotAi hAi)
            | inr hBi => exact hBi)
        exact Or.inr
          (cardinalProductRepresentation_mem_pcf_of_eventually_mem
            (subset_union_right A B)
            (unionCardSet_regulars hRegularsA hRegularsB)
            hRegular J hUltra hTcf hB)
  · intro hTheta
    cases hTheta with
    | inl hA =>
        exact cardinalProductRepresentation_pcf_mono
          (subset_union_left A B)
          (unionCardSet_regulars hRegularsA hRegularsB)
          theta hA
    | inr hB =>
        exact cardinalProductRepresentation_pcf_mono
          (subset_union_right A B)
          (unionCardSet_regulars hRegularsA hRegularsB)
          theta hB

def FinsetUnionCardSet
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u}) : CardSet.{u} :=
  fun theta => exists i, i ∈ s /\ A i theta

theorem finsetUnionCardSet_empty
    {ι : Type v}
    (A : ι -> CardSet.{u}) :
    FinsetUnionCardSet (∅ : Finset ι) A = emptyCardSet := by
  funext theta
  apply propext
  constructor
  · rintro ⟨i, hi, _hA⟩
    simp at hi
  · intro hFalse
    exact False.elim hFalse

theorem finsetUnionCardSet_insert
    {ι : Type v}
    [DecidableEq ι]
    (i : ι)
    (s : Finset ι)
    (A : ι -> CardSet.{u}) :
    FinsetUnionCardSet (insert i s) A =
      UnionCardSet (A i) (FinsetUnionCardSet s A) := by
  classical
  funext theta
  apply propext
  constructor
  · rintro ⟨j, hj, hAj⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl hAj
    · exact Or.inr ⟨j, hj, hAj⟩
  · intro hUnion
    cases hUnion with
    | inl hAi => exact ⟨i, Finset.mem_insert_self i s, hAi⟩
    | inr hRest =>
        obtain ⟨j, hj, hAj⟩ := hRest
        exact ⟨j, Finset.mem_insert_of_mem hj, hAj⟩

theorem finsetUnionCardSet_regulars
    {ι : Type v}
    {s : Finset ι}
    {A : ι -> CardSet.{u}}
    (hRegulars : forall i, SetOfRegulars (A i)) :
    SetOfRegulars (FinsetUnionCardSet s A) := by
  intro theta hTheta
  obtain ⟨i, _hi, hA⟩ := hTheta
  exact hRegulars i theta hA

/-- Canonical PCF commutes with finite unions of regular-cardinal sets.

The theorem is proved by finite induction from the empty-set theorem and the
binary-union localization theorem. It makes no claim about infinite unions.
-/
theorem cardinalProductRepresentation_pcf_finsetUnion
    {ι : Type v}
    (s : Finset ι)
    (A : ι -> CardSet.{u})
    (hRegulars : forall i, SetOfRegulars (A i)) :
    cardinalProductRepresentation.pcf (FinsetUnionCardSet s A) =
      FinsetUnionCardSet s
        (fun i => cardinalProductRepresentation.pcf (A i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [finsetUnionCardSet_empty, cardinalProductRepresentation_pcf_empty,
        finsetUnionCardSet_empty]
  | @insert i s hi ih =>
      rw [finsetUnionCardSet_insert]
      rw [cardinalProductRepresentation_pcf_union
        (hRegulars i)
        (finsetUnionCardSet_regulars hRegulars)]
      rw [ih]
      rw [finsetUnionCardSet_insert]

def canonicalBelowIdeal
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) : Ideal Cardinal.{u} where
  Small B :=
    forall beta,
      cardinalProductRepresentation.pcf (InterCardSet A B) beta ->
        beta < theta
  empty_small := by
    intro beta hBeta
    have hEmpty :
        InterCardSet A (fun _ => False) = emptyCardSet := by
      funext gamma
      apply propext
      constructor
      · intro h
        exact h.2
      · intro h
        exact False.elim h
    exfalso
    apply cardinalProductRepresentation_not_mem_pcf_empty beta
    rw [← hEmpty]
    exact hBeta
  subset_small := by
    intro B C hB hCB beta hBeta
    apply hB beta
    exact cardinalProductRepresentation_pcf_mono
      (hRegulars := interCardSet_regulars hRegulars)
      (fun gamma (hGamma : InterCardSet A C gamma) =>
        ⟨hGamma.1, hCB gamma hGamma.2⟩)
      beta hBeta
  union_small := by
    intro B C hB hC beta hBeta
    have hBetaUnion : cardinalProductRepresentation.pcf
        (UnionCardSet (InterCardSet A B) (InterCardSet A C)) beta := by
      rw [← inter_unionCardSet A B C]
      exact hBeta
    rw [cardinalProductRepresentation_pcf_union
      (interCardSet_regulars hRegulars)
      (interCardSet_regulars hRegulars)] at hBetaUnion
    cases hBetaUnion with
    | inl hBbeta => exact hB beta hBbeta
    | inr hCbeta => exact hC beta hCbeta

def canonicalAtMostIdeal
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) : Ideal Cardinal.{u} where
  Small B :=
    forall beta,
      cardinalProductRepresentation.pcf (InterCardSet A B) beta ->
        beta <= theta
  empty_small := by
    intro beta hBeta
    have hEmpty :
        InterCardSet A (fun _ => False) = emptyCardSet := by
      funext gamma
      apply propext
      constructor
      · intro h
        exact h.2
      · intro h
        exact False.elim h
    exfalso
    apply cardinalProductRepresentation_not_mem_pcf_empty beta
    rw [← hEmpty]
    exact hBeta
  subset_small := by
    intro B C hB hCB beta hBeta
    apply hB beta
    exact cardinalProductRepresentation_pcf_mono
      (hRegulars := interCardSet_regulars hRegulars)
      (fun gamma (hGamma : InterCardSet A C gamma) =>
        ⟨hGamma.1, hCB gamma hGamma.2⟩)
      beta hBeta
  union_small := by
    intro B C hB hC beta hBeta
    have hBetaUnion : cardinalProductRepresentation.pcf
        (UnionCardSet (InterCardSet A B) (InterCardSet A C)) beta := by
      rw [← inter_unionCardSet A B C]
      exact hBeta
    rw [cardinalProductRepresentation_pcf_union
      (interCardSet_regulars hRegulars)
      (interCardSet_regulars hRegulars)] at hBetaUnion
    cases hBetaUnion with
    | inl hBbeta => exact hB beta hBbeta
    | inr hCbeta => exact hC beta hCbeta

theorem canonicalBelowIdeal_small_iff
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u})
    (B : CardSet.{u}) :
    (canonicalBelowIdeal A hRegulars theta).Small B <->
      forall beta,
        cardinalProductRepresentation.pcf (InterCardSet A B) beta ->
          beta < theta := Iff.rfl

theorem canonicalAtMostIdeal_small_iff
    (A : CardSet.{u})
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u})
    (B : CardSet.{u}) :
    (canonicalAtMostIdeal A hRegulars theta).Small B <->
      forall beta,
        cardinalProductRepresentation.pcf (InterCardSet A B) beta ->
          beta <= theta := Iff.rfl

/-! The canonical filtration is ordered exactly as its PCF thresholds
    suggest. These are semantic ideal comparisons, not generator existence
    theorems. -/
theorem canonicalBelowIdeal_mono
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma) :
    Ideal.Le (canonicalBelowIdeal A hRegulars theta)
      (canonicalBelowIdeal A hRegulars gamma) := by
  intro B hB
  apply (canonicalBelowIdeal_small_iff A hRegulars gamma B).mpr
  intro beta hBeta
  exact ((canonicalBelowIdeal_small_iff A hRegulars theta B).mp hB beta hBeta).trans_le
    hThetaGamma

theorem canonicalAtMostIdeal_mono
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma) :
    Ideal.Le (canonicalAtMostIdeal A hRegulars theta)
      (canonicalAtMostIdeal A hRegulars gamma) := by
  intro B hB
  apply (canonicalAtMostIdeal_small_iff A hRegulars gamma B).mpr
  intro beta hBeta
  exact ((canonicalAtMostIdeal_small_iff A hRegulars theta B).mp hB beta hBeta).trans
    hThetaGamma

theorem canonicalAtMostIdeal_le_canonicalBelowIdeal_of_lt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta gamma : Cardinal.{u}}
    (hThetaGamma : theta < gamma) :
    Ideal.Le (canonicalAtMostIdeal A hRegulars theta)
      (canonicalBelowIdeal A hRegulars gamma) := by
  intro B hB
  apply (canonicalBelowIdeal_small_iff A hRegulars gamma B).mpr
  intro beta hBeta
  exact ((canonicalAtMostIdeal_small_iff A hRegulars theta B).mp hB beta hBeta).trans_lt
    hThetaGamma

theorem canonicalBelowIdeal_isProper_iff_exists_pcf_not_lt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) :
    Ideal.IsProper (canonicalBelowIdeal A hRegulars theta) <->
      exists beta, cardinalProductRepresentation.pcf A beta /\
        Not (beta < theta) := by
  classical
  constructor
  · intro hProper
    by_contra hNo
    apply hProper
    intro beta hBeta
    by_cases hLt : beta < theta
    · exact hLt
    · have hBetaA : cardinalProductRepresentation.pcf A beta := by
        have hInterEq : InterCardSet A (fun _ => True) = A := by
          funext gamma
          apply propext
          constructor
          · intro h
            exact h.1
          · intro h
            exact ⟨h, True.intro⟩
        rw [hInterEq] at hBeta
        exact hBeta
      exact False.elim (hNo ⟨beta, hBetaA, hLt⟩)
  · rintro ⟨beta, hBeta, hNotLt⟩ hSmall
    have hInterEq : InterCardSet A (fun _ => True) = A := by
      funext gamma
      apply propext
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, True.intro⟩
    have hBeta' : cardinalProductRepresentation.pcf
        (InterCardSet A (fun _ => True)) beta := by
      rw [hInterEq]
      exact hBeta
    exact hNotLt (hSmall beta hBeta')

theorem canonicalAtMostIdeal_isProper_iff_exists_pcf_gt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) :
    Ideal.IsProper (canonicalAtMostIdeal A hRegulars theta) <->
      exists beta, cardinalProductRepresentation.pcf A beta /\
        theta < beta := by
  classical
  constructor
  · intro hProper
    by_contra hNo
    apply hProper
    intro beta hBeta
    by_cases hLe : beta <= theta
    · exact hLe
    · have hBetaA : cardinalProductRepresentation.pcf A beta := by
        have hInterEq : InterCardSet A (fun _ => True) = A := by
          funext gamma
          apply propext
          constructor
          · intro h
            exact h.1
          · intro h
            exact ⟨h, True.intro⟩
        rw [hInterEq] at hBeta
        exact hBeta
      exact False.elim (hNo ⟨beta, hBetaA, lt_of_not_ge hLe⟩)
  · rintro ⟨beta, hBeta, hGt⟩ hSmall
    have hInterEq : InterCardSet A (fun _ => True) = A := by
      funext gamma
      apply propext
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, True.intro⟩
    have hBeta' : cardinalProductRepresentation.pcf
        (InterCardSet A (fun _ => True)) beta := by
      rw [hInterEq]
      exact hBeta
    exact (not_lt_of_ge (hSmall beta hBeta')) hGt

theorem canonicalBelowIdeal_not_isProper_iff_forall_pcf_lt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) :
    Not (Ideal.IsProper (canonicalBelowIdeal A hRegulars theta)) <->
      forall beta, cardinalProductRepresentation.pcf A beta -> beta < theta := by
  constructor
  · intro hNot beta hBeta
    by_contra hNotLt
    apply hNot
    exact (canonicalBelowIdeal_isProper_iff_exists_pcf_not_lt
      hRegulars theta).mpr ⟨beta, hBeta, hNotLt⟩
  · intro hAll hProper
    obtain ⟨beta, hBeta, hNotLt⟩ :=
      (canonicalBelowIdeal_isProper_iff_exists_pcf_not_lt
        hRegulars theta).mp hProper
    exact hNotLt (hAll beta hBeta)

theorem canonicalAtMostIdeal_not_isProper_iff_forall_pcf_le
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) :
    Not (Ideal.IsProper (canonicalAtMostIdeal A hRegulars theta)) <->
      forall beta, cardinalProductRepresentation.pcf A beta -> beta <= theta := by
  constructor
  · intro hNot beta hBeta
    by_contra hNotLe
    apply hNot
    exact (canonicalAtMostIdeal_isProper_iff_exists_pcf_gt
      hRegulars theta).mpr ⟨beta, hBeta, lt_of_not_ge hNotLe⟩
  · intro hAll hProper
    obtain ⟨beta, hBeta, hGt⟩ :=
      (canonicalAtMostIdeal_isProper_iff_exists_pcf_gt
        hRegulars theta).mp hProper
    exact (not_lt_of_ge (hAll beta hBeta)) hGt

/-! A genuine gap in the represented PCF spectrum is invisible to the
    canonical filtration. The reverse implications use monotonicity from a
    localized intersection back to `A`, so the statement is about all
    localized PCF spectra, not just the global one. -/
theorem canonicalBelowIdeal_eq_of_no_pcf_between
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma)
    (hGap : forall beta, cardinalProductRepresentation.pcf A beta ->
      Not (theta <= beta /\ beta < gamma)) :
    canonicalBelowIdeal A hRegulars theta =
      canonicalBelowIdeal A hRegulars gamma := by
  apply Ideal.ext
  intro B
  constructor
  · intro hSmall
    apply (canonicalBelowIdeal_small_iff A hRegulars gamma B).mpr
    intro beta hBeta
    exact ((canonicalBelowIdeal_small_iff A hRegulars theta B).mp
      hSmall beta hBeta).trans_le hThetaGamma
  · intro hSmall
    apply (canonicalBelowIdeal_small_iff A hRegulars theta B).mpr
    intro beta hBeta
    have hBetaA : cardinalProductRepresentation.pcf A beta :=
      cardinalProductRepresentation_pcf_mono
        (hRegulars := hRegulars)
        (fun _ h => h.1) beta hBeta
    by_contra hNotLt
    exact (hGap beta hBetaA) ⟨le_of_not_gt hNotLt,
      (canonicalBelowIdeal_small_iff A hRegulars gamma B).mp
        hSmall beta hBeta⟩

theorem canonicalAtMostIdeal_eq_of_no_pcf_between
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma)
    (hGap : forall beta, cardinalProductRepresentation.pcf A beta ->
      Not (theta < beta /\ beta <= gamma)) :
    canonicalAtMostIdeal A hRegulars theta =
      canonicalAtMostIdeal A hRegulars gamma := by
  apply Ideal.ext
  intro B
  constructor
  · intro hSmall
    apply (canonicalAtMostIdeal_small_iff A hRegulars gamma B).mpr
    intro beta hBeta
    exact ((canonicalAtMostIdeal_small_iff A hRegulars theta B).mp
      hSmall beta hBeta).trans hThetaGamma
  · intro hSmall
    apply (canonicalAtMostIdeal_small_iff A hRegulars theta B).mpr
    intro beta hBeta
    have hBetaA : cardinalProductRepresentation.pcf A beta :=
      cardinalProductRepresentation_pcf_mono
        (hRegulars := hRegulars)
        (fun _ h => h.1) beta hBeta
    by_contra hNotLe
    exact (hGap beta hBetaA) ⟨lt_of_not_ge hNotLe,
      (canonicalAtMostIdeal_small_iff A hRegulars gamma B).mp
        hSmall beta hBeta⟩

theorem canonicalBelowIdeal_eq_canonicalAtMostIdeal_of_not_mem
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hNotMem : Not (cardinalProductRepresentation.pcf A theta)) :
    canonicalBelowIdeal A hRegulars theta =
      canonicalAtMostIdeal A hRegulars theta := by
  apply Ideal.ext
  intro B
  constructor
  · intro hSmall
    apply (canonicalAtMostIdeal_small_iff A hRegulars theta B).mpr
    intro beta hBeta
    exact ((canonicalBelowIdeal_small_iff A hRegulars theta B).mp
      hSmall beta hBeta).le
  · intro hSmall
    apply (canonicalBelowIdeal_small_iff A hRegulars theta B).mpr
    intro beta hBeta
    have hBetaA : cardinalProductRepresentation.pcf A beta :=
      cardinalProductRepresentation_pcf_mono
        (hRegulars := hRegulars)
        (fun _ h => h.1) beta hBeta
    have hBetaNe : beta ≠ theta := by
      intro hEq
      apply hNotMem
      simpa only [hEq] using hBetaA
    exact lt_of_le_of_ne
      ((canonicalAtMostIdeal_small_iff A hRegulars theta B).mp
        hSmall beta hBeta) hBetaNe

#print axioms canonicalBelowIdeal_not_isProper_iff_forall_pcf_lt
#print axioms canonicalAtMostIdeal_not_isProper_iff_forall_pcf_le
#print axioms canonicalBelowIdeal_eq_of_no_pcf_between
#print axioms canonicalAtMostIdeal_eq_of_no_pcf_between
#print axioms canonicalBelowIdeal_eq_canonicalAtMostIdeal_of_not_mem

theorem canonicalBelowIdeal_isProper_of_mem_pcf_le
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta beta : Cardinal.{u}}
    (hBeta : cardinalProductRepresentation.pcf A beta)
    (hThetaBeta : theta <= beta) :
    Ideal.IsProper (canonicalBelowIdeal A hRegulars theta) :=
  (canonicalBelowIdeal_isProper_iff_exists_pcf_not_lt
    hRegulars theta).mpr
    ⟨beta, hBeta, not_lt_of_ge hThetaBeta⟩

theorem canonicalAtMostIdeal_isProper_of_mem_pcf_lt
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    {theta beta : Cardinal.{u}}
    (hBeta : cardinalProductRepresentation.pcf A beta)
    (hThetaBeta : theta < beta) :
    Ideal.IsProper (canonicalAtMostIdeal A hRegulars theta) :=
  (canonicalAtMostIdeal_isProper_iff_exists_pcf_gt
    hRegulars theta).mpr
    ⟨beta, hBeta, hThetaBeta⟩

#print axioms canonicalBelowIdeal_mono
#print axioms canonicalAtMostIdeal_mono
#print axioms canonicalAtMostIdeal_le_canonicalBelowIdeal_of_lt
#print axioms canonicalBelowIdeal_isProper_of_mem_pcf_le
#print axioms canonicalAtMostIdeal_isProper_of_mem_pcf_lt

theorem GeneratorSystem.belowIdeal_eq_canonical
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) :
    G.belowIdeal theta = canonicalBelowIdeal A hRegulars theta := by
  apply Ideal.ext
  intro B
  exact (G.belowIdeal_small_iff theta B).trans
    (canonicalBelowIdeal_small_iff A hRegulars theta B).symm

theorem GeneratorSystem.atMostIdeal_eq_canonical
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) :
    G.atMostIdeal theta = canonicalAtMostIdeal A hRegulars theta := by
  apply Ideal.ext
  intro B
  exact (G.atMostIdeal_small_iff theta B).trans
    (canonicalAtMostIdeal_small_iff A hRegulars theta B).symm

/-! The abstract generator equivalence can be read directly in the canonical
    filtration. This is the local form needed when a PCF argument moves
    between a strict threshold and its generator. -/
theorem GeneratorSystem.canonical_atMost_small_iff_exists_below_cover
    {A : CardSet.{u}}
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hRegulars : SetOfRegulars A)
    {theta : Cardinal.{u}}
    (hTheta : cardinalProductRepresentation.pcf A theta)
    (B : Cardinal.{u} -> Prop) :
    (canonicalAtMostIdeal A hRegulars theta).Small B <->
      exists T : Cardinal.{u} -> Prop,
        (canonicalBelowIdeal A hRegulars theta).Small T /\
          forall beta, B beta -> T beta \/ G.generator theta beta := by
  rw [← G.atMostIdeal_eq_canonical hRegulars theta,
    ← G.belowIdeal_eq_canonical hRegulars theta]
  exact G.atMost_small_iff_exists_below_cover hTheta B

theorem canonicalBelowIdeal_le_canonicalAtMostIdeal
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (theta : Cardinal.{u}) :
    Ideal.Le (canonicalBelowIdeal A hRegulars theta)
      (canonicalAtMostIdeal A hRegulars theta) := by
  intro B hB
  apply (canonicalAtMostIdeal_small_iff A hRegulars theta B).mpr
  intro beta hBeta
  exact ((canonicalBelowIdeal_small_iff A hRegulars theta B).mp hB beta hBeta).le

#print axioms GeneratorSystem.canonical_atMost_small_iff_exists_below_cover
#print axioms canonicalBelowIdeal_le_canonicalAtMostIdeal

/-- Package a supplied canonical generator family after the two filtration
ideals have been constructed from PCF semantics. This does not prove the
generator or its ideal-equivalence property; those remain explicit inputs. -/
noncomputable def canonicalGeneratorSystemOfGenerator
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (generator : Cardinal.{u} -> CardSet.{u})
    (hGeneratorSubset :
      forall {theta},
        cardinalProductRepresentation.pcf A theta ->
          SubsetOf (generator theta) A)
    (hGeneratorIdealEquiv :
      forall {theta},
        cardinalProductRepresentation.pcf A theta ->
          Ideal.Equivalent
            (canonicalAtMostIdeal A hRegulars theta)
            ((canonicalBelowIdeal A hRegulars theta).extendBy
              (generator theta))) :
    GeneratorSystem cardinalProductRepresentation A where
  belowIdeal := canonicalBelowIdeal A hRegulars
  atMostIdeal := canonicalAtMostIdeal A hRegulars
  generator := generator
  belowIdeal_spec := canonicalBelowIdeal_small_iff A hRegulars
  atMostIdeal_spec := canonicalAtMostIdeal_small_iff A hRegulars
  generator_subset := hGeneratorSubset
  generator_ideal_equiv := hGeneratorIdealEquiv

theorem cardinalProductRepresentation_pcf_subset_of_principal_ultrafilters
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hPrincipal :
      forall J : Ideal (CardinalIndex A),
        J.IsUltrafilterDual ->
          exists i0, J = Ideal.excludePoint i0) :
    SubsetOf
      (cardinalProductRepresentation.pcf A)
      A := by
  intro theta hTheta
  obtain ⟨_hRegular, J, hUltra, hTcf⟩ :=
    (cardinalProductRepresentation_mem_pcf_iff
      (A := A) (theta := theta)).mp hTheta
  obtain ⟨i0, rfl⟩ := hPrincipal J hUltra
  have hEq : theta = i0.1 :=
    (cardinalProductFrame_excludePoint_hasTrueCofinality_iff
      hRegulars i0).mp hTcf
  rw [hEq]
  exact i0.2

theorem cardinalProductRepresentation_pcf_eq_of_principal_ultrafilters
    {A : CardSet.{u}}
    (hRegulars : SetOfRegulars A)
    (hPrincipal :
      forall J : Ideal (CardinalIndex A),
        J.IsUltrafilterDual ->
          exists i0, J = Ideal.excludePoint i0) :
    cardinalProductRepresentation.pcf A = A := by
  funext theta
  apply propext
  constructor
  · exact cardinalProductRepresentation_pcf_subset_of_principal_ultrafilters
      hRegulars hPrincipal theta
  · exact cardinalProductRepresentation_subset_pcf hRegulars theta

theorem cardinalProductRepresentation_maxPcfWitness_mono
    {A B : CardSet.{u}}
    (hMA : MaxPcfWitness cardinalProductRepresentation A)
    (hMB : MaxPcfWitness cardinalProductRepresentation B)
    (hAB : SubsetOf A B)
    (hRegulars : SetOfRegulars B) :
    hMA.theta <= hMB.theta := by
  exact hMA.theta_le_of_pcf_subset hMB
    (cardinalProductRepresentation_pcf_mono hAB hRegulars)

end PcfProject
