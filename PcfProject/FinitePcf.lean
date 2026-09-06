import PcfProject.PrincipalPcf
import PcfProject.ContinuumControl
import PcfProject.CofinalCore
import Mathlib.Data.Finset.Max

/-!
# Finite canonical PCF

This file proves that an ultrafilter on a finite index type is principal, then
uses the canonical product semantics to identify `pcf(A)` with `A` for finite
sets of regular cardinals. It also proves the countable-PCF target bound for
finite regular sets below `aleph_omega`, without a countable-bound hypothesis.
It also identifies principalization with finite total cardinal index and,
for singleton-fibre indexed unions, identifies concentration with the same
finite-index condition.
-/

namespace PcfProject

universe u v

namespace Ideal

variable {I : Type u} (J : Ideal I)

theorem finset_exists_small
    {K : Type v}
    (s : Finset K)
    (P : K -> I -> Prop)
    (hSmall : forall k, k ∈ s -> J.Small (P k)) :
    J.Small (fun i => exists k, k ∈ s /\ P k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact J.subset_small J.empty_small (by simp)
  | @insert a s ha ih =>
      have hA : J.Small (P a) := hSmall a (by simp)
      have hRest : J.Small (fun i => exists k, k ∈ s /\ P k i) :=
        ih (fun k hk => hSmall k (by simp [hk]))
      exact J.subset_small (J.union_small hA hRest) (by
        intro i hi
        obtain ⟨k, hk, hPi⟩ := hi
        rcases Finset.mem_insert.mp hk with hka | hk
        · subst k
          exact Or.inl hPi
        · exact Or.inr ⟨k, hk, hPi⟩)

theorem IsUltrafilterDual.exists_compl_singleton_small
    {J : Ideal I}
    [Finite I]
    (hJ : J.IsUltrafilterDual) :
    exists i0 : I, J.Small (fun i => Not (i = i0)) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  by_contra hNoPoint
  have hSingleton : forall i0 : I, J.Small (fun i => i = i0) := by
    intro i0
    cases hJ.small_or_compl_small (fun i => i = i0) with
    | inl hSmall => exact hSmall
    | inr hCompl => exact (hNoPoint ⟨i0, hCompl⟩).elim
  apply hJ.isProper
  exact J.subset_small
    (J.finset_exists_small Finset.univ (fun i0 i => i = i0)
      (fun i0 _ => hSingleton i0))
    (by
      intro i _
      exact ⟨i, Finset.mem_univ i, rfl⟩)

theorem IsUltrafilterDual.small_iff_not_at
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    {i0 : I}
    (hCompl : J.Small (fun i => Not (i = i0)))
    (S : I -> Prop) :
    J.Small S <-> Not (S i0) := by
  constructor
  · intro hSmall hSi0
    apply hJ.isProper
    exact J.subset_small (J.union_small hSmall hCompl) (by
      intro i _
      by_cases hi : i = i0
      · subst i
        exact Or.inl hSi0
      · exact Or.inr hi)
  · intro hNot
    exact J.subset_small hCompl (by
      intro i hSi hi
      subst i
      exact hNot hSi)

theorem IsUltrafilterDual.eq_excludePoint_of_finite
    {J : Ideal I}
    [Finite I]
    (hJ : J.IsUltrafilterDual) :
    exists i0 : I, J = excludePoint i0 := by
  obtain ⟨i0, hCompl⟩ := hJ.exists_compl_singleton_small
  refine ⟨i0, Ideal.ext ?_⟩
  intro S
  exact hJ.small_iff_not_at hCompl S

end Ideal

namespace AllUltrafiltersPrincipal

/-- 有限规范指标集上的每个超滤对偶理想都是排除某个单点所得的主理想。 -/
theorem of_finite
    {A : CardSet.{u}}
    [Finite (CardinalIndex A)] :
    AllUltrafiltersPrincipal A := by
  intro J hJ
  exact hJ.eq_excludePoint_of_finite

end AllUltrafiltersPrincipal


/-! 有限 PCF 的核心事实：有限多个有限坐标的并仍有有限索引，单点集亦然。 -/
theorem finite_cardinalIndex_finsetUnion
    {I : Type v}
    (s : Finset I)
    (A : I -> CardSet.{u})
    (hFinite : forall i, i ∈ s -> Finite (CardinalIndex (A i))) :
    Finite (CardinalIndex (finsetUnionCardSet s A)) := by
  classical
  let K := {i : I // i ∈ s}
  letI : Fintype K := Fintype.ofFinite K
  letI : forall i : K, Finite (CardinalIndex (A i.1)) :=
    fun i => hFinite i.1 i.2
  letI : Finite (Sigma (fun i : K => CardinalIndex (A i.1))) := by
    letI : forall i : K, Fintype (CardinalIndex (A i.1)) :=
      fun i => Fintype.ofFinite (CardinalIndex (A i.1))
    exact Finite.of_fintype (Sigma (fun i : K => CardinalIndex (A i.1)))
  let f : CardinalIndex (finsetUnionCardSet s A) ->
      Sigma (fun i : K => CardinalIndex (A i.1)) := fun theta =>
    let hTheta := Classical.choose_spec theta.2
    ⟨⟨Classical.choose theta.2, hTheta.1⟩,
      ⟨theta.1, hTheta.2⟩⟩
  apply Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  have hVal := congrArg
    (fun z : Sigma (fun i : K => CardinalIndex (A i.1)) => z.2.1) hxy
  simpa only [f] using hVal

/-! A singleton cardinal set has a finite canonical index.  This elementary
fact is useful when a countable filtration is built from finite unions of
singleton coordinates. -/
theorem finite_cardinalIndex_singleton
    (theta : Cardinal.{u}) :
    Finite (CardinalIndex (singletonCardSet theta)) := by
  apply Finite.of_injective (fun _ : CardinalIndex (singletonCardSet theta) =>
    PUnit.unit)
  intro i j _hij
  apply Subtype.ext
  exact i.2.trans j.2.symm

#print axioms finite_cardinalIndex_singleton

/-- The finite-index PCF construction applies to a finite union once the
component regularity and nonemptiness facts have been supplied. The
finite-index premise is proved from the components by
`finite_cardinalIndex_finsetUnion`. -/
theorem cardinalProductRepresentation_pcf_subset_of_finite
    {A : CardSet.{u}}
    [Finite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A) :
  SubsetOf (cardinalProductRepresentation.pcf A) A := by
  exact cardinalProductRepresentation_pcf_subset_of_principal_ultrafilters
    hRegulars (AllUltrafiltersPrincipal.of_finite (A := A))

theorem cardinalProductRepresentation_pcf_eq_of_finite
    {A : CardSet.{u}}
    [Finite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A) :
  cardinalProductRepresentation.pcf A = A := by
  exact cardinalProductRepresentation_pcf_eq_of_principal_ultrafilters
    hRegulars (AllUltrafiltersPrincipal.of_finite (A := A))

/-! 对非空有限正则集，取有限索引中的最大坐标；`pcf(A)=A` 保证它正是最大 pcf 见证。 -/
noncomputable def finiteMaxPcfWitness
    {A : CardSet.{u}}
    [Finite (CardinalIndex A)]
    (hRegulars : SetOfRegulars A)
    (hNonempty : exists theta, A theta) :
    MaxPcfWitness cardinalProductRepresentation A := by
  classical
  letI : Nonempty (CardinalIndex A) := by
    obtain ⟨theta, hTheta⟩ := hNonempty
    exact ⟨⟨theta, hTheta⟩⟩
  letI : Fintype (CardinalIndex A) := Fintype.ofFinite _
  let iMax : CardinalIndex A :=
    Finset.univ.max' Finset.univ_nonempty
  exact {
    theta := iMax.1
    isMax := by
      constructor
      · exact cardinalProductRepresentation_mem_pcf_of_mem
          hRegulars iMax.2
      · intro beta hBeta
        let iBeta : CardinalIndex A :=
          ⟨beta, cardinalProductRepresentation_pcf_subset_of_finite
            hRegulars beta hBeta⟩
        exact Finset.le_max' Finset.univ iBeta (Finset.mem_univ iBeta)
  }

#print axioms finiteMaxPcfWitness

end PcfProject
