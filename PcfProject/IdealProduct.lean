import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Zorn

/-!
# Ideals and reduced products

This file is the abstract base layer for reduced products and does not assert
any PCF structural theorem. The ideal fields are the usual closure properties needed to define
eventual truth and reduced-product comparison. The base `Ideal` structure
allows improper ideals for compatibility; `Ideal.IsProper` is the explicit
predicate used when a genuine reduced-product argument needs properness.
The pushforward API also identifies principal pushforwards exactly with
eventual concentration on one map fiber. On every infinite index type, a
Zorn construction below produces a nonprincipal ultrafilter-dual ideal, so
principalization is correctly restricted to finite-index or explicit
principalization hypotheses. For a nonprincipal
ultrafilter-dual ideal, every singleton and finite subset is proved small, or
equivalently the ideal eventually avoids every finite set. On `Nat`, this is
strengthened to eventual domination of every fixed threshold.
-/

namespace PcfProject

universe u v w

/-- A finitely additive ideal of predicates on `I`; improper ideals are allowed. -/
structure Ideal (I : Type u) where
  Small : (I -> Prop) -> Prop
  empty_small : Small (fun _ => False)
  subset_small :
    forall {A B : I -> Prop}, Small A -> (forall i, B i -> A i) -> Small B
  union_small :
    forall {A B : I -> Prop}, Small A -> Small B ->
      Small (fun i => A i \/ B i)

namespace Ideal

variable {I : Type u} (J : Ideal I)

/-- The least ideal: a predicate is small exactly when it is empty. -/
def emptyOnly (I : Type u) : Ideal I where
  Small S := forall i, Not (S i)
  empty_small := by
    intro i hFalse
    exact hFalse
  subset_small := by
    intro A B hA hBA i hBi
    exact hA i (hBA i hBi)
  union_small := by
    intro A B hA hB i hAB
    cases hAB with
    | inl hAi => exact hA i hAi
    | inr hBi => exact hB i hBi

/-- The improper ideal in which every predicate is small. -/
def all (I : Type u) : Ideal I where
  Small _ := True
  empty_small := True.intro
  subset_small := by
    intro _ _ _ _
    exact True.intro
  union_small := by
    intro _ _ _ _
    exact True.intro

/-- The principal proper ideal of predicates omitting one fixed point. -/
def excludePoint (i0 : I) : Ideal I where
  Small S := Not (S i0)
  empty_small := by
    intro hFalse
    exact hFalse
  subset_small := by
    intro A B hA hBA hBi
    exact hA (hBA i0 hBi)
  union_small := by
    intro A B hA hB hAB
    cases hAB with
    | inl hAi => exact hA hAi
    | inr hBi => exact hB hBi

/-- Inclusion of ideals: every `J1`-small predicate is `J2`-small. -/
def Le (J1 J2 : Ideal I) : Prop :=
  forall S, J1.Small S -> J2.Small S

/-- Extensional equivalence of ideals, expressed by mutual inclusion. -/
def Equivalent (J1 J2 : Ideal I) : Prop :=
  Le J1 J2 /\ Le J2 J1

@[ext] theorem ext
    {J1 J2 : Ideal I}
    (hSmall : forall S, J1.Small S <-> J2.Small S) :
    J1 = J2 := by
  cases J1 with
  | mk Small1 empty1 subset1 union1 =>
      cases J2 with
      | mk Small2 empty2 subset2 union2 =>
          have h : Small1 = Small2 := by
            funext S
            exact propext (hSmall S)
          subst Small2
          rfl

/-- An ideal is proper when the constantly true predicate is not small. -/
def IsProper (J : Ideal I) : Prop :=
  Not (J.Small (fun _ => True))

/-- `J` is the ideal dual to an ultrafilter: it is proper and decides every
predicate up to complement. -/
def IsUltrafilterDual (J : Ideal I) : Prop :=
  J.IsProper /\
    forall S : I -> Prop,
      J.Small S \/ J.Small (fun i => Not (S i))

namespace IsUltrafilterDual

theorem isProper
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual) :
    J.IsProper :=
  hJ.1

theorem small_or_compl_small
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (S : I -> Prop) :
    J.Small S \/ J.Small (fun i => Not (S i)) :=
  hJ.2 S

theorem not_small_and_compl_small
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (S : I -> Prop) :
    Not (J.Small S /\ J.Small (fun i => Not (S i))) := by
  intro hBoth
  apply hJ.isProper
  exact J.subset_small (J.union_small hBoth.1 hBoth.2) (by
    intro i _
    by_cases hSi : S i
    · exact Or.inl hSi
    · exact Or.inr hSi)

end IsUltrafilterDual

theorem finset_small_iff
    {K : Type v}
    (s : Finset K)
    (P : K -> I -> Prop) :
    J.Small (fun i => exists k, k ∈ s /\ P k i) <->
      forall k, k ∈ s -> J.Small (P k) := by
  classical
  constructor
  · intro hSmall k hk
    exact J.subset_small hSmall (by
      intro i hPi
      exact ⟨k, hk, hPi⟩)
  · intro hSmall
    induction s using Finset.induction_on with
    | empty =>
        exact J.subset_small J.empty_small (by simp)
    | @insert k s hk ih =>
        exact J.subset_small (J.union_small
          (hSmall k (by simp))
          (ih (fun j hj => hSmall j (by simp [hj])))) (by
            intro i hi
            obtain ⟨j, hj, hPi⟩ := hi
            rcases Finset.mem_insert.mp hj with rfl | hj
            · exact Or.inl hPi
            · exact Or.inr ⟨j, hj, hPi⟩)

theorem excludePoint_isProper
    (i0 : I) :
    IsProper (excludePoint i0) := by
  intro hUniv
  exact hUniv True.intro

theorem excludePoint_isUltrafilterDual
    (i0 : I) :
    IsUltrafilterDual (excludePoint i0) := by
  classical
  constructor
  · exact excludePoint_isProper i0
  · intro S
    by_cases hSi : S i0
    · exact Or.inr (fun hNotSi => hNotSi hSi)
    · exact Or.inl hSi

/-- The ideal on `K` induced by taking preimages along `f`. In filter
language, this is the dual of the pushforward filter. -/
def pushforward
    {K : Type v}
    (f : I -> K) : Ideal K where
  Small S := J.Small (fun i => S (f i))
  empty_small := J.empty_small
  subset_small := by
    intro A B hA hBA
    exact J.subset_small hA (fun i hBi => hBA (f i) hBi)
  union_small := by
    intro A B hA hB
    exact J.union_small hA hB

@[simp] theorem pushforward_small_iff
    {K : Type v}
    (f : I -> K)
    (S : K -> Prop) :
    (J.pushforward f).Small S <-> J.Small (fun i => S (f i)) :=
  Iff.rfl

theorem IsProper.pushforward
    {K : Type v}
    {J : Ideal I}
    (hJ : J.IsProper)
    (f : I -> K) :
    (J.pushforward f).IsProper := by
  intro hUniv
  apply hJ
  exact hUniv

theorem IsUltrafilterDual.pushforward
    {K : Type v}
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (f : I -> K) :
    (J.pushforward f).IsUltrafilterDual := by
  constructor
  · exact hJ.isProper.pushforward f
  · intro S
    exact hJ.small_or_compl_small (fun i => S (f i))

/-! Inclusion of ideals is preserved by pushforward along a fixed map. -/
theorem pushforward_mono
    {K : Type v}
    {J0 J1 : Ideal I}
    (hLe : Le J0 J1)
    (f : I -> K) :
    Le (J0.pushforward f) (J1.pushforward f) := by
  intro S hS
  exact hLe _ hS

/-- `P` holds eventually modulo `J` when its complement is `J`-small. -/
def Eventually (P : I -> Prop) : Prop :=
  J.Small (fun i => Not (P i))

theorem IsUltrafilterDual.small_iff_not_eventually
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (P : I -> Prop) :
    J.Small P <-> Not (J.Eventually P) := by
  constructor
  · intro hSmall hEventually
    exact hJ.not_small_and_compl_small P ⟨hSmall, hEventually⟩
  · intro hNotEventually
    cases hJ.small_or_compl_small P with
    | inl hSmall => exact hSmall
    | inr hEventually => exact False.elim (hNotEventually hEventually)

theorem excludePoint_eventually_iff
    (i0 : I)
    (P : I -> Prop) :
    (excludePoint i0).Eventually P <-> P i0 := by
  classical
  change Not (Not (P i0)) <-> P i0
  constructor
  · exact Classical.byContradiction
  · exact fun hPi hNotPi => hNotPi hPi

@[simp] theorem pushforward_eventually_iff
    {K : Type v}
    (f : I -> K)
    (P : K -> Prop) :
    (J.pushforward f).Eventually P <->
      J.Eventually (fun i => P (f i)) :=
  Iff.rfl

@[simp] theorem pushforward_id
    (J : Ideal I) :
    J.pushforward (fun i => i) = J := by
  apply Ideal.ext
  intro S
  rfl

@[simp] theorem pushforward_comp
    {K : Type v} {L : Type w}
    (J : Ideal I)
    (f : I -> K)
    (g : K -> L) :
    (J.pushforward f).pushforward g = J.pushforward (g ∘ f) := by
  apply Ideal.ext
  intro S
  rfl

/-! The pushforward of an ultrafilter-dual ideal is principal at `k0`
exactly when the original ideal is eventually concentrated on the fiber over
`k0`. No injectivity of the map is required. -/
theorem IsUltrafilterDual.pushforward_eq_excludePoint_iff_eventually_eq
    {K : Type v}
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (f : I -> K)
    (k0 : K) :
    J.pushforward f = excludePoint k0 <->
      J.Eventually (fun i => f i = k0) := by
  constructor
  · intro hPush
    have hEventually :
        (J.pushforward f).Eventually (fun k => k = k0) := by
      rw [hPush]
      exact (excludePoint_eventually_iff k0 _).mpr rfl
    exact (pushforward_eventually_iff J f _).mp hEventually
  · intro hEventually
    change J.Small (fun i => Not (f i = k0)) at hEventually
    apply Ideal.ext
    intro S
    constructor
    · intro hSmall hSk0
      change J.Small (fun i => S (f i)) at hSmall
      apply hJ.isProper
      exact J.subset_small (J.union_small hSmall hEventually) (by
        intro i _
        by_cases hi : f i = k0
        · exact Or.inl (by simpa only [hi] using hSk0)
        · exact Or.inr hi)
    · intro hNotSk0
      change J.Small (fun i => S (f i))
      exact J.subset_small hEventually (by
        intro i hSfi hi
        apply hNotSk0
        simpa only [hi] using hSfi)

/-! A nonprincipal ultrafilter-dual ideal makes every singleton small. -/
theorem IsUltrafilterDual.singleton_small_of_ne_excludePoint
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    {i0 : I}
    (hNonprincipal : Not (J = excludePoint i0)) :
    J.Small (fun i => i = i0) := by
  cases hJ.small_or_compl_small (fun i => i = i0) with
  | inl hSmall =>
      exact hSmall
  | inr hComplSmall =>
      exfalso
      apply hNonprincipal
      have hPush :
          J.pushforward (fun i => i) = excludePoint i0 :=
        (hJ.pushforward_eq_excludePoint_iff_eventually_eq
          (fun i => i) i0).mpr hComplSmall
      simpa only [pushforward_id] using hPush

/-! If no point is principal, every finite subset of the index type is small. -/
theorem IsUltrafilterDual.finset_small_of_forall_ne_excludePoint
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (hNonprincipal : forall i, Not (J = excludePoint i))
    (s : Finset I) :
    J.Small (fun i => Membership.mem s i) := by
  have hUnion :
      J.Small (fun i => exists k, Membership.mem s k /\ i = k) :=
    (J.finset_small_iff s (fun k i => i = k)).mpr (by
      intro k hk
      exact hJ.singleton_small_of_ne_excludePoint (hNonprincipal k))
  exact J.subset_small hUnion (by
    intro i hi
    exact ⟨i, hi, rfl⟩)

/-! The corresponding eventual statement says that a nonprincipal
ultrafilter-dual ideal eventually avoids every finite set. -/
theorem IsUltrafilterDual.eventually_not_mem_finset_of_forall_ne_excludePoint
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (hNonprincipal : forall i, Not (J = excludePoint i))
    (s : Finset I) :
    J.Eventually (fun i => Not (Membership.mem s i)) := by
  classical
  change J.Small (fun i => Not (Not (Membership.mem s i)))
  exact J.subset_small
    (hJ.finset_small_of_forall_ne_excludePoint hNonprincipal s)
    (by
      intro i hNotNot
      exact Classical.byContradiction hNotNot)

/-! Localize an ideal to a predicate `X`.  A set is small in the localized
ideal exactly when its intersection with `X` was small in the original
ideal.  Thus reduced-product comparison modulo `J.localize X` is comparison
"on `X`" in the sense used in the PCF decomposition lemmas. -/
def localize (J : Ideal I) (X : I -> Prop) : Ideal I where
  Small S := J.Small (fun i => S i /\ X i)
  empty_small := by
    exact J.subset_small J.empty_small (by
      intro i h
      exact h.1)
  subset_small := by
    intro A B hA hBA
    exact J.subset_small hA (by
      intro i hi
      exact ⟨hBA i hi.1, hi.2⟩)
  union_small := by
    intro A B hA hB
    exact J.subset_small (J.union_small hA hB) (by
      intro i hi
      cases hi.1 with
      | inl hAi => exact Or.inl ⟨hAi, hi.2⟩
      | inr hBi => exact Or.inr ⟨hBi, hi.2⟩)

@[simp] theorem localize_small_iff
    (J : Ideal I) (X S : I -> Prop) :
    (J.localize X).Small S <-> J.Small (fun i => S i /\ X i) :=
  Iff.rfl

@[simp] theorem localize_isProper_iff
    (J : Ideal I) (X : I -> Prop) :
    (J.localize X).IsProper <-> Not (J.Small X) := by
  change (Not (J.Small (fun i => True /\ X i))) <-> Not (J.Small X)
  simp only [true_and]

@[simp] theorem localize_eventually_iff
    (J : Ideal I) (X P : I -> Prop) :
    (J.localize X).Eventually P <->
      J.Small (fun i => Not (P i) /\ X i) :=
  Iff.rfl

theorem le_localize (J : Ideal I) (X : I -> Prop) :
    Ideal.Le J (J.localize X) := by
  intro S hS
  exact J.subset_small hS (by
    intro i hi
    exact hi.1)

@[simp] theorem localize_true (J : Ideal I) :
    J.localize (fun _ => True) = J := by
  apply Ideal.ext
  intro S
  change J.Small (fun i => S i /\ True) <-> J.Small S
  simp only [and_true]

@[simp] theorem localize_localize
    (J : Ideal I) (X Y : I -> Prop) :
    (J.localize X).localize Y =
      J.localize (fun i => X i /\ Y i) := by
  apply Ideal.ext
  intro S
  change J.Small (fun i => (S i /\ Y i) /\ X i) <->
    J.Small (fun i => S i /\ (X i /\ Y i))
  constructor
  · intro h
    exact J.subset_small h (by
      intro i hi
      exact ⟨⟨hi.1, hi.2.2⟩, hi.2.1⟩)
  · intro h
    exact J.subset_small h (by
      intro i hi
      exact ⟨hi.1.1, ⟨hi.2, hi.1.2⟩⟩)

/-! Localizing a pushforward ideal is the pushforward of the localization by
the pulled-back predicate.  This identifies the positive pieces seen on the
target with predicates on the original index type. -/
@[simp] theorem pushforward_localize
    {K : Type v}
    (J : Ideal I)
    (f : I -> K)
    (X : K -> Prop) :
    (J.pushforward f).localize X =
      (J.localize (fun i => X (f i))).pushforward f := by
  apply Ideal.ext
  intro S
  rfl

/-- Restrict an ideal on `K` along a map `f : I -> K`. A predicate on `I`
is small when its direct image is small in `K`. -/
def restrictAlong
    {K : Type v}
    (J : Ideal K)
    (f : I -> K) : Ideal I where
  Small S := J.Small (fun k => exists i, f i = k /\ S i)
  empty_small := by
    exact J.subset_small J.empty_small (by
      intro k h
      obtain ⟨i, _, hFalse⟩ := h
      exact hFalse)
  subset_small := by
    intro A B hA hBA
    exact J.subset_small hA (by
      intro k hB
      obtain ⟨i, hi, hBi⟩ := hB
      exact ⟨i, hi, hBA i hBi⟩)
  union_small := by
    intro A B hA hB
    exact J.subset_small (J.union_small hA hB) (by
      intro k h
      obtain ⟨i, hi, hAi | hBi⟩ := h
      · exact Or.inl ⟨i, hi, hAi⟩
      · exact Or.inr ⟨i, hi, hBi⟩)

@[simp] theorem restrictAlong_small_iff
    {K : Type v}
    (J : Ideal K)
    (f : I -> K)
    (S : I -> Prop) :
    (J.restrictAlong f).Small S <->
      J.Small (fun k => exists i, f i = k /\ S i) :=
  Iff.rfl

/-! If an ideal regards the image of `S` as eventual, then its restriction
along an injection regards `S` itself as eventual.  Injectivity is exactly
what makes the image of the complement disjoint from the image of `S`. -/
theorem restrictAlong_eventually_of_eventually_image
    {K : Type v}
    (J : Ideal K)
    (f : I -> K)
    (hf : Function.Injective f)
    (S : I -> Prop)
    (hImage : J.Eventually
      (fun k => exists i, f i = k /\ S i)) :
    (J.restrictAlong f).Eventually S := by
  exact J.subset_small hImage (by
    intro k hImageNotS hImageS
    obtain ⟨i, hik, hNotSi⟩ := hImageNotS
    obtain ⟨j, hjk, hSj⟩ := hImageS
    have hij : i = j := hf (hik.trans hjk.symm)
    exact hNotSi (hij ▸ hSj))

/-- If `J` concentrates on the range of `f`, restricting to the domain and
pushing forward again recovers `J`. -/
theorem restrictAlong_pushforward_eq
    {K : Type v}
    (J : Ideal K)
    (f : I -> K)
    (hRange : J.Eventually (fun k => exists i, f i = k)) :
    (J.restrictAlong f).pushforward f = J := by
  apply Ideal.ext
  intro S
  constructor
  · intro hImage
    exact J.subset_small (J.union_small hImage hRange) (by
      intro k hSk
      by_cases hk : exists i, f i = k
      · obtain ⟨i, hi⟩ := hk
        exact Or.inl ⟨i, hi, by simpa only [hi] using hSk⟩
      · exact Or.inr hk)
  · intro hS
    exact J.subset_small hS (by
      intro k hImage
      obtain ⟨i, hi, hSfi⟩ := hImage
      simpa only [hi] using hSfi)

/-- An ultrafilter concentrated on the range of an injection induces an
ultrafilter on the injection's domain. -/
theorem IsUltrafilterDual.restrictAlong
    {K : Type v}
    {J : Ideal K}
    (hJ : J.IsUltrafilterDual)
    (f : I -> K)
    (hf : Function.Injective f)
    (hRange : J.Eventually (fun k => exists i, f i = k)) :
    (J.restrictAlong f).IsUltrafilterDual := by
  constructor
  · intro hUniv
    apply hJ.isProper
    rw [← J.restrictAlong_pushforward_eq f hRange]
    exact hUniv
  · intro S
    let imageS : K -> Prop := fun k => exists i, f i = k /\ S i
    cases hJ.small_or_compl_small imageS with
    | inl hSmall =>
        exact Or.inl hSmall
    | inr hComplSmall =>
        exact Or.inr (J.subset_small hComplSmall (by
          intro k hImageNot hImage
          obtain ⟨i, hi, hNotSi⟩ := hImageNot
          obtain ⟨j, hj, hSj⟩ := hImage
          have hij : i = j := hf (hi.trans hj.symm)
          exact hNotSi (hij ▸ hSj)))

def extendBy (B : I -> Prop) : Ideal I where
  Small S := exists T : I -> Prop, J.Small T /\ forall i, S i -> T i \/ B i
  empty_small := by
    exact Exists.intro (fun _ => False)
      (And.intro J.empty_small (by
        intro i hFalse
        exact False.elim hFalse))
  subset_small := by
    intro A BSet hA hSubset
    cases hA with
    | intro T hT =>
        exact Exists.intro T
          (And.intro hT.left (by
            intro i hBSet
            exact hT.right i (hSubset i hBSet)))
  union_small := by
    intro A BSet hA hBSet
    cases hA with
    | intro TA hTA =>
        cases hBSet with
        | intro TB hTB =>
            exact Exists.intro (fun i => TA i \/ TB i)
              (And.intro (J.union_small hTA.left hTB.left) (by
                intro i hUnion
                cases hUnion with
                | inl hAi =>
                    cases hTA.right i hAi with
                    | inl hTAi =>
                        exact Or.inl (Or.inl hTAi)
                    | inr hBi =>
                        exact Or.inr hBi
                | inr hBSeti =>
                    cases hTB.right i hBSeti with
                    | inl hTBi =>
                        exact Or.inl (Or.inr hTBi)
                    | inr hBi =>
                        exact Or.inr hBi))

theorem le_refl (J : Ideal I) :
    Le J J := by
  intro S hS
  exact hS

theorem le_trans
    {J1 J2 J3 : Ideal I}
    (h12 : Le J1 J2)
    (h23 : Le J2 J3) :
    Le J1 J3 := by
  intro S hS
  exact h23 S (h12 S hS)

theorem le_of_equivalent_left
    {J1 J2 : Ideal I}
    (h : Equivalent J1 J2) :
    Le J1 J2 :=
  h.left

theorem le_of_equivalent_right
    {J1 J2 : Ideal I}
    (h : Equivalent J1 J2) :
    Le J2 J1 :=
  h.right

theorem small_in_extendBy
    {S B : I -> Prop}
    (hS : J.Small S) :
    (J.extendBy B).Small S := by
  exact Exists.intro S
    (And.intro hS (by
      intro i hSi
      exact Or.inl hSi))

theorem le_extendBy
    (B : I -> Prop) :
    Le J (J.extendBy B) := by
  intro S hS
  exact J.small_in_extendBy hS

theorem generator_small_in_extendBy
    (B : I -> Prop) :
    (J.extendBy B).Small B := by
  exact Exists.intro (fun _ => False)
    (And.intro J.empty_small (by
      intro i hBi
      exact Or.inr hBi))

theorem extendBy_isProper_iff_not_eventually
    (B : I -> Prop) :
    IsProper (J.extendBy B) <-> Not (J.Eventually B) := by
  classical
  constructor
  · intro hProper hEventually
    apply hProper
    exact Exists.intro (fun i => Not (B i))
      (And.intro hEventually (by
        intro i _
        by_cases hBi : B i
        · exact Or.inr hBi
        · exact Or.inl hBi))
  · intro hNotEventually hUniv
    apply hNotEventually
    obtain ⟨T, hT, hCover⟩ := hUniv
    exact J.subset_small hT (by
      intro i hNotBi
      cases hCover i True.intro with
      | inl hTi => exact hTi
      | inr hBi => exact False.elim (hNotBi hBi))

theorem IsProper.not_eventually_false
    {J : Ideal I}
    (hProper : IsProper J) :
    Not (J.Eventually (fun _ => False)) := by
  simpa only [Eventually, not_false_eq_true] using hProper

theorem IsProper.not_eventually_of_forall_not
    {J : Ideal I}
    (hProper : IsProper J)
    {P : I -> Prop}
    (hP : forall i, Not (P i)) :
    Not (J.Eventually P) := by
  intro hEventually
  apply hProper
  exact J.subset_small hEventually (by
    intro i _
    exact hP i)

theorem eventually_mono
    {P Q : I -> Prop}
    (hP : J.Eventually P)
    (hPQ : forall i, P i -> Q i) :
    J.Eventually Q := by
  exact J.subset_small hP (by
    intro i hnotQ hPi
    exact hnotQ (hPQ i hPi))

/-! On `Nat`, a nonprincipal ultrafilter-dual ideal is eventually above every
fixed threshold. This is finite avoidance applied to the corresponding
initial segment. -/
theorem IsUltrafilterDual.eventually_nat_lt_of_forall_ne_excludePoint
    {J : Ideal Nat}
    (hJ : J.IsUltrafilterDual)
    (hNonprincipal : forall i, Not (J = excludePoint i))
    (n : Nat) :
    J.Eventually (fun m => n < m) := by
  have hAvoid :=
    hJ.eventually_not_mem_finset_of_forall_ne_excludePoint
      hNonprincipal (Finset.range (n + 1))
  exact J.eventually_mono hAvoid (by
    intro m hm
    simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hm)

theorem eventually_congr
    {P Q : I -> Prop}
    (hPQ : forall i, P i <-> Q i) :
    J.Eventually P <-> J.Eventually Q := by
  constructor
  · intro hP
    exact J.eventually_mono hP (by
      intro i hPi
      exact (hPQ i).mp hPi)
  · intro hQ
    exact J.eventually_mono hQ (by
      intro i hQi
      exact (hPQ i).mpr hQi)

theorem IsUltrafilterDual.eventually_or_eventually_not
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (P : I -> Prop) :
    J.Eventually P \/ J.Eventually (fun i => Not (P i)) := by
  classical
  cases hJ.small_or_compl_small P with
  | inl hSmall =>
      have hEventuallyNot : J.Eventually (fun i => Not (P i)) := by
        change J.Small (fun i => Not (Not (P i)))
        exact J.subset_small hSmall (by
          intro i hNotNot
          exact Classical.byContradiction hNotNot)
      exact Or.inr hEventuallyNot
  | inr hComplSmall =>
      exact Or.inl hComplSmall

/- theorem IsUltrafilterDual.exists_eventually_of_finset_cover
    {L : Type v}
    {P : L -> I -> Prop}
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (s : Finset L)
    (hCover : J.Eventually (fun i => exists j, j 鈭?s /\\ P j i)) :
    exists j, j 鈭?s /\\ J.Eventually (P j) := by
  classical
  revert hCover
  induction s using Finset.induction_on with
  | empty =>
      intro hCover
      have hFalse : J.Eventually (fun _ => False) :=
        J.eventually_mono hCover (by
          intro i hExists
          obtain 鉄╥, hi, _hP鉄?:= hExists
          simp at hi)
      exact False.elim (hJ.isProper.not_eventually_false hFalse)
  | @insert j s hj ih =>
      intro hCover
      cases hJ.eventually_or_eventually_not (P j) with
      | inl hPj =>
          exact 鉄╥, Finset.mem_insert_self j s, hPj鉄?
      | inr hNotPj =>
          have hRest :
              J.Eventually (fun i => exists k, k 鈭?s /\\ P k i) := by
            have hAnd := J.eventually_and hCover hNotPj
            apply J.eventually_mono hAnd
            intro i hBoth
            obtain 鉄╥, hi, hPi鉄?:= hBoth.1
            rcases Finset.mem_insert.mp hi with rfl | hi
            路 exact False.elim (hBoth.2 hPi)
            路 exact 鉄╥, hi, hPi鉄?
          obtain 鉄╥, hi, hPi鉄?:= ih hRest
          exact 鉄╥, Finset.mem_insert_of_mem hi, hPi鉄?

 -/

theorem eventually_of_forall
    {P : I -> Prop}
    (hP : forall i, P i) :
    J.Eventually P := by
  exact J.subset_small J.empty_small (by
    intro i hnotP
    exact hnotP (hP i))

theorem eventually_and
    {P Q : I -> Prop}
    (hP : J.Eventually P)
    (hQ : J.Eventually Q) :
    J.Eventually (fun i => P i /\ Q i) := by
  classical
  exact J.subset_small (J.union_small hP hQ) (by
    intro i hnotAnd
    exact
      if hPi : P i then
        Or.inr (by
          intro hQi
          exact hnotAnd (And.intro hPi hQi))
      else
        Or.inl hPi)

/-! The ideal-dual form of the Fubini sum of a family of filters.  A set is
small in the flattened ideal exactly when, for outer-almost every index, it
is small in the corresponding inner ideal.  The inner ideals all live on the
same coordinate type, which is the form used to flatten iterated canonical
products in Lemma 24.24. -/
def fubini
    {K : Type v}
    (J : Ideal I)
    (D : I -> Ideal K) : Ideal K where
  Small S := J.Eventually (fun i => (D i).Small S)
  empty_small := J.eventually_of_forall (fun i => (D i).empty_small)
  subset_small := by
    intro A B hA hBA
    exact J.eventually_mono hA (fun i hi =>
      (D i).subset_small hi hBA)
  union_small := by
    intro A B hA hB
    exact J.eventually_mono (J.eventually_and hA hB) (fun i hi =>
      (D i).union_small hi.1 hi.2)

@[simp] theorem fubini_small_iff
    {K : Type v}
    (J : Ideal I)
    (D : I -> Ideal K)
    (S : K -> Prop) :
    (J.fubini D).Small S <->
      J.Eventually (fun i => (D i).Small S) :=
  Iff.rfl

@[simp] theorem fubini_eventually_iff
    {K : Type v}
    (J : Ideal I)
    (D : I -> Ideal K)
    (P : K -> Prop) :
    (J.fubini D).Eventually P <->
      J.Eventually (fun i => (D i).Eventually P) :=
  Iff.rfl

/-! A Fubini sum of ultrafilter-dual ideals is again ultrafilter-dual.  The
outer ultrafilter first decides which inner ideals regard a predicate as
small; on the complementary outer-large set, inner ultrafilter maximality
forces the predicate's complement to be small. -/
theorem IsUltrafilterDual.fubini
    {K : Type v}
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (D : I -> Ideal K)
    (hD : forall i, (D i).IsUltrafilterDual) :
    (J.fubini D).IsUltrafilterDual := by
  constructor
  · intro hUniv
    exact hJ.isProper.not_eventually_of_forall_not
      (fun i => (hD i).isProper) hUniv
  · intro S
    cases hJ.eventually_or_eventually_not (fun i => (D i).Small S) with
    | inl hSmall =>
        exact Or.inl hSmall
    | inr hNotSmall =>
        right
        exact J.eventually_mono hNotSmall (by
          intro i hi
          cases (hD i).small_or_compl_small S with
          | inl hSmall => exact False.elim (hi hSmall)
          | inr hCompl => exact hCompl)

theorem IsUltrafilterDual.exists_eventually_of_finset_cover
    {L : Type v}
    {P : L -> I -> Prop}
    {J : Ideal I}
    (hJ : J.IsUltrafilterDual)
    (s : Finset L)
    (hCover : J.Eventually
      (fun i => exists j, Membership.mem s j /\ P j i)) :
    exists j, Membership.mem s j /\ J.Eventually (P j) := by
  classical
  revert hCover
  induction s using Finset.induction_on with
  | empty =>
      intro hCover
      have hFalse : J.Eventually (fun _ => False) :=
        J.eventually_mono hCover (by
          intro i hExists
          obtain ⟨j, hj, _hP⟩ := hExists
          simp at hj)
      exact False.elim (hJ.isProper.not_eventually_false hFalse)
  | @insert j s hj ih =>
      intro hCover
      cases hJ.eventually_or_eventually_not (P j) with
      | inl hPj =>
          exact ⟨j, Finset.mem_insert_self j s, hPj⟩
      | inr hNotPj =>
          have hRest : J.Eventually
              (fun i => exists k, Membership.mem s k /\ P k i) := by
            have hAnd := J.eventually_and hCover hNotPj
            apply J.eventually_mono hAnd
            intro i hBoth
            obtain ⟨k, hk, hPk⟩ := hBoth.1
            rcases Finset.mem_insert.mp hk with rfl | hk
            · exact False.elim (hBoth.2 hPk)
            · exact ⟨k, hk, hPk⟩
          obtain ⟨k, hk, hPk⟩ := ih hRest
          exact ⟨k, Finset.mem_insert_of_mem hk, hPk⟩

end Ideal

/-- The coordinate preorders and ideal needed to form an abstract reduced product. -/
structure ReducedProductFrame where
  Index : Type u
  Coord : Index -> Type v
  le : forall i, Coord i -> Coord i -> Prop
  le_refl : forall i (a : Coord i), le i a a
  le_trans :
    forall i {a b c : Coord i}, le i a b -> le i b c -> le i a c
  J : Ideal Index

/-- A choice of one element from each coordinate of a reduced-product frame. -/
abbrev ProductElement (F : ReducedProductFrame.{u, v}) : Type (max u v) :=
  (i : F.Index) -> F.Coord i

namespace ReducedProductFrame

variable (F : ReducedProductFrame.{u, v})

/-- Pointwise comparison outside a set that is small for the frame's ideal. -/
def eventuallyLe (x y : ProductElement F) : Prop :=
  F.J.Eventually (fun i => F.le i (x i) (y i))

theorem eventuallyLe_of_forallLe
    {x y : ProductElement F}
    (hxy : forall i, F.le i (x i) (y i)) :
    F.eventuallyLe x y := by
  exact F.J.eventually_of_forall hxy

theorem eventuallyLe_refl
    (x : ProductElement F) :
    F.eventuallyLe x x := by
  exact F.eventuallyLe_of_forallLe (by
    intro i
    exact F.le_refl i (x i))

theorem eventuallyLe_trans
    {x y z : ProductElement F}
    (hxy : F.eventuallyLe x y)
    (hyz : F.eventuallyLe y z) :
    F.eventuallyLe x z := by
  classical
  exact F.J.subset_small (F.J.union_small hxy hyz) (by
    intro i hnotxz
    exact
      if hxyi : F.le i (x i) (y i) then
        Or.inr (by
          intro hyzi
          exact hnotxz (F.le_trans i hxyi hyzi))
      else
        Or.inl hxyi)

end ReducedProductFrame

/-! ### Zorn construction of a nonprincipal ultrafilter-dual ideal

The following construction is included because the infinite-index boundary is
semantic, not merely an unavailable-library issue.  Start with the finite-set
ideal, take a maximal proper ideal family containing it, and use maximality to
decide every predicate.  The resulting ultrafilter-dual ideal contains every
singleton, so it cannot be `excludePoint` at any coordinate.
-/

def IdealFamilyIsIdeal {I : Type u} (M : Set (I -> Prop)) : Prop :=
  (fun _ : I => False) ∈ M /\
    (forall {A B : I -> Prop}, A ∈ M ->
      (forall i, B i -> A i) -> B ∈ M) /\
    (forall {A B : I -> Prop}, A ∈ M -> B ∈ M ->
      (fun i => A i \/ B i) ∈ M)

def IdealFamilyIsProper {I : Type u} (M : Set (I -> Prop)) : Prop :=
  Not ((fun _ : I => True) ∈ M)

def IdealFamilyIsGood {I : Type u} (M : Set (I -> Prop)) : Prop :=
  IdealFamilyIsIdeal M /\ IdealFamilyIsProper M

def finiteIdealFamily (I : Type u) : Set (I -> Prop) :=
  {S | Set.Finite {i : I | S i}}

theorem finiteIdealFamily_isIdeal {I : Type u} :
    IdealFamilyIsIdeal (finiteIdealFamily I) := by
  constructor
  · change Set.Finite {i : I | False}
    simp
  · constructor
    · intro A B hA hBA
      change Set.Finite {i : I | A i} at hA
      change Set.Finite {i : I | B i}
      exact hA.subset (by
        intro i hi
        exact hBA i hi)
    · intro A B hA hB
      change Set.Finite {i : I | A i} at hA
      change Set.Finite {i : I | B i} at hB
      change Set.Finite {i : I | A i \/ B i}
      exact hA.union hB

theorem finiteIdealFamily_isGood {I : Type u} [Infinite I] :
    IdealFamilyIsGood (finiteIdealFamily I) := by
  refine ⟨finiteIdealFamily_isIdeal, ?_⟩
  intro hUniv
  change Set.Finite {i : I | True} at hUniv
  exact (Set.infinite_univ (α := I)) (by simpa using hUniv)

theorem idealFamily_union_isGood
    {I : Type u}
    {c : Set (Set (I -> Prop))}
    (hc : IsChain (· ⊆ ·) c)
    (hcNonempty : c.Nonempty)
    (hcGood : forall (M : Set (I -> Prop)), M ∈ c -> IdealFamilyIsGood M) :
    IdealFamilyIsGood (⋃₀ c) := by
  constructor
  · constructor
    · obtain ⟨M, hMc⟩ := hcNonempty
      exact Set.mem_sUnion.mpr ⟨M, hMc, (hcGood M hMc).1.1⟩
    · constructor
      · intro A B hA hBA
        obtain ⟨M, hMc, hAM⟩ := Set.mem_sUnion.mp hA
        apply Set.mem_sUnion.mpr
        exact ⟨M, hMc, (hcGood M hMc).1.2.1 hAM hBA⟩
      · intro A B hA hB
        obtain ⟨M, hMc, hAM⟩ := Set.mem_sUnion.mp hA
        obtain ⟨N, hNc, hBN⟩ := Set.mem_sUnion.mp hB
        by_cases hMN : M = N
        · subst N
          apply Set.mem_sUnion.mpr
          exact ⟨M, hMc, (hcGood M hMc).1.2.2 hAM hBN⟩
        · rcases hc hMc hNc hMN with hMN | hNM
          · apply Set.mem_sUnion.mpr
            refine ⟨N, hNc, ?_⟩
            exact (hcGood N hNc).1.2.2
              (hMN hAM) hBN
          · apply Set.mem_sUnion.mpr
            refine ⟨M, hMc, ?_⟩
            exact (hcGood M hMc).1.2.2
              hAM (hNM hBN)
  · intro hUniv
    obtain ⟨M, hMc, hMUniv⟩ := Set.mem_sUnion.mp hUniv
    exact (hcGood M hMc).2 hMUniv

theorem exists_maximal_good_idealFamily
    {I : Type u} [Infinite I] :
    exists M : Set (I -> Prop),
      IdealFamilyIsGood M /\
        finiteIdealFamily I ⊆ M /\
        forall N, IdealFamilyIsGood N -> M ⊆ N -> N ⊆ M := by
  let S : Set (Set (I -> Prop)) := {M | IdealFamilyIsGood M}
  obtain ⟨M, hFiniteM, hMax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hcChain hcNonempty => by
        refine ⟨⋃₀ c, ?_, ?_⟩
        · exact idealFamily_union_isGood hcChain hcNonempty hcS
        · intro N hNc
          exact Set.subset_sUnion_of_mem hNc)
      (finiteIdealFamily I)
      (finiteIdealFamily_isGood (I := I))
  refine ⟨M, hMax.1, hFiniteM, ?_⟩
  intro N hN hMN
  exact hMax.2 hN hMN

/-! The same Zorn argument starts above any already proper ideal family.
    This is the extension form needed when a PCF construction first fixes a
    collection of sets that must be small and only then chooses an
    ultrafilter-dual ideal. -/
theorem exists_maximal_good_idealFamily_above
    {I : Type u}
    {M0 : Set (I -> Prop)}
    (hM0 : IdealFamilyIsGood M0) :
    exists M : Set (I -> Prop),
      IdealFamilyIsGood M /\
        M0 ⊆ M /\
        forall N, IdealFamilyIsGood N -> M ⊆ N -> N ⊆ M := by
  let S : Set (Set (I -> Prop)) := {M | IdealFamilyIsGood M}
  obtain ⟨M, hM0M, hMax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hcChain hcNonempty => by
        refine ⟨⋃₀ c, ?_, ?_⟩
        · exact idealFamily_union_isGood hcChain hcNonempty hcS
        · intro N hNc
          exact Set.subset_sUnion_of_mem hNc)
      M0 hM0
  refine ⟨M, hMax.1, hM0M, ?_⟩
  intro N hN hMN
  exact hMax.2 hN hMN

def idealFamilyAdjoin {I : Type u}
    (M : Set (I -> Prop)) (S : I -> Prop) : Set (I -> Prop) :=
  {B | exists A, A ∈ M /\ forall i, B i -> A i \/ S i}

theorem idealFamilyAdjoin_isIdeal
    {I : Type u}
    {M : Set (I -> Prop)}
    (hM : IdealFamilyIsIdeal M)
    (S : I -> Prop) :
    IdealFamilyIsIdeal (idealFamilyAdjoin M S) := by
  constructor
  · refine ⟨fun _ => False, hM.1, ?_⟩
    intro i hFalse
    exact False.elim hFalse
  · constructor
    · intro A B hA hBA
      obtain ⟨C, hCM, hCover⟩ := hA
      refine ⟨C, hCM, ?_⟩
      intro i hBi
      exact hCover i (hBA i hBi)
    · intro A B hA hB
      obtain ⟨C, hCM, hCoverC⟩ := hA
      obtain ⟨D, hDM, hCoverD⟩ := hB
      refine ⟨fun i => C i \/ D i, hM.2.2 hCM hDM, ?_⟩
      intro i hAB
      cases hAB with
      | inl hAi =>
          rcases hCoverC i hAi with hCi | hSi
          · exact Or.inl (Or.inl hCi)
          · exact Or.inr hSi
      | inr hBi =>
          rcases hCoverD i hBi with hDi | hSi
          · exact Or.inl (Or.inr hDi)
          · exact Or.inr hSi

theorem idealFamily_subset_adjoin
    {I : Type u}
    {M : Set (I -> Prop)}
    (S : I -> Prop) :
    M ⊆ idealFamilyAdjoin M S := by
  intro A hAM
  exact ⟨A, hAM, by
    intro i hAi
    exact Or.inl hAi⟩

theorem idealFamily_adjoin_mem
    {I : Type u}
    {M : Set (I -> Prop)}
    (hM : IdealFamilyIsIdeal M)
    (S : I -> Prop) :
    S ∈ idealFamilyAdjoin M S := by
  exact ⟨fun _ => False, hM.1, by
    intro i hSi
    exact Or.inr hSi⟩

theorem idealFamily_compl_mem_of_maximal
    {I : Type u}
    {M : Set (I -> Prop)}
    (hMIdeal : IdealFamilyIsIdeal M)
    (_hMProper : IdealFamilyIsProper M)
    (hMax : forall N, IdealFamilyIsGood N -> M ⊆ N -> N ⊆ M)
    (S : I -> Prop) :
    S ∈ M \/ (fun i => Not (S i)) ∈ M := by
  by_cases hSM : S ∈ M
  · exact Or.inl hSM
  · right
    let N := idealFamilyAdjoin M S
    have hNIdeal : IdealFamilyIsIdeal N :=
      idealFamilyAdjoin_isIdeal hMIdeal S
    have hMsubset : M ⊆ N :=
      idealFamily_subset_adjoin S
    have hNnotProper : Not (IdealFamilyIsProper N) := by
      intro hNProper
      have hNGood : IdealFamilyIsGood N := ⟨hNIdeal, hNProper⟩
      have hNsubset : N ⊆ M := hMax N hNGood hMsubset
      exact hSM (hNsubset (idealFamily_adjoin_mem hMIdeal S))
    have hUniv : (fun _ : I => True) ∈ N := by
      by_contra hNotUniv
      exact hNnotProper hNotUniv
    obtain ⟨A, hAM, hCover⟩ := hUniv
    apply hMIdeal.2.1 hAM
    intro i hNotSi
    rcases hCover i True.intro with hAi | hSi
    · exact hAi
    · exact False.elim (hNotSi hSi)

def idealOfFamily {I : Type u}
    (M : Set (I -> Prop))
    (hM : IdealFamilyIsIdeal M) : Ideal I where
  Small S := S ∈ M
  empty_small := hM.1
  subset_small := hM.2.1
  union_small := hM.2.2

namespace Ideal

/-! The ideal of finite predicates, exposed as an actual `Ideal` so it can be
    used as the base of the family-extension construction below. -/
def finiteSet (I : Type u) : Ideal I :=
  idealOfFamily (finiteIdealFamily I) finiteIdealFamily_isIdeal

theorem finiteSet_small_iff
    {I : Type u}
    (S : I -> Prop) :
    (finiteSet I).Small S <-> Set.Finite {i : I | S i} :=
  Iff.rfl

theorem finiteSet_isProper
    {I : Type u} [Infinite I] :
    (finiteSet I).IsProper :=
  (finiteIdealFamily_isGood (I := I)).2

end Ideal

/-! The finite union of a predicate family.  It is kept separate from the
    generated ideal family below so later reduced-product arguments can state
    the exact finite-compatibility condition they need. -/
def finitePredicateUnion
    {I : Type u} {K : Type w}
    (P : K -> I -> Prop)
    (s : Finset K) : I -> Prop :=
  fun i => exists k, k ∈ s /\ P k i

/-! Adjoin an arbitrary predicate family to an ideal in one step.  Membership
    means containment in the union of one old-small set and finitely many of
    the predicates being adjoined. -/
def idealFamilyAdjoinFamily
    {I : Type u} {K : Type w}
    (J : Ideal I)
    (P : K -> I -> Prop) : Set (I -> Prop) :=
  {S | exists T : I -> Prop,
    J.Small T /\
      exists s : Finset K,
        forall i, S i -> T i \/ finitePredicateUnion P s i}

theorem idealFamilyAdjoinFamily_isIdeal
    {I : Type u} {K : Type w}
    (J : Ideal I)
    (P : K -> I -> Prop) :
    IdealFamilyIsIdeal (idealFamilyAdjoinFamily J P) := by
  classical
  constructor
  · refine ⟨fun _ => False, J.empty_small, ∅, ?_⟩
    intro i hFalse
    exact False.elim hFalse
  · constructor
    · intro A B hA hBA
      obtain ⟨T, hT, s, hCover⟩ := hA
      exact ⟨T, hT, s, fun i hBi => hCover i (hBA i hBi)⟩
    · intro A B hA hB
      obtain ⟨T, hT, s, hCoverA⟩ := hA
      obtain ⟨U, hU, t, hCoverB⟩ := hB
      refine ⟨fun i => T i \/ U i, J.union_small hT hU, s ∪ t, ?_⟩
      intro i hAB
      cases hAB with
      | inl hAi =>
          rcases hCoverA i hAi with hTi | hPi
          · exact Or.inl (Or.inl hTi)
          · obtain ⟨k, hks, hPki⟩ := hPi
            exact Or.inr ⟨k, by simp [hks], hPki⟩
      | inr hBi =>
          rcases hCoverB i hBi with hUi | hPi
          · exact Or.inl (Or.inr hUi)
          · obtain ⟨k, hkt, hPki⟩ := hPi
            exact Or.inr ⟨k, by simp [hkt], hPki⟩

theorem idealFamilyAdjoinFamily_isGood
    {I : Type u} {K : Type w}
    (J : Ideal I)
    (P : K -> I -> Prop)
    (hCompatible : forall s : Finset K,
      (J.extendBy (finitePredicateUnion P s)).IsProper) :
    IdealFamilyIsGood (idealFamilyAdjoinFamily J P) := by
  refine ⟨idealFamilyAdjoinFamily_isIdeal J P, ?_⟩
  intro hUniv
  obtain ⟨T, hT, s, hCover⟩ := hUniv
  apply hCompatible s
  exact ⟨T, hT, fun i _ => hCover i True.intro⟩

theorem idealFamily_subset_adjoinFamily
    {I : Type u} {K : Type w}
    (J : Ideal I)
    (P : K -> I -> Prop) :
    {S : I -> Prop | J.Small S} ⊆ idealFamilyAdjoinFamily J P := by
  classical
  intro S hS
  exact ⟨S, hS, ∅, fun i hSi => Or.inl hSi⟩

theorem idealFamilyAdjoinFamily_mem
    {I : Type u} {K : Type w}
    (J : Ideal I)
    (P : K -> I -> Prop)
    (k : K) :
    P k ∈ idealFamilyAdjoinFamily J P := by
  classical
  refine ⟨fun _ => False, J.empty_small, {k}, ?_⟩
  intro i hPki
  exact Or.inr ⟨k, by simp, hPki⟩

/-! A compactness form of the ultrafilter lemma for ideals.  If adjoining
    every finite subfamily preserves properness, one ultrafilter-dual ideal
    extends the original ideal and contains the whole family.  This is the
    form needed to choose a quotient in which every member of a proposed
    cofinal family fails a prescribed eventual comparison. -/
theorem exists_ultrafilterDual_ideal_extending_family
    {I : Type u} {K : Type w}
    (J0 : Ideal I)
    (P : K -> I -> Prop)
    (hCompatible : forall s : Finset K,
      (J0.extendBy (finitePredicateUnion P s)).IsProper) :
    exists J : Ideal I,
      J.IsUltrafilterDual /\
        Ideal.Le J0 J /\
        forall k, J.Small (P k) := by
  let M0 : Set (I -> Prop) := idealFamilyAdjoinFamily J0 P
  have hM0 : IdealFamilyIsGood M0 :=
    idealFamilyAdjoinFamily_isGood J0 P hCompatible
  obtain ⟨M, hM, hM0M, hMax⟩ :=
    exists_maximal_good_idealFamily_above hM0
  let J : Ideal I := idealOfFamily M hM.1
  have hUltra : J.IsUltrafilterDual := by
    constructor
    · intro hUniv
      exact hM.2 hUniv
    · intro S
      exact idealFamily_compl_mem_of_maximal
        hM.1 hM.2 hMax S
  refine ⟨J, hUltra, ?_, ?_⟩
  · intro S hS
    exact hM0M (idealFamily_subset_adjoinFamily J0 P hS)
  · intro k
    exact hM0M (idealFamilyAdjoinFamily_mem J0 P k)

/-! Equivalently, a finitely compatible family can be forced to fail
    eventual truth simultaneously in one ultrafilter-dual extension. -/
theorem exists_ultrafilterDual_ideal_avoiding_eventual_family
    {I : Type u} {K : Type w}
    (J0 : Ideal I)
    (P : K -> I -> Prop)
    (hCompatible : forall s : Finset K,
      (J0.extendBy (finitePredicateUnion P s)).IsProper) :
    exists J : Ideal I,
      J.IsUltrafilterDual /\
        Ideal.Le J0 J /\
        forall k, Not (J.Eventually (P k)) := by
  obtain ⟨J, hUltra, hLe, hSmall⟩ :=
    exists_ultrafilterDual_ideal_extending_family J0 P hCompatible
  exact ⟨J, hUltra, hLe,
    fun k => (hUltra.small_iff_not_eventually (P k)).mp (hSmall k)⟩

/-! Starting with the finite-set ideal makes the ultrafilter-dual extension
    nonprincipal.  The family is still adjoined simultaneously, so every
    prescribed predicate is small in the same ideal. -/
theorem exists_nonprincipal_ultrafilterDual_ideal_extending_family
    {I : Type u} {K : Type w} [Infinite I]
    (P : K -> I -> Prop)
    (hCompatible : forall s : Finset K,
      ((Ideal.finiteSet I).extendBy
        (finitePredicateUnion P s)).IsProper) :
    exists J : Ideal I,
      J.IsUltrafilterDual /\
        Ideal.Le (Ideal.finiteSet I) J /\
        (forall i, Not (J = Ideal.excludePoint i)) /\
        forall k, J.Small (P k) := by
  obtain ⟨J, hUltra, hLe, hSmall⟩ :=
    exists_ultrafilterDual_ideal_extending_family
      (Ideal.finiteSet I) P hCompatible
  refine ⟨J, hUltra, hLe, ?_, hSmall⟩
  intro i hEq
  have hSingleton : J.Small (fun j : I => j = i) := by
    apply hLe
    rw [Ideal.finiteSet_small_iff]
    simp
  rw [hEq] at hSingleton
  exact hSingleton rfl

theorem exists_nonprincipal_ultrafilterDual_ideal_avoiding_eventual_family
    {I : Type u} {K : Type w} [Infinite I]
    (P : K -> I -> Prop)
    (hCompatible : forall s : Finset K,
      ((Ideal.finiteSet I).extendBy
        (finitePredicateUnion P s)).IsProper) :
    exists J : Ideal I,
      J.IsUltrafilterDual /\
        (forall i, Not (J = Ideal.excludePoint i)) /\
        forall k, Not (J.Eventually (P k)) := by
  obtain ⟨J, hUltra, _hLe, hNonprincipal, hSmall⟩ :=
    exists_nonprincipal_ultrafilterDual_ideal_extending_family
      P hCompatible
  exact ⟨J, hUltra, hNonprincipal,
    fun k => (hUltra.small_iff_not_eventually (P k)).mp (hSmall k)⟩

namespace ReducedProductFrame

/-! Replace only the ideal of a reduced-product frame.  Coordinates and
    their preorder are definitionally unchanged, which lets the compactness
    construction below reuse the same candidate functions. -/
def withIdeal
    (F : ReducedProductFrame.{u, v})
    (J : Ideal F.Index) : ReducedProductFrame.{u, v} where
  Index := F.Index
  Coord := F.Coord
  le := F.le
  le_refl := F.le_refl
  le_trans := F.le_trans
  J := J

/-! If every finite collection of comparison sets can be adjoined while
    preserving properness, one ultrafilter-dual extension makes all those
    comparisons fail eventually. -/
theorem exists_ultrafilterDual_ideal_avoiding_eventuallyLe_family
    (F : ReducedProductFrame.{u, v})
    {K : Type w}
    (d : K -> ProductElement F)
    (g : ProductElement F)
    (hCompatible : forall s : Finset K,
      (F.J.extendBy (finitePredicateUnion
        (fun k i => F.le i (g i) (d k i)) s)).IsProper) :
    exists J : Ideal F.Index,
      J.IsUltrafilterDual /\
        Ideal.Le F.J J /\
        forall k,
          Not ((F.withIdeal J).eventuallyLe g (d k)) := by
  obtain ⟨J, hUltra, hLe, hAvoid⟩ :=
    exists_ultrafilterDual_ideal_avoiding_eventual_family F.J
      (fun k i => F.le i (g i) (d k i)) hCompatible
  refine ⟨J, hUltra, hLe, ?_⟩
  intro k
  simpa only [withIdeal, eventuallyLe] using hAvoid k

end ReducedProductFrame

theorem exists_nonprincipal_ultrafilterDual_ideal
    {I : Type u} [Infinite I] :
    exists J : Ideal I,
      J.IsUltrafilterDual /\
        forall i, Not (J = Ideal.excludePoint i) := by
  obtain ⟨M, hM, hFiniteM, hMax⟩ :=
    exists_maximal_good_idealFamily (I := I)
  let J := idealOfFamily M hM.1
  have hUltra : J.IsUltrafilterDual := by
    constructor
    · intro hUniv
      exact hM.2 hUniv
    · intro S
      exact idealFamily_compl_mem_of_maximal
        hM.1 hM.2 hMax S
  refine ⟨J, hUltra, ?_⟩
  intro i hEq
  have hSingletonMem : (fun j : I => j = i) ∈ M := by
    apply hFiniteM
    change Set.Finite {j : I | j = i}
    simp
  have hSingletonSmall : J.Small (fun j : I => j = i) := hSingletonMem
  rw [hEq] at hSingletonSmall
  exact hSingletonSmall rfl

end PcfProject
