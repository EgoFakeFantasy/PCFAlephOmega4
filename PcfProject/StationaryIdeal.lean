import PcfProject.IdealProduct
import PcfProject.Stationary

/-!
# The nonstationary ideal

This module connects the project's verified stationary-set API to the ideal
and eventual-truth API used by reduced products.  It is the basic ideal in
Shelah's Theorem 24.16.  No true-cofinality assertion is made here.
-/

namespace PcfProject

universe u v

open Set Cardinal
open scoped Cardinal

theorem cof_Iio_ne_aleph0_of_aleph0_lt_cof
    {eta : Ordinal.{u}}
    (hEtaCof : Cardinal.aleph0 < eta.cof) :
    Order.cof (Set.Iio eta) ≠ Cardinal.aleph0 := by
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof]
  have hlt : Cardinal.lift.{u + 1} Cardinal.aleph0 <
      Cardinal.lift.{u + 1} eta.cof :=
    Cardinal.lift_lt.mpr hEtaCof
  rw [Cardinal.lift_aleph0] at hlt
  exact ne_of_gt hlt

theorem cof_Iio_cofOrd_ne_aleph0_of_aleph0_lt_cof
    {eta : Ordinal.{u}}
    (hEtaCof : Cardinal.aleph0 < eta.cof) :
    Order.cof (Set.Iio eta.cof.ord) ≠ Cardinal.aleph0 := by
  apply cof_Iio_ne_aleph0_of_aleph0_lt_cof
  simpa only [Ordinal.cof_ord_cof] using hEtaCof

theorem exists_ultrafilterDual_ideal_extending
    {I : Type u}
    (J0 : Ideal I)
    (hProper : J0.IsProper) :
    exists J : Ideal I, J.IsUltrafilterDual /\ Ideal.Le J0 J := by
  obtain ⟨J, hUltra, hLe, _hEmpty⟩ :=
    exists_ultrafilterDual_ideal_extending_family
      J0 (fun _ : Empty => fun _ => False) (by
        intro s
        have hs : s = ∅ := by
          ext i
          exact Empty.elim i
        subst s
        have hUnion : finitePredicateUnion
            (fun _ : Empty => fun _ : I => False) ∅ =
            (fun _ : I => False) := by
          funext i
          simp [finitePredicateUnion]
        rw [hUnion]
        rw [Ideal.extendBy_isProper_iff_not_eventually]
        exact hProper.not_eventually_false)
  exact ⟨J, hUltra, hLe⟩

theorem Ideal.eventually_iff_forall_ultrafilterDual_extension
    {I : Type u}
    (J0 : Ideal I)
    (P : I -> Prop) :
    J0.Eventually P ↔
      forall J : Ideal I, J.IsUltrafilterDual ->
        Ideal.Le J0 J -> J.Eventually P := by
  constructor
  · intro hEventually J _hUltra hLe
    exact hLe _ hEventually
  · intro hAll
    by_contra hNotEventually
    have hExtendedProper : (J0.extendBy P).IsProper :=
      (Ideal.extendBy_isProper_iff_not_eventually J0 P).mpr hNotEventually
    obtain ⟨J, hUltra, hLe⟩ :=
      exists_ultrafilterDual_ideal_extending
        (J0.extendBy P) hExtendedProper
    have hBaseLe : Ideal.Le J0 J :=
      Ideal.le_trans (J0.le_extendBy P) hLe
    have hPSmall : J.Small P :=
      hLe P (J0.generator_small_in_extendBy P)
    have hNotJEventually : ¬ J.Eventually P :=
      (hUltra.small_iff_not_eventually P).mp hPSmall
    exact hNotJEventually (hAll J hUltra hBaseLe)

def nonstationaryIdeal
    (alpha : Type u)
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hCof : Order.cof alpha ≠ Cardinal.aleph0) : Ideal alpha where
  Small S := Nonstationary {i | S i}
  empty_small := nonstationary_empty
  subset_small := by
    intro A B hA hBA
    exact nonstationary_mono (fun i hi => hBA i hi) hA
  union_small := by
    intro A B hA hB
    exact nonstationary_union hCof hA hB

@[simp] theorem nonstationaryIdeal_small_iff
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hCof : Order.cof alpha ≠ Cardinal.aleph0)
    (S : alpha -> Prop) :
    (nonstationaryIdeal alpha hCof).Small S ↔
      Nonstationary {i | S i} :=
  Iff.rfl

theorem nonstationaryIdeal_isProper
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    [Nonempty alpha]
    (hCof : Order.cof alpha ≠ Cardinal.aleph0) :
    (nonstationaryIdeal alpha hCof).IsProper := by
  intro hSmall
  have hNonstationary : Nonstationary (Set.univ : Set alpha) := by
    simpa only [Set.setOf_true] using hSmall
  exact (nonstationary_iff_not_stationary Set.univ).mp hNonstationary
    (univ_stationary hCof)

theorem nonstationaryIdeal_eventually_iff_contains_club
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hCof : Order.cof alpha ≠ Cardinal.aleph0)
    (P : alpha -> Prop) :
    (nonstationaryIdeal alpha hCof).Eventually P ↔
      exists C : Set alpha, IsClub C /\ forall i, i ∈ C -> P i := by
  constructor
  · rintro ⟨C, hC, hAvoid⟩
    refine ⟨C, hC, ?_⟩
    intro i hiC
    by_contra hi
    exact hAvoid i hiC hi
  · rintro ⟨C, hC, hCP⟩
    exact ⟨C, hC, fun i hiC hiNot => hiNot (hCP i hiC)⟩

theorem nonstationaryIdeal_le_iff_eventually_of_isClub
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hCof : Order.cof alpha ≠ Cardinal.aleph0)
    (J : Ideal alpha) :
    Ideal.Le (nonstationaryIdeal alpha hCof) J ↔
      forall C : Set alpha, IsClub C ->
        J.Eventually (fun i => i ∈ C) := by
  constructor
  · intro hLe C hC
    apply hLe
    exact ⟨C, hC, fun i hiC hiNotC => hiNotC hiC⟩
  · intro hClubs S hS
    obtain ⟨C, hC, hAvoid⟩ := hS
    exact J.subset_small (hClubs C hC) (by
      intro i hiS hiC
      exact hAvoid i hiC hiS)

/-! Restricting an ideal which contains every target club along a normal
cofinal map produces an ideal containing the source nonstationary ideal.
The image-of-club theorem supplies target clubs, and injectivity of a normal
map turns eventual image membership back into eventual source membership. -/
theorem nonstationaryIdeal_le_restrictAlong_of_isNormal_of_isCofinal
    {alpha : Type u} {beta : Type v}
    [LinearOrder alpha] [WellFoundedLT alpha] [Nonempty alpha]
    [LinearOrder beta]
    (hAlphaCof : Order.cof alpha ≠ Cardinal.aleph0)
    (J : Ideal beta)
    (hClubs : forall C : Set beta, IsClub C ->
      J.Eventually (fun b => b ∈ C))
    (f : alpha -> beta)
    (hf : Order.IsNormal f)
    (hCof : IsCofinal (Set.range f)) :
    Ideal.Le (nonstationaryIdeal alpha hAlphaCof)
      (J.restrictAlong f) := by
  apply (nonstationaryIdeal_le_iff_eventually_of_isClub
    hAlphaCof (J.restrictAlong f)).mpr
  intro C hC
  have hImageClub : IsClub (f '' C) :=
    isClub_image_of_isNormal_of_isCofinal hf hCof hC
  have hImage : J.Eventually
      (fun b => exists a, f a = b /\ a ∈ C) :=
    J.eventually_mono (hClubs (f '' C) hImageClub) (by
      intro b hb
      obtain ⟨a, haC, hab⟩ := hb
      exact ⟨a, hab, haC⟩)
  exact J.restrictAlong_eventually_of_eventually_image
    f hf.strictMono.injective (fun a => a ∈ C) hImage

theorem exists_club_subset_of_forall_nonstationaryIdeal_extension_eventually
    {alpha : Type u}
    [LinearOrder alpha]
    [WellFoundedLT alpha]
    (hCof : Order.cof alpha ≠ Cardinal.aleph0)
    (P : alpha -> Prop)
    (hAll : forall J : Ideal alpha,
      J.IsUltrafilterDual ->
      Ideal.Le (nonstationaryIdeal alpha hCof) J ->
      J.Eventually P) :
    exists C : Set alpha,
      IsClub C /\ forall i, i ∈ C -> P i := by
  apply
    (nonstationaryIdeal_eventually_iff_contains_club hCof P).mp
  exact
    (Ideal.eventually_iff_forall_ultrafilterDual_extension
      (nonstationaryIdeal alpha hCof) P).mpr hAll

end PcfProject
