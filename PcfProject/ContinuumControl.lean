import PcfProject.PrincipalPcf
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Cardinal arithmetic at `aleph_omega`

This file contains the two elementary cardinal-arithmetic facts used by the
PCF proof.  Under the strong-limit hypothesis, the powers
`2 ^ aleph_omega` and `aleph_omega ^ aleph_0` agree; the ordinary continuum
is strictly below `aleph_omega`.

No PCF spectrum, generator, or maximum-PCF assumption is introduced here.
-/

namespace PcfProject

universe u v w x

open Cardinal Set Order

noncomputable abbrev continuumAtAlephOmega : Cardinal.{u} :=
  (2 : Cardinal.{u}) ^ targetAlephOmega

/-! The countable-exponent power of `aleph_omega` is bounded by the power
    appearing in `continuumAtAlephOmega`. This is only cardinal arithmetic:
    the exponent is enlarged from `aleph0` to `aleph_omega`, and the latter
    self-power is identified with the two-power by Cantor arithmetic. It does
    not identify the two cardinals and does not supply the PCF continuum
    bridge. -/
theorem targetAlephOmega_power_aleph0_le_continuumAtAlephOmega :
    targetAlephOmega.{u} ^ Cardinal.aleph0 <= continuumAtAlephOmega := by
  calc
    targetAlephOmega.{u} ^ Cardinal.aleph0 <=
        targetAlephOmega.{u} ^ targetAlephOmega.{u} :=
      Cardinal.power_le_power_left
        (by exact (show targetAlephOmega.{u} ≠ 0 from
          (Cardinal.aleph0_pos.trans_le targetAlephOmega_aleph0_le).ne'))
        targetAlephOmega_aleph0_le
    _ = (2 : Cardinal.{u}) ^ targetAlephOmega := by
      exact Cardinal.power_self_eq targetAlephOmega_aleph0_le
    _ = continuumAtAlephOmega := rfl

#print axioms targetAlephOmega_power_aleph0_le_continuumAtAlephOmega

/-! A strong-limit coding lemma for the continuum at `aleph_omega`.  Choose a
    cofinal subset of the canonical well-order of `aleph_omega`.  Each initial
    segment has a powerset of cardinality below `aleph_omega`, so a subset of
    the whole ordinal is determined by its traces on the countably cofinal
    family of initial segments.  This is a genuine cardinal-arithmetic proof;
    it does not use any PCF structural theorem. -/
theorem continuumAtAlephOmega_le_targetAlephOmega_power_aleph0_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    continuumAtAlephOmega.{u} <=
      targetAlephOmega.{u} ^ Cardinal.aleph0 := by
  let α := targetAlephOmega.ord.ToType
  obtain ⟨s, hsCof, hsCard⟩ := Order.exists_cof_eq α
  have hα : #α = targetAlephOmega := by
    change #(targetAlephOmega.ord.ToType) = targetAlephOmega
    simp
  have hcof : #s = Cardinal.aleph0 := by
    rw [hsCard]
    change Order.cof α = Cardinal.aleph0
    simp [α, targetAlephOmega, targetIndexOmega]
  let B : s → Type u := fun i => Set (Set.Iic (i : α))
  have hB : ∀ i : s, #(B i) ≤ targetAlephOmega := by
    intro i
    have hOrder : (#α).ord = Ordinal.type (· < · : α → α → Prop) := by
      rw [hα]
      exact (Ordinal.type_toType targetAlephOmega.ord).symm
    have hα0 : Cardinal.aleph0 ≤ #α := by
      rw [hα]
      exact targetAlephOmega_aleph0_le
    have hIic : #(Set.Iic (i : α)) < #α :=
      Cardinal.mk_Iic_lt (i : α) hOrder hα0
    calc
      #(B i) = 2 ^ #(Set.Iic (i : α)) := by
        simp [B, Cardinal.mk_set]
      _ ≤ targetAlephOmega := by
        exact (hStrongLimit.isStrongPrelimit
          (by simpa [hα] using hIic)).le
  let code : Set α → ((i : s) → B i) := fun X i =>
    {y : Set.Iic (i : α) | (y : α) ∈ X}
  have hCode : Function.Injective code := by
    intro X Y hXY
    apply Set.ext
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := hsCof x
      let i' : s := ⟨i, hi⟩
      let y : Set.Iic (i : α) := ⟨x, hxi⟩
      have hy : y ∈ code X i' := by
        change x ∈ X
        exact hx
      have hpoint : code X i' = code Y i' := congrFun hXY i'
      rw [hpoint] at hy
      change x ∈ Y at hy
      exact hy
    · intro hx
      obtain ⟨i, hi, hxi⟩ := hsCof x
      let i' : s := ⟨i, hi⟩
      let y : Set.Iic (i : α) := ⟨x, hxi⟩
      have hy : y ∈ code Y i' := by
        change x ∈ Y
        exact hx
      have hpoint : code X i' = code Y i' := congrFun hXY i'
      rw [← hpoint] at hy
      change x ∈ X at hy
      exact hy
  have hCodeCard : #(Set α) ≤ #((i : s) → B i) :=
    Cardinal.mk_le_of_injective hCode
  have hPi : #((i : s) → B i) ≤ targetAlephOmega ^ #s := by
    rw [Cardinal.mk_pi]
    exact (Cardinal.prod_le_prod _ _ hB).trans_eq
      (Cardinal.prod_const' s targetAlephOmega)
  have hSet : #(Set α) = (2 : Cardinal.{u}) ^ targetAlephOmega := by
    simp [Cardinal.mk_set, hα]
  have hLeft : (2 : Cardinal.{u}) ^ targetAlephOmega ≤ #(Set α) := hSet.ge
  calc
    (2 : Cardinal.{u}) ^ targetAlephOmega ≤ #(Set α) := hLeft
    _ ≤ #((i : s) → B i) := hCodeCard
    _ ≤ targetAlephOmega ^ #s := hPi
    _ = targetAlephOmega ^ Cardinal.aleph0 := by rw [hcof]

#print axioms continuumAtAlephOmega_le_targetAlephOmega_power_aleph0_of_strongLimit

/-! The preceding two inequalities identify the two powers under the
    strong-limit hypothesis.  Keeping this as a named equality avoids
    repeating the arithmetic sandwich in final-assembly arguments. -/
theorem continuumAtAlephOmega_eq_targetAlephOmega_power_aleph0_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    continuumAtAlephOmega.{u} =
      targetAlephOmega.{u} ^ Cardinal.aleph0 := by
  exact le_antisymm
    (continuumAtAlephOmega_le_targetAlephOmega_power_aleph0_of_strongLimit
      hStrongLimit)
    targetAlephOmega_power_aleph0_le_continuumAtAlephOmega

#print axioms continuumAtAlephOmega_eq_targetAlephOmega_power_aleph0_of_strongLimit

/-! Under the strong-limit premise, the ordinary continuum is strictly below
    `aleph_omega`. This is the elementary cardinal-arithmetic part of the
    conditional PCF route; it does not identify `2 ^ aleph_omega` with the
    ordinary continuum and does not provide the PCF continuum bridge. -/
theorem two_power_aleph0_lt_targetAlephOmega_of_strongLimit
    (hStrongLimit : Cardinal.IsStrongLimit targetAlephOmega.{u}) :
    (2 : Cardinal.{u}) ^ Cardinal.aleph0 < targetAlephOmega := by
  apply hStrongLimit.isStrongPrelimit
  simpa only [targetAlephOmega, targetIndexOmega] using
    (Cardinal.aleph0_lt_aleph.mpr Ordinal.omega0_pos)

#print axioms two_power_aleph0_lt_targetAlephOmega_of_strongLimit

end PcfProject
