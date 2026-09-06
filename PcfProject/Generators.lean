import PcfProject.PcfBasics
import Mathlib.Data.Finset.Max

/-!
# Stage 6: Generator/no-holes/max-pcf hypothesis interfaces

This file is a Mathlib-cardinal rewrite of the former generator skeleton. It
defines the interfaces used to state generator systems, no-holes, and max-pcf
witnesses, but it does not prove the structural PCF theorems.

The package `PcfStructuralHypotheses` is intentionally named as a hypothesis
bundle. Its fields are hard mathematical assumptions supplied by a caller.
`GeneratorSystem` requires its two ideals to have the standard PCF semantics
through `pcf (A inter B)`, rather than accepting arbitrarily named ideals. The
lemmas below expose those fields and prove their filtration, generator,
uniqueness, and interval-closure consequences.
-/

namespace PcfProject

universe u v w x

def InterCardSet (A B : CardSet.{u}) : CardSet.{u} :=
  fun theta => A theta /\ B theta

def Between
    (left theta right : Cardinal.{u}) : Prop :=
  left < theta /\ theta < right

/-- `A` is order-convex among regular cardinals. -/
def CardinalInterval (A : CardSet.{u}) : Prop :=
  forall {left theta right : Cardinal.{u}},
    A left ->
    A right ->
    Cardinal.IsRegular theta ->
    Between left theta right ->
    A theta

structure GeneratorSystem
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) where
  belowIdeal : Cardinal.{u} -> Ideal Cardinal.{u}
  atMostIdeal : Cardinal.{u} -> Ideal Cardinal.{u}
  generator : Cardinal.{u} -> CardSet.{u}
  belowIdeal_spec :
    forall theta B,
      (belowIdeal theta).Small B <->
        forall beta, R.pcf (InterCardSet A B) beta -> beta < theta
  atMostIdeal_spec :
    forall theta B,
      (atMostIdeal theta).Small B <->
        forall beta, R.pcf (InterCardSet A B) beta -> beta <= theta
  generator_subset :
    forall {theta}, R.pcf A theta -> SubsetOf (generator theta) A
  generator_ideal_equiv :
    forall {theta}, R.pcf A theta ->
      Ideal.Equivalent
        (atMostIdeal theta)
        ((belowIdeal theta).extendBy (generator theta))

namespace GeneratorSystem

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}

theorem subset_of_mem_pcf
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    SubsetOf (G.generator theta) A :=
  G.generator_subset hTheta

theorem belowIdeal_small_iff
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u})
    (B : CardSet.{u}) :
    (G.belowIdeal theta).Small B <->
      forall beta, R.pcf (InterCardSet A B) beta -> beta < theta :=
  G.belowIdeal_spec theta B

theorem atMostIdeal_small_iff
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u})
    (B : CardSet.{u}) :
    (G.atMostIdeal theta).Small B <->
      forall beta, R.pcf (InterCardSet A B) beta -> beta <= theta :=
  G.atMostIdeal_spec theta B

theorem ideal_equiv_of_mem_pcf
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    Ideal.Equivalent
      (G.atMostIdeal theta)
      ((G.belowIdeal theta).extendBy (G.generator theta)) :=
  G.generator_ideal_equiv hTheta

theorem atMost_le_generated
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    Ideal.Le
      (G.atMostIdeal theta)
      ((G.belowIdeal theta).extendBy (G.generator theta)) :=
  Ideal.le_of_equivalent_left (G.ideal_equiv_of_mem_pcf hTheta)

theorem generated_le_atMost
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    Ideal.Le
      ((G.belowIdeal theta).extendBy (G.generator theta))
      (G.atMostIdeal theta) :=
  Ideal.le_of_equivalent_right (G.ideal_equiv_of_mem_pcf hTheta)

/-! The generator equivalence can be used as an explicit localization
    principle.  This form is convenient when a later argument needs to carry
    the witnessing `< theta`-small set rather than an abstract ideal
    comparison. -/
theorem atMost_small_iff_exists_below_cover
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (B : Cardinal.{u} -> Prop) :
    (G.atMostIdeal theta).Small B <->
      exists T : Cardinal.{u} -> Prop,
        (G.belowIdeal theta).Small T /\
          forall i, B i -> T i \/ G.generator theta i := by
  constructor
  · intro hB
    have hGenerated := G.atMost_le_generated hTheta B hB
    exact hGenerated
  · rintro ⟨T, hT, hCover⟩
    apply G.generated_le_atMost hTheta B
    exact ⟨T, hT, hCover⟩

theorem belowIdeal_le_atMost
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u}) :
    Ideal.Le (G.belowIdeal theta) (G.atMostIdeal theta) :=
  by
    intro B hB
    apply (G.atMostIdeal_small_iff theta B).mpr
    intro beta hBeta
    exact ((G.belowIdeal_small_iff theta B).mp hB beta hBeta).le

theorem belowIdeal_mono
    (G : GeneratorSystem R A)
    {theta gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma) :
    Ideal.Le (G.belowIdeal theta) (G.belowIdeal gamma) := by
  intro B hB
  apply (G.belowIdeal_small_iff gamma B).mpr
  intro beta hBeta
  exact ((G.belowIdeal_small_iff theta B).mp hB beta hBeta).trans_le
    hThetaGamma

theorem atMostIdeal_mono
    (G : GeneratorSystem R A)
    {theta gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma) :
    Ideal.Le (G.atMostIdeal theta) (G.atMostIdeal gamma) := by
  intro B hB
  apply (G.atMostIdeal_small_iff gamma B).mpr
  intro beta hBeta
  exact ((G.atMostIdeal_small_iff theta B).mp hB beta hBeta).trans
    hThetaGamma

theorem atMostIdeal_le_belowIdeal_of_lt
    (G : GeneratorSystem R A)
    {theta gamma : Cardinal.{u}}
    (hThetaGamma : theta < gamma) :
    Ideal.Le (G.atMostIdeal theta) (G.belowIdeal gamma) := by
  intro B hB
  apply (G.belowIdeal_small_iff gamma B).mpr
  intro beta hBeta
  exact ((G.atMostIdeal_small_iff theta B).mp hB beta hBeta).trans_lt
    hThetaGamma

theorem belowIdeal_isProper_iff_exists_pcf_not_lt
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u}) :
    Ideal.IsProper (G.belowIdeal theta) <->
      exists beta, R.pcf A beta /\ Not (beta < theta) := by
  classical
  constructor
  · intro hProper
    by_contra hNo
    apply hProper
    apply (G.belowIdeal_small_iff theta (fun _ => True)).mpr
    intro beta hBeta
    by_cases hLt : beta < theta
    · exact hLt
    · have hBetaA : R.pcf A beta := by
        have hInterEq : InterCardSet A (fun _ => True) = A := by
          funext gamma
          apply propext
          constructor
          · intro h
            exact h.1
          · intro h
            exact And.intro h True.intro
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
        exact And.intro h True.intro
    have hBeta' : R.pcf (InterCardSet A (fun _ => True)) beta := by
      rw [hInterEq]
      exact hBeta
    exact hNotLt
      ((G.belowIdeal_small_iff theta (fun _ => True)).mp hSmall
        beta hBeta')

theorem atMostIdeal_isProper_iff_exists_pcf_gt
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u}) :
    Ideal.IsProper (G.atMostIdeal theta) <->
      exists beta, R.pcf A beta /\ theta < beta := by
  classical
  constructor
  · intro hProper
    by_contra hNo
    apply hProper
    apply (G.atMostIdeal_small_iff theta (fun _ => True)).mpr
    intro beta hBeta
    by_cases hLe : beta <= theta
    · exact hLe
    · have hBetaA : R.pcf A beta := by
        have hInterEq : InterCardSet A (fun _ => True) = A := by
          funext gamma
          apply propext
          constructor
          · intro h
            exact h.1
          · intro h
            exact And.intro h True.intro
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
        exact And.intro h True.intro
    have hBeta' : R.pcf (InterCardSet A (fun _ => True)) beta := by
      rw [hInterEq]
      exact hBeta
    exact (not_le_of_gt hGt)
      ((G.atMostIdeal_small_iff theta (fun _ => True)).mp hSmall
        beta hBeta')

theorem below_small_atMost
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    {S : Cardinal.{u} -> Prop}
    (hS : (G.belowIdeal theta).Small S) :
    (G.atMostIdeal theta).Small S :=
  G.belowIdeal_le_atMost theta S hS

theorem generator_small_atMost
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    (G.atMostIdeal theta).Small (G.generator theta) :=
  G.generated_le_atMost hTheta
    (G.generator theta)
    ((G.belowIdeal theta).generator_small_in_extendBy (G.generator theta))

/-! A finite union of generator sets is the first concrete closure layer used
    in the usual PCF filtration argument.  The support and threshold facts are
    kept explicit: the result only uses generators whose PCF values are already
    known and which lie below the displayed threshold. -/

def finsetGeneratorUnion
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u})) : CardSet.{u} :=
  fun i => exists beta, beta ∈ s /\ G.generator beta i

def finsetGeneratorClosure
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (S : CardSet.{u}) : CardSet.{u} :=
  fun i => S i \/ G.finsetGeneratorUnion s i

theorem finsetGeneratorUnion_subset_of_mem_pcf
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta) :
    SubsetOf (G.finsetGeneratorUnion s) A := by
  intro i hi
  obtain ⟨beta, hbeta, hi⟩ := hi
  exact G.subset_of_mem_pcf (hSupport beta hbeta) i hi

/-! The closure operator is monotone in both pieces of finite data.  These
    elementary facts are useful when a localizer is enlarged: enlarging the
    finite support can only add generators, and enlarging the seed can only
    add points already present in the closure. -/

theorem finsetGeneratorUnion_mono
    (G : GeneratorSystem R A)
    {s t : Finset (Cardinal.{u})}
    (hst : s ⊆ t) :
    SubsetOf (G.finsetGeneratorUnion s)
      (G.finsetGeneratorUnion t) := by
  intro i hi
  obtain ⟨beta, hbeta, hi⟩ := hi
  exact ⟨beta, hst hbeta, hi⟩

theorem finsetGeneratorClosure_mono
    (G : GeneratorSystem R A)
    {s t : Finset (Cardinal.{u})}
    {S T : CardSet.{u}}
    (hst : s ⊆ t)
    (hST : SubsetOf S T) :
    SubsetOf (G.finsetGeneratorClosure s S)
      (G.finsetGeneratorClosure t T) := by
  intro i hi
  cases hi with
  | inl hSi =>
      exact Or.inl (hST i hSi)
  | inr hGi =>
      exact Or.inr (G.finsetGeneratorUnion_mono hst i hGi)

theorem finsetGeneratorUnion_small_atMost_of_le
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    (hBound : forall beta, beta ∈ s -> beta <= theta) :
    (G.atMostIdeal theta).Small (G.finsetGeneratorUnion s) := by
  apply ((G.atMostIdeal theta).finset_small_iff s
    (fun beta i => G.generator beta i)).mpr
  intro beta hbeta
  have hSmall : (G.atMostIdeal beta).Small (G.generator beta) :=
    G.generator_small_atMost (hSupport beta hbeta)
  exact (G.atMostIdeal_mono (hBound beta hbeta))
    (G.generator beta) hSmall

theorem finsetGeneratorClosure_subset_of_subset
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    {S : CardSet.{u}}
    (hS : SubsetOf S A) :
    SubsetOf (G.finsetGeneratorClosure s S) A := by
  intro i hi
  cases hi with
  | inl hSi => exact hS i hSi
  | inr hGi =>
      exact (finsetGeneratorUnion_subset_of_mem_pcf G s hSupport) i hGi

theorem finsetGeneratorClosure_small_atMost_of_small
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    (hBound : forall beta, beta ∈ s -> beta <= theta)
    {S : CardSet.{u}}
    (hS : (G.atMostIdeal theta).Small S) :
    (G.atMostIdeal theta).Small (G.finsetGeneratorClosure s S) := by
  exact (G.atMostIdeal theta).union_small hS
    (G.finsetGeneratorUnion_small_atMost_of_le
      s hSupport hBound)

theorem finsetGeneratorClosure_subset_left
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (S : CardSet.{u}) :
    SubsetOf S (G.finsetGeneratorClosure s S) := by
  intro i hi
  exact Or.inl hi

theorem pcf_inter_finsetGeneratorClosure_le_of_small'
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    (hBound : forall beta, beta ∈ s -> beta <= theta)
    {S : CardSet.{u}}
    (hS : (G.atMostIdeal theta).Small S) :
    forall beta, R.pcf (InterCardSet A
      (G.finsetGeneratorClosure s S)) beta -> beta <= theta := by
  intro beta hBeta
  exact (G.atMostIdeal_small_iff theta
    (G.finsetGeneratorClosure s S)).mp
    (G.finsetGeneratorClosure_small_atMost_of_small
      s hSupport hBound hS) beta hBeta

/-! Iterating the one-step operation gives a finite closure certificate.  This
    is deliberately a generic finite-stage result; it does not assert that the
    closure covers all PCF values. -/

def finsetGeneratorClosureIterate
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u})) : Nat -> CardSet.{u} -> CardSet.{u}
  | 0, S => S
  | n + 1, S =>
      G.finsetGeneratorClosure s (G.finsetGeneratorClosureIterate s n S)

theorem finsetGeneratorClosureIterate_zero
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (S : CardSet.{u}) :
    G.finsetGeneratorClosureIterate s 0 S = S :=
  rfl

theorem finsetGeneratorClosureIterate_succ
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (n : Nat)
    (S : CardSet.{u}) :
    G.finsetGeneratorClosureIterate s (n + 1) S =
  G.finsetGeneratorClosure s
        (G.finsetGeneratorClosureIterate s n S) :=
  rfl

theorem finsetGeneratorClosureIterate_mono
    (G : GeneratorSystem R A)
    {s t : Finset (Cardinal.{u})}
    {S T : CardSet.{u}}
    (hst : s ⊆ t)
    (hST : SubsetOf S T) :
    forall n, SubsetOf
      (G.finsetGeneratorClosureIterate s n S)
      (G.finsetGeneratorClosureIterate t n T) := by
  intro n
  induction n with
  | zero =>
      exact hST
  | succ n ih =>
      rw [G.finsetGeneratorClosureIterate_succ,
        G.finsetGeneratorClosureIterate_succ]
      exact G.finsetGeneratorClosure_mono hst ih

theorem finsetGeneratorClosureIterate_four_mono
    (G : GeneratorSystem R A)
    {s t : Finset (Cardinal.{u})}
    {S T : CardSet.{u}}
    (hst : s ⊆ t)
    (hST : SubsetOf S T) :
    SubsetOf
      (G.finsetGeneratorClosureIterate s 4 S)
      (G.finsetGeneratorClosureIterate t 4 T) :=
  G.finsetGeneratorClosureIterate_mono hst hST 4

theorem finsetGeneratorClosureIterate_seed_subset
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (S : CardSet.{u}) :
    forall n, SubsetOf S
      (G.finsetGeneratorClosureIterate s n S) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      exact hi
  | succ n ih =>
      rw [G.finsetGeneratorClosureIterate_succ]
      intro i hi
      exact Or.inl (ih i hi)

theorem finsetGeneratorClosureIterate_subset_of_subset
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    {S : CardSet.{u}}
    (hS : SubsetOf S A) :
    forall n, SubsetOf
      (G.finsetGeneratorClosureIterate s n S) A := by
  intro n
  induction n with
  | zero =>
      exact hS
  | succ n ih =>
      rw [G.finsetGeneratorClosureIterate_succ]
      exact G.finsetGeneratorClosure_subset_of_subset
        s hSupport ih

theorem finsetGeneratorClosureIterate_small_atMost_of_small
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    (hBound : forall beta, beta ∈ s -> beta <= theta)
    {S : CardSet.{u}}
    (hS : (G.atMostIdeal theta).Small S) :
    forall n, (G.atMostIdeal theta).Small
      (G.finsetGeneratorClosureIterate s n S) := by
  intro n
  induction n with
  | zero =>
      exact hS
  | succ n ih =>
      rw [G.finsetGeneratorClosureIterate_succ]
      exact G.finsetGeneratorClosure_small_atMost_of_small
        s hSupport hBound ih

theorem pcf_inter_finsetGeneratorClosureIterate_le_of_small
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    (hBound : forall beta, beta ∈ s -> beta <= theta)
    {S : CardSet.{u}}
    (hS : (G.atMostIdeal theta).Small S) :
    forall n beta,
      R.pcf (InterCardSet A
        (G.finsetGeneratorClosureIterate s n S)) beta -> beta <= theta := by
  intro n beta hBeta
  exact (G.atMostIdeal_small_iff theta
    (G.finsetGeneratorClosureIterate s n S)).mp
    (G.finsetGeneratorClosureIterate_small_atMost_of_small
      s hSupport hBound hS n) beta hBeta

theorem pcf_inter_finsetGeneratorClosureIterate_four_le_of_small
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    (hBound : forall beta, beta ∈ s -> beta <= theta)
    {S : CardSet.{u}}
    (hS : (G.atMostIdeal theta).Small S) :
    forall beta, R.pcf (InterCardSet A
      (G.finsetGeneratorClosureIterate s 4 S)) beta -> beta <= theta :=
  G.pcf_inter_finsetGeneratorClosureIterate_le_of_small
    s hSupport hBound hS 4

theorem finsetGeneratorClosureIterate_four_subset_of_subset
    (G : GeneratorSystem R A)
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    {S : CardSet.{u}}
    (hS : SubsetOf S A) :
    SubsetOf (G.finsetGeneratorClosureIterate s 4 S) A :=
  G.finsetGeneratorClosureIterate_subset_of_subset
    s hSupport hS 4

theorem finsetGeneratorClosureIterate_four_small_atMost_of_small
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (s : Finset (Cardinal.{u}))
    (hSupport : forall beta, beta ∈ s -> R.pcf A beta)
    (hBound : forall beta, beta ∈ s -> beta <= theta)
    {S : CardSet.{u}}
    (hS : (G.atMostIdeal theta).Small S) :
    (G.atMostIdeal theta).Small
      (G.finsetGeneratorClosureIterate s 4 S) :=
  G.finsetGeneratorClosureIterate_small_atMost_of_small
    s hSupport hBound hS 4

/-! A finite closure certificate records the exact finite-support statement
    needed in the generator part of the countable-PCF argument.  The first
    four fields are elementary closure data and are checked below.  The
    `covered` field is the substantive PCF assertion: every global PCF value
    must already occur in the PCF of the displayed finite closure.  Keeping
    that field visible prevents a finite closure construction from being
    mistaken for the full generator theorem. -/

structure FiniteGeneratorClosureCertificate
    (G : GeneratorSystem R A)
    (theta : Cardinal.{u}) where
  support : Finset (Cardinal.{u})
  support_mem_pcf : forall beta, beta ∈ support -> R.pcf A beta
  support_le : forall beta, beta ∈ support -> beta <= theta
  seed : CardSet.{u}
  seed_subset : SubsetOf seed A
  seed_small : (G.atMostIdeal theta).Small seed
  covered : forall beta, R.pcf A beta ->
    R.pcf (InterCardSet A
      (G.finsetGeneratorClosureIterate support 4 seed)) beta

namespace FiniteGeneratorClosureCertificate

variable {G : GeneratorSystem R A}
variable {theta : Cardinal.{u}}

def closure (C : FiniteGeneratorClosureCertificate G theta) : CardSet.{u} :=
  G.finsetGeneratorClosureIterate C.support 4 C.seed

theorem closure_eq
    (C : FiniteGeneratorClosureCertificate G theta) :
    C.closure = G.finsetGeneratorClosureIterate C.support 4 C.seed :=
  rfl

theorem closure_subset
    (C : FiniteGeneratorClosureCertificate G theta) :
    SubsetOf C.closure A := by
  exact G.finsetGeneratorClosureIterate_four_subset_of_subset
    C.support C.support_mem_pcf C.seed_subset

theorem closure_small_atMost
    (C : FiniteGeneratorClosureCertificate G theta) :
    (G.atMostIdeal theta).Small C.closure := by
  exact G.finsetGeneratorClosureIterate_four_small_atMost_of_small
    C.support C.support_mem_pcf C.support_le C.seed_small

theorem closure_covered
    (C : FiniteGeneratorClosureCertificate G theta)
    {beta : Cardinal.{u}}
    (hBeta : R.pcf A beta) :
    R.pcf (InterCardSet A C.closure) beta := by
  exact C.covered beta hBeta

theorem pcf_le
    (C : FiniteGeneratorClosureCertificate G theta)
    {beta : Cardinal.{u}}
    (hBeta : R.pcf A beta) :
    beta <= theta := by
  exact G.pcf_inter_finsetGeneratorClosureIterate_four_le_of_small
    C.support C.support_mem_pcf C.support_le C.seed_small beta
    (C.covered beta hBeta)

theorem pcf_bounded
    (C : FiniteGeneratorClosureCertificate G theta) :
    forall beta, R.pcf A beta -> beta <= theta := by
  intro beta hBeta
  exact C.pcf_le hBeta

theorem pcf_lt_of_closure_bound
    (C : FiniteGeneratorClosureCertificate G theta)
    {bound : Cardinal.{u}}
    (hTheta : theta < bound) :
    forall beta, R.pcf A beta -> beta < bound := by
  intro beta hBeta
  exact (C.pcf_le hBeta).trans_lt hTheta

/-! A certificate may be transported to any larger threshold.  The finite
    support, seed, and covered closure are unchanged; only the two threshold
    inequalities and the seed's ideal-smallness need to be transported. -/
def of_le
    (C : FiniteGeneratorClosureCertificate G theta)
    {gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma) :
    FiniteGeneratorClosureCertificate G gamma := by
  refine
    { support := C.support
      support_mem_pcf := C.support_mem_pcf
      support_le := ?_
      seed := C.seed
      seed_subset := C.seed_subset
      seed_small := ?_
      covered := C.covered }
  · intro beta hBeta
    exact (C.support_le beta hBeta).trans hThetaGamma
  · exact G.atMostIdeal_mono hThetaGamma C.seed C.seed_small

theorem closure_subset_of_support_subset_of_seed_subset
    (C : FiniteGeneratorClosureCertificate G theta)
    {gamma : Cardinal.{u}}
    (D : FiniteGeneratorClosureCertificate G gamma)
    (hSupport : C.support ⊆ D.support)
    (hSeed : SubsetOf C.seed D.seed) :
    SubsetOf C.closure D.closure := by
  rw [C.closure_eq, D.closure_eq]
  exact G.finsetGeneratorClosureIterate_four_mono hSupport hSeed

#print axioms
  closure_subset_of_support_subset_of_seed_subset

theorem closure_small_atMost_of_le
    (C : FiniteGeneratorClosureCertificate G theta)
    {gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma) :
    (G.atMostIdeal gamma).Small C.closure := by
  exact G.atMostIdeal_mono hThetaGamma C.closure C.closure_small_atMost

#print axioms closure_small_atMost_of_le

theorem pcf_le_of_threshold_le
    (C : FiniteGeneratorClosureCertificate G theta)
    {gamma beta : Cardinal.{u}}
    (hThetaGamma : theta <= gamma)
    (hBeta : R.pcf A beta) :
    beta <= gamma := by
  exact (C.pcf_le hBeta).trans hThetaGamma

#print axioms pcf_le_of_threshold_le

theorem of_le_closure
    (C : FiniteGeneratorClosureCertificate G theta)
    {gamma : Cardinal.{u}}
    (hThetaGamma : theta <= gamma) :
    (C.of_le hThetaGamma).closure = C.closure := by
  rfl

#print axioms of_le_closure

theorem of_le_covered
    (C : FiniteGeneratorClosureCertificate G theta)
    {gamma beta : Cardinal.{u}}
    (hThetaGamma : theta <= gamma)
    (hBeta : R.pcf A beta) :
    R.pcf (InterCardSet A (C.of_le hThetaGamma).closure) beta := by
  rw [C.of_le_closure hThetaGamma]
  exact C.closure_covered hBeta

#print axioms of_le_covered

/-! The closure certificate has an exact converse at the level of its
    displayed threshold. Given a bound on the whole PCF set, one may take
    empty finite support and the seed `A`; the empty generator iteration then
    remains `A`. This is deliberately a *degenerate* certificate
    construction: it proves that the `covered` field is precisely the hard
    content, and it does not provide the finite-support localization used in
    Shelah's argument. -/
noncomputable def of_pcf_bounded
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hBound : forall beta, R.pcf A beta -> beta <= theta) :
    FiniteGeneratorClosureCertificate G theta := by
  let hInter : InterCardSet A A = A := by
    funext beta
    apply propext
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, h⟩
  refine
    { support := ∅
      support_mem_pcf := by simp
      support_le := by simp
      seed := A
      seed_subset := by intro beta hBeta; exact hBeta
      seed_small := ?_
      covered := ?_ }
  · apply (G.atMostIdeal_small_iff theta A).mpr
    intro beta hBeta
    apply hBound
    rw [hInter] at hBeta
    exact hBeta
  · intro beta hBeta
    have hEmpty :
        G.finsetGeneratorUnion (∅ : Finset (Cardinal.{u})) =
          (fun _ => False) := by
      funext gamma
      apply propext
      constructor
      · intro h
        obtain ⟨delta, hdelta, _⟩ := h
        simp at hdelta
      · intro h
        exact False.elim h
    have hStep : forall n : Nat,
        G.finsetGeneratorClosureIterate (∅ : Finset (Cardinal.{u})) n A = A := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [G.finsetGeneratorClosureIterate_succ, ih]
          funext gamma
          apply propext
          constructor
          · intro h
            cases h with
            | inl hA => exact hA
            | inr hEmpty' =>
                exact False.elim (by
                  rw [hEmpty] at hEmpty'
                  exact hEmpty')
          · intro hA
            exact Or.inl hA
    have hClosure :
        G.finsetGeneratorClosureIterate (∅ : Finset (Cardinal.{u})) 4 A = A :=
      hStep 4
    rw [hClosure, hInter]
    exact hBeta

theorem exists_iff_pcf_bounded
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}} :
    Nonempty (FiniteGeneratorClosureCertificate G theta) <->
      forall beta, R.pcf A beta -> beta <= theta := by
  constructor
  · rintro ⟨C⟩
    exact C.pcf_bounded
  · intro hBound
    exact ⟨of_pcf_bounded G hBound⟩

#print axioms exists_iff_pcf_bounded

end FiniteGeneratorClosureCertificate

theorem generator_pcf_le
    (G : GeneratorSystem R A)
    {theta beta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hBeta : R.pcf (InterCardSet A (G.generator theta)) beta) :
    beta <= theta :=
  (G.atMostIdeal_small_iff theta (G.generator theta)).mp
    (G.generator_small_atMost hTheta) beta hBeta

theorem generated_isProper
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hProper : Ideal.IsProper (G.atMostIdeal theta)) :
    Ideal.IsProper
      ((G.belowIdeal theta).extendBy (G.generator theta)) :=
  (Ideal.isProper_equivalent_iff (G.ideal_equiv_of_mem_pcf hTheta)).mp
    hProper

theorem generator_not_eventually_below
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hProper : Ideal.IsProper (G.atMostIdeal theta)) :
    Not ((G.belowIdeal theta).Eventually (G.generator theta)) :=
  ((G.belowIdeal theta).extendBy_isProper_iff_not_eventually
    (G.generator theta)).mp
      (G.generated_isProper hTheta hProper)

/-! These pointwise forms are the local threshold consequences used by
    generator localization. They retain the displayed PCF witness, so they
    do not assume a maximum PCF value. -/
theorem belowIdeal_isProper_of_mem_pcf_le
    (G : GeneratorSystem R A)
    {theta beta : Cardinal.{u}}
    (hBeta : R.pcf A beta)
    (hThetaBeta : theta <= beta) :
    Ideal.IsProper (G.belowIdeal theta) :=
  (G.belowIdeal_isProper_iff_exists_pcf_not_lt theta).mpr
    ⟨beta, hBeta, not_lt_of_ge hThetaBeta⟩

theorem atMostIdeal_isProper_of_mem_pcf_lt
    (G : GeneratorSystem R A)
    {theta beta : Cardinal.{u}}
    (hBeta : R.pcf A beta)
    (hThetaBeta : theta < beta) :
    Ideal.IsProper (G.atMostIdeal theta) :=
  (G.atMostIdeal_isProper_iff_exists_pcf_gt theta).mpr
    ⟨beta, hBeta, hThetaBeta⟩

theorem generated_isProper_of_mem_pcf_lt
    (G : GeneratorSystem R A)
    {theta beta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hBeta : R.pcf A beta)
    (hThetaBeta : theta < beta) :
    Ideal.IsProper
      ((G.belowIdeal theta).extendBy (G.generator theta)) :=
  G.generated_isProper hTheta
    (G.atMostIdeal_isProper_of_mem_pcf_lt hBeta hThetaBeta)

theorem generator_not_eventually_below_of_mem_pcf_lt
    (G : GeneratorSystem R A)
    {theta beta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hBeta : R.pcf A beta)
    (hThetaBeta : theta < beta) :
    Not ((G.belowIdeal theta).Eventually (G.generator theta)) :=
  G.generator_not_eventually_below hTheta
    (G.atMostIdeal_isProper_of_mem_pcf_lt hBeta hThetaBeta)

end GeneratorSystem

def NoHolesStatement
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) : Prop :=
  SetOfRegulars A ->
    ProgressiveCardSet A ->
      CardinalInterval A ->
      forall {left theta right : Cardinal.{u}},
        R.pcf A left ->
        R.pcf A right ->
        Cardinal.IsRegular theta ->
        Between left theta right ->
        R.pcf A theta

theorem noHoles_apply
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (hNoHoles : NoHolesStatement R A)
    (hRegulars : SetOfRegulars A)
    (hProgressive : ProgressiveCardSet A)
    (hInterval : CardinalInterval A)
    {left theta right : Cardinal.{u}}
    (hLeft : R.pcf A left)
    (hRight : R.pcf A right)
    (hRegular : Cardinal.IsRegular theta)
    (hBetween : Between left theta right) :
    R.pcf A theta :=
  hNoHoles hRegulars hProgressive hInterval
    hLeft hRight hRegular hBetween

def IsMaxPcf
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u})
    (theta : Cardinal.{u}) : Prop :=
  R.pcf A theta /\ forall beta, R.pcf A beta -> beta <= theta

def HasMaxPcf
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) : Prop :=
  exists theta, IsMaxPcf R A theta

structure MaxPcfWitness
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) where
  theta : Cardinal.{u}
  isMax : IsMaxPcf R A theta

namespace FiniteGeneratorClosureCertificate

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}
variable {G : GeneratorSystem R A}
variable {theta : Cardinal.{u}}

def maxPcfWitnessOfCertificate
    (C : GeneratorSystem.FiniteGeneratorClosureCertificate G theta)
    (hTheta : R.pcf A theta) :
    MaxPcfWitness R A where
  theta := theta
  isMax := by
    constructor
    · exact hTheta
    · exact C.pcf_bounded

theorem hasMaxPcf_of_certificate
    (C : GeneratorSystem.FiniteGeneratorClosureCertificate G theta)
    (hTheta : R.pcf A theta) :
    HasMaxPcf R A :=
  ⟨theta, (maxPcfWitnessOfCertificate C hTheta).isMax⟩

end FiniteGeneratorClosureCertificate

theorem maxPcf_mem
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    {theta : Cardinal.{u}}
    (hMax : IsMaxPcf R A theta) :
    R.pcf A theta :=
  hMax.left

theorem maxPcf_bounds
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    {theta beta : Cardinal.{u}}
    (hMax : IsMaxPcf R A theta)
    (hBeta : R.pcf A beta) :
    beta <= theta :=
  hMax.right beta hBeta

theorem isMaxPcf_unique
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    {theta beta : Cardinal.{u}}
    (hTheta : IsMaxPcf R A theta)
    (hBeta : IsMaxPcf R A beta) :
    theta = beta :=
  le_antisymm
    (hBeta.right theta hTheta.left)
    (hTheta.right beta hBeta.left)

namespace MaxPcfWitness

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}

theorem mem_pcf
    (M : MaxPcfWitness R A) :
    R.pcf A M.theta :=
  maxPcf_mem M.isMax

theorem isRegular
    (M : MaxPcfWitness R A) :
    Cardinal.IsRegular M.theta :=
  R.mem_pcf_regular M.mem_pcf

theorem bounds
    (M : MaxPcfWitness R A)
    {beta : Cardinal.{u}}
    (hBeta : R.pcf A beta) :
    beta <= M.theta :=
  maxPcf_bounds M.isMax hBeta

theorem hasMaxPcf
    (M : MaxPcfWitness R A) :
    HasMaxPcf R A :=
  Exists.intro M.theta M.isMax

theorem theta_eq
    (M N : MaxPcfWitness R A) :
    M.theta = N.theta :=
  isMaxPcf_unique M.isMax N.isMax

/-- Maximal PCF values are monotone under inclusion of the represented PCF
sets. This is independent of generators and no-holes. -/
theorem theta_le_of_pcf_subset
    {B : CardSet.{u}}
    (M : MaxPcfWitness R A)
    (N : MaxPcfWitness R B)
    (hSubset : SubsetOf (R.pcf A) (R.pcf B)) :
    M.theta <= N.theta :=
  N.bounds (hSubset M.theta M.mem_pcf)

/-- Maximal PCF values agree whenever the represented PCF sets agree, even
when the underlying cardinal-set parameters differ. -/
theorem theta_eq_of_pcf_eq
    {B : CardSet.{u}}
    (M : MaxPcfWitness R A)
    (N : MaxPcfWitness R B)
    (hEq : R.pcf A = R.pcf B) :
    M.theta = N.theta := by
  apply le_antisymm
  · apply M.theta_le_of_pcf_subset N
    intro theta hTheta
    rw [← hEq]
    exact hTheta
  · apply N.theta_le_of_pcf_subset M
    intro theta hTheta
    rw [hEq]
    exact hTheta

/-! A maximum witness can be transported across equality of the represented
PCF sets. This changes only the parameter set of the witness; it does not
construct either the equality or a maximum witness from scratch. -/
def of_pcf_eq
    {B : CardSet.{u}}
    (M : MaxPcfWitness R A)
    (hEq : R.pcf A = R.pcf B) :
    MaxPcfWitness R B where
  theta := M.theta
  isMax := And.intro
    (by
      have hMem := M.mem_pcf
      rw [hEq] at hMem
      exact hMem)
    (by
      intro beta hBeta
      apply M.bounds
      have hPcf : R.pcf A beta := by
        rw [hEq]
        exact hBeta
      exact hPcf)

end MaxPcfWitness

/-! A finite PCF value set has a maximum independently of how its values were
represented. This is only an order-theoretic finite-set construction: it does
not prove that a general PCF value set is finite or nonempty. -/

noncomputable def maxPcfWitnessOfFinitePcfSet
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    [Finite { theta : Cardinal.{u} // R.pcf A theta }]
    (hNonempty : exists theta, R.pcf A theta) :
    MaxPcfWitness R A := by
  classical
  letI : Nonempty { theta : Cardinal.{u} // R.pcf A theta } := by
    obtain ⟨theta, hTheta⟩ := hNonempty
    exact ⟨⟨theta, hTheta⟩⟩
  letI : Fintype { theta : Cardinal.{u} // R.pcf A theta } :=
    Fintype.ofFinite _
  let iMax : { theta : Cardinal.{u} // R.pcf A theta } :=
    Finset.univ.max' Finset.univ_nonempty
  exact {
    theta := iMax.1
    isMax := by
      constructor
      · exact iMax.2
      · intro beta hBeta
        let iBeta : { theta : Cardinal.{u} // R.pcf A theta } :=
          ⟨beta, hBeta⟩
        exact Finset.le_max' Finset.univ iBeta (Finset.mem_univ iBeta)
  }

theorem hasMaxPcf_of_finitePcfSet
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    [Finite { theta : Cardinal.{u} // R.pcf A theta }]
    (hNonempty : exists theta, R.pcf A theta) :
    HasMaxPcf R A :=
  (maxPcfWitnessOfFinitePcfSet hNonempty).hasMaxPcf

theorem hasMaxPcf_iff_nonempty_of_finitePcfSet
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    [Finite { theta : Cardinal.{u} // R.pcf A theta }] :
    HasMaxPcf R A <-> exists theta, R.pcf A theta := by
  constructor
  · rintro ⟨theta, hMax⟩
    exact ⟨theta, hMax.1⟩
  · intro hNonempty
    exact hasMaxPcf_of_finitePcfSet hNonempty

/-! A fixed-point equality transports the maximum-PCF question exactly to
the ordinary greatest-element question on the fixed-point set. -/

theorem MaxPcfWitness.isGreatest_of_pcf_eq
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (M : MaxPcfWitness R A)
    (hPcfEq : R.pcf A = A) :
    IsGreatest A M.theta := by
  constructor
  · have hMem := M.mem_pcf
    rw [hPcfEq] at hMem
    exact hMem
  · intro beta hBeta
    apply M.bounds
    have hPcf : R.pcf A beta := by
      rw [hPcfEq]
      exact hBeta
    exact hPcf

noncomputable def maxPcfWitnessOfGreatest_of_pcf_eq
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (hPcfEq : R.pcf A = A)
    {theta : Cardinal.{u}}
    (hGreatest : IsGreatest A theta) :
    MaxPcfWitness R A where
  theta := theta
  isMax := by
    constructor
    · have hMem := hGreatest.1
      rw [← hPcfEq] at hMem
      exact hMem
    · intro beta hBeta
      have hA : A beta := by
        rw [hPcfEq] at hBeta
        exact hBeta
      exact hGreatest.2 hA

theorem hasMaxPcf_iff_exists_greatest_of_pcf_eq
    {R : PcfRepresentation.{u, v, w, x}}
    {A : CardSet.{u}}
    (hPcfEq : R.pcf A = A) :
    HasMaxPcf R A <-> exists theta, IsGreatest A theta := by
  constructor
  · rintro ⟨theta, hMax⟩
    let M : MaxPcfWitness R A :=
      { theta := theta, isMax := hMax }
    exact ⟨theta, M.isGreatest_of_pcf_eq hPcfEq⟩
  · rintro ⟨theta, hGreatest⟩
    exact (maxPcfWitnessOfGreatest_of_pcf_eq hPcfEq hGreatest).hasMaxPcf

theorem GeneratorSystem.belowIdeal_isProper_of_le_max
    (G : GeneratorSystem R A)
    (M : MaxPcfWitness R A)
    {theta : Cardinal.{u}}
    (hTheta : theta <= M.theta) :
    Ideal.IsProper (G.belowIdeal theta) :=
  (G.belowIdeal_isProper_iff_exists_pcf_not_lt theta).mpr
    ⟨M.theta, M.mem_pcf, not_lt_of_ge hTheta⟩

theorem GeneratorSystem.atMostIdeal_isProper_of_lt_max
    (G : GeneratorSystem R A)
    (M : MaxPcfWitness R A)
    {theta : Cardinal.{u}}
    (hTheta : theta < M.theta) :
    Ideal.IsProper (G.atMostIdeal theta) :=
  (G.atMostIdeal_isProper_iff_exists_pcf_gt theta).mpr
    ⟨M.theta, M.mem_pcf, hTheta⟩

theorem GeneratorSystem.belowIdeal_isProper_iff_le_max
    (G : GeneratorSystem R A)
    (M : MaxPcfWitness R A)
    {theta : Cardinal.{u}} :
    Ideal.IsProper (G.belowIdeal theta) <-> theta <= M.theta := by
  constructor
  · intro hProper
    obtain ⟨beta, hBeta, hNotLt⟩ :=
      (G.belowIdeal_isProper_iff_exists_pcf_not_lt theta).mp hProper
    exact (le_of_not_gt hNotLt).trans (M.bounds hBeta)
  · exact G.belowIdeal_isProper_of_le_max M

theorem GeneratorSystem.atMostIdeal_isProper_iff_lt_max
    (G : GeneratorSystem R A)
    (M : MaxPcfWitness R A)
    {theta : Cardinal.{u}} :
    Ideal.IsProper (G.atMostIdeal theta) <-> theta < M.theta := by
  constructor
  · intro hProper
    obtain ⟨beta, hBeta, hThetaBeta⟩ :=
      (G.atMostIdeal_isProper_iff_exists_pcf_gt theta).mp hProper
    exact hThetaBeta.trans_le (M.bounds hBeta)
  · exact G.atMostIdeal_isProper_of_lt_max M

theorem GeneratorSystem.isMaxPcf_iff_atMostIdeal_not_isProper
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}} :
    IsMaxPcf R A theta <->
      R.pcf A theta /\ Not (Ideal.IsProper (G.atMostIdeal theta)) := by
  constructor
  · rintro ⟨hTheta, hMax⟩
    constructor
    · exact hTheta
    · intro hProper
      obtain ⟨beta, hBeta, hGt⟩ :=
        (G.atMostIdeal_isProper_iff_exists_pcf_gt theta).mp hProper
      exact (not_lt_of_ge (hMax beta hBeta)) hGt
  · rintro ⟨hTheta, hNotProper⟩
    constructor
    · exact hTheta
    · intro beta hBeta
      by_contra hNotLe
      apply hNotProper
      exact (G.atMostIdeal_isProper_iff_exists_pcf_gt theta).mpr
        ⟨beta, hBeta, lt_of_not_ge hNotLe⟩

theorem GeneratorSystem.atMostIdeal_not_isProper_of_max
    (G : GeneratorSystem R A)
    (M : MaxPcfWitness R A) :
    Not (Ideal.IsProper (G.atMostIdeal M.theta)) :=
  (G.isMaxPcf_iff_atMostIdeal_not_isProper).mp M.isMax |>.2

/-- A PCF member at which the at-most filtration becomes improper is a
maximum PCF witness. This isolates the ideal-theoretic obligation needed for
maximum existence; it does not prove that such a member exists. -/
def GeneratorSystem.maxPcfWitnessOfAtMostIdealNotProper
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hNotProper : Not (Ideal.IsProper (G.atMostIdeal theta))) :
    MaxPcfWitness R A where
  theta := theta
  isMax := G.isMaxPcf_iff_atMostIdeal_not_isProper.mpr
    ⟨hTheta, hNotProper⟩

/-- A cardinal is the maximum PCF value exactly when the semantic filtration
jumps there: the strict-below ideal remains proper, while the at-most ideal is
improper. In the reverse direction, PCF membership of the threshold is
derived rather than assumed. -/
theorem GeneratorSystem.isMaxPcf_iff_criticalThreshold
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}} :
    IsMaxPcf R A theta <->
      Ideal.IsProper (G.belowIdeal theta) /\
        Not (Ideal.IsProper (G.atMostIdeal theta)) := by
  constructor
  · intro hMax
    let M : MaxPcfWitness R A := ⟨theta, hMax⟩
    exact ⟨G.belowIdeal_isProper_of_le_max M (le_refl theta),
      G.atMostIdeal_not_isProper_of_max M⟩
  · rintro ⟨hBelowProper, hAtMostNotProper⟩
    obtain ⟨beta, hBeta, hNotLt⟩ :=
      (G.belowIdeal_isProper_iff_exists_pcf_not_lt theta).mp
        hBelowProper
    have hBetaLe : beta <= theta := by
      by_contra hNotLe
      apply hAtMostNotProper
      exact (G.atMostIdeal_isProper_iff_exists_pcf_gt theta).mpr
        ⟨beta, hBeta, lt_of_not_ge hNotLe⟩
    have hBetaEq : beta = theta :=
      le_antisymm hBetaLe (le_of_not_gt hNotLt)
    apply G.isMaxPcf_iff_atMostIdeal_not_isProper.mpr
    exact ⟨by simpa only [hBetaEq] using hBeta, hAtMostNotProper⟩

/-- A threshold where the strict-below filtration is still proper but the
at-most filtration is improper determines a maximum PCF witness. Unlike
`maxPcfWitnessOfAtMostIdealNotProper`, PCF membership of the threshold is
derived from the two semantic filtration contracts. -/
def GeneratorSystem.maxPcfWitnessOfCriticalThreshold
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hBelowProper : Ideal.IsProper (G.belowIdeal theta))
    (hAtMostNotProper : Not (Ideal.IsProper (G.atMostIdeal theta))) :
    MaxPcfWitness R A where
  theta := theta
  isMax := G.isMaxPcf_iff_criticalThreshold.mpr
    ⟨hBelowProper, hAtMostNotProper⟩

/-- Existence of a maximum PCF value is exactly existence of a PCF member at
which the at-most filtration is improper. This is a reformulation of the
remaining existence obligation, not a proof that the critical member exists.
-/
theorem GeneratorSystem.hasMaxPcf_iff_exists_atMostIdeal_not_isProper
    (G : GeneratorSystem R A) :
    HasMaxPcf R A <->
      exists theta, R.pcf A theta /\
        Not (Ideal.IsProper (G.atMostIdeal theta)) := by
  constructor
  · rintro ⟨theta, hMax⟩
    exact ⟨theta,
      G.isMaxPcf_iff_atMostIdeal_not_isProper.mp hMax⟩
  · rintro ⟨theta, hTheta, hNotProper⟩
    exact (G.maxPcfWitnessOfAtMostIdealNotProper
      hTheta hNotProper).hasMaxPcf

/-- Maximum PCF existence is equivalent to a genuine jump in the filtration:
the strict-below ideal is proper at some threshold while the corresponding
at-most ideal is not. The reverse implication derives that the threshold is a
PCF member; no membership premise is hidden in the right-hand side. -/
theorem GeneratorSystem.hasMaxPcf_iff_exists_criticalThreshold
    (G : GeneratorSystem R A) :
    HasMaxPcf R A <->
      exists theta,
        Ideal.IsProper (G.belowIdeal theta) /\
          Not (Ideal.IsProper (G.atMostIdeal theta)) := by
  constructor
  · rintro ⟨theta, hMax⟩
    let M : MaxPcfWitness R A := ⟨theta, hMax⟩
    exact ⟨theta,
      G.belowIdeal_isProper_of_le_max M (le_refl theta),
      G.atMostIdeal_not_isProper_of_max M⟩
  · rintro ⟨theta, hBelowProper, hAtMostNotProper⟩
    exact (G.maxPcfWitnessOfCriticalThreshold
      hBelowProper hAtMostNotProper).hasMaxPcf

theorem GeneratorSystem.isMaxPcf_iff_generator_eventually_below
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta) :
    IsMaxPcf R A theta <->
      (G.belowIdeal theta).Eventually (G.generator theta) := by
  constructor
  · intro hMax
    by_contra hNotEventually
    apply (G.atMostIdeal_not_isProper_of_max
      ⟨theta, hMax⟩)
    exact (Ideal.isProper_equivalent_iff
      (G.ideal_equiv_of_mem_pcf hTheta)).mpr
      (((G.belowIdeal theta).extendBy_isProper_iff_not_eventually
        (G.generator theta)).mpr hNotEventually)
  · intro hEventually
    apply (G.isMaxPcf_iff_atMostIdeal_not_isProper).mpr
    constructor
    · exact hTheta
    · intro hProper
      exact ((G.belowIdeal theta).extendBy_isProper_iff_not_eventually
        (G.generator theta)).mp
        ((Ideal.isProper_equivalent_iff
          (G.ideal_equiv_of_mem_pcf hTheta)).mp hProper)
        hEventually

theorem GeneratorSystem.generator_eventually_below_of_max
    (G : GeneratorSystem R A)
    (M : MaxPcfWitness R A) :
    (G.belowIdeal M.theta).Eventually (G.generator M.theta) :=
  (G.isMaxPcf_iff_generator_eventually_below M.mem_pcf).mp M.isMax

/-- A PCF member whose generator is eventually present modulo its strict
lower ideal determines a maximum PCF witness. PCF membership remains an
explicit premise. -/
def GeneratorSystem.maxPcfWitnessOfGeneratorEventuallyBelow
    (G : GeneratorSystem R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hEventually :
      (G.belowIdeal theta).Eventually (G.generator theta)) :
    MaxPcfWitness R A where
  theta := theta
  isMax := (G.isMaxPcf_iff_generator_eventually_below hTheta).mpr
    hEventually

/-- Maximum PCF existence is equivalent to a PCF generator becoming
eventually present at its own threshold. The right side is the explicit
generator-theoretic existence obligation. -/
theorem GeneratorSystem.hasMaxPcf_iff_exists_generator_eventually_below
    (G : GeneratorSystem R A) :
    HasMaxPcf R A <->
      exists theta, R.pcf A theta /\
        (G.belowIdeal theta).Eventually (G.generator theta) := by
  constructor
  · rintro ⟨theta, hMax⟩
    exact ⟨theta, hMax.1,
      (G.isMaxPcf_iff_generator_eventually_below hMax.1).mp hMax⟩
  · rintro ⟨theta, hTheta, hEventually⟩
    exact (G.maxPcfWitnessOfGeneratorEventuallyBelow
      hTheta hEventually).hasMaxPcf

theorem GeneratorSystem.generated_isProper_of_mem_pcf_lt_max
    (G : GeneratorSystem R A)
    (M : MaxPcfWitness R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hThetaMax : theta < M.theta) :
    Ideal.IsProper
      ((G.belowIdeal theta).extendBy (G.generator theta)) :=
  G.generated_isProper hTheta
    (G.atMostIdeal_isProper_of_lt_max M hThetaMax)

theorem GeneratorSystem.generator_not_eventually_below_of_mem_pcf_lt_max
    (G : GeneratorSystem R A)
    (M : MaxPcfWitness R A)
    {theta : Cardinal.{u}}
    (hTheta : R.pcf A theta)
    (hThetaMax : theta < M.theta) :
    Not ((G.belowIdeal theta).Eventually (G.generator theta)) :=
  G.generator_not_eventually_below hTheta
    (G.atMostIdeal_isProper_of_lt_max M hThetaMax)

structure PcfStructuralHypotheses
    (R : PcfRepresentation.{u, v, w, x})
    (A : CardSet.{u}) where
  generators : GeneratorSystem R A
  no_holes : NoHolesStatement R A
  maxPcf : MaxPcfWitness R A

namespace PcfStructuralHypotheses

variable {R : PcfRepresentation.{u, v, w, x}}
variable {A : CardSet.{u}}

def generators_field
    (H : PcfStructuralHypotheses R A) :
    GeneratorSystem R A :=
  H.generators

theorem no_holes_field
    (H : PcfStructuralHypotheses R A) :
    NoHolesStatement R A :=
  H.no_holes

def maxPcf_field
    (H : PcfStructuralHypotheses R A) :
    MaxPcfWitness R A :=
  H.maxPcf

theorem maxPcf_mem
    (H : PcfStructuralHypotheses R A) :
    R.pcf A H.maxPcf.theta :=
  H.maxPcf.mem_pcf

theorem maxPcf_isRegular
    (H : PcfStructuralHypotheses R A) :
    Cardinal.IsRegular H.maxPcf.theta :=
  H.maxPcf.isRegular

theorem maxPcf_bounds
    (H : PcfStructuralHypotheses R A)
    {beta : Cardinal.{u}}
    (hBeta : R.pcf A beta) :
    beta <= H.maxPcf.theta :=
  H.maxPcf.bounds hBeta

theorem has_max_pcf
    (H : PcfStructuralHypotheses R A) :
    HasMaxPcf R A :=
  H.maxPcf.hasMaxPcf

theorem mem_pcf_of_between_member_and_max
    (H : PcfStructuralHypotheses R A)
    (hRegulars : SetOfRegulars A)
    (hProgressive : ProgressiveCardSet A)
    (hInterval : CardinalInterval A)
    {left theta : Cardinal.{u}}
    (hLeft : R.pcf A left)
    (hRegular : Cardinal.IsRegular theta)
    (hBetween : Between left theta H.maxPcf.theta) :
    R.pcf A theta :=
  H.no_holes hRegulars hProgressive hInterval
    hLeft H.maxPcf.mem_pcf hRegular hBetween

end PcfStructuralHypotheses

end PcfProject
