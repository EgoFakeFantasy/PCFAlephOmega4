import PcfProject.PcfGeneratorConstruction
import Mathlib.Logic.Small.List

/-!
# Finite-path construction for transitive generators

This implements the path-composition part of Jech 24.31 and constructs a
universal seed bounding all finite-path composite families. Cofinally high
characteristic agreement for the coordinate-function family remains an
explicit input; this module does not yet construct the elementary chain.
-/

namespace PcfProject

universe u

/-- A finite path through a displayed family of thinned generators. -/
inductive GeneratorPath {A : CardSet.{u}}
    (B : Cardinal.{u} -> CardSet.{u}) : CardinalIndex A -> CardinalIndex A -> Type (u + 1)
  | refl (i) : GeneratorPath B i i
  | step {i j k} (edge : B j.1 i.1) (tail : GeneratorPath B j k) : GeneratorPath B i k

noncomputable def GeneratorPath.append {A : CardSet.{u}} {B : Cardinal.{u} -> CardSet.{u}}
    {i j k : CardinalIndex A} (p : GeneratorPath B i j) (q : GeneratorPath B j k) :
    GeneratorPath B i k := by
  induction p with
  | refl => exact q
  | step edge _ ih => exact .step edge (ih q)

#print axioms GeneratorPath.append

/-- Iterated evaluation along the chosen finite path, from its terminal
coordinate back to its initial coordinate, as in Jech (24.17). -/
noncomputable def GeneratorPath.eval {A : CardSet.{u}} {B : Cardinal.{u} -> CardSet.{u}}
    (f : forall j : CardinalIndex A, j.1.ord.ToType ->
      forall i : CardinalIndex A, i.1.ord.ToType)
    {i j : CardinalIndex A} (p : GeneratorPath B i j) : j.1.ord.ToType -> i.1.ord.ToType := by
  induction p with
  | refl => exact id
  | @step i j k edge tail ih => exact fun alpha => f j (ih alpha) i

#print axioms GeneratorPath.eval

theorem GeneratorPath.eval_characteristic
    {A : CardSet.{u}} {B : Cardinal.{u} -> CardSet.{u}}
    (f : forall j : CardinalIndex A, j.1.ord.ToType ->
      forall i : CardinalIndex A, i.1.ord.ToType)
    (chi : forall i : CardinalIndex A, i.1.ord.ToType)
    (hAgreement : forall i j : CardinalIndex A, B j.1 i.1 -> f j (chi j) i = chi i)
    {i j : CardinalIndex A} (p : GeneratorPath B i j) :
    p.eval f (chi j) = chi i := by
  induction p with
  | refl => rfl
  | @step i j k edge tail ih =>
      change f j (tail.eval f (chi k)) i = chi i
      rw [ih]
      exact hAgreement i j edge

#print axioms GeneratorPath.eval_characteristic

def generatorPathClosure {A : CardSet.{u}}
    (B : Cardinal.{u} -> CardSet.{u}) (lambda : Cardinal.{u}) : CardSet.{u} :=
  fun nu => exists hNu : A nu, exists hLambda : A lambda,
    Nonempty (GeneratorPath B ⟨nu, hNu⟩ ⟨lambda, hLambda⟩)

theorem generatorPathClosure_subset {A : CardSet.{u}}
    (B : Cardinal.{u} -> CardSet.{u}) (lambda : Cardinal.{u}) :
    SubsetOf (generatorPathClosure (A := A) B lambda) A := by
  rintro nu ⟨hNu, _, _⟩
  exact hNu

#print axioms generatorPathClosure_subset

theorem generatorPathClosure_contains {A : CardSet.{u}}
    (B : Cardinal.{u} -> CardSet.{u}) {lambda : Cardinal.{u}} (hLambda : A lambda)
    (hSubset : SubsetOf (B lambda) A) :
    SubsetOf (B lambda) (generatorPathClosure (A := A) B lambda) := by
  intro nu hNu
  exact ⟨hSubset nu hNu, hLambda, ⟨.step hNu (.refl _)⟩⟩

#print axioms generatorPathClosure_contains

theorem generatorPathClosure_transitive {A : CardSet.{u}}
    (B : Cardinal.{u} -> CardSet.{u}) {mu lambda : Cardinal.{u}}
    (hMu : generatorPathClosure (A := A) B lambda mu) :
    SubsetOf (generatorPathClosure (A := A) B mu) (generatorPathClosure (A := A) B lambda) := by
  obtain ⟨hMuA, hLambda, ⟨q⟩⟩ := hMu
  rintro nu ⟨hNu, _, ⟨p⟩⟩
  exact ⟨hNu, hLambda, ⟨p.append q⟩⟩

#print axioms generatorPathClosure_transitive

noncomputable def generatorPathCompositeFamily
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (B : Cardinal.{u} -> CardSet.{u})
    (f : forall j : CardinalIndex A, j.1.ord.ToType ->
      forall i : CardinalIndex A, i.1.ord.ToType)
    (lambda : CardinalIndex A) (alpha : lambda.1.ord.ToType)
    (i : CardinalIndex A) : i.1.ord.ToType := by
  classical
  exact if h : Nonempty (GeneratorPath B i lambda) then
    (Classical.choice h).eval f alpha
  else Ordinal.ToType.mk ⟨0, (hRegulars i.1 i.2).ord_pos⟩

#print axioms generatorPathCompositeFamily

theorem generatorPathCompositeFamily_characteristic
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (B : Cardinal.{u} -> CardSet.{u})
    (f : forall j : CardinalIndex A, j.1.ord.ToType ->
      forall i : CardinalIndex A, i.1.ord.ToType)
    (chi : forall i : CardinalIndex A, i.1.ord.ToType)
    (hAgreement : forall i j : CardinalIndex A, B j.1 i.1 -> f j (chi j) i = chi i)
    (lambda i : CardinalIndex A)
    (hPath : generatorPathClosure (A := A) B lambda.1 i.1) :
    generatorPathCompositeFamily hRegulars B f lambda (chi lambda) i = chi i := by
  classical
  obtain ⟨_, _, hPath⟩ := hPath
  simp only [generatorPathCompositeFamily, dif_pos hPath]
  exact GeneratorPath.eval_characteristic f chi hAgreement _

#print axioms generatorPathCompositeFamily_characteristic

/-- The terminal smallness argument: a bound on the whole composite family
lying pointwise below the characteristic defeats every path coordinate at
the characteristic index. Constructing such a characteristic-closed bound
is still a separate elementary-chain obligation. -/
theorem generatorPathClosure_small_of_characteristic_bound
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (B : Cardinal.{u} -> CardSet.{u})
    (f : forall j : CardinalIndex A, j.1.ord.ToType ->
      forall i : CardinalIndex A, i.1.ord.ToType)
    (chi : forall i : CardinalIndex A, i.1.ord.ToType)
    (hAgreement : forall i j : CardinalIndex A, B j.1 i.1 -> f j (chi j) i = chi i)
    (lambda : CardinalIndex A) (J : Ideal (CardinalIndex A))
    (g : forall i : CardinalIndex A, i.1.ord.ToType)
    (hBelow : forall i, g i < chi i)
    (hBound : forall alpha, J.Eventually (fun i =>
      generatorPathCompositeFamily hRegulars B f lambda alpha i <= g i)) :
    J.Small (fun i => generatorPathClosure (A := A) B lambda.1 i.1) := by
  apply J.subset_small (hBound (chi lambda))
  intro i hPath hLe
  rw [generatorPathCompositeFamily_characteristic hRegulars B f chi hAgreement lambda i hPath] at hLe
  exact (not_le_of_gt (hBelow i)) hLe

#print axioms generatorPathClosure_small_of_characteristic_bound

/-- Replacing a generator by an at-most-small superset of a below-equivalent
thinning preserves the full semantic generator identity. -/
theorem GeneratorSystem.ideal_equiv_of_thinning_superset
    {A : CardSet.{u}} (G : GeneratorSystem cardinalProductRepresentation A)
    {theta : Cardinal.{u}} (hTheta : cardinalProductRepresentation.pcf A theta)
    (B C : CardSet.{u})
    (hDifference : (G.belowIdeal theta).Small (fun a => G.generator theta a /\ Not (B a)))
    (hBC : SubsetOf B C) (hC : (G.atMostIdeal theta).Small C) :
    Ideal.Equivalent (G.atMostIdeal theta) ((G.belowIdeal theta).extendBy C) := by
  classical
  constructor
  · intro S hS
    obtain ⟨T, hT, hCover⟩ := G.atMost_le_generated hTheta S hS
    refine ⟨(fun a => T a \/ (G.generator theta a /\ Not (B a))),
      (G.belowIdeal theta).union_small hT hDifference, ?_⟩
    intro a ha
    rcases hCover a ha with hTa | hGa
    · exact Or.inl (Or.inl hTa)
    · by_cases hBa : B a
      · exact Or.inr (hBC a hBa)
      · exact Or.inl (Or.inr ⟨hGa, hBa⟩)
  · rintro S ⟨T, hT, hCover⟩
    exact (G.atMostIdeal theta).subset_small
      ((G.atMostIdeal theta).union_small (G.belowIdeal_le_atMost theta T hT) hC) hCover

#print axioms GeneratorSystem.ideal_equiv_of_thinning_superset

/-- The finite-path suffix of Jech 24.31, with its remaining characteristic
data explicit. The hypotheses do not assert path-closure smallness or the
existence of transitive generators: both are derived here. -/
theorem exists_transitive_generators_of_characteristic_path_bounds
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hFixed : cardinalProductRepresentation.pcf A = A)
    (B : Cardinal.{u} -> CardSet.{u})
    (hBSubset : forall lambda, A lambda -> SubsetOf (B lambda) A)
    (hDifference : forall lambda, A lambda ->
      (G.belowIdeal lambda).Small (fun a => G.generator lambda a /\ Not (B lambda a)))
    (f : forall j : CardinalIndex A, j.1.ord.ToType ->
      forall i : CardinalIndex A, i.1.ord.ToType)
    (chi : forall i : CardinalIndex A, i.1.ord.ToType)
    (hAgreement : forall i j : CardinalIndex A, B j.1 i.1 -> f j (chi j) i = chi i)
    (hBounds : forall lambda : CardinalIndex A,
      exists g : forall i : CardinalIndex A, i.1.ord.ToType,
        (forall i, g i < chi i) /\
        (forall alpha, ((G.atMostIdeal lambda.1).restrictAlong
          (fun i : CardinalIndex A => i.1)).Eventually (fun i =>
            generatorPathCompositeFamily hRegulars B f lambda alpha i <= g i))) :
    exists H : GeneratorSystem cardinalProductRepresentation A,
      TransitiveGeneratorSystem H /\
      H.generator = generatorPathClosure (A := A) B := by
  have hClosureSmall : forall lambda, A lambda ->
      (G.atMostIdeal lambda).Small (generatorPathClosure (A := A) B lambda) := by
    intro lambda hLambda
    obtain ⟨g, hBelow, hBound⟩ := hBounds ⟨lambda, hLambda⟩
    have hIndexSmall := generatorPathClosure_small_of_characteristic_bound
      hRegulars B f chi hAgreement ⟨lambda, hLambda⟩
      ((G.atMostIdeal lambda).restrictAlong (fun i : CardinalIndex A => i.1)) g hBelow hBound
    apply (G.atMostIdeal lambda).subset_small hIndexSmall
    intro a ha
    exact ⟨⟨a, generatorPathClosure_subset B lambda a ha⟩, rfl, ha⟩
  let H : GeneratorSystem cardinalProductRepresentation A :=
    { G with
      generator := generatorPathClosure (A := A) B
      generator_subset := fun {_} _ => generatorPathClosure_subset B _
      generator_ideal_equiv := by
        intro lambda hLambda
        have hLambdaA : A lambda := hFixed ▸ hLambda
        exact G.ideal_equiv_of_thinning_superset hLambda (B lambda) _
          (hDifference lambda hLambdaA)
          (generatorPathClosure_contains B hLambdaA (hBSubset lambda hLambdaA))
          (hClosureSmall lambda hLambdaA) }
  exact ⟨H, fun {_ _} h => generatorPathClosure_transitive B h, rfl⟩

#print axioms exists_transitive_generators_of_characteristic_path_bounds

/-- A path is coded by its successive vertices; edge proofs carry no data. -/
noncomputable def GeneratorPath.code {A : CardSet.{u}} {B : Cardinal.{u} -> CardSet.{u}}
    {i j : CardinalIndex A} (p : GeneratorPath B i j) : List (CardinalIndex A) := by
  induction p with
  | refl => exact []
  | @step i j k _ _ ih => exact j :: ih

#print axioms GeneratorPath.code

theorem GeneratorPath.code_injective {A : CardSet.{u}} {B : Cardinal.{u} -> CardSet.{u}}
    {i j : CardinalIndex A} : Function.Injective (@GeneratorPath.code A B i j) := by
  intro p q h
  induction p with
  | refl =>
      cases q with
      | refl => rfl
      | step edge tail => cases h
  | @step i j k edge tail ih =>
      cases q with
      | refl => cases h
      | @step _ j' _ edge' tail' =>
          have hCons : j :: tail.code = j' :: tail'.code := h
          obtain ⟨hJ, hTail⟩ := List.cons.inj hCons
          subst j'
          have hPath := ih hTail
          cases hPath
          rfl

#print axioms GeneratorPath.code_injective

/-- Forget which thinning permitted a path. This allows all later thinnings
to share a single, preselected family of bounds. -/
noncomputable def GeneratorPath.erase {A : CardSet.{u}} {B : Cardinal.{u} -> CardSet.{u}}
    {i j : CardinalIndex A} (p : GeneratorPath B i j) : GeneratorPath (fun _ _ => True) i j := by
  induction p with
  | refl => exact .refl _
  | step _ _ ih => exact .step trivial ih

#print axioms GeneratorPath.erase

theorem GeneratorPath.eval_erase {A : CardSet.{u}} {B : Cardinal.{u} -> CardSet.{u}}
    (f : forall j : CardinalIndex A, j.1.ord.ToType -> forall i : CardinalIndex A, i.1.ord.ToType)
    {i j : CardinalIndex A} (p : GeneratorPath B i j) (alpha : j.1.ord.ToType) :
    p.erase.eval f alpha = p.eval f alpha := by
  induction p with
  | refl => rfl
  | @step i j k edge tail ih =>
      change f j (tail.erase.eval f alpha) i = f j (tail.eval f alpha) i
      rw [ih]

#print axioms GeneratorPath.eval_erase

def UniversalGeneratorPathChoices (A : CardSet.{u}) :=
  Sigma fun lambda : CardinalIndex A =>
    forall i : CardinalIndex A, Option (GeneratorPath (fun _ _ => True) i lambda)

noncomputable def universalGeneratorPathChoicesCode {A : CardSet.{u}}
    (q : UniversalGeneratorPathChoices A) :
    CardinalIndex A × (CardinalIndex A -> Option (List (CardinalIndex A))) :=
  ⟨q.1, fun i => (q.2 i).map GeneratorPath.code⟩

#print axioms universalGeneratorPathChoicesCode

theorem universalGeneratorPathChoicesCode_injective {A : CardSet.{u}} :
    Function.Injective (@universalGeneratorPathChoicesCode A) := by
  rintro ⟨lambda, p⟩ ⟨mu, q⟩ h
  have hLambda : lambda = mu := congrArg Prod.fst h
  subst mu
  have hCodes : (fun i => (p i).map GeneratorPath.code) =
      (fun i => (q i).map GeneratorPath.code) := congrArg Prod.snd h
  have hPQ : p = q := by
    funext i
    have hi := congrFun hCodes i
    cases hp : p i with
    | none =>
        cases hq : q i with
        | none => rfl
        | some t =>
            simp only [hp, hq, Option.map_none, Option.map_some] at hi
            cases hi
    | some s =>
        cases hq : q i with
        | none =>
            simp only [hp, hq, Option.map_none, Option.map_some] at hi
            cases hi
        | some t =>
            rw [hp, hq] at hi
            have hCode : s.code = t.code := Option.some.inj hi
            exact congrArg Option.some (GeneratorPath.code_injective hCode)
  cases hPQ
  rfl

#print axioms universalGeneratorPathChoicesCode_injective

theorem mk_universalGeneratorPathChoices_le_two_power
    {A : CardSet.{u}} (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A)) :
    Cardinal.mk (UniversalGeneratorPathChoices A) <=
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) := by
  have hList : Cardinal.mk (List (CardinalIndex A)) <= Cardinal.mk (CardinalIndex A) :=
    (Cardinal.mk_list_le_max _).trans_eq (max_eq_right hInfinite)
  have hOption : Cardinal.mk (Option (List (CardinalIndex A))) <= Cardinal.mk (CardinalIndex A) := by
    rw [Cardinal.mk_option]
    exact (add_le_add hList (le_refl (1 : Cardinal.{u + 1}))).trans_eq (Cardinal.add_one_eq hInfinite)
  have hCode := Cardinal.mk_le_of_injective (@universalGeneratorPathChoicesCode_injective A)
  have hArrow : Cardinal.mk (CardinalIndex A -> Option (List (CardinalIndex A))) <=
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) := by
    rw [Cardinal.mk_arrow]
    simp only [Cardinal.lift_id]
    exact (Cardinal.power_le_power_right hOption).trans_eq (Cardinal.power_self_eq hInfinite)
  calc
    Cardinal.mk (UniversalGeneratorPathChoices A) <=
        Cardinal.mk (CardinalIndex A × (CardinalIndex A -> Option (List (CardinalIndex A)))) := hCode
    _ <= Cardinal.mk (CardinalIndex A) * ((2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A)) := by
      simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
        mul_le_mul_right hArrow (Cardinal.mk (CardinalIndex A))
    _ = _ := by
      rw [Cardinal.mul_eq_max_of_aleph0_le_left hInfinite
        (ne_of_gt ((zero_le : (0 : Cardinal.{u + 1}) <= Cardinal.mk (CardinalIndex A)).trans_lt (Cardinal.cantor _)))]
      exact max_eq_right (Cardinal.cantor _).le

#print axioms mk_universalGeneratorPathChoices_le_two_power

noncomputable def universalGeneratorPathComposite
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (f : forall j : CardinalIndex A, j.1.ord.ToType -> forall i : CardinalIndex A, i.1.ord.ToType)
    (q : UniversalGeneratorPathChoices A) (alpha : q.1.1.ord.ToType)
    (i : CardinalIndex A) : i.1.ord.ToType :=
  match q.2 i with
  | none => Ordinal.ToType.mk ⟨0, (hRegulars i.1 i.2).ord_pos⟩
  | some p => p.eval f alpha

#print axioms universalGeneratorPathComposite

noncomputable def generatorErasedPathChoices
    {A : CardSet.{u}} (B : Cardinal.{u} -> CardSet.{u}) (lambda : CardinalIndex A) :
    UniversalGeneratorPathChoices A := by
  classical
  exact ⟨lambda, fun i => if h : Nonempty (GeneratorPath B i lambda) then
    some (Classical.choice h).erase else none⟩

#print axioms generatorErasedPathChoices

theorem universalGeneratorPathComposite_erased
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (B : Cardinal.{u} -> CardSet.{u})
    (f : forall j : CardinalIndex A, j.1.ord.ToType -> forall i : CardinalIndex A, i.1.ord.ToType)
    (lambda : CardinalIndex A) (alpha : lambda.1.ord.ToType) (i : CardinalIndex A) :
    universalGeneratorPathComposite hRegulars f (generatorErasedPathChoices B lambda) alpha i =
      generatorPathCompositeFamily hRegulars B f lambda alpha i := by
  classical
  by_cases h : Nonempty (GeneratorPath B i lambda)
  · simp only [universalGeneratorPathComposite, generatorErasedPathChoices,
      generatorPathCompositeFamily, dif_pos h]
    exact GeneratorPath.eval_erase f _ alpha
  · simp only [universalGeneratorPathComposite, generatorErasedPathChoices,
      generatorPathCompositeFamily, dif_neg h]

#print axioms universalGeneratorPathComposite_erased

/-- Simultaneously preselect bounds for every finite-path choice, before the
thinned edge relation or characteristic function is known. The powerset gap
puts this entire family below one pointwise seed. -/
theorem exists_universalGeneratorPathBound_seed
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hDirected : GeneratorAtMostIdealSuccessorDirected G)
    (f : forall j : CardinalIndex A, j.1.ord.ToType -> forall i : CardinalIndex A, i.1.ord.ToType) :
    exists seed : forall i : CardinalIndex A, i.1.ord.ToType,
      forall (B : Cardinal.{u} -> CardSet.{u}) (lambda : CardinalIndex A),
        exists g : forall i : CardinalIndex A, i.1.ord.ToType,
          (forall i, g i < seed i) /\
          (forall alpha, ((G.atMostIdeal lambda.1).restrictAlong
            (fun i : CardinalIndex A => i.1)).Eventually (fun i =>
              generatorPathCompositeFamily hRegulars B f lambda alpha i <= g i)) := by
  classical
  letI : Small.{u} (CardinalIndex A) := hSmall
  letI : Small.{u} (Option (List (CardinalIndex A))) :=
    small_map (Equiv.optionEquivSumPUnit (List (CardinalIndex A)))
  letI : Small.{u} (UniversalGeneratorPathChoices A) :=
    small_of_injective (@universalGeneratorPathChoicesCode_injective A)
  have hBounds : forall q : UniversalGeneratorPathChoices A,
      exists g : forall i : CardinalIndex A, i.1.ord.ToType,
        forall alpha, ((G.atMostIdeal q.1.1).restrictAlong
          (fun i : CardinalIndex A => i.1)).Eventually (fun i =>
            universalGeneratorPathComposite hRegulars f q alpha i <= g i) := by
    intro q
    have hDir := hDirected A (fun _ h => h) q.1.1
      (cardinalProductRepresentation_mem_pcf_of_mem hRegulars q.1.2)
    obtain ⟨g, hg⟩ := hDir q.1.1.ord.ToType
      (by simpa only [Cardinal.mk_ord_toType] using Order.lt_succ q.1.1)
      (universalGeneratorPathComposite hRegulars f q)
    exact ⟨g, fun alpha =>
      ((G.atMostIdeal q.1.1).restrictAlong (fun i : CardinalIndex A => i.1)).eventually_mono
        (hg alpha) (fun _ h => h.1)⟩
  choose g hg using hBounds
  have hSize : forall a, A a ->
      Cardinal.mk (Shrink.{u} (UniversalGeneratorPathChoices A)) < a := by
    intro a ha
    apply Cardinal.lift_lt.{u, u + 1}.mp
    rw [Cardinal.lift_mk_shrink'']
    exact (mk_universalGeneratorPathChoices_le_two_power hInfinite).trans_lt (hPower a ha)
  obtain ⟨seed, hSeed⟩ := cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt
    hRegulars hSize (fun t : Shrink.{u} (UniversalGeneratorPathChoices A) =>
      g ((equivShrink _).symm t))
  refine ⟨seed, ?_⟩
  intro B lambda
  let q := generatorErasedPathChoices B lambda
  refine ⟨g q, ?_, ?_⟩
  · intro i
    simpa only [Equiv.symm_apply_apply] using hSeed (equivShrink _ q) i
  · intro alpha
    simpa only [q, universalGeneratorPathComposite_erased] using hg q alpha

#print axioms exists_universalGeneratorPathBound_seed

/-- The path-bound hypothesis is discharged by the universal seed. The
remaining source obligation is cofinally high characteristic agreement for
the displayed family of coordinate functions, modulo each below ideal. -/
theorem exists_transitive_generators_of_cofinally_characteristic_agreement
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} a)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hFixed : cardinalProductRepresentation.pcf A = A)
    (hDirected : GeneratorAtMostIdealSuccessorDirected G)
    (f : forall j : CardinalIndex A, j.1.ord.ToType -> forall i : CardinalIndex A, i.1.ord.ToType)
    (hCharacteristics : forall seed : forall i : CardinalIndex A, i.1.ord.ToType,
      exists chi : forall i : CardinalIndex A, i.1.ord.ToType,
        (forall i, seed i <= chi i) /\
        (forall lambda : CardinalIndex A,
          ((G.belowIdeal lambda.1).restrictAlong (fun i : CardinalIndex A => i.1)).Eventually
            (fun i => G.generator lambda.1 i.1 -> f lambda (chi lambda) i = chi i))) :
    exists H : GeneratorSystem cardinalProductRepresentation A, TransitiveGeneratorSystem H := by
  classical
  obtain ⟨seed, hSeed⟩ := exists_universalGeneratorPathBound_seed
    hRegulars hSmall hInfinite hPower G hDirected f
  obtain ⟨chi, hSeedChi, hAgreement⟩ := hCharacteristics seed
  let B : Cardinal.{u} -> CardSet.{u} := fun lambda nu =>
    exists hLambda : A lambda, exists hNu : A nu,
      G.generator lambda nu /\ f ⟨lambda, hLambda⟩ (chi ⟨lambda, hLambda⟩) ⟨nu, hNu⟩ = chi ⟨nu, hNu⟩
  have hBSubset : forall lambda, A lambda -> SubsetOf (B lambda) A := by
    rintro lambda _ nu ⟨_, hNu, _⟩
    exact hNu
  have hDifference : forall lambda, A lambda ->
      (G.belowIdeal lambda).Small (fun a => G.generator lambda a /\ Not (B lambda a)) := by
    intro lambda hLambda
    have hLambdaPcf : cardinalProductRepresentation.pcf A lambda := hFixed.symm ▸ hLambda
    apply (G.belowIdeal lambda).subset_small (hAgreement ⟨lambda, hLambda⟩)
    rintro a ⟨hGa, hNot⟩
    have hAa := G.generator_subset hLambdaPcf a hGa
    refine ⟨⟨a, hAa⟩, rfl, ?_⟩
    intro hEq
    exact hNot ⟨hLambda, hAa, hGa, hEq hGa⟩
  have hEdge : forall i j : CardinalIndex A, B j.1 i.1 -> f j (chi j) i = chi i := by
    rintro i j ⟨_, _, _, hEq⟩
    exact hEq
  obtain ⟨H, hTransitive, _⟩ := exists_transitive_generators_of_characteristic_path_bounds
    hRegulars G hFixed B hBSubset hDifference f chi hEdge (by
      intro lambda
      obtain ⟨g, hg, hBound⟩ := hSeed B lambda
      exact ⟨g, fun i => (hg i).trans_le (hSeedChi i), hBound⟩)
  exact ⟨H, hTransitive⟩

#print axioms exists_transitive_generators_of_cofinally_characteristic_agreement

/-- Pointwise-strict exact upper bounds in a cardinal product are unique
modulo the ideal. This is the ideal-theoretic equality used in Jech (24.14). -/
theorem cardinalProduct_exactUpperBounds_eventually_eq
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {T : Type u} [Nonempty T]
    (d : T -> ProductElement (cardinalProductFrame A J))
    (f g : ProductElement (cardinalProductFrame A J))
    (hf : (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound d f)
    (hg : (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound d g) :
    J.Eventually (fun i => f i = g i) := by
  classical
  let X : CardinalIndex A -> Prop := fun i =>
    Not ((cardinalProductFrame A J).le i (f i) (g i))
  have hX : J.Small X := by
    by_contra hNotSmall
    have hProper : (J.localize X).IsProper := (J.localize_isProper_iff X).mpr hNotSmall
    have hgf : (cardinalProductFrame A (J.localize X)).eventuallyPointwiseLt g f := by
      change J.Small (fun i => Not
        ((cardinalProductFrame A J).le i (g i) (f i) /\
          Not ((cardinalProductFrame A J).le i (f i) (g i))) /\ X i)
      exact J.subset_small J.empty_small (by
        intro i h
        apply h.1
        exact ⟨le_of_not_ge h.2, h.2⟩)
    obtain ⟨t, ht⟩ := (ReducedProductFrame.IsPointwiseStrictExactUpperBound.localize
      (cardinalProductFrame A J) hf (Classical.choice inferInstance) X).2 g hgf
    have htg : (cardinalProductFrame A (J.localize X)).eventuallyPointwiseLt (d t) g :=
      (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
        (J.localize X) (J.le_localize X) (hg.1 t)
    have hFalse : (J.localize X).Eventually (fun _ => False) :=
      (J.localize X).eventually_mono ((J.localize X).eventually_and ht htg) (by
        intro i h
        exact h.2.2 h.1)
    exact hProper.not_eventually_false hFalse
  let Y : CardinalIndex A -> Prop := fun i =>
    Not ((cardinalProductFrame A J).le i (g i) (f i))
  have hY : J.Small Y := by
    by_contra hNotSmall
    have hProper : (J.localize Y).IsProper := (J.localize_isProper_iff Y).mpr hNotSmall
    have hfg : (cardinalProductFrame A (J.localize Y)).eventuallyPointwiseLt f g := by
      change J.Small (fun i => Not
        ((cardinalProductFrame A J).le i (f i) (g i) /\
          Not ((cardinalProductFrame A J).le i (g i) (f i))) /\ Y i)
      exact J.subset_small J.empty_small (by
        intro i h
        apply h.1
        exact ⟨le_of_not_ge h.2, h.2⟩)
    obtain ⟨t, ht⟩ := (ReducedProductFrame.IsPointwiseStrictExactUpperBound.localize
      (cardinalProductFrame A J) hg (Classical.choice inferInstance) Y).2 f hfg
    have htf : (cardinalProductFrame A (J.localize Y)).eventuallyPointwiseLt (d t) f :=
      (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
        (J.localize Y) (J.le_localize Y) (hf.1 t)
    have hFalse : (J.localize Y).Eventually (fun _ => False) :=
      (J.localize Y).eventually_mono ((J.localize Y).eventually_and ht htf) (by
        intro i h
        exact h.2.2 h.1)
    exact hProper.not_eventually_false hFalse
  exact J.subset_small (J.union_small hX hY) (by
    intro i hNe
    by_cases hle : (cardinalProductFrame A J).le i (f i) (g i)
    · exact Or.inr (fun hge => hNe (by
        have hle' : (show i.1.ord.ToType from f i) <=
            (show i.1.ord.ToType from g i) := hle
        have hge' : (show i.1.ord.ToType from g i) <=
            (show i.1.ord.ToType from f i) := hge
        exact @le_antisymm i.1.ord.ToType (inferInstance : PartialOrder i.1.ord.ToType)
          (f i) (g i) hle' hge'))
    · exact Or.inl hle)

#print axioms cardinalProduct_exactUpperBounds_eventually_eq

/-- An exact upper bound is eventually below every pointwise-strict upper
bound of the same nonempty family. This is the comparison needed when a
scale is normalized at large-cofinality limit indices. -/
theorem cardinalProduct_exactUpperBound_eventuallyLe_upperBound
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {T : Type u} [Nonempty T]
    (d : T -> ProductElement (cardinalProductFrame A J))
    (q p : ProductElement (cardinalProductFrame A J))
    (hq : (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound d q)
    (hp : (cardinalProductFrame A J).IsPointwiseStrictUpperBound d p) :
    (cardinalProductFrame A J).eventuallyLe q p := by
  classical
  let X : CardinalIndex A -> Prop := fun i =>
    Not ((cardinalProductFrame A J).le i (q i) (p i))
  change J.Small X
  by_contra hNotSmall
  have hProper : (J.localize X).IsProper :=
    (J.localize_isProper_iff X).mpr hNotSmall
  have hpq : (cardinalProductFrame A (J.localize X)).eventuallyPointwiseLt p q := by
    change J.Small (fun i => Not
      ((cardinalProductFrame A J).le i (p i) (q i) /\
        Not ((cardinalProductFrame A J).le i (q i) (p i))) /\ X i)
    exact J.subset_small J.empty_small (by
      intro i h
      apply h.1
      exact ⟨le_of_not_ge h.2, h.2⟩)
  obtain ⟨t, hpt⟩ :=
    (ReducedProductFrame.IsPointwiseStrictExactUpperBound.localize
      (cardinalProductFrame A J) hq (Classical.choice inferInstance) X).2 p hpq
  have hdp : (cardinalProductFrame A (J.localize X)).eventuallyPointwiseLt (d t) p :=
    (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
      (J.localize X) (J.le_localize X) (hp t)
  have hFalse : (J.localize X).Eventually (fun _ => False) :=
    (J.localize X).eventually_mono ((J.localize X).eventually_and hpt hdp) (by
      intro i h
      exact h.2.2 h.1)
  exact hProper.not_eventually_false hFalse

#print axioms cardinalProduct_exactUpperBound_eventuallyLe_upperBound

/-- A closed exact upper bound lying below an actual pointwise-strict upper
bound cannot reach the coordinate top on a positive set. It therefore has a
genuine product representative, which is a pointwise-strict exact upper bound. -/
theorem exists_pointwiseStrictExactUpperBound_of_closed_of_upperBound
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)}
    {T : Type u} [Nonempty T]
    (d : T -> ProductElement (cardinalProductFrame A J))
    (c : CardinalProductClosedElement A)
    (hExact : CardinalProductClosedExactUpperBound J d c)
    (p : ProductElement (cardinalProductFrame A J))
    (hUpper : (cardinalProductFrame A J).IsPointwiseStrictUpperBound d p) :
    exists q : ProductElement (cardinalProductFrame A J),
      (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound d q := by
  classical
  let Top : CardinalIndex A -> Prop := fun k => (c k).1 = k.1.ord
  have hTopSmall : J.Small Top := by
    by_contra hNot
    have hProper : (J.localize Top).IsProper := (J.localize_isProper_iff Top).mpr hNot
    have hpc : CardinalProductEventuallyLtClosed (J.localize Top) p c := by
      change J.Small (fun k => Not (cardinalProductOrdinalValue p k < (c k).1) /\ Top k)
      exact J.subset_small J.empty_small (by
        intro k h
        apply h.1
        rw [h.2]
        exact cardinalProductOrdinalValue_lt p k)
    obtain ⟨t, hpt⟩ := (hExact.localize (Classical.choice inferInstance) Top).2 p hpc
    have htp : (cardinalProductFrame A (J.localize Top)).eventuallyPointwiseLt (d t) p :=
      (cardinalProductFrame A J).eventuallyPointwiseLt_withLargerIdeal
        (J.localize Top) (J.le_localize Top) (hUpper t)
    have hFalse : (J.localize Top).Eventually (fun _ => False) :=
      (J.localize Top).eventually_mono ((J.localize Top).eventually_and hpt htp) (by
        intro k h
        exact h.2.2 h.1)
    exact hProper.not_eventually_false hFalse
  let X : CardinalIndex A -> Prop := fun k => Not (Top k)
  have hX : forall k, X k -> (c k).1 < k.1.ord := by
    intro k hk
    exact lt_of_le_of_ne (c k).2 hk
  let q := cardinalProductClosedToProductOn p c X hX
  have hEventuallyX : J.Eventually X := by
    change J.Small (fun k => Not (X k))
    simpa only [X, Top, not_not] using hTopSmall
  have hEq : J.Eventually (fun k => cardinalProductOrdinalValue q k = (c k).1) :=
    J.eventually_mono hEventuallyX (fun k hk =>
      cardinalProductOrdinalValue_closedToProductOn p c X hX k hk)
  refine ⟨q, ?_, ?_⟩
  · intro t
    apply (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue (d t) q).mpr
    exact J.eventually_mono (J.eventually_and (hExact.1 t) hEq) (by
      intro k h
      simpa only [h.2] using h.1)
  · intro h hh
    have hhOrdinal := (cardinalProduct_eventuallyPointwiseLt_iff_ordinalValue h q).mp hh
    apply hExact.2 h
    exact J.eventually_mono (J.eventually_and hhOrdinal hEq) (by
      intro k hk
      simpa only [hk.2] using hk.1)

#print axioms exists_pointwiseStrictExactUpperBound_of_closed_of_upperBound

theorem PointwiseStrictScale.initialSegment_exactUpperBound_of_closedPrinciple
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta kappa : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (alpha : theta.ord.ToType) [Nonempty (Set.Iio alpha)]
    (e : kappa.ord.ToType ≃o Set.Iio alpha)
    (hPrinciple : CardinalProductClosedExactUpperBoundPrinciple A J kappa) :
    exists q : ProductElement (cardinalProductFrame A J),
      (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound
        (fun beta : Set.Iio alpha => s.seq beta.1) q := by
  let d : kappa.ord.ToType -> ProductElement (cardinalProductFrame A J) :=
    fun eta => s.seq (e eta).1
  have hIncreasing : forall {eta zeta}, (cardinalScaleLength kappa).lt eta zeta ->
      (cardinalProductFrame A J).eventuallyPointwiseLt (d eta) (d zeta) := by
    intro eta zeta h
    have h' : (show kappa.ord.ToType from eta) <
        (show kappa.ord.ToType from zeta) := h
    have he : e eta < e zeta := e.lt_iff_lt.mpr h'
    exact s.increasing he
  obtain ⟨c, hc⟩ := hPrinciple d hIncreasing
  have hc' : CardinalProductClosedExactUpperBound J
      (fun beta : Set.Iio alpha => s.seq beta.1) c := by
    have hFamily : (fun beta : Set.Iio alpha => s.seq (e (e.symm beta)).1) =
        (fun beta : Set.Iio alpha => s.seq beta.1) := by
      funext beta
      rw [e.apply_symm_apply]
    rw [← hFamily]
    simpa only [d] using hc.reindex e.toEquiv
  exact exists_pointwiseStrictExactUpperBound_of_closed_of_upperBound
    (fun beta : Set.Iio alpha => s.seq beta.1) c hc' (s.seq alpha)
    (fun beta => s.increasing beta.2)

#print axioms PointwiseStrictScale.initialSegment_exactUpperBound_of_closedPrinciple

/-- Closed exactness on a strictly increasing cofinal subsequence is already
closed exactness for the entire scale initial segment. -/
theorem PointwiseStrictScale.closedExactUpperBound_of_cofinal_subsequence
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (alpha : theta.ord.ToType) {K : Type u}
    (r : K -> Set.Iio alpha)
    (hCofinal : forall beta : Set.Iio alpha, exists eta, beta <= r eta)
    (c : CardinalProductClosedElement A)
    (hExact : CardinalProductClosedExactUpperBound J (fun eta => s.seq (r eta).1) c) :
    CardinalProductClosedExactUpperBound J (fun beta : Set.Iio alpha => s.seq beta.1) c := by
  constructor
  · intro beta
    obtain ⟨eta, hBeta⟩ := hCofinal beta
    rcases hBeta.eq_or_lt with hEq | hLt
    · simpa only [hEq] using hExact.1 eta
    · exact (hExact.1 eta).trans_of_eventuallyPointwiseLt
        (s.increasing (show beta.1 < (r eta).1 from hLt))
  · intro h hh
    obtain ⟨eta, hEta⟩ := hExact.2 h hh
    exact ⟨r eta, hEta⟩

#print axioms PointwiseStrictScale.closedExactUpperBound_of_cofinal_subsequence

/-- Lemma 24.10 applied at the cofinality of an arbitrary scale index. -/
theorem PointwiseStrictScale.initialSegment_exactUpperBound_of_cofinalMap_two_power_lt
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta kappa : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hKappaRegular : Cardinal.IsRegular kappa)
    (hKappaUncountable : Cardinal.aleph0 < kappa)
    (hPower : (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
      Cardinal.lift.{u + 1} kappa)
    (alpha : theta.ord.ToType)
    (r : kappa.ord.ToType -> Set.Iio alpha) (hStrict : StrictMono r)
    (hCofinal : forall beta : Set.Iio alpha, exists eta, beta <= r eta) :
    exists q : ProductElement (cardinalProductFrame A J),
      (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound
        (fun beta : Set.Iio alpha => s.seq beta.1) q := by
  have hNonempty : Nonempty kappa.ord.ToType := by
    rw [Ordinal.nonempty_toType_iff]
    exact ne_of_gt (Cardinal.ord_pos.mpr (Cardinal.aleph0_pos.trans hKappaUncountable))
  letI : Nonempty kappa.ord.ToType := hNonempty
  letI : Nonempty (Set.Iio alpha) := ⟨r (Classical.choice hNonempty)⟩
  let d : kappa.ord.ToType -> ProductElement (cardinalProductFrame A J) :=
    fun eta => s.seq (r eta).1
  have hIncreasing : forall {eta zeta}, (cardinalScaleLength kappa).lt eta zeta ->
      (cardinalProductFrame A J).eventuallyPointwiseLt (d eta) (d zeta) := by
    intro eta zeta h
    exact s.increasing (show (r eta).1 < (r zeta).1 from hStrict h)
  have hPrinciple : CardinalProductClosedExactUpperBoundPrinciple A J kappa := by
    simpa only [Ideal.pushforward_id] using
      (pushforwardCardinalProductClosedExactUpperBoundPrinciple_of_two_power_lt
        (J := J) id hIndexInfinite hKappaRegular hKappaUncountable hPower)
  obtain ⟨c, hc⟩ := hPrinciple d hIncreasing
  have hcFull := s.closedExactUpperBound_of_cofinal_subsequence alpha r hCofinal c hc
  exact exists_pointwiseStrictExactUpperBound_of_closed_of_upperBound
    (fun beta : Set.Iio alpha => s.seq beta.1) c hcFull (s.seq alpha)
    (fun beta => s.increasing beta.2)

#print axioms PointwiseStrictScale.initialSegment_exactUpperBound_of_cofinalMap_two_power_lt

/-- A scale index has source-large cofinality when it has a regular cofinal
presentation whose cardinal is above the powerset of the coordinate index.
This is the exact hypothesis used to normalize the scale in Jech 24.31. -/
def CardinalProductScaleIndexHasLargeCofinality
    (A : CardSet.{u}) {theta : Cardinal.{u}}
    (alpha : theta.ord.ToType) : Prop :=
  exists kappa : Cardinal.{u},
    Cardinal.IsRegular kappa /\
      Cardinal.aleph0 < kappa /\
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} kappa /\
      exists r : kappa.ord.ToType -> Set.Iio alpha,
        StrictMono r /\
          forall beta : Set.Iio alpha, exists eta, beta <= r eta

/-- Lemma 24.10 supplies an exact upper bound at every scale index with a
source-large cofinal presentation. -/
theorem PointwiseStrictScale.exists_initialSegment_exactUpperBound_of_largeCofinality
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (alpha : theta.ord.ToType)
    (hLarge : CardinalProductScaleIndexHasLargeCofinality A alpha) :
    exists q : ProductElement (cardinalProductFrame A J),
      (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound
        (fun beta : Set.Iio alpha => s.seq beta.1) q := by
  rcases hLarge with ⟨kappa, hRegular, hUncountable, hPower,
    r, hStrict, hCofinal⟩
  exact s.initialSegment_exactUpperBound_of_cofinalMap_two_power_lt
    hIndexInfinite hRegular hUncountable hPower alpha r hStrict hCofinal

#print axioms
  PointwiseStrictScale.exists_initialSegment_exactUpperBound_of_largeCofinality

/-- Replace a scale value at each source-large-cofinality index by a chosen
exact upper bound of its initial segment. Elsewhere retain the original
scale value. -/
noncomputable def PointwiseStrictScale.exactifiedValue
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (alpha : theta.ord.ToType) :
    ProductElement (cardinalProductFrame A J) := by
  classical
  exact if hLarge : CardinalProductScaleIndexHasLargeCofinality A alpha then
      Classical.choose
        (s.exists_initialSegment_exactUpperBound_of_largeCofinality
          hIndexInfinite alpha hLarge)
    else s.seq alpha

theorem PointwiseStrictScale.exactifiedValue_exact
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (alpha : theta.ord.ToType)
    (hLarge : CardinalProductScaleIndexHasLargeCofinality A alpha) :
    (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound
      (fun beta : Set.Iio alpha => s.seq beta.1)
      (s.exactifiedValue hIndexInfinite alpha) := by
  rw [PointwiseStrictScale.exactifiedValue, dif_pos hLarge]
  exact Classical.choose_spec
    (s.exists_initialSegment_exactUpperBound_of_largeCofinality
      hIndexInfinite alpha hLarge)

#print axioms PointwiseStrictScale.exactifiedValue_exact

theorem PointwiseStrictScale.exactifiedValue_eventuallyLe
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (alpha : theta.ord.ToType) :
    (cardinalProductFrame A J).eventuallyLe
      (s.exactifiedValue hIndexInfinite alpha) (s.seq alpha) := by
  classical
  by_cases hLarge : CardinalProductScaleIndexHasLargeCofinality A alpha
  · rcases hLarge with ⟨kappa, hRegular, hUncountable, hPower,
      r, hStrict, hCofinal⟩
    have hKappaNonempty : Nonempty kappa.ord.ToType := by
      rw [Ordinal.nonempty_toType_iff]
      exact ne_of_gt (Cardinal.ord_pos.mpr
        (Cardinal.aleph0_pos.trans_le hUncountable.le))
    letI : Nonempty kappa.ord.ToType := hKappaNonempty
    letI : Nonempty (Set.Iio alpha) := ⟨r (Classical.choice hKappaNonempty)⟩
    apply cardinalProduct_exactUpperBound_eventuallyLe_upperBound
      (fun beta : Set.Iio alpha => s.seq beta.1)
      (s.exactifiedValue hIndexInfinite alpha) (s.seq alpha)
      (s.exactifiedValue_exact hIndexInfinite alpha
        ⟨kappa, hRegular, hUncountable, hPower, r, hStrict, hCofinal⟩)
    intro beta
    exact s.increasing beta.2
  · simp only [PointwiseStrictScale.exactifiedValue, dif_neg hLarge]
    exact (cardinalProductFrame A J).eventuallyLe_refl (s.seq alpha)

#print axioms PointwiseStrictScale.exactifiedValue_eventuallyLe

theorem PointwiseStrictScale.eventuallyPointwiseLt_exactifiedValue_of_lt
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    {alpha beta : theta.ord.ToType} (hAlphaBeta : alpha < beta) :
    (cardinalProductFrame A J).eventuallyPointwiseLt
      (s.seq alpha) (s.exactifiedValue hIndexInfinite beta) := by
  classical
  by_cases hLarge : CardinalProductScaleIndexHasLargeCofinality A beta
  · exact (s.exactifiedValue_exact hIndexInfinite beta hLarge).1
      ⟨alpha, hAlphaBeta⟩
  · simpa only [PointwiseStrictScale.exactifiedValue, dif_neg hLarge] using
      s.increasing hAlphaBeta

#print axioms
  PointwiseStrictScale.eventuallyPointwiseLt_exactifiedValue_of_lt

/-- Normalize an entire pointwise-strict scale. At large-cofinality indices
its values are exact upper bounds of the original initial segments. -/
noncomputable def PointwiseStrictScale.exactifyLargeCofinality
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hThetaInfinite : Cardinal.aleph0 <= theta) :
    PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta) where
  seq := s.exactifiedValue hIndexInfinite
  increasing := by
    intro alpha beta hAlphaBeta
    exact (cardinalProductFrame A J).eventuallyLe_eventuallyPointwiseLt_trans
      (s.exactifiedValue_eventuallyLe hIndexInfinite alpha)
      (s.eventuallyPointwiseLt_exactifiedValue_of_lt
        hIndexInfinite hAlphaBeta)
  cofinal := by
    letI : NoMaxOrder theta.ord.ToType := Cardinal.noMaxOrder hThetaInfinite
    intro g
    obtain ⟨alpha : theta.ord.ToType, hAlpha⟩ := s.cofinal g
    obtain ⟨beta : theta.ord.ToType, hAlphaBeta⟩ :=
      (exists_gt alpha : exists beta : theta.ord.ToType, alpha < beta)
    have hStrict := s.eventuallyPointwiseLt_exactifiedValue_of_lt
      hIndexInfinite hAlphaBeta
    exact ⟨beta, (cardinalProductFrame A J).eventuallyLe_trans hAlpha
      (J.eventually_mono hStrict (fun _ h => h.1))⟩

#print axioms PointwiseStrictScale.exactifyLargeCofinality

/-- At every source-large-cofinality index, the normalized value is an exact
upper bound of the normalized (not merely original) scale initial segment. -/
theorem PointwiseStrictScale.exactifyLargeCofinality_initialSegment_exact
    {A : CardSet.{u}} {J : Ideal (CardinalIndex A)} {theta : Cardinal.{u}}
    (s : PointwiseStrictScale (cardinalProductFrame A J) (cardinalScaleLength theta))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hThetaInfinite : Cardinal.aleph0 <= theta)
    (alpha : theta.ord.ToType)
    (hLarge : CardinalProductScaleIndexHasLargeCofinality A alpha) :
    (cardinalProductFrame A J).IsPointwiseStrictExactUpperBound
      (fun beta : Set.Iio alpha =>
        (s.exactifyLargeCofinality hIndexInfinite hThetaInfinite).seq beta.1)
      ((s.exactifyLargeCofinality hIndexInfinite hThetaInfinite).seq alpha) := by
  classical
  rcases hLarge with ⟨kappa, hRegular, hUncountable, hPower,
    r, hStrict, hCofinal⟩
  let hLarge' : CardinalProductScaleIndexHasLargeCofinality A alpha :=
    ⟨kappa, hRegular, hUncountable, hPower, r, hStrict, hCofinal⟩
  have hExact := s.exactifiedValue_exact hIndexInfinite alpha hLarge'
  constructor
  · intro beta
    change (cardinalProductFrame A J).eventuallyPointwiseLt
      (s.exactifiedValue hIndexInfinite beta.1)
      (s.exactifiedValue hIndexInfinite alpha)
    exact (cardinalProductFrame A J).eventuallyLe_eventuallyPointwiseLt_trans
      (s.exactifiedValue_eventuallyLe hIndexInfinite beta.1)
      (s.eventuallyPointwiseLt_exactifiedValue_of_lt hIndexInfinite beta.2)
  · intro h hh
    change (cardinalProductFrame A J).eventuallyPointwiseLt
      h (s.exactifiedValue hIndexInfinite alpha) at hh
    obtain ⟨beta, hBeta⟩ := hExact.2 h hh
    have hKappaNonempty : Nonempty kappa.ord.ToType := by
      rw [Ordinal.nonempty_toType_iff]
      exact ne_of_gt (Cardinal.ord_pos.mpr
        (Cardinal.aleph0_pos.trans_le hUncountable.le))
    letI : Nonempty kappa.ord.ToType := hKappaNonempty
    letI : NoMaxOrder kappa.ord.ToType := Cardinal.noMaxOrder hUncountable.le
    obtain ⟨eta, hBetaEta⟩ := hCofinal beta
    obtain ⟨zeta, hEtaZeta⟩ := exists_gt eta
    let gamma : Set.Iio alpha := r zeta
    have hBetaGamma : beta.1 < gamma.1 :=
      hBetaEta.trans_lt (hStrict hEtaZeta)
    have hToGamma :=
      s.eventuallyPointwiseLt_exactifiedValue_of_lt
        hIndexInfinite hBetaGamma
    have hHGamma :=
      (cardinalProductFrame A J).eventuallyLe_eventuallyPointwiseLt_trans
        hBeta hToGamma
    refine ⟨gamma, ?_⟩
    exact J.eventually_mono hHGamma (fun _ h => h.1)

#print axioms
  PointwiseStrictScale.exactifyLargeCofinality_initialSegment_exact

abbrev PcfCharacteristic (A : CardSet.{u}) : Type (u + 1) :=
  forall i : CardinalIndex A, i.1.ord.ToType

/-- One stage of the explicit closure recursion replacing the elementary
model chain in the proof of Jech 24.31. The base dominates the seed and all
earlier stages. The value additionally closes under every scale value and
under a cofinal index selected for every coordinate scale. -/
structure PcfCharacteristicClosureStage
    {A : CardSet.{u}} {kappa : Cardinal.{u}}
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType)
    (previous : forall xi : kappa.ord.ToType, xi < eta -> PcfCharacteristic A) where
  base : PcfCharacteristic A
  value : PcfCharacteristic A
  seed_lt_base : forall i, seed i < base i
  previous_lt_base : forall xi hxi i, previous xi hxi i < base i
  base_lt_value : forall i, base i < value i
  scale_lt_value : forall lambda i,
    (show i.1.ord.ToType from (s lambda).seq (base lambda) i) < value i
  cofinalIndex : forall lambda : CardinalIndex A, lambda.1.ord.ToType
  base_le_scale : forall lambda,
    (cardinalProductFrame A (J lambda)).eventuallyLe base
      ((s lambda).seq (cofinalIndex lambda))
  cofinalIndex_lt_value : forall lambda, cofinalIndex lambda < value lambda

/-- Existence of one closure stage. Smallness is used only to replace the
large-universe coordinate index by `Shrink`; regularity then performs the
two coordinatewise diagonalizations. -/
theorem exists_pcfCharacteristicClosureStage
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType)
    (previous : forall xi : kappa.ord.ToType, xi < eta -> PcfCharacteristic A) :
    Nonempty (PcfCharacteristicClosureStage J s seed eta previous) := by
  classical
  letI : Small.{u} (CardinalIndex A) := hSmall
  let K := kappa.ord.ToType
  have hOrderType : (Cardinal.mk K).ord =
      Ordinal.type (fun x y : K => x < y) := by
    rw [show Cardinal.mk K = kappa from Cardinal.mk_ord_toType kappa]
    exact (Ordinal.type_toType kappa.ord).symm
  have hEtaSmall : Cardinal.mk (Set.Iio eta) < kappa :=
    (Cardinal.mk_Iio_lt eta hOrderType).trans_eq
      (Cardinal.mk_ord_toType kappa)
  let priorFamily : Set.Iio eta -> PcfCharacteristic A :=
    fun xi => previous xi.1 xi.2
  obtain ⟨priorBound, hPriorBound⟩ :=
    cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt
      hRegulars
      (fun a ha => hEtaSmall.trans (hKappaCoordinates ⟨a, ha⟩)) priorFamily
  have hBase : forall i : CardinalIndex A,
      exists x : i.1.ord.ToType, seed i < x /\ priorBound i < x := by
    intro i
    letI : NoMaxOrder i.1.ord.ToType :=
      Cardinal.noMaxOrder (hRegulars i.1 i.2).aleph0_le
    obtain ⟨x, hx⟩ := exists_gt (max (seed i) (priorBound i))
    exact ⟨x, (le_max_left _ _).trans_lt hx,
      (le_max_right _ _).trans_lt hx⟩
  choose base hSeedBase hPriorBase using hBase
  have hScaleIndexSmall : forall i : CardinalIndex A,
      Cardinal.mk (Shrink.{u} (CardinalIndex A)) < i.1 := by
    intro i
    apply Cardinal.lift_lt.{u, u + 1}.mp
    rw [Cardinal.lift_mk_shrink'']
    exact hIndexKappa.trans (Cardinal.lift_lt.mpr (hKappaCoordinates i))
  let scaleFamily : Shrink.{u} (CardinalIndex A) -> PcfCharacteristic A :=
    fun q =>
      let lambda := (equivShrink (CardinalIndex A)).symm q
      (s lambda).seq (base lambda)
  obtain ⟨scaleBound, hScaleBound⟩ :=
    cardinalProduct_exists_pointwise_strict_upper_bound_of_mk_lt
      hRegulars (fun a ha => hScaleIndexSmall ⟨a, ha⟩) scaleFamily
  have hCofinal : forall lambda : CardinalIndex A,
      exists alpha : lambda.1.ord.ToType,
        (cardinalProductFrame A (J lambda)).eventuallyLe base
          ((s lambda).seq alpha) := by
    intro lambda
    exact (s lambda).cofinal base
  choose cofinalIndex hBaseLe using hCofinal
  have hValue : forall i : CardinalIndex A,
      exists y : i.1.ord.ToType,
        base i < y /\ scaleBound i < y /\ cofinalIndex i < y := by
    intro i
    letI : NoMaxOrder i.1.ord.ToType :=
      Cardinal.noMaxOrder (hRegulars i.1 i.2).aleph0_le
    obtain ⟨y, hy⟩ := exists_gt (max (max (base i) (scaleBound i)) (cofinalIndex i))
    exact ⟨y,
      (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans_lt hy),
      (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans_lt hy),
      (le_max_right _ _ |>.trans_lt hy)⟩
  choose value hBaseValue hScaleValue hIndexValue using hValue
  refine ⟨{
    base := base
    value := value
    seed_lt_base := ?_
    previous_lt_base := ?_
    base_lt_value := hBaseValue
    scale_lt_value := ?_
    cofinalIndex := cofinalIndex
    base_le_scale := hBaseLe
    cofinalIndex_lt_value := hIndexValue }⟩
  · intro i
    exact hSeedBase i
  · intro xi hxi i
    exact (hPriorBound ⟨xi, hxi⟩ i).trans (hPriorBase i)
  · intro lambda i
    have hBound := hScaleBound (equivShrink (CardinalIndex A) lambda) i
    change (show i.1.ord.ToType from
      (s ((equivShrink (CardinalIndex A)).symm
      (equivShrink (CardinalIndex A) lambda))).seq
        (base ((equivShrink (CardinalIndex A)).symm
          (equivShrink (CardinalIndex A) lambda))) i) < scaleBound i at hBound
    rw [Equiv.symm_apply_apply] at hBound
    exact hBound.trans (hScaleValue i)

#print axioms exists_pcfCharacteristicClosureStage

noncomputable def pcfCharacteristicClosureStageChoice
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType)
    (previous : forall xi : kappa.ord.ToType, xi < eta -> PcfCharacteristic A) :
    PcfCharacteristicClosureStage J s seed eta previous :=
  Classical.choice (exists_pcfCharacteristicClosureStage
    hRegulars hSmall hIndexKappa hKappaCoordinates J s seed eta previous)

noncomputable def pcfCharacteristicClosureChain
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) :
    kappa.ord.ToType -> PcfCharacteristic A :=
  WellFounded.fix wellFounded_lt fun eta previous =>
    (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
      hKappaCoordinates J s seed eta previous).value

theorem pcfCharacteristicClosureChain_eq
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) :
    pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta =
      (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta
          (fun xi _ => pcfCharacteristicClosureChain hRegulars hSmall
            hIndexKappa hKappaCoordinates J s seed xi)).value := by
  rw [pcfCharacteristicClosureChain, WellFounded.fix_eq]

#print axioms pcfCharacteristicClosureChain_eq

noncomputable def pcfCharacteristicClosureBase
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) : PcfCharacteristic A :=
  (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta
      (fun xi _ => pcfCharacteristicClosureChain hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed xi)).base

noncomputable def pcfCharacteristicClosureCofinalIndex
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) (lambda : CardinalIndex A) :
    lambda.1.ord.ToType :=
  (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta
      (fun xi _ => pcfCharacteristicClosureChain hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed xi)).cofinalIndex lambda

theorem pcfCharacteristicClosureChain_seed_lt_base
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) (i : CardinalIndex A) :
    seed i < pcfCharacteristicClosureBase hRegulars hSmall hIndexKappa
      hKappaCoordinates J s seed eta i :=
  (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta
      (fun xi _ => pcfCharacteristicClosureChain hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed xi)).seed_lt_base i

theorem pcfCharacteristicClosureChain_previous_lt_base
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    {xi eta : kappa.ord.ToType} (hxi : xi < eta) (i : CardinalIndex A) :
    pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed xi i <
      pcfCharacteristicClosureBase hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta i :=
  (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta
      (fun zeta _ => pcfCharacteristicClosureChain hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed zeta)).previous_lt_base xi hxi i

theorem pcfCharacteristicClosureChain_base_lt
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) (i : CardinalIndex A) :
    pcfCharacteristicClosureBase hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta i <
      pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta i := by
  rw [pcfCharacteristicClosureChain_eq]
  exact (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta
      (fun xi _ => pcfCharacteristicClosureChain hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed xi)).base_lt_value i

theorem pcfCharacteristicClosureChain_strictMono_at
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) :
    StrictMono (fun eta => pcfCharacteristicClosureChain hRegulars hSmall
      hIndexKappa hKappaCoordinates J s seed eta i) := by
  intro xi eta hxi
  exact (pcfCharacteristicClosureChain_previous_lt_base hRegulars hSmall
    hIndexKappa hKappaCoordinates J s seed hxi i).trans
      (pcfCharacteristicClosureChain_base_lt hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed eta i)

#print axioms pcfCharacteristicClosureChain_strictMono_at

theorem pcfCharacteristicClosureChain_scale_lt
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) (lambda i : CardinalIndex A) :
    (show i.1.ord.ToType from
      (s lambda).seq
        (pcfCharacteristicClosureBase hRegulars hSmall hIndexKappa
          hKappaCoordinates J s seed eta lambda) i) <
      pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta i := by
  rw [pcfCharacteristicClosureChain_eq]
  exact (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta
      (fun xi _ => pcfCharacteristicClosureChain hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed xi)).scale_lt_value lambda i

theorem pcfCharacteristicClosureChain_base_le_scale
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) (lambda : CardinalIndex A) :
    (cardinalProductFrame A (J lambda)).eventuallyLe
      (pcfCharacteristicClosureBase hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta)
      ((s lambda).seq
        (pcfCharacteristicClosureCofinalIndex hRegulars hSmall hIndexKappa
          hKappaCoordinates J s seed eta lambda)) :=
  (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta
      (fun xi _ => pcfCharacteristicClosureChain hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed xi)).base_le_scale lambda

theorem pcfCharacteristicClosureChain_cofinalIndex_lt
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) (lambda : CardinalIndex A) :
    pcfCharacteristicClosureCofinalIndex hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta lambda <
      pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta lambda := by
  rw [pcfCharacteristicClosureChain_eq]
  exact (pcfCharacteristicClosureStageChoice hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta
      (fun xi _ => pcfCharacteristicClosureChain hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed xi)).cofinalIndex_lt_value lambda

#print axioms pcfCharacteristicClosureChain_scale_lt
#print axioms pcfCharacteristicClosureChain_base_le_scale
#print axioms pcfCharacteristicClosureChain_cofinalIndex_lt

noncomputable def pcfCharacteristicClosureOrdinal
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}}
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) : Ordinal.{u} :=
  iSup fun eta : kappa.ord.ToType =>
    cardinalProductOrdinalValue (J := J i)
      (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta) i

theorem pcfCharacteristicClosureOrdinal_lt_and_cof_eq
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) :
    pcfCharacteristicClosureOrdinal hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed i < i.1.ord /\
      (pcfCharacteristicClosureOrdinal hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed i).cof = kappa := by
  apply cardinalScaleLength_strictSequence_iSup_lt_and_cof_eq
    hKappaRegular (hRegulars i.1 i.2) (hKappaCoordinates i)
  · intro eta zeta hEtaZeta
    apply (cardinalProductOrdinalValue_lt_iff
      (J := J i)
      (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta)
      (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed zeta) i).mpr
    exact pcfCharacteristicClosureChain_strictMono_at hRegulars hSmall
      hIndexKappa hKappaCoordinates J s seed i hEtaZeta
  · intro eta
    exact cardinalProductOrdinalValue_lt
      (J := J i)
      (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta) i

#print axioms pcfCharacteristicClosureOrdinal_lt_and_cof_eq

/-- The terminal characteristic is the pointwise supremum of the closure
chain. The strict gap `kappa < i` and regularity of every coordinate keep it
inside the genuine product. -/
noncomputable def pcfCharacteristicClosure
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) : PcfCharacteristic A :=
  fun i => Ordinal.ToType.mk
    ⟨pcfCharacteristicClosureOrdinal hRegulars hSmall hIndexKappa
      hKappaCoordinates J s seed i,
      (pcfCharacteristicClosureOrdinal_lt_and_cof_eq hRegulars hSmall
        hKappaRegular hIndexKappa hKappaCoordinates J s seed i).1⟩

@[simp] theorem pcfCharacteristicClosure_ordinalValue
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) :
    cardinalProductOrdinalValue (J := J i)
        (pcfCharacteristicClosure hRegulars hSmall hKappaRegular
          hIndexKappa hKappaCoordinates J s seed) i =
      pcfCharacteristicClosureOrdinal hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed i := by
  exact congrArg Subtype.val
    ((Ordinal.ToType.mk : Set.Iio i.1.ord ≃o i.1.ord.ToType).symm_apply_apply
      ⟨pcfCharacteristicClosureOrdinal hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed i,
        (pcfCharacteristicClosureOrdinal_lt_and_cof_eq hRegulars hSmall
          hKappaRegular hIndexKappa hKappaCoordinates J s seed i).1⟩)

#print axioms pcfCharacteristicClosure_ordinalValue

theorem pcfCharacteristicClosureChain_lt
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A)
    (eta : kappa.ord.ToType) (i : CardinalIndex A) :
    pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta i <
      pcfCharacteristicClosure hRegulars hSmall hKappaRegular
        hIndexKappa hKappaCoordinates J s seed i := by
  letI : NoMaxOrder kappa.ord.ToType :=
    Cardinal.noMaxOrder hKappaRegular.aleph0_le
  obtain ⟨zeta : kappa.ord.ToType, hEtaZeta⟩ :=
    (exists_gt eta : exists zeta : kappa.ord.ToType, eta < zeta)
  apply (cardinalProductOrdinalValue_lt_iff
    (J := J i)
    (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
      hKappaCoordinates J s seed eta)
    (pcfCharacteristicClosure hRegulars hSmall hKappaRegular
      hIndexKappa hKappaCoordinates J s seed) i).mp
  rw [pcfCharacteristicClosure_ordinalValue]
  exact ((cardinalProductOrdinalValue_lt_iff
    (J := J i)
    (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
      hKappaCoordinates J s seed eta)
    (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
      hKappaCoordinates J s seed zeta) i).mpr
        (pcfCharacteristicClosureChain_strictMono_at hRegulars hSmall
          hIndexKappa hKappaCoordinates J s seed i hEtaZeta)).trans_le
    (Ordinal.le_iSup (fun xi : kappa.ord.ToType =>
      cardinalProductOrdinalValue (J := J i)
        (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
          hKappaCoordinates J s seed xi) i) zeta)

#print axioms pcfCharacteristicClosureChain_lt

noncomputable def pcfCharacteristicClosureCofinalMap
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) :
    kappa.ord.ToType -> Set.Iio
      (pcfCharacteristicClosure hRegulars hSmall hKappaRegular
        hIndexKappa hKappaCoordinates J s seed i) :=
  fun eta => ⟨pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed eta i,
    pcfCharacteristicClosureChain_lt hRegulars hSmall hKappaRegular
      hIndexKappa hKappaCoordinates J s seed eta i⟩

theorem pcfCharacteristicClosureCofinalMap_strictMono
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) :
    StrictMono (pcfCharacteristicClosureCofinalMap hRegulars hSmall
      hKappaRegular hIndexKappa hKappaCoordinates J s seed i) := by
  intro eta zeta hEtaZeta
  apply Subtype.mk_lt_mk.mpr
  exact pcfCharacteristicClosureChain_strictMono_at hRegulars hSmall
    hIndexKappa hKappaCoordinates J s seed i hEtaZeta

theorem pcfCharacteristicClosureCofinalMap_cofinal
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) :
    forall beta : Set.Iio
      (pcfCharacteristicClosure hRegulars hSmall hKappaRegular
        hIndexKappa hKappaCoordinates J s seed i),
      exists eta, beta <= pcfCharacteristicClosureCofinalMap hRegulars hSmall
        hKappaRegular hIndexKappa hKappaCoordinates J s seed i eta := by
  classical
  intro beta
  let e : Set.Iio i.1.ord ≃o i.1.ord.ToType := Ordinal.ToType.mk
  let betaOrdinal : Ordinal.{u} := (e.symm beta.1).1
  have hBetaOrdinal : betaOrdinal <
      pcfCharacteristicClosureOrdinal hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed i := by
    have hb := e.symm.lt_iff_lt.mpr beta.2
    change betaOrdinal < cardinalProductOrdinalValue (J := J i)
      (pcfCharacteristicClosure hRegulars hSmall hKappaRegular
        hIndexKappa hKappaCoordinates J s seed) i at hb
    simpa only [pcfCharacteristicClosure_ordinalValue] using hb
  obtain ⟨eta, hEta⟩ := Ordinal.lt_iSup_iff.mp hBetaOrdinal
  refine ⟨eta, ?_⟩
  apply Subtype.mk_le_mk.mpr
  have hInverse : e.symm beta.1 < e.symm
      (pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
        hKappaCoordinates J s seed eta i) := by
    apply Subtype.mk_lt_mk.mpr
    exact hEta
  exact (e.symm.lt_iff_lt.mp hInverse).le

#print axioms pcfCharacteristicClosureCofinalMap_strictMono
#print axioms pcfCharacteristicClosureCofinalMap_cofinal

theorem pcfCharacteristicClosure_largeCofinality
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hKappaUncountable : Cardinal.aleph0 < kappa)
    (hIndexPowerKappa :
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) :
    CardinalProductScaleIndexHasLargeCofinality A
      (pcfCharacteristicClosure hRegulars hSmall hKappaRegular
        ((Cardinal.cantor _).trans hIndexPowerKappa)
        hKappaCoordinates J s seed i) := by
  let hIndexKappa := (Cardinal.cantor
    (Cardinal.mk (CardinalIndex A))).trans hIndexPowerKappa
  exact ⟨kappa, hKappaRegular, hKappaUncountable, hIndexPowerKappa,
    pcfCharacteristicClosureCofinalMap hRegulars hSmall hKappaRegular
      hIndexKappa hKappaCoordinates J s seed i,
    pcfCharacteristicClosureCofinalMap_strictMono hRegulars hSmall
      hKappaRegular hIndexKappa hKappaCoordinates J s seed i,
    pcfCharacteristicClosureCofinalMap_cofinal hRegulars hSmall
      hKappaRegular hIndexKappa hKappaCoordinates J s seed i⟩

#print axioms pcfCharacteristicClosure_largeCofinality

theorem pcfCharacteristicClosure_seed_le
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hIndexKappa : Cardinal.mk (CardinalIndex A) < Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (i : CardinalIndex A) :
    seed i <= pcfCharacteristicClosure hRegulars hSmall hKappaRegular
      hIndexKappa hKappaCoordinates J s seed i := by
  have hKappaNonempty : Nonempty kappa.ord.ToType := by
    rw [Ordinal.nonempty_toType_iff]
    exact ne_of_gt (Cardinal.ord_pos.mpr
      (Cardinal.aleph0_pos.trans_le hKappaRegular.aleph0_le))
  let eta := Classical.choice hKappaNonempty
  exact ((pcfCharacteristicClosureChain_seed_lt_base hRegulars hSmall
    hIndexKappa hKappaCoordinates J s seed eta i).trans
      (pcfCharacteristicClosureChain_base_lt hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed eta i) |>.trans
      (pcfCharacteristicClosureChain_lt hRegulars hSmall hKappaRegular
        hIndexKappa hKappaCoordinates J s seed eta i)).le

#print axioms pcfCharacteristicClosure_seed_le

/-- The terminal closure characteristic is an exact upper bound of every
scale initial segment cut out by its own coordinate. This is the direct
combinatorial replacement for the elementary-submodel exactness argument in
Jech 24.31. -/
theorem pcfCharacteristicClosure_isExactUpperBound
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hKappaUncountable : Cardinal.aleph0 < kappa)
    (hIndexPowerKappa :
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (s : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) (lambda : CardinalIndex A) :
    let hIndexKappa := (Cardinal.cantor
      (Cardinal.mk (CardinalIndex A))).trans hIndexPowerKappa
    let chi := pcfCharacteristicClosure hRegulars hSmall hKappaRegular
      hIndexKappa hKappaCoordinates J s seed
    (cardinalProductFrame A (J lambda)).IsPointwiseStrictExactUpperBound
      (fun beta : Set.Iio (chi lambda) => (s lambda).seq beta.1) chi := by
  classical
  let hIndexKappa := (Cardinal.cantor
    (Cardinal.mk (CardinalIndex A))).trans hIndexPowerKappa
  let chi := pcfCharacteristicClosure hRegulars hSmall hKappaRegular
    hIndexKappa hKappaCoordinates J s seed
  let chain := pcfCharacteristicClosureChain hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed
  let base := pcfCharacteristicClosureBase hRegulars hSmall hIndexKappa
    hKappaCoordinates J s seed
  let cofinalIndex := pcfCharacteristicClosureCofinalIndex hRegulars hSmall
    hIndexKappa hKappaCoordinates J s seed
  let r := pcfCharacteristicClosureCofinalMap hRegulars hSmall hKappaRegular
    hIndexKappa hKappaCoordinates J s seed lambda
  letI : NoMaxOrder kappa.ord.ToType :=
    Cardinal.noMaxOrder hKappaRegular.aleph0_le
  constructor
  · intro beta
    obtain ⟨eta, hBetaEta⟩ :=
      pcfCharacteristicClosureCofinalMap_cofinal hRegulars hSmall
        hKappaRegular hIndexKappa hKappaCoordinates J s seed lambda beta
    obtain ⟨zeta : kappa.ord.ToType, hEtaZeta⟩ :=
      (exists_gt eta : exists zeta : kappa.ord.ToType, eta < zeta)
    obtain ⟨rho : kappa.ord.ToType, hZetaRho⟩ :=
      (exists_gt zeta : exists rho : kappa.ord.ToType, zeta < rho)
    have hBetaChain : beta.1 < chain zeta lambda := by
      have hStrictR :=
        pcfCharacteristicClosureCofinalMap_strictMono hRegulars hSmall
          hKappaRegular hIndexKappa hKappaCoordinates J s seed lambda hEtaZeta
      exact Subtype.mk_lt_mk.mp (hBetaEta.trans_lt hStrictR)
    have hBetaBase : beta.1 < base rho lambda :=
      hBetaChain.trans
        (pcfCharacteristicClosureChain_previous_lt_base hRegulars hSmall
          hIndexKappa hKappaCoordinates J s seed hZetaRho lambda)
    have hFirst := (s lambda).increasing hBetaBase
    have hSecond : (cardinalProductFrame A (J lambda)).eventuallyPointwiseLt
        ((s lambda).seq (base rho lambda)) (chain rho) :=
      (J lambda).eventually_of_forall (by
        intro i
        have h := pcfCharacteristicClosureChain_scale_lt hRegulars hSmall
          hIndexKappa hKappaCoordinates J s seed rho lambda i
        exact ⟨h.le, not_le_of_gt h⟩)
    have hThird : (cardinalProductFrame A (J lambda)).eventuallyPointwiseLt
        (chain rho) chi :=
      (J lambda).eventually_of_forall (by
        intro i
        have h := pcfCharacteristicClosureChain_lt hRegulars hSmall
          hKappaRegular hIndexKappa hKappaCoordinates J s seed rho i
        exact ⟨h.le, not_le_of_gt h⟩)
    exact (cardinalProductFrame A (J lambda)).eventuallyPointwiseLt_trans
      ((cardinalProductFrame A (J lambda)).eventuallyPointwiseLt_trans
        hFirst hSecond) hThird
  · intro h hh
    have hGood : (J lambda).Eventually (fun i =>
        (show i.1.ord.ToType from h i) < chi i) :=
      (J lambda).eventually_mono hh (by
        intro i hi
        exact lt_of_le_of_ne hi.1 (fun hEq => hi.2 hEq.ge))
    have hKappaNonempty : Nonempty kappa.ord.ToType := by
      rw [Ordinal.nonempty_toType_iff]
      exact ne_of_gt (Cardinal.ord_pos.mpr
        (Cardinal.aleph0_pos.trans_le hKappaUncountable.le))
    let eta0 := Classical.choice hKappaNonempty
    have hStageExists : forall i : CardinalIndex A,
        exists eta : kappa.ord.ToType,
          (show i.1.ord.ToType from h i) < chi i ->
            (show i.1.ord.ToType from h i) < chain eta i := by
      intro i
      by_cases hi : (show i.1.ord.ToType from h i) < chi i
      · obtain ⟨eta, hEta⟩ :=
          pcfCharacteristicClosureCofinalMap_cofinal hRegulars hSmall
            hKappaRegular hIndexKappa hKappaCoordinates J s seed i
              ⟨(show i.1.ord.ToType from h i), hi⟩
        obtain ⟨zeta : kappa.ord.ToType, hEtaZeta⟩ :=
          (exists_gt eta : exists zeta : kappa.ord.ToType, eta < zeta)
        refine ⟨zeta, fun _ => ?_⟩
        have hStrictR :=
          pcfCharacteristicClosureCofinalMap_strictMono hRegulars hSmall
            hKappaRegular hIndexKappa hKappaCoordinates J s seed i hEtaZeta
        exact Subtype.mk_lt_mk.mp (hEta.trans_lt hStrictR)
      · exact ⟨eta0, fun hFalse => False.elim (hi hFalse)⟩
    choose stageIndex hStageIndex using hStageExists
    have hShrinkKappa : Cardinal.mk (Shrink.{u} (CardinalIndex A)) < kappa := by
      apply Cardinal.lift_lt.{u, u + 1}.mp
      rw [Cardinal.lift_mk_shrink'']
      exact hIndexKappa
    obtain ⟨eta, hEta⟩ := exists_strict_upper_bound_of_mk_lt_regular
      hKappaRegular hShrinkKappa
      (fun q : Shrink.{u} (CardinalIndex A) =>
        stageIndex ((equivShrink (CardinalIndex A)).symm q))
    have hHChain : (cardinalProductFrame A (J lambda)).eventuallyLe h (chain eta) :=
      (J lambda).eventually_mono hGood (by
        intro i hi
        have hIndexLt : stageIndex i < eta := by
          simpa only [Equiv.symm_apply_apply] using
            hEta (equivShrink (CardinalIndex A) i)
        exact ((hStageIndex i hi).trans
          (pcfCharacteristicClosureChain_strictMono_at hRegulars hSmall
            hIndexKappa hKappaCoordinates J s seed i hIndexLt)).le)
    obtain ⟨rho : kappa.ord.ToType, hEtaRho⟩ :=
      (exists_gt eta : exists rho : kappa.ord.ToType, eta < rho)
    have hChainBase : (cardinalProductFrame A (J lambda)).eventuallyLe
        (chain eta) (base rho) :=
      (cardinalProductFrame A (J lambda)).eventuallyLe_of_forallLe (by
        intro i
        exact (pcfCharacteristicClosureChain_previous_lt_base hRegulars hSmall
          hIndexKappa hKappaCoordinates J s seed hEtaRho i).le)
    let betaValue := cofinalIndex rho lambda
    have hBetaLt : betaValue < chi lambda :=
      (pcfCharacteristicClosureChain_cofinalIndex_lt hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed rho lambda).trans
          (pcfCharacteristicClosureChain_lt hRegulars hSmall hKappaRegular
            hIndexKappa hKappaCoordinates J s seed rho lambda)
    refine ⟨⟨betaValue, hBetaLt⟩, ?_⟩
    exact (cardinalProductFrame A (J lambda)).eventuallyLe_trans
      ((cardinalProductFrame A (J lambda)).eventuallyLe_trans
        hHChain hChainBase)
      (pcfCharacteristicClosureChain_base_le_scale hRegulars hSmall
        hIndexKappa hKappaCoordinates J s seed rho lambda)

#print axioms pcfCharacteristicClosure_isExactUpperBound

/-- After normalizing every scale at its source-large-cofinality indices, the
terminal characteristic closure agrees modulo each ideal with the scale value
at its own coordinate. This is the characteristic-agreement core of Jech
24.31, separated from the subsequent generator thinning argument. -/
theorem exists_pcfCharacteristicClosure_eventual_agreement
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hKappaUncountable : Cardinal.aleph0 < kappa)
    (hIndexPowerKappa :
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (J : CardinalIndex A -> Ideal (CardinalIndex A))
    (raw : forall lambda : CardinalIndex A,
      PointwiseStrictScale (cardinalProductFrame A (J lambda))
        (cardinalScaleLength lambda.1))
    (seed : PcfCharacteristic A) :
    let normalized := fun lambda : CardinalIndex A =>
      (raw lambda).exactifyLargeCofinality hIndexInfinite
        (hRegulars lambda.1 lambda.2).aleph0_le
    exists chi : PcfCharacteristic A,
      (forall i, seed i <= chi i) /\
        forall lambda : CardinalIndex A,
          (J lambda).Eventually (fun i =>
            (normalized lambda).seq (chi lambda) i = chi i) := by
  classical
  let normalized := fun lambda : CardinalIndex A =>
    (raw lambda).exactifyLargeCofinality hIndexInfinite
      (hRegulars lambda.1 lambda.2).aleph0_le
  let hIndexKappa := (Cardinal.cantor
    (Cardinal.mk (CardinalIndex A))).trans hIndexPowerKappa
  let chi := pcfCharacteristicClosure hRegulars hSmall hKappaRegular
    hIndexKappa hKappaCoordinates J normalized seed
  refine ⟨chi, ?_, ?_⟩
  · exact pcfCharacteristicClosure_seed_le hRegulars hSmall hKappaRegular
      hIndexKappa hKappaCoordinates J normalized seed
  · intro lambda
    have hLarge : CardinalProductScaleIndexHasLargeCofinality A
        (chi lambda) :=
      pcfCharacteristicClosure_largeCofinality hRegulars hSmall
        hKappaRegular hKappaUncountable hIndexPowerKappa hKappaCoordinates
        J normalized seed lambda
    rcases hLarge with ⟨rho, hRhoRegular, hRhoUncountable, hRhoPower,
      r, hStrict, hCofinal⟩
    let hLarge' : CardinalProductScaleIndexHasLargeCofinality A
        (chi lambda) :=
      ⟨rho, hRhoRegular, hRhoUncountable, hRhoPower,
        r, hStrict, hCofinal⟩
    have hRhoNonempty : Nonempty rho.ord.ToType := by
      rw [Ordinal.nonempty_toType_iff]
      exact ne_of_gt (Cardinal.ord_pos.mpr
        (Cardinal.aleph0_pos.trans_le hRhoUncountable.le))
    letI : Nonempty (Set.Iio (chi lambda)) :=
      ⟨r (Classical.choice hRhoNonempty)⟩
    have hNormalizedExact :
        (cardinalProductFrame A (J lambda)).IsPointwiseStrictExactUpperBound
          (fun beta : Set.Iio (chi lambda) =>
            (normalized lambda).seq beta.1)
          ((normalized lambda).seq (chi lambda)) := by
      exact (raw lambda).exactifyLargeCofinality_initialSegment_exact
        hIndexInfinite (hRegulars lambda.1 lambda.2).aleph0_le
        (chi lambda) hLarge'
    have hClosureExact :
        (cardinalProductFrame A (J lambda)).IsPointwiseStrictExactUpperBound
          (fun beta : Set.Iio (chi lambda) =>
            (normalized lambda).seq beta.1) chi := by
      exact pcfCharacteristicClosure_isExactUpperBound hRegulars hSmall
        hKappaRegular hKappaUncountable hIndexPowerKappa
        hKappaCoordinates J normalized seed lambda
    exact cardinalProduct_exactUpperBounds_eventually_eq
      (fun beta : Set.Iio (chi lambda) =>
        (normalized lambda).seq beta.1)
      ((normalized lambda).seq (chi lambda)) chi
      hNormalizedExact hClosureExact

#print axioms exists_pcfCharacteristicClosure_eventual_agreement

/-- A family of local generator scales, together with one regular closure
length above the powerset of the index and below all coordinates, yields a
transitive generator system. The scales are normalized internally, so no
extra exactness hypothesis remains in the interface. -/
theorem exists_transitive_generators_of_localScales
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} a)
    (G : GeneratorSystem cardinalProductRepresentation A)
    (hFixed : cardinalProductRepresentation.pcf A = A)
    (hDirected : GeneratorAtMostIdealSuccessorDirected G)
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hKappaUncountable : Cardinal.aleph0 < kappa)
    (hIndexPowerKappa :
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1)
    (raw : forall lambda : CardinalIndex A,
      let J := ((G.belowIdeal lambda.1).restrictAlong
        (fun i : CardinalIndex A => i.1)).localize
          (fun i => G.generator lambda.1 i.1)
      PointwiseStrictScale (cardinalProductFrame A J)
        (cardinalScaleLength lambda.1)) :
    exists H : GeneratorSystem cardinalProductRepresentation A,
      TransitiveGeneratorSystem H := by
  classical
  let J := fun lambda : CardinalIndex A =>
    ((G.belowIdeal lambda.1).restrictAlong
      (fun i : CardinalIndex A => i.1)).localize
        (fun i => G.generator lambda.1 i.1)
  let normalized := fun lambda : CardinalIndex A =>
    (raw lambda).exactifyLargeCofinality hIndexInfinite
      (hRegulars lambda.1 lambda.2).aleph0_le
  let f := fun lambda : CardinalIndex A => (normalized lambda).seq
  apply exists_transitive_generators_of_cofinally_characteristic_agreement
    hRegulars hSmall hIndexInfinite hPower G hFixed hDirected f
  intro seed
  obtain ⟨chi, hSeed, hAgreement⟩ :=
    exists_pcfCharacteristicClosure_eventual_agreement hRegulars hSmall
      hIndexInfinite hKappaRegular hKappaUncountable hIndexPowerKappa
      hKappaCoordinates J raw seed
  refine ⟨chi, hSeed, ?_⟩
  intro lambda
  let J0 := (G.belowIdeal lambda.1).restrictAlong
    (fun i : CardinalIndex A => i.1)
  have hEq : (J0.localize (fun i => G.generator lambda.1 i.1)).Eventually
      (fun i => f lambda (chi lambda) i = chi i) := by
    simpa only [J, normalized, f] using hAgreement lambda
  have hSmallBad : J0.Small (fun i =>
      Not (f lambda (chi lambda) i = chi i) /\
        G.generator lambda.1 i.1) := by
    exact (Ideal.localize_eventually_iff J0
      (fun i => G.generator lambda.1 i.1)
      (fun i => f lambda (chi lambda) i = chi i)).mp hEq
  change J0.Small (fun i => Not (G.generator lambda.1 i.1 ->
    f lambda (chi lambda) i = chi i))
  apply J0.subset_small hSmallBad
  intro i hi
  constructor
  · intro hValue
    exact hi (fun _ => hValue)
  · exact Classical.byContradiction (fun hNotGenerator =>
      hi (fun hGenerator => False.elim (hNotGenerator hGenerator)))

#print axioms exists_transitive_generators_of_localScales

/-- Canonical local PCF scales discharge the remaining scale-family input in
`exists_transitive_generators_of_localScales`. Thus a fixed PCF set satisfying
the closure-length gap has transitive generators. -/
theorem exists_transitive_generators_of_regularClosureGap
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    (hSmall : Small.{u} (CardinalIndex A))
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} a)
    (hFixed : cardinalProductRepresentation.pcf A = A)
    {kappa : Cardinal.{u}} (hKappaRegular : Cardinal.IsRegular kappa)
    (hKappaUncountable : Cardinal.aleph0 < kappa)
    (hIndexPowerKappa :
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} kappa)
    (hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1) :
    exists H : GeneratorSystem cardinalProductRepresentation A,
      TransitiveGeneratorSystem H := by
  classical
  let G := canonicalGeneratorSystemOfTwoPowerBelowCoordinates
    hRegulars hSmall hIndexInfinite hPower
  have hDirected : GeneratorAtMostIdealSuccessorDirected G :=
    generatorAtMostIdealSuccessorDirected_of_two_power_below_coordinates
      hRegulars hSmall hIndexInfinite hPower G
  let raw := fun lambda : CardinalIndex A =>
    canonicalSemanticGeneratorPointwiseScale hRegulars hSmall
      hIndexInfinite hPower
        (show cardinalProductRepresentation.pcf A lambda.1 from
          hFixed.symm ▸ lambda.2)
  exact exists_transitive_generators_of_localScales hRegulars hSmall
    hIndexInfinite hPower G hFixed hDirected hKappaRegular
    hKappaUncountable hIndexPowerKappa hKappaCoordinates raw

#print axioms exists_transitive_generators_of_regularClosureGap

/-- Jech 24.31 in the present cardinal-product interface: if `A = pcf A`
and the successor of the powerset of its (shrunk) index lies below every
coordinate, then `A` has a transitive generator system. -/
theorem exists_transitive_generators_of_successorPowerBelowCoordinates
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    [Small.{u} (CardinalIndex A)]
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hFixed : cardinalProductRepresentation.pcf A = A)
    (hSuccessorPower : forall i : CardinalIndex A,
      Order.succ ((2 : Cardinal.{u}) ^
        Cardinal.mk (Shrink.{u} (CardinalIndex A))) < i.1) :
    exists H : GeneratorSystem cardinalProductRepresentation A,
      TransitiveGeneratorSystem H := by
  classical
  let hSmall : Small.{u} (CardinalIndex A) := inferInstance
  let rho := (2 : Cardinal.{u}) ^
    Cardinal.mk (Shrink.{u} (CardinalIndex A))
  let kappa := Order.succ rho
  have hShrinkInfinite : Cardinal.aleph0 <=
      Cardinal.mk (Shrink.{u} (CardinalIndex A)) := by
    rw [← Cardinal.lift_le.{u + 1}, Cardinal.lift_mk_shrink'',
      Cardinal.lift_aleph0]
    exact hIndexInfinite
  have hRhoInfinite : Cardinal.aleph0 <= rho :=
    hShrinkInfinite.trans (Cardinal.cantor _).le
  have hKappaRegular : Cardinal.IsRegular kappa :=
    Cardinal.isRegular_succ hRhoInfinite
  have hKappaUncountable : Cardinal.aleph0 < kappa :=
    hRhoInfinite.trans_lt (Order.lt_succ rho)
  have hIndexPowerKappa :
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} kappa := by
    simp only [kappa, rho, Cardinal.lift_succ, Cardinal.lift_power,
      Cardinal.lift_ofNat, Cardinal.lift_mk_shrink'']
    exact Order.lt_succ _
  have hKappaCoordinates : forall i : CardinalIndex A, kappa < i.1 := by
    intro i
    exact hSuccessorPower i
  have hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} a := by
    intro a ha
    exact hIndexPowerKappa.trans
      (Cardinal.lift_lt.mpr (hKappaCoordinates ⟨a, ha⟩))
  exact exists_transitive_generators_of_regularClosureGap hRegulars hSmall
    hIndexInfinite hPower hFixed hKappaRegular hKappaUncountable
    hIndexPowerKappa hKappaCoordinates

#print axioms
  exists_transitive_generators_of_successorPowerBelowCoordinates

/-- A universe-correct strengthened double-powerset gap. The extra successor
is the margin needed after passing from a set to its PCF spectrum: the
spectrum's powerset is bounded by the original double powerset, and taking a
successor still leaves it below every coordinate. -/
def CardinalProductSuccessorDoublePowerBelowCoordinates
    (A : CardSet.{u}) [Small.{u} (CardinalIndex A)] : Prop :=
  forall a : CardinalIndex A,
    Order.succ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
      Cardinal.mk (Shrink.{u} (CardinalIndex A)))) < a.1

theorem cardinalProductDoublePowerBelowCoordinates_of_successor
    {A : CardSet.{u}} [Small.{u} (CardinalIndex A)]
    (hSuccessorDouble :
      CardinalProductSuccessorDoublePowerBelowCoordinates A) :
    CardinalProductDoublePowerBelowCoordinates A := by
  intro a
  have hSmallUniverse :
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
          Cardinal.mk (Shrink.{u} (CardinalIndex A))) < a.1 :=
    (Order.lt_succ _).trans (hSuccessorDouble a)
  have hLifted : Cardinal.lift.{u + 1}
        ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
          Cardinal.mk (Shrink.{u} (CardinalIndex A)))) <
      Cardinal.lift.{u + 1} a.1 :=
    Cardinal.lift_lt.mpr hSmallUniverse
  simpa only [Cardinal.lift_power, Cardinal.lift_ofNat,
    Cardinal.lift_mk_shrink''] using hLifted

#print axioms
  cardinalProductDoublePowerBelowCoordinates_of_successor

/-- The strengthened double-powerset gap constructs transitive and
successor-directed generators on the PCF spectrum itself. This is the form
needed by the tail localization pipeline. -/
theorem exists_pcf_transitive_successorDirected_generators_of_successorDoublePower
    {A : CardSet.{u}} (hRegulars : SetOfRegulars A)
    [Small.{u} (CardinalIndex A)]
    (hIndexInfinite : Cardinal.aleph0 <= Cardinal.mk (CardinalIndex A))
    (hSuccessorDouble :
      CardinalProductSuccessorDoublePowerBelowCoordinates A) :
    exists G : GeneratorSystem cardinalProductRepresentation
        (cardinalProductRepresentation.pcf A),
      TransitiveGeneratorSystem G /\
        GeneratorAtMostIdealSuccessorDirected G := by
  classical
  let hSmall : Small.{u} (CardinalIndex A) := inferInstance
  have hDouble : CardinalProductDoublePowerBelowCoordinates A :=
    cardinalProductDoublePowerBelowCoordinates_of_successor hSuccessorDouble
  have hPower : forall a, A a ->
      (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) <
        Cardinal.lift.{u + 1} a :=
    fun a ha => (Cardinal.cantor _).trans (hDouble ⟨a, ha⟩)
  let G0 := canonicalGeneratorSystemOfTwoPowerBelowCoordinates
    hRegulars hSmall hIndexInfinite hPower
  have hDirected0 : GeneratorAtMostIdealSuccessorDirected G0 :=
    generatorAtMostIdealSuccessorDirected_of_two_power_below_coordinates
      hRegulars hSmall hIndexInfinite hPower G0
  have hPcfSmall : Small.{u}
      (CardinalIndex (cardinalProductRepresentation.pcf A)) :=
    small_of_injective
      (generator_predicate_injective_of_successorDirected
        hRegulars G0 hDirected0)
  letI : Small.{u}
      (CardinalIndex (cardinalProductRepresentation.pcf A)) := hPcfSmall
  have hPcfInfinite : Cardinal.aleph0 <=
      Cardinal.mk (CardinalIndex (cardinalProductRepresentation.pcf A)) :=
    hIndexInfinite.trans (Cardinal.mk_subtype_mono
      (fun _ h => cardinalProductRepresentation_mem_pcf_of_mem hRegulars h))
  have hPcfFixed : cardinalProductRepresentation.pcf
      (cardinalProductRepresentation.pcf A) =
        cardinalProductRepresentation.pcf A :=
    cardinalProductRepresentation_pcf_pcf_eq_of_doublePowerBelow
      A hRegulars hDouble
  have hSpectrumIndexBound :
      Cardinal.mk (CardinalIndex (cardinalProductRepresentation.pcf A)) <=
        (2 : Cardinal.{u + 1}) ^ Cardinal.mk (CardinalIndex A) :=
    cardinal_mk_cardinalIndex_pcf_le_two_power_of_two_power_below_coordinates
      hRegulars hSmall hIndexInfinite hPower
  let rho := (2 : Cardinal.{u}) ^
    Cardinal.mk (Shrink.{u}
      (CardinalIndex (cardinalProductRepresentation.pcf A)))
  let delta := (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
    Cardinal.mk (Shrink.{u} (CardinalIndex A)))
  have hRhoDelta : rho <= delta := by
    rw [← Cardinal.lift_le.{u + 1}]
    simp only [rho, delta, Cardinal.lift_power, Cardinal.lift_ofNat,
      Cardinal.lift_mk_shrink'']
    exact Cardinal.power_le_power_left two_ne_zero hSpectrumIndexBound
  have hPcfSuccessorPower : forall theta :
      CardinalIndex (cardinalProductRepresentation.pcf A),
      Order.succ rho < theta.1 := by
    intro theta
    obtain ⟨a, ha, haTheta⟩ :=
      cardinalProductRepresentation_mem_pcf_exists_member_le
        hRegulars theta.2
    exact (Order.succ_le_succ hRhoDelta).trans_lt
      (hSuccessorDouble ⟨a, ha⟩) |>.trans_le haTheta
  obtain ⟨G, hTransitive⟩ :=
    exists_transitive_generators_of_successorPowerBelowCoordinates
      (cardinalProductRepresentation.pcf_is_setOfRegulars A)
      hPcfInfinite hPcfFixed hPcfSuccessorPower
  have hPcfPower := pcf_two_power_below_coordinates_of_doublePower
    hRegulars hSmall hIndexInfinite hDouble
  exact ⟨G, hTransitive,
    generatorAtMostIdealSuccessorDirected_of_two_power_below_coordinates
      (cardinalProductRepresentation.pcf_is_setOfRegulars A)
      hPcfSmall hPcfInfinite hPcfPower G⟩

#print axioms
  exists_pcf_transitive_successorDirected_generators_of_successorDoublePower

end PcfProject
