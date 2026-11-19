import AtomlessBooleanAlgebra.Topology

/-! # Stone space and its identification with Cantor space

Points are Boolean characters, equivalently ultrafilters of the Boolean algebra.
They are not set-theoretic ultrafilters on the underlying type of algebra elements.
-/

open Set Topology TopologicalSpace

/-- The Stone space of a Boolean algebra, represented by its two-valued characters.
Bounded lattice homomorphisms between Boolean algebras also preserve complements. -/
def StoneSpace (B : Type*) [BooleanAlgebra B] := BoundedLatticeHom B Bool

namespace StoneSpace

variable {B : Type*} [BooleanAlgebra B]

instance : FunLike (StoneSpace B) B Bool :=
  inferInstanceAs (FunLike (BoundedLatticeHom B Bool) B Bool)

instance : BoundedLatticeHomClass (StoneSpace B) B Bool :=
  inferInstanceAs (BoundedLatticeHomClass (BoundedLatticeHom B Bool) B Bool)

instance : TopologicalSpace (StoneSpace B) :=
  TopologicalSpace.induced (fun F : StoneSpace B => (F : B → Bool)) inferInstance

theorem continuous_coe : Continuous (fun F : StoneSpace B => (F : B → Bool)) :=
  continuous_induced_dom

instance : T2Space (StoneSpace B) :=
  T2Space.of_injective_continuous DFunLike.coe_injective continuous_coe

theorem continuous_eval (b : B) : Continuous (fun F : StoneSpace B => F b) :=
  (continuous_apply b).comp continuous_coe

end StoneSpace

/-- The basic Stone open associated with an algebra element. -/
def StoneBasicOpen {B : Type*} [BooleanAlgebra B] (b : B) : Set (StoneSpace B) :=
  {F | F b = true}

theorem isClopen_StoneBasicOpen {B : Type*} [BooleanAlgebra B] (b : B) :
    IsClopen (StoneBasicOpen b) :=
  (isClopen_discrete ({true} : Set Bool)).preimage (StoneSpace.continuous_eval b)

@[simp] theorem StoneBasicOpen_bot {B : Type*} [BooleanAlgebra B] :
    StoneBasicOpen (⊥ : B) = ∅ := by
  ext F
  simp [StoneBasicOpen]

@[simp] theorem StoneBasicOpen_top {B : Type*} [BooleanAlgebra B] :
    StoneBasicOpen (⊤ : B) = Set.univ := by
  ext F
  simp [StoneBasicOpen]

namespace AtomlessBooleanAlgebra

/-- Evaluation at a point is a Boolean character of the cylinder algebra. -/
noncomputable def stoneEvaluation (x : Cantor) : StoneSpace CountableAtomlessBA :=
  { toFun := fun A => (A : Set Cantor).boolIndicator x
    map_sup' := by
      intro A B
      by_cases hA : x ∈ A.val <;> by_cases hB : x ∈ B.val <;>
        simp [Set.boolIndicator, hA, hB]
    map_inf' := by
      intro A B
      by_cases hA : x ∈ A.val <;> by_cases hB : x ∈ B.val <;>
        simp [Set.boolIndicator, hA, hB]
    map_top' := by simp [Set.boolIndicator]
    map_bot' := by simp [Set.boolIndicator] }

@[simp] theorem stoneEvaluation_apply (x : Cantor) (A : CountableAtomlessBA) :
    stoneEvaluation x A = true ↔ x ∈ (A : Set Cantor) := by
  change A.val.boolIndicator x = true ↔ _
  exact (Set.mem_iff_boolIndicator A.val x).symm

theorem continuous_stoneEvaluation : Continuous stoneEvaluation := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro A
  exact (continuous_boolIndicator_iff_isClopen A.val).mpr
    ((mem_CountableAtomlessBA_iff_isClopen A.val).mp A.property)

theorem stoneEvaluation_injective : Function.Injective stoneEvaluation := by
  intro x y h
  funext i
  let s : BitString (i + 1) := fun j => x j
  let A : CountableAtomlessBA := ⟨cylinder s, cylinder_mem s⟩
  have hx : stoneEvaluation x A = true := (stoneEvaluation_apply x A).mpr (by intro j; rfl)
  rw [h] at hx
  have hy := (stoneEvaluation_apply y A).mp hx
  exact (hy ⟨i, Nat.lt_succ_self i⟩).symm

/-- Compactness turns a character's finite-intersection property into a point. -/
theorem stoneEvaluation_surjective : Function.Surjective stoneEvaluation := by
  intro F
  let I := {A : CountableAtomlessBA // F A = true}
  haveI : Nonempty I := ⟨⟨⊤, by exact map_top F⟩⟩
  have hne (A : I) : (A.val : Set Cantor).Nonempty := by
    by_contra h
    have heq : A.val = ⊥ := Subtype.ext (Set.not_nonempty_iff_eq_empty.mp h)
    have hf := A.property
    rw [heq, map_bot] at hf
    cases hf
  have hdir : Directed (· ⊇ ·) (fun A : I => (A.val : Set Cantor)) := by
    intro A B
    refine ⟨⟨A.val ⊓ B.val, ?_⟩, Set.inter_subset_left, Set.inter_subset_right⟩
    rw [map_inf, A.property, B.property]
    rfl
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun A : I => (A.val : Set Cantor)) hdir hne
    (fun A =>
      ((mem_CountableAtomlessBA_iff_isClopen A.val.val).mp A.val.property).isClosed.isCompact)
    (fun A => ((mem_CountableAtomlessBA_iff_isClopen A.val.val).mp A.val.property).isClosed)
  have hpos (A : CountableAtomlessBA) (hA : F A = true) : x ∈ (A : Set Cantor) :=
    Set.mem_iInter.mp hx ⟨A, hA⟩
  refine ⟨x, DFunLike.ext _ _ fun A => ?_⟩
  cases hA : F A with
  | true => exact (stoneEvaluation_apply x A).mpr (hpos A hA)
  | false =>
    have hc : F Aᶜ = true := by rw [map_compl', hA]; rfl
    have hnot : x ∉ (A : Set Cantor) := hpos Aᶜ hc
    change A.val.boolIndicator x = false
    simp [Set.boolIndicator, hnot]

/-- The canonical Stone-space/Cantor-space homeomorphism. -/
noncomputable def cantorHomeomorphStone : Cantor ≃ₜ StoneSpace CountableAtomlessBA :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective stoneEvaluation ⟨stoneEvaluation_injective, stoneEvaluation_surjective⟩)
    continuous_stoneEvaluation

/-- The Stone space of the constructed Boolean algebra is Cantor space. -/
noncomputable def stoneHomeomorphCantor : StoneSpace CountableAtomlessBA ≃ₜ Cantor :=
  cantorHomeomorphStone.symm

/-- The same Stone space is homeomorphic to the middle-thirds Cantor set. -/
noncomputable def stoneHomeomorphCantorSet : StoneSpace CountableAtomlessBA ≃ₜ cantorSet :=
  stoneHomeomorphCantor.trans cantorHomeomorphCantorSet

end AtomlessBooleanAlgebra
