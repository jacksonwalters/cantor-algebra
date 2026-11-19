import AtomlessBooleanAlgebra.Countability
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Instances.CantorSet

/-! # The cylinder algebra is the algebra of clopen subsets of Cantor space -/

open Set Topology TopologicalSpace

namespace AtomlessBooleanAlgebra

instance : TopologicalSpace Cantor := inferInstanceAs (TopologicalSpace (ℕ → Bool))
instance : CompactSpace Cantor := inferInstanceAs (CompactSpace (ℕ → Bool))
instance : T2Space Cantor := inferInstanceAs (T2Space (ℕ → Bool))

/-- A cylinder fixes finitely many coordinates in a product of discrete spaces. -/
theorem isClopen_cylinder {n : ℕ} (s : BitString n) : IsClopen (cylinder s) := by
  have heq : cylinder s = ⋂ i : Fin n, {x : Cantor | x i = s i} := by
    ext x
    simp [cylinder]
  rw [heq]
  exact isClopen_iInter_of_finite fun i =>
    (isClopen_discrete ({s i} : Set Bool)).preimage (continuous_apply i.val)

/-- Every open neighborhood contains an initial-segment cylinder about its point. -/
theorem exists_cylinder_subset_of_isOpen {U : Set Cantor} (hU : IsOpen U)
    {x : Cantor} (hx : x ∈ U) :
    ∃ n, ∃ s : BitString n, x ∈ cylinder s ∧ cylinder s ⊆ U := by
  obtain ⟨V, hV, hxV, hVU⟩ :=
    (isTopologicalBasis_pi fun _ : ℕ => isTopologicalBasis_opens (α := Bool)).isOpen_iff.mp hU x hx
  obtain ⟨W, F, _, rfl⟩ := hV
  refine ⟨F.sup id + 1, fun i => x i, (by intro i; rfl), ?_⟩
  intro y hy
  apply hVU
  intro i hi
  have hiN : i < F.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  rw [hy ⟨i, hiN⟩]
  exact hxV i hi

theorem cylinders_isTopologicalBasis :
    IsTopologicalBasis (Set.range fun p : Σ n, BitString n => cylinder p.2) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨p, rfl⟩
    exact (isClopen_cylinder p.2).isOpen
  · intro x U hx hU
    obtain ⟨n, s, hxs, hsU⟩ := exists_cylinder_subset_of_isOpen hU hx
    exact ⟨cylinder s, ⟨⟨n, s⟩, rfl⟩, hxs, hsU⟩

/-- The finite-union construction gives exactly the clopen sets, including the empty set. -/
theorem mem_CountableAtomlessBA_iff_isClopen (A : Set Cantor) :
    A ∈ CountableAtomlessBA.carrier ↔ IsClopen A := by
  constructor
  · rintro ⟨S, rfl⟩
    exact isClopen_biUnion_finset fun p _ => isClopen_cylinder p.2
  · intro hA
    let I := {p : Σ n, BitString n | cylinder p.2 ⊆ A}
    have hcover : A ⊆ ⋃ p : I, cylinder p.val.2 := by
      intro x hx
      obtain ⟨n, s, hxs, hsA⟩ := exists_cylinder_subset_of_isOpen hA.isOpen hx
      exact Set.mem_iUnion.mpr ⟨⟨⟨n, s⟩, hsA⟩, hxs⟩
    obtain ⟨S, hS⟩ := hA.isClosed.isCompact.elim_finite_subcover
      (fun p : I => cylinder p.val.2) (fun p => (isClopen_cylinder p.val.2).isOpen) hcover
    classical
    refine ⟨S.image Subtype.val, Set.Subset.antisymm ?_ ?_⟩
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hS hx)
      exact Set.mem_iUnion₂.mpr ⟨p.val, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hxp⟩
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
      exact q.property hxp

/-- An order isomorphism of Boolean algebras preserves all Boolean operations. -/
def clopensOrderIso : CountableAtomlessBA ≃o Clopens Cantor where
  toFun A := ⟨A.val, (mem_CountableAtomlessBA_iff_isClopen A.val).mp A.property⟩
  invFun A := ⟨A, (mem_CountableAtomlessBA_iff_isClopen A).mpr A.isClopen⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The sequence model agrees with the middle-thirds Cantor subset of the real line. -/
noncomputable def cantorHomeomorphCantorSet : Cantor ≃ₜ cantorSet :=
  cantorSetHomeomorphNatToBool.symm

end AtomlessBooleanAlgebra
