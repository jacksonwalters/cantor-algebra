import AtomlessBooleanAlgebra.Basic
import Mathlib.Data.Set.Countable

/-! # Countability of the cylinder algebra -/

namespace AtomlessBooleanAlgebra

/-- Finite unions of cylinders are parametrized by a countable type. -/
theorem CountableAtomlessBA_countable : CountableAtomlessBA.carrier.Countable := by
  have h : CountableAtomlessBA.carrier =
      Set.range (fun S : Finset (Σ n, BitString n) => ⋃ p ∈ S, cylinder p.2) := by
    ext A
    simp only [CountableAtomlessBA, Set.mem_setOf_eq, Set.mem_range]
    exact exists_congr fun S => eq_comm
  rw [h]
  exact Set.countable_range _

instance : Countable CountableAtomlessBA :=
  CountableAtomlessBA_countable.to_subtype

/-- The empty set and the whole Cantor space are distinct algebra elements. -/
instance : Nontrivial CountableAtomlessBA := by
  refine ⟨⟨⊥, ⊤, ?_⟩⟩
  intro h
  have hsets := congrArg (fun A : CountableAtomlessBA => (A : Set Cantor)) h
  change (∅ : Set Cantor) = Set.univ at hsets
  have hx : (fun _ => false : Cantor) ∈ (∅ : Set Cantor) := hsets.symm ▸ Set.mem_univ _
  exact hx

end AtomlessBooleanAlgebra
