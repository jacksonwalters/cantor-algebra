# Countable Atomless Boolean Algebra

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21613013.svg)](https://doi.org/10.5281/zenodo.21613013)

A Lean 4 formalization of the construction, topology, Stone representation,
and uniqueness of the countable atomless Boolean algebra, also known as the
Cantor algebra.

The construction begins with Cantor space, represented as the type of infinite
Boolean sequences `ℕ → Bool`. A finite bitstring determines a cylinder set:
the set of all infinite sequences having that bitstring as a prefix. Finite
unions of cylinder sets form a Boolean subalgebra of the power set of Cantor
space.

For mathematical motivation and proofs of the construction, Stone representation,
and uniqueness, see
[Construction of the Cantor Algebra](https://doi.org/10.5281/zenodo.24379100).

## Formalized results

The development:

- defines finite bitstrings, Cantor space, cylinder sets, and compatibility;
- proves that incompatible cylinders have empty intersection;
- proves that compatible cylinders intersect in another cylinder;
- expresses complements and intersections of finite unions of cylinders as
  finite unions of cylinders;
- constructs `CountableAtomlessBA` as a `BooleanSubalgebra (Set Cantor)`;
- proves that every cylinder splits into two disjoint, nonempty cylinders;
- proves that every nonempty element of `CountableAtomlessBA` contains a
  nonempty proper subelement;
- proves that its carrier is countable and nontrivial;
- equips Cantor space with the product topology and proves that cylinders form
  a clopen basis;
- identifies the constructed algebra with **all** clopen subsets of Cantor space;
- defines the Stone space using Boolean characters and proves it is homeomorphic
  to Cantor space and to the middle-thirds Cantor subset of the real line;
- proves Stone representation for arbitrary Boolean algebras; and
- proves uniqueness of the nontrivial countable atomless Boolean algebra.

The original atomlessness theorem is:

```lean
theorem CountableAtomlessBA_is_atomless :
  ∀ b ∈ CountableAtomlessBA.carrier, b.Nonempty →
  ∃ a ∈ CountableAtomlessBA.carrier, a.Nonempty ∧ a ⊂ b
```

The main additional results, in namespace `AtomlessBooleanAlgebra`, are:

```lean
theorem CountableAtomlessBA_countable : CountableAtomlessBA.carrier.Countable

theorem mem_CountableAtomlessBA_iff_isClopen (A : Set Cantor) :
  A ∈ CountableAtomlessBA.carrier ↔ IsClopen A

def clopensOrderIso : CountableAtomlessBA ≃o TopologicalSpace.Clopens Cantor

noncomputable def stoneHomeomorphCantor :
  StoneSpace CountableAtomlessBA ≃ₜ Cantor

noncomputable def stoneHomeomorphCantorSet :
  StoneSpace CountableAtomlessBA ≃ₜ cantorSet

theorem countable_atomless_unique (B : Type*)
    [BooleanAlgebra B] [Nontrivial B] [Countable B]
    (hB : Atomless B) : Nonempty (B ≃o CountableAtomlessBA)
```

Here `Atomless B` means that every nonzero element has a nonzero proper
subelement. An order isomorphism `≃o` between Boolean algebras preserves joins,
meets, bottom, top, and complements, so the uniqueness theorem is a
Boolean-algebra classification. `countable_atomless_iso` also gives an
isomorphism between any two algebras satisfying these hypotheses.

`StoneSpace B` is the type of bounded lattice homomorphisms `B → Bool`, with
the topology induced from the product `B → Bool`. These homomorphisms preserve
complements and represent Boolean-algebra ultrafilters by their characteristic
functions. The basic open associated with `b` consists of characters taking
`b` to `true`. This replaces the earlier, incorrect stub using set-theoretic
`Ultrafilter B` and singleton membership.

The canonical map from Cantor space evaluates membership in clopen sets.
Compactness proves its surjectivity, and cylinders separate points. For general
uniqueness, binary partitions successively decide an enumeration of the
algebra; their branches identify its Stone space with Cantor space. Stone
representation then transports the clopen algebra isomorphism. The final
identification with the middle-thirds set reuses mathlib's
`cantorSetHomeomorphNatToBool`.

## Building

The project uses Lean 4.26.0 and mathlib 4.26.0. With
[elan](https://github.com/leanprover/elan) installed, the committed toolchain
and Lake manifest select the required versions automatically:

```sh
git clone https://github.com/jacksonwalters/cantor-algebra.git
cd cantor-algebra
lake build
```

## Project structure

- [`AtomlessBooleanAlgebra/Basic.lean`](AtomlessBooleanAlgebra/Basic.lean)
  contains the cylinder construction and atomlessness proof.
- [`AtomlessBooleanAlgebra/Countability.lean`](AtomlessBooleanAlgebra/Countability.lean)
  proves countability and nontriviality.
- [`AtomlessBooleanAlgebra/Topology.lean`](AtomlessBooleanAlgebra/Topology.lean)
  proves the clopen characterization and connects the two Cantor-space models.
- [`AtomlessBooleanAlgebra/Stone.lean`](AtomlessBooleanAlgebra/Stone.lean)
  defines Stone space and proves the canonical homeomorphism for this algebra.
- [`AtomlessBooleanAlgebra/Representation.lean`](AtomlessBooleanAlgebra/Representation.lean)
  proves general Stone representation using prime-ideal separation.
- [`AtomlessBooleanAlgebra/Uniqueness.lean`](AtomlessBooleanAlgebra/Uniqueness.lean)
  constructs binary refinements and proves general uniqueness.
- [`AtomlessBooleanAlgebra.lean`](AtomlessBooleanAlgebra.lean) is the library
  entry point.

## Citation

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). GitHub's
**Cite this repository** menu can export the citation in common formats.

## License

This project is released under the [MIT License](LICENSE).
