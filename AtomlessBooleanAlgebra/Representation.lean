import AtomlessBooleanAlgebra.Stone
import Mathlib.Order.PrimeSeparator

/-! # Stone representation for Boolean algebras -/

open Set Topology TopologicalSpace

namespace StoneSpace

variable {B : Type*} [BooleanAlgebra B]

theorem isClosed_range_coe : IsClosed (Set.range (fun F : StoneSpace B => (F : B → Bool))) := by
  have hr : Set.range (fun F : StoneSpace B => (F : B → Bool)) =
      {f : B → Bool | f ⊤ = ⊤ ∧ f ⊥ = ⊥ ∧
        (∀ a b, f (a ⊔ b) = f a ⊔ f b) ∧ (∀ a b, f (a ⊓ b) = f a ⊓ f b)} := by
    ext f
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨map_top F, map_bot F, map_sup F, map_inf F⟩
    · rintro ⟨ht, hb, hs, hi⟩
      exact ⟨({ toFun := f
                map_top' := ht
                map_bot' := hb
                map_sup' := hs
                map_inf' := hi } : BoundedLatticeHom B Bool), rfl⟩
  rw [hr]
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_eq (continuous_apply _) continuous_const).inter
    ((isClosed_eq (continuous_apply _) continuous_const).inter ?_)
  apply IsClosed.inter
  · exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply _) (by fun_prop)
  · exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply _) (by fun_prop)

instance : CompactSpace (StoneSpace B) :=
  (show IsClosedEmbedding (fun F : StoneSpace B => (F : B → Bool)) from
    ⟨DFunLike.coe_injective.isEmbedding_induced, isClosed_range_coe⟩).compactSpace

/-- The complement of a prime ideal gives a two-valued Boolean character. -/
noncomputable def ofPrimeIdeal (I : Order.Ideal B) (hI : I.IsPrime) : StoneSpace B := by
  classical
  have hs (a b : B) : a ⊔ b ∈ I ↔ a ∈ I ∧ b ∈ I :=
    ⟨fun h => ⟨I.lower le_sup_left h, I.lower le_sup_right h⟩,
      fun h => Order.Ideal.sup_mem h.1 h.2⟩
  have hi (a b : B) : a ⊓ b ∈ I ↔ a ∈ I ∨ b ∈ I :=
    ⟨hI.mem_or_mem, fun h => h.elim (I.lower inf_le_left) (I.lower inf_le_right)⟩
  exact
    { toFun := fun b => decide (b ∉ I)
      map_top' := by simp [hI.toIsProper.top_notMem]
      map_bot' := by simp [I.bot_mem]
      map_sup' := by
        intro a b
        by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;> simp [hs, ha, hb]
      map_inf' := by
        intro a b
        by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;> simp [hi, ha, hb] }

/-- Boolean characters separate any failed order relation. -/
theorem exists_separating_character {a b : B} (h : ¬a ≤ b) :
    ∃ F : StoneSpace B, F a = true ∧ F b = false := by
  classical
  have hd : Disjoint (Order.PFilter.principal a : Set B) (Order.Ideal.principal b) := by
    apply Set.disjoint_left.mpr
    intro c hc hd
    exact h (hc.trans hd)
  obtain ⟨I, hI, hbI, hdI⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
  have ha : a ∉ I := Set.disjoint_left.mp hdI (show a ∈ Order.PFilter.principal a from le_rfl)
  have hb : b ∈ I := hbI (show b ∈ Order.Ideal.principal b from le_rfl)
  refine ⟨ofPrimeIdeal I hI, ?_, ?_⟩ <;>
    change decide (_ ∉ I) = _ <;> simp [ha, hb]

theorem basicOpen_subset_iff {a b : B} : StoneBasicOpen a ⊆ StoneBasicOpen b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    obtain ⟨F, ha, hb⟩ := exists_separating_character hab
    have := h ha
    change F b = true at this
    rw [hb] at this
    cases this
  · intro h F hF
    change F a = true at hF
    have hm : F a ≤ F b := OrderHomClass.mono F h
    rw [hF] at hm
    exact top_unique hm

theorem basicOpen_nonempty {a : B} (ha : a ≠ ⊥) : (StoneBasicOpen a).Nonempty := by
  obtain ⟨F, hF, _⟩ := exists_separating_character (show ¬a ≤ ⊥ from fun h => ha (le_bot_iff.mp h))
  exact ⟨F, hF⟩

@[simp] theorem basicOpen_sup (a b : B) :
    StoneBasicOpen (a ⊔ b) = StoneBasicOpen a ∪ StoneBasicOpen b := by
  ext F
  simp [StoneBasicOpen, map_sup]

@[simp] theorem basicOpen_inf (a b : B) :
    StoneBasicOpen (a ⊓ b) = StoneBasicOpen a ∩ StoneBasicOpen b := by
  ext F
  simp [StoneBasicOpen, map_inf]

@[simp] theorem basicOpen_compl (a : B) :
    StoneBasicOpen aᶜ = (StoneBasicOpen a)ᶜ := by
  ext F
  simp [StoneBasicOpen, map_compl']

theorem basicOpen_basis : IsTopologicalBasis (Set.range (StoneBasicOpen (B := B))) := by
  classical
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact (isClopen_StoneBasicOpen a).isOpen
  · intro F U hFU hU
    obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
    obtain ⟨S, W, hW, hWV⟩ := isOpen_pi_iff.mp hV F hFU
    let c : B → B := fun a => if F a then a else aᶜ
    refine ⟨StoneBasicOpen (S.inf c), ⟨S.inf c, rfl⟩, ?_, ?_⟩
    · change F (S.inf c) = ⊤
      rw [map_finset_inf, Finset.inf_eq_top_iff]
      intro a _
      cases hFa : F a <;> simp [c, hFa, map_compl']
    · intro G hG
      change G (S.inf c) = true at hG
      apply hWV
      intro a ha
      have hm : G (S.inf c) ≤ G (c a) := OrderHomClass.mono G (Finset.inf_le ha)
      rw [hG] at hm
      have hc : G (c a) = true := top_unique hm
      have heq : G a = F a := by
        cases hFa : F a <;> cases hGa : G a <;> simp_all [c, map_compl']
      change G a ∈ W a
      rw [heq]
      exact (hW a ha).2

/-- Every clopen of a Stone space is a single Boolean basic open. -/
theorem clopen_eq_basicOpen (U : Clopens (StoneSpace B)) : ∃ a : B, StoneBasicOpen a = U := by
  classical
  let I := {a : B // StoneBasicOpen a ⊆ U}
  have hc : (U : Set (StoneSpace B)) ⊆ ⋃ a : I, StoneBasicOpen a.val := by
    intro F hF
    obtain ⟨_, ⟨a, rfl⟩, ha, hs⟩ := basicOpen_basis.isOpen_iff.mp U.isOpen F hF
    exact Set.mem_iUnion.mpr ⟨⟨a, hs⟩, ha⟩
  obtain ⟨S, hS⟩ := U.isClosed.isCompact.elim_finite_subcover
    (fun a : I => StoneBasicOpen a.val) (fun a => (isClopen_StoneBasicOpen a.val).isOpen) hc
  have heq : StoneBasicOpen (S.sup Subtype.val) = ⋃ a ∈ S, StoneBasicOpen a.val := by
    clear hS
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih => simp [Finset.sup_insert, ih]
  refine ⟨S.sup Subtype.val, ?_⟩
  rw [heq]
  exact Set.Subset.antisymm (by
    intro F hF
    obtain ⟨a, _, ha⟩ := Set.mem_iUnion₂.mp hF
    exact a.property ha) hS

/-- Stone's representation as an order isomorphism, hence a Boolean-algebra isomorphism. -/
noncomputable def representation (B : Type*) [BooleanAlgebra B] :
    B ≃o Clopens (StoneSpace B) := by
  let f : B → Clopens (StoneSpace B) := fun b =>
    ⟨StoneBasicOpen b, isClopen_StoneBasicOpen b⟩
  have hinj : Function.Injective f := by
    intro a b h
    have heq : StoneBasicOpen a = StoneBasicOpen b := congrArg SetLike.coe h
    exact le_antisymm (basicOpen_subset_iff.mp heq.le) (basicOpen_subset_iff.mp heq.ge)
  have hsurj : Function.Surjective f := fun U => by
    obtain ⟨a, ha⟩ := clopen_eq_basicOpen U
    exact ⟨a, Clopens.ext ha⟩
  exact { Equiv.ofBijective f ⟨hinj, hsurj⟩ with map_rel_iff' := basicOpen_subset_iff }

end StoneSpace
