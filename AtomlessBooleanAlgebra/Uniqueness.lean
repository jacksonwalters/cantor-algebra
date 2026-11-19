import AtomlessBooleanAlgebra.Representation

/-! # Uniqueness of the nontrivial countable atomless Boolean algebra

We construct binary partitions which successively decide an enumeration of the algebra.
Their branches identify the Stone space with Cantor space; Stone representation then
gives the Boolean-algebra isomorphism.
-/

open Set Topology TopologicalSpace

namespace AtomlessBooleanAlgebra

/-- Every nonzero element admits a nonzero proper subelement. -/
def Atomless (B : Type*) [BooleanAlgebra B] : Prop :=
  ∀ b : B, b ≠ ⊥ → ∃ a : B, a ≠ ⊥ ∧ a < b

theorem CountableAtomlessBA_atomless : Atomless CountableAtomlessBA := by
  intro b hb
  have hne : b.val.Nonempty := Set.nonempty_iff_ne_empty.mpr
    (fun h => hb (Subtype.ext h))
  obtain ⟨a, ha, hne, hlt⟩ := CountableAtomlessBA_is_atomless b.val b.property hne
  exact ⟨⟨a, ha⟩, (fun h => hne.ne_empty (congrArg Subtype.val h)), hlt⟩

namespace Classification

variable {B : Type*} [BooleanAlgebra B]

theorem exists_split (hB : Atomless B) {b : B} (hb : b ≠ ⊥) :
    ∃ a c : B, a ≠ ⊥ ∧ c ≠ ⊥ ∧ a ⊔ c = b ∧ Disjoint a c := by
  obtain ⟨a, ha, hab⟩ := hB b hb
  refine ⟨a, b \ a, ha, ?_, sup_sdiff_cancel_right hab.le, disjoint_sdiff_self_right⟩
  intro h
  exact hab.not_ge (sdiff_eq_bot_iff.mp h)

theorem exists_deciding_split (hB : Atomless B) {b : B} (hb : b ≠ ⊥) (d : B) :
    ∃ f : Bool → B, (∀ i, f i ≠ ⊥) ∧ f false ⊔ f true = b ∧
      Disjoint (f false) (f true) ∧ (∀ i, f i ≤ d ∨ f i ≤ dᶜ) := by
  obtain ⟨a, c, ha, hc, hac, hdac⟩ := exists_split hB hb
  have hab : a ≤ b := hac ▸ le_sup_left
  have hcb : c ≤ b := hac ▸ le_sup_right
  by_cases hbd : b ⊓ d = ⊥
  · have hle : b ≤ dᶜ := (disjoint_iff.mpr hbd).le_compl_right
    refine ⟨(fun i => if i then c else a), ?_, hac, hdac, ?_⟩
    · intro i; cases i <;> assumption
    · intro i; cases i <;> exact Or.inr (le_trans (by assumption) hle)
  · by_cases hbc : b ⊓ dᶜ = ⊥
    · have hle : b ≤ d := disjoint_compl_right_iff.mp (disjoint_iff.mpr hbc)
      refine ⟨(fun i => if i then c else a), ?_, hac, hdac, ?_⟩
      · intro i; cases i <;> assumption
      · intro i; cases i <;> exact Or.inl (le_trans (by assumption) hle)
    · refine ⟨(fun i => if i then b ⊓ dᶜ else b ⊓ d), ?_, sup_inf_inf_compl,
        disjoint_compl_right.mono inf_le_right inf_le_right, ?_⟩
      · intro i; cases i <;> assumption
      · intro i; cases i
        · exact Or.inl inf_le_right
        · exact Or.inr inf_le_right

noncomputable def split (hB : Atomless B) (b d : B) : Bool → B := by
  classical
  exact if hb : b = ⊥ then fun _ => ⊥ else (exists_deciding_split hB hb d).choose

theorem split_spec (hB : Atomless B) {b : B} (hb : b ≠ ⊥) (d : B) :
    (∀ i, split hB b d i ≠ ⊥) ∧ split hB b d false ⊔ split hB b d true = b ∧
    Disjoint (split hB b d false) (split hB b d true) ∧
    (∀ i, split hB b d i ≤ d ∨ split hB b d i ≤ dᶜ) := by
  simpa [split, hb] using (exists_deciding_split hB hb d).choose_spec

theorem split_le (hB : Atomless B) {b : B} (hb : b ≠ ⊥) (d : B) (i : Bool) :
    split hB b d i ≤ b := by
  calc
    split hB b d i ≤ split hB b d false ⊔ split hB b d true := by
      cases i
      · exact le_sup_left
      · exact le_sup_right
    _ = b := (split_spec hB hb d).2.1

noncomputable def node (hB : Atomless B) (e : ℕ → B) : (n : ℕ) → BitString n → B
  | 0, _ => ⊤
  | n + 1, s => split hB (node hB e n (fun i => s i.castSucc)) (e n) (s (Fin.last n))

variable [Nontrivial B]

theorem node_ne_bot (hB : Atomless B) (e : ℕ → B) (n : ℕ) (s : BitString n) :
    node hB e n s ≠ ⊥ := by
  induction n with
  | zero => exact top_ne_bot
  | succ n ih => exact (split_spec hB (ih _) (e n)).1 _

def initialSegment (x : Cantor) (n : ℕ) : BitString n := fun i => x i

theorem node_antitone (hB : Atomless B) (e : ℕ → B) (x : Cantor) :
    Antitone (fun n => node hB e n (initialSegment x n)) := by
  apply antitone_nat_of_succ_le
  intro n
  exact split_le hB (node_ne_bot hB e n _) (e n) (x n)

theorem exists_path_point (hB : Atomless B) (e : ℕ → B) (x : Cantor) :
    ∃ F : StoneSpace B, ∀ n, F (node hB e n (initialSegment x n)) = true := by
  let C := fun n => StoneBasicOpen (node hB e n (initialSegment x n))
  have hd : Directed (· ⊇ ·) C := by
    intro n m
    exact ⟨max n m, StoneSpace.basicOpen_subset_iff.mpr (node_antitone hB e x (le_max_left _ _)),
      StoneSpace.basicOpen_subset_iff.mpr (node_antitone hB e x (le_max_right _ _))⟩
  obtain ⟨F, hF⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hd
    (fun n => StoneSpace.basicOpen_nonempty (node_ne_bot hB e n _))
    (fun n => (isClopen_StoneBasicOpen _).isClosed.isCompact)
    (fun n => (isClopen_StoneBasicOpen _).isClosed)
  exact ⟨F, fun n => Set.mem_iInter.mp hF n⟩

noncomputable def pathPoint (hB : Atomless B) (e : ℕ → B) (x : Cantor) : StoneSpace B :=
  (exists_path_point hB e x).choose

theorem pathPoint_spec (hB : Atomless B) (e : ℕ → B) (x : Cantor) (n : ℕ) :
    pathPoint hB e x (node hB e n (initialSegment x n)) = true :=
  (exists_path_point hB e x).choose_spec n

omit [Nontrivial B] in
theorem character_eq_of_decides {a b : B} (hd : a ≤ b ∨ a ≤ bᶜ)
    {F G : StoneSpace B} (hF : F a = true) (hG : G a = true) : F b = G b := by
  rcases hd with h | h
  · have hFb := StoneSpace.basicOpen_subset_iff.mpr h hF
    have hGb := StoneSpace.basicOpen_subset_iff.mpr h hG
    exact hFb.trans hGb.symm
  · have hFb := StoneSpace.basicOpen_subset_iff.mpr h hF
    have hGb := StoneSpace.basicOpen_subset_iff.mpr h hG
    change F bᶜ = true at hFb
    change G bᶜ = true at hGb
    rw [map_compl'] at hFb hGb
    cases h1 : F b <;> cases h2 : G b <;> simp_all

theorem characters_eq_on_path (hB : Atomless B) {e : ℕ → B} (he : Function.Surjective e)
    (x : Cantor) {F G : StoneSpace B}
    (hF : ∀ n, F (node hB e n (initialSegment x n)) = true)
    (hG : ∀ n, G (node hB e n (initialSegment x n)) = true) : F = G := by
  apply DFunLike.ext
  intro b
  obtain ⟨n, rfl⟩ := he b
  exact character_eq_of_decides
    ((split_spec hB (node_ne_bot hB e n _) (e n)).2.2.2 (x n)) (hF (n + 1)) (hG (n + 1))

instance (n : ℕ) : TopologicalSpace (BitString n) :=
  inferInstanceAs (TopologicalSpace (Fin n → Bool))

instance (n : ℕ) : DiscreteTopology (BitString n) :=
  inferInstanceAs (DiscreteTopology (Fin n → Bool))

omit [Nontrivial B] in
theorem character_apply_of_decides {a b : B} (hd : a ≤ b ∨ a ≤ bᶜ)
    {F : StoneSpace B} (hF : F a = true) :
    F b = @decide (a ≤ b) (Classical.propDecidable _) := by
  classical
  by_cases h : a ≤ b
  · simpa [h] using (StoneSpace.basicOpen_subset_iff.mpr h hF : F b = true)
  · have hc : F bᶜ = true := StoneSpace.basicOpen_subset_iff.mpr (hd.resolve_left h) hF
    rw [map_compl'] at hc
    cases hFb : F b <;> simp_all

theorem continuous_pathPoint (hB : Atomless B) {e : ℕ → B} (he : Function.Surjective e) :
    Continuous (pathPoint hB e) := by
  classical
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  obtain ⟨n, rfl⟩ := he b
  have hc : Continuous (fun x : Cantor => decide
      (node hB e (n + 1) (initialSegment x (n + 1)) ≤ e n)) :=
    (continuous_of_discreteTopology (f := fun s : BitString (n + 1) =>
      decide (node hB e (n + 1) s ≤ e n))).comp
      (continuous_pi fun i => continuous_apply i.val)
  convert hc using 1
  funext x
  exact character_apply_of_decides
    ((split_spec hB (node_ne_bot hB e n _) (e n)).2.2.2 (x n))
    (pathPoint_spec hB e x (n + 1))

omit [Nontrivial B] in
theorem split_bit_unique (hB : Atomless B) {b : B} (hb : b ≠ ⊥) (d : B)
    (F : StoneSpace B) {i j : Bool}
    (hi : F (split hB b d i) = true) (hj : F (split hB b d j) = true) : i = j := by
  have hd := congrArg F (split_spec hB hb d).2.2.1.eq_bot
  rw [map_inf, map_bot] at hd
  cases i <;> cases j <;> simp_all

theorem pathPoint_injective (hB : Atomless B) (e : ℕ → B) :
    Function.Injective (pathPoint hB e) := by
  intro x y h
  have hs : ∀ n, initialSegment x n = initialSegment y n := by
    intro n
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
      have hx := pathPoint_spec hB e x (n + 1)
      have hy := pathPoint_spec hB e y (n + 1)
      change pathPoint hB e x (split hB (node hB e n (initialSegment x n)) (e n) (x n)) = true at hx
      change pathPoint hB e y (split hB (node hB e n (initialSegment y n)) (e n) (y n)) = true at hy
      rw [h, ih] at hx
      have hbit := split_bit_unique hB (node_ne_bot hB e n _) (e n) _ hx hy
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hbit
      · exact congrFun ih j
  funext i
  exact congrFun (hs (i + 1)) (Fin.last i)

noncomputable def branch (hB : Atomless B) (e : ℕ → B) (F : StoneSpace B) :
    (n : ℕ) → BitString n
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (branch hB e F n)
      (if F (split hB (node hB e n (branch hB e F n)) (e n) false) then false else true)

theorem branch_mem (hB : Atomless B) (e : ℕ → B) (F : StoneSpace B) (n : ℕ) :
    F (node hB e n (branch hB e F n)) = true := by
  induction n with
  | zero => exact map_top F
  | succ n ih =>
    have hs := congrArg F (split_spec hB (node_ne_bot hB e n (branch hB e F n)) (e n)).2.1
    rw [map_sup, ih] at hs
    simp only [node, branch, Fin.snoc_castSucc, Fin.snoc_last]
    cases h : F (split hB (node hB e n (branch hB e F n)) (e n) false) <;>
      simp_all

noncomputable def branchSequence (hB : Atomless B) (e : ℕ → B) (F : StoneSpace B) : Cantor :=
  fun n => branch hB e F (n + 1) (Fin.last n)

omit [Nontrivial B] in
theorem branchSequence_initialSegment (hB : Atomless B) (e : ℕ → B)
    (F : StoneSpace B) (n : ℕ) :
    initialSegment (branchSequence hB e F) n = branch hB e F n := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · change branchSequence hB e F j = branch hB e F (n + 1) j.castSucc
      simpa only [branch, Fin.snoc_castSucc] using congrFun ih j

theorem pathPoint_surjective (hB : Atomless B) {e : ℕ → B} (he : Function.Surjective e) :
    Function.Surjective (pathPoint hB e) := by
  intro F
  refine ⟨branchSequence hB e F, characters_eq_on_path hB he _
    (pathPoint_spec hB e _) ?_⟩
  intro n
  rw [branchSequence_initialSegment]
  exact branch_mem hB e F n

/-- Binary refinement identifies the Stone space of any enumerated atomless algebra. -/
noncomputable def cantorHomeomorph (hB : Atomless B) {e : ℕ → B}
    (he : Function.Surjective e) : Cantor ≃ₜ StoneSpace B :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (pathPoint hB e)
      ⟨pathPoint_injective hB e, pathPoint_surjective hB he⟩)
    (continuous_pathPoint hB he)

end Classification

/-- A homeomorphism transports the Boolean algebra of clopen sets by inverse image. -/
def clopensCongr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Clopens Y ≃o Clopens X where
  toFun U := ⟨h ⁻¹' U, U.isClopen.preimage h.continuous⟩
  invFun U := ⟨h.symm ⁻¹' U, U.isClopen.preimage h.symm.continuous⟩
  left_inv U := by ext x; simp
  right_inv U := by ext x; simp
  map_rel_iff' := by
    intro U V
    exact ⟨fun hUV y hy => by simpa using hUV (show h.symm y ∈ h ⁻¹' U by simpa),
      fun hUV x hx => hUV hx⟩

/-- Every nontrivial countable atomless Boolean algebra is isomorphic to the cylinder algebra.
Order isomorphisms of Boolean algebras preserve joins, meets, bounds, and complements. -/
theorem countable_atomless_unique (B : Type*) [BooleanAlgebra B] [Nontrivial B] [Countable B]
    (hB : Atomless B) : Nonempty (B ≃o CountableAtomlessBA) := by
  obtain ⟨e, he⟩ := exists_surjective_nat B
  exact ⟨(StoneSpace.representation B).trans
    ((clopensCongr (Classification.cantorHomeomorph hB he)).trans clopensOrderIso.symm)⟩

/-- Any two nontrivial countable atomless Boolean algebras are isomorphic. -/
theorem countable_atomless_iso (B C : Type*) [BooleanAlgebra B] [BooleanAlgebra C]
    [Nontrivial B] [Nontrivial C] [Countable B] [Countable C]
    (hB : Atomless B) (hC : Atomless C) : Nonempty (B ≃o C) := by
  obtain ⟨f⟩ := countable_atomless_unique B hB
  obtain ⟨g⟩ := countable_atomless_unique C hC
  exact ⟨f.trans g.symm⟩

end AtomlessBooleanAlgebra
