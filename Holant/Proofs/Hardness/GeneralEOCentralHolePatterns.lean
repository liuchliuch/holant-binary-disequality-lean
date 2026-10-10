import Holant.Proofs.Hardness.GeneralEONegativePairing
import Mathlib.Logic.Equiv.Fintype

/-! Finite coordinate combinatorics for the central-hole descent. An oriented
perfect pairing is used only to select actual original coordinates. No pairing
restriction is installed as a physical signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHolePatterns
open Holant Holant.Tractable
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible)
end L
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (p : OrientedPerfectPairing n) (a b c : Fin n → Bool)

/-- Reorient every original pair so that `a` is zero at its first incidence. -/
def port (q : Fin p.count × Bool) : Fin n :=
  p.ports (q.1, Bool.xor (a (p.ports (q.1,false))) q.2)

theorem port_injective : Function.Injective (port p a) := by
  intro q r h
  have hh := p.ports.injective h
  have hk := congrArg Prod.fst hh
  rcases q with ⟨q,u⟩
  rcases r with ⟨r,v⟩
  dsimp at hk
  subst r
  have hb := congrArg Prod.snd hh
  dsimp at hb
  congr 1
  cases ha : a (p.ports (q,false)) <;> cases u <;> cases v <;> simp_all

theorem port_a (ha : L.Compatible p a) (k : Fin p.count) (u : Bool) :
    a (port p a (k,u)) = u := by
  have hh := ha k
  unfold port
  cases h0 : a (p.ports (k,false)) <;> cases h1 : a (p.ports (k,true)) <;>
    cases u <;> simp_all

theorem port_opposite (w : Fin n → Bool) (hw : L.Compatible p w) (k : Fin p.count) :
    w (port p a (k,true)) = !(w (port p a (k,false))) := by
  have hh := hw k
  unfold port
  cases ha : a (p.ports (k,false)) <;>
    cases h0 : w (p.ports (k,false)) <;> cases h1 : w (p.ports (k,true)) <;> simp_all

/-- The four triple-column classes modulo simultaneous complementation. -/
def key (k : Fin p.count) : Bool × Bool :=
  (b (port p a (k,false)), c (port p a (k,false)))

theorem port_b (hb : L.Compatible p b) (k : Fin p.count) (u : Bool) :
    b (port p a (k,u)) = Bool.xor (key p a b c k).1 u := by
  cases u
  · simp [key]
  · simpa [key] using port_opposite p a b hb k

theorem port_c (hc : L.Compatible p c) (k : Fin p.count) (u : Bool) :
    c (port p a (k,u)) = Bool.xor (key p a b c k).2 u := by
  cases u
  · simp [key]
  · simpa [key] using port_opposite p a c hc k

theorem twice_count : 2 * p.count = n := by
  have h := Fintype.card_congr p.ports
  simpa [Fintype.card_prod,Nat.mul_comm] using h

/-- With no constant class and no repeated class, only three pairs remain. -/
theorem small_of_no_constant_no_repeat
    (hzero : ∀ k, key p a b c k ≠ (false,false))
    (hinj : Function.Injective (key p a b c)) : n ≤ 6 := by
  let f : Fin p.count → {q : Bool × Bool // q ≠ (false,false)} :=
    fun k => ⟨key p a b c k,hzero k⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hf
  have ht : Fintype.card {q : Bool × Bool // q ≠ (false,false)} = 3 := by decide
  rw [Fintype.card_fin,ht] at hcard
  have hp := twice_count p
  omega

/-- The exact pair-class pigeonhole partition used by the arity descent. -/
theorem partition :
    (∃ k, key p a b c k = (false,false)) ∨
    (∃ i j, i ≠ j ∧ key p a b c i = key p a b c j ∧
      key p a b c i ≠ (false,false)) ∨ n ≤ 6 := by
  classical
  by_cases hz : ∃ k, key p a b c k = (false,false)
  · exact Or.inl hz
  right
  have hzero : ∀ k, key p a b c k ≠ (false,false) := by simpa using hz
  by_cases hi : Function.Injective (key p a b c)
  · exact Or.inr (small_of_no_constant_no_repeat p a b c hzero hi)
  · left
    simp only [Function.Injective,not_forall] at hi
    obtain ⟨i,j,hi⟩ := hi
    obtain ⟨he,hne⟩ := hi
    exact ⟨i,j,hne,he,hzero i⟩

/-- The constant class supplies two different actual ports with columns 000,111. -/
theorem constant_coordinates (ha : L.Compatible p a) (hb : L.Compatible p b)
    (hc : L.Compatible p c) (k : Fin p.count) (hk : key p a b c k = (false,false)) :
    ∃ i j : Fin n, i ≠ j ∧
      a i = false ∧ b i = false ∧ c i = false ∧
      a j = true ∧ b j = true ∧ c j = true := by
  refine ⟨port p a (k,false),port p a (k,true),?_,?_,?_,?_,?_,?_,?_⟩
  · intro h
    have h' := congrArg Prod.snd (port_injective p a h)
    exact Bool.false_ne_true h'
  · exact port_a p a ha k false
  · simpa [hk] using port_b p a b c hb k false
  · simpa [hk] using port_c p a b c hc k false
  · exact port_a p a ha k true
  · simpa [hk] using port_b p a b c hb k true
  · simpa [hk] using port_c p a b c hc k true

/-- Four actual ports, ordered as two equal oriented triple-column pairs. -/
def repeatedPorts (i j : Fin p.count) : Fin 4 → Fin n :=
  ![port p a (i,false),port p a (i,true),port p a (j,false),port p a (j,true)]

theorem repeatedPorts_injective (i j : Fin p.count) (hij : i ≠ j) :
    Function.Injective (repeatedPorts p a i j) := by
  intro u v huv
  fin_cases u <;> fin_cases v <;> try rfl
  all_goals
    have hh := port_injective p a huv
    simp [Prod.mk.injEq,hij,Ne.symm hij] at hh

/-- An arbitrary finite ordered list of distinct original ports can be moved
into the prefix by an actual permutation of all original coordinates. -/
theorem exists_prefix_permutation {r : ℕ} (v : Fin r → Fin n)
    (hv : Function.Injective v) :
    ∃ (h : r ≤ n) (e : Equiv.Perm (Fin n)), ∀ k, e (Fin.castLE h k) = v k := by
  have h : r ≤ n := by simpa using Fintype.card_le_of_injective v hv
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE h) v (Fin.castLE_injective h) hv
  exact ⟨h,e,he⟩

/-- The four-column alternating word with initial bit `u`. -/
def alternating (u : Bool) : Fin 4 → Bool := ![u,!u,u,!u]

theorem repeated_a (ha : L.Compatible p a) (i j : Fin p.count) :
    a ∘ repeatedPorts p a i j = alternating false := by
  funext t
  fin_cases t <;> simp [repeatedPorts,alternating,port_a p a ha]

theorem repeated_b (hb : L.Compatible p b) (i j : Fin p.count)
    (hk : key p a b c i = key p a b c j) :
    b ∘ repeatedPorts p a i j = alternating (key p a b c i).1 := by
  funext t
  fin_cases t <;>
    simp [repeatedPorts,alternating,port_b p a b c hb,←hk]

theorem repeated_c (hc : L.Compatible p c) (i j : Fin p.count)
    (hk : key p a b c i = key p a b c j) :
    c ∘ repeatedPorts p a i j = alternating (key p a b c i).2 := by
  funext t
  fin_cases t <;>
    simp [repeatedPorts,alternating,port_c p a b c hc,←hk]

/-- Reverse both selected pairs. This is only a coordinate permutation. -/
def reverseFour : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 1).trans (Equiv.swap 2 3)

theorem alternating_reverse (u : Bool) : alternating u ∘ reverseFour = alternating (!u) := by
  funext t
  fin_cases t <;> simp [Function.comp_def,reverseFour,alternating,Equiv.swap_apply_def]

/-- One row differs from the other two on the repeated pattern. Its position
among a,b,c is explicitly retained, so no symmetry assumption is needed. -/
def RepeatedColumns (v : Fin 4 → Fin n) : Prop :=
  (a ∘ v = alternating false ∧ b ∘ v = alternating false ∧ c ∘ v = alternating true) ∨
  (a ∘ v = alternating false ∧ c ∘ v = alternating false ∧ b ∘ v = alternating true) ∨
  (b ∘ v = alternating false ∧ c ∘ v = alternating false ∧ a ∘ v = alternating true)

theorem repeated_coordinates (ha : L.Compatible p a) (hb : L.Compatible p b)
    (hc : L.Compatible p c) (i j : Fin p.count) (hij : i ≠ j)
    (hk : key p a b c i = key p a b c j) (hn : key p a b c i ≠ (false,false)) :
    ∃ v : Fin 4 → Fin n, Function.Injective v ∧ RepeatedColumns a b c v := by
  have ha' := repeated_a p a ha i j
  have hb' := repeated_b p a b c hb i j hk
  have hc' := repeated_c p a b c hc i j hk
  have hi := repeatedPorts_injective p a i j hij
  cases he : key p a b c i with
  | mk u v =>
    cases u <;> cases v
    · exact False.elim (hn he)
    · exact ⟨repeatedPorts p a i j,hi,Or.inl ⟨ha',by simpa [he] using hb',by simpa [he] using hc'⟩⟩
    · exact ⟨repeatedPorts p a i j,hi,Or.inr (Or.inl
        ⟨ha',by simpa [he] using hc',by simpa [he] using hb'⟩)⟩
    · refine ⟨repeatedPorts p a i j ∘ reverseFour,hi.comp reverseFour.injective,Or.inr (Or.inr ?_)⟩
      have hr (w : Fin n → Bool) (t : Bool)
          (hw : w ∘ repeatedPorts p a i j = alternating t) :
          w ∘ (repeatedPorts p a i j ∘ reverseFour) = alternating (!t) := by
        rw [←Function.comp_assoc,hw,alternating_reverse]
      exact ⟨hr b true (by simpa [he] using hb'),
        hr c true (by simpa [he] using hc'),hr a false ha'⟩

/-- Coordinate form of the full partition, ready for pinning or loop gadgets. -/
theorem coordinate_partition (ha : L.Compatible p a) (hb : L.Compatible p b)
    (hc : L.Compatible p c) :
    (∃ i j : Fin n, i ≠ j ∧
      a i = false ∧ b i = false ∧ c i = false ∧
      a j = true ∧ b j = true ∧ c j = true) ∨
    (∃ v : Fin 4 → Fin n, Function.Injective v ∧ RepeatedColumns a b c v) ∨ n ≤ 6 := by
  rcases partition p a b c with hz | hr | hs
  · obtain ⟨k,hk⟩ := hz
    exact Or.inl (constant_coordinates p a b c ha hb hc k hk)
  · obtain ⟨i,j,hij,hk,hn⟩ := hr
    exact Or.inr (Or.inl (repeated_coordinates p a b c ha hb hc i j hij hk hn))
  · exact Or.inr (Or.inr hs)

/-- No supplied pairing witness is needed for a central supported triple. -/
theorem central_coordinate_partition (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (ha : f a ≠ 0) (hb : f b ≠ 0) (hc : f c ≠ 0)
    (hd : charge (tripleXor a b c) = 0) :
    (∃ i j : Fin n, i ≠ j ∧
      a i = false ∧ b i = false ∧ c i = false ∧
      a j = true ∧ b j = true ∧ c j = true) ∨
    (∃ v : Fin 4 → Fin n, Function.Injective v ∧ RepeatedColumns a b c v) ∨ n ≤ 6 := by
  let p := GeneralEONegativePairing.pairing f he ha hb hc hd
  apply coordinate_partition p a b c
  · simpa [p] using GeneralEONegativePairing.compatible f he ha hb hc hd (false,false)
  · simpa [p] using GeneralEONegativePairing.compatible f he ha hb hc hd (true,false)
  · simpa [p] using GeneralEONegativePairing.compatible f he ha hb hc hd (false,true)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHolePatterns
