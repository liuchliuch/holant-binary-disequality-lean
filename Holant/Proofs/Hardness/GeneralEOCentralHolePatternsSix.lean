import Holant.Proofs.Hardness.GeneralEOCentralHolePatternsPrefix

/-! The genuine six-port endpoint of the complementary-column partition.
All three nonconstant classes must occur, once each. Their actual original
ports give the explicit normal form used in MWX Lemma 52. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHolePatterns
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (p : OrientedPerfectPairing n) (a b c : Fin n → Bool)

def sixFirst : Fin 6 → Bool := ![true,false,true,false,false,true]
def sixSecond : Fin 6 → Bool := ![true,false,false,true,true,false]
def sixThird : Fin 6 → Bool := ![false,true,true,false,true,false]
def sixHole : Fin 6 → Bool := ![false,true,false,true,false,true]

theorem six_xor : tripleXor sixFirst sixSecond sixThird = sixHole := by
  funext t
  fin_cases t <;> rfl

/-- Ordered ports for the three different nonconstant classes. -/
def sixPorts (i j k : Fin p.count) : Fin 6 → Fin n :=
  ![port p a (i,true),port p a (i,false),port p a (j,true),
    port p a (j,false),port p a (k,false),port p a (k,true)]

theorem sixPorts_injective (i j k : Fin p.count) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (sixPorts p a i j k) := by
  intro u v huv
  fin_cases u <;> fin_cases v <;> try rfl
  all_goals
    have hh := port_injective p a huv
    simp [Prod.mk.injEq,hij,hik,hjk,Ne.symm hij,Ne.symm hik,Ne.symm hjk] at hh

theorem sixPorts_first (ha : L.Compatible p a) (i j k : Fin p.count) :
    a ∘ sixPorts p a i j k = sixFirst := by
  funext t
  fin_cases t <;> simp [sixPorts,sixFirst,port_a p a ha]

theorem sixPorts_second (hb : L.Compatible p b) (i j k : Fin p.count)
    (hi : key p a b c i = (false,true)) (hj : key p a b c j = (true,false))
    (hk : key p a b c k = (true,true)) :
    b ∘ sixPorts p a i j k = sixSecond := by
  funext t
  fin_cases t <;> simp [sixPorts,sixSecond,port_b p a b c hb,hi,hj,hk]

theorem sixPorts_third (hc : L.Compatible p c) (i j k : Fin p.count)
    (hi : key p a b c i = (false,true)) (hj : key p a b c j = (true,false))
    (hk : key p a b c k = (true,true)) :
    c ∘ sixPorts p a i j k = sixThird := by
  funext t
  fin_cases t <;> simp [sixPorts,sixThird,port_c p a b c hc,hi,hj,hk]

/-- At arity six, absence of the two reduction cases forces all three
nonconstant classes to occur. -/
theorem six_keys (hn : n = 6)
    (hzero : ∀ k, key p a b c k ≠ (false,false))
    (hinj : Function.Injective (key p a b c)) :
    ∃ i j k : Fin p.count, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      key p a b c i = (false,true) ∧ key p a b c j = (true,false) ∧
      key p a b c k = (true,true) := by
  let f : Fin p.count → {q : Bool × Bool // q ≠ (false,false)} :=
    fun k => ⟨key p a b c k,hzero k⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcard : Fintype.card (Fin p.count) =
      Fintype.card {q : Bool × Bool // q ≠ (false,false)} := by
    have hp := twice_count p
    have ht : Fintype.card {q : Bool × Bool // q ≠ (false,false)} = 3 := by decide
    rw [Fintype.card_fin,ht]
    omega
  have hs := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩).2
  obtain ⟨i,hi⟩ := hs ⟨(false,true),by decide⟩
  obtain ⟨j,hj⟩ := hs ⟨(true,false),by decide⟩
  obtain ⟨k,hk⟩ := hs ⟨(true,true),by decide⟩
  have hi' : key p a b c i = (false,true) := congrArg Subtype.val hi
  have hj' : key p a b c j = (true,false) := congrArg Subtype.val hj
  have hk' : key p a b c k = (true,true) := congrArg Subtype.val hk
  refine ⟨i,j,k,?_,?_,?_,hi',hj',hk'⟩
  · intro h
    rw [h,hj'] at hi'
    contradiction
  · intro h
    rw [h,hk'] at hi'
    contradiction
  · intro h
    rw [h,hk'] at hj'
    contradiction

/-- A full equivalence of the original coordinates gives the exact three
supported words and their central xor, with their row order unchanged. -/
theorem six_normal_form (hn : n = 6)
    (ha : L.Compatible p a) (hb : L.Compatible p b) (hc : L.Compatible p c)
    (hzero : ∀ k, key p a b c k ≠ (false,false))
    (hinj : Function.Injective (key p a b c)) :
    ∃ e : Fin 6 ≃ Fin n,
      a ∘ e = sixFirst ∧ b ∘ e = sixSecond ∧ c ∘ e = sixThird ∧
      (tripleXor a b c) ∘ e = sixHole := by
  obtain ⟨i,j,k,hij,hik,hjk,hi,hj,hk⟩ := six_keys p a b c hn hzero hinj
  have hv := sixPorts_injective p a i j k hij hik hjk
  have hbije : Function.Bijective (sixPorts p a i j k) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hv,by simp [hn]⟩
  let e : Fin 6 ≃ Fin n := Equiv.ofBijective (sixPorts p a i j k) hbije
  have h1 : a ∘ e = sixFirst := sixPorts_first p a ha i j k
  have h2 : b ∘ e = sixSecond := sixPorts_second p a b c hb i j k hi hj hk
  have h3 : c ∘ e = sixThird := sixPorts_third p a b c hc i j k hi hj hk
  refine ⟨e,h1,h2,h3,?_⟩
  change tripleXor (a ∘ e) (b ∘ e) (c ∘ e) = sixHole
  rw [h1,h2,h3,six_xor]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHolePatterns
