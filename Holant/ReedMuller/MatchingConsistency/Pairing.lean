import Holant.ReedMuller.ZeroCardGraph.Source

/-! Named-port perfect pairings and their exact equality support. -/
noncomputable section
namespace Holant.ReedMuller.MatchingConsistency
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.FixedCoreDeck

structure Pairing (ι : Type*) where
  mate : ι → ι
  involutive : Function.Involutive mate
  ne_self : ∀ i, mate i ≠ i

variable {ι : Type*}

theorem Pairing.injective (M : Pairing ι) : Function.Injective M.mate := M.involutive.injective

theorem Pairing.mate_eq_iff (M : Pairing ι) (u v : ι) : M.mate u=v ↔ M.mate v=u :=
  ⟨fun h => h ▸ M.involutive u,fun h => h ▸ M.involutive v⟩

def Pairing.graph (M : Pairing ι) : SimpleGraph ι where
  Adj u v := M.mate u=v
  symm := ⟨fun _ _ h => (M.mate_eq_iff _ _).mp h⟩
  loopless := ⟨M.ne_self⟩

def Pairing.Support (M : Pairing ι) (x : ι → Bool) : Prop := ∀i,x (M.mate i)=x i

 def pairIndicator [DecidableEq ι] (u v : ι) : ι → Bool := fun i => decide (i=u ∨ i=v)

 theorem Pairing.support_pair_iff [DecidableEq ι] (M : Pairing ι) (u v : ι) (huv : u≠v) :
    M.Support (pairIndicator u v) ↔ M.mate u=v := by
  constructor
  · intro h
    have hh := h u
    have hx : M.mate u=u ∨ M.mate u=v := by simpa [pairIndicator] using hh
    exact hx.resolve_left (M.ne_self u)
  · intro h i
    have hh : M.mate v=u := (M.mate_eq_iff u v).mp h
    simp only [pairIndicator]
    apply decide_eq_decide.mpr
    constructor
    · rintro (hi | hi)
      · exact Or.inr (M.injective (hi.trans hh.symm))
      · exact Or.inl (M.injective (hi.trans h.symm))
    · rintro (rfl | rfl)
      · exact Or.inr h
      · exact Or.inl hh

/-- Zero is allowed. Otherwise support is exactly an actual perfect matching
of equal bits; coefficients and physical scalars remain in the tensor. -/
def EqualityMatchingOrZero {K : Type*} [Zero K] (q : Tensor K ι) : Prop :=
  q=0 ∨ ∃ M : Pairing ι, ∀x,q x≠0 ↔ M.Support x

 theorem EqualityMatchingOrZero.zero_value {K : Type*} [Zero K] {q : Tensor K ι}
    (h : EqualityMatchingOrZero q) : q=0 ∨ q (fun _=>false)≠0 := by
  rcases h with h | ⟨M,hM⟩
  · exact Or.inl h
  · exact Or.inr ((hM _).mpr (fun _=>rfl))

 def Pairing.ofPorts {E : Type*} (p : (E × Bool) ≃ ι) : Pairing ι where
  mate i := p ((p.symm i).1,!(p.symm i).2)
  involutive i := by simp
  ne_self i := by
    intro h
    have hh := congrArg (fun j => (p.symm j).2) h
    simpa using hh

 theorem Pairing.ofPorts_support {E : Type*} (p : (E × Bool) ≃ ι) (x : ι → Bool) :
    (Pairing.ofPorts p).Support x ↔ ∀e,x (p (e,false))=x (p (e,true)) := by
  constructor
  · intro h e
    simpa [Pairing.Support,Pairing.ofPorts] using (h (p (e,true)))
  · intro h i
    obtain ⟨⟨e,b⟩,rfl⟩ := p.surjective i
    cases b <;> simp [Pairing.ofPorts,h]

 theorem weighted_equalityMatching {n r : ℕ} (M : WeightedMatching n r) :
    EqualityMatchingOrZero M.value := by
  refine Or.inr ⟨Pairing.ofPorts M.ports,?_⟩
  intro x
  rw [M.value_ne_zero_iff,Pairing.ofPorts_support]

end Holant.ReedMuller.MatchingConsistency
