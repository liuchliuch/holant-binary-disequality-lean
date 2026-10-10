import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin

/-! Exact original-coordinate meaning of physically selected residual pins. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
open Computability
variable {s b : ℕ} {arity : ℕ → ℕ}

/-- Selection is a specification of the emitted bytes, not a running lookup instruction. -/
def selected (value : Bool) (r : RawClosedNetwork) (v : Fin r.vertices.length) (p : r.Ports arity) :
    Option (ResidualLabel.Pin (arity (r.vertices.get v).1)) :=
  if hv : p.1 = v then
    some (Fin.cast (congrArg (fun u : Fin r.vertices.length => arity (r.vertices.get u).1) hv) p.2,value)
  else none

theorem selected_encode (value : Bool) (r : RawClosedNetwork) (v : Fin r.vertices.length) (p : r.Ports arity) :
    (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding
      (ResidualLabel.pinEncoding (arity (r.vertices.get v).1))).encode (selected value r v p) =
      pinWord value p.1.val v.val p.2.val := by
  by_cases hv : p.1=v
  · have hh : p.1.val=v.val := congrArg Fin.val hv
    simp [selected,hv,pinWord,hh,Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding,
      ResidualLabel.pinEncoding,OccurrenceLabel.unaryPortEncoding]
  · have hh : p.1.val ≠ v.val := fun h => hv (Fin.ext h)
    simp [selected,hv,pinWord,hh,Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding]

theorem selected_some (value : Bool) (r : RawClosedNetwork) (v : Fin r.vertices.length)
    (p : r.Ports arity) (q : ResidualLabel.Pin (arity (r.vertices.get v).1))
    (hq : selected value r v p = some q) : p.1=v ∧ p.2.val=q.1.val ∧ q.2=value := by
  unfold selected at hq
  split at hq
  · rename_i hv
    cases Option.some.inj hq
    exact ⟨hv,rfl,rfl⟩
  · contradiction

private theorem ports_eq (r : RawClosedNetwork) (p q : r.Ports arity)
    (hv : p.1=q.1) (hi : p.2.val=q.2.val) : p=q := by
  rcases p with ⟨v,i⟩
  rcases q with ⟨w,j⟩
  dsimp only at hv hi
  cases hv
  have he : i=j := Fin.ext hi
  cases he
  rfl

/-- Two original ends of one edge can never denote the same original local port. -/
theorem lookup_ends_ne (r : RawClosedNetwork) (h : r.WellFormed s b arity) (e : Fin r.edges.length) :
    r.lookup h (e,false) ≠ r.lookup h (e,true) := by
  intro hp
  have he := congrArg (r.route h) hp
  rw [r.route_lookup h (e,false),r.route_lookup h (e,true)] at he
  exact Bool.false_ne_true (congrArg Prod.snd he)

/-- A loop yields two distinct local pins at one vertex; ordinary endpoints may
select at most one pin at each vertex. Original port order is retained. -/
theorem selected_ends_disjoint (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (e : Fin r.edges.length) (v : Fin r.vertices.length) (a z : Bool) :
    ∀ p ∈ selected a r v (r.lookup h (e,false)),
      ∀ q ∈ selected z r v (r.lookup h (e,true)), p.1 ≠ q.1 := by
  intro p hp q hq he
  have hp' : selected a r v (r.lookup h (e,false)) = some p := hp
  have hq' : selected z r v (r.lookup h (e,true)) = some q := hq
  obtain ⟨hv,hpval,_⟩ := selected_some a r v _ p hp'
  obtain ⟨hw,hqval,_⟩ := selected_some z r v _ q hq'
  have hi : (r.lookup h (e,false)).2.val = (r.lookup h (e,true)).2.val :=
    hpval.trans ((congrArg Fin.val he).trans hqval.symm)
  exact lookup_ends_ne r h e (ports_eq r _ _ (hv.trans hw.symm) hi)

/-- The two derived pins form a valid residual zero-assignment descriptor. -/
def zeroDescriptor (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (e : Fin r.edges.length) (v : Fin r.vertices.length) (a z : Bool) :
    ResidualLabel.Descriptor (arity (r.vertices.get v).1) :=
  ⟨(selected a r v (r.lookup h (e,false)), selected z r v (r.lookup h (e,true)), none), by
    refine ⟨selected_ends_disjoint r h e v a z, ?_, ?_⟩ <;> simp⟩

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
