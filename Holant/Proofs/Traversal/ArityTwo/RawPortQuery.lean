import Holant.Proofs.Traversal.ArityTwo.PortWalk
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Records
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertexInterface
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawPortQuery
open Holant Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ)
abbrev Input := EndpointVertex.Input s b arity
abbrev encoding := EndpointVertex.inputEncoding s b arity
abbrev rawEncoding := RawClosedNetwork.validatedEncoding s b arity
abbrev portsEncoding := framedListEncoding RawClosedNetwork.endpointEncoding

def port (x : Input s b arity) := x.1.val.lookup x.1.property x.2
def endpoint (x : Input s b arity) : RawEndpoint := (x.2.1.val,x.2.2)
def vertexQuery (x : Input s b arity) : Query s b arity := ⟨x.1,(port s b arity x).1⟩

def sourceComputes : Computes (encoding s b arity) (rawEncoding s b arity) (fun x => x.1) :=
  recode (Wiring.firstComputes (rawEncoding s b arity) RawClosedNetwork.endpointEncoding)
    (fun x => (x.1,endpoint s b arity x)) (fun _ => rfl) (fun _ => rfl)

def endpointComputes : Computes (encoding s b arity) RawClosedNetwork.endpointEncoding
    (endpoint s b arity) :=
  recode (Wiring.secondComputes (rawEncoding s b arity) RawClosedNetwork.endpointEncoding)
    (fun x => (x.1,endpoint s b arity x)) (fun _ => rfl) (fun _ => rfl)

def vertexComputes : Computes (encoding s b arity) (queryEncoding s b arity)
    (vertexQuery s b arity) :=
  recode (pairComputes (sourceComputes s b arity) (EndpointVertex.computes s b arity))
    id (fun _ => rfl) (fun _ => rfl)

def row (x : Input s b arity) : RawVertex := x.1.val.vertices.get (port s b arity x).1

def rowComputes : Computes (encoding s b arity) RawClosedNetwork.vertexEncoding (row s b arity) :=
  (vertexComputes s b arity).andThen (originalRowComputes s b arity)

def portsComputes : Computes (encoding s b arity) portsEncoding (fun x => (row s b arity x).2) :=
  (rowComputes s b arity).andThen
    (recode (Wiring.secondComputes encodingNatBool portsEncoding) id (fun _ => rfl) (fun _ => rfl))

def slot (k : ℕ) (x : Input s b arity) := (row s b arity x).2.getD k (0,false)

def slotComputes (k : ℕ) : Computes (encoding s b arity) RawClosedNetwork.endpointEncoding
    (slot s b arity k) :=
  (portsComputes s b arity).andThen (getDComputes RawClosedNetwork.endpointEncoding k (0,false))

def first (x : Input s b arity) : Bool := decide (slot s b arity 0 x = endpoint s b arity x)

def firstComputes : Computes (encoding s b arity) encodingBoolBool (first s b arity) :=
  (pairComputes (slotComputes s b arity 0) (endpointComputes s b arity)).andThen
    (equalComputes RawClosedNetwork.endpointEncoding)

def outgoing (x : Input s b arity) : RawEndpoint :=
  if first s b arity x then slot s b arity 1 x else slot s b arity 0 x

def outgoingComputes : Computes (encoding s b arity) RawClosedNetwork.endpointEncoding
    (outgoing s b arity) :=
  ifComputes (firstComputes s b arity) (slotComputes s b arity 1) (slotComputes s b arity 0)

def flipComputes : Computes RawClosedNetwork.endpointEncoding RawClosedNetwork.endpointEncoding
    (fun p => (p.1,!p.2)) := by
  let neg : Computes encodingBoolBool encodingBoolBool Bool.not :=
    FiniteRecode.computes _ _ Bool.not 1 (fun bit => by cases bit <;> decide)
  exact recode (pairComputes (Wiring.firstComputes encodingNatBool encodingBoolBool)
    ((Wiring.secondComputes encodingNatBool encodingBoolBool).andThen neg))
    id (fun _ => rfl) (fun _ => rfl)

def nextComputes : Computes (encoding s b arity) RawClosedNetwork.endpointEncoding
    (fun x => ((outgoing s b arity x).1,!(outgoing s b arity x).2)) :=
  (outgoingComputes s b arity).andThen flipComputes

theorem endpoint_at (x : Input s b arity) :
    x.1.val.portEndpoint x.1.property (port s b arity x) = endpoint s b arity x :=
  congrArg (fun p => (p.1.val,p.2)) (x.1.val.route_lookup x.1.property x.2)

theorem first_iff (x : Input s b arity) :
    first s b arity x = true ↔ (port s b arity x).2.val = 0 := by
  let p := port s b arity x
  have hpos : 0 < arity (x.1.val.vertices.get p.1).1 := Nat.zero_lt_of_lt p.2.isLt
  let z : x.1.val.Ports arity := ⟨p.1,⟨0,hpos⟩⟩
  have hz : slot s b arity 0 x = x.1.val.portEndpoint x.1.property z := by
    have hl := (x.1.property.1 p.1).2
    have hzero : 0 < (row s b arity x).2.length := by
      change 0 < (x.1.val.vertices.get p.1).2.length
      rw [hl]
      exact hpos
    change (row s b arity x).2.getD 0 (0,false) = _
    rw [List.getD_eq_getElem _ _ hzero]
    rfl
  rw [first,decide_eq_true_eq,hz,← endpoint_at s b arity x]
  constructor
  · intro he
    have he' : x.1.val.route x.1.property z = x.1.val.route x.1.property p := by
      apply Prod.ext
      · apply Fin.ext
        exact congrArg Prod.fst he
      · change (x.1.val.portEndpoint x.1.property z).2 = (x.1.val.portEndpoint x.1.property p).2
        exact congrArg Prod.snd he
    have hp := (x.1.val.route_bijective x.1.property).1 he'
    have := congrArg (fun q : x.1.val.Ports arity => q.2.val) hp
    exact this.symm
  · intro hp
    have he : z = p := by
      change (⟨p.1,⟨0,hpos⟩⟩ : x.1.val.Ports arity) = p
      have hv : (⟨0,hpos⟩ : Fin (arity (x.1.val.vertices.get p.1).1)) = p.2 := Fin.ext hp.symm
      simpa only [hv] using (Sigma.eta p)
    rw [he]

theorem outgoing_at (x : Input s b arity) (q : x.1.val.Ports arity)
    (hq : PortWalk.other x.1.val (port s b arity x) = some q) :
    outgoing s b arity x = x.1.val.portEndpoint x.1.property q := by
  obtain ⟨hv,hi,hd⟩ := PortWalk.other_some x.1.val (port s b arity x) q hq
  have hlen : (row s b arity x).2.length = 2 :=
    (x.1.property.1 (port s b arity x).1).2.trans hd
  have hp := (port s b arity x).2.isLt
  by_cases hzero : (port s b arity x).2.val = 0
  · have hb := (first_iff s b arity x).mpr hzero
    have hqval : q.2.val = 1 := by omega
    change (if first s b arity x then slot s b arity 1 x else slot s b arity 0 x) = _
    rw [hb]
    simp only [↓reduceIte, slot]
    rw [List.getD_eq_getElem _ _ (show 1 < (row s b arity x).2.length by omega)]
    simp [RawClosedNetwork.portEndpoint, row, hv, hqval, List.get_eq_getElem]
  · have hb : first s b arity x = false := by
      cases h : first s b arity x <;> simp_all [first_iff]
    have hqval : q.2.val = 0 := by dsimp [PortWalk.degree] at hd; omega
    change (if first s b arity x then slot s b arity 1 x else slot s b arity 0 x) = _
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte, slot]
    rw [List.getD_eq_getElem _ _ (show 0 < (row s b arity x).2.length by omega)]
    simp [RawClosedNetwork.portEndpoint, row, hv, hqval, List.get_eq_getElem]

theorem primitive_bound (x : Input s b arity) :
    let w := nextComputes s b arity
    primitiveCost w.machine (w.outputs x).steps
      (some (Turing.initList w.machine.computer ((encoding s b arity).encode x))) ≤
        (primitivePolynomial w).eval ((encoding s b arity).encode x).length :=
  computes_primitive_cost (nextComputes s b arity) x

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawPortQuery
