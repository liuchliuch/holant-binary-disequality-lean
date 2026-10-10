import Holant.Proofs.Traversal.ArityTwo.PortWalk
import Holant.Proofs.Traversal.ArityTwo.Components


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.Descriptors
open Holant Holant.Complexity Holant.OneHot.Computable PortWalk
variable {s b : ℕ} {arity : ℕ → ℕ} {A : Type}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (vertex : ∀ v : Fin r.vertices.length, (Fin (degree (arity := arity) r v) → Bool) → A)
variable (edge : Fin r.edges.length → Kernel A)

/-- For a binary vertex, the first matrix index is the actual entering port. -/
def binaryTable (p : r.Ports arity) : Kernel A :=
  fun a b => vertex p.1 (fun i => if i.val = p.2.val then a else b)

def unaryTable (v : Fin r.vertices.length) : Bool → A := fun a => vertex v (fun _ => a)

/-- Edge orientation uses the original endpoint flag, even for a self-loop. -/
def edgeTable (p : r.Ports arity) : Kernel A :=
  orient (r.route h p).2 (edge (r.route h p).1)

theorem edgeTable_false (p : r.Ports arity) (hp : (r.route h p).2 = false) :
    edgeTable r h edge p = edge (r.route h p).1 := by simp [edgeTable,orient,hp]

theorem edgeTable_true (p : r.Ports arity) (hp : (r.route h p).2 = true) :
    edgeTable r h edge p = Kernel.transpose (edge (r.route h p).1) := by simp [edgeTable,orient,hp]

/-- Every recorded binary occurrence contributes its tensor and outgoing edge. -/
def cycleMatrices : List (r.Ports arity) → Option (List (Kernel A))
  | [] => some []
  | p::ps => do
      let q ← other r p
      let tail ← cycleMatrices ps
      pure (binaryTable r vertex p :: edgeTable r h edge q :: tail)

theorem cycleMatrices_length (ps : List (r.Ports arity)) (ms : List (Kernel A))
    (hm : cycleMatrices r h vertex edge ps = some ms) : ms.length = 2*ps.length := by
  induction ps generalizing ms with
  | nil =>
    simp only [cycleMatrices,Option.some.injEq] at hm
    subst ms
    rfl
  | cons p ps ih =>
    simp only [cycleMatrices] at hm
    cases ho : other r p with
    | none => simp [ho] at hm
    | some q =>
      cases ht : cycleMatrices r h vertex edge ps with
      | none => simp [ho,ht] at hm
      | some tail =>
        simp only [ho,ht,Option.bind_some,Option.some.injEq] at hm
        cases hm
        have hi := ih tail ht
        simp only [List.length_cons]
        omega

/-- The final entry must be a unary occurrence, never an invented all-ones cap. -/
def pathMatrices : List (r.Ports arity) → Option (List (Kernel A) × (Bool → A))
  | [] => none
  | p::ps =>
      if degree (arity := arity) r p.1 = 1 then
        if ps.isEmpty then some ([],unaryTable r vertex p.1) else none
      else do
        let q ← other r p
        let tail ← pathMatrices ps
        pure (binaryTable r vertex p :: edgeTable r h edge q :: tail.1,tail.2)

theorem pathMatrices_length (ps : List (r.Ports arity)) (ms : List (Kernel A)) (right : Bool → A)
    (hm : pathMatrices r h vertex edge ps = some (ms,right)) : ms.length+2 = 2*ps.length := by
  induction ps generalizing ms right with
  | nil => simp [pathMatrices] at hm
  | cons p ps ih =>
    simp only [pathMatrices] at hm
    split at hm
    · split at hm
      · have he : ps = [] := by cases ps <;> simp_all
        subst ps
        cases hm
        rfl
      · contradiction
    · cases ho : other r p with
      | none => simp [ho] at hm
      | some q =>
        cases ht : pathMatrices r h vertex edge ps with
        | none => simp [ho,ht] at hm
        | some tail =>
          simp only [ho,ht,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at hm
          rcases hm with ⟨rfl,rfl⟩
          have hi := ih tail.1 tail.2 ht
          simp only [List.length_cons]
          omega

/-- One more than the number of original port occurrences permits the closing
repeat test after a full traversal. This choice is structural, not a certificate. -/
def fuel : ℕ := 2*r.edges.length+1

def pathFrom (v : Fin r.vertices.length) (hv : degree (arity := arity) r v = 1) : Option (Component A) := do
  let p : r.Ports arity := ⟨v,⟨0,by change 0 < degree (arity := arity) r v; rw [hv]; decide⟩⟩
  let w := walk r h (fuel r) [p] (cross r h p)
  match w.2 with
  | .terminal _ =>
      let tail ← pathMatrices r h vertex edge w.1
      pure (.path (unaryTable r vertex v) (edgeTable r h edge p::tail.1) tail.2)
  | _ => none

def cycleFrom (v : Fin r.vertices.length) (hv : degree (arity := arity) r v = 2) : Option (Component A) := do
  let p : r.Ports arity := ⟨v,⟨0,by change 0 < degree (arity := arity) r v; rw [hv]; decide⟩⟩
  let w := walk r h (fuel r) [] p
  match w.2 with
  | .repeated q =>
      if q = p then
        let ms ← cycleMatrices r h vertex edge w.1
        match ms with
        | [] => none
        | M::tail => pure (.cycle M tail)
      else none
  | _ => none

/-- Unary endpoints take precedence over the least-ID root, which may be binary. -/
def component (root : Fin r.vertices.length) : Option (Component A) :=
  match ((r.graph h).componentVertices root).find? (fun v => decide (degree (arity := arity) r v = 1)) with
  | some v => if hv : degree (arity := arity) r v = 1 then pathFrom r h vertex edge v hv else none
  | none =>
      if degree (arity := arity) r root = 0 then some (.scalar (vertex root (fun _ => false)))
      else if hv : degree (arity := arity) r root = 2 then cycleFrom r h vertex edge root hv else none

/-- Each real component root is visited once, in the pre-existing original-ID
order. A failure is preserved rather than silently dropping that component. -/
def all : Option (List (Component A)) :=
  (r.graph h).roots.mapM (component r h vertex edge)

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.Descriptors
