import Holant.Proofs.Traversal.ArityTwo.SemanticAssembly


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo
open Holant Holant.Complexity PortWalk Descriptors OrderedDenote
set_option backward.isDefEq.respectTransparency false
open scoped Classical
variable {A B K : Type}

def mapKernel (f : A → B) (M : Kernel A) : Kernel B := fun a b => f (M a b)

def Component.map (f : A → B) : Component A → Component B
  | .scalar a => .scalar (f a)
  | .path l ms r => .path (fun b => f (l b)) (ms.map (mapKernel f)) (fun b => f (r b))
  | .cycle M ms => .cycle (mapKernel f M) (ms.map (mapKernel f))

theorem Component.eval_map_labels [CommSemiring K] (f : A → B) (coeff : B → K) (c : Component A) :
    (c.map f).eval coeff = c.eval (fun a => coeff (f a)) := by
  have hm (M : Kernel A) : realizeMatrix coeff (mapKernel f M) =
      realizeMatrix (fun a => coeff (f a)) M := by
    funext i j
    rfl
  cases c <;> simp only [Component.map,Component.eval,List.map_map,Function.comp_def,
    hm,List.map_cons]

theorem evaluateComponents_map_labels [CommSemiring K] (f : A → B) (coeff : B → K)
    (cs : List (Component A)) :
    evaluateComponents coeff (cs.map (Component.map f)) = evaluateComponents (fun a => coeff (f a)) cs := by
  simp only [evaluateComponents,List.map_map,Function.comp_def,Component.eval_map_labels]

variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (vertex : ∀ v : Fin r.vertices.length, (Fin (degree (arity := arity) r v) → Bool) → A)
variable (edge : Fin r.edges.length → Kernel A) (f : A → B)

theorem unaryTable_map (v : Fin r.vertices.length) :
    unaryTable r (fun v x => f (vertex v x)) v = fun b => f (unaryTable r vertex v b) := rfl

theorem binaryTable_map (p : r.Ports arity) :
    binaryTable r (fun v x => f (vertex v x)) p = mapKernel f (binaryTable r vertex p) := rfl

theorem edgeTable_map (p : r.Ports arity) :
    edgeTable r h (fun e a b => f (edge e a b)) p = mapKernel f (edgeTable r h edge p) := by
  funext a b
  simp only [edgeTable,orient,mapKernel]
  split <;> rfl

theorem cycleMatrices_map (xs : List (r.Ports arity)) :
    cycleMatrices r h (fun v x => f (vertex v x)) (fun e a b => f (edge e a b)) xs =
      (cycleMatrices r h vertex edge xs).map (List.map (mapKernel f)) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    cases ho : other r p <;>
      cases hm : cycleMatrices r h vertex edge xs <;>
      simp [cycleMatrices,ho,ih,hm,binaryTable_map,edgeTable_map]

theorem pathMatrices_map (xs : List (r.Ports arity)) :
    pathMatrices r h (fun v x => f (vertex v x)) (fun e a b => f (edge e a b)) xs =
      (pathMatrices r h vertex edge xs).map
        (fun t => (t.1.map (mapKernel f),fun b => f (t.2 b))) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    by_cases hp : degree (arity := arity) r p.1 = 1
    · by_cases he : xs.isEmpty
      · simp [pathMatrices,hp,he,unaryTable_map]
      · simp [pathMatrices,hp,he]
    · cases ho : other r p <;>
        cases hm : pathMatrices r h vertex edge xs <;>
        simp [pathMatrices,hp,ho,ih,hm,binaryTable_map,edgeTable_map]

theorem pathFrom_map (v : Fin r.vertices.length) (hv : degree (arity := arity) r v = 1) :
    pathFrom r h (fun v x => f (vertex v x)) (fun e a b => f (edge e a b)) v hv =
      (pathFrom r h vertex edge v hv).map (Component.map f) := by
  let p : r.Ports arity := ⟨v,⟨0,by change arity (r.vertices.get v).1 = 1 at hv; omega⟩⟩
  cases hw : (walk r h (fuel r) [p] (cross r h p)).2 <;>
    cases hm : pathMatrices r h vertex edge (walk r h (fuel r) [p] (cross r h p)).1 <;>
    simp [pathFrom,p,hw,pathMatrices_map,hm,Component.map,unaryTable_map,edgeTable_map]

theorem cycleFrom_map (v : Fin r.vertices.length) (hv : degree (arity := arity) r v = 2) :
    cycleFrom r h (fun v x => f (vertex v x)) (fun e a b => f (edge e a b)) v hv =
      (cycleFrom r h vertex edge v hv).map (Component.map f) := by
  let p : r.Ports arity := ⟨v,⟨0,by change arity (r.vertices.get v).1 = 2 at hv; omega⟩⟩
  cases hw : (walk r h (fuel r) [] p).2 with
  | terminal q => simp [cycleFrom,p,hw]
  | exhausted => simp [cycleFrom,p,hw]
  | repeated q =>
    by_cases hq : q = p
    · cases hm : cycleMatrices r h vertex edge (walk r h (fuel r) [] p).1 with
      | none => simp [cycleFrom,p,hw,hq,cycleMatrices_map,hm]
      | some ms => cases ms <;> simp [cycleFrom,p,hw,hq,cycleMatrices_map,hm,Component.map]
    · simp [cycleFrom,p,hw,hq]

theorem component_map (root : Fin r.vertices.length) :
    component r h (fun v x => f (vertex v x)) (fun e a b => f (edge e a b)) root =
      (component r h vertex edge root).map (Component.map f) := by
  unfold component
  split
  · split
    · exact pathFrom_map r h vertex edge f _ _
    · rfl
  · split
    · rfl
    · split
      · exact cycleFrom_map r h vertex edge f _ _
      · rfl

theorem all_map (cs : List (Component A)) (hc : all r h vertex edge = some cs) :
    all r h (fun v x => f (vertex v x)) (fun e a b => f (edge e a b)) =
      some (cs.map (Component.map f)) := by
  have aux (roots : List (Fin r.vertices.length)) (cs : List (Component A))
      (hc : roots.mapM (component r h vertex edge) = some cs) :
      roots.mapM (component r h (fun v x => f (vertex v x)) (fun e a b => f (edge e a b))) =
        some (cs.map (Component.map f)) := by
    induction roots generalizing cs with
    | nil => have he : cs = [] := by simpa using hc.symm
             subst cs
             rfl
    | cons root roots ih =>
      cases hv : component r h vertex edge root with
      | none => simp [hv] at hc
      | some c =>
        cases ht : roots.mapM (component r h vertex edge) with
        | none => simp [hv,ht] at hc
        | some tail =>
          have he : cs = c::tail := by simpa [hv,ht] using hc.symm
          subst cs
          simp [component_map,hv,ih tail ht]
  exact aux _ cs hc

variable [CommSemiring K]
variable (labels : (i : Fin s) → Signature A (arity i.val)) (edges : Fin b → Kernel A) (coeff : A → K)

/-- Correctness with finite symbolic labels, suitable for the actual bytecode. -/
theorem labelled_all_correct (hd : ∀ v, degree (arity := arity) r v ≤ 2) (cs : List (Component A))
    (hc : all r h (occurrenceVertex r h labels) (occurrenceEdge r h edges) = some cs) :
    evaluateComponents coeff cs =
      (r.realize h (fun i x => coeff (labels i x)) (fun i a b => coeff (edges i a b))).denote Fin.elim0 := by
  have hm := all_map r h (occurrenceVertex r h labels) (occurrenceEdge r h edges) coeff cs hc
  have he := all_correct r h (fun i x => coeff (labels i x)) (fun i a b => coeff (edges i a b))
    hd (cs.map (Component.map coeff)) hm
  simpa only [evaluateComponents_map_labels,id_eq] using he

end Holant.LocalDrafts.TraversalCompletion.ArityTwo
